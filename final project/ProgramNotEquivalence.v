(**
*  CS386L Programming Languages
* Final project
* Tian Zhang (tz3272)
* Brief Introduction:
*     For the this file, I am working on program inequivalence, and 
      all the work is based on Maps, Imp in class. I got some idea from
      the book
*)

Require Import ProgramEquivalence.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Import ListNotations.
Require Import Maps.
Require Import Imp.


(** Now we have prove that program are equivalent,
 the next step is to prove that programs are not equivalent 
*)


(** First, define a function that substitutes an arithmetic
    expression for each occurrence of a given variable in another
    expression: 

       c1  =  (X ::= 4 + 5;; 
               Y ::= Y + X)
       c2  =  (X ::= 4 + 5;; 
               Y ::= Y + (4 + 5))
    *)

Fixpoint subst_aexp (i : id) (u : aexp) (a : aexp) : aexp :=
  match a with
  | ANum n       =>
      ANum n
  | AId i'       =>
      if beq_id i i' then u else AId i'
  | APlus a1 a2  =>
      APlus (subst_aexp i u a1) (subst_aexp i u a2)
  | AMinus a1 a2 =>
      AMinus (subst_aexp i u a1) (subst_aexp i u a2)
  | AMult a1 a2  =>
      AMult (subst_aexp i u a1) (subst_aexp i u a2)
  end.

Example subst_aexp_ex :
  subst_aexp X (APlus (ANum 42) (ANum 53))
             (APlus (AId Y) (AId X)) 
= (APlus (AId Y) (APlus (ANum 42) (ANum 53))).
Proof. reflexivity.  Qed.

(** Now we need to prove that such subsitution are behaviour equivalence
 *)

Definition subst_equiv_property := forall i1 i2 a1 a2,
  cequiv (i1 ::= a1;; i2 ::= a2)
         (i1 ::= a1;; i2 ::= subst_aexp i1 a1 a2).

(** the property does not always hold. Here is the counter example


    Consider the following program:

         X ::= APlus (AId X) (ANum 1);; Y ::= AId X

    Note that

         (X ::= APlus (AId X) (ANum 1);; Y ::= AId X)
         / empty_state \\ st1,

    where [st1 = { X |-> 1, Y |-> 1 }].

    By our assumption, we know that

        cequiv (X ::= APlus (AId X) (ANum 1);; Y ::= AId X)
               (X ::= APlus (AId X) (ANum 1);; Y ::= APlus (AId X) (ANum 1))

    so, by the definition of [cequiv], we have

        (X ::= APlus (AId X) (ANum 1);; Y ::= APlus (AId X) (ANum 1))
        / empty_state \\ st1.

    But we can also derive

        (X ::= APlus (AId X) (ANum 1);; Y ::= APlus (AId X) (ANum 1))
        / empty_state \\ st2,

    where [st2 = { X |-> 1, Y |-> 2 }].  Note that [st1 <> st2]; this
    is a contradiction, since [ceval] is deterministic!  [] *)

(**Then the next step is to prove this inequiv*)

Theorem subst_inequiv :
  ~ subst_equiv_property.
Proof.
  unfold subst_equiv_property.
  intros Contra.

  (* Here is the counterexample: assuming that [subst_equiv_property]
     holds allows us to prove that these two programs are
     equivalent... *)
  remember (X ::= APlus (AId X) (ANum 1);;
            Y ::= AId X)
      as c1.
  remember (X ::= APlus (AId X) (ANum 1);;
            Y ::= APlus (AId X) (ANum 1))
      as c2.
  assert (cequiv c1 c2) by (subst; apply Contra).

  (* ... allows us to show that the command [c2] can terminate
     in two different final states:
        st1 = {X |-> 1, Y |-> 1}
        st2 = {X |-> 1, Y |-> 2}. *)
  remember (t_update (t_update empty_state X 1) Y 1) as st1.
  remember (t_update (t_update empty_state X 1) Y 2) as st2.
  assert (H1: c1 / empty_state \\ st1);
  assert (H2: c2 / empty_state \\ st2);
  try (subst;
       apply E_Seq with (st' := (t_update empty_state X 1));
       apply E_Ass; reflexivity).
  apply H in H1.

  (* Finally, we use the fact that evaluation is deterministic
     to obtain a contradiction. *)
  assert (Hcontra: st1 = st2)
    by (apply (ceval_deterministic c2 empty_state); assumption).
  assert (Hcontra': st1 Y = st2 Y)
    by (rewrite Hcontra; reflexivity).
  subst. inversion Hcontra'.  Qed.


(** Actually, The above equivalence it was actually almost right.  
    To make it correct, we just need to
    exclude the case where the variable [X] occurs in the
    right-hand-side of the first assignment statement. 
*)

Inductive var_not_used_in_aexp (X:id) : aexp -> Prop :=
  | VNUNum: forall n, var_not_used_in_aexp X (ANum n)
  | VNUId: forall Y, X <> Y -> var_not_used_in_aexp X (AId Y)
  | VNUPlus: forall a1 a2,
      var_not_used_in_aexp X a1 ->
      var_not_used_in_aexp X a2 ->
      var_not_used_in_aexp X (APlus a1 a2)
  | VNUMinus: forall a1 a2,
      var_not_used_in_aexp X a1 ->
      var_not_used_in_aexp X a2 ->
      var_not_used_in_aexp X (AMinus a1 a2)
  | VNUMult: forall a1 a2,
      var_not_used_in_aexp X a1 ->
      var_not_used_in_aexp X a2 ->
      var_not_used_in_aexp X (AMult a1 a2).

Lemma aeval_weakening : forall i st a ni,
  var_not_used_in_aexp i a ->
  aeval (t_update st i ni) a = aeval st a.
Proof.
  intros.
  induction a; simpl;
    try (inversion H; subst);
    try (apply IHa1 in H2; apply IHa2 in H3);
    try (rewrite H2; rewrite H3);
    try reflexivity.
  - (* AId *)
  apply t_update_neq.
  assumption.
Qed.

(** Using var_not_used_in_aexp, we can formalize and prove a correct verson
    of subst_equiv_property. I call it subst_equiv_weaker_property 
*)

Lemma aeval__var_not_used_in_aexp: forall a b i st,
    var_not_used_in_aexp i b ->
    st i = aeval st b ->
    aeval st a = aeval st (subst_aexp i b a).
Proof.
  induction a; intros;
    simpl;
    try rewrite <- IHa1; try rewrite <- IHa2;
      try destruct (beq_idP i0 i); subst;
      try reflexivity; try assumption.
Qed.

Theorem subst_equiv_property_weak: forall i1 i2 a1 a2,
    var_not_used_in_aexp i1 a1 ->
    cequiv (i1 ::= a1;; i2 ::= a2)
           (i1 ::= a1;; i2 ::= subst_aexp i1 a1 a2).
Proof.
  intros i1 i2 a1 a2 Hvar.
  split; intros H; inversion H; subst.
  - apply E_Seq with st'0.
    + assumption.
    + inversion H5; subst. constructor.
      rewrite <- aeval__var_not_used_in_aexp;
        try reflexivity; try assumption.
      * inversion H2; subst.
        rewrite aeval_weakening; try assumption.
        unfold t_update. rewrite <- beq_id_refl. reflexivity.
  - apply E_Seq with st'0.
    + assumption.
    + inversion H5; subst. constructor.
      rewrite <- aeval__var_not_used_in_aexp;
        try reflexivity; try assumption.
      * inversion H2; subst.
        rewrite aeval_weakening; try assumption.
        unfold t_update. rewrite <- beq_id_refl. reflexivity.
Qed.


(** Here are more example of program inequality.
    Prove that an infinite loop is not equivalent to [SKIP] 
*)

Theorem inequiv_exercise:
  ~ cequiv (WHILE BTrue DO SKIP END) SKIP.
Proof.
  unfold not.
  remember (WHILE BTrue DO SKIP END) as c eqn:Heqc.
  induction c; try (inversion Heqc).
  intros.
  rewrite H1 in *.
  assert (bequiv b BTrue).
  unfold bequiv. intros. rewrite H0. simpl. reflexivity.
  unfold cequiv in H.  
  apply WHILE_true_nonterm with (c:=SKIP) (st:=empty_state) (st':=empty_state) in H2.
  unfold not in H2.
  rewrite H0 in H2.
  rewrite H in H2.
  assert (SKIP / empty_state \\ empty_state).
  apply E_Skip.
  apply H2 in H3.
  assumption.
Qed.  



