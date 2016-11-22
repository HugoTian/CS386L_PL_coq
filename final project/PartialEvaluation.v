(**
*  CS386L Programming Languages
* Final project
* Tian Zhang (tz3272)
* Brief Introduction:
*     For the final project, I am working on partial evaluation, and 
      all the work is based on Maps, Imp in class. I got some idea from
      the book
*)


Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import Maps.
Require Import Imp.
Require Import Smallstep.

(** Now we have constant folding, and the next step is 
    propagates known constants and uses them to simplify programs.
    In this file I am about to implement partial evaluation.
    some of the definition and proof structure are followed PE.v file
    of software-foundation book
*)

(** Define Partial States , and some partial evaluation related 
definition and method *)

(** The idea is that a variable [id] appears in the list if and only
    if we know its current [nat] value.  The [pe_lookup] function thus
    interprets this concrete representation. *)
    
Definition pe_state := list (id * nat).

Fixpoint pe_lookup (pe_st : pe_state) (V:id) : option nat :=
  match pe_st with
  | [] => None
  | (V',n')::pe_st => if beq_id V V' then Some n'
                      else pe_lookup pe_st V
  end.

Definition empty_pe_state : pe_state := [].

(** More generally, if the list representing a pe_state does not
    contain some id, then that pe_state must map that id to
    None *)

(**
    compare V V'

    means to reason by cases over [beq_id V V'].
    In the case where [V = V'], the tactic
    substitutes [V] for [V'] throughout. *)
    
Tactic Notation "compare" ident(i) ident(j) :=
  let H := fresh "Heq" i j in
  destruct (beq_idP i j);
  [ subst j | ].

Theorem pe_domain: forall pe_st V n,
  pe_lookup pe_st V = Some n ->
  In V (map (@fst _ _) pe_st).
Proof. intros pe_st V n H. induction pe_st as [| [V' n'] pe_st].
  - (* [] *) inversion H.
  - (* :: *) simpl in H. simpl. compare V V'; auto. Qed.
  
(** If a type [A] has an operator [beq] for testing equality of its
    elements, we can compute a boolean [inb beq a l] for testing
    whether [In a l] holds or not. *)

Fixpoint inb {A : Type} (beq : A -> A -> bool) (a : A) (l : list A) :=
  match l with
  | [] => false
  | a'::l' => beq a a' || inb beq a l'
  end.

(** It is easy to relate [inb] to [In] with the [reflect] property: *)

Lemma inbP : forall A : Type, forall beq : A->A->bool,
  (forall a1 a2, reflect (a1 = a2) (beq a1 a2)) ->
  forall a l, reflect (In a l) (inb beq a l).
Proof.
  intros A beq beqP a l.
  induction l as [|a' l' IH].
  - constructor. intros [].
  - simpl. destruct (beqP a a').
    + subst. constructor. left. reflexivity.
    + simpl. destruct IH; constructor.
      * right. trivial.
      * intros [H1 | H2]; congruence.
Qed.


(** now we do partial evaluation on arithmetic expression *)


(** Partial evaluation of aexp is just constant folding, replace
a variable with constant expression*)

Fixpoint pe_aexp (pe_st : pe_state) (a : aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | AId i => match pe_lookup pe_st i with (* <----- NEW *)
             | Some n => ANum n
             | None => AId i
             end
  | APlus a1 a2 =>
      match (pe_aexp pe_st a1, pe_aexp pe_st a2) with
      | (ANum n1, ANum n2) => ANum (n1 + n2)
      | (a1', a2') => APlus a1' a2'
      end
  | AMinus a1 a2 =>
      match (pe_aexp pe_st a1, pe_aexp pe_st a2) with
      | (ANum n1, ANum n2) => ANum (n1 - n2)
      | (a1', a2') => AMinus a1' a2'
      end
  | AMult a1 a2 =>
      match (pe_aexp pe_st a1, pe_aexp pe_st a2) with
      | (ANum n1, ANum n2) => ANum (n1 * n2)
      | (a1', a2') => AMult a1' a2'
      end
  end.


Example test_pe_aexp1:
  pe_aexp [(X,3)] (APlus (APlus (AId X) (ANum 1)) (AId Y))
  = APlus (ANum 4) (AId Y).
Proof. reflexivity. Qed.

(** Now, the next step is to prove that this partial evaluation is 
correct. 
    a full state st is consistent with a partial state
    pe_st  evaluating [a] and evaluating [pe_aexp pe_st a] 
    in st yields the same result. *)

Definition pe_consistent (st:state) (pe_st:pe_state) :=
  forall V n, Some n = pe_lookup pe_st V -> st V = n.

Theorem pe_aexp_correct: forall st pe_st, pe_consistent st pe_st ->
  forall a, aeval st a = aeval st (pe_aexp pe_st a).
Proof. unfold pe_consistent. intros st pe_st H a.
  induction a; simpl;
    try reflexivity;
    try (destruct (pe_aexp pe_st a1);
         destruct (pe_aexp pe_st a2);
         rewrite IHa1; rewrite IHa2; reflexivity).
  - (* AId *)
    remember (pe_lookup pe_st i) as l. destruct l.
    + (* Some *) rewrite H with (n:=n) by apply Heql. reflexivity.
    + (* None *) reflexivity.
Qed.

(** The next step is to remove assignment for partial evaluator *)

Fixpoint pe_update (st:state) (pe_st:pe_state) : state :=
  match pe_st with
  | [] => st
  | (V,n)::pe_st => t_update (pe_update st pe_st) V n
  end.

(** now we can prove the partial update is correct and we combine 
  the pe_update and pe_consistent in two ways*)
  
Theorem pe_update_correct_weak: forall st pe_st V0,
  pe_update st pe_st V0 =
  match pe_lookup pe_st V0 with
  | Some n => n
  | None => st V0
  end.
Proof. intros. induction pe_st as [| [V n] pe_st]. reflexivity.
  simpl in *. unfold t_update.
  compare V0 V; auto. rewrite <- beq_id_refl; auto. rewrite false_beq_id; auto. Qed.

Theorem pe_update_consistent: forall st pe_st,
  pe_consistent (pe_update st pe_st) pe_st.
Proof. intros st pe_st V n H. rewrite pe_update_correct.
  destruct (pe_lookup pe_st V); inversion H. reflexivity. Qed.

Theorem pe_consistent_update: forall st pe_st,
  pe_consistent st pe_st -> forall V, st V = pe_update st pe_st V.
Proof. intros st pe_st H V. rewrite pe_update_correct.
  remember (pe_lookup pe_st V) as l. destruct l; auto. Qed.

(** Now we can state and prove that [pe_aexp] is correct in the
    stronger sense that will help us define the rest of the partial
    evaluator.

    partial evaluation is a two-stage process.  
    
    First, static stage, we partially evaluate the given 
    program with respect to some partial state to get a residual program.  
    
    Second, dynamic stage, we
    evaluate the residual program with respect to the rest of the
    state.  
    
    This dynamic state provides values for those variables
    that are unknown in the static state.  Thus, the
    residual program should be equivalent to prepending the
    assignments listed in the partial state to the original program. *)

Theorem pe_aexp_correct: forall (pe_st:pe_state) (a:aexp) (st:state),
  aeval (pe_update st pe_st) a = aeval st (pe_aexp pe_st a).
Proof.
  intros pe_st a st.
  induction a; simpl;
    try reflexivity;
    try (destruct (pe_aexp pe_st a1);
         destruct (pe_aexp pe_st a2);
         rewrite IHa1; rewrite IHa2; reflexivity).
  rewrite pe_update_correct. destruct (pe_lookup pe_st i); reflexivity.
Qed.

(** Since we finish the arithmetic partial evaluation, and the next
step is to finish partial evaluation for boolean *)

Fixpoint pe_bexp (pe_st : pe_state) (b : bexp) : bexp :=
  match b with
  | BTrue        => BTrue
  | BFalse       => BFalse
  | BEq a1 a2 =>
      match (pe_aexp pe_st a1, pe_aexp pe_st a2) with
      | (ANum n1, ANum n2) => if beq_nat n1 n2 then BTrue else BFalse
      | (a1', a2') => BEq a1' a2'
      end
  | BLe a1 a2 =>
      match (pe_aexp pe_st a1, pe_aexp pe_st a2) with
      | (ANum n1, ANum n2) => if leb n1 n2 then BTrue else BFalse
      | (a1', a2') => BLe a1' a2'
      end
  | BNot b1 =>
      match (pe_bexp pe_st b1) with
      | BTrue => BFalse
      | BFalse => BTrue
      | b1' => BNot b1'
      end
  | BAnd b1 b2 =>
      match (pe_bexp pe_st b1, pe_bexp pe_st b2) with
      | (BTrue, BTrue) => BTrue
      | (BTrue, BFalse) => BFalse
      | (BFalse, BTrue) => BFalse
      | (BFalse, BFalse) => BFalse
      | (b1', b2') => BAnd b1' b2'
      end
  end.

(** Example *)
Example test_pe_bexp1:
  pe_bexp [(X,3)] (BNot (BLe (AId X) (ANum 3)))
  = BFalse.
Proof. reflexivity. Qed.

(** The correctness of pe_bexp is analogous to the correctness of
    pe_aexp above. *)

Theorem pe_bexp_correct: forall (pe_st:pe_state) (b:bexp) (st:state),
  beval (pe_update st pe_st) b = beval st (pe_bexp pe_st b).
Proof.
  intros pe_st b st.
  induction b; simpl;
    try reflexivity;
    try (remember (pe_aexp pe_st a) as a';
         remember (pe_aexp pe_st a0) as a0';
         assert (Ha: aeval (pe_update st pe_st) a = aeval st a');
         assert (Ha0: aeval (pe_update st pe_st) a0 = aeval st a0');
           try (subst; apply pe_aexp_correct);
         destruct a'; destruct a0'; rewrite Ha; rewrite Ha0;
         simpl; try destruct (beq_nat n n0);
         try destruct (leb n n0); reflexivity);
    try (destruct (pe_bexp pe_st b); rewrite IHb; reflexivity);
    try (destruct (pe_bexp pe_st b1);
         destruct (pe_bexp pe_st b2);
         rewrite IHb1; rewrite IHb2; reflexivity).
Qed.

(** * Partial Evaluation of Commands, Without Loops *)