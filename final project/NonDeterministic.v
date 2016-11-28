(**
*  CS386L Programming Languages
* Final project
* Tian Zhang (tz3272)
* Brief Introduction:
*     For the this file, I am working on non-deteminisitic imp, and 
      all the work is based on Maps, Imp in class. I got some idea from
      the book, optional exercise from equiv.v
*)

Require Import ProgramEquivalence.
Require Import ProgramNotEquivalence.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Import ListNotations.
Require Import Maps.
Require Import Imp.


(**  Imp's evaluation relation is deterministic.  However,
    non_determinism is an important part of the definition of many
    real programming languages. 
    
    We will extend Imp with a simple
    nondeterministic command 
    
    The new command has the syntax [HAVOC X],
    where [X] is an identifier. The effect of executing [HAVOC X] is
    to assign an arbitrary number to the variable [X],
    nondeterministically. 
    
    For example, after executing the program:

      HAVOC Y;;
      Z ::= Y * 2

    the value of [Y] can be any number, while the value of [Z] is
    twice that of [Y] (so [Z] is always even). 
    
    In other word, a variable on which we do [HAVOC] roughly corresponds
    to an unitialized variable in a low-level language like C.  After
    the [HAVOC], the variable holds a fixed but arbitrary number.  Most
    sources of nondeterminism in language definitions are there
    precisely because programmers don't care which choice is made 
*)


(** To formalize this new imp, we first add a clause to the definition of
    commands. *)

Inductive com : Type :=
  | CSkip : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CHavoc : id -> com.                (* new *)

Notation "'SKIP'" :=
  CSkip.
Notation "X '::=' a" :=
  (CAss X a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" :=
  (CIf e1 e2 e3) (at level 80, right associativity).
Notation "'HAVOC' l" := (CHavoc l) (at level 60).


(** Now, we must extend the operational semantics. define ceval for this
  new HAVOC
*)

Reserved Notation "c1 '/' st '\\' st'"
                  (at level 40, st at level 39).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st : state, SKIP / st \\ st
  | E_Ass : forall (st : state) (a1 : aexp) (n : nat) (X : id),
      aeval st a1 = n ->
      (X ::= a1) / st \\ t_update st X n
  | E_Seq : forall (c1 c2 : com) (st st' st'' : state),
      c1 / st \\ st' ->
      c2 / st' \\ st'' ->
      (c1 ;; c2) / st \\ st''
  | E_IfTrue : forall (st st' : state) (b1 : bexp) (c1 c2 : com),
      beval st b1 = true ->
      c1 / st \\ st' ->
      (IFB b1 THEN c1 ELSE c2 FI) / st \\ st'
  | E_IfFalse : forall (st st' : state) (b1 : bexp) (c1 c2 : com),
      beval st b1 = false ->
      c2 / st \\ st' ->
      (IFB b1 THEN c1 ELSE c2 FI) / st \\ st'
  | E_WhileEnd : forall (b1 : bexp) (st : state) (c1 : com),
      beval st b1 = false -> 
      (WHILE b1 DO c1 END) / st \\ st
  | E_WhileLoop : forall (st st' st'' : state) (b1 : bexp) (c1 : com),
      beval st b1 = true ->
      c1 / st \\ st' ->
      (WHILE b1 DO c1 END) / st' \\ st'' ->
      (WHILE b1 DO c1 END) / st \\ st''
  | E_Havoc : forall (st : state) (i : id) (n : nat),
      (HAVOC i) / st \\ (t_update st i n)

  where "c1 '/' st '\\' st'" := (ceval c1 st st').


(** next, we repeat the definition of command equivalence from above: *)

Definition cequiv (c1 c2 : com) : Prop := forall st st' : state,
  c1 / st \\ st' <-> c2 / st \\ st'.

(** The next step is to prove some nondeterministic
    programs equivalent / inequivalent. *)


Definition pXY :=
  HAVOC X;; HAVOC Y.

Definition pYX :=
  HAVOC Y;; HAVOC X.



Theorem pXY_cequiv_pYX :
  cequiv pXY pYX \/ ~cequiv pXY pYX.
Proof.
left.
  unfold cequiv.
  split; intros;
    inversion H; subst;
    inversion H2; subst;
    inversion H5; subst.
  -(* -> *)
    replace (t_update (t_update st X n) Y n0) with (t_update (t_update st Y n0) X n).
    apply E_Seq with (t_update st Y n0).
    apply E_Havoc.
    apply E_Havoc.
    apply functional_extensionality; intros.
    rewrite t_update_permute. reflexivity.
    unfold not.
    intros.
    inversion H0.
  - (* <- *)
    replace (t_update (t_update st Y n) X n0) with (t_update (t_update st X n0) Y n).
    apply E_Seq with (t_update st X n0).
    apply E_Havoc.
    apply E_Havoc.
    apply functional_extensionality; intros.
    rewrite t_update_permute. reflexivity.
    unfold not.
    intros.
    inversion H0.
Qed.


(** Here is the second example, havoc_copy, and we want to see
  whether non-deteminisitic copy is equivalent to variable initialization
 *)


Definition ptwice :=
  HAVOC X;; HAVOC Y.

Definition pcopy :=
  HAVOC X;; Y ::= AId X.

Theorem ptwice_cequiv_pcopy :
  cequiv ptwice pcopy \/ ~cequiv ptwice pcopy.
Proof.
  right.
  unfold not.
  intros contra.
  unfold cequiv in contra.
  assert (ptwice / empty_state \\ t_update (t_update empty_state X 1) Y 2) as PT.
  apply E_Seq with (st':=t_update empty_state X 1).
  apply E_Havoc.
  apply E_Havoc.
  assert (pcopy / empty_state \\ t_update (t_update empty_state X 1) Y 2) as PC.
  apply contra; assumption.
  inversion PC; inversion PT; subst.
  inversion H1; inversion H7; subst.
  inversion H10; inversion H4; subst.
  unfold t_update at 3 in H9.
  simpl in H9.
  remember (beq_nat n 1).
  destruct b.
  - (* n = 1 *)
    apply beq_nat_eq in Heqb.
    rewrite Heqb in *.
    inversion H9.
    assert (t_update (t_update empty_state X 1) Y 1 Y = t_update (t_update empty_state X 1) Y 2 Y).
    rewrite H2. reflexivity.
    rewrite t_update_eq in H0.
    symmetry in H0.
    rewrite t_update_eq in H0.
    inversion H0.
  - (* n != 1 *)
    assert (t_update (t_update empty_state X n) Y n X = t_update (t_update empty_state X 1) Y 2 X).
    rewrite H9. reflexivity.
    unfold t_update in H0. simpl in H0. rewrite H0 in Heqb. inversion Heqb.
Qed.

(** The following part illustrate the phenomenon of nondeterministic about loop.
    In a language,
    with nondeterminism, some programs always terminate,
    some programs always diverge, and some programs can
    nondeterministically terminate in some runs and diverge in
    others. 
*)

(** below part is the advanced exercise in equiv.v about nondeterminism  *)

(** Prove that [p1] and [p2] are equivalent.
  
 *)


Definition p1 : com :=
  WHILE (BNot (BEq (AId X) (ANum 0))) DO
    HAVOC Y;;
    X ::= APlus (AId X) (ANum 1)
  END.

Definition p2 : com :=
  WHILE (BNot (BEq (AId X) (ANum 0))) DO
    SKIP
  END.

(** Intuitively, the programs have the same termination
    behavior: either they loop forever, or they terminate in the
    same state they started in.  
    
    We can capture the termination
    behavior of p1 and p2 individually with these lemmas: *)

Lemma WHILE_true_nonterm : forall (P : state -> Prop) (b : bexp) (c : com),
  (forall (st : state), P st -> beval st b = true) ->
  (forall (st st' : state), P st -> c / st \\ st' -> P st') ->
  (forall (st st' : state), P st -> ~((WHILE b DO c END) / st \\ st')).
Proof.
  intro P.
  intros b c.
  intros Hb Hc.
  intros st st'.
  intro HP.
  intro Contra.
  remember (WHILE b DO c END) as cw.
  induction Contra;
  (* Trivial, contradiction cases. *)
  try (inversion Heqcw);
  subst.
  (* E_WhileEnd *)
  rewrite -> Hb in H.
  inversion H.
  assumption.
  (* E_WhileLoop *)
  apply IHContra2.
  eapply Hc.
  apply HP.
  apply Contra1.
  reflexivity. Qed.

(** lemma for condition evaluation for while loop*)

Lemma p1p2_cond_eval : forall (st : state),
  st X <> 0 ->
  beval st (BNot (BEq (AId X) (ANum 0))) = true.
Proof.
  intro st.
  intro H.
  simpl.
  apply negb_true_iff.
  apply beq_nat_false_iff.
  assumption. Qed.
  

Lemma p1_may_diverge : forall st st', st X <> 0 ->
  ~ p1 / st \\ st'.
Proof. 
  intros st st'.
  intro HX.
  apply WHILE_true_nonterm with (P := fun st => st X <> 0).

  apply p1p2_cond_eval.

  intros st0 st'0.
  intros HP Hc.
  inversion Hc. subst.
  inversion H1. subst.
  inversion H4. subst.
  unfold update.
  simpl.
  apply not_eq_sym.
  rewrite <- plus_comm.
  apply O_S.

  assumption. Qed.

Lemma p2_may_diverge : forall st st', st X <> 0 ->
  ~ p2 / st \\ st'.
Proof.
  intros st st'.
  intro HX.
  apply WHILE_true_nonterm with (P := fun st => st X <> 0).

  apply p1p2_cond_eval.

  intros st0 st'0.
  intros HP Hc.
  inversion Hc. subst.
  apply HP.

  assumption. Qed.

(** Next, use those lemmas to prove that p1 and p2 are actually
    equivalent. *)

Theorem p1_p2_equiv : cequiv p1 p2.
Proof.
  unfold cequiv.
  intros st st'.
  destruct (eq_nat_dec (st X) 0).

  (* st X = 0 *)
  split;
  intro H;
  inversion H; subst;
  try (apply E_WhileEnd;
       simpl;
       rewrite -> e;
       reflexivity);
  try (simpl in H2;
       rewrite -> e in H2;
       simpl in H2;
       inversion H2).

  (* st X <> 0 *)
  split;
  intro H;
  try (apply p1_may_diverge in H);
  try (apply p2_may_diverge in H);
  try (contradiction H);
  assumption. 
Qed.


(** Below is part of advanced exercise in equiv.v about nondeterminism
    Prove that the following programs are not equivalent. 
*)

Definition p3 : com :=
  Z ::= ANum 1;;
  WHILE (BNot (BEq (AId X) (ANum 0))) DO
    HAVOC X;;
    HAVOC Z
  END.

Definition p4 : com :=
  X ::= (ANum 0);;
  Z ::= (ANum 1).


Definition st_X1 : state := t_update empty_state X 1.
Definition st_Z0_X0 : state := t_update (t_update st_X1 Z 0) X 0.

Lemma p3_X0_Z0 :
  p3 / st_X1 \\ st_Z0_X0.
Proof.
  unfold p3.
  eapply E_Seq.
  apply E_Ass.
  reflexivity.
  apply E_WhileLoop with (st' := t_update (t_update (t_update st_X1 Z 1) X 0) Z 0).
  reflexivity.
  apply E_Seq with (st' := t_update (t_update st_X1 Z 1) X 0).
  apply E_Havoc.
  apply E_Havoc.
  assert (eval : t_update (t_update (t_update st_X1 Z 1) X 0) Z 0
               = t_update (t_update st_X1 Z 0) X 0).
    unfold t_update.
    apply functional_extensionality.
    intro V.
    destruct (beq_id Z V);
    destruct (beq_id X V);
    reflexivity.
  rewrite -> eval.
  apply E_WhileEnd.
  reflexivity. Qed.

Theorem p3_p4_inequiv : ~ cequiv p3 p4.
Proof.
  unfold cequiv.
  intro Contra.
  assert (H : p3 / st_X1 \\ st_Z0_X0).
    apply p3_X0_Z0.

  apply Contra in H.
  unfold p4 in H.
  inversion H. subst.
  inversion H2. subst.
  inversion H5. subst.
  simpl in H6.

  assert (H0 : st_Z0_X0 Z = 0).
    reflexivity.
  assert (H1 : st_Z0_X0 Z = 1).
    rewrite <- H6.
    reflexivity.
  rewrite -> H0 in H1.
  inversion H1. Qed.
 
 
(** below example is  5 stars advanced exercise in equiv.v 
  proof that program p5 and p6 are equivalent
*)

Definition p5 : com :=
  WHILE (BNot (BEq (AId X) (ANum 1))) DO
    HAVOC X
  END.

Definition p6 : com :=
  X ::= ANum 1.

(** to prove the equivalence of these 2 program, cequiv is hard to achieve
at once.
    As a result, I introduce clequiv, that simple has the left side of cequiv
    So, I will prove clequiv p5 p6 and then clequiv p6 p5.
    Finally, prove that cequiv p5 p6.

*)
Definition clequiv (c1 c2 : com) := forall (st st' : state),
  c1 / st \\ st' -> c2 / st \\ st'.
  
Lemma p5_p6_lequiv : clequiv p5 p6.
Proof.
  intros st st'.
  intro H.
  remember p5 as p5c.
  unfold p6.
  induction H;
  (* Trivial, contradiction cases. *)
  try (inversion Heqp5c);
  subst.
  (* E_WhileEnd *)
  simpl in H.
  rewrite -> negb_false_iff in H.
  apply beq_nat_true_iff in H.
  assert (Hst : t_update st X 1 = st).
    apply functional_extensionality.
    intro V. rewrite <- H.
    rewrite-> t_update_same. reflexivity.
  rewrite <- Hst at 2.
  apply E_Ass.
  reflexivity.
  (* E_WhileLoop *)
  assert (Hass : p6 / st' \\ st'').
    apply IHceval2.
    assumption.
  clear IHceval1 IHceval2 Heqp5c H H1.
  inversion H0. subst.
  inversion Hass. subst.
  assert (Hsimpl : t_update (t_update st X n) X (aeval (t_update st X n) (ANum 1))
           = t_update st X 1).
    simpl.
    apply functional_extensionality.
    intro V.
    rewrite -> t_update_shadow. reflexivity.
  rewrite -> Hsimpl.
  apply E_Ass.
  reflexivity. Qed.
  
Lemma p6_p5_lequiv : clequiv p6 p5.
Proof.
  unfold p6.
  unfold p5.
  intros st st'.
  intro H.
  inversion H; subst.
  destruct (eq_nat_dec (st X) 1).
  (* X = 1 *)
  assert (Hsimpl : t_update st X (aeval st (ANum 1)) = st).
    apply functional_extensionality.
    intro V. simpl. rewrite <- e.
    rewrite -> t_update_same.
    reflexivity.
  rewrite -> Hsimpl.
  apply E_WhileEnd.
  simpl.
  rewrite -> e.
  reflexivity.
  (* X <> 1 *)
  eapply E_WhileLoop.
  simpl.
  rewrite -> negb_true_iff.
  apply beq_nat_false_iff.
  assumption.
  unfold beq_nat.
  apply E_Havoc.
  apply E_WhileEnd.
  reflexivity. Qed.

Theorem p5_p6_equiv : cequiv p5 p6.
Proof. 
  split.
  apply p5_p6_lequiv.
  apply p6_p5_lequiv. 
Qed.


