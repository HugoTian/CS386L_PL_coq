(**
*  CS386L Programming Languages
* Final project
* Tian Zhang (tz3272)
* Brief Introduction:
*     This file contains proof for program equivalence, a starting point
*     For my final project
*     All the proof is based on Imp.v 
*     Some example and proof are followed content from equiv.v
*)

Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Import ListNotations.
Require Import Maps.
Require Import Imp.


(** Two aexp or bexp are behaviorally equivalent if they
    evaluate to the same result in every state *)

Definition aequiv (a1 a2 : aexp) : Prop :=
  forall (st:state),
    aeval st a1 = aeval st a2.

Definition bequiv (b1 b2 : bexp) : Prop :=
  forall (st:state),
    beval st b1 = beval st b2.

(** Two commands are behaviorally equivalent
    if, for any given starting state, they either both diverge or both
    terminate in the same final state.*)

Definition cequiv (c1 c2 : com) : Prop :=
  forall (st st' : state),
    (c1 / st \\ st') <-> (c2 / st \\ st').


(** Here is some command equivalent example*)

(** SKIP , skip in command left and skip in command right*)

Theorem skip_left: forall c,
  cequiv 
     (SKIP;; c) 
     c.
Proof. 
  intros c st st'.
  split; intros H.
  - (* -> *) 
    inversion H. subst. 
    inversion H2. subst. 
    assumption.
  - (* <- *) 
    apply E_Seq with st.
    apply E_Skip. 
    assumption.  
Qed.


Theorem skip_right: forall c,
  cequiv 
    (c;; SKIP) 
    c.
Proof.
  intros.
  split; intros.
  - (* -> *)
    inversion H.
    simpl. subst. inversion H5.
    subst.
    assumption.
  - (* <- *)
  apply E_Seq with st'.
  assumption.
  apply E_Skip.
Qed.

(** IFB, (IFB b THEN c1 ELSE c2 FI), if clause evaluate to true , 
    then goto c1
    If evaluate to false, then goto c2
*)


Theorem IFB_true: forall b c1 c2,
     bequiv b BTrue  ->
     cequiv
       (IFB b THEN c1 ELSE c2 FI)
       c1.
Proof.
  intros b c1 c2 Hb.
  split; intros H.
  - (* -> *)
    inversion H; subst.
    + (* b == true *)
      assumption.
    + (* b == false *)
      unfold bequiv in Hb. simpl in Hb.
      rewrite Hb in H5.
      inversion H5.
  - (* <- *)
    apply E_IfTrue; try assumption.
    unfold bequiv in Hb. simpl in Hb.
    rewrite Hb. reflexivity.  Qed.


Theorem IFB_false: forall b c1 c2,
  bequiv b BFalse  ->
  cequiv
    (IFB b THEN c1 ELSE c2 FI)
    c2.
Proof.
  intros b c1 c2 Hb.
  split; intros H.
  - (* -> *)
    inversion H; subst.
    + (* b => true *)
    unfold bequiv in Hb.
    rewrite Hb in H5. inversion H5.
    + (* b => false *)
    assumption.
  - (* <- *)
    apply E_IfFalse.
    unfold bequiv in Hb.
    simpl in Hb. apply Hb.
    assumption.
Qed.


(** swap_if_branches,
    swap the if else cases by negating the if clause
  *)

Lemma beval_neg : forall st b b',
                    beval st (BNot b) = b' -> beval st b = negb b'.
Proof.
  intros.
  destruct b'; simpl in H; symmetry in H; apply negb_sym in H; assumption.
Qed. 

Theorem swap_if_branches: forall b e1 e2,
  cequiv
    (IFB b THEN e1 ELSE e2 FI)
    (IFB BNot b THEN e2 ELSE e1 FI).
Proof.
  intros.
  split; intros.
  - (* -> *)
  inversion H; subst.
  apply E_IfFalse. simpl. rewrite H5. reflexivity.
  assumption.
  apply E_IfTrue. simpl. rewrite H5. reflexivity.
  assumption.
  - (* <- *)
  inversion H; subst.
    + (* False *)
    apply E_IfFalse.
    apply beval_neg in H5; simpl in H5; assumption.
    assumption.
    + (*True *)
    apply E_IfTrue.
    apply beval_neg in H5; simpl in H5; assumption.
    assumption.
Qed.


(** WHILE loops, if while clause evaluate to false, then it is similar
  to skip
 *)

Theorem WHILE_false : forall b c,
     bequiv b BFalse ->
     cequiv
       (WHILE b DO c END)
       SKIP.
Proof.
  intros b c Hb. split; intros H.
  - (* -> *)
    inversion H; subst.
    + (* E_WhileEnd *)
      apply E_Skip.
    + (* E_WhileLoop *)
      rewrite Hb in H2. inversion H2.
  - (* <- *)
    inversion H; subst.
    apply E_WhileEnd.
    rewrite Hb.
    reflexivity.  Qed.



(** When while clause evaluate to true, it will never terminate,
    Here is the lemma,

    If b is equivalent to [BTrue], then it cannot be the
    case that [(WHILE b DO c END) / st \\ st'].
*)

Lemma WHILE_true_nonterm : forall b c st st',
     bequiv b BTrue ->
     ~( (WHILE b DO c END) / st \\ st' ).
Proof.

  intros b c st st' Hb.
  intros H.
  remember (WHILE b DO c END) as cw eqn:Heqcw.
  induction H;
    (*by inversion *)
    inversion Heqcw; subst; clear Heqcw.
  - (* E_WhileEnd *) (* contradictory -- b is always true! *)
    unfold bequiv in Hb.
    (* [rewrite] is able to instantiate the quantifier in [st] *)
    rewrite Hb in H. inversion H.
  - (* E_WhileLoop *) (* immediate from the IH *)
    apply IHceval2. reflexivity.  Qed.


(** now we have lemma, we can evaluate while true *)

Theorem ex_falso_quodlibet : forall (P:Prop), False -> P.
Proof.
  intros. inversion H.
Qed.

Lemma skip_state : forall st st',
                     SKIP / st \\ st' -> st = st'.
Proof.
  intros.
  inversion H. subst.
  reflexivity.
Qed.


Theorem WHILE_true: forall b c,
     bequiv b BTrue  ->
     cequiv
       (WHILE b DO c END)
       (WHILE BTrue DO SKIP END).
Proof.
  intros.
  intros st st'. split.
  - (* -> *) 
    intros.
    apply WHILE_true_nonterm with (c:=c) (st:=st) (st':=st') in H.
    apply ex_falso_quodlibet.
    apply H in H0. assumption.
  - (* <- *)
  intros.
  remember (WHILE BTrue DO SKIP END).
  induction H0; inversion Heqc0. 
    + (* E_WhileEnd *)
  subst. simpl in H0. inversion H0.
    + (* E_WhileLoop *)
  subst.
  clear IHceval1.
  rename H0_ into Hst.
  apply skip_state in Hst.
  rewrite Hst.
  apply IHceval2.
  assumption.
Qed.


(** another key concept in loop is loop unrolling , programms are
    behaviorally equivalent if we perform the loop unrolling
*)

Theorem loop_unrolling: forall b c,
  cequiv
    (WHILE b DO c END)
    (IFB b THEN (c;; WHILE b DO c END) ELSE SKIP FI).
Proof.
  intros b c st st'.
  split; intros Hce.
  - (* -> *)
    inversion Hce; subst.
    + (* loop doesn't run *)
      apply E_IfFalse. assumption. apply E_Skip.
    + (* loop runs *)
      apply E_IfTrue. assumption.
      apply E_Seq with (st' := st'0). assumption. assumption.
  - (* <- *)
    inversion Hce; subst.
    + (* loop runs *)
      inversion H5; subst.
      apply E_WhileLoop with (st' := st'0).
      assumption. assumption. assumption.
    + (* loop doesn't run *)
      inversion H5; subst. apply E_WhileEnd. assumption.  Qed.


(** change the associativity of command *)


Theorem seq_assoc : forall c1 c2 c3,
  cequiv ((c1;;c2);;c3) (c1;;(c2;;c3)).
Proof.
 intros.
  split; intros.
  - (* -> *)
  inversion H; subst.
  inversion H2; subst.
  apply E_Seq with (st':=st'1).
  assumption.
  apply E_Seq with (st':=st'0).
  assumption.
  assumption.
  - (* <- *)
  inversion H; subst.
  inversion H5; subst.
  apply E_Seq with (st':=st'1).
  apply E_Seq with (st':=st'0).
  assumption.
  assumption.
  assumption.
Qed.


(** Assignment , simple example is like indentity assignment *)

Theorem identity_assignment : forall (X:id),
  cequiv
    (X ::= AId X)
    SKIP.
Proof.
   intros. split; intro H.
     - (* -> *)
       inversion H; subst. simpl.
       replace (t_update st X (st X)) with st.
       + constructor.
       + apply functional_extensionality. intro.
         rewrite t_update_same; reflexivity.
     - (* <- *)
       replace st' with (t_update st' X (aeval st' (AId X))).
       + inversion H. subst. apply E_Ass. reflexivity.
       + apply functional_extensionality. intro.
         rewrite t_update_same. reflexivity.
Qed.

(** Another theorem about assignment simple, no need to assign twices
if X already evaluate to e*)


Theorem assign_aequiv : forall X e,
  aequiv (AId X) e ->
  cequiv SKIP (X ::= e).
Proof.
intros.
  split; intro He.
  - (* -> *)
  apply skip_state in He.
  unfold aequiv in H.
  assert (st' = (t_update st' X (st' X))).
    apply functional_extensionality. intro.
    rewrite t_update_same; reflexivity.
  rewrite H0.
  rewrite He.
  apply E_Ass.
  rewrite <- H.
  simpl. reflexivity.
  - (* <- *)
  inversion He.
  subst.
  assert (st = t_update st X (st X)).
    apply functional_extensionality. intros.
    rewrite t_update_same; reflexivity.
  rewrite H0 in He at 1.
  inversion He.
  rewrite <- H0 in H4.
  unfold aequiv in H.
  rewrite <- H in H5.
  simpl in H5.
  rewrite H5.
  rewrite <- H0.
  apply E_Skip.
Qed.





(** Now we show the detail of program equivalence, and the next step
is show the  Properties of Behavioral Equivalence , in order to help further
proof about constant folding and partial evaluation
*)

(** First, we verify that the equivalences on aexps, bexps, and
    coms are eflexive,
    symmetric, and transitive. *)

Lemma refl_aequiv : forall (a : aexp), aequiv a a.
Proof.
  intros a st. reflexivity.  Qed.

Lemma sym_aequiv : forall (a1 a2 : aexp),
  aequiv a1 a2 -> aequiv a2 a1.
Proof.
  intros a1 a2 H. intros st. symmetry. apply H.  Qed.

Lemma trans_aequiv : forall (a1 a2 a3 : aexp),
  aequiv a1 a2 -> aequiv a2 a3 -> aequiv a1 a3.
Proof.
  unfold aequiv. intros a1 a2 a3 H12 H23 st.
  rewrite (H12 st). rewrite (H23 st). reflexivity.  Qed.

Lemma refl_bequiv : forall (b : bexp), bequiv b b.
Proof.
  unfold bequiv. intros b st. reflexivity.  Qed.

Lemma sym_bequiv : forall (b1 b2 : bexp),
  bequiv b1 b2 -> bequiv b2 b1.
Proof.
  unfold bequiv. intros b1 b2 H. intros st. symmetry. apply H.  Qed.

Lemma trans_bequiv : forall (b1 b2 b3 : bexp),
  bequiv b1 b2 -> bequiv b2 b3 -> bequiv b1 b3.
Proof.
  unfold bequiv. intros b1 b2 b3 H12 H23 st.
  rewrite (H12 st). rewrite (H23 st). reflexivity.  Qed.

Lemma refl_cequiv : forall (c : com), cequiv c c.
Proof.
  unfold cequiv. intros c st st'. apply iff_refl.  Qed.

Lemma sym_cequiv : forall (c1 c2 : com),
  cequiv c1 c2 -> cequiv c2 c1.
Proof.
  unfold cequiv. intros c1 c2 H st st'.
  assert (c1 / st \\ st' <-> c2 / st \\ st') as H'.
  { (* Proof of assertion *) apply H. }
  apply iff_sym. assumption.
Qed.

Lemma iff_trans : forall (P1 P2 P3 : Prop),
  (P1 <-> P2) -> (P2 <-> P3) -> (P1 <-> P3).
Proof.
  intros P1 P2 P3 H12 H23.
  inversion H12. inversion H23.
  split; intros A.
    apply H1. apply H. apply A.
    apply H0. apply H2. apply A.  Qed.

Lemma trans_cequiv : forall (c1 c2 c3 : com),
  cequiv c1 c2 -> cequiv c2 c3 -> cequiv c1 c3.
Proof.
  unfold cequiv. intros c1 c2 c3 H12 H23 st st'.
  apply iff_trans with (c2 / st \\ st'). apply H12. apply H23.  Qed.


(** The next step is to prove Behavioral Equivalence is a Congruence 
    That is, the equivalence of two subprograms implies the
    equivalence of the larger programs in which they are embedded:


              cequiv c1 c1'
              cequiv c2 c2'
         ------------------------
         cequiv (c1;;c2) (c1';;c2')
*)


(** First, aquiv cases, which is simple,
              aequiv a1 a1'
      -----------------------------
      cequiv (i ::= a1) (i ::= a1')
*)

Theorem CAss_congruence : forall i a1 a1',
  aequiv a1 a1' ->
  cequiv (CAss i a1) (CAss i a1').
Proof.
  intros i a1 a2 Heqv st st'.
  split; intros Hceval.
  - (* -> *)
    inversion Hceval. subst. apply E_Ass.
    rewrite Heqv. reflexivity.
  - (* <- *)
    inversion Hceval. subst. apply E_Ass.
    rewrite Heqv. reflexivity.  Qed.
    
(** Next case is while loop,
                    bequiv b1 b1'
      --------------------------------------------------
      cequiv (WHILE b1 DO c1 END) (WHILE b1' DO c1' END).
*)
Theorem CWhile_congruence : forall b1 b1' c1 c1',
  bequiv b1 b1' -> cequiv c1 c1' ->
  cequiv (WHILE b1 DO c1 END) (WHILE b1' DO c1' END).
Proof.
  unfold bequiv,cequiv.
  intros b1 b1' c1 c1' Hb1e Hc1e st st'.
  split; intros Hce.
  - (* -> *)
    remember (WHILE b1 DO c1 END) as cwhile
      eqn:Heqcwhile.
    induction Hce; inversion Heqcwhile; subst.
    + (* E_WhileEnd *)
      apply E_WhileEnd. rewrite <- Hb1e. apply H.
    + (* E_WhileLoop *)
      apply E_WhileLoop with (st' := st').
      * (* show loop runs *) rewrite <- Hb1e. apply H.
      * (* body execution *)
        apply (Hc1e st st').  apply Hce1.
      * (* subsequent loop execution *)
        apply IHHce2. reflexivity.
  - (* <- *)
    remember (WHILE b1' DO c1' END) as c'while
      eqn:Heqc'while.
    induction Hce; inversion Heqc'while; subst.
    + (* E_WhileEnd *)
      apply E_WhileEnd. rewrite -> Hb1e. apply H.
    + (* E_WhileLoop *)
      apply E_WhileLoop with (st' := st').
      * (* show loop runs *) rewrite -> Hb1e. apply H.
      * (* body execution *)
        apply (Hc1e st st').  apply Hce1.
      * (* subsequent loop execution *)
        apply IHHce2. reflexivity.  Qed.

(** the next case is about command sequence
                    cequiv c1 c1' 
                    cequiv c2 c2'
           -----------------------------
           cequiv (c1;;c2) (c1';;c2').
*)
Theorem CSeq_congruence : forall c1 c1' c2 c2',
  cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (c1;;c2) (c1';;c2').
Proof.
  intros. unfold cequiv. split; intros He.
  - (* <- *)
  unfold cequiv in *. inversion He. subst.
  apply H with (st':=st'0) in H3.
  apply H0 with (st:=st'0) in H6.
  apply E_Seq with (st':=st'0). assumption.
  assumption.
  - (* -> *)
  unfold cequiv in *.
  inversion He. subst.
  apply H with (st':=st'0) in H3.
  apply H0 with (st:=st'0) in H6.
  apply E_Seq with (st':=st'0).
  assumption.
  assumption.
Qed.

(** The final case is about if
                    bequiv b b'
                    cequiv c1 c1' 
                    cequiv c2 c2'
         ----------------------------------------------------
   cequiv (IFB b THEN c1 ELSE c2 FI) (IFB b' THEN c1' ELSE c2' FI).

*)
Theorem CIf_congruence : forall b b' c1 c1' c2 c2',
  bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (IFB b THEN c1 ELSE c2 FI)
         (IFB b' THEN c1' ELSE c2' FI).
Proof.
  intros.
  unfold cequiv.
  split; intro He.
  - (* -> *)
  unfold cequiv in *.
  unfold bequiv in H.
  inversion He; subst.
    + (* b => true *)
    apply E_IfTrue. rewrite H in H7. assumption.
    rewrite H0 in H8. assumption.
    + (* b => false *)
    apply E_IfFalse. rewrite H in H7. assumption.
    rewrite H1 in H8. assumption.
  - (* <- *)
  unfold cequiv in *.
  unfold bequiv in H.
  symmetry in H.
  inversion He; subst.
     + (* b => true *)
  apply E_IfTrue. rewrite H in H7. assumption.
  rewrite <- H0 in H8. assumption.
     + (* b => false *)
  apply E_IfFalse. rewrite H in H7. assumption.
  rewrite <- H1 in H8. assumption.
Qed.

(** Now we finish the definition and proof about behaviorally equivalence
    the next step is to use those definition and proof in constant propagation
    and partial evaluation
*)
