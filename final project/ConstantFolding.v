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
Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Import ListNotations.
Require Import Maps.
Require Import Imp.



(** before partial evalation, the first part I want to implement
  a more simple idea, constant folding

  An expression is constant when it contains no variable
  references. Constant folding is an optimization that finds constant
  expressions and replaces them by their values. 
  
  Some definition and proof idea is followed equiv.v in the software
  foundation book
*)

Fixpoint fold_constants_aexp (a : aexp) : aexp :=
  match a with
  | ANum n       => ANum n
  | AId i        => AId i
  | APlus a1 a2  =>
    match (fold_constants_aexp a1, fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 + n2)
    | (a1', a2') => APlus a1' a2'
    end
  | AMinus a1 a2 =>
    match (fold_constants_aexp a1, fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 - n2)
    | (a1', a2') => AMinus a1' a2'
    end
  | AMult a1 a2  =>
    match (fold_constants_aexp a1, fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 * n2)
    | (a1', a2') => AMult a1' a2'
    end
  end.

(** Example, fold 1 + 2 => 3 *)
Example fold_aexp_ex1 :
    fold_constants_aexp
      (AMult (APlus (ANum 1) (ANum 2)) (AId X))
  = AMult (ANum 3) (AId X).
Proof. reflexivity. Qed.

(** we can also fold boolean expression , if we find constant boolean expression
    we can evaluate in place *)

Fixpoint fold_constants_bexp (b : bexp) : bexp :=
  match b with
  | BTrue        => BTrue
  | BFalse       => BFalse
  | BEq a1 a2  =>
    match (fold_constants_aexp a1, fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) =>
        if beq_nat n1 n2 then BTrue else BFalse
    | (a1', a2') =>
        BEq a1' a2'
    end
  | BLe a1 a2  =>
    match (fold_constants_aexp a1, fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) =>
        if leb n1 n2 then BTrue else BFalse
    | (a1', a2') =>
        BLe a1' a2'
    end
  | BNot b1  =>
    match (fold_constants_bexp b1) with
    | BTrue => BFalse
    | BFalse => BTrue
    | b1' => BNot b1'
    end
  | BAnd b1 b2  =>
    match (fold_constants_bexp b1, fold_constants_bexp b2)
    with
    | (BTrue, BTrue) => BTrue
    | (BTrue, BFalse) => BFalse
    | (BFalse, BTrue) => BFalse
    | (BFalse, BFalse) => BFalse
    | (b1', b2') => BAnd b1' b2'
    end
  end.

Example fold_bexp_ex1 :
    fold_constants_bexp (BAnd BTrue (BNot (BAnd BFalse BTrue)))
  = BTrue.
Proof. reflexivity. Qed.

(** the next step is to fold constant in command*)
Fixpoint fold_constants_com (c : com) : com :=
  match c with
  | SKIP      =>
      SKIP
  | i ::= a  =>
      CAss i (fold_constants_aexp a)
  | c1 ;; c2  =>
      (fold_constants_com c1) ;; (fold_constants_com c2)
  | IFB b THEN c1 ELSE c2 FI =>
      match fold_constants_bexp b with
      | BTrue => fold_constants_com c1
      | BFalse => fold_constants_com c2
      | b' => IFB b' THEN fold_constants_com c1
                     ELSE fold_constants_com c2 FI
      end
  | WHILE b DO c END =>
      match fold_constants_bexp b with
      | BTrue => WHILE BTrue DO SKIP END
      | BFalse => SKIP
      | b' => WHILE b' DO (fold_constants_com c) END
      end
  end.
  
(** Example *)
Example fold_com_ex1 :
  fold_constants_com
    (* Original program: *)
    (X ::= APlus (ANum 4) (ANum 5);;
     Y ::= AMinus (AId X) (ANum 3);;
     IFB BEq (AMinus (AId X) (AId Y))
             (APlus (ANum 2) (ANum 4)) THEN
       SKIP
     ELSE
       Y ::= ANum 0
     FI;;
     IFB BLe (ANum 0)
             (AMinus (ANum 4) (APlus (ANum 2) (ANum 1))) 
     THEN
       Y ::= ANum 0
     ELSE
       SKIP
     FI;;
     WHILE BEq (AId Y) (ANum 0) DO
       X ::= APlus (AId X) (ANum 1)
     END)
  = (* After constant folding: *)
    (X ::= ANum 9;;
     Y ::= AMinus (AId X) (ANum 3);;
     IFB BEq (AMinus (AId X) (AId Y)) (ANum 6) THEN
       SKIP
     ELSE
       (Y ::= ANum 0)
     FI;;
     Y ::= ANum 0;;
     WHILE BEq (AId Y) (ANum 0) DO
       X ::= APlus (AId X) (ANum 1)
     END).
Proof. reflexivity. Qed.

(** Now we have constant folding, we need to prove that, after folding,
  the program is correct*)
  
(** Here is some definition in equiv.v to help prove that constant 
  folding is correct*)
  
  
(** First, we need to introduce the behaviorally equivalent 
    that two aexp or bexp are behaviorally equivalent if they
    evaluate to the same result in every state. *)

Definition aequiv (a1 a2 : aexp) : Prop :=
  forall (st:state),
    aeval st a1 = aeval st a2.

Definition bequiv (b1 b2 : bexp) : Prop :=
  forall (st:state),
    beval st b1 = beval st b2.


Definition cequiv (c1 c2 : com) : Prop :=
  forall (st st' : state),
    (c1 / st \\ st') <-> (c2 / st \\ st').

(** ** Behavioral Equivalence Is an Equivalence
    the equivalence can be proved by reflexive,
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

(** Prove that adding a SKIP after a command results in an
    equivalent program *)
    
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
    + (* b evaluates to true *)
      assumption.
    + (* b evaluates to false (contradiction) *)
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

(** A loop whose guard is equivalent to BFalse is equivalent to SKIP,
    while a loop whose guard is equivalent to [BTrue] is equivalent to
    WHILE BTrue DO SKIP END  *)

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
    
Lemma WHILE_true_nonterm : forall b c st st',
     bequiv b BTrue ->
     ~( (WHILE b DO c END) / st \\ st' ).
Proof.
  (* WORKED IN CLASS *)
  intros b c st st' Hb.
  intros H.
  remember (WHILE b DO c END) as cw eqn:Heqcw.
  induction H;
    (* Most rules don't apply, and we can rule them out
       by inversion *)
    inversion Heqcw; subst; clear Heqcw.
  (* The two interesting cases are the ones for WHILE loops: *)
  - (* E_WhileEnd *) (* contradictory -- b is always true! *)
    unfold bequiv in Hb.
    (* [rewrite] is able to instantiate the quantifier in [st] *)
    rewrite Hb in H. inversion H.
  - (* E_WhileLoop *) (* immediate from the IH *)
    apply IHceval2. reflexivity.  Qed.

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

(** ** Behavioral Equivalence Is a Congruence *)

(** behavioral equivalence is also a congruence
    The equivalence of two subprograms implies the
    equivalence of the larger programs in which they are embedded *)

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
    rewrite Heqv. reflexivity.  
Qed.

Theorem CWhile_congruence : forall b1 b1' c1 c1',
  bequiv b1 b1' -> cequiv c1 c1' ->
  cequiv (WHILE b1 DO c1 END) (WHILE b1' DO c1' END).
Proof.
  (* WORKED IN CLASS *)
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


(** A program transformation is _sound_ if it preserves the
    behavior of the original program. *)

Definition atrans_sound (atrans : aexp -> aexp) : Prop :=
  forall (a : aexp),
    aequiv a (atrans a).

Definition btrans_sound (btrans : bexp -> bexp) : Prop :=
  forall (b : bexp),
    bequiv b (btrans b).

Definition ctrans_sound (ctrans : com -> com) : Prop :=
  forall (c : com),
    cequiv c (ctrans c).

(** The prove has 3 parts, for aexp, bexp and command *)
    
Theorem fold_constants_aexp_sound :
  atrans_sound fold_constants_aexp.
Proof.
  unfold atrans_sound. intros a. unfold aequiv. intros st.
  induction a; simpl;
    try reflexivity;
    try (destruct (fold_constants_aexp a1);
         destruct (fold_constants_aexp a2);
         rewrite IHa1; rewrite IHa2; reflexivity). 
Qed.



Theorem fold_constants_bexp_sound:
  btrans_sound fold_constants_bexp.
Proof.
  unfold btrans_sound. intros b. unfold bequiv. intros st.
  induction b;
   
    try reflexivity.
  - rename a into a1. rename a0 into a2. simpl.
    remember (fold_constants_aexp a1) as a1' eqn:Heqa1'.
    remember (fold_constants_aexp a2) as a2' eqn:Heqa2'.
    replace (aeval st a1) with (aeval st a1') by
       (subst a1'; rewrite <- fold_constants_aexp_sound; reflexivity).
    replace (aeval st a2) with (aeval st a2') by
       (subst a2'; rewrite <- fold_constants_aexp_sound; reflexivity).
    destruct a1'; destruct a2'; try reflexivity.
    simpl. destruct (beq_nat n n0); reflexivity.
  - (* BLe *)
    rename a into a1. rename a0 into a2. simpl.
    remember (fold_constants_aexp a1) as a1' eqn:Heqa1'.
    remember (fold_constants_aexp a2) as a2' eqn:Heqa2'.
    replace (aeval st a1) with (aeval st a1') by
      (subst a1'; rewrite <- fold_constants_aexp_sound; reflexivity).
    replace (aeval st a2) with (aeval st a2') by
      (subst a2'; rewrite <- fold_constants_aexp_sound; reflexivity).
    destruct a1'; destruct a2'; auto.
    simpl. destruct ( n <=? n0); auto.
  - (* BNot *)
    simpl. remember (fold_constants_bexp b) as b' eqn:Heqb'.
    rewrite IHb.
    destruct b'; reflexivity.
  - (* BAnd *)
    simpl.
    remember (fold_constants_bexp b1) as b1' eqn:Heqb1'.
    remember (fold_constants_bexp b2) as b2' eqn:Heqb2'.
    rewrite IHb1. rewrite IHb2.
    destruct b1'; destruct b2'; simpl; try reflexivity
    ; eauto using andb_true_l, andb_true_r, andb_false_l, andb_false_r.
Qed.



Theorem fold_constants_com_sound :
  ctrans_sound fold_constants_com.
Proof.
  unfold ctrans_sound. intros c.
  induction c; simpl.
  - (* SKIP *) apply refl_cequiv.
  - (* ::= *) apply CAss_congruence.
              apply fold_constants_aexp_sound.
  - (* ;; *) apply CSeq_congruence; assumption.
  - (* IFB *)
    assert (bequiv b (fold_constants_bexp b)). {
      apply fold_constants_bexp_sound. }
    destruct (fold_constants_bexp b) eqn:Heqb;
      try (apply CIf_congruence; assumption).

    + (* b always true *)
      apply trans_cequiv with c1; try assumption.
      apply IFB_true; assumption.
    + (* b always false *)
      apply trans_cequiv with c2; try assumption.
      apply IFB_false; assumption.
  - (* WHILE *)
    assert (bequiv b (fold_constants_bexp b)).
    apply fold_constants_bexp_sound.
    destruct (fold_constants_bexp b) eqn:Hb; try (apply CWhile_congruence; assumption; assumption).
    apply WHILE_true with (c:=c) in H.
    assumption.
    apply WHILE_false with (c:=c) in H.
    assumption.
Qed.

