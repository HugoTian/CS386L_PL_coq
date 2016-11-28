(**
*  CS386L Programming Languages
* Final project
* Tian Zhang (tz3272)
* Brief Introduction:
*     For the this file, I am working on for while loop equivalence, and 
      all the work is based on Maps, Imp in class. I got some idea from
      the midterm
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


(** In midterm, we extends the optional add_for_loop exercise from
    the [Imp] chapter, and we were asked to extend the language 
    of commands with C-style for loops. Now I want to prove that 
    for command and while command are equivalent, that is
    the command:

      for (c1 ; b ; c2) {
          c3
      }

    is equivalent to:

       c1 ;
       WHILE b DO
         c3 ;
         c2
       END
   are equivalent
*)

(** first of all , we will add the definition for for loop *)

Inductive com' : Type :=
  | CSkip' : com'
  | CAss' : id -> aexp -> com'
  | CSeq' : com' -> com' -> com'
  | CIf' : bexp -> com' -> com' -> com'
  | CWhile' : bexp -> com' -> com'
  | CFor' : com' -> bexp -> com' -> com' -> com'.

Inductive ceval' : com' -> state -> state -> Prop :=
  | E_Skip' : forall st, 
      ceval' CSkip' st st
  | E_Ass' : forall st a1 n x, 
      aeval st a1 = n -> 
      ceval' (CAss' x a1) st (t_update st x n)
  | E_Seq' : forall c1 c2 st st' st'', 
      ceval' c1 st st' -> 
      ceval' c2 st' st'' -> 
      ceval' (CSeq' c1 c2) st st''
  | E_IfTrue' : forall st st' b c1 c2,
      beval st b = true -> 
      ceval' c1 st st' -> 
      ceval' (CIf' b c1 c2) st st'
  | E_IfFalse' : forall st st' b c1 c2,
      beval st b = false -> 
      ceval' c2 st st' -> 
      ceval' (CIf' b c1 c2) st st'
  | E_WhileEnd' : forall b st c,
      beval st b = false ->
      ceval' (CWhile' b c) st st
  | E_WhileLoop' : forall st st' st'' b c,
      beval st b = true ->
      ceval' c st st' ->
      ceval' (CWhile' b c) st' st'' ->
      ceval' (CWhile' b c) st st''
  | E_For' : forall st st' st'' b c1 c2 c3,
      ceval' c1 st st' ->
      ceval' (CWhile' b (CSeq' c2 c3)) st' st'' ->
      ceval' (CFor' c1 b c2 c3) st st''.

(** Next step is to prove that those two programs are equivalent*)

Definition cequiv_for_while (c1 c2 : com') : Prop :=
  forall st st' : state, ceval' c1 st st' <-> ceval' c2 st st'.

Theorem for_while_equiv : forall b c1 c2 c3,
  cequiv_for_while (CFor' c1 b c2 c3) (CSeq' c1 (CWhile' b (CSeq' c2 c3))).
Proof.
  unfold cequiv_for_while.
  split; intros.
  - (* -> *)
    inversion H; subst.
    apply E_Seq' with st'0.
    apply H6.
    apply H7.
  - (* <- *)
    inversion H; subst.
    apply E_For' with st'0.
    apply H2.
    apply H5.
Qed.




