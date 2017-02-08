Require Import Arith.
Require Import Omega.
Require Import Recdef.
Require Import List.
Require Import Program.Tactics.
Import ListNotations.

Section Lecture6.

  (* True iff the list’s elements are in decreasing order *)
  Inductive Dec : list nat -> Prop :=
  | DNil : Dec []
  | DCons : forall a l,
      (forall b, In b l -> a <= b) ->
      Dec l ->
      Dec (a :: l).
  Hint Constructors Dec.

  (* True iff the list’s elements are in INcreasing order *)
  Inductive Inc : list nat -> Prop :=
  | INil : Inc []
  | ICons : forall a l,
      (forall b, In b l -> b <= a) ->
      Inc l ->
      Inc (a :: l).
  Hint Constructors Inc.

  (* A fact about appending increasing lists *)
  Lemma Inc_app xs ys:
    Inc xs -> Inc ys ->
    (forall x y, In x xs -> In y ys -> y <= x) ->
    Inc (xs ++ ys).
  Admitted.


  Lemma Dec_rev xs: Dec (rev xs) -> Inc xs.
  Abort.

End Lecture6.
