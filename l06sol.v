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
    induction xs.
    auto.
    simpl.
    intros.
    apply ICons; intros.
    (* Ugh! We could prove some lemmas about Dec, but instead
       let’s use a more convenient induction principle. *)
  Abort.


  (* Reverse induction on lists: *)
  Lemma rev_ind {A} (P:list A -> Prop):
      P [] ->
      (forall a l, P l -> P (l ++ [a])) ->
      (forall l, P l).
    (* But this is difficult to prove from scratch.
       We need one more helper induction principle. *)
  Abort.

  Lemma rev_ind' {A} (P:list A -> Prop):
      P [] ->
      (forall a l, P (rev l) -> P (rev (a :: l))) ->
      (forall l, P (rev l)).
    (* This induction principle is easier to prove
       because, in the inductive hypotheses, `l` grows
       in the normal way (from the front). *)
    intros; induction l; auto.
  Qed.

  Lemma rev_ind {A} (P:list A -> Prop):
      P [] ->
      (forall a l, P l -> P (l ++ [a])) ->
      (forall l, P l).
    intros.
    rewrite <- (rev_involutive l). (* `rev (rev l) = l` *)
    apply rev_ind'; auto.
    intros.
    simpl.
    apply H0.
    auto.
  Qed.


  (* We’ve proved the new induction principle correct,
     so we can use it. *)
  Lemma Dec_rev xs: Dec (rev xs) -> Inc xs.
    induction xs using rev_ind; auto.
    rewrite rev_unit. (* `rev (xs ++ [a]) = a :: rev xs` *)
    intros; inversion H; subst.
    apply Inc_app.
    - apply IHxs; auto.
    - apply ICons; intros.
      + destruct H0.
      + auto.
    - intros; destruct H1.
      + subst.
        apply H2.
        apply in_rev in H0.
        auto.
      + destruct H1.
  Qed.


  (* The proof gets easier if we tell Coq `auto` to
     automatically resolve `In _ nil` hypotheses. *)
  Hint Extern 1 => match goal with
                   | [ H : In _ nil |- _ ] => destruct H
                   end.

  Lemma Dec_rev' xs: Dec (rev xs) -> Inc xs.
    induction xs using rev_ind; auto.
    rewrite rev_unit. (* `rev (xs ++ [a]) = a :: rev xs` *)
    intros; inversion H; subst.
    apply Inc_app.
    - apply IHxs; auto.
    - apply ICons; intros; auto.
    - intros; destruct H1; auto.
      apply in_rev in H0; subst; auto.
  Qed.

End Lecture6.
