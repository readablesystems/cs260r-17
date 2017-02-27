Require Import Arith.
Require Import Omega.
Require Import Recdef.
Require Import List.
Require Import Program.Tactics.
Require Import Program.Equality.
Require Import Sorting.Permutation.
Import ListNotations.

Variable A:Type.
Implicit Types l : list A.


(* This Ltac performs inversion on `Add` terms where the result list
   is a cons. *)
Ltac InvAdd := repeat (match goal with
 | H: Add ?x _ (_ :: _) |- _ => inversion H; clear H; subst
 end).


(* Let’s try to prove Permutation_Add_inv without a new induction
   principle! Look where we get stuck. *)

Theorem Permutation_Add_inv' a l1 l2 :
  Permutation l1 l2 ->
  forall l1' l2', Add a l1' l1 ->
                  Add a l2' l2 ->
                  Permutation l1' l2'.
Proof.
  revert l1 l2.
  refine (Permutation_ind _ _ _ _ _).
  - (* nil *)
    intros.
    inversion H.
  - (* skip *)
    intros x l1 l2 PE IH. intros.
    InvAdd.
    + auto.
    + rewrite <- PE. now apply Permutation_Add.
    + rewrite PE. symmetry. now apply Permutation_Add.
    + apply perm_skip. now apply IH.
  - (* swap *)
    intros x y l l1 l2 A1 A2. intros.
    Check Permutation_ind.
    (* DAMN *)
    admit.
  - (* trans *)
    intros l1 l l2 PE IH PE' IH' l1' l2' AD1 AD2.
    assert (Ha : In a l).
    { rewrite <- PE. rewrite (Add_in AD1). simpl; auto. }
    destruct (Add_inv _ _ Ha) as (l',AD).
    transitivity l'.
    now apply IH.
    now apply IH'.
Abort.


(* This new induction principle is inspired by the place we got stuck. *)

Lemma Permutation_ind_bis:
  forall P: list A -> list A -> Prop,
    (* nil: *)
    P [] [] ->
    (* skip/cons: *)
    (forall a l l', Permutation l l' -> P l l' ->
                    P (a :: l) (a :: l')) ->
    (* generalized swap: *)
    (forall x y l l', Permutation l l' -> P l l' ->
                      P (x :: y :: l) (y :: x :: l')) ->
    (* trans: *)
    (forall l l' l'', Permutation l l' -> P l l' ->
                      Permutation l' l'' -> P l' l'' ->
                      P l l'') ->
    (* ...imply true for all *)
    forall l l', Permutation l l' -> P l l'.
  intros P Hnil Hcons Hswap Htrans l l' PE.
  induction PE.
  auto.
  apply Hcons; auto.
  apply Hswap.
  apply Permutation_refl.
  induction l; auto.
  apply Htrans with (l':=l'); auto.
Qed.


(* Now we can prove Add_inv! *)

Theorem Permutation_Add_inv a l1 l2 :
  Permutation l1 l2 ->
  forall l1' l2', Add a l1' l1 ->
                  Add a l2' l2 ->
                  Permutation l1' l2'.
Proof.
  revert l1 l2.
  refine (Permutation_ind_bis _ _ _ _ _).
  - (* nil *)
    inversion_clear 1.
  - (* skip *)
    intros x l1 l2 PE IH. intros.
    InvAdd.
    + auto.
    + rewrite <- PE. now apply Permutation_Add.
    + rewrite PE. symmetry. now apply Permutation_Add.
    + apply perm_skip. now apply IH.
  - (* swap *)
    intros x y l1 l2 PE IH. intros.
    InvAdd.
    + now constructor.
    + now constructor.
    + constructor. rewrite <- PE. now apply Permutation_Add.
    + now constructor.
    + now constructor.
    + rewrite perm_swap. constructor. rewrite <- PE.
      now apply Permutation_Add.
    + constructor. rewrite PE. symmetry.
      now apply Permutation_Add.
    + rewrite perm_swap. constructor. rewrite PE. symmetry.
      now apply Permutation_Add.
    + (* The case that needs the inductive hypothesis! *)
      rewrite perm_swap. constructor. constructor.
      now apply IH.
  - (* trans *)
    intros l1 l l2 PE IH PE' IH' l1' l2' AD1 AD2.
    assert (Ha : In a l).
    { rewrite <- PE. rewrite (Add_in AD1). simpl; auto. }
    destruct (Add_inv _ _ Ha) as (l',AD).
    transitivity l'.
    now apply IH.
    now apply IH'.
Qed.


(* A little more Ltac makes this easier to prove, but harder to
   investigate the proof. This is basically the library’s proof
   (the library uses `auto` here and there). *)

Ltac finish_basic_perms H :=
  try constructor; try rewrite perm_swap; try constructor; trivial;
  (rewrite <- H; now apply Permutation_Add) ||
  (rewrite H; symmetry; now apply Permutation_Add).

Theorem Permutation_Add_inv' a l1 l2 :
  Permutation l1 l2 ->
  forall l1' l2', Add a l1' l1 ->
                  Add a l2' l2 ->
                  Permutation l1' l2'.
Proof.
  revert l1 l2.
  refine (Permutation_ind_bis _ _ _ _ _).
  - (* nil *)
    inversion_clear 1.
  - (* skip *)
    intros x l1 l2 PE IH. intros.
    InvAdd; try finish_basic_perms PE.
    apply perm_skip. now apply IH.
  - (* swap *)
    intros x y l1 l2 PE IH. intros.
    InvAdd; try finish_basic_perms PE.
    (* The case that needs the inductive hypothesis! *)
    rewrite perm_swap. do 2 constructor. now apply IH.
  - (* trans *)
    intros l1 l l2 PE IH PE' IH' l1' l2' AD1 AD2.
    assert (Ha : In a l).
    { rewrite <- PE. rewrite (Add_in AD1). simpl; auto. }
    destruct (Add_inv _ _ Ha) as (l',AD).
    transitivity l'.
    now apply IH.
    now apply IH'.
Qed.
