Require Import Arith.
Require Import Omega.
Require Import Recdef.
Require Import List.
Require Import Program.Tactics.
Require Import Program.Equality.
Import ListNotations.

(* You may find this lemma useful later. *)
Lemma in_middle: forall {A} a (xs1 xs2:list A), In a (xs1 ++ a :: xs2).
  induction xs1; intros; simpl; [ left | right ]; auto.
Qed.


Section Pset2PermutationDef.
  (* All definitions in this section will be predicated on a type
     argument, A. *)
  Context {A: Type}.


  (* PERMUTATIONS

     List `xs` is a permutation of list `ys` iff `xs` and `ys` have
     the same elements regardless of order. Coq’s library comes with
     an inductive definition of permutations: `xs` is a permutation of
     `ys` iff `xs` can be obtained from `ys` via a series of swap
     operations. This is maybe a little surprising, but it works
     great. This problem set section has you work with this
     definition. We repeat the definition (using the library’s terms)
     and prove many library lemmas. *)


  (* A Permutation is a relation between lists of A, so a permutation
     proposition looks like `Permutation x y`. *)

  Inductive Permutation: list A -> list A -> Prop :=

  (* The empty list is a permutation of itself. *)
  | perm_nil: Permutation [] []

  (* Adding an element preserves the permutation relation.
     (Called `perm_skip` rather than `perm_cons` because `apply`ing
     it in a theorem conclusion removes an element.) *)
  | perm_skip : forall a xs ys,
      Permutation xs ys -> Permutation (a :: xs) (a :: ys)

  (* Swapping the head elements preserves the permutation relation. *)
  | perm_swap : forall a b xs,
      Permutation (a :: b :: xs) (b :: a :: xs)

  (* Permutation is closed under transitivity. *)
  | perm_trans : forall xs ys zs,
      Permutation xs ys -> Permutation ys zs -> Permutation xs zs.

End Pset2PermutationDef.


Section Pset2PermutationEx.
  (* Prove that a permutation exists, the painful way *)
  Example sample_permutation:
    Permutation [1; 2; 3; 4; 5] [4; 1; 5; 2; 3].
  Proof.
    apply perm_trans with (ys:=[1; 4; 5; 2; 3]);
      [ | (* proving `Permutation [1; 4; 5; 2; 3] [4; 1; 5; 2; 3]`: *)
          apply perm_swap ].
    apply perm_skip.
    apply perm_trans with (ys:=[4; 2; 5; 3]);
      [ | (* proving `Permutation [4; 2; 5; 3] [4; 5; 2; 3]`: *)
          apply perm_skip;
          apply perm_swap ].
    apply perm_trans with (ys:=[2; 4; 5; 3]);
      [ | apply perm_swap ].
    apply perm_skip.
    apply perm_trans with (ys:=[4; 3; 5]);
      [ | apply perm_skip;
          apply perm_swap ].
    apply perm_trans with (ys:=[3; 4; 5]);
      [ | apply perm_swap ].
    apply perm_skip.
    apply perm_skip.
    apply perm_skip.
    apply perm_nil.
  Qed.


  (* This says that Permutation constructors should be applied by
     `auto` and `eauto`. *)
  Hint Constructors Permutation.

  Example sample_permutation':
    Permutation [1; 2; 3; 4; 5] [4; 1; 5; 2; 3].
  Proof.
    (* Note how `Hint Constructors` simplifies the proof! When a constructor
       applies, `auto` applies it. *)
    apply perm_trans with (ys:=[1; 4; 5; 2; 3]); auto.
    constructor. (* Applies the first constructor that works. *)
    apply perm_trans with (ys:=[4; 2; 5; 3]); auto.
    apply perm_trans with (ys:=[2; 4; 5; 3]); auto.
    constructor.
    apply perm_trans with (ys:=[4; 3; 5]); auto.
  Qed.
End Pset2PermutationEx.


Section Pset2PermutationLemmas.
  Hint Constructors Permutation.
  Context {A: Type}.

  (* We can perform induction on permutation hypotheses. The induction
     cases are just the induction constructors. Here are three simple
     lemmas to show how that works. *)

  Lemma Permutation_nil (xs:list A):
    Permutation xs [] -> xs = [].
  Proof.
    intros.
    (* need to `remember` the empty set or induction will fail! *)
    remember nil as ys.
    induction H.
    - auto.
    - discriminate.
    - discriminate.
    - pose (IHPermutation2 Heqys); rewrite e in *.
      pose (IHPermutation1 Heqys). auto.

    (* With a bit of care, a shorter proof appears. *)
    Restart.
    intros; remember nil as ys in H. (* NB remember ONLY in H! *)
    induction H; try discriminate; auto.
  Qed.


  Lemma Permutation_refl (xs:list A):
    Permutation xs xs.
  Proof.
    (* Sometimes it’s easier to induct on the list. *)
    induction xs; auto.
  Qed.
  Local Hint Resolve Permutation_refl.


  Lemma Permutation_sym (xs ys:list A):
    Permutation xs ys -> Permutation ys xs.
  Proof.
    intros; induction H; auto.
    apply (perm_trans _ _ _ IHPermutation2); auto.
  Qed.


  (* Now it’s your turn! Complete these lemmas. You may complete
     the proofs in any order, but don’t use later lemmas in earlier
     proofs. *)

  Theorem Permutation_in (xs ys:list A) a:
    Permutation xs ys -> In a xs -> In a ys.
  Admitted.

  Lemma Permutation_app_tail (xs ys zs:list A) :
    Permutation xs ys -> Permutation (xs ++ zs) (ys ++ zs).
  Admitted.

  Lemma Permutation_app_head (xs ys zs:list A) :
    Permutation ys zs -> Permutation (xs ++ ys) (xs ++ zs).
  Admitted.

  Lemma Permutation_app (xs1 ys1 xs2 ys2:list A) :
    Permutation xs1 ys1 ->
    Permutation xs2 ys2 ->
    Permutation (xs1 ++ xs2) (ys1 ++ ys2).
  Admitted.

  Lemma Permutation_ends a (xs:list A):
    Permutation (a :: xs) (xs ++ [a]).
  Admitted.

  Lemma Permutation_app_comm (xs ys:list A) :
    Permutation (xs ++ ys) (ys ++ xs).
  Admitted.
  Local Hint Resolve Permutation_app_comm.

  Lemma Permutation_middle (xs ys:list A) a:
    Permutation (a :: xs ++ ys) (xs ++ a :: ys).
  Admitted.
  Local Hint Resolve Permutation_middle.



  Lemma Permutation_add a (xs ys:list A):
    Permutation xs ys ->
    forall xsm ysm, Add a xsm xs ->
                    Add a ysm ys ->
                    Permutation xsm ysm.
    (* ************************************* *)
    (* YOU DO NOT NEED TO PROVE THIS LEMMA!! *)
    (* ************************************* *)

    (* First, check out and understand the `Add` inductive type... *)
    Print Add.
    (* ...and some example `Add` facts. *)
    Check Add_split.
    Check Add_in.

    (* EXPLANATION

       This lemma statement is equivalent to
         `Permutation (xs1 ++ a :: xs2) (ys1 ++ a :: ys2) ->
          Permutation (xs1 ++ xs2) (ys1 ++ ys2)`.
       Why should that be hard to prove? Seems obvious!

       But while it’s easy to make larger Permutations from smaller ones,
       it’s quite hard to make *smaller* permutations from *larger* ones.

       The reason is that two lists can be `Permutation`s in
       *many different ways,* complicating the task of reversing
       a given Permutation.

       For instance, assume `P : Permutation (a :: xs) (a :: ys)`.
       `P` could have been created by `perm_skip` from
       `Permutation xs ys`, but it might have been created in many other
       ways too! For instance, perhaps it was created by `perm_trans`
       from `Permutation (a :: b :: xs') (c :: a :: ys')` and
       `Permutation (c :: a :: ys') (a :: c :: ys')`. So you can’t
       just apply `inversion` to `P` to reverse it: the inversion
       spins off more and more cases. Induction doesn’t help either,
       and for the same reason.

       A secondary problem is that `a` might be in the lists multiple
       times. So it’s not enough to prove that *some* `a`s can be removed
       from each list, you need to prove that the `a`s *in the
       hypothesized positions* can be removed. (The `Add` inductive
       type eases this problem somewhat.)

       But the lemma *is* true, and for advanced optional work, you may
       try to prove it.

       The library proves this lemma by first stating, and then
       proving, that a more general induction scheme for Permutations
       is equivalent to the natural scheme generated from the
       definition. Thought exercise: What might such a scheme be? *)
  Admitted.
  Local Hint Constructors Add.


  (* Finish off by proving these. *)

  Lemma Permutation_cons_inv (xs ys:list A) a :
    Permutation (a :: xs) (a :: ys) ->
    Permutation xs ys.
  Admitted.
    
  Lemma Permutation_rev (xs:list A):
    Permutation xs (rev xs).
  Admitted.

  Lemma Permutation_length (xs ys:list A):
    Permutation xs ys -> length xs = length ys.
  Admitted.

  Lemma Permutation_length_1_inv a (xs:list A):
    Permutation [a] xs -> xs = [a].
  Admitted.


  (* The library has many more lemmas:
     https://coq.inria.fr/library/Coq.Sorting.Permutation.html
     Try to prove one or two others if you want! *)
End Pset2PermutationLemmas.


Section Pset2AlternatePermutation.
  Hint Constructors Permutation.
  Local Hint Resolve Permutation_app_comm.
  Local Hint Resolve Permutation_middle.


  (* In this section you’ll experiment with alternate definitions
     of permutations. We’ll start out with an expert’s definition
     of permutation from 2014. This definition is INCORRECT. *)

  Definition sublist {A} (xs ys:list A) : Prop :=
    forall x, In x xs -> In x ys.

  Definition pseudopermutation {A} (xs ys:list A) : Prop :=
    sublist xs ys /\ length xs = length ys.

  (* YOUR CODE HERE: Provide a pseudopermutation that is
     not a permutation. *)
  Example bad_pseudopermutation:
    exists (xs ys:list nat),
      pseudopermutation xs ys /\ ~ Permutation xs ys.
  Admitted.


  (* Now write an alternate permutation definition that *is* correct.

     Your definition can be either computational (e.g., a Function
     Fixpoint) or inductive, but it should differ substantially from
     Coq’s. In particular, your definition should NOT assume
     transitivity, the way Coq’s does. (Your equivalent of `perm_trans`
     should be a lemma, not an inductive case.)

     It’s recommended to start with an inductive definition. If
     you choose a computational definition, you’ll need the `eq_dec`
     hypothesis, which says that variables of type A can be
     distinguished. *)

  Context {A:Type}.

  Hypothesis eq_dec : forall x y : A, {x = y} + {x <> y}.
  (* An example theorem with this type: Nat.eq_dec. *)


  (* YOUR CODE HERE *)


  (* Now prove that your permutation definition and `Permutation` mean
     the same thing. Write the lemma statements and finish the proofs.

     NOTE! You will almost certainly need helper lemmas. One very
     helpful helper will be a version of `Permutation_add`. You may
     leave your version of `Permutation_add` as `Admitted` (as long as
     it’s actually true!), but all other lemmas should be proven. *)

  (* YOUR CODE HERE *)

End Pset2AlternatePermutation.
