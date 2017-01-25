Module Lecture2.
  Require Import List.
  Require Import Arith.
  Require Import Omega. (* the `omega` tactic knows arithmetic *)
  Import ListNotations. (* `[]`, `[a; b; c]` notation *)



  (* Let's define our own functions on lists and prove
     some things about them.

     These functions are recursive on the `list` type,
     so they are defined with `Function` (not `Definition`). *)

  (* xlength should return the length of a list. *)

  (* xappend should append two lists together. *)

  (* xreverse should reverse a list in O(N^2) time. *)

  (* xireverse should reverse a list in O(N) time. *)


  (* Use `Eval compute` to test out your functions. *)


  (* Now, prove some things! *)



  (* Let's prove a relationship between different
     definitios of natural-number ordering, our own
     and the one in Coq's libraries. *)
  Inductive order : Type :=
  | Less
  | Equal
  | Greater.

  Function nat_cmp (n m:nat) : order := Less.


  (* Now let's try to prove a theorem about how nat_cmp
     relates to normal ordering. We will get stuck because
     our theorem as stated isn't strong enough! The point
     is to see how that feels. *)
  Lemma nat_cmp_gt_bad (n m:nat) :
    nat_cmp n m = Greater -> n > m.
  Admitted.


  (* A stronger hypothesis is needed. *)
  Lemma nat_cmp_gt_forall :
    forall n m:nat, nat_cmp n m = Greater -> n > m.
  Admitted.


  (* Or we can supply the stronger hypothesis! *)


  (* Finally, define an inductive type truth with 3 constructors,
     Yes, No, and Maybe. Yes stands for certain truth, No for
     certain falsehood, and Maybe for an unknown situation.

     Define “not,” “and,” and “or” for this replacement boolean
     algebra. Prove that your implementation of “and” is
     commutative and distributes over your implementation of
     “or.” [Adam Chlipala] *)

End Lecture2.
