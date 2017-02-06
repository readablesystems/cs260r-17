Require Import Arith.
Require Import Omega.
Require Import Recdef.
Require Import List.
Require Import Program.Tactics.
Import ListNotations.

Section Lecture5.

  (* Define some local variables to this section. *)
  Definition A := nat.
  Definition LE := le.
  Hint Unfold LE.

  (* Some facts about lists. *)
  Check In.
  Print In.

  Check app.
  Print app.

  (* Let's prove our own list fact. *)
  Lemma in_middle: forall (a:A) xs1 xs2, In a (xs1 ++ a :: xs2).
  Admitted.


  (* Now, write an inductive Prop `Dec`, with a single `list A` argument,
     where `Dec l` is true iff the elements of `l` are in decreasing order
     by `LE`. *)


  (* Do it again. *)


  (* Prove the definitions equivalent. *)


  (* Now, prove a lemma about appending decreasing lists. *)

End Section.
