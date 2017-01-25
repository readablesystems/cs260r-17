Module Lecture2.
  Require Import List.
  Require Import Arith.
  Require Import Omega. (* the `omega` tactic knows arithmetic *)
  Import ListNotations. (* `[]`, `[a; b; c]` notation *)


  Print list.

  Definition x : list nat := 1 :: 2 :: 3 :: nil.
  Print x.


  (* Let's define our own functions on lists and prove
     some things about them.

     These functions are recursive on the `list` type,
     so they are defined with `Function` (not `Definition`). *)

  (* xlength should return the length of a list. *)
  Function xlength {A} (x:list A) :=
    match x with
    | nil => 0
    | _ :: x' => S (xlength x')
    end.

  (* xappend should append two lists together. *)
  Function xappend {A} (x y:list A) :=
    match x with
    | nil => y
    | a :: x' => a :: (xappend x' y)
    end.

  Eval compute in xlength [].
  Eval compute in xlength [1;2;3;4].
  Eval compute in xlength [[];[];[1]].
  Eval compute in xappend [1;2;3] [4;5;6;7].

  (* xreverse should reverse a list in O(N^2) time. *)
  Function xreverse {A} (x:list A) :=
    match x with
    | nil => nil
    | a :: x' => xappend (xreverse x') [a]
    end.

  Check list_rec.

  Eval compute in xreverse [3;2;1].

  (* xireverse should reverse a list in O(N) time. *)
  Function xireverse {A} (x y:list A) :=
    match x with
    | nil => y
    | a :: x' => xireverse x' (a :: y)
    end.

  Eval compute in xireverse [1;3;495;10] [].


  (* Use `Eval compute` to test out your functions. *)


  (* Now, prove some things! *)

  Lemma xappend_length {A} :
    forall l1 l2:list A, xlength l1 + xlength l2
                          = xlength (xappend l1 l2).
  Proof.
    intros.
    induction l1.
    auto.
    simpl.
    rewrite IHl1.
    reflexivity.
  Qed.

  (* At this point in class, we tried to prove
     something for which we lacked the tools. *)
  Lemma xreverse_reverse {A} (x:list A) :
    xreverse (xreverse x) = x.
  Proof.
    induction x; auto.
    simpl.
  Abort.


  (* WHAT YOU SHOULD DO: Try to prove xreverse_reverse! *)

  (* I proved xreverse_reverse using 3 additional lemmas and the
     following tactics only: `induction`, `simpl`, `auto`, `rewrite`.
     `try` is useful for shortening proofs but not required.

     You'll learn most by trying to prove xreverse_reverse yourself.
     That will give you experience in detecting when you're stuck and
     finding and proving helper lemmas. Think about basic properties
     of mathematical objects, and things that are true about list
     operations. For instance, associativity: is `xappend`
     associative? Would that ever be useful?

     If you get really stuck, the lemma statements I used are below,
     after some space. Fun fact: two of my lemmas have the *exact same
     proof statement*. *)










































































































  Lemma xappend_empty {A} (x:list A):
    xappend x [] = x.
  Abort.

  Lemma xappend_assoc {A} (x y z:list A):
    xappend (xappend x y) z =
      xappend x (xappend y z).
  Abort.

  Lemma xreverse_append {A} (x y:list A):
    xreverse (xappend x y) =
      xappend (xreverse y) (xreverse x).
  Abort.

  Lemma xreverse_reverse {A} (x:list A):
    xreverse (xreverse x) = x.
  Abort.

End Lecture2.
