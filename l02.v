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

End Lecture2.
