Require Import Arith.
Require Import Omega.
Require Import Recdef.
Require Import List.
Require Import Program.Tactics.
Require Import Program.Equality.
Require Import Sorting.Permutation.
Require Import Sorting.Sorted.
Import ListNotations.

(* Write a function that sorts a list of `nat`s into increasing
   order. Your function must take O(N log N) time in the average
   case. This means no insertion-sort or bubble-sort. (Remember
   that `++` takes O(N) time, so if you go crazy with it, your
   function will be slower than it looks.)

   Then test your function, using `Eval compute` or `Extraction`.

   Then prove it correct. Write a specification for sorting
   and show that your function obeys that specification.
   You may use parts of the standard library in your spec; I
   definitely recommend using `Permutation`. Your function code
   and proof code should be your own, however. *)

(* YOUR CODE HERE *)
