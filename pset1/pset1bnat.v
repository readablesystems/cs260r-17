Require Import Arith.
Require Import Omega.
Require Import Recdef.

Module Pset1Bnat.

  (* In this module, you'll prove some facts about *binary*
     numbers, rather than Coq's default unary numbers.
     We'll start out with some useful lemmas. *)
  Lemma double_eq (n m:nat) : n + n = m + m <-> n = m.
  Proof. omega. Qed.

  Lemma double_lt (n m:nat) : n + n < m + m <-> n < m.
  Proof. omega. Qed.

  Lemma double_lt_n_Sm (n m:nat) : n + n < S (m + m) <-> n < S m.
  Proof. omega. Qed.

  (* The `clean_arithmetic` tactic cleans up a lot of arithmetic
     identities typically occurring in these problems.
     It replaces `x + 0` with `x`, `S x = S y` with `x = y`, and
     `x + x = y + y` with `x = y`. *)
  Ltac clean_arithmetic :=
    repeat match goal with
      | [H : context[_ + 0] |- _] => rewrite Nat.add_0_r in H
      | [ |- context[_ + 0] ] => rewrite Nat.add_0_r
      | [H : context[?a + ?a = ?b + ?b] |- _] => rewrite double_eq in H
      | [ |- context[?a + ?a = ?b + ?b] ] => rewrite double_eq
      | [H : context[S _ = S _] |- _] => apply eq_add_S in H
      | [ |- context[S _ = S _] ] => apply eq_S
    end.


  (* Coq's Peano arithmetic defines natural numbers inductively,
     based on two constructors: 0 and successor. So 10 is defined
     as a structure of length 11:
     (S (S (S (S (S (S (S (S (S (S Z)))))))))))
     And in general N is defined in a structure of length O(N).

     We're going to work with natural numbers based on *three*
     constructors. That will lead to numbers defined in structures
     of length O(log_2 N). *)

  Inductive bnat : Type :=
    | BZ : bnat              (* Zero *)
    | BD1 : bnat -> bnat     (* BD1 X is the number 2*X + 1 *)
    | BD2 : bnat -> bnat.    (* BD2 X is the number 2*X + 2 *)


  (* EXERCISE: Write a function that computes the conventional
     (Peano) value of bnat `b`. *)
  Function bval (b:bnat) : nat :=
    0.


  (* EXERCISE: Prove that if `bval b = 0`, then `b = BZ`. *)
  Lemma bval_zero (b:bnat) :
    bval b = 0 -> b = BZ.
  Proof.
  Abort.


  (* EXERCISE: Prove that every natural number has a unique
     binary representation. *)
  Lemma bval_uniq (b c:bnat) :
    bval b = bval c -> b = c.
  Proof.
    (* Your first tactic should be `generalize c`.
       Don't forget `discriminate`, `clean_arithmetic`, and `omega`. *)
    generalize c.
  Abort.


  (* EXERCISE: Write a function that returns the successor of `b`.
     You'll want to work this out on paper first, and there will
     be at least one recursive call to `bsucc`. *)
  Function bsucc (b:bnat) : bnat :=
    0.


  (* EXERCISE: Prove that your `bsucc` is correct. *)
  Lemma bsucc_correct (b:bnat) :
    bval (bsucc b) = S (bval b).
  Proof.
    (* If regular induction doesn't work, try
       `functional induction (bval b)`, which runs induction over the
       cases of the `bval` function. *)
  Abort.


  (* This function returns the length of a binary number. *)
  Function blen (b:bnat) : nat :=
    match b with
    | BZ => 0
    | BD1 b' => S (blen b')
    | BD2 b' => S (blen b')
    end.


  (* The sum of the lengths of two binary numbers in a pair. *)
  Definition bpairlen (x:bnat*bnat) : nat :=
    blen (fst x) + blen (snd x).


  (* EXERCISE: Write a function that adds two binary numbers.
     You'll want to work this out on paper first too. Everything
     works out easier if the numbers are passed in a pair; you
     can decompose the pair with `fst` and `snd` (Check them),
     or with matching.

     After writing the function, you'll need to prove that its
     recursion terminates. Do that too. *)
  Function baddpair (x:bnat*bnat) {measure bpairlen x} : bnat :=
    0.
  (* Proof. ... Qed. *)

  (* A more conventional adder function: *)
  Definition badd (x y:bnat) := baddpair (x,y).


  (* EXERCISE: Prove that your add function is correct. *)
  Lemma baddpair_correct (x:bnat*bnat) :
    bval (baddpair x) = bval (fst x) + bval (snd x).
  Proof.
  Abort.


  (* EXERCISE: Write a function that determines whether
     `fst x < snd x`. Return either False or True. *)
  Function blesspair (x:bnat*bnat) {measure bpairlen x} : Prop :=
    True.
  (* Proof. ... Qed. *)

  Definition bless (x y:bnat) : Prop := blesspair (x,y).


  (* EXERCISE: Prove that `blesspair` is correct.
     For me this was the hardest proof in this module. *)
  Lemma blesspair_correct (x:bnat*bnat) :
    bval (fst x) < bval (snd x) <-> blesspair x.
  Proof.
  Abort.

End Pset1Bnat.
