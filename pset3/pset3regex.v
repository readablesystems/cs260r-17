Require Import Arith.
Require Import Omega.
Require Import Recdef.
Require Import String.
Require Import List.
Require Import Program.Tactics.
Require Import Relation_Operators.
Require Import Ascii.
Require Import Program.
Require Import Bool.
Require Import Sorting.Permutation.

Section CharacterFacts.
  (* Perhaps useful in your regular-expression development. *)

  (* `ascii_eq` is an executable equality test for characters. *)
  Definition ascii_eq (a b:ascii) : bool :=
    match (a, b) with
    | (Ascii a1 a2 a3 a4 a5 a6 a7 a8,
       Ascii b1 b2 b3 b4 b5 b6 b7 b8) =>
      eqb a1 b1 && eqb a2 b2 && eqb a3 b3 && eqb a4 b4 &&
          eqb a5 b5 && eqb a6 b6 && eqb a7 b7 && eqb a8 b8
    end.

  Lemma ascii_eq_refl (a:ascii):
    ascii_eq a a = true.
  Proof.
    destruct a; unfold ascii_eq; repeat rewrite eqb_reflx; simpl; auto.
  Qed.

  (* `ascii_eq` is equivalent to character equality. *)
  Lemma ascii_eq_iff a b:
    ascii_eq a b = true <-> a = b.
  Proof.
    split; intros.
    - unfold ascii_eq in H; destruct a; destruct b;
        repeat rewrite andb_true_iff in *; destruct_pairs;
          rewrite eqb_true_iff in *; congruence.
    - rewrite H; apply ascii_eq_refl.
  Qed.
End CharacterFacts.


Section StringFacts.
  (* Perhaps useful in your regular-expression development. *)

  (* Coq `string`s are constructed from characters using a
     `list`-like cons procedure. The two `string` constructors
     are `EmptyString` (also written ` ""%string `; like `nil`)
     and `String ch s` (which is like `ch :: s`). *)


  (* `append` is the string version of `app` (list append).
     The Coq library has fewer `append` lemmas; we provide them. *)

  Lemma append_nil_l s:
    ("" ++ s)%string = s.
  Proof.
    simpl; auto.
  Qed.

  Lemma append_nil_r s:
    (s ++ "")%string = s.
  Proof.
    induction s; simpl; try rewrite IHs; auto.
  Qed.

  Lemma append_assoc s1 s2 s3:
    (s1 ++ s2 ++ s3)%string = ((s1 ++ s2) ++ s3)%string.
  Proof.
    induction s1; simpl; try rewrite IHs1; auto.
  Qed.

  Lemma append_comm_cons a s1 s2:
    (String a s1 ++ s2)%string = String a (s1 ++ s2)%string.
  Proof.
    induction s1; simpl; auto.
  Qed.


  Definition strlen := String.length.

  Lemma append_strlen_l s1 s2:
    strlen s1 <= strlen (s1 ++ s2).
  Proof.
    induction s1; simpl; try rewrite IHs1; omega.
  Qed.

  Lemma append_strlen_r s1 s2:
    strlen s2 <= strlen (s1 ++ s2).
  Proof.
    induction s1; simpl; try rewrite IHs1; omega.
  Qed.
End StringFacts.


(* Define a type that represents regular expressions.

   Support the following grammar (but you don’t need to
   use this concrete syntax):

   regex ::= 'ε'    // matches the empty string
          |  'ANY'  // matches any character
          |  CHAR   // matches a specific character
          |  regex '++' regex   // concatenation
          |  regex '|' regex    // or
          |  regex '*'          // Kleene star

   This type *represents* regular expressions in memory,
   so it is a `Set` (not a `Prop`). *)

(* YOUR CODE HERE *)



(* Now define an inductive proposition with two parameters,
   a regex and a string, that holds iff the regex matches
   the string.

   (This type *defines* the semantics of regular expressions,
   so you can’t prove it correct---it just needs to match
   the expected semantics.) *)

(* YOUR CODE HERE *)



(* Write a couple `Example`s that show that specific regular
   expressions match specific strings, and prove them. *)

(* YOUR CODE HERE *)



(* State and prove a theorem that relates Kleene-star and
   concatenation. Your theorem should say that if `r*` matches
   a string `s`, then there exists a regex `r ++ r ++ ... ++ r`
   that matches `s`, and vice versa. (Probably easiest to
   introduce a helper function that produces `r ++ ... ++ r`
   for a given count, and then to prove two lemmas, one per
   direction. *)

(* YOUR CODE HERE *)



(* Now, write a regular expression IMPLEMENTATION and prove
   it at least partially correct.

   Q. What does “implementation” mean?
   A. Here are some possibilities.
      - COMPUTATIONAL MATCHER: You could write a `Function`
        or `Fixpoint` that takes a regex as an argument and
        returns `true` if the regex matches.
      - NFA MATCHER: You could design an inductive type for
        nondeterministic finite automata. This would include
        a `Function` or `Fixpoint` that builds the NFA for
        a regex using Thompson’s construction, and an
        inductive proposition that implements NFA matching.
      - DERIVATIVES MATCHER:
        http://www.ccs.neu.edu/home/turon/re-deriv.pdf
      - OTHER: Check with me!

   Q. Any general gotchas?
   A. DON’T PREMATURELY OPTIMIZE.

   Q. Any gotchas with a computational matcher?
   A. Kleene-star will cause problems since your recursion
      might never terminate. It’s OK to add an extra “fuel”
      argument to force termination. Each recursive call
      will consume a unit of fuel, and the match may terminate
      prematurely (i.e., return `false`) if it runs out of
      fuel. But given enough fuel, your matcher should succeed
      on Kleene-star arguments (it’s not OK to return `false`
      for every Kleene-star regex).

   Q. Any gotchas with an NFA matcher?
   A. I found it far easier to work with a “nested” NFA
      design, in which an NFA node may contain another NFA as
      a subgraph, than a “flat” NFA design, in which the
      regex-to-NFA function flattens the regex as it goes.

   Q. What does “partially correct” mean?
   A. Full correctness requires that (1) every string that
      matches the spec also matches the implementation (perhaps
      with a “given enough fuel” clause), and (2) every string
      that matches the implementation also matches the spec.
      Please prove AT LEAST ONE of these directions.

   Q. Any general hints?
   A. I found the NFA matcher easier to work with because of
      the absence of fuel.
   A. You will likely need some additional type definitions.
   A. `inversion` is your friend.
   A. You will almost certainly want `Hint Constructors` for
      your types. `auto` goes a lot further when `Hint
      Constructors` is active. Consider writing your own
      tactics too; I benefited enormously from a tactic that
      can tell when an edge (such as one created by
      `inversion` or `destruct`) is not actually in an NFA.

   Q. This is fun. How can I go further?
   A. You’re crazy. But, for example, given an NFA matcher,
      you could implement an NFA-to-DFA converter and prove it
      preserved the NFA’s semantics. I wrote an NFA flattener,
      which de-nests a recursive NFA into a flat graph, and
      proved that flattening preserves the NFA’s semantics.
      That was hard, but fun.

   Q. How can I not get stuck?
   A. Share your inductive definitions with me before you get
      too far down the proof route. *)

(* YOUR CODE HERE *)
