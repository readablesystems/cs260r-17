Module Lecture1.
  Require Import Arith.
  Require Import List.

  Definition AnIntegerExists : nat.
  (* First prove by construction. Start with
     Definition AnIntegerExists : nat := _.
     and fill in the underscore. *)

  Lemma AnIntegerExistsB : nat.
  (* Then prove using tactics. Start with
     "Proof." and check out Coq's reports.
     Tactics: `apply`, `intros`, `split`, `destruct`. *)


  Definition Proj1 {A B:Prop} : A /\ B -> A.

  Lemma Proj1B {A B:Prop} : A /\ B -> A.


  (* Use `Locate`, `Check`, and `Print` to figure out
     how <-> works. Start with `Locate "_ <-> _".` *)
  Lemma ObjectivismB {A:Prop} : A <-> A.

  Definition Objectivism {A:Prop} : A <-> A.


  Lemma DistributeAnd {A B C:Prop} : 
    A /\ (B \/ C) -> (A /\ B) \/ (A /\ C).

End Lecture1.
