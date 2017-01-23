Module Lecture1.
  Require Import Arith.
  Require Import List.

  Definition AnIntegerExists : nat := 2.

  Lemma AnIntegerExistsB : nat.
  Proof.
    apply 0.
  Qed.

  Print nat.


  Locate "_ /\ _".
  Check and.
  Print and.

  Definition Proj1 {A B:Prop} : A /\ B -> A :=
    fun (H:A /\ B) =>
      match H with
      | conj x y => x
      end.

  Lemma Proj1B {A B:Prop} : A /\ B -> A.
  Proof.
    intros.
    destruct H.
    apply H.
  Qed.


  Locate "_ <-> _".
  Check iff.
  Print iff.
  Print and.

  Lemma ObjectivismB {A:Prop} : A <-> A.
  Proof.
    split.
    intros.
    apply H.
    intros.
    apply H.
  Qed.

  Lemma ObjectivismB_Semicolons {A:Prop} : A <-> A.
  Proof.
    split; intros; apply H.
  Qed.

  Lemma ObjectivismB_Auto {A:Prop} : A <-> A.
  Proof.
    split; auto.
  Qed.

  Definition Objectivism {A:Prop} : A <-> A :=
    conj (fun x => x) (fun x => x).


  Lemma DistributeAnd {A B C:Prop} :
    A /\ (B \/ C) -> (A /\ B) \/ (A /\ C).
  Proof.
    intros.
    destruct H.
    destruct H0.
    left.
    split.
    apply H.
    apply H0.
    right.
    split.
    apply H.
    apply H0.
  Qed.

  Lemma DistributeAnd_Semicolons {A B C:Prop} :
    A /\ (B \/ C) -> (A /\ B) \/ (A /\ C).
  Proof.
    intros.
    destruct H.
    destruct H0;
      (* [X1 | X2 | ... | Xn] applies X1 to the 1st
         subgoal, X2 to the second, and so forth. *)
      [left | right];
      split; try apply H; try apply H0.
  Qed.

End Lecture1.
