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
  Print list.


  Check In.
  Print In.

  Check app.
  Print app.

  (* Let's prove our own list fact. *)
  Lemma in_middle: forall (a:A) xs1 xs2,
    In a (xs1 ++ a :: xs2).
    intros.
    induction xs1.
    simpl; auto.
    rewrite <- app_comm_cons.
    apply in_cons.
    auto.
  Qed.


  (* Now, write an inductive Prop `Dec`, with a single
     `list A` argument, where `Dec l` is true iff the
     elements of `l` are in decreasing order by `LE`. *)
  Inductive Dec : list A -> Prop :=
  | DNil : Dec []
  | DSingleton : forall a, Dec [a]
  | DCons : forall a b l,
      LE a b ->
      Dec (b :: l) ->
      Dec (a :: b :: l).
  Hint Constructors Dec.

  Example DecExample : Dec [1;2;3;3;4].
    auto 7.
  Qed.


  (* Do it again. *)
  Inductive Dec2 : list A -> Prop :=
  | D2Nil : Dec2 []
  | D2Cons : forall a l,
      (forall b, In b l -> LE a b) ->
      Dec2 l ->
      Dec2 (a :: l).
  Hint Constructors Dec2.

  Example Dec2Example : Dec2 [1;2;3;3;4].
  Proof.
    apply D2Cons; intros.
    simpl in H; repeat destruct or H; unfold LE in *; omega.
    apply D2Cons; intros.
    simpl in H; repeat destruct or H; unfold LE in *; omega.
    apply D2Cons; intros.
    simpl in H; repeat destruct or H; unfold LE in *; omega.
    apply D2Cons; intros.
    simpl in H; repeat destruct or H; unfold LE in *; omega.
    apply D2Cons; intros.
    simpl in H; repeat destruct or H; unfold LE in *; omega.
    auto.
  Qed.


  (* Prove the definitions equivalent. *)

  Lemma Dec_Dec2 l:
    Dec l -> Dec2 l.
  Proof.
    (* Here's a first, long, interactive proof. *)
    intros.
    induction H.
    auto.
    apply D2Cons; intros. destruct H.
    auto.
    apply D2Cons.
    intros.
    inversion IHDec.
    destruct H1.
    rewrite <- H1; auto.
    apply H4 in H1.
    apply le_trans with (m:=b); auto.
    auto.

    (* Clean it up with an outline. *)
    Restart.
    intros; induction H.
    - auto.
    - apply D2Cons; intros. destruct H. auto.
    - apply D2Cons; intros.
      + inversion IHDec. (* invert Dec2 inductive hypothesis *)
        destruct H1. (* In b0 (b::l) becomes two cases:
                        b0 = b \/ In b0 l *)
        * rewrite <- H1; auto.
        * apply H4 in H1.
          apply le_trans with (m:=b); auto.
      + auto.

    (* We need `le_trans` because `omega` can’t see through
       `LE`. So unfold it explicitly. *)
    Restart.
    intros; induction H.
    - auto.
    - apply D2Cons; intros. destruct H. auto.
    - apply D2Cons; intros.
      + inversion IHDec.
        unfold LE in *.
        destruct H1. (* In b0 (b::l) becomes two cases:
                        b0 = b \/ In b0 l *)
        * omega.
        * apply H4 in H1; omega.
      + auto.

    (* Reducing the structure cleans up further. *)
    Restart.
    intros; induction H; auto;
      apply D2Cons; intros; auto; [ destruct H | ].
    inversion IHDec; unfold LE in *;
      destruct H1; try apply H4 in H1; omega.
  Qed.


  (* Proving that Dec2 implies Dec is much easier.
     This is because Dec2s are easier to take apart
     -- fewer cases -- and Decs are easier to build
     -- only local requirements. It’s nice to know
     they are equivalent; now we can switch between
     them whenever we want! *)

  Lemma Dec2_Dec l:
    Dec2 l -> Dec l.
  Proof.
    intros; induction H; auto.
    destruct l; auto.
    apply DCons; auto.
    apply H; simpl; auto.
  Qed.


  (* Now, prove a lemma about appending decreasing lists. *)

  (* Left for later *)

End Lecture5.
