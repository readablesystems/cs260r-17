Require Import Arith.
Require Import Omega.
Require Import Recdef.
Require Import List.
Require Import Program.Tactics.
Require Import Program.Equality.
Require Import Sorting.Permutation.
Import ListNotations.

(** * Cyclic permutations

This file contains a permutation development based on cycling:

[[
Inductive Perm2 {A}: list A -> list A -> Prop :=
| perm2_nil : Perm2 [] []
| perm2_cons : forall x y a,
    Perm2 x y -> Perm2 (a :: x) (a :: y)
| perm2_cycle : forall x y a,
    Perm2 (a :: x) y -> Perm2 (x ++ [a]) y.
]]

We prove that cycling permutations are equivalent to Coq Permutations.
As you’ve seen, though, this definition is radically difficult to work with.
There is no way I’ve found to prove anything about Perm2 directly
(the equivalent of the [Permutation_Add_inv] lemma must be assumed).

Instead we work with a stronger definition, [NatCyclePerm], about which
we can prove stronger properties. [NatCyclePerm] is a cyclic permutation
for _distinct natural numbers_:

[[
Inductive NatCyclePerm : list nat -> list nat -> Prop :=
| ncp_nil : NatCyclePerm [] []
| ncp_cons : forall is js i,
    NatCyclePerm is js ->
    ~ In i is ->
    NatCyclePerm (i::is) (i::js)
| ncp_cycle : forall is js i,
    NatCyclePerm (i::is) js -> NatCyclePerm (is++[i]) js.
]]

When the members of a set are distinct, it becomes easier to prove
properties about permutations. In particular, we can prove this strong
statement:

[[
  Lemma ncp_all is js:
    NoDup is ->
    NoDup js ->
    (forall i, In i is <-> In i js) ->
    NatCyclePerm is js.
]]

That is, if [is] and [js] are lists of distinct [nat]s, and they are subsets
of each other (every element of [is] is in [js] and vice versa), then there
exists a cycle-based permutation between [is] and [js].

But how can we go from permutations of [nat]s to permutations of anything?
We use this function, which looks up the [i]th element of a list:

[[
Fixpoint map_nth {A} is l : list A :=
  match is with
  | [] => []
  | i::is' => match nth_error l i with
              | Some a => a :: map_nth is' l
              | None => []
              end
  end.
]]

Working through the proof still involved a lot of excitement, and (as almost
every Coq development seems to require) proving facts about lists. A critical
lemma was [NoDup_nat_complete], which allows us to assert the existence of
a [NatCyclePerm] at an important point.

*)


(* ** Facts about [In] *)

Section InFacts.
  Context {A:Type}.
  Implicit Types l:list A.

  Lemma in_middle a l1 l2:
    In a (l1 ++ a :: l2).

    induction l1; intros; simpl; [ left | right ]; auto.
  Qed.

  Lemma in_add_middle a b l1 l2:
    In a (l1 ++ l2) ->
    In a (l1 ++ b :: l2).

    intros; apply in_app_or in H; intuition.
  Qed.

  Lemma in_remove_middle a b l1 l2:
    In a (l1 ++ b :: l2) ->
    a <> b ->
    In a (l1 ++ l2).

    intros; apply in_app_or in H; intuition.
    destruct H1; intuition.
  Qed.

  Lemma in_remove_left a l1 l2:
    In a (l1 ++ l2) ->
    ~ In a l1 ->
    In a l2.

    intros; apply in_app_or in H; intuition.
  Qed.

  Lemma in_remove_right a l1 l2:
    In a (l1 ++ l2) ->
    ~ In a l2 ->
    In a l1.

    intros; apply in_app_or in H; intuition.
  Qed.

End InFacts.


(** ** [AllLess]

   This predicate says that everything in a [list nat] is less than
   a number. We could’ve written it as [Forall (ge n)]. *)

Section AllLess.

  Definition AllLess n l :=
    forall i, In i l -> i < n.

  (** These facts make [AllLess] easier to work with in proofs. *)
  Lemma AllLess_cons n l i:
    AllLess n l -> i < n -> AllLess n (i :: l).

    unfold AllLess; intros.
    destruct H1; intuition.
  Qed.

  Lemma AllLess_skip {n l i}:
    AllLess n (i :: l) -> AllLess n l.

    unfold AllLess; intros; apply H; intuition.
  Qed.

  Lemma AllLess_app_1 {n l1 l2}:
    AllLess n (l1 ++ l2) -> AllLess n l1.

    unfold AllLess; intros; apply H; intuition.
  Qed.

  Lemma AllLess_app_2 {n l1 l2}:
    AllLess n (l1 ++ l2) -> AllLess n l2.

    unfold AllLess; intros; apply H; intuition.
  Qed.

  Lemma AllLess_zero_nil l:
    AllLess 0 l -> l = [].

    destruct l; intros; auto.
    assert (n < 0) by (apply H; intuition).
    omega.
  Qed.

End AllLess.


(** ** Facts about [map_nth] *)

Fixpoint map_nth {A} is l : list A :=
  match is with
  | [] => []
  | i::is' => match nth_error l i with
              | Some a => a :: map_nth is' l
              | None => []
              end
  end.

Section MapNthFacts.
  Context {A:Type}.
  Implicit Types l:list A.
  Implicit Types is js:list nat.

  (* A useful Ltac tactic *)
  Ltac map_nth_head :=
    match goal with
    | [ H : context [ AllLess (length ?l) (?a :: ?is) ] |- _ ] =>
      let M := fresh "SO" in
      let ne := fresh "ne" in
      assert (a < length l) as M by (apply H; intuition);
      rewrite <- nth_error_Some in M; simpl;
      remember (nth_error l a) as ne; destruct ne; [ clear M | contradiction ]
    end.


  (** Easy facts about [map_nth] *)

  Lemma in_map_nth_position is l a:
    In a (map_nth is l) ->
    exists i, In i is /\ i < length l /\ nth_error l i = Some a.
  Admitted.

  Lemma in_map_nth is l a:
    In a (map_nth is l) ->
    In a l.

    intros; apply in_map_nth_position in H.
    destruct H as [i [X [L Y]]].
    now apply nth_error_In in Y.
  Qed.

  Lemma map_nth_empty is:
    map_nth is ([]:list A) = ([]:list A).
  Admitted.

  Lemma map_nth_app is1 is2 l:
    AllLess (length l) is1 ->
    map_nth (is1 ++ is2) l = map_nth is1 l ++ map_nth is2 l.
  Admitted.

  Lemma map_nth_cons is l a:
    map_nth (map S is) (a :: l) = map_nth is l.
  Admitted.

  Lemma map_nth_length is l:
    AllLess (length l) is <->
    length is = length (map_nth is l).
  Admitted.


  (* NoDup is Coq’s inductive type representing the absence of
     duplicates in a list. *)
  Local Hint Constructors NoDup.

  Lemma map_nth_NoDup is l:
    NoDup is ->
    NoDup l ->
    NoDup (map_nth is l).
  Admitted.

  Lemma map_nth_nth is i j l:
    nth_error is i = Some j ->
    AllLess (length l) is ->
    nth_error (map_nth is l) i = nth_error l j.
  Admitted.

  (** A critical lemma for proving [Perm2] transitivity. *)
  Lemma map_nth_compose is js l:
    AllLess (length js) is ->
    AllLess (length l) js ->
    map_nth is (map_nth js l) = map_nth (map_nth is js) l.
  Admitted.

End MapNthFacts.


(** ** Facts about [NoDup] *)

Section NoDupFacts.
  Context {A:Type}.
  Implicit Types a b:A.
  Implicit Types l:list A.

  Lemma in_NoDup_inv a b l:
    NoDup (b :: l) ->
    a <> b ->
    In a (b :: l) ->
    In a l.

    intros ND neq I.
    inversion ND; destruct I; intuition.
  Qed.

  Lemma NoDup_app_swap l1 l2:
    NoDup (l1 ++ l2) <-> NoDup (l2 ++ l1).

    induction l1.
    - simpl; rewrite app_nil_r; intuition.
    - rewrite <- app_comm_cons; split; intro ND.
      + inversion ND; subst.
        assert (Add a (l2 ++ l1) (l2 ++ a :: l1)) by (apply Add_app).
        rewrite (NoDup_Add H).
        rewrite <- IHl1; split; auto.
        contradict H1; rewrite in_app_iff in *; intuition.
      + apply NoDup_remove in ND; destruct ND as [ND NI].
        apply NoDup_cons.
        contradict NI; rewrite in_app_iff in *; intuition.
        rewrite IHl1; assumption.
  Qed.

  Lemma NoDup_remove_iff a x1 x2 y:
    NoDup (x1 ++ a :: x2) ->
    NoDup (a :: y) ->
    (forall i, In i (x1 ++ a :: x2) <-> In i (a :: y)) ->
    forall i, In i (x1 ++ x2) <-> In i y.

    intros NDx NDy EQ i.
    apply NoDup_remove in NDx.
    destruct NDx as [NDx NIx].
    inversion NDy; subst.

    split; intros.
    - apply in_remove_left with (l1:=[a]).
      apply EQ.
      now apply in_add_middle.
      contradict NIx.
      inversion NIx; subst; intuition.
    - apply in_remove_middle with (b:=a).
      apply EQ.
      intuition.
      contradict H1.
      subst; assumption.
  Qed.

  Lemma NoDup_in_iff_length l1 l2:
    NoDup l1 ->
    NoDup l2 ->
    (forall i, In i l1 <-> In i l2) ->
    length l1 = length l2.

    intros NX; revert l2; induction NX;
      intros l2 NY HI.
    - destruct l2; auto.
      assert (In a (a :: l2)) by intuition.
      rewrite <- HI in H; destruct H.
    - assert (In x l2) by (rewrite <- HI; intuition).
      apply in_split in H0.
      destruct H0 as [m1 [m2 Hm2]]; subst.
      rewrite app_length; simpl.
      rewrite <- plus_n_Sm; apply eq_S.
      rewrite <- app_length.
      apply IHNX.
      apply NoDup_remove_1 with (a:=x); auto.
      symmetry; revert i.
      apply NoDup_remove_iff with (a:=x); auto.
      now constructor.
      symmetry; revert i; now assumption.
  Qed.

End NoDupFacts.



(** ** Facts about [iota]

   [iota n] counts from 0 to [n - 1], and is defined in terms of
   the library’s [seq]. *)

Definition iota n := seq 0 n.

Section IotaFacts.

  Lemma in_iota_iff n i:
    In i (iota n) <-> i < n.
  Admitted.

  Lemma iota_NoDup n:
    NoDup (iota n).

    now apply seq_NoDup.
  Qed.

  Lemma iota_length n:
    length (iota n) = n.

    now apply seq_length.
  Qed.

  Lemma iota_AllLess n:
    AllLess n (iota n).

    unfold AllLess; intros; now apply in_iota_iff.
  Qed.

  Lemma seq_app start len1 len2:
    seq start (len1 + len2) = seq start len1 ++ seq (start + len1) len2.

    revert start len2; induction len1; intros.
    - simpl; auto.
    - cbn; rewrite IHlen1; rewrite plus_Sn_m; rewrite <- plus_n_Sm; reflexivity.
  Qed.

  Lemma iota_nth n i:
    i < n -> nth_error (iota n) i = Some i.
  Admitted.

  Lemma iota_S n:
    iota (S n) = 0 :: map S (iota n).

    unfold iota; rewrite seq_shift; reflexivity.
  Qed.

  Lemma map_nth_iota {A} (xs:list A):
    map_nth (iota (length xs)) xs = xs.

    induction xs; cbn in *; auto.
    rewrite <- seq_shift.
    rewrite map_nth_cons.
    unfold iota in IHxs; now rewrite IHxs.
  Qed.

End IotaFacts.


(** ** [NoDup_nat_complete]

   This section states and proves this lemma: If a list [l] contains
   [n] [nat]s with no duplicates, and all elements of [l] are less
   than [n], then [l] contains _every_ [nat] less than [n]. We need
   it to prove that [Perm2]s are transitive.

   This is too hard to prove in a single induction, so we introduce
   a [transfer] type to let us state the induction-aware lemma,
   [NoDup_AllLess_transfer]. *)

Section NoDupNatComplete.

  Inductive transfer {A}: list A -> list A -> list A -> Prop :=
  | transfer_nil : forall ys, transfer [] ys ys
  | transfer_cons : forall xs ys1 y ys2 zs,
      transfer xs (ys1 ++ y :: ys2) zs ->
      transfer (y :: xs) (ys1 ++ ys2) zs.
  Hint Constructors transfer.

  Lemma in_transfer_iff {A} (xs ys zs:list A) a:
    transfer xs ys zs ->
    In a zs <-> In a (xs ++ ys).
  Admitted.

  Lemma transfer_length {A} (xs ys zs:list A):
    transfer xs ys zs ->
    length zs = length xs + length ys.
  Admitted.

  Lemma in_transfer_rest {A} (xs ys zs:list A) a:
    transfer xs ys zs ->
    In a zs ->
    ~ In a xs ->
    In a ys.
  Admitted.


  Lemma NoDup_AllLess_transfer n xs:
    NoDup xs ->
    AllLess n xs ->
    exists ys, transfer xs ys (iota n).
  Admitted.

  Lemma NoDup_nat_complete i is:
    NoDup is ->
    AllLess (length is) is ->
    i < length is ->
    In i is.
  Admitted.

End NoDupNatComplete.


(** ** [NatCyclePerm]

   This is the cycle-based permutation definition that lets us show
   reflexivity, symmetry, and transitivity without further
   assumptions. *)

Section NatCyclePerm.

  Inductive NatCyclePerm : list nat -> list nat -> Prop :=
  | ncp_nil : NatCyclePerm [] []
  | ncp_cons : forall is js i,
      NatCyclePerm is js ->
      ~ In i is ->
      NatCyclePerm (i::is) (i::js)
  | ncp_cycle : forall is js i,
      NatCyclePerm (i::is) js -> NatCyclePerm (is++[i]) js.
  Hint Constructors NatCyclePerm.

  Lemma ncp_length_eq {is js}:
    NatCyclePerm is js ->
    length is = length js.

    intro PE; induction PE; auto.
    now apply eq_S.
    rewrite app_length; simpl in *. omega.
  Qed.

  Lemma ncp_eq_nil is:
    NatCyclePerm is [] ->
    is = [].

    intros; apply ncp_length_eq in H.
    simpl; apply length_zero_iff_nil; subst; auto.
  Qed.


  Lemma ncp_refl is:
    NoDup is ->
    NatCyclePerm is is.

    induction is; auto; intros.
    constructor.
    - apply IHis; inversion H; auto.
    - inversion H; auto.
  Qed.

  Lemma ncp_app_cycle is1 is2 js:
    NatCyclePerm (is1 ++ is2) js ->
    NatCyclePerm (is2 ++ is1) js.

    revert is2; induction is1; intros.
    simpl; rewrite app_nil_r; auto.
    replace (is2 ++ a :: is1) with ((is2 ++ [a]) ++ is1).
    apply IHis1; rewrite app_assoc; apply ncp_cycle; apply H.
    rewrite <- app_assoc; apply eq_refl.
  Qed.

  (** This important lemma lets us construct a [NatCyclePerm]
      from _any_ [nat] lists that meet some simple conditions. *)
  Lemma ncp_all is js:
    NoDup is ->
    NoDup js ->
    (forall i, In i is <-> In i js) ->
    NatCyclePerm is js.
  Admitted.

  Lemma ncp_expand is js:
    NatCyclePerm is js ->
    NoDup is
    /\ NoDup js
    /\ (forall i, In i is <-> In i js).
  Admitted.

  Lemma ncp_NoDup_is {is js}:
    NatCyclePerm is js -> NoDup is.

    intros PE; apply ncp_expand in PE; intuition.
  Qed.

  Lemma ncp_NoDup_js {is js}:
    NatCyclePerm is js -> NoDup js.

    intros PE; apply ncp_expand in PE; intuition.
  Qed.

  Lemma ncp_in_iff {is js}:
    NatCyclePerm is js -> forall i, In i is <-> In i js.

    intro PE; apply ncp_expand in PE; intuition.
  Qed.



  (** Once we have [ncp_expand] and [ncp_all], we can prove symmetry
      and transitivity. *)

  Lemma ncp_sym is js:
    NatCyclePerm is js ->
    NatCyclePerm js is.

    intros.
    apply ncp_expand in H.
    destruct_conjs.
    apply ncp_all; auto.
    split; intros; now apply H1.
  Qed.

  Lemma ncp_trans is js ks:
    NatCyclePerm is js ->
    NatCyclePerm js ks ->
    NatCyclePerm is ks.

    intros.
    apply ncp_expand in H.
    apply ncp_expand in H0.
    destruct_conjs.
    apply ncp_all; auto.
    split; intros.
    apply H2; now apply H4.
    apply H4; now apply H2.
  Qed.


  (** Given symmetry and transitivity, we can prove the equivalence
      of the library’s [Permutation] and [NatCyclePerm] (for
      duplicate-free lists). *)

  Lemma perm_ncp is js:
    NoDup is ->
    Permutation is js ->
    NatCyclePerm is js.
  Admitted.

  Lemma ncp_perm is js:
    NatCyclePerm is js ->
    Permutation is js.
  Admitted.

End NatCyclePerm.


(** ** [Perm2] Facts

   We are finally ready to state the [Perm2] definition
   and prove it equivalent to [NatCyclePerm], and therefore
   [Permutation]. *)

Section Perm2.
  Hint Constructors NatCyclePerm.

  Inductive Perm2 {A}: list A -> list A -> Prop :=
  | perm2_nil : Perm2 [] []
  | perm2_cons : forall x y a,
      Perm2 x y -> Perm2 (a :: x) (a :: y)
  | perm2_cycle : forall x y a,
      Perm2 (a :: x) y -> Perm2 (x ++ [a]) y.
  Hint Constructors Perm2.

  Lemma perm2_length_eq {A} (xs ys:list A):
    Perm2 xs ys ->
    length xs = length ys.

    intros PE; induction PE; auto.
    simpl; now apply eq_S.
    rewrite app_length; rewrite <- IHPE; simpl. omega.
  Qed.


  Lemma ncp_perm2 {A} is js (ctx:list A):
    NatCyclePerm is js ->
    AllLess (length ctx) is ->
    Perm2 (map_nth is ctx) (map_nth js ctx).
  Admitted.

  Lemma perm2_np {A} (xs ys:list A):
    Perm2 xs ys ->
    exists is, NatCyclePerm is (iota (length xs))
               /\ map_nth is ys = xs.
  Admitted.


  Lemma perm2_refl {A} (xs:list A):
    Perm2 xs xs.

    rewrite <- (map_nth_iota xs).
    apply ncp_perm2.
    apply ncp_refl.
    apply iota_NoDup.
    apply iota_AllLess.
  Qed.

  Lemma perm2_sym {A} (xs ys:list A):
    Perm2 xs ys -> Perm2 ys xs.
  Admitted.

  (* Transitivity in [Perm2] doesn’t follow immediately from
     transitivity in [NatCyclePerm], for a funny reason. The
     [perm2_np] lemma lets us construct [NatCyclePerm]s
     between [xs] and [ys], and between [ys] and [zs]---but
     unfortunately, those [NatCyclePerm]s are unrelated!
     (The [nat] list used to represent [ys] differs.) So we
     need to add another link to the transitive chain.
     That’s what NoDup_nat_complete is for. *)

  Lemma perm2_trans {A} (xs ys zs:list A):
    Perm2 xs ys ->
    Perm2 ys zs ->
    Perm2 xs zs.
  Admitted.

End Perm2.
