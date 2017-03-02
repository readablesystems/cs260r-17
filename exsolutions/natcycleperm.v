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
    NatCyclePerm is js -> ~ In i is ->
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

That is, if [is] and [js] are distinct lists of [nat]s, and they are subsets
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

    revert is l a; induction is; simpl; intros.
    contradiction.
    remember (nth_error l a) as ne; destruct ne; [ | destruct H ].
    simpl in H; destruct or H; subst.
    - assert (nth_error l a <> None) by (rewrite <- Heqne; discriminate).
      rewrite nth_error_None in H.
      exists a; intuition.
    - apply IHis in H; destruct H as [x H].
      exists x; intuition.
  Qed.

  Lemma in_map_nth is l a:
    In a (map_nth is l) ->
    In a l.

    intros; apply in_map_nth_position in H.
    destruct H as [i [X [L Y]]].
    now apply nth_error_In in Y.
  Qed.

  Lemma map_nth_empty is:
    map_nth is ([]:list A) = ([]:list A).

    induction is; auto; simpl.
    rewrite IHis.
    assert (length ([]:list A) <= a) by (simpl; omega).
    rewrite <- nth_error_None in H.
    now rewrite H.
  Qed.

  Lemma map_nth_app is1 is2 l:
    AllLess (length l) is1 ->
    map_nth (is1 ++ is2) l = map_nth is1 l ++ map_nth is2 l.

    induction is1; intros AL.
    - intuition.
    - map_nth_head; now rewrite (IHis1 (AllLess_skip AL)).
  Qed.

  Lemma map_nth_cons is l a:
    map_nth (map S is) (a :: l) = map_nth is l.

    induction is; simpl; auto.
    remember (nth_error l a0) as mm; destruct mm; auto.
    now rewrite IHis.
  Qed.

  Lemma map_nth_length is l:
    AllLess (length l) is <->
    length is = length (map_nth is l).

    revert l; induction is; intros l.
    - unfold AllLess; intuition.
    - split; intros H.
      + map_nth_head; simpl; apply eq_S.
        rewrite <- IHis; now apply (AllLess_skip H).
      + unfold AllLess; intros i I; simpl in I.
        simpl in H.
        remember (nth_error l a) as ne; destruct ne; try discriminate.
        simpl in H; apply eq_add_S in H; rewrite <- IHis in H.
        assert (a < length l) by (apply nth_error_Some; rewrite <- Heqne; discriminate).
        destruct I; [ omega | now apply H ].
  Qed.


  (* NoDup is Coq’s inductive type representing the absence of
     duplicates in a list. *)
  Local Hint Constructors NoDup.

  Lemma map_nth_NoDup is l:
    NoDup is ->
    NoDup l ->
    NoDup (map_nth is l).

    remember (map_nth is l) as ks.
    revert is l Heqks; induction ks; intros is l Heqks NDi NDl; auto.
    destruct is; simpl in Heqks; [ discriminate | ].
    remember (nth_error l n) as ne; destruct ne; [ | discriminate ].
    inversion Heqks; subst; clear Heqks.
    constructor.
    + contradict NDi.
      apply in_map_nth_position in NDi.
      destruct NDi as [i [INi [INl NTHi]]].
      rewrite Heqne in NTHi.
      rewrite (NoDup_nth_error l) in NDl.
      apply (NDl _ _ INl) in NTHi.
      subst; intro H; inversion H; contradiction.
    + apply (IHks is l); auto.
      inversion NDi; auto.
  Qed.

  Lemma map_nth_nth is i j l:
    nth_error is i = Some j ->
    AllLess (length l) is ->
    nth_error (map_nth is l) i = nth_error l j.

    intros SO AL; apply nth_error_split in SO.
    destruct SO as [l1 [l2 [Hi Hl]]]; subst.

    assert (length (map_nth l1 l) = length l1) as LL1.
    symmetry; apply map_nth_length; now apply (AllLess_app_1 AL).

    rewrite map_nth_app by (apply (AllLess_app_1 AL)).
    rewrite nth_error_app2 by omega.
    rewrite LL1; rewrite minus_diag.
    simpl.
    remember (nth_error l j) as ne; destruct ne; auto.
  Qed.

  (** A critical lemma for proving [Perm2] transitivity. *)
  Lemma map_nth_compose is js l:
    AllLess (length js) is ->
    AllLess (length l) js ->
    map_nth is (map_nth js l) = map_nth (map_nth is js) l.

    revert js l; induction is; intros js l ALi ALj; auto.
    map_nth_head.
    simpl (map_nth (n :: map_nth is js) l).
    remember (nth_error l n) as ne2; destruct ne2.
    remember (nth_error (map_nth js l) a) as ne3; destruct ne3;
      rewrite map_nth_nth with (j:=n) in Heqne3; auto.
    - rewrite <- Heqne3 in Heqne2; inversion Heqne2; subst.
      rewrite (IHis _ _ (AllLess_skip ALi) ALj); reflexivity.
    - rewrite <- Heqne3 in Heqne2; discriminate.
    - symmetry in Heqne2; rewrite nth_error_None in Heqne2.
      symmetry in Heqne; apply nth_error_In in Heqne.
      apply ALj in Heqne; omega.
  Qed.

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

    split; intros.
    apply in_seq in H; omega.
    apply in_seq; omega.
  Qed.

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

    intros L; pose L as L'; rewrite <- iota_length in L'.
    apply nth_split with (d:=0) in L'.
    destruct L' as [l1 [l2 [IEQ L1L]]].
    unfold iota in *; rewrite (seq_nth 0 0 L) in IEQ.
    rewrite IEQ.
    rewrite nth_error_app2.
    rewrite L1L; rewrite minus_diag; now simpl.
    omega.
  Qed.

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

    intro TR; induction TR.
    - intuition.
    - rewrite IHTR.
      repeat rewrite in_app_iff; simpl; intuition.
  Qed.

  Lemma transfer_length {A} (xs ys zs:list A):
    transfer xs ys zs ->
    length zs = length xs + length ys.

    intro TR; induction TR.
    - simpl; auto.
    - simpl; rewrite IHTR.
      repeat rewrite app_length; simpl; omega.
  Qed.

  Lemma in_transfer_rest {A} (xs ys zs:list A) a:
    transfer xs ys zs ->
    In a zs ->
    ~ In a xs ->
    In a ys.

    intros TR; induction TR; intros Iz NIx.
    - auto.
    - apply not_in_cons in NIx.
      destruct NIx as [Ny NIx].
      apply in_remove_middle with (b:=y); auto.
  Qed.


  Lemma NoDup_AllLess_transfer n xs:
    NoDup xs ->
    AllLess n xs ->
    exists ys, transfer xs ys (iota n).

    induction xs; intros ND AL.
    - exists (iota n); constructor.
    - inversion ND; subst.
      generalize (AllLess_skip AL); intro AL0.
      generalize (IHxs H2 AL0); intro IH.
      destruct IH as [ys IH].
      assert (In a ys). {
        apply (in_transfer_rest _ _ _ a IH).
        rewrite in_iota_iff; auto.
        apply AL; intuition.
        auto.
      }
      apply in_split in H.
      destruct H as [y1 [y2 H]]; subst.
      exists (y1 ++ y2); now constructor.
  Qed.

  Lemma NoDup_nat_complete i is:
    NoDup is ->
    AllLess (length is) is ->
    i < length is ->
    In i is.

    intros ND AL Less.
    generalize (NoDup_AllLess_transfer (length is) is ND AL);
      intros TR.
    destruct TR as [ys TR].
    generalize (transfer_length _ _ _ TR); intros TRlen.
    rewrite iota_length in TRlen.
    assert (length ys = 0) by omega.
    apply length_zero_iff_nil in H; subst.
    rewrite <- app_nil_r.
    rewrite <- (in_transfer_iff _ _ _ _ TR).
    now rewrite in_iota_iff.
  Qed.

End NoDupNatComplete.


(** ** [NatCyclePerm]

   This is the cycle-based permutation definition that lets us show
   reflexivity, symmetry, and transitivity without further
   assumptions. *)

Section NatCyclePerm.

  Inductive NatCyclePerm : list nat -> list nat -> Prop :=
  | ncp_nil : NatCyclePerm [] []
  | ncp_cons : forall is js i,
      NatCyclePerm is js -> ~ In i is ->
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

    revert is; induction js; intros is NDx NDy I.
    - assert (length is = length ([]:list nat)).
      apply NoDup_in_iff_length; auto.
      simpl in H.
      apply length_zero_iff_nil in H.
      subst; auto.
    - assert (In a is) by (apply I; intuition).
      apply in_split in H.
      destruct H as [l1 [l2 H]]; subst.
      apply ncp_app_cycle.
      rewrite <- app_comm_cons.
      constructor.
      apply ncp_app_cycle.
      apply IHjs.
      + now apply NoDup_remove_1 with (a:=a).
      + now apply NoDup_remove_1 with (a:=a) (l:=[]).
      + now apply NoDup_remove_iff with (a0:=a).
      + rewrite in_app_iff.
        rewrite or_comm.
        rewrite <- in_app_iff.
        now apply NoDup_remove_2 with (a:=a).
  Qed.

  Lemma ncp_expand is js:
    NatCyclePerm is js ->
    NoDup is
    /\ NoDup js
    /\ (forall i, In i is <-> In i js).

    intro PE; induction PE; auto.
    - repeat split; try apply NoDup_nil; auto.
    - destruct IHPE as [NDx [NDy IH]].
      split; [ now apply NoDup_cons | ].
      split; [ apply NoDup_cons;
               try rewrite <- IH; auto | ].
      intros; simpl; rewrite <- IH; intuition.
    - destruct IHPE as [NDx [NDy IH]].
      split; [ | split].
      + apply NoDup_app_swap; now assumption.
      + assumption.
      + intros; rewrite <- IH; rewrite in_app_iff.
        simpl; intuition.
  Qed.

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

    intros ND PE; induction PE; auto.
    - inversion ND; subst.
      apply IHPE in H2.
      apply ncp_expand in H2.
      destruct H2 as [NDl [NDl' IN]].
      apply ncp_all; auto.
      apply NoDup_cons.
      now rewrite <- IN.
      assumption.
      intros i; simpl; rewrite <- IN; reflexivity.
    - inversion ND; subst.
      inversion H2; subst.
      apply ncp_all; auto.
      + apply NoDup_cons.
        contradict H1; simpl in *; intuition.
        apply NoDup_cons; auto.
        contradict H1; simpl in *; intuition.
      + intros i; simpl.
        intuition.
    - apply IHPE1 in ND.
      generalize (ncp_expand _ _ ND); intros H.
      destruct H as [NDl [NDl' IN]].
      apply IHPE2 in NDl'.
      now apply ncp_trans with (js:=l').
  Qed.

  Lemma ncp_perm is js:
    NatCyclePerm is js ->
    Permutation is js.

    intros ND; induction ND; auto.
    rewrite (Permutation_app_comm is [i]).
    now apply IHND.
  Qed.

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

    intros PE AL.
    induction PE; simpl.
    - auto.
    - remember (nth_error ctx i) as a.
      destruct a; constructor.
      apply IHPE; now apply (AllLess_skip AL).
    - assert (AllLess (length ctx) is) as ALX by (now apply (AllLess_app_1 AL)).
      assert (Perm2 (map_nth (i :: is) ctx) (map_nth js ctx)) as IPE.
      apply IHPE.
      apply AllLess_cons; auto; apply (AllLess_app_2 AL); intuition.
      clear IHPE.
      rewrite map_nth_app by (apply ALX).
      simpl in *.
      remember (nth_error ctx i) as a; destruct a.
      + now apply perm2_cycle.
      + symmetry in Heqa; apply nth_error_None in Heqa.
        assert (i < length ctx) by (apply AL; intuition).
        omega.
  Qed.

  Lemma perm2_np {A} (xs ys:list A):
    Perm2 xs ys ->
    exists is, NatCyclePerm is (iota (length xs))
               /\ map_nth is ys = xs.

    intros PE; induction PE.
    - exists []; repeat split; auto.
    - destruct IHPE as [is [NPE MX]].
      exists (0 :: map S is).
      apply ncp_expand in NPE.
      destruct NPE as [NDi [NDj IN]].
      split.
      + simpl length.
        rewrite iota_S; constructor.
        apply ncp_all.
        * apply FinFun.Injective_map_NoDup; auto.
          unfold FinFun.Injective; now apply eq_add_S.
        * apply FinFun.Injective_map_NoDup; auto.
          unfold FinFun.Injective; now apply eq_add_S.
        * intros; repeat rewrite in_map_iff.
          split; intros.
          destruct H as [m [S I]].
          exists m; rewrite <- IN; intuition.
          destruct H as [m [S I]].
          exists m; rewrite IN; intuition.
        * rewrite in_map_iff.
          intro H; destruct H as [m [S I]]; omega.
      + simpl.
        rewrite map_nth_cons.
        rewrite MX; auto.
    - destruct IHPE as [is [NP MX]].
      assert (length is = length (iota (length (a :: x)))) as Lis
          by (apply (ncp_length_eq NP)).
      rewrite iota_length in Lis; simpl in Lis.
      destruct is; simpl in MX; try discriminate.
      remember (nth_error y n) as b.
      destruct b; try discriminate.
      exists (is ++ [n]); split.
      + apply ncp_cycle.
        rewrite app_length; rewrite plus_comm;
          rewrite <- app_length; now apply NP.
      + inversion MX; subst.
        rewrite map_nth_app; simpl.
        now rewrite <- Heqb.
        rewrite map_nth_length.
        now apply eq_add_S.
  Qed.


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

    intros.
    assert (length xs = length ys) as LE by (now apply perm2_length_eq).
    apply perm2_np in H.
    destruct H as [is [NP MX]].
    apply ncp_sym in NP.
    rewrite <- MX.
    rewrite <- (map_nth_iota ys) at 1.
    rewrite <- LE.
    apply ncp_perm2; auto.
    rewrite <- LE; now apply iota_AllLess.
  Qed.

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

    intros PX PY.
    remember (length xs) as n.
    generalize (perm2_length_eq _ _ PX); intros Heqys.
    generalize (perm2_length_eq _ _ PY); intros Heqzs.
    rewrite <- Heqn in *; rewrite <- Heqys in *.

    apply perm2_np in PX.
    destruct PX as [is [NPX MX]].
    apply perm2_np in PY.
    destruct PY as [js [NPY MZ]].
    rewrite <- Heqn in *; rewrite <- Heqys in *.
    generalize (ncp_length_eq NPX); intros Heqjs.
    generalize (ncp_length_eq NPY); intros Heqks.
    rewrite iota_length in *.

    assert (AllLess n is) as ALI. {
      unfold AllLess; intros i H.
      apply in_iota_iff.
      now apply (ncp_in_iff NPX).
    }
    assert (AllLess n js) as ALJ. {
      unfold AllLess; intros j H.
      apply in_iota_iff.
      now apply (ncp_in_iff NPY).
    }
    generalize (ncp_NoDup_is NPX); intros NDi.
    generalize (ncp_NoDup_is NPY); intros NDj.
    assert (length (map_nth is js) = n) as Heqmij. {
      pose (map_nth_length is js).
      rewrite Heqks in i.
      rewrite i in ALI.
      rewrite <- ALI; now rewrite Heqjs.
    }
    assert (forall a, In a (map_nth is js) <-> In a (iota n)) as IN. {
      intros i; split; intros.
      - apply in_map_nth in H; now apply (ncp_in_iff NPY).
      - apply NoDup_nat_complete.
        apply map_nth_NoDup; auto.
        unfold AllLess; intros ii HH.
        rewrite Heqmij.
        apply ALJ.
        now apply in_map_nth with (is0:=is).
        rewrite Heqmij; now apply in_iota_iff.
    }

    replace xs with (map_nth (map_nth is js) zs).
    replace zs with (map_nth (iota n) zs) at 2.

    - apply ncp_perm2.
      apply ncp_all; auto.
      apply map_nth_NoDup; auto.
      now apply iota_NoDup.
      rewrite <- Heqzs; unfold AllLess; intros i H.
      apply ALJ; now apply (in_map_nth is).
    - rewrite Heqzs; apply map_nth_iota.
    - rewrite <- map_nth_compose.
      now rewrite MZ.
      now rewrite Heqks.
      now rewrite <- Heqzs.
  Qed.

End Perm2.
