Require Import Arith.
Require Import Omega.
Require Import Recdef.
Require Import List.
Require Import Program.Tactics.
Require Import Classical.

(* A *group* is an algebraic structure comprising a set of elements
   `T` and a binary operation `f` and satisfying four laws:

   1. CLOSURE: If `x, y ∈ T`, then `f x y ∈ T`.
   2. ASSOCIATIVITY: `f x (f y z) = f (f x y) z`.
   3. RIGHT IDENTITY: There exists an identity element `e ∈ T`
      where `f x e = x` for all `x`.
   4. RIGHT INVERSE: Every element `x` has a right inverse, `y`,
      so that `f x y = e`.

   We can express this in Coq like so, using a *type class*. The
   type class is parameterized on the set `T`, the operation `f`,
   the right-identity element `e`, and the inverse function `i`.
   Then there are three laws that must hold. *)

Class Group {T} {f:T -> T -> T} {e:T} {i:T -> T} := {
  gassoc : forall a b c:T, f a (f b c) = f (f a b) c;
  grightid : forall a:T, f a e = a;
  grightinv : forall a:T, f a (i a) = e
}.


(* To show that a given set and operation form a group, we create an
   *instance* of the Group type class.

   Let’s show that addition on integers (the Coq `Z` type) is a group.
   The identity element is 0 (`Z0`), and the inverse function is
   `Z.opp` (Coq’s name for the unary negative operator).

   To declare the type instance, we first give its arguments:
   `Z Z.add Z0 Z.opp`. Then we need to show that the group laws hold.
   Here, we do that using a `Proof` environment, which opens three
   subgoals, one per law. *)

Instance Z_Group: @Group Z Z.add Z0 Z.opp := { }.
Proof.
  - apply Z.add_assoc.
  - apply Z.add_0_r.
  - apply Z.add_opp_diag_r.
Qed.


(* Given the `Z_Group` instance, we can prove facts about `Z`. *)
Lemma Z_add_assoc x y z:
  (x + (y + z))%Z = (x + y + z)%Z.

  apply gassoc. (* Magic! Coq finds `Z_Group`. *)
Qed.


(* But this becomes much more interesting if we can prove some facts
   about *all* groups. *)

Section GroupFacts.
  Variable T:Type.
  Variable f:T -> T -> T.
  Variable e:T.
  Variable i:T -> T.
  Variable G:@Group T f e i.

  Infix "*" := f.

  (* Gain local names for the group laws on group G. *)
  Local Definition Gassoc := @gassoc _ _ _ _ G.
  Local Definition Grightinv := @grightinv _ _ _ _ G.
  Local Definition Grightid := @grightid _ _ _ _ G.

  Set Implicit Arguments.

  Lemma mult_both a b c d1 d2:
    a * c = d1 ->
    b * c = d2 ->
    a = b ->
    d1 = d2.

    intros; rewrite <- H; rewrite <- H0; rewrite H1; auto.
  Qed.


  (* Your turn! These generic laws are true for all groups. *)
  Lemma characterizingid a:
    a * a = a ->
    a = e.

    intros.
    rewrite <- (Grightid a).
    rewrite <- (Grightinv a).
    rewrite gassoc.
    rewrite H.
    auto.
  Qed.

  Lemma leftinv a:
    i a * a = e.

    apply characterizingid.
    rewrite gassoc.
    rewrite <- (gassoc (i a) a).
    rewrite Grightinv.
    rewrite Grightid.
    auto.
  Qed.

  Lemma leftid a:
    e * a = a.

    rewrite <- (Grightinv a).
    rewrite <- Gassoc.
    rewrite leftinv.
    rewrite Grightid.
    auto.
  Qed.

  Lemma leftid_uniq p a:
    p * a = a ->
    p = e.

    intros.
    rewrite <- Grightid at 1.
    rewrite <- (Grightinv a).
    rewrite Gassoc.
    rewrite H.
    auto.
  Qed.

  Lemma rightinv_uniq a b:
    a * b = e ->
    b = i a.

    intros.
    rewrite <- (Grightid (i a)).
    rewrite <- H.
    rewrite Gassoc.
    rewrite (leftinv a).
    rewrite leftid.
    auto.
  Qed.

  Lemma leftinv_uniq a b:
    a * b = e ->
    a = i b.

    intros.
    rewrite <- (leftid (i b)).
    rewrite <- H.
    rewrite <- Gassoc.
    rewrite Grightinv.
    rewrite Grightid.
    auto.
  Qed.

  Lemma right_cancel a b x:
    a * x = b * x ->
    a = b.

    intros.
    rewrite <- Grightid at 1.
    rewrite <- Grightid.
    rewrite <- (Grightinv x) at 1.
    rewrite <- (Grightinv x) at 1.
    rewrite Gassoc.
    rewrite H.
    rewrite <- Gassoc.
    auto.
  Qed.

  Lemma left_cancel a b x:
    x * a = x * b ->
    a = b.

    intros.
    rewrite <- leftid.
    rewrite <- leftid at 1.
    rewrite <- (leftinv x).
    rewrite <- Gassoc.
    rewrite H.
    rewrite Gassoc.
    auto.
  Qed.

  Lemma inv_distrib a b:
    i (a * b) = i b * i a.

    apply right_cancel with (x:=(a * b)).
    rewrite leftinv.
    rewrite <- Gassoc.
    rewrite (Gassoc (i a)).
    rewrite leftinv.
    rewrite leftid.
    rewrite leftinv.
    auto.
  Qed.

  Lemma double_inv a:
    i (i a) = a.

    rewrite <- Grightid.
    rewrite <- Grightid at 1.
    rewrite <- (Grightinv (i a)).
    rewrite Gassoc.
    rewrite leftinv.
    rewrite leftid.
    rewrite Gassoc.
    rewrite Grightinv.
    rewrite leftid.
    auto.
  Qed.

  Lemma id_inv:
    i e = e.

    rewrite <- leftid at 1.
    rewrite Grightinv.
    auto.
  Qed.

  Unset Implicit Arguments.
End GroupFacts.


(* Now these *general* group facts can be used to prove properties
   about any group, such as Z. *)

Lemma Z_inv_distrib (a b:Z):
  (- (a + b))%Z = (- b + - a)%Z.

  apply (inv_distrib Z_Group).
Qed.


(* But of course there are many other groups. We now show that
   addition modulo 32 is a group. *)

(* `Z32` is the set `{0, 1, ..., 31}`. We write it as a dependent
   type. Constructing a `Z32` requires two things: a `nat` and a proof
   that the `nat` is less than 32. *)
Inductive Z32 : Set :=
| z32 : forall n:nat, n < 32 -> Z32.
Hint Constructors Z32.

(* Two Z32s are equal iff their `nat` components are equal.
   The proof of this lemma uses classical logic. *)
Lemma z32_proof_irrelevance n pf1 p pf2:
  n = p -> z32 n pf1 = z32 p pf2.

  intros; subst.
  assert (pf1 = pf2) by (apply proof_irrelevance).
  subst; auto.
Qed.


(* Addition on integers (mod 32) *)
Definition z32_add: Z32 -> Z32 -> Z32.
  (* What we want to do: given `x y`, return `(x + y) mod 32`.
     But in order to construct the answer as a Z32, we must provide a
     proof that the returned value’s `nat` component is less than 32.
     It’s easiest to do this by editing a proof. *)
  refine (fun x y => match (x, y) with
                     | (z32 n _, z32 p _) => z32 ((n + p) mod 32) _
                     end).
  apply Nat.mod_upper_bound; discriminate.
Defined.

(* Addition on integers mod 32 is associative *)
Lemma z32_add_assoc x y z:
  z32_add x (z32_add y z) = z32_add (z32_add x y) z.

  destruct x, y, z; unfold z32_add.
  apply z32_proof_irrelevance.
  rewrite Nat.add_mod_idemp_l by omega.
  rewrite Nat.add_mod_idemp_r by omega.
  rewrite plus_assoc; auto.
Qed.


(* Zero (mod 32) *)
Definition z32_0 : Z32.
  refine (z32 0 _).
  omega.
Defined.


(* Inverse on integers (mod 32) *)
Definition z32_inv: Z32 -> Z32.
  refine (fun x => match x with
                   | (z32 0 _) => x
                   | (z32 (S n) pf) => z32 (32 - (S n)) _
                   end).
  omega.
Defined.

(* Inverse is an inverse *)
Lemma z32_add_inv_diag x:
  z32_add x (z32_inv x) = z32_0.
  remember (z32_inv x) as y; destruct x, y.
  simpl; apply z32_proof_irrelevance.
  destruct n.
  - simpl in Heqy; inversion Heqy; auto.
  - assert (n0 = 32 - S n) by (simpl in Heqy; inversion Heqy; auto).
    subst.
    rewrite <- le_plus_minus by omega.
    apply Nat.mod_same; discriminate.
Qed.


(* Now we are ready to show that Z32 is a group. *)
Instance Z32_Group : @Group Z32 z32_add z32_0 z32_inv := { }.
Proof.
  - apply z32_add_assoc.
  - intros; unfold z32_add; destruct a.
    apply z32_proof_irrelevance.
    rewrite <- plus_n_O.
    apply Nat.mod_small; auto.
  - apply z32_add_inv_diag.
Qed.


(* Which lets us easily prove facts about Z32. *)
Lemma Z32_rightinv_uniq x y:
  z32_add x y = z32_0 ->
  y = z32_inv x.

  apply (rightinv_uniq Z32_Group).
Qed.
