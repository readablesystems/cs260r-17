Require Import Bool Arith List Omega.
Require Import Recdef Morphisms.
Require Import Program.Tactics.
Require Import Relation_Operators.
Require FMapList.
Require FMapFacts.
Require Import Classical.
Require Import Coq.Classes.RelationClasses.
Require Import OrderedType OrderedTypeEx DecidableType.
Require Import Sorting.Permutation.
Import ListNotations.

Section ListFacts.
  Context {A:Type}.
  Implicit Types l:list A.

  Lemma filter_app (f:A -> bool) l1 l2:
    filter f (l1 ++ l2) = filter f l1 ++ filter f l2.
  Admitted.

  Lemma filter_app_eq (f:A -> bool) x y:
    filter f (x ++ y) = x ++ y ->
    filter f x = x /\ filter f y = y.
  Admitted.

  Lemma Forall_app (P:A -> Prop) l1 l2:
    Forall P (l1 ++ l2) <-> Forall P l1 /\ Forall P l2.
  Admitted.

End ListFacts.


Module WXFacts_fun (E:DecidableType) (Import Map:FMapInterface.WSfun E).
Module MapFacts := FMapFacts.WFacts_fun E Map.
Section XFacts.
  Notation eq_dec := E.eq_dec.
  Variable elt: Type.
  Implicit Types m: t elt.
  Implicit Types x y z: key.
  Implicit Types e: elt.

  Lemma add_same_Equal: forall m x e,
      MapsTo x e m ->
      Equal m (add x e m).
  Proof.
    intros; rewrite MapFacts.Equal_mapsto_iff; split; intros.
    - destruct (eq_dec x k); subst.
      + rewrite <- e1 in H0.
        rewrite (MapFacts.MapsTo_fun H H0).
        now eapply Map.add_1.
      + now eapply Map.add_2.
    - rewrite MapFacts.add_mapsto_iff in H0;
        destruct H0; destruct_conjs.
      + rewrite <- H0; now rewrite <- H1.
      + auto.
  Qed.

  Lemma add_redundant_Equal: forall m x e e',
      Equal (add x e m) (add x e (add x e' m)).
  Admitted.

  Lemma add_commutes: forall m x y e e',
      ~ E.eq x y ->
      Equal (add x e (add y e' m)) (add y e' (add x e m)).
  Admitted.

  Lemma add_remove_Equal: forall m x e,
      Equal (add x e m) (add x e (remove x m)).
  Admitted.

  Lemma remove_redundant_Equal: forall m x e,
      Equal (remove x m) (remove x (add x e m)).
  Admitted.

  Lemma remove_commutes: forall m x y,
      Equal (remove x (remove y m)) (remove y (remove x m)).
  Admitted.

End XFacts.
End WXFacts_fun.
