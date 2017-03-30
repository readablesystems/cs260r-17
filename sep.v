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

Module WXFacts_fun (E:DecidableType) (Import Map:FMapInterface.WSfun E).
Module MapF := FMapFacts.WFacts_fun E Map.
Module MapProperties := FMapFacts.WProperties_fun E Map.
Section XFacts.
  Notation eq_dec := E.eq_dec.
  Context {elt: Type}.
  Implicit Types m: t elt.
  Implicit Types x y z: key.
  Implicit Types e: elt.
  Notation Partition := MapProperties.Partition.
  Notation Disjoint := MapProperties.Disjoint.
  Notation update := MapProperties.update.


  Definition Submap m1 m2 :=
    forall k e, MapsTo k e m1 -> MapsTo k e m2.

  Lemma Submap_in:
    forall {m1 m2}, Submap m1 m2 ->
                    forall k, In k m1 -> In k m2.
  Admitted.


  (* Pull in the library’s facts on Disjoint and Partition. *)
  Lemma Disjoint_alt:
    forall m m', Disjoint m m' <->
                 (forall k e e', MapsTo k e m -> MapsTo k e' m' -> False).
  Admitted.

  Lemma Disjoint_empty_r:
    forall {m}, Disjoint m (Map.empty elt).
  Admitted.

  Lemma Disjoint_sym:
    forall {m1 m2}, Disjoint m1 m2 -> Disjoint m2 m1.
  Admitted.

  Lemma Disjoint_in_nin:
    forall {m1 m2}, Disjoint m1 m2 ->
                    forall k, In k m1 -> ~ In k m2.
  Admitted.

  Lemma Disjoint_mapsto_nin:
    forall {m1 m2}, Disjoint m1 m2 ->
                    forall k e, MapsTo k e m1 -> ~ In k m2.
  Admitted.

  Lemma Disjoint_submap_r:
    forall m1 m2 m3, Disjoint m1 m2 ->
                     Submap m3 m2 -> Disjoint m1 m3.
  Admitted.


  Lemma update_in_iff:
    forall m1 m2 k, In k (update m1 m2) <-> In k m1 \/ In k m2.
  Admitted.

  Lemma update_mapsto_iff:
    forall m1 m2 k e, MapsTo k e (update m1 m2) <->
                      (MapsTo k e m2 \/ (MapsTo k e m1 /\ ~ In k m2)).
  Admitted.

  Lemma disjoint_update_mapsto_iff:
    forall {m1 m2}, Disjoint m1 m2 ->
                    forall k e, MapsTo k e (update m1 m2) <->
                                MapsTo k e m1 \/ MapsTo k e m2.
  Admitted.

  Lemma disjoint_update_comm:
    forall {m1 m2}, Disjoint m1 m2 ->
                    Map.Equal (update m1 m2) (update m2 m1).
  Admitted.

  Lemma update_submap_r:
    forall m1 m2, Submap m2 (update m1 m2).
  Admitted.

  Lemma disjoint_update_submap_l:
    forall {m1 m2}, Disjoint m1 m2 ->
                    Submap m1 (update m1 m2).
  Admitted.


  Lemma Partition_disjoint:
    forall {m m1 m2}, Partition m m1 m2 -> Disjoint m1 m2.
  Admitted.

  Lemma Partition_mapsto_iff:
    forall {m m1 m2}, Partition m m1 m2 ->
                      forall k e, MapsTo k e m <->
                                  MapsTo k e m1 \/ MapsTo k e m2.
  Admitted.

  Lemma Partition_mapsto_l:
    forall {m m1 m2}, Partition m m1 m2 ->
                      forall k e, MapsTo k e m1 -> MapsTo k e m.
  Admitted.

  Lemma Partition_mapsto_r:
    forall {m m1 m2}, Partition m m1 m2 ->
                      forall k e, MapsTo k e m2 -> MapsTo k e m.
  Admitted.

  Lemma Partition_submap_l:
    forall {m m1 m2}, Partition m m1 m2 -> Submap m1 m.
  Admitted.

  Lemma Partition_submap_r:
    forall {m m1 m2}, Partition m m1 m2 -> Submap m2 m.
  Admitted.

  Lemma Partition_in_iff:
    forall {m m1 m2}, Partition m m1 m2 ->
                      forall k, In k m <-> In k m1 \/ In k m2.
  Admitted.

  Lemma Partition_in_l:
    forall {m m1 m2}, Partition m m1 m2 ->
                      forall k, In k m1 -> In k m.
  Admitted.

  Lemma Partition_in_r:
    forall {m m1 m2}, Partition m m1 m2 ->
                      forall k, In k m2 -> In k m.
  Admitted.

  Lemma Partition_refl:
    forall m, Partition m m (Map.empty elt).
  Admitted.

  Lemma Partition_sym:
    forall m m1 m2, Partition m m1 m2 -> Partition m m2 m1.
  Admitted.

  Lemma Partition_empty_r:
    forall m m', Partition m m' (Map.empty elt) -> Map.Equal m m'.
  Admitted.

  Lemma Partition_update:
    forall m m1 m2, Partition m m1 m2 -> Map.Equal m (update m1 m2).
  Admitted.

  Lemma disjoint_update_partition:
    forall m1 m2, Disjoint m1 m2 -> Partition (update m1 m2) m1 m2.
  Admitted.

  Lemma Partition_assoc:
    forall m m1 m2 m2a m2b,
      Partition m m1 m2 ->
      Partition m2 m2a m2b ->
      Partition m (update m1 m2a) m2b.
  Admitted.

  Lemma Partition_add_1:
    forall m m1 m2 k v v1,
      Partition m (Map.add k v1 m1) m2 ->
      Partition (Map.add k v m) (Map.add k v m1) m2.
  Admitted.

End XFacts.
End WXFacts_fun.


Module Separation.
  Definition ptr := Z.
  Definition ptr_eq := Z.eq_dec.
  Definition value := Z.
  Implicit Types v: value.

  Module Heap := FMapList.Make Z_as_OT.
  Module HeapF := FMapFacts.WFacts_fun Z_as_OT Heap.
  Module HeapP := FMapFacts.WProperties_fun Z_as_OT Heap.
  Module HeapX := WXFacts_fun Z_as_OT Heap.

  Definition heap := Heap.t value.
  Implicit Types h : heap.
  Definition empty_heap := Heap.empty value.

  Notation heap_Equal := Heap.Equal.


  (* Assertions, aka heap propositions *)
  Definition weak_assertion := heap -> Prop.

  Definition assertion_wf (wa:weak_assertion) :=
    forall h1 h2,
      heap_Equal h1 h2 -> wa h1 -> wa h2.

  Lemma assertion_wf_iff:
    forall wa:weak_assertion,
      forall wawf:assertion_wf wa,
        forall h1 h2,
          heap_Equal h1 h2 -> wa h1 <-> wa h2.
  Proof.
    split; intros; unfold assertion_wf in *.
    - now apply wawf with (h1:=h1).
    - apply wawf with (h1:=h2); [ symmetry | ]; auto.
  Qed.

  Inductive assertion : Type :=
  | Assert : forall wa:weak_assertion,
      forall wawf:assertion_wf wa,
        assertion.
  Hint Constructors assertion.

  Definition asserts : assertion -> heap -> Prop :=
    fun a h =>
      match a with
      | Assert wa _ => wa h
      end.

  Global Instance: Proper (eq ==> heap_Equal ==> iff) asserts.
  Proof.
    intros a1 a2 aeq h1 h2 heq; subst; destruct a2.
    unfold asserts; split; intros.
    - now apply (wawf _ _ heq).
    - symmetry in heq; now apply (wawf _ _ heq).
  Qed.


  Definition assertion_imp : assertion -> assertion -> Prop :=
    fun a1 a2 =>
      forall h, asserts a1 h -> asserts a2 h.

  Definition assertion_iff : assertion -> assertion -> Prop :=
    fun a1 a2 =>
      forall h, asserts a1 h <-> asserts a2 h.

  Infix "===>" := assertion_imp (at level 90) : sep_scope.
  Infix "<===>" := assertion_iff (at level 90) : sep_scope.
  Local Open Scope sep_scope.


  Definition emp : assertion.
    refine (Assert (fun h => heap_Equal h empty_heap) _).
    unfold assertion_wf; intros; now rewrite <- H.
  Defined.

  Definition pointsto : ptr -> value -> assertion.
    intros p v.
    refine (Assert (fun h => heap_Equal h (Heap.add p v empty_heap)) _).
    unfold assertion_wf; intros; now rewrite <- H.
  Defined.
  Infix "|>" := pointsto (no associativity, at level 75) : sep_scope.

  Definition points : ptr -> assertion.
    intros p.
    refine (Assert (fun h => exists v, heap_Equal h (Heap.add p v empty_heap)) _).
    unfold assertion_wf; intros.
    destruct H0; exists x; now rewrite <- H.
  Defined.
  Notation "p |>?" := (points p) (no associativity, at level 75) : sep_scope.

  Definition weak_star : assertion -> assertion -> weak_assertion :=
    fun a1 a2 =>
      fun h =>
        exists h1 h2, HeapP.Partition h h1 h2 /\ asserts a1 h1 /\ asserts a2 h2.
  
  Definition star : assertion -> assertion -> assertion.
    intros a1 a2.
    refine (Assert (weak_star a1 a2) _).
    unfold assertion_wf; unfold weak_star; intros; destruct_conjs.
    exists H0, H1; rewrite <- H; intuition.
  Defined.
  Infix "**" := star (right associativity, at level 80) : sep_scope.

  Definition heq : heap -> assertion.
    intros h.
    refine (Assert (fun h' => Heap.Equal h h') _).
    unfold assertion_wf; intros; transitivity h1; auto.
  Defined.
 
  Definition weak_imp : assertion -> assertion -> weak_assertion :=
    fun a1 a2 =>
      fun h => asserts a1 h -> asserts a2 h.

  Definition imp : assertion -> assertion -> assertion.
    intros a1 a2.
    refine (Assert (weak_imp a1 a2) _).
    unfold assertion_wf. unfold weak_imp. intros.
    rewrite H in *. auto.
  Qed.

  Definition weak_magic_wand : assertion -> assertion -> weak_assertion :=
    fun a1 a2 =>
      fun h => forall h', HeapP.Disjoint h h' -> asserts a1 h' ->
                          asserts a2 (HeapP.update h h').

  Definition magic_wand : assertion -> assertion -> assertion.
    intros a1 a2.
    refine (Assert (weak_magic_wand a1 a2) _).
    unfold assertion_wf. unfold weak_magic_wand. intros.
    assert (HeapP.Disjoint h1 h') by (now rewrite H).
    apply (H0 _ H3) in H2.
    assert (heap_Equal (HeapP.update h2 h') (HeapP.update h1 h'))
      by (now rewrite H).
    now rewrite H4.
  Qed.


  Lemma emp_empty_heap:
    asserts emp empty_heap.
  Admitted.

  Lemma emp_equals_iff h:
    asserts emp h <-> heap_Equal h empty_heap.
  Admitted.

  Lemma heq_equals_iff h1 h:
    asserts (heq h1) h <-> heap_Equal h1 h.
  Admitted.

  Lemma pointsto_equals_iff a v h:
    asserts (pointsto a v) h <-> heap_Equal h (Heap.add a v empty_heap).
  Admitted.

  Lemma points_equals_iff a h:
    asserts (points a) h <-> exists v, heap_Equal h (Heap.add a v empty_heap).
  Admitted.

  Lemma star_iff :
    forall a1 a2 h, asserts (a1 ** a2) h <->
                    exists h1 h2, HeapP.Partition h h1 h2
                                  /\ asserts a1 h1 /\ asserts a2 h2.
  Admitted.

  Ltac destruct_star :=
    match goal with
    | [ |- context [ asserts (?a1 ** ?a2) ?h ] ] => rewrite (star_iff a1 a2 h)
    end.

  Ltac destruct_star_in H :=
    match goal with
    | [ H : context [ asserts (?a1 ** ?a2) ?h ] |- _ ] => rewrite (star_iff a1 a2) in H
    end.

  Lemma add_emp_r:
    forall a, a <===> a ** emp.
  Admitted.

  Lemma star_comm:
    forall a1 a2, a1 ** a2 ===> a2 ** a1.
  Admitted.

  Lemma star_assoc :
    forall a1 a2 a3 h, asserts (a1 ** a2 ** a3) h <-> asserts ((a1 ** a2) ** a3) h.
  Admitted.

  Lemma star_imp:
    forall {a1 a2}, a1 ===> a2 -> forall x, a1 ** x ===> a2 ** x.
  Admitted.

  Lemma pointsto_find:
    forall {p v h}, asserts (p |> v) h -> Heap.find p h = Some v.
  Admitted.

  Lemma star_pointsto_find:
    forall {p v a h}, asserts (p |> v ** a) h -> Heap.find p h = Some v.
  Admitted.

  Lemma points_find:
    forall {p h}, asserts (p |>?) h -> exists v, Heap.find p h = Some v.
  Admitted.

  Lemma star_points_find:
    forall {p a h}, asserts (p |>? ** a) h -> exists v, Heap.find p h = Some v.
  Admitted.



  
  Definition Cmd := heap -> option heap.

  Definition sep_triple (p:assertion) (c:Cmd) (q:assertion) :=
    forall rest h,
      asserts (p ** heq rest) h ->
      exists h', c h = Some h' /\ asserts (q ** heq rest) h'. (* NB stuff about termination *)
  Notation "{{ P }} c {{ Q }}" := (sep_triple P c Q) (at level 90) : sep_scope.


  Lemma consequence:
    forall p p' c q q',
      {{p}} c {{q}} ->
      p' ===> p ->
      q ===> q' ->
      {{p'}} c {{q'}}.
  Proof.
    unfold sep_triple; intros.
    apply star_imp with (x:=heq rest) in H0.
    apply star_imp with (x:=heq rest) in H1.
    apply H0 in H2.
    apply H in H2.
    destruct_conjs.
    apply H1 in H4.
    exists H2; intuition.
  Qed.


  Lemma frame:
    forall p c q r,
      {{p}} c {{q}} ->
      {{p ** r}} c {{q ** r}}.
  Proof.
    unfold sep_triple; intros.
    rewrite <- star_assoc in H0.
    rewrite star_iff in H0.
    destruct_conjs.
    assert (asserts (p ** heq H1) h).
    rewrite star_iff.
    exists H0, H1; intuition.
    unfold asserts; unfold heq; reflexivity.
    apply H in H5.
    destruct_conjs.
    exists H5.
    intuition.
    rewrite <- star_assoc.
    rewrite star_iff in H7; destruct_conjs.
    rewrite star_iff.
    exists H7, H1.
    rewrite heq_equals_iff in H11.
    repeat rewrite H11 in *.
    intuition.
  Qed.


  Inductive expr :=
  | Ev : Z -> expr
  | Ebin : expr -> expr -> (Z -> Z -> Z) -> expr
  | Eread : expr -> expr
  | Ewrite : expr -> expr -> expr.

  Fixpoint estepf (e:expr) (h:heap) : option (expr * heap) :=
    match e with
    | Ebin (Ev v1) (Ev v2) op => Some (Ev (op v1 v2), h)
    | Ebin (Ev v1) e2 op => match estepf e2 h with
                            | Some (e2',h') => Some (Ebin (Ev v1) e2' op, h')
                            | _ => None
                            end
    | Ebin e1 e2 op => match estepf e1 h with
                       | Some (e1',h') => Some (Ebin e1' e2 op, h')
                       | _ => None
                       end
    | Eread (Ev a) => match Heap.find a h with
                      | Some v => Some (Ev v, h)
                      | _ => None
                      end
    | Eread e => match estepf e h with
                 | Some (e',h') => Some (Eread e', h')
                 | _ => None
                 end
    | Ewrite (Ev a) (Ev v) => match Heap.find a h with
                              | Some _ => Some (Ev v, Heap.add a v h)
                              | _ => None
                              end
    | Ewrite (Ev a) e => match estepf e h with
                         | Some (e',h') => Some (Ewrite (Ev a) e', h')
                         | _ => None
                         end
    | Ewrite a e => match estepf a h with
                    | Some (a',h') => Some (Ewrite a' e, h')
                    | _ => None
                    end
    | _ => None
    end.

  Definition ecmd : expr -> Cmd :=
    fun e h =>
      match estepf e h with
      | Some (e', h') => Some h'
      | _ => None
      end.
  Hint Resolve ecmd.

  Lemma ecmd_estepf_iff e h h':
    ecmd e h = Some h' <-> exists e', estepf e h = Some (e', h').
  Proof.
    split; intros.
    unfold ecmd in *; remember (estepf e h) as s; destruct s.
    destruct p; exists e0; inversion H; intuition.
    discriminate.
    unfold ecmd in *; destruct H as [e' H]; rewrite H; auto.
  Qed.


  Lemma readv_tc:
    forall a v,
      {{ a |> v }} ecmd (Eread (Ev a)) {{ a |> v }}.
  Admitted.

  Lemma writev_tc:
    forall a v,
      {{ a |>? }} ecmd (Ewrite (Ev a) (Ev v)) {{ a |> v }}.
  Admitted.

  Lemma reads_tc:
    forall a1 a2 e1,
      {{a1}} ecmd e1 {{a2}} ->
      {{a1}} ecmd (Eread e1) {{a2}}.
  Proof.
    intros a1 a2 e1 H rest h A.
    generalize (H rest h A); intro G; destruct G as [hg [G1 G2]].
    exists hg; split; auto.
    rewrite ecmd_estepf_iff in G1; destruct G1 as [e' G1].
  Admitted.

End Separation.
