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
  Proof.
    intros m1 m2 S k I.
    destruct I.
    exists x.
    now apply S.
  Qed.


  (* Pull in the library’s facts on Disjoint and Partition. *)
  Lemma Disjoint_alt:
    forall m m', Disjoint m m' <->
                 (forall k e e', MapsTo k e m ->
                                 MapsTo k e' m' ->
                                 False).
  Proof.
    apply MapProperties.Disjoint_alt.
  Qed.

  Lemma Disjoint_empty_r:
    forall {m}, Disjoint m (Map.empty elt).
  Proof.
    intros; rewrite Disjoint_alt; intros.
    now rewrite MapF.empty_mapsto_iff in H0.
  Qed.

  Lemma Disjoint_sym:
    forall {m1 m2}, Disjoint m1 m2 -> Disjoint m2 m1.
  Proof.
    apply MapProperties.Disjoint_sym.
  Qed.

  Lemma Disjoint_in_nin:
    forall {m1 m2}, Disjoint m1 m2 ->
                    forall k, In k m1 -> ~ In k m2.
  Proof.
    intros m1 m2 D k I1 I2; apply (D k); intuition.
  Qed.

  Lemma Disjoint_mapsto_nin:
    forall {m1 m2}, Disjoint m1 m2 ->
                    forall k e, MapsTo k e m1 -> ~ In k m2.
  Proof.
    intros m1 m2 D k e M1 I2; apply (D k); intuition; now exists e.
  Qed.

  Lemma Disjoint_submap_r:
    forall m1 m2 m3, Disjoint m1 m2 ->
                     Submap m3 m2 -> Disjoint m1 m3.
  Proof.
    intros m1 m2 m3 D S k I; destruct I as [I1 I2].
    apply (Submap_in S) in I2; now apply (D k).
  Qed.


  Lemma update_in_iff:
    forall m1 m2 k, In k (update m1 m2) <-> In k m1 \/ In k m2.
  Proof.
    apply MapProperties.update_in_iff.
  Qed.

  Lemma update_mapsto_iff:
    forall m1 m2 k e, MapsTo k e (update m1 m2) <->
                      (MapsTo k e m2 \/
                       (MapsTo k e m1 /\ ~ In k m2)).
  Proof.
    apply MapProperties.update_mapsto_iff.
  Qed.

  Lemma disjoint_update_mapsto_iff:
    forall {m1 m2}, Disjoint m1 m2 ->
                    forall k e, MapsTo k e (update m1 m2) <->
                                MapsTo k e m1 \/ MapsTo k e m2.
  Proof.
    intros m1 m2 D k e; rewrite update_mapsto_iff.
    generalize (Disjoint_mapsto_nin D k e); intros G; intuition.
  Qed.

  Lemma disjoint_update_comm:
    forall {m1 m2}, Disjoint m1 m2 ->
                    Map.Equal (update m1 m2) (update m2 m1).
  Proof.
    intros m1 m2 D; rewrite MapF.Equal_mapsto_iff; intros.
    rewrite (disjoint_update_mapsto_iff D).
    rewrite (disjoint_update_mapsto_iff (Disjoint_sym D)).
    intuition.
  Qed.

  Lemma update_submap_r:
    forall m1 m2, Submap m2 (update m1 m2).
  Proof.
    intros m1 m2 k e M; apply update_mapsto_iff; now left.
  Qed.

  Lemma disjoint_update_submap_l:
    forall {m1 m2}, Disjoint m1 m2 ->
                    Submap m1 (update m1 m2).
  Proof.
    intros m1 m2 D k e M; apply disjoint_update_mapsto_iff; intuition.
  Qed.


  Lemma Partition_disjoint:
    forall {m m1 m2}, Partition m m1 m2 -> Disjoint m1 m2.
  Proof.
    unfold Partition; intuition.
  Qed.

  Lemma Partition_mapsto_iff:
    forall {m m1 m2}, Partition m m1 m2 ->
                      forall k e, MapsTo k e m <->
                                  MapsTo k e m1 \/ MapsTo k e m2.
  Proof.
    unfold Partition; intuition.
  Qed.

  Lemma Partition_mapsto_l:
    forall {m m1 m2}, Partition m m1 m2 ->
                      forall k e, MapsTo k e m1 -> MapsTo k e m.
  Proof.
    intros; rewrite (Partition_mapsto_iff H); intuition.
  Qed.

  Lemma Partition_mapsto_r:
    forall {m m1 m2}, Partition m m1 m2 ->
                      forall k e, MapsTo k e m2 -> MapsTo k e m.
  Proof.
    intros; rewrite (Partition_mapsto_iff H); intuition.
  Qed.

  Lemma Partition_submap_l:
    forall {m m1 m2}, Partition m m1 m2 -> Submap m1 m.
  Proof.
    intros m m1 m2 P k e M; rewrite (Partition_mapsto_iff P); intuition.
  Qed.

  Lemma Partition_submap_r:
    forall {m m1 m2}, Partition m m1 m2 -> Submap m2 m.
  Proof.
    intros m m1 m2 P k e M; rewrite (Partition_mapsto_iff P); intuition.
  Qed.

  Lemma Partition_in_iff:
    forall {m m1 m2}, Partition m m1 m2 ->
                      forall k, In k m <-> In k m1 \/ In k m2.
  Proof.
    intros; generalize (Partition_mapsto_iff H); split; intros.
    - destruct H1; rewrite H0 in H1; destruct or H1;
        [ left | right ]; now exists x.
    - destruct or H1; destruct H1; exists x; rewrite H0; intuition.
  Qed.

  Lemma Partition_in_l:
    forall {m m1 m2}, Partition m m1 m2 ->
                      forall k, In k m1 -> In k m.
  Proof.
    intros; rewrite (Partition_in_iff H); intuition.
  Qed.

  Lemma Partition_in_r:
    forall {m m1 m2}, Partition m m1 m2 ->
                      forall k, In k m2 -> In k m.
  Proof.
    intros; rewrite (Partition_in_iff H); intuition.
  Qed.


  Lemma Partition_refl:
    forall m, Partition m m (Map.empty elt).
  Proof.
    intros; unfold Partition; split.
    - apply Disjoint_empty_r.
    - intros; rewrite MapF.empty_mapsto_iff; intuition.
  Qed.

  Lemma Partition_sym:
    forall m m1 m2, Partition m m1 m2 -> Partition m m2 m1.
  Proof.
    apply MapProperties.Partition_sym.
  Qed.

  Lemma Partition_empty_r:
    forall m m', Partition m m' (Map.empty elt) ->
                 Map.Equal m m'.
  Proof.
    intros; apply MapF.Equal_mapsto_iff; intros.
    unfold Partition in *; destruct_conjs.
    generalize (H0 k e); rewrite MapF.empty_mapsto_iff; intuition.
  Qed.

  Lemma Partition_update:
    forall m m1 m2, Partition m m1 m2 ->
                    Map.Equal m (update m1 m2).
  Proof.
    intros; unfold MapProperties.Partition in *; destruct_conjs.
    apply MapF.Equal_mapsto_iff; intros.
    rewrite H0.
    rewrite (disjoint_update_mapsto_iff H).
    intuition.
  Qed.

  Lemma disjoint_update_partition:
    forall m1 m2, Disjoint m1 m2 ->
                  Partition (update m1 m2) m1 m2.
  Proof.
    intros; unfold Partition; split; auto; intros.
    rewrite (disjoint_update_mapsto_iff H); intuition.
  Qed.

  Lemma Partition_assoc:
    forall m m1 m2 m2a m2b,
      Partition m m1 m2 ->
      Partition m2 m2a m2b ->
      Partition m (update m1 m2a) m2b.
  Proof.
    intros; unfold Partition; split.
    - unfold Disjoint; intros k I; destruct I as [Ia Ib].
      apply update_in_iff in Ia; destruct or Ia.
      + apply (Partition_disjoint H k).
        now apply (Partition_in_r H0) in Ib.
      + now apply (Partition_disjoint H0 k).
    - intros; rewrite disjoint_update_mapsto_iff.
      rewrite (Partition_mapsto_iff H).
      rewrite (Partition_mapsto_iff H0).
      split; intuition.
      apply Disjoint_submap_r with (m2:=m2).
      apply (Partition_disjoint H).
      apply (Partition_submap_l H0).
  Qed.

  Lemma Partition_add_1:
    forall m m1 m2 k v v1,
      Partition m (Map.add k v1 m1) m2 ->
      Partition (Map.add k v m) (Map.add k v m1) m2.
  Proof.
    intros m m1 m2 k v v1 P.
    unfold Partition; split.
    - intros kk I; destruct I; apply (Partition_disjoint P kk).
      rewrite MapF.add_in_iff in *; intuition.
    - intros kk e.
      rewrite MapF.add_mapsto_iff.
      rewrite (Partition_mapsto_iff P).
      repeat rewrite MapF.add_mapsto_iff.
      intuition.
      right; split; intuition.
      apply (Partition_disjoint P kk).
      rewrite H in *; rewrite MapF.add_in_iff; intuition; now exists e.
  Qed.

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
    intros a1 a2 aeq h1 h2 heq.
    subst; destruct a2.
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
    unfold assertion_wf; intros.
    now rewrite <- H.
  Defined.

  Definition pointsto : ptr -> value -> assertion.
    intros p v.
    refine (Assert (fun h => heap_Equal h
                          (Heap.add p v empty_heap)) _).
    unfold assertion_wf; intros; now rewrite <- H.
  Defined.
  Infix "|>" := pointsto (no associativity, at level 75) : sep_scope.

  Definition points : ptr -> assertion.
    intros p.
    refine (Assert (fun h => exists v,
              heap_Equal h (Heap.add p v empty_heap)) _).
    unfold assertion_wf; intros.
    destruct H0; exists x; now rewrite <- H.
  Defined.
  Notation "p |>?" := (points p) (no associativity, at level 75) : sep_scope.

  Definition weak_star : assertion -> assertion ->
                         weak_assertion :=
    fun a1 a2 =>
      fun h =>
        exists h1 h2, HeapP.Partition h h1 h2 /\
                      asserts a1 h1 /\
                      asserts a2 h2.

  Definition star : assertion -> assertion ->
                    assertion.
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


  Lemma emp_empty_heap:
    asserts emp empty_heap.
  Proof.
    unfold asserts; unfold emp; reflexivity.
  Qed.

  Lemma emp_equals_iff h:
    asserts emp h <-> heap_Equal h empty_heap.
    split; intros.
    - auto.
    - rewrite H; apply emp_empty_heap.
  Qed.

  Lemma heq_equals_iff h1 h:
    asserts (heq h1) h <-> heap_Equal h1 h.
  Proof.
    split; intros.
    - auto.
    - unfold asserts; unfold heq; auto.
  Qed.

  Lemma pointsto_equals_iff a v h:
    asserts (pointsto a v) h <->
    heap_Equal h (Heap.add a v empty_heap).
  Proof.
    split; intros.
    - auto.
    - unfold asserts; unfold pointsto; auto.
  Qed.

  Lemma points_equals_iff a h:
    asserts (points a) h <-> exists v, heap_Equal h (Heap.add a v empty_heap).
  Proof.
    split; intros.
    - auto.
    - unfold asserts; unfold points; auto.
  Qed.

  Lemma star_iff :
    forall a1 a2 h, asserts (a1 ** a2) h <->
      exists h1 h2, HeapP.Partition h h1 h2
                    /\ asserts a1 h1 /\ asserts a2 h2.
  Proof.
    unfold asserts at 1; unfold star; unfold weak_star; intuition.
  Qed.

  Ltac destruct_star :=
    match goal with
    | [ |- context [ asserts (?a1 ** ?a2) ?h ] ] => rewrite (star_iff a1 a2 h)
    end.

  Ltac destruct_star_in H :=
    match goal with
    | [ H : context [ asserts (?a1 ** ?a2) ?h ] |- _ ] => rewrite (star_iff a1 a2) in H
    end.

  Lemma add_emp_r :
    forall a, a <===> a ** emp.
  Proof.
    split; intros.
    - destruct_star.
      exists h, empty_heap; split; [ | split].
      + apply HeapX.Partition_refl.
      + auto.
      + apply emp_empty_heap.
    - destruct_star_in H.
      destruct_conjs.
      rewrite emp_equals_iff in H3.
      rewrite H3 in H1.
      apply HeapX.Partition_empty_r in H1.
      now rewrite H1.
  Qed.

  Lemma star_comm :
    forall a1 a2, a1 ** a2 ===> a2 ** a1.
  Proof.
    intros a1 a2 h I.
    rewrite star_iff in *; destruct_conjs.
    exists H, I; intuition.
    now apply HeapX.Partition_sym.
  Qed.

  Lemma star_assoc :
    forall a1 a2 a3 h, asserts (a1 ** a2 ** a3) h <->
                       asserts ((a1 ** a2) ** a3) h.
    split; intros.
    - destruct_star_in H; destruct_conjs.
      destruct_star_in H3; destruct_conjs.
      destruct_star; exists (HeapP.update H H3), H4.
      split; [ | split ].
      + now apply HeapX.Partition_assoc with (m2:=H0).
      + destruct_star; exists H, H3; split; auto.
        apply HeapX.disjoint_update_partition.
        unfold HeapP.Partition in *; destruct_conjs.
        rewrite HeapP.Disjoint_alt in *; intros.
        assert (Heap.MapsTo k e' H0). rewrite H8; now left.
        apply (H1 _ _ _ H10 H12).
      + auto.
    - destruct_star_in H; destruct_conjs.
      destruct_star_in H2; destruct_conjs.
      destruct_star; exists H2, (HeapP.update H4 H0).
      assert (HeapP.Disjoint H0 H4). {
        unfold HeapP.Partition in *; destruct_conjs.
        intros k I; destruct_conjs.
        destruct H10, H11.
        assert (Heap.MapsTo k x0 H).
        rewrite H8; now right.
        apply (H1 k); split; [now exists x0 | now exists x].
      }
      split; [ | split ].
      + apply HeapP.Partition_sym.
        rewrite HeapX.disjoint_update_comm.
        apply HeapX.Partition_assoc with (m2:=H).
        now apply HeapP.Partition_sym.
        now apply HeapP.Partition_sym.
        now apply HeapP.Disjoint_sym.
      + auto.
      + destruct_star; exists H4, H0; split; [ | split ]; auto.
        apply HeapX.disjoint_update_partition.
        now apply HeapP.Disjoint_sym.
  Qed.

  Lemma star_imp:
    forall {a1 a2}, a1 ===> a2 ->
                    forall x, a1 ** x ===> a2 ** x.
  Proof.
    intros a1 a2 I x h L.
    unfold asserts in *; unfold star in *; unfold weak_star in *.
    destruct_conjs.
    apply I in H1.
    exists L, H; intuition.
  Qed.

  Lemma pointsto_find:
    forall {p v h}, asserts (p |> v) h -> Heap.find p h = Some v.
  Proof.
    intros p v h A.
    unfold asserts in *; unfold pointsto in *.
    rewrite A.
    apply Heap.find_1; now apply Heap.add_1.
  Qed.

  Lemma star_pointsto_find:
    forall {p v a h}, asserts (p |> v ** a) h -> Heap.find p h = Some v.
  Proof.
    intros p v a h A.
    rewrite star_iff in A; destruct_conjs.
    apply pointsto_find in H1.
    apply Heap.find_1; apply (HeapX.Partition_mapsto_l H0); now apply Heap.find_2.
  Qed.

  Lemma points_find:
    forall {p h}, asserts (p |>?) h -> exists v, Heap.find p h = Some v.
  Proof.
    intros p h A.
    unfold asserts in *; unfold points in *.
    destruct A.
    exists x; rewrite H; apply Heap.find_1; now apply Heap.add_1.
  Qed.

  Lemma star_points_find:
    forall {p a h}, asserts (p |>? ** a) h -> exists v, Heap.find p h = Some v.
  Proof.
    intros p a h A.
    rewrite star_iff in A; destruct_conjs.
    apply points_find in H1; destruct H1; exists x.
    apply Heap.find_1; apply (HeapX.Partition_mapsto_l H0); now apply Heap.find_2.
  Qed.




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
  Proof.
    intros a v rest h A; exists h.
    unfold ecmd; simpl.
    rewrite (star_pointsto_find A).
    unfold asserts in A; unfold star in A.
    intuition.
  Qed.

  Lemma writev_tc:
    forall a v,
      {{ a |>? }} ecmd (Ewrite (Ev a) (Ev v)) {{ a |> v }}.
    intros a v rest h A; exists (Heap.add a v h).
    unfold ecmd; simpl.
    generalize (star_points_find A); intros G; destruct G.
    rewrite H; intuition.
    exists (Heap.add a v empty_heap), rest; split; [ | split ].
    - rewrite star_iff in A; destruct_conjs.
      rewrite points_equals_iff in H2; destruct H2 as [xx H2]; rewrite H2 in H1.
      apply HeapX.Partition_add_1 with (v1:=xx).
      rewrite heq_equals_iff in H3; now rewrite H3.
    - rewrite pointsto_equals_iff; reflexivity.
    - rewrite heq_equals_iff; reflexivity.
  Qed.

  Lemma reads_tc:
    forall a1 a2 e1,
      {{a1}} ecmd e1 {{a2}} ->
      {{a1}} ecmd (Eread e1) {{a2}}.
  Proof.
    intros a1 a2 e1 H rest h A.
    generalize (H rest h A); intro G; destruct G as [hg [G1 G2]].
    exists hg; split; auto.
    rewrite ecmd_estepf_iff in G1; destruct G1 as [e' G1].
    destruct e1; try discriminate.
    all: rewrite ecmd_estepf_iff; exists (Eread e').
    all: simpl in *; rewrite G1; auto.
  Qed.

End Separation.
