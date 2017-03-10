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

(** * Process isolation

This problem set contains a model of a multi-process
operating system with a single ramdisk. You show that process
isolation holds across system calls.

The problem set has two purposes. First, it shows one way to model
a real system -- it’s much more like seL4 than like mergesort.
Second, we delve deeper into the standard library. Most large Coq
developments use complex data structures like finite maps; we do
too. *)


(** ** Memory

A _memory_ is a partial function from addresses to “byte” values (we use
[nat] because why not). An address is a [nat]; a value is an [option nat],
where [None] indicates unmapped memory. We use the [memory] type to
represent both process memory and the ramdisk. *)

Section Memory.

  (** We represent a memory as a function. *)
  Definition memory : Set := nat -> option nat.


  Implicit Types m : memory.
  Implicit Types addr len : nat.
  Implicit Types vs : list nat.

  (** The empty memory *)
  Definition memnil : memory :=
    fun a => None.

  (** Returns [True] iff the [len] addresses starting at [addr] are all
      mapped. *)
  Definition memmapped m addr len : Prop :=
    forall i, i < len -> m (addr + i) <> None.


  (** These functions create a new memory based on [m]. *)

  (** Add new values [vs] to [m], starting at [addr]. *)
  Definition memmap m addr vs : memory :=
    fun a =>
      if (addr <=? a) && (a <? addr + length vs)
      then nth_error vs (a - addr)
      else m a.

  (** Remove the addresses from [addr] to [addr + len - 1] in [m]. *)
  Definition memunmap m addr len : memory :=
    fun a =>
      if (addr <=? a) && (a <? addr + len)
      then None
      else m a.


  (** This function returns a [list] containing the [len] bytes starting
      at [addr] in [m].  If _any_ of the bytes are unmapped, it should
      return [None]. *)
  Fixpoint memrange m addr len : option (list nat) :=
    (* YOUR CODE HERE *)
    None.

  (* Test out your code with some [Example]s! *)
End Memory.


(** As always, we need a few more facts about lists. *)

Section ListFacts.
  Context {A:Type}.
  Implicit Types l:list A.

  Lemma filter_app (f:A -> bool) l1 l2:
    filter f (l1 ++ l2) = filter f l1 ++ filter f l2.
  Proof.
    (* YOUR CODE HERE *)
  Admitted.

  Lemma Forall_app (P:A -> Prop) l1 l2:
    Forall P (l1 ++ l2) <-> Forall P l1 /\ Forall P l2.
  Proof.
    (* YOUR CODE HERE *)
  Admitted.
End ListFacts.


(** ** Process definitions

Main definitions:

- [process]: The internal configuration of a process, including
  its memory, its current execution mode, and what system call
  it’s executing (if any).

- [event]: A history variable that records execution steps for
  proofs.

- [procview]: A process’s view of the system. Comprises a
  [process], the kernel’s ramdisk, and a trace (a list of
  [event]s).

- [procstep1]: The transition relation for [procview]s. *)

Section Process.

  (** A [process] is computing on its current memory ([PComp]),
      blocked in a system call ([PSys]), or dead ([PDead]).
      The system-call constructor [PSys] also specifies the system
      call name and arguments. Not all arguments are used for all
      system calls. *)

  Inductive syscall : Set := Map | Unmap | Read | Write | Kill.

  Inductive process : Set :=
  | PComp: forall (pm:memory), process
  | PSys: forall (pm:memory) (sysc:syscall) (addr len offset:nat), process
  | PDead.


  Inductive event : Set :=
  | EC (* Computation event *)
  | ES (* system call Start event *)
  | ER (* system call Return event *)
  | EK (* system call in-Kernel event *)
  | EKW: forall (offset len:nat), event
       (* system call in-Kernel Write event: records what offsets written *)
  | ED. (* Die event *)

  (** Is event [e] not a write? *)
  Definition event_nonwrite e : Prop :=
    match e with
    | EKW _ _ => False
    | _ => True
    end.

  (** Is event [e] not an in-kernel event? *)
  Definition event_nonkernel e : Prop :=
    match e with
    | EK => False
    | EKW _ _ => False
    | _ => True
    end.


  Inductive procview : Set :=
  | PS: forall (p:process) (km:memory) (tr:list event), procview.


  (** The [procstep1 : procview -> procview -> Prop] relation
      determines how the OS works. The basic ideas are that processes
      alternate between computing and system calls, and that system
      calls execute one byte at a time.

      - [PS_compute]: A computing process can change its memory (but
        it can only change memory that is already mapped).
      - [PS_syscall]: A computing process can make a new system call.
      - [PS_sysdone]: When a system call is done, the process starts
        computing again.
      - [PS_kill]: A process can be killed at any time.

      Then there are four constructors to execute the four system
      calls. The system calls take the same arguments: [addr] is an
      address in the process’s memory, [len] is a number of bytes,
      and [offset] (not always used) is an offset into the ramdisk.

      - [Map addr len]: Like malloc or mmap: adds [len] bytes to this
        process’s address space. The new bytes are zeroed out.
      - [Unmap addr len]: Like munmap: removes [len] bytes from this
        process’s address space.
      - [Read addr len offset]: Reads [len] bytes from the ramdisk
        starting at [offset].
      - [Write addr len offset]: Writes [len] bytes to the ramdisk
        starting at [offset].

      The [Read] and [Write] system calls require that the relevant
      part of the process’s memory is mapped.

      Each step records its function in the [procview]’s [tr] trace
      history variable. *)

  Inductive procstep1 : relation procview :=
  | PS_compute: forall pm km tr addr vs,
      memmapped pm addr (length vs) ->
      procstep1 (PS (PComp pm) km tr)
                (PS (PComp (memmap pm addr vs)) km (tr ++ [EC]))
  | PS_syscall: forall pm km tr sysc addr len offset,
      procstep1 (PS (PComp pm) km tr)
                (PS (PSys pm sysc addr len offset) km (tr ++ [ES]))
  | PS_sysdone: forall pm km tr sysc addr offset,
      procstep1 (PS (PSys pm sysc addr 0 offset) km tr)
                (PS (PComp pm) km (tr ++ [ER]))
  | PS_map: forall pm km tr addr len offset,
      procstep1 (PS (PSys pm Map addr (S len) offset) km tr)
                (PS (PSys (memmap pm addr [0]) Map (S addr) len (S offset))
                    km (tr ++ [EK]))
  | PS_unmap: forall pm km tr addr len offset,
      procstep1 (PS (PSys pm Unmap addr (S len) offset) km tr)
                (PS (PSys (memunmap pm addr 1) Unmap (S addr) len (S offset))
                    km (tr ++ [EK]))
  | PS_read: forall pm km tr addr len offset v,
      km offset = Some v ->
      procstep1 (PS (PSys pm Read addr (S len) offset) km tr)
                (PS (PSys (memmap pm addr [v]) Read (S addr) len (S offset))
                    km (tr ++ [EK]))
  | PS_write: forall pm km tr addr len offset v,
      pm addr = Some v ->
      memmapped km offset 1 ->
      procstep1 (PS (PSys pm Write addr (S len) offset) km tr)
                (PS (PSys pm Write (S addr) len (S offset))
                    (memmap km offset [v]) (tr ++ [EKW offset 1]))
  | PS_kill: forall p km tr,
      procstep1 (PS p km tr)
                (PS PDead km (tr ++ [ED])).

  (** [procsteps : procview -> procview -> Prop] is the reflexive,
      transitive closure of [procstep1]. So [procsteps a b] holds if
      there is some chain [a0, a1, a2, ..., an] of zero or more steps,
      so that [a0 = a], [an = b], and
      [forall i, i < n -> procstep1 ai a{i+1}].

      [clos_refl_trans_n1] is defined in Coq’s standard library. *)

  Definition procsteps := clos_refl_trans_n1 procview procstep1.

End Process.


(** ** Finite maps

We now examine Coq’s [FMap] module, which defines a dictionary-like data type.

[FMap] functions are defined in the [FMapInterface] module, which also has
many lemmas. Many other lemmas are defined in [FMapFacts].

[FMap]s are instantiated in three steps. First, we choose an underlying
representation, such as an AVL tree. We, though, use sorted lists, via
the [FMapList] type, since they print nicer.

Second, we provide the type of keys, which must be an ordered type.
This gives us a new module specialized for a kind of key. For example:
<<
  Module NatMap := FMapList.Make Nat_as_OT.
>>
Now [NatMap] defines [FMap] types, functions, and lemmas specialized
for [nat] keys. ([Nat_as_OT] is defined in the Coq library.) We can refer
to those types, functions, and lemmas as [NatMap.whatever].

Finally, we provide the type of values, which can be anything.
<<
  Definition Map_from_nat_to_bool := NatMap.t bool.
  Definition an_empty_map := NatMap.empty bool.
>>
Now [Map_from_nat_to_bool] is a map type. Its representation is hidden,
meaning you can only access its contents via [FMap] functions and lemmas
(and things you build on top).

The most important [Map] accessors are as follows. In the below, [key]
is the map’s key type, [elt] is its value type, and [t elt] is the map
type. In arguments, [x] and [y] are keys, [e] and [e'] are values, and
[m] and [m'] are maps.

- [Map.empty elt] is an empty map storing [elt] values.
- [Map.add x e m: t elt] sets [x]’s value to [e] in [m]. Coq is functional,
  of course, so this involves making a copy of [m].
- [Map.find x m: option elt] returns [x]’s value in [m], if it exists.
- [Map.In x m: Prop] is [True] iff [x] has a value in [m].
- [Map.MapsTo x e m: Prop] is [True] iff [x]’s value in [m] is [e].

Three lemmas in [Map] show how [MapsTo] and [add] relate. [add_1] is about
the value of the added key, [add_2] and [add_3] are about other keys.
These lemmas are use [E.eq] to test keys for equality; for [nat]s, [E.eq]
is just [=].
<<
  Lemma Map.add_1 (x y:key) (e:elt) (m:t elt) :
     E.eq x y -> Map.MapsTo y e (Map.add x e m).
  Lemma Map.add_2 (x y:key) (e e':elt) (m:t elt) :
     ~ E.eq x y -> Map.MapsTo y e m -> Map.MapsTo y e (Map.add x e' m).
  Lemma Map.add_3 (x y:key) (e e':elt) (m:t elt) :
     ~ E.eq x y -> Map.MapsTo y e (Map.add x e' m) -> Map.MapsTo y e m.
>>

Then there are some useful lemmas in [MapFacts]. [add_mapsto_iff]
completely specifies the behavior of [Map.add]; it’s like a combination
of [add_1], [add_2], and [add_3].
<<
  Lemma MapFacts.add_mapsto_iff (m:t elt) (x y:key) (e e':elt) :
    Map.MapsTo y e' (Map.add x e m) <->
      (E.eq x y /\ e = e') \/
      (~ E.eq x y /\ Map.MapsTo y e' m).
>>

[MapsTo_fun] says that [MapsTo] is a (partial) function: if the
same key maps to two different values, then those values are equal.
<<
  Lemma MapFacts.MapsTo_fun (m:t elt) (x:key) (e e':elt) :
    Map.MapsTo x e m -> Map.MapsTo x e' m -> e = e'.
>>

And there are others, such as [add_in_iff].


*** The problem of equality

Maps (and other complicated data structures) force us to think more
carefully about equality. Intuitively, we think two maps are equal if
they contain the same elements. This is captured by the [Map.Equal]
relation:

<<
  Definition Map.Equal m m' := forall x, Map.find x m = Map.find x m'.
>>

Unfortunately, it is _not_ true that [Map.Equal m m' -> m = m'].
“Different” [Map]s, in terms of Leibniz equality (Coq’s primitive
equality), can have the same contents. For example, the [Map]s might
be balanced trees with different layouts. :(

This makes life more difficult! It’s very nice to use [rewrite]
tactics, and usually [rewrite] requires Leibniz equality.

To use [rewrite] on [Map]s, or data types containing [Map]s, we must
provide separate lemmas showing that rewriting in specific situations
is OK. We’ll see some such lemmas below. But the Coq library already
provides many of these lemmas for [Map] operations, so this proof
works:

<<
  Lemma MapsTo_Equal x e m m':
    Map.Equal m m' ->
    Map.MapsTo x e m ->
    Map.MapsTo x e m'.

    intros EQ H. now rewrite <- EQ.
  Qed.
>>

The [rewrite] succeeds because the Coq library has proved that
[Equal] [Map]s can be substituted inside a [MapsTo]’s arguments.

A useful fact about [Equal]:

<<
  Lemma MapFacts.Equal_mapsto_iff m m':
    Equal m m' <-> (forall x e, MapsTo x e m <-> MapsTo x e m').
>>


*** Your work

Get started by proving some useful facts about [Map]s in general. We
start a new module for these facts, called [WXFacts_fun].

*)

Module WXFacts_fun (E:DecidableType) (Import Map:FMapInterface.WSfun E).
Module MapFacts := FMapFacts.WFacts_fun E Map.
Section XFacts.
  Notation eq_dec := E.eq_dec.
  Variable elt: Type.
  Implicit Types m: t elt.
  Implicit Types x y z: key.
  Implicit Types e: elt.

  (** A map doesn’t change if you [add] the same element to it. *)
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

  (** Now you prove this: [add]ing an element overrides the previous
      element at that key. *)
  Lemma add_redundant_Equal: forall m x e e',
      Equal (add x e m) (add x e (add x e' m)).
  Proof.
    (* YOUR CODE HERE *)
  Admitted.
End XFacts.
End WXFacts_fun.

(** Our [Map]s have [nat] as keys. We instantiate the three useful modules:
    the [Map] itself, its [Facts], and its [XFacts] (that we just wrote). *)
Module NatMap := FMapList.Make Nat_as_OT.
Module NatMapFacts := FMapFacts.WFacts_fun Nat_as_OT NatMap.
Module NatMapXFacts := WXFacts_fun Nat_as_OT NatMap.



(** ** Operating system view

An [osview] is the analogy to [procview], but for the whole operating system,
not just a single process. An [osview] contains a [NatMap] of [process]es,
mapped by process ID; a ramdisk; and a trace history variable, where this time
each trace element is a pair of process ID and event.

Since [osview]s contain [Map]s, Leibniz equality isn’t the right notion of
equality. We provide our own equality definition, prove that it is reflexive,
symmetric, and transitive, and finally show that it is an equivalence relation,
allowing it to be used by tactics like [reflexivity], [symmetry], and
[transitivity]. *)

Section OSView.

  Definition processes := NatMap.t process.

  Definition trace := list (nat * event).

  Inductive osview :=
  | OS: forall (ps:processes) (km:memory) (tr:trace), osview.

  Definition osv_ps os := match os with OS ps _ _ => ps end.
  Definition osv_km os := match os with OS _ km _ => km end.
  Definition osv_tr os := match os with OS _ _ tr => tr end.


  Definition osv_equal os1 os2 :=
    match os1, os2 with
    | OS ps1 km1 tr1, OS ps2 km2 tr2 =>
      NatMap.Equal ps1 ps2 /\ km1 = km2 /\ tr1 = tr2
    end.

  Global Instance osv_equal_refl : Reflexive osv_equal.
    intro os1. (* unpack the [Reflexive] definition *)
    destruct os1; simpl; intuition.
  Qed.

  Global Instance osv_equal_sym : Symmetric osv_equal.
    intros os1 os2.
    destruct os1, os2; simpl; intuition.
  Qed.

  Global Instance osv_equal_trans : Transitive osv_equal.
    intros os1 os2 os3.
    destruct os1, os2, os3; simpl; intros; destruct_conjs; repeat split.
    - now transitivity ps0.
    - now subst.
    - now subst.
  Qed.

  Global Instance : Equivalence osv_equal.
    split;
    [ apply osv_equal_refl | apply osv_equal_sym | apply osv_equal_trans ].
  Qed.

End OSView.



(** ** Trace facts

Some helper functions and lemmas about traces. *)

Section TraceFacts.
  Implicit Types tr:trace.
  Implicit Types pid:nat.

  (** Returns a trace that _only_ contains events from process [pid]. *)
  Definition trace_filter_pid pid tr : trace :=
    filter (fun pr => fst pr =? pid) tr.

  (** Returns a trace that _strips out_ events from process [pid]. *)
  Definition trace_remove_pid pid tr : trace :=
    filter (fun pr => negb (fst pr =? pid)) tr.

  (** [True] iff none of the events in [tr] are kernel writes. *)
  Definition trace_nowrites tr : Prop :=
    Forall event_nonwrite (map snd tr).


  Lemma trace_filter_pid_app pid tr1 tr2:
    trace_filter_pid pid (tr1 ++ tr2) =
    trace_filter_pid pid tr1 ++ trace_filter_pid pid tr2.
  Proof.
    (* YOUR CODE HERE -- remember ListFacts above! *)
  Admitted.

  Lemma trace_remove_pid_app pid tr1 tr2:
    trace_remove_pid pid (tr1 ++ tr2) =
    trace_remove_pid pid tr1 ++ trace_remove_pid pid tr2.
  Proof.
    (* YOUR CODE HERE *)
  Admitted.

  Lemma trace_nowrites_app tr1 tr2:
    trace_nowrites (tr1 ++ tr2) <-> trace_nowrites tr1 /\ trace_nowrites tr2.
  Proof.
    (* YOUR CODE HERE *)
  Admitted.


  (** These lemmas relate the [trace_filter_pid] and [trace_remove_pid]
      operations to [map]s over event lists. *)
  Lemma trace_filter_pid_map_eq pid es:
    trace_filter_pid pid (map (pair pid) es) = map (pair pid) es.
  Proof.
    (* YOUR CODE HERE *)
  Admitted.

  Lemma trace_filter_pid_map_neq pid pid':
    pid <> pid' ->
    forall es, trace_filter_pid pid (map (pair pid') es) = [].
  Proof.
    (* YOUR CODE HERE *)
  Admitted.

  Lemma trace_remove_pid_map_neq pid pid':
    pid <> pid' ->
    forall es, trace_remove_pid pid (map (pair pid') es) = map (pair pid') es.
  Proof.
    (* YOUR CODE HERE *)
  Admitted.

End TraceFacts.


(** ** Operating system step relation

We are now ready to state the [osstep1 : osview -> osview -> Prop]
step relation: the OS as a whole takes a step when one of its component
processes takes a step. And we define [ossteps], which is the reflexive,
transitive closure of [osstep1].

Issues involving equality affect both of these definitions. In [OS_step],
we don’t require that the new OS contain _exactly_ [NatMap.add pid p' ps];
instead, we require that it contain some _equivalent_ process map.
Similarly, the [os_refl] rule applies to _equivalent_ OSs, not merely
_equal_ ones. *)

Section OSStep.

  Inductive osstep1 : relation osview :=
  | OS_step : forall ps km tr ps' km' tr' pid p p',
      NatMap.MapsTo pid p ps ->
      procstep1 (PS p km []) (PS p' km' tr') ->
      NatMap.Equal ps' (NatMap.add pid p' ps) ->
      osstep1 (OS ps km tr)
              (OS ps' km' (tr ++ (map (pair pid) tr'))).

  Inductive ossteps : relation osview :=
  | os_refl: forall os1 os2,
      osv_equal os1 os2 ->
      ossteps os1 os2
  | os_trans: forall os1 os2 os3,
      ossteps os1 os2 ->
      osstep1 os2 os3 ->
      ossteps os1 os3.

End OSStep.


(** ** Rewriting for [osstep1] and [ossteps]

In this section you prove that [osstep1] and [ossteps] hold true up to
the [osv_equal] equivalence relation. This lets us show the [Proper]
instances that will let us [rewrite] the arguments of [osstep1] and
[ossteps]. *)

Section OSStepRewriting.

  Lemma osstep1_equal os1 os1' os2 os2':
    osv_equal os1 os1' ->
    osv_equal os2 os2' ->
    osstep1 os1 os2 ->
    osstep1 os1' os2'.
  Proof.
    (* YOUR CODE HERE *)
  Admitted.

  Global Instance: Proper (osv_equal ==> osv_equal ==> iff) osstep1.
  Proof.
    intros os1 os1' H1 os2 os2' H2.
    split; intros.
    - now apply osstep1_equal with (os1:=os1) (os2:=os2).
    - apply osstep1_equal with (os1:=os1') (os2:=os2'); intuition.
  Qed.


  Lemma ossteps_equal os1 os1' os2 os2':
    osv_equal os1 os1' ->
    osv_equal os2 os2' ->
    ossteps os1 os2 ->
    ossteps os1' os2'.
  Proof.
    (* YOUR CODE HERE *)
  Admitted.

  Global Instance: Proper (osv_equal ==> osv_equal ==> iff) ossteps.
  Proof.
    intros os1 os1' H1 os2 os2' H2.
    split; intros.
    - now apply ossteps_equal with (os1:=os1) (os2:=os2).
    - now apply ossteps_equal with (os1:=os1') (os2:=os2').
  Qed.

End OSStepRewriting.


(** ** Process isolation

You’re finally there: you’re going to prove two process isolation lemmas.

The first theorem, [process_isolation], says that if a process takes no steps
in some trace, then that process’s internal state remains unchanged.

The second theorem, [write_isolation], says that for processes only communicate
through [Write]s to the ramdisk. Specifically, we consider a trace in which
no process but [p] writes to the ramdisk. Given that trace, we show that
[p] could take the exact same steps, with the same results, in a different
trace where _no other process takes any steps at all_.

You can imagine many other theorems. For example, [read_isolation] would show
that if a process performs no [Read]s from the ramdisk, then it could take
the same steps in a different trace where no other process takes steps.
Or [reverse_write_isolation] would show that _adding_ non-write actions to a
trace containing [p] won’t affect [p]’s actions. *)

Section ProcessIsolation.

  (* Helper lemma: processes never disappear. *)
  Lemma ossteps_In_ps pid os1 os2:
    NatMap.In pid (osv_ps os1) ->
    ossteps os1 os2 ->
    NatMap.In pid (osv_ps os2).
  Proof.
    (* YOUR CODE HERE *)
  Admitted.


  Theorem process_isolation os1 os2 pid p:
    ossteps os1 os2 ->
    NatMap.MapsTo pid p (osv_ps os1) ->
    osv_tr os1 = [] ->
    ~ In pid (map fst (osv_tr os2)) ->
    NatMap.MapsTo pid p (osv_ps os2).
  Proof.
    (* YOUR CODE HERE *)
  Admitted.


  Theorem write_isolation os1 os2 pid p p':
    ossteps os1 os2 ->
    NatMap.MapsTo pid p (osv_ps os1) ->
    NatMap.MapsTo pid p' (osv_ps os2) ->
    osv_tr os1 = [] ->
    trace_nowrites (trace_remove_pid pid (osv_tr os2)) ->
    ossteps os1 (OS (NatMap.add pid p' (osv_ps os1))
                    (osv_km os2)
                    (trace_filter_pid pid (osv_tr os2))).
  Proof.
    (* YOUR CODE HERE *)
  Admitted.

End ProcessIsolation.
