Require Import Arith.
Require Import Omega.
Require Import Recdef.
Require Import List.
Require Import Program.Tactics.
Require Import Relation_Operators.

Section ForwardSimulation.

  (* S is the type of a specification. *)
  Variable S:Type.

  (* I is the type of an implementation state. *)
  Variable I:Type.

  (* This function takes a single deterministic step on an
     implementation state. *)
  Variable istep:I -> I.

  (* This relation represents a nondeterministic step on the
     specification. *)
  Variable sstep:S -> S -> Prop.

  (* This relation says whether an implementation state matches a
     specification. *)
  Variable ispec:I -> S -> Prop.


  (* Kleene-star on `istep`: `isteps i i'` is True iff you can get
     from i to i' in zero or more `istep`s. *)
  Inductive isteps: I -> I -> Prop :=
  | isteps_refl: forall i, isteps i i
  | isteps_cons: forall i i', isteps i i' -> isteps i (istep i').

  (* Kleene-star on `sstep`: `ssteps s s'` is True iff you can get
     from s to s' in zero or more `sstep`s. *)
  Inductive ssteps: S -> S -> Prop :=
  | ssteps_refl: forall s, ssteps s s
  | ssteps_cons: forall a b c, ssteps a b -> sstep b c -> ssteps a c.


  (* Prove this lemma. *)
  Lemma ssteps_trans (a b c:S):
    ssteps a b -> ssteps b c -> ssteps a c.
    (* YOUR CODE HERE *)
  Admitted.


  (* Now, *state* the definition of forward simulation.

     There are many forward simulation definitions. The one we want is
     that single deterministic implementation steps are matched by
     zero or more specification steps.

     So `PS`, a Prop over specifications, is a forward simulation iff:

     1. For every specification `s` that fits `PS` (i.e. `PS s` is
        True),
     2. And every implementation `i` that maps to `s` under
        `ispec`,
     3. When implementation `i` takes a step via `istep`,
     4. That next implementation maps to some specification `s'` that
        also fits `PS`. *)

  Definition ForwardSimulation (PS:S -> Prop) :=
    forall ... (* YOUR CODE HERE! *)

  Hint Unfold ForwardSimulation.
  

  (* Now, state and prove this lemma, which says that forward
     simulation is preserved over MULTIPLE implementation steps
     (isteps rather than istep). *)
  Lemma ForwardSimulation_star
        (PS:S -> Prop)
        (fsim:ForwardSimulation PS)
        (* YOUR CODE HERE! *)

End ForwardSimulation.
