Naïve Coq
=========

Overview
--------

| WHEN YOU WANT                           | USE        |
| --------------------------------------- | ---------- |
| simple case analysis                    | `destruct` |
| smart case analysis on complex objects  | `inversion_clear` |
| inductive case analysis                 | `induction` |
| simultaneous induction                  | `induction x, y` |
| a more general inductive hypothesis     | `generalize; induction` |
| inductive case analysis on a `Function` body | `functional induction` |
| Coq to do something obvious             | `auto`, `omega` |
| to expand a function body               | `simpl`, `unfold` |
| to expand a `Function` body             | `rewrite [functionname]_equation` |
| to rewrite using equality               | `rewrite H` |
| an obvious contradiction                | `contradiction` |
| a contradiction about different constructors     | `discriminate`  |
| to go from a theorem’s conclusion to its premise | `apply`         |
| to go from a theorem’s premise to its conclusion | `apply in H`    |
| a new hypothesis                        | `pose`, `assert` |
| a new name for an expression            | `remember`       |
| to work with `A /\ B`                   | `split` (goal), `destruct` (hypothesis) |
| to work with `A \/ B`                   | `left`, `right` (goal), `destruct` (hypothesis) |
| to show `exists x, P`                   | `exists p`       |
| the same thing in every subgoal         | `tactic1; tactic2` |
| different things in diffent subgoals    | `[ tactic1 | tactic2 | ... ]` |
| suppressed tactic errors                | `...; try tactic; ...` |


Introduction tactics: adding hypotheses
---------------------------------------

These tactics add new hypotheses.

### `pose (expression)`

This adds a new hypothesis defined by `expression`, which might be an
already-defined theorem (e.g., `pose le_S_n`, `pose (le_S_n 2 3)`) or a
version of an existing hypothesis (e.g., `pose (IHx 0)`). `pose (expression)
as Hname` gives the new hypothesis a specific name.

### `assert (expression)`

Pause the current proof and start a new subgoal of proving `expression`.

### `assert (expression) by tactic`

Add `expression` as a hypothesis, but only if it can be proved by `tactic`.

### `remember (expression) as x`

Adds a new variable `x` and a hypothesis `x = expression`, then rewrites
everything else to use `x` instead of `expression`. Useful to simplify
arguments for tactics such as functional induction.

> Note that some people think good Coq style requires minimizing hypotheses,
> so you should only introduce facts by applying them to existing hypotheses
> or goals. I think this is too strict.


Destructive tactics: destruction, induction, inversion
------------------------------------------------------

Every object of an inductive type `T` was created by one of `T`’s
constructors. A `nat` was created by either `O` or `S`, a `bool` was created
by either `false` or `true`, and so forth.

The *destructive tactics* break a proof into cases by generating one case per
constructor. Destructive tactics usually create subgoals. They are either
simple (they don’t generate inductive hypotheses) or inductive (they do).

### `destruct x`: simple

Replaces `x` with one subgoal per `x` constructor.

### `destruct H`: simple

Replaces `H` with one subgoal per `H` constructor.

### `destruct (expression)`: simple

Adds one subgoal per constructor of the expression, possibly including new
hypotheses. Example: `destruct (eq_nat_dec n m)`.

`destruct` can lose context. For example, `destruct (S n)` generates an
impossible case (the one where `(S n) = O`), but also drops the context
required to prove the case impossible. Other destructive tactics are less
stupid. `destruct` is best on simple objects, like pure variables.

### `destruct_pairs`: simple

Separate all logical-and hyptheses into their component parts. Never loses
context. Needs `Require Import Program.Tactics`.

### `inversion_clear H`: simple

Replaces `H` with one subgoal per `H` constructor, *and* generates additional
constraints based on arguments to `H`, *and* eliminates impossible cases,
*and* cleans up redundant hypotheses.

`inversion_clear` is useful when `destruct` loses too much context.

### `inversion H`: simple

Like `inversion_clear`, but preserves possibly-redundant hypotheses.

### Example: Simple destructive tactic comparison

Here we try to prove a basic fact about `cons`. Note how the different tactics
behave:

```
Coq < Lemma cons_eq {A} (a b:A) x y:
Coq <     a :: x = b :: y -> a = b.
Coq < Proof. intros.

1 subgoal, subgoal 1 (ID 748)

  A : Type
  n, m : A
  p, q : list A
  H : n :: p = m :: q
  ============================
  p = q

Coq < destruct H. (* loses context *)

1 subgoal, subgoal 1 (ID 757)

  A : Type
  n, m : A
  p, q : list A
  ============================
  p = q

Coq < Restart. intros; inversion H. (* keeps context, redundancy *)

1 subgoal, subgoal 1 (ID 774)

  A : Type
  n, m : A
  p, q : list A
  H : n :: p = m :: q
  H1 : n = m
  H2 : p = q
  ============================
  q = q

Coq < Restart. intros; inversion_clear H. (* keeps context, less redundancy *)

  A : Type
  n, m : A
  p, q : list A
  ============================
  q = q
```

### `induction x`: inductive

Adds one subgoal per `x` constructor, with inductive hypotheses when
appropriate. You can induct over hypotheses too.

### `induction x, y`: inductive

Simultaneous induction on `x` and `y`. This is often preferred to `induction
x; induction y`, which performs a *separate* induction on `y` for *each*
inductive case on `x`. In simultaneous induction, the inductive hypotheses are
over *both* `x` and `y`; in separate induction, `y`’s inductive hypothesis
will assume a specific `x`.

### `functional induction (f arg...)`: inductive

Adds one subgoal per case in the definition of `f`, which must have been
defined by `Function`. Works best if the `arg`s are simple variables; if
they’re not, it can lose context. Use `remember` to avoid this.

`rewrite f_equation` is useful for functional induction.

### `generalize x`

Replaces a goal that refers to a specific variable, `x`, with `forall x,
[goal]`. Use this when applying an induction tactic gives you an inductive
hypothesis that’s too specific.


Applicative tactics
-------------------

These tactics work with implications: statements of the form `P -> Q`. This
includes certain inductive constructors; for instance, the type of the
natural-number successor operation `S` is `nat -> nat`.

### `apply H`, `apply Theorem`, `apply (expression)`

Matches the goal with the conclusion of the implication, and replaces it with
the premise. For instance, given the goal `S (a + b) > S x`, `apply gt_n_S`
will create the new goal `a + b > x`. May generate new subgoals for new
dependencies.

### `apply ... with (var:=expr)`

Sometimes Coq can’t figure out how to apply an implication. Help it by giving
more hypotheses or by assigning values to specific variables. This often
occurs with transitivity. For instance:

```
Coq < Check gt_trans.

gt_trans
     : forall n m p : nat, n > m -> m > p -> n > p

Coq < Lemma gt_trans_Snp x y z: S x > y -> y > S z -> S x > S z.
Coq < intros. apply gt_trans.

Error: Unable to find an instance for the variable m.

Coq < apply (gt_trans (S x) y z).         (* works *)
Coq < apply gt_trans with (m:=y).         (* also works *)
Coq < apply (gt_trans _ _ _ (S x > y)).   (* also works *)
```

### `apply ... in H`

Applies an implication in a hypothesis rather than the goal. This works in the
other direction—it matches the *premise* of the implication against the
hypothesis, and replaces the hypothesis with the *conclusion*.


Existence tactics
-----------------

These tactics are useful when you’re trying to prove that something exists.
They are really forms of `apply`, specialized for inductive types. The goal
states the something exists; the tactics replace that goal with the premises
for one of the corresponding constructors.

These tactics are typically used for propositions rather than objects, since a
proof goal rarely has the form “a list exists.” They do not apply to
hypotheses: you can’t say `split in H`. In hypotheses, use a destructive
tactic instead. (For instance, to split apart a hypothesis `H : A /\ B` or `H
: A \/ B`, you usually want `destruct H`.)

### `split`

`split` is typically used for logical-and goals, but works for all goals with
single-constructor types. It just applies the single constructor. `split`
never loses context.

> Explanation: Every object witnesses its type, and constructors let us make
> new objects from old ones. In Coq, the goal `A /\ B` (or, equivalently, `and
> A B`) means “there exists an object of type `and A B`.” Since that inductive
> type has one constructor, `conj` (of type `A -> B -> and A B`), that object,
> if it exists, must have been constructed by that constructor. As soon as we
> have an `A` and a `B` (that is, witnesses for those types), we can create an
> `A /\ B` by applying `conj`. The `split` tactic implements this logic: it
> replaces a `A /\ B` goal with its requirements, `A` and `B`.

### `left` and `right`

`left` and `right` are typically used for logical-or goals, but work for all
goals with two-constructor types. `left` applies the first constructor and
`right` applies the second one. This can lose context, so make sure you pick
the right one.

### `exists`

`exists p` is typically used for existence goals (like `exists p, p = 5`), but
works for all goals with single-constructor types. It applies the single
constructor with argument `p`. For instance, `exists p, p = 5` can be proved
by `exists (2 * 2 + 1); auto`.

### `constructor`

More generally, `constructor` applies the first constructor that matches the
goal. If more than one constructor matches, `constructor` can lose context.
Use `constructor N` to apply the `N`th constructor specifically. Use
`constructor ... with (var:=value)` if the constructor can’t figure out values
for some variables.


Completion tactics
------------------

These tactics solve a goal.

### `auto` (fail-free)

Solve an “obvious” system. “Obvious” means Coq searches for a solution by
simplifying expressions, rewriting equalities, finding contradictions, etc.,
but not for very long. Give a number, such as `auto 10`, to tell Coq to look a
little harder.

If `auto` can’t solve the current subgoal, it does nothing.

### `omega`

Solve a system by arithmetic or fail. You may prefer `try omega`.

### `contradiction`

Solve a system with transparently contradictory hypotheses (e.g., `False`, `~
True`) or fail. You may prefer `try contradiction`.

### `discriminate H`

Solve a system by contradiction, given an absurd hypothesis `H` that equates
different constructors of the same type (e.g., `S n = 0`).

### `reflexivity`

Solve a system whose goal is a reflexive equality (e.g., `x = x`). `auto` is
better.


Simplification tactics
----------------------

These tactics simplify expressions by rewriting function calls.

### `simpl in *` (fail-free)

Simplify all function calls that can be simplified. To localize the tactic’s
effects, Use `simpl` (goal only), `simpl in H` (hypothesis `H` only), `simpl
functionname` (`functionname` only), `simpl functionname at N [in H]` (only
the `N`th occurrence of `functionname`).

### `unfold functionname in *`

Replace a function call with the function’s body. Use `unfold functionname` or
`unfold functionname in H` to localize effects.

### `fold functionname in *`

Replace a function’s body with a call. This is the inverse of `unfold
functionname in *`.

### `rewrite <functionname>_equation in *`

The `simpl` and `unfold` tactics don’t work well on recursive functions
defined by `Function`. Use this instead; it rewrites a function call with the
function’s body.


Tactics that use equivalence
----------------------------

These tactics rewrite expressions using equivalence facts, either primitive
equality (`x = y`) or if-and-only-if propositions (`A <-> B`).

### `rewrite H in *`

`H` should be an equality or equivalence. This replaces all occurrences of the
left-hand side of the equality with the right-hand side.

### `rewrite <- H in *`

Same, but replaces occurrences of the right-hand side with the left-hand side.



Meta-tactics
------------

### `idtac`

No-op tactic.

### `fail`

Always fail.

### `try tactic`

Try `tactic`, but do nothing if it fails.

### `tactic1; tactic2`

Do `tactic1`, and if it succeeds, apply `tactic2` to every generated subgoal.

### `[ tactic1 | tactic2 | ... | tacticN ]`

Requires that there are `N` active subgoals. Applies `tacticI` to the `I`th
subgoal.

### `repeat tactic`

Do `tactic` until it fails.
