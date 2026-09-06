import Verso
import VersoManual
import VersoBlueprint
import LaxLogic.Obligation

open Verso.Genre
open Verso.Genre.Manual
open Informal
open LaxLogic.Obligation

#doc (Manual) "Computing the reduced constraint" =>

Where the original paper says "given such reasoning is built into constraint
reductions" and prints the answer. Here the reduction is three rewrite lemmas,
and it runs at the moment the obligation is recorded.

# What the original leaves to the reader

In the latch analysis of the original paper, the synthesised constraint at
equation (8) is

```
∀t₁ ≥ tₐ + D₁. ∃m₁₁ ≥ sₐ. m₁₁ + 2d₁ + d₂ ≤ t₁  ∧  D₂ + D₁ > 0
```

and the paper then says:

> the condition `∀t₁ ≥ tₐ + D₁. ∃m₁₁ ≥ sₐ. m₁₁ + 2d₁ + d₂ ≤ t₁` is logically
> equivalent to `tₐ + D₁ ≥ sₐ + 2d₁ + d₂`.  Given such reasoning is built into
> constraint reductions, we are looking at the solution form …

before printing equation (9).  That sentence is where the method stops being
mechanical.  Everything up to it is derivation; the step itself is arithmetic
performed by the authors and asserted to be automatable.

# The fragment

It is automatable, and the reason is that the modality's rules can only build
constraints of one shape.  Every constraint this library synthesises has the
form

```
∀ z, A ≤ z → e ≤ z
```

with `e` built from atoms by `+` and `max` — those two and no others, because
`meet` and `image` are the only combinators the rules introduce, and on lower
bounds they are exactly `max` and `+`.  Over that signature the reduction is
forced:

1. the quantifier goes by instantiating at its own bound, giving `e ≤ A`;
2. `+` distributes over `max`, so `e` normalises to a **max of sums**;
3. `max` splits on the left of `≤`.

So the solved form of any such constraint is a **conjunction of linear
inequalities**, one per timing path.  That is not merely a tidier form; it is
what static timing analysis wants, and it is finer than what a person writing
the answer by hand would usually bother with.  The datapath's second obligation
comes out as

```
T + δsum ≤ Tclk  ∧  tp + δsum ≤ Tclk
```

naming the two paths separately, where the hand-written version said
`max T tp + δsum ≤ Tclk`.

# The reduction is three rewrite lemmas

There is no normaliser.  The three steps above are three theorems, and the
solved form is computed by rewriting with them:

:::group "solve"
The solver and the tactics around it.
:::

:::definition "oblIff" (parent := "solve") (lean := "Solve.oblIff")
The (8) to (9) step: a constraint universally quantified over a time, with a
lower bound as its hypothesis, is the bound instantiated at itself.  Depends on
no axioms.
:::

:::definition "distrR" (parent := "solve") (uses := "oblIff") (lean := "Solve.distrR")
`+` distributes over `max` on the right.
:::

:::definition "distrL" (parent := "solve") (uses := "oblIff") (lean := "Solve.distrL")
And on the left.
:::

# The right-hand side is computed, not written

`simp only` with those lemmas rewrites the left of `ty ↔ ?rhs`, and `Iff.rfl`
assigns the **metavariable** on the right to whatever came out.  Nothing states
the answer, and nothing unverified is trusted: the lemmas are theorems, so the
equivalence is kernel-checked by construction.

:::definition "reduceIff" (parent := "solve") (uses := "oblIff, distrR, distrL") (lean := "Solve.reduceIff")
Compute the solved form into a metavariable, with the equivalence that certifies
it.
:::

The two passes are not cosmetic.  `simp` rewrites innermost-first, so splitting
the `max` before instantiating the quantifier would destroy the pattern the
first lemma matches.

# When the solving happens

At the moment the obligation is recorded, not afterwards.  That is the
difference between the solved form being an extra theorem about the obligation
and the solved form *being* the obligation:

:::definition "reduceAtRecord" (parent := "solve") (uses := "reduceIff, postpone") (lean := "Solve.reduceAtRecord")
The reducer `postpone` calls as it records — the solved proposition, and a proof
that it implies the goal.
:::

So `#obligations` prints `n * δ ≤ T`, the finished statement quantifies over
`n * δ ≤ T`, and unfolding the obligation constant gives `n * δ ≤ T`.  A
borrowed obligation is left verbatim, which costs nothing, because the callee's
obligation was itself solved when *it* was recorded.

:::definition "solvefor" (parent := "solve") (uses := "reduceAtRecord, debt") (lean := "Solve.solveFor")
What still runs afterwards: the fold of a declaration's obligations into the
single implication `C ⊃ φ`.
:::

# No `Classical.choice`

An earlier version certified with `omega`, which normalises `max` by a classical
case split, so every constraint arising from a parallel join carried
`Classical.choice`.  The three lemmas are `[propext]` at worst, so the reduced
constraints are clean and the contrast that used to be recorded here has gone
with its cause.

What remains is a different job: *discharging* a whole constraint set at a
model is still one call to `omega`, and where that goal contains a `max` the
classical split is still there.  That is a general-purpose decision procedure
applied to concrete arithmetic, not part of the mechanism, and it is pinned
where it occurs.

# Outside the fragment

The latch's second obligation is `∀t₁ ≥ tₐ + D₁. t₁ < t₁ + D₂ + D₁`, whose
bound mentions the quantified time on both sides.  That is outside the fragment,
the solver says so in a warning, and leaves the obligation unreduced — it still
appears in the `Debt` fold, so the statement stays true and the gap is visible
rather than silent.  Its reduced form, `0 < D₂ + D₁`, remains hand-written and
`omega`-proved, and is the one place in the case studies where a right-hand side
is still supplied by a person.

# The two remaining tactics

:::definition "reduce_obligation" (parent := "solve") (uses := "oblIff") (lean := "reduceObligationTac")
The (8) to (9) step as a tactic, for the cases a person states by hand.
:::

:::definition "discharge_obligation" (parent := "solve") (uses := "solvefor") (lean := "dischargeObligationTac")
Close a constraint once the delays and the deadline are fixed, so the concrete
theorem follows from the abstract one by evaluation.
:::

In practice the `Debt` fold makes the second largely unnecessary: because the
whole constraint set is presented as one conjunction, a single `omega` closes it
at a model.
