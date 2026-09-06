import Verso
import VersoManual
import VersoBlueprint
import LaxLogic.Obligation

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Computing the reduced constraint" =>

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

# The normaliser is not verified, and does not need to be

`Solve.lean` computes the right-hand side by ordinary metaprogramming over
`Expr`.  It is a _search_ device in the sense this repository already uses for
proof and countermodel discovery: it proposes the reduced form, and `omega`
certifies the resulting equivalence against the kernel.  A bug in the
normaliser cannot produce an unsound theorem.  It can only produce one `omega`
refuses to prove, which is a build failure.

Two hazards were guarded explicitly.  Generated theorems go through the ordinary
`theorem` elaborator rather than `addDecl`, whose `addAsAxiom` fallback
silently axiomatises anything that fails to check; and each result is then
confirmed to be a theorem before the command returns.

# It runs by itself

A command the author has to invoke is still a place where the author supplies
something.  `postponing theorem` therefore runs the solver as each declaration
is recorded, through a hook that is inert unless the solver module is imported.
The reduced forms and the `C ⊃ φ` fold are output, not input:

:::group "solve"
The solver and the tactics around it.
:::

:::definition "normmp" (parent := "solve") (lean := "LaxLogic.Obligation.Solve.normMP")
Normalise a `(max, +)` expression to a max of sums.
:::

:::definition "solvedform" (parent := "solve") (lean := "LaxLogic.Obligation.Solve.solvedForm")
The solved form of one obligation, or nothing if it is outside the fragment.
:::

:::definition "solvefor" (parent := "solve") (lean := "LaxLogic.Obligation.Solve.solveFor")
Solve and fold the obligations of a declaration.  Called by the
`solve_obligations` command and by `postponing theorem` itself.
:::

For a declaration `d` this emits `d.obligationᵢ_solved` for each obligation —
including ones `lax_apply` borrowed transitively — and `d_debt`, the single
implication over the whole computed constraint set.

# Outside the fragment

The latch's second obligation is `∀t₁ ≥ tₐ + D₁. t₁ < t₁ + D₂ + D₁`, whose
bound mentions the quantified time on both sides.  That is outside the fragment,
the solver says so in a warning, and leaves the obligation unreduced — it still
appears in the `Debt` fold, so the statement stays true and the gap is visible
rather than silent.  Its reduced form, `0 < D₂ + D₁`, remains hand-written and
`omega`-proved, and is the one place in the case studies where a right-hand side
is still supplied by a person.

# The two remaining tactics

:::definition "reduce_obligation" (parent := "solve") (lean := "LaxLogic.Obligation.reduceObligationTac")
The (8) to (9) step as a tactic, for the cases a person states by hand.
:::

:::definition "discharge_obligation" (parent := "solve") (lean := "LaxLogic.Obligation.dischargeObligationTac")
Close a constraint once the delays and the deadline are fixed, so the concrete
theorem follows from the abstract one by evaluation.
:::

In practice the `Debt` fold makes the second largely unnecessary: because the
whole constraint set is presented as one conjunction, a single `omega` closes
it at a model.

# Where `Classical.choice` enters

`omega` normalises `max` through a classical case split.  So a constraint
arising from a `meet` — a parallel join, the only source of `max` in this
calculus — is certified with `Classical.choice`, and one that is not stays at
`propext` and `Quot.sound`.  Both cases are pinned side by side in the
development.  This is a property of the certifying tactic, not of the
mathematics: `Nat.max_le` is `[propext]`, so a certificate built from
`Nat.le_max_left` and `Nat.add_le_add_right` instead of `omega` would be clean.
It is recorded as owed work rather than absorbed.
