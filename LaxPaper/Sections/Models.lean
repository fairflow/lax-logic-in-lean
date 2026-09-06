import Verso
import VersoManual
import VersoBlueprint
import LaxLogic.Obligation
import LaxLogic.Obligation.Budget

open Verso.Genre
open Verso.Genre.Manual
open Informal
open LaxLogic.Obligation

#doc (Manual) "Constraint models" =>

A constraint model fixes what a constraint _is_: the witness type, and how two
constraints combine.  The modality and every tactic above are independent of
that choice, so the development carries several models side by side, one per
module, and the case studies say which they are using.

# Timing: lower bounds on a clock

The model the modality was invented for.  The witness type is a clock and a
constraint is a lower bound: `◯∀[from_ a] P` reads "`P` holds from time `a`
onwards".

:::group "models"
The models.
:::

:::definition "from_" (parent := "models") (uses := "laxall") (lean := "Timing.from_")
Availability from a time onwards.
:::

The content of the model is that the two constraint operations specialise to the
two operations of timing analysis:

:::theorem "meet_lower" (parent := "models") (uses := "from_, laxall_meet") (lean := "Timing.meet_lowerBound")
Combining constraints on a shared witness is `max` — parallel join.  The reason
it is `max` and not `min` is that the constraints are lower bounds and they are
conjoined: to have both signals you must wait for the later one.
:::

:::theorem "image_delay" (parent := "models") (uses := "from_, laxall_image") (lean := "Timing.image_delay")
Propagating a constraint through a component of delay `d` shifts the bound by
`d` — sequential composition.
:::

:::theorem "pipeline" (parent := "models") (uses := "meet_lower, image_delay") (lean := "Timing.pipeline")
The two rules together, which is the original paper's introductory example in
general form: two components available from `a` and `b` feed a third that needs
both and adds `d`, giving `max a b + d`.
:::

That example is reproduced literally, data-dependent bound and all.  The paper's
three component specifications are

```
ψ₁ = ∀s.       (s ≥ 5)      ⊃ P₁ a s
ψ₂ = ∀s,y.     (s ≥ 9 - y)  ⊃ P₂ (f y) s
ψ₃ = ∀t,y₁,y₂. (∃s. t ≥ s+35 ∧ P₁ y₁ s ∧ P₂ y₂ s) ⊃ Q (g y₁ y₂) t
```

and the derived availability of the result is `max 5 (9 - a) + 35`.  Two things
survive that a coarser encoding would lose: the second component's bound depends
on a _value_, and the conclusion is about a _computed_ value `g y₁ y₂`.  The
constraint arithmetic is independent of the value arithmetic, which is the
separation the original paper's Fig. 1 draws.

# Resource budgets: costs that add

Nothing forced the timing reading.  `Budget.lean` instantiates the same
machinery where the witness is a resource budget, and the difference is not the
shape of one constraint but how two combine:

:::definition "atLeast" (parent := "models") (uses := "laxall") (lean := "Budget.atLeast")
A budget covering a cost.  Formally identical to `from_`.
:::

:::theorem "budget_combine" (parent := "models") (uses := "atLeast, laxall_image") (lean := "Budget.combine")
Two components drawn from **separate** pools cost the sum.  This is the case the
timing reading never produces, and it is the paper's `⊃_◯` at the direct image
along addition.
:::

:::theorem "budget_share" (parent := "models") (uses := "atLeast, laxall_meet") (lean := "Budget.share")
Two components sharing **one** pool cost the max — which is the timing rule, so
the timing model is the shared-resource case.
:::

The area of a prefix adder is a real constraint that the delay analysis of the
next section cannot see:

:::definition "treeGates" (parent := "models") (lean := "Budget.treeGates")
Merge cells in a balanced prefix tree of depth `k`, by the recursion the tree is
built on.
:::

:::theorem "treeGates_eq" (parent := "models") (uses := "treeGates") (lean := "Budget.treeGates_eq")
`treeGates k = 2ᵏ - 1`.
:::

:::theorem "tree32_fits" (parent := "models") (uses := "treeGates_eq, atLeast, postpone, solvefor") (lean := "Budget.tree32_fits")
The 32-bit block's thirty-one cells fit a forty-cell budget — discharged from a
synthesised obligation, not an assumed one.
:::

:::theorem "tree32_too_big" (parent := "models") (uses := "treeGates_eq, postpone") (lean := "Budget.tree32_too_big")
And do not fit thirty: refuted, not unproved.
:::

Because the additive constraints contain no `max`, they are certified without
`Classical.choice`, unlike the timing ones.  Having both models in one
repository is what makes that contrast checkable rather than asserted.

# Obligations proper: the one-point clock

A proof obligation is a timing constraint on a clock with one tick.  There is
nothing to schedule, so a constraint is just a proposition and `max`
degenerates to conjunction:

:::theorem "meet_unit" (parent := "models") (uses := "debt") (lean := "Timing.meet_unit")
On a one-point clock, parallel composition is conjunction.
:::

That is `Debt`, and it is why the same two rules — combine, propagate — do all
the work in the tactic.

# Mendler's `(Ω*, [], @)`

Mendler's thesis takes a constraint to be a _list_ of propositions, applied by
iterated implication, with the empty list as unit and append as composition.
That is exactly the shape `postponing theorem` produces, and the ledger is the
list.

:::theorem "weak_singleton" (parent := "models") (uses := "weak, debt") (lean := "weak_singleton")
A one-element constraint is `Debt`.
:::

:::theorem "laxAll_as_weak" (parent := "models") (uses := "weak, laxall") (lean := "laxAll_as_weak")
And `◯∀` is `weak` read pointwise.
:::

Two remarks from the thesis explain why the Lean rendering is smaller than
either source.  Mendler notes that a higher-order object language would make the
refinement type `|M|` depend on the formula substituted for a propositional
variable, "whence `|M|` would be a dependent type", and that adding dependent
types to both logics is "a major complication that we want to avoid".  Lean's
base logic is dependently typed, so the complication is simply absent.  He also
notes that intuitionism is load-bearing: it is what lets constraint information
be extracted from derivations as ordinary lambda terms.  The same point appears
here as the observation that classically `A` modulo `C` collapses to `A ∨ ¬C`
and the debt evaporates.

# Standard constraints, and the two units

The Curry's-problem paper's standard constraints are lists of _pairs_, applied
as a conjunction of clauses `Kᵢ ⊃ (x ∨ Lᵢ)`.  These are not Mendler's lists, and
the difference is not cosmetic: their units sit at opposite ends.  Mendler's
`[]` is no weakening at all; theirs is total weakening.  Both land in `Debt`, at
different combinations of the atomic constraints:

:::theorem "weak_debt" (parent := "models") (uses := "weak, debt") (lean := "StdCtxBridge.weak_iff_debt_allOf")
Mendler's constraint is `Debt` at the **conjunction** of its demands.
:::

:::theorem "applyP_bot" (parent := "models") (uses := "debt") (lean := "StdCtxBridge.applyP_bot_iff")
A standard constraint with every escape `⊥` is `Debt` at the **disjunction** of
its preconditions, because a conjunction of clauses `Kᵢ ⊃ x` is discharged by
any one of the `Kᵢ`.
:::

# The object logic

Finally, the readings above are models of the repository's own natural deduction
system for propositional lax logic, not merely analogies to it.

:::theorem "sound" (parent := "models") (uses := "debt") (lean := "PLLBridge.sound")
`Debt C` is a sound interpretation of `◯`, by structural induction: the two lax
rules are the unit and the bind of `Debt` and nothing else.  This depends on no
axioms.
:::

The interpretation uses one constraint for every occurrence of `◯`, which
collapses iterated modalities.  Above `Prop` it should not collapse, and does
not: under the writer reading of the same repository, `◯φ` is a pair of a
constraint and a value, `◯◯φ` carries two constraints, and the multiplication
that combines them is not injective — how the constraint was apportioned between
the two modalities is destroyed.  For the timing reading that apportionment is
the point, since `1 then 2` and `3 then 0` are different schedules with the same
total.
