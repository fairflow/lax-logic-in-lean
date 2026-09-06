import Verso
import VersoManual
import VersoBlueprint
import LaxLogic.Obligation

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Case study: a modular datapath" =>

The latch and the adders each synthesise the constraints of one circuit.  This
example is about the step after: building a second proof on top of the first
_while its constraint is still outstanding_, so that the composite's constraint
is computed rather than restated.

# Three stages

Each stage uses the previous holed theorem as an ordinary lemma, through
`lax_apply`.

:::group "pipe"
The datapath.
:::

:::definition "UnitSpec" (parent := "pipe") (lean := "LaxLogic.Obligation.Modular.UnitSpec")
A one-input cell.  Without it, a buffer has to be written as a two-input cell
fed twice, and every downstream constraint carries a `max a a`.
:::

:::theorem "buffer" (parent := "pipe") (uses := "UnitSpec, from_") (lean := "LaxLogic.Obligation.Modular.buffer")
The one-input refinement rule: availability shifts by the delay.
:::

:::theorem "datapath" (parent := "pipe") (uses := "bal_meets_cycle, carry_cell, postpone") (lean := "LaxLogic.Obligation.Modular.datapath_meets_clock")
Stage 2, the carry-lookahead block plus its sum XOR.  Two obligations: the
block's, borrowed, and the XOR's, new.
:::

:::theorem "pipeline_thm" (parent := "pipe") (uses := "datapath, buffer, postpone") (lean := "LaxLogic.Obligation.Modular.pipeline_meets_clock")
Stage 3, plus an output buffer.  Three obligations: two inherited — one of which
the datapath had itself inherited — and one new.
:::

# Folding back

The finished statement _is_ Mendler's `weak` at the concatenated ledger; the
fold-back is not a further construction but what `postponing theorem` already
produced.

:::theorem "is_weak" (parent := "pipe") (uses := "pipeline_thm, weak") (lean := "LaxLogic.Obligation.Modular.pipeline_is_weak")
The statement as `weak [C₁,C₂,C₃] φ`, with the theorem itself as the proof.
:::

:::theorem "ledger_append" (parent := "pipe") (uses := "weak_append") (lean := "LaxLogic.Obligation.Modular.pipeline_ledger_append")
And the monoid law on it: the ledger of a modular proof is the concatenation of
the ledgers.
:::

Currying the list gives the single implication, which the solver emits:

```
pipeline_meets_clock_debt :
  ∀ Gp Pb Sum Q δ δsum δbuf T tp Tclk Tout k, …
    Debt (k * δ ≤ T ∧ (T + δsum ≤ Tclk ∧ tp + δsum ≤ Tclk) ∧ Tclk + δbuf ≤ Tout)
         (◯∀[from_ Tout] Q)
```

Every conjunct was derived; none appears in the source.  Getting from there to
the fully concrete statement is a `simp only` over three definitions — `Debt`,
`LaxAll` and `from_` — and nothing else, because `Debt` is an abbreviation
rather than a structure:

:::theorem "expanded" (parent := "pipe") (uses := "debt") (lean := "LaxLogic.Obligation.Modular.pipeline_debt_expanded")
The `C ⊃ φ` form and its base-logic expansion are the same proposition, by
`lax_refine` alone.
:::

# Discharging at a constraint model

Fix the delays and the deadline and the whole set becomes decidable arithmetic —
**one** `omega`, not one per constraint, because the fold presents it as a single
conjunction.  Merge `120 ps` over a depth-5 tree, local propagate at `200`, sum
XOR `60`, output buffer `90`, internal deadline `700`, output deadline `1 ns`:

:::theorem "concrete" (parent := "pipe") (uses := "pipeline_thm, solvefor") (lean := "LaxLogic.Obligation.Modular.pipeline_concrete")
The concrete theorem, obtained from the abstract one by evaluation.  No timing
hypothesis survives.
:::

:::theorem "too_tight" (parent := "pipe") (uses := "pipeline_thm") (lean := "LaxLogic.Obligation.Modular.pipeline_too_tight")
At a `750 ps` deadline the buffer's constraint is false.  The model decides the
design in both directions.
:::

# The earliest schedule

The internal times are not really inputs.  They are scheduling choices, and the
natural one makes each signal available as early as the derivation allows.
Instantiating there satisfies every internal constraint by reflexivity and
collapses the set to a single inequality on the leaf delays and the deadline —
which is what static timing analysis reports.

:::theorem "earliest" (parent := "pipe") (uses := "pipeline_thm") (lean := "LaxLogic.Obligation.Modular.pipeline_earliest")
The whole constraint set at the earliest schedule is
`max (k·δ) tp + δsum + δbuf ≤ Tout`.
:::
