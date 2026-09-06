import Verso
import VersoManual
import VersoBlueprint
import LaxLogic.Obligation

open Verso.Genre
open Verso.Genre.Manual
open Informal
open LaxLogic.Obligation

#doc (Manual) "Case study: two adders" =>

The repository already contained two adders, built on the _other_ modality.
Under the `◯∃` reading a proof term is evaluated in a writer monad over the
delay monoid, so evaluating it **returns** a delay alongside the value; that is
how the ripple-carry and carry-lookahead comparisons were originally done.
Running the same two circuits through the `◯∀` side turns the delay into the
constraint the claim is weakened by, and gives three things the writer reading
cannot express.

# One cell, two shapes, one theorem

The carry cell is the timing pipeline rule applied once.  The ripple chain and
the balanced prefix fold are then the _same_ induction over it, which mirrors
the object logic, where the two folds inhabit one sequent and differ only in
associativity.

:::group "adders"
The adders.
:::

:::definition "CellSpec" (parent := "adders") (lean := "Adder.CellSpec")
A two-input cell of delay `δ`, specified functionally with no times mentioned.
:::

:::theorem "carry_cell" (parent := "adders") (uses := "CellSpec, pipeline") (lean := "Adder.carry_cell")
Availability composes as `max` then `+ δ`.
:::

:::theorem "chain_ready" (parent := "adders") (uses := "carry_cell") (lean := "Adder.chain_ready")
Linear carry delay `n·δ`, by induction on the width — one carry cell per step.
:::

:::theorem "bal_ready" (parent := "adders") (uses := "carry_cell") (lean := "Adder.bal_ready")
Depth-`k` availability `k·δ` for the balanced fold, whatever the leaf count.  At
`k := 2ᵏ - 1` the same theorem gives the ripple-shaped fold of `2ᵏ` leaves.
:::

# The two readings agree

This one was not forced by anything.  The bound in the `◯∀` statement is the
number the `◯∃` extractor computes off the object-logic proof term; the two meet
only because both are the same recurrence.

:::theorem "ripple_is_extracted" (parent := "adders") (uses := "chain_ready") (lean := "Adder.ripple_is_extracted")
The ripple's obligation bound is the delay extracted from its proof term.
:::

:::theorem "bal_is_extracted" (parent := "adders") (uses := "bal_ready") (lean := "Adder.bal_is_extracted")
And likewise for the balanced fold.
:::

# Which design is the easier obligation

`◯∀` is antitone in the constraint, so a later availability is a stronger
demand.  "The design got faster" is movement along that order, and the order is
Heyting entailment in the pointwise algebra.

:::theorem "lookahead_weaker" (parent := "adders") (uses := "from_") (lean := "Adder.lookahead_strictly_weaker")
The ripple's availability constraint entails the lookahead's, and not
conversely.
:::

# The design question becomes an obligation

"Does the carry make the sampling edge at `T`?" is one application of the
antitonicity rule away from the availability theorem, and its side condition is
the timing constraint.  Written with `postpone`, the statement carries no timing
hypothesis:

:::theorem "ripple_meets_cycle" (parent := "adders") (uses := "chain_ready, laxall_mono, postpone, reduceAtRecord") (lean := "Adder.ripple_meets_cycle")
The ripple adder meets the cycle, modulo one recorded obligation.
:::

:::theorem "bal_meets_cycle" (parent := "adders") (uses := "bal_ready, laxall_mono, postpone, reduceAtRecord") (lean := "Adder.bal_meets_cycle")
The balanced fold likewise: same derivation, same cell, different depth.
:::

The solver reduces both to `n·δ ≤ T` and `k·δ ≤ T`.  Neither right-hand side is
written anywhere in the source.  Note also what they do not mention: the
functional layer.  The constraint is independent of it, which is the separation
of concerns falling out rather than being imposed — and it is why the refutation
below holds for every instance at once.

# The loop closes

Nominal sky130 numbers, `120 ps` per cell, a 32-bit add in a `1 ns` cycle.

:::theorem "ripple32_false" (parent := "adders") (uses := "ripple_meets_cycle") (lean := "Adder.ripple32_obligation_false")
**Refuted**, not unproved: `32 · 120 = 3840 > 1000`, for every instantiation of
the functional layer.
:::

The response is to restructure.  The balanced fold over the same thirty-two
leaves uses the same thirty-one merge cells re-associated, and the two folds are
already known to compute the same group generate/propagate pair, so the
re-association is sound rather than a change of specification.

:::theorem "lookahead32_holds" (parent := "adders") (uses := "bal_meets_cycle") (lean := "Adder.lookahead32_obligation_holds")
Depth five at `120 ps` is `600 ps`, inside the cycle.
:::

:::theorem "closes" (parent := "adders") (uses := "ripple32_false, lookahead32_holds") (lean := "Adder.restructuring_closes_the_loop")
Synthesise, refute, restructure, discharge — with the availability the
specification asked for at the end of it.  The constraint chose the
architecture.
:::

What the delay comparison does not see is area, and that is the point of having
a second constraint model: the balanced tree is the more expensive network per
unit depth, and its area obligation is synthesised by the same pipeline over a
different monoid.
