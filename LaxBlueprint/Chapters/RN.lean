import Verso
import VersoManual
import VersoBlueprint
import wip.rnClassify
import wip.gapWidth

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "The RN(◯,∅) lattice" =>

`RN(◯,∅)` is the Rieger–Nishimura lattice of the one-variable fragment
carried over to PLL: the `◯`-and-`⊥` formulas in a single variable, ordered
by derivability and taken up to interderivability.  It is small enough to
draw, which is the point of it — the whole ordering fits on a page, and
questions intractable in general become finite computations here.

Two abbreviations run through everything below:

$$`a := ◯⊥ \qquad b := ◯¬◯⊥ \;\; (= ◯¬a)`

The data behind the diagram is a 462-cell matrix over PLL: the `⊬` side is
kernel-pinned by certificates, the `⊢` side engine-certified, and the scoped
Hasse diagram has 37 cover edges.  Sources are `RNDB/`,
`docs/rho-structure.md` and `docs/rho-order.md`; the conjectures recorded
alongside the regularities there are deliberately not repeated here.

# The shape of the order

:::group "rn_shape"
Four verified regularities, all certificate-backed.
:::

:::proposition "rn_graded" (parent := "rn_shape")
*Graded.*  Every cover edge spans exactly one rank.  The rank profile is
`1-2-2-3-5-5-3-1`, so the height is 7.

TO WRITE — whether to show the Hasse diagram inline.  It exists as
`docs/rho-hasse-pll.svg` and carries far more than the profile does.
:::

:::proposition "rn_irreducibles" (parent := "rn_shape")
*Lower-cover join-generation, in the poset sense.*  Every join-reducible
node is the poset least upper bound of its own lower covers, and there are
ten poset-join-irreducibles: $`⊥`, $`a`, $`¬a`, $`¬¬a`, $`b`, and
$`ρ_{12}`, $`ρ_{13}`, $`ρ_{14}`, $`ρ_{19}`, $`ρ_{20}`.  Every one of them
except the rails' atoms is an implication.

The distinction a first reading gets wrong, and which the source document
corrects explicitly: the poset least upper bound is *weaker* than the class
of the syntactic join.  Whether a node is interderivable with the join of
its lower covers is a separate question at each node.  It is certified at
$`ρ_{10}`, $`ρ_{15}` and $`ρ_{18}`, and open at three frontier cells.
:::

:::proposition "rn_cubes" (parent := "rn_shape")
*Two stacked cubes.*  The interval $`[ρ_4, ρ_{18}]` is exactly $`2^3` on the
atoms $`ρ_6`, $`ρ_7`, $`ρ_{14}`, and its identities are certified as *class*
identities rather than merely poset ones.  A dual cube sits over $`ρ_9` on
$`ρ_{12}`, $`ρ_{18}`, $`ρ_{20}`; three of its four vertices are new classes
and the fourth is open.
:::

:::proposition "rn_two_generators" (parent := "rn_shape")
*A two-generator presentation.*  Every one of the 22 representatives is a
Heyting-algebra term over $`a` and $`b` alone: *exactly two
`◯`-applications occur in the entire catalogue*, namely $`◯⊥` and
$`◯¬◯⊥`.

This is what makes the lattice finite and drawable, and it is exactly what
fails on extension.  The q-dictionary's $`q_{12} = ◯ρ_6` and
$`q_{13} = ◯ρ_{11}` sit *outside* the catalogue: they are the first depth-2
`◯`-generators.  See {uses "rn_extension"}[].
:::

# What is proved

:::group "rn_proved"
The two headline results, both mechanised.
:::

:::theorem "rn_classification" (parent := "rn_proved") (lean := "PLLND.RNEmbed.rn_classification, PLLND.RNEmbed.image_classification")
*The classification.*  For every `◯`-free formula $`A` whose only variable
is $`p`, the substitution $`A[p := ◯⊥]` is interderivable either with some
rung of the ladder or with $`⊤`.  So the image of $`h` is the rungs
together with $`⊤`.

The method deserves recording, because it is reusable.  Classify
*semantically* first: a function computes the ladder truth set of $`A` by
structural recursion through three fully tabulated Heyting operations on
up-set codes.  Then *derive* each of the 48 table rows — each hard side a
short modus-ponens composition through the Rieger–Nishimura recursion, each
easy side rung order through the decision procedure.  Then glue by
congruence in the structural induction.

A consequence worth advertising ahead of the theorem itself: the
classification doubles as a *decision procedure for interderivability* on
the whole `◯`-free one-variable fragment.
:::

:::theorem "rn_complement_infinite" (parent := "rn_proved") (lean := "PLLND.RNEmbed.complement_infinite_final")
*The complement of the image is infinite*, with no caveat: the boxed odd
rungs are pairwise distinct and all lie off the image.  Depends on
{uses "rn_classification"}[].
:::

:::theorem "rn_width" (parent := "rn_proved") (lean := "PLLND.RNEmbed.width_infinite, PLLND.RNEmbed.gap_incomparable")
*`RN(◯,∅)` has unbounded width.*  The family
$$`\mathrm{gap}\,k \;:=\; ◯(\mathrm{rnSub}\,(2k{+}1)) ⊃ \mathrm{rnSub}\,(2k{+}1)`
generalises the dictionary class $`q_8` level by level — $`\mathrm{gap}\,1`
is $`q_8` — and for $`k ≥ 2` the $`\mathrm{gap}\,k` are pairwise
`⊬`-incomparable.  That is an $`ℕ`-indexed antichain, so the width question
is settled, and settled the interesting way: infinite, not bounded.

This is the result that makes the lattice worth studying rather than
tabulating, and a single new semantic computation carries it, on an edged
lift with one extra constraint edge.
:::

# The database

:::group "rn_db"
Why the catalogue is a database and not a table in a document.
:::

:::definition "rn_claim" (parent := "rn_db")
`Claim`, `Evidence`, `Entry` and `Frontier` (`RNDB/Types.lean`), with the
un-sorriable `ok` field: *an entry cannot record a claim it has no
evidence for.*  That is the design decision that makes a machine-maintained
catalogue trustworthy, and it is why the `⊬` side of the 462-cell matrix can
be relied on rather than spot-checked.

TO WRITE — a worked entry, shown whole.  One example will explain this
better than any description.
:::

:::definition "rn_order_def" (parent := "rn_db")
`Lt`, `Covers` and `CoversIn` (`RNDB/Order.lean`): the strict order and the
covering relation, the latter being what the Hasse diagram actually draws.

TO WRITE — why covering is computed rather than read off the order, and
what `CoversIn` scopes the covering to.
:::

:::definition "rn_engines" (parent := "rn_db")
`Engine` and `DerivRule`: which instrument settled each cell, kept in the
record so a later reader can re-run it rather than trust it.
:::

# The open direction

:::proposition "rn_extension" (parent := "rn_db")
OPEN — extension to more complex formulas.

{uses "rn_two_generators"}[] localises the obstruction exactly, and this is
not vagueness dressed as future work: the catalogue is closed under Heyting
operations over $`a` and $`b`, but $`q_{12} = ◯ρ_6` and
$`q_{13} = ◯ρ_{11}` are depth-2 `◯`-generators and leave it.  So the
question is not whether the lattice extends, but what the right generated
object is once a second `◯`-application is admitted.

TO WRITE — the two things that would turn this into a statement: what is
already known to survive at depth 2, and whether {uses "rn_width"}[]'s
antichain construction lifts.  Both are answerable from the existing
catalogue and `docs/rho-structure.md`; the work is to say it in a page.
:::
