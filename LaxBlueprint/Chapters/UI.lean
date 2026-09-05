import Verso
import VersoManual
import VersoBlueprint
import LaxLogic.PLLCraig

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Towards uniform interpolation" =>

The aim, in one line: for every PLL formula `φ` and variable `p` there are
`p`-free formulas `∃p.φ` and `∀p.φ` in Pitts's sense.

This chapter is a *live* campaign, not a finished result, and it is
deliberately written to say which parts are proved, which are stopped, and
where exactly the obstruction sits.  Its source is
`docs/ui-routeB-blueprint.md`, which is the maintained node table; this
chapter is the reader's view of it and will drift unless kept in step.

A note on method, since it explains what is and is not attached below.
Route (B) is moving week by week, so nodes here carry `(lean := "...")`
only where the declaration is settled.  Where a statement is still drafted
or carries a `sorry`, the node is prose: attaching a name that is about to
change would break the build for no gain.

# Craig interpolation

:::group "craig"
The proved starting point.  Uniform interpolation strengthens this to an
interpolant depending only on the antecedent and the shared variables.
:::

:::theorem "maehara" (parent := "craig") (lean := "PLLND.SC.maehara")
TODO — Maehara's method on the cut-free sequent calculus.
:::

:::theorem "craig" (parent := "craig") (lean := "PLLND.craig_interpolation")
TODO — Craig interpolation for PLL, from {uses "maehara"}[].
:::

:::theorem "craig_imp" (parent := "craig") (lean := "PLLND.craig_implication")
TODO — the implication form.
:::

# Route (B): the fuel-founded retention interpolant

:::group "routeB"
LJF◯'s `interpF` computes two chains: `E_f` descending from `⊤` and `A_f`
ascending from `⊥`.  If both stabilise, the cell has uniform interpolants.
Stabilisation everywhere is the open theorem.
:::

:::definition "interpF" (parent := "routeB")
TODO — `LJFO.interpF` (`LJF/OFuel.lean`), the retention interpolant at a
given fuel.  `E_f := interpF p f [] done none` and
`A_f := interpF p f [] done (some G)`.
:::

:::theorem "n0a_soundness" (parent := "routeB")
N0a — *soundness at every fuel*.  `LJFO.eSoundF` and `LJFO.aSoundF`
(`LJF/OFuelSound.lean`).  Recorded as PROVED in the node table.

CHECK OUTSTANDING: the table records the axioms as
`[propext, Quot.sound]`, but neither declaration carries a `#print axioms`
pin, and no pin for them was found elsewhere.  Under the standing rule that
`#print axioms` is the only recognised checker, this is asserted rather than
verified.  Adding the pins is a small job and would settle it.
:::

:::theorem "n0h_heights" (parent := "routeB")
N0h — *height bounds* for every derivation transformer, the Step-0 table,
with `LJFO.laxReleaseUp` and `LJFO.laxReleaseCirc`
(`LJF/OFuelHeight.lean`, 844 lines).  PROVED, same pin caveat as
{uses "n0a_soundness"}[].
:::

:::theorem "n0b_rows" (parent := "routeB")
N0b — row equations at fuel, the processing phase `eMinFF`/`aMinFF`, and
the reductions.  `LJFO.SatE2F`, `LJFO.SatA2F` and
`LJFO.cimpAntF_of_satA2F` are in `LJF/OFuelMin.lean`; note that
`ecofinalF_of_satE2F` and `acofinalF_of_satA2F` are currently in
`wip/ui_routeB_statements.lean`, not where the node table says.
Depends on {uses "n0a_soundness"}[].
:::

# Where it is stopped

:::proposition "n0c_cofinality" (parent := "routeB")
N0c — *cofinality at a saturated station*: every sufficient `p`-free
formula is reached at some fuel.  **STOPPED TWICE, and the obstruction is
exact**, which is worth more than a vague "hard": there is no station-first
order (§4.11), and no height-first order on {uses "interpF"}[] either,
because the three reshaping processing clauses raise height (§4.13).

This is the node the whole route waits on.  Depends on
{uses "n0a_soundness"}[], {uses "n0b_rows"}[] and {uses "n0e_parking"}[].
:::

:::definition "n0e_parking" (parent := "routeB")
N0e — the **parking definition** `interpP`: park `(Q₁∨Q₂) ⊃ N`,
`↓↑P′ ⊃ N` and `↓(M₁∧M₂) ⊃ N`, one retained-guard row each, then found
{uses "n0c_cofinality"}[] on `(height, weight)`.  The governing principle
is no rewriting of hypotheses, and every non-atomic implication firing
through a retained guard; the soundness pair comes first.

DECIDED 2026-09-05, IN BUILD.  Depends on {uses "n0h_heights"}[].
:::

# The chain to uniform interpolation

:::group "chain"
Statements drafted, proofs open.  These are stated in
`wip/ui_routeB_blueprint.lean`.
:::

:::definition "n1_stabilises" (parent := "chain")
N1 — `EStabilises` and `AStabilises`: the chains eventually constant, the
`A`-side modulo `E_f`.  DRAFTED.
:::

:::definition "n2_uipair" (parent := "chain")
N2 — `IsUIPair` and `HasUI`: Pitts's pair for a cell, stated intrinsically
rather than via the construction.  DRAFTED.
:::

:::theorem "n3_equivalence" (parent := "chain")
N3 — **stabilisation ⟺ uniform interpolation, per cell**, given
{uses "n0a_soundness"}[] and N0d.  This is the conceptual heart: it turns
an open question about interpolants into an open question about chains.
DRAFTED, carries a `sorry`.  Depends on {uses "n1_stabilises"}[] and
{uses "n2_uipair"}[].
:::

:::theorem "n4_stabilisation_all" (parent := "chain")
N4 — `StabilisationAll`: every saturated cell stabilises.  **OPEN BOTH
WAYS** — neither proved nor refuted, with a `sorry` placeholder.  This is
THE open theorem of the route.
:::

:::theorem "n5_ljfo_ui" (parent := "chain")
N5 — uniform interpolation for LJF◯, from {uses "n3_equivalence"}[] and
{uses "n4_stabilisation_all"}[].  DRAFTED, `sorry`.
:::

:::theorem "n6_transport" (parent := "chain")
N6 — transport to PLL along the bridge: `PLL_UI := ∀ p φ, Σ E A,
IsUIPairPLL p φ E A`.  DRAFTED, `sorry`.  Depends on
{uses "n5_ljfo_ui"}[] and {uses "n0b_rows"}[].
:::
