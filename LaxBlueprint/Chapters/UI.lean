import Verso
import VersoManual
import VersoBlueprint
import LaxLogic.PLLCraig
import LJF.OFuelPCofinal

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Towards uniform interpolation" =>

The aim, in one line: for every PLL formula `φ` and variable `p` there are
`p`-free formulas `∃p.φ` and `∀p.φ` in Pitts's sense.

This chapter is a *live* campaign, not a finished result, and it is
deliberately written to say which parts are proved, which are stopped, and
where exactly the obstruction sits.  Its sources are
`docs/ui-routeB-blueprint.md`, the maintained node table, and
`docs/ui-ljfo-clause-table.md`, the running record — currently to §4.20.
This chapter is the reader's view of them and will drift unless kept in
step; it has twice been a day stale already.

As of §4.19 and §4.20 (2026-09-05) the shape is this: everything from N0a to
N3 is proved, N5 carries the last `sorry`, and *one* mathematical question is
open — {uses "n4_stabilisation_all"}[]. What is not proved elsewhere is
carried as a named obligation in a signature.

A note on method, since it explains what is and is not attached below.
Route (B) is moving week by week, so nodes here carry `(lean := "...")`
only where the declaration is settled.  Where a statement is still drafted
or carries a `sorry`, the node is prose: attaching a name that is about to
change would break the build for no gain.

The WP2 nodes below are the current exception, and for the stated reason:
`wip/ui_routeB_n3.lean` is proved and pinned, but N7 plans to hoist it out
of `wip/`, so its names are the ones about to change.

# Craig interpolation

:::group "craig"
The proved starting point.  Uniform interpolation strengthens this to an
interpolant depending only on the antecedent and the shared variables.
:::

:::theorem "maehara" (parent := "craig") (lean := "PLLND.SC.maehara")
TO WRITE — Maehara's method on the cut-free sequent calculus.
:::

:::theorem "craig" (parent := "craig") (lean := "PLLND.craig_interpolation")
TO WRITE — Craig interpolation for PLL, from {uses "maehara"}[].
:::

:::theorem "craig_imp" (parent := "craig") (lean := "PLLND.craig_implication")
TO WRITE — the implication form.
:::

# Route (B): the fuel-founded retention interpolant

:::group "routeB"
LJF◯'s `interpF` computes two chains: `E_f` descending from `⊤` and `A_f`
ascending from `⊥`.  If both stabilise, the cell has uniform interpolants.
Stabilisation everywhere is the open theorem.
:::

:::definition "interpF" (parent := "routeB")
TO WRITE — `LJFO.interpF` (`LJF/OFuel.lean`), the retention interpolant at a
given fuel.  `E_f := interpF p f [] done none` and
`A_f := interpF p f [] done (some G)`.
:::

:::theorem "n0a_soundness" (parent := "routeB")
N0a — *soundness at every fuel*.  `LJFO.eSoundF` and `LJFO.aSoundF`
(`LJF/OFuelSound.lean`), PROVED and pinned `[propext, Quot.sound]`.

The pin is verified rather than asserted: `LJF/OFuelSound.lean` closes with
`#axioms_within eSoundF [propext, Quot.sound]`, and the same for `aSoundF`,
`eSoundFWitness` and `aSoundFWitness`.  Why the set is this small is worth
recording — `Classical.choice` enters the *unfuelled* `eSound`/`aSound`
through the well-founded recursion on the todo/done measure, and the fuel
recursion does not use it.  Pinning tightly makes a regression that
re-introduces choice an error rather than a silent widening.
:::

:::theorem "n0h_heights" (parent := "routeB")
N0h — *height bounds* for every derivation transformer, the Step-0 table,
with `LJFO.laxReleaseUp` and `LJFO.laxReleaseCirc`
(`LJF/OFuelHeight.lean`, 1182 lines).  PROVED and pinned
`[propext, Quot.sound]` in `LJF/OAudit.lean`.

These two transformers were genuinely unpinned when this chapter was first
drafted — only their size lemmas `szI_laxReleaseUp` and `szI_laxReleaseCirc`
were — and the gap was closed on 2026-09-05 in answer to the note that stood
here.
:::

:::theorem "n0b_rows" (parent := "routeB")
N0b — row equations at fuel, the processing phase `eMinFF`/`aMinFF`, and
the reductions.  `LJFO.SatE2F`, `LJFO.SatA2F` and
`LJFO.cimpAntF_of_satA2F` are in `LJF/OFuelMin.lean`; note that
`ecofinalF_of_satE2F` and `acofinalF_of_satA2F` are currently in
`wip/ui_routeB_statements.lean`, not where the node table says.
Depends on {uses "n0a_soundness"}[].
:::

# The parking repair

:::theorem "n0c_cofinality" (parent := "routeB") (lean := "LJFO.tinvP, LJFO.uentryP, LJFO.parkAntP, LJFO.satE2P, LJFO.satA2P")
N0c — *cofinality at a saturated station*: every sufficient `p`-free formula
is reached at some fuel.  *PROVED, and unconditional*, over
{uses "n0e_parking"}[], pinned `[propext, Classical.choice, Quot.sound]`
(§4.17).  `tinvP`, `uentryP`, `parkAntP`, `satE2P`, `satA2P` — the
17-definition family in fuel-carrying form, as ONE `mutual` founded on
$`μ = (\mathrm{hgt}, \mathrm{weight}, \mathrm{sizeOf})`, across
`LJF/OFuelPFamKit.lean`, `LJF/OFuelPFam.lean` and `LJF/OFuelPCofinal.lean`.

The `Classical.choice` in that pin is *located*, not mysterious: WP1c
traced it to `atomMem_of_mem` in `LJF/O.lean`, a proof about string order,
and not to the recursion.  It will go when that lemma is reproved and not
before.

*Unconditional* is the word carrying the result.  The antecedent guard is a
native recursive call at all twenty parked arms, so `ParkAntP` is a
consequence of the construction rather than a hypothesis it must assume —
and `DykAntP`, the hypothesis an earlier draft needed, was WITHDRAWN on
2026-09-05 (§4.15–4.16).

The history is worth keeping, because it is what forced the parking
definition.  On `interpF` this family was *stopped twice*, and the
obstruction was located exactly rather than described as difficulty: there
is no station-first order (§4.11), and no height-first order either
(§4.13), because the three reshaping processing clauses raise height.
{uses "n0e_parking"}[] is the repair, not a workaround — and the repair
worked.

Depends on {uses "n0a_soundness"}[], {uses "n0b_rows"}[] and
{uses "n0e_parking"}[].
:::

:::theorem "n0d_cofinal" (parent := "routeB") (lean := "LJFO.ECofinalP, LJFO.ACofinalP, LJFO.ecofinalP, LJFO.acofinalP")
N0d — the cofinality statements themselves: `ECofinalP` and `ACofinalP`,
with their inhabitants `ecofinalP` and `acofinalP`
(`LJF/OFuelPCofinal.lean`).  *PROVED* for `interpP`, pinned
`[propext, Classical.choice, Quot.sound]` (§4.17).

The `interpF` forms — `ECofinalF`, `ACofinalF`, and the upward-closed
`ECofinalUp` and `ACofinalUp` — remain DRAFTED.  That asymmetry is the
present shape of the route: the parking interpolant carries the results, and
the original fuel interpolant is where they are still owed.

Depends on {uses "n0c_cofinality"}[].
:::

:::definition "n0e_parking" (parent := "routeB")
N0e — the *parking definition* `interpP`.  PROVED (§4.14).

Park $`(Q_1∨Q_2) ⊃ N`, $`↓↑P' ⊃ N` and $`↓(M_1∧M_2) ⊃ N`, one retained-guard
row each.  The governing principle is that no hypothesis is rewritten and
every non-atomic implication fires through a retained guard; the soundness
pair comes first, and `eSoundP`/`aSoundP` hold with the gate watched
failing.  The rows, the processing phase and the reductions are proved, and
so is the founding: under $`μ = (\mathrm{hgt}, \mathrm{weight},
\mathrm{sizeOf})` every edge class descends, including the antecedent
dispatch for all five parked shapes.  A kernel `decide` check confirms
`interpP = interpF` on a station without the changed shapes at fuels 0–8,
with negative controls.

Depends on {uses "n0h_heights"}[].
:::

# The chain to uniform interpolation

:::group "chain"
WP2, in `wip/ui_routeB_n3.lean`.  *Nothing in that file is a* `sorry`.
Every case not proved is a *typed obligation* — a `def … : Type` passed as
an argument, the `CimpAnt` idiom — so an unfinished step is a visible
hypothesis in a signature rather than a hole in a proof.  The cofinality
statements are taken as variables there, so the file stands independent of
the family module while that is re-founded.
:::

:::definition "n1_stabilises" (parent := "chain")
N1 — the chains eventually constant.  Two forms: `EStabEq`/`AStabEq`, where
the chain is *literally* constant from some fuel on, and
`EStabilises`/`AStabilises`, the same up to interderivability, with
`estabilises_of_stabEq` and `astabilises_of_stabEq` between them.  PROVED,
pinned `[propext]` and `[propext, Quot.sound]`.

Alongside them sits the fuel-irrelevance side: `interpP_pfree` — the
interpolants are `p`-free at *every* fuel, not merely in the limit — and
`FuelIrrelevance`, the obligation that a recursion bottoming out below its
fuel is fuel-invariant.
:::

:::definition "n2_uipair" (parent := "chain")
N2 — `IsUIPair` and `HasUI` for {uses "n0e_parking"}[]: Pitts's pair for a
cell, stated intrinsically rather than via the construction.  Pinned `[]` —
they depend on no axioms at all, being data.
:::

:::theorem "n3_equivalence" (parent := "chain")
N3 — *stabilisation ⟺ uniform interpolation, per cell*.  Both directions are
now proved, and they cost differently, which is the thing to notice:

* *forward*, `hasUI_of_stabEq` — PROVED outright from the two cofinality
  variables, `[propext, Quot.sound]`, no cut needed;
* *backward*, `stabilises_of_hasUI` — PROVED *relative to* `CutInv`, the
  composition principle: cut at a negative formula in the inversion phase
  with an empty pending zone.  It is stated at every judgment `j` because
  that is the form a cut-admissibility proof for LJF◯ would deliver, though
  the backward direction instantiates it only at `j = .tru`.

So the remaining debt in this node is not a gap in an argument but a named
theorem someone must supply.  Depends on {uses "n1_stabilises"}[],
{uses "n2_uipair"}[] and {uses "n0d_cofinal"}[].
:::

:::theorem "n4_stabilisation_all" (parent := "chain")
N4 — `StabilisationAll`: every saturated cell stabilises.  *OPEN BOTH WAYS*,
and this is the theorem the route exists to settle.  It is now the only
genuinely open mathematical question in the chain.

Two prongs, and the point worth making to a reader is that *either outcome
is a result*.  The proof prong bounds the fuel a cell needs uniformly over
$`Δ`, by loop-elimination over the finite space of (station, goal) pairs, in
the decider's style; the measured constraint is roughly one parked-box
nesting level per ten fuel units, about three times the derivation height.
The refutation prong looks for a cell whose `A`-chain ascends without bound
— the Ghilardi–Zawadowski shape — using the §4.12 harness: instance screen,
chain probe, cofinality instances by focused kernel search.  A
non-stabilising cell would, with {uses "n3_equivalence"}[], be a proof that
PLL *lacks* uniform interpolation.
:::

:::theorem "n5_ljfo_ui" (parent := "chain")
N5 — `ljfo_ui_of_stabilisation`, uniform interpolation for LJF◯ at every
saturated station, from {uses "n3_equivalence"}[] and
{uses "n4_stabilisation_all"}[].  Still in `wip/ui_routeB_blueprint.lean`
and still carrying a `sorry`; it is the one node WP2 did not reach.
:::

:::theorem "n6_transport" (parent := "chain")
N6 — transport to PLL: `IsUIPairPLL`, `PLL_UI`, the polarisation fact
`pfree_roundTripN`, and the transport itself,
`isUIPairPLL_of_isUIPair` and `pll_ui_of_ljfo`.  PROVED relative to
`CutInv` and to `CellsFor`, pinned `[propext, Quot.sound]`.

`CellsFor` says what the transport still needs per formula: a
uniform-interpolant pair at the polarised station and one at the polarised
goal cell.  The second is an instance of N3 forward at the empty station;
the first is N3 forward at the *saturation* of `[negOfO φ]`, so it also
needs the processing phase `eMinPP`/`aMinPP` to carry the pair back from the
saturated station.  That carrying step is WP4's, and — the sentence worth
quoting to anyone asking how far the route has come — it is the only thing
between that file and `PLL_UI`.

Depends on {uses "n3_equivalence"}[] and {uses "n0b_rows"}[].
:::
