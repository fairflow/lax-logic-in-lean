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

Two nodes are an exception of a different kind.  N0c and N0d below are
settled and pinned, but they live in
`LJF/OFuelPFamKit.lean`, `LJF/OFuelPFam.lean` and
`LJF/OFuelPCofinal.lean`, which reach this branch only with the merge into
`frjw-dev`.  Attaching them before that merge would break the build, so they
should be attached in the first commit after it.

# Craig interpolation

:::group "craig"
The proved starting point.  Uniform interpolation strengthens this to an
interpolant depending only on the antecedent and the shared variables.
:::

:::theorem "maehara" (parent := "craig") (lean := "PLLND.SC.maehara")
Maehara's method on the cut-free sequent calculus `SCh`/`SC` of
`PLLSequent.lean`.  Given a derivation of `Γ ⊢ C` and a splitting of the
context into two parts, the induction produces an interpolant `I` with
`Γ₁ ⊢ I` and `I, Γ₂ ⊢ C` whose atoms occur both in `Γ₁` and in `Γ₂, C`.
Because the left rules of `SCh` keep their principal formula in the context,
the splitting is a membership assignment (`∀ ψ ∈ Γ, ψ ∈ Γ₁ ∨ ψ ∈ Γ₂`) rather
than a partition, and the interpolants combine by `∧`, `∨` and `⊃` according
to the side that carries the principal formula, with the split swapped for
the minor premise of `⊃`-left.  The lax rules add nothing new to the
combinatorics: `◯` on the right passes the interpolant through, and `◯` on the
left boxes it.  The choice-free form `SC.maehara'` is pinned at
`[propext, Quot.sound]`; the Mathlib-phrased wrapper adds `Classical.choice`.
:::

:::theorem "craig" (parent := "craig") (lean := "PLLND.craig_interpolation")
Craig interpolation for PLL, the sequent form, read off {uses "maehara"}[]
at the append splitting `Γ₁ ++ Γ₂`: if `Γ₁ ++ Γ₂ ⊢ C` is derivable then some
`I` has `Γ₁ ⊢ I`, `I, Γ₂ ⊢ C`, and every atom of `I` occurs in `Γ₁` and in
`Γ₂, C`.  Since `SC` is proved equivalent to natural deduction, the Hilbert
system and the term calculus, interpolation for `SC`-derivability is Craig
interpolation for the logic, not for a presentation of it.  The interpolant
is not unique and depends on `C`; removing that dependence is what the rest
of the chapter is about.
:::

:::theorem "craig_imp" (parent := "craig") (lean := "PLLND.craig_implication")
The implication form: if `⊢ A ⊃ B` then some `I` over the common atoms of
`A` and `B` has `⊢ A ⊃ I` and `⊢ I ⊃ B`.  It is the sequent form at the
splitting `[A]; []` after one cut with `⊃`-left, and it is the statement a
textbook reader expects.  Both forms exist choice-free (primed) and in the
Mathlib phrasing of atom sets (unprimed).
:::

# Route (B): the fuel-founded retention interpolant

:::group "routeB"
LJF◯'s `interpF` computes two chains: `E_f` descending from `⊤` and `A_f`
ascending from `⊥`.  If both stabilise, the cell has uniform interpolants.
Stabilisation everywhere is the open theorem.
:::

:::definition "interpF" (parent := "routeB")
`LJFO.interpF` (`LJF/OFuel.lean`) and its parking refinement `LJFO.interpP`
(`LJF/OFuelP.lean`), the retention interpolant at a given fuel.  The
recursion follows the focused proof search of LJF◯ over a station
`(todo, done)`: a processing phase consumes `todo` (atoms, shifts and
conjunctions are unpacked; the implications whose antecedent is a compound
positive, the boxes and the `◯`-implications are parked in `done`), and an
aggregate phase reads the interpolant off the saturated `done`.  In `∃p`
mode (`goal = none`) the read-off is a conjunction of one row per parked
member; in `∀p` mode (`goal = some G`) it is a disjunction of the ways the
station can advance `G`, one attack row per parked member.  Each row of a
parked implication `Q ⊃ N` retains the `∀p` interpolant of its own antecedent
at the full station as a guard, `A(done ⇒ ↑Q)`, which is what makes the
antecedent dispatch an instance of the family's own recursion.  The fuel is
used only as a bound: fuel `0` returns `⊤` in `∃p` mode and `⊥` in `∀p` mode,
so every fuel level is sound by construction and the chains
`E_f := interpP p f [] done none` and `A_f := interpP p f [] done (some G)`
descend from `⊤` and ascend from `⊥`.  `interpP` agrees with `interpF` on
every station without the three parked shapes, kernel-checked at fuels
`0`–`8`, and differs on each of them, kernel-checked.
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

:::theorem "n0c_cofinality" (parent := "routeB")
N0c — *cofinality at a saturated station*: every sufficient `p`-free formula
is reached at some fuel.  *PROVED, and unconditional*, over
{uses "n0e_parking"}[], pinned `[propext, Classical.choice, Quot.sound]`
(§4.17).  `tinvP`, `uentryP`, `parkAntP`, `satE2P`, `satA2P` — the
17-definition family in fuel-carrying form, as ONE `mutual` founded on
$`μ = (\mathrm{hgt}, \mathrm{weight}, \mathrm{sizeOf})`, across
`LJF/OFuelPFamKit.lean`, `LJF/OFuelPFam.lean` and `LJF/OFuelPCofinal.lean`.

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

:::theorem "n0d_cofinal" (parent := "routeB")
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
N3 — *stabilisation ⟺ uniform interpolation, per cell*, given
{uses "n0a_soundness"}[] and {uses "n0d_cofinal"}[].  This is the conceptual heart: it turns
an open question about interpolants into an open question about chains.
DRAFTED, carries a `sorry`.  Depends on {uses "n1_stabilises"}[] and
{uses "n2_uipair"}[].
:::

:::theorem "n4_stabilisation_all" (parent := "chain")
N4 — `StabilisationAll`: every saturated cell stabilises.  *OPEN BOTH WAYS*,
and this is the theorem the route exists to settle.

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
N5 — uniform interpolation for LJF◯, from {uses "n3_equivalence"}[] and
{uses "n4_stabilisation_all"}[].  DRAFTED, `sorry`.
:::

:::theorem "n6_transport" (parent := "chain")
N6 — transport to PLL along the bridge: `PLL_UI := ∀ p φ, Σ E A,
IsUIPairPLL p φ E A`.  DRAFTED, `sorry`.  Depends on
{uses "n5_ljfo_ui"}[] and {uses "n0b_rows"}[].
:::
