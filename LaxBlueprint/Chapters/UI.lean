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
where exactly the obstruction sits.  Its sources are
`docs/ui-routeB-blueprint.md`, the maintained node table, and
`docs/ui-ljfo-clause-table.md`, the running record — currently to §4.20.
This chapter is the reader's view of them and will drift unless kept in
step; it has twice been a day stale already.

As of §4.28 (2026-09-06) the shape is this: everything from N0a through N3 is
proved, N5 and N6 are proved relative to N4, and what is not proved is
carried as a *named obligation in a signature* rather than as a hole.  **N4
is the only obligation left between route (B) and `PLL_UI`** — its `◯`-free
instance proved, and the PLL case reduced to a single statement, `PQHard`.

These statuses move daily.  The maintained record is
`docs/ui-routeB-blueprint.md` with `docs/ui-ljfo-clause-table.md`; where this
chapter and those disagree, they are right and this is stale.

A note on method, since it explains what is and is not attached below.
Route (B) is moving week by week, so nodes here carry `(lean := "...")`
only where the declaration is settled.  Where a statement is still drafted
or carries a `sorry`, the node is prose: attaching a name that is about to
change would break the build for no gain.

Two exceptions, both for the same reason — the name or the founding is
about to change:

* the WP2 nodes: `wip/ui_routeB_n3.lean` is proved and pinned, but N7 plans
  to hoist it out of `wip/`;
* N0c and N0d: proved and pinned, but attaching them means importing
  `LJF.OFuelPCofinal`, and hence `LJF/OFuelPFam.lean` — the module §4.20
  measures at 1463 s on a clean build, because of the `WellFounded.fix`
  packing rather than anything about its content.  §4.20 also records the
  design that replaces that founding.  Tying this chapter's build to a
  founding that is being replaced buys a derived status at the cost of a
  25-minute build on every publish, so these two stay prose until the
  refounding lands.  *The statements do not change under it* (§4.18) — only
  the founding does, so the prose below is not at risk of going stale.

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
WP2, in `wip/ui_routeB_n3.lean`.  *Nothing in that file is a* `sorry`.
Every case not proved is a *typed obligation* — a `def … : Type` passed as
an argument, the `CimpAnt` idiom — so an unfinished step is a visible
hypothesis in a signature rather than a hole in a proof.  The cofinality
statements are taken as variables there, so the file stands independent of
the family module while that is re-founded.
:::

:::definition "n1_stabilises" (parent := "chain")
N1 — the chains eventually constant.  STATED in two forms, and *only one of
them survives*.

`EStabEq`/`AStabEq` ask for the chain to be *literally* constant from some
fuel on.  That form is REFUTED (§4.23), in the kernel and by six designed
cells: the `∀p` attack row of a parked `Q ⊃ N ∈ done` at goal `↑Q`
reproduces the same call one fuel down, so the chain is strictly
size-ascending.  `EStabEq`/`AStabEq` therefore have *no instances* at any
saturated station carrying a retained compound implication.  The dividing
line is saturation with such an implication, not weight —
`literal_N1_dividing_line` packages all six cells, with an unsaturated
control that *is* literally constant.

`EStabilises`/`AStabilises`, the same statement up to interderivability, are
the forms the route actually uses.

Alongside them, `interpP_pfree`: the interpolants are `p`-free at *every*
fuel, not merely in the limit.  `FuelIrrelevance` is recorded MOOT — its
consumer's hypothesis is unsatisfiable at the stations of interest.
:::

:::definition "n2_uipair" (parent := "chain")
N2 — `IsUIPair` and `HasUI` for {uses "n0e_parking"}[]: Pitts's pair for a
cell, stated intrinsically rather than via the construction.  Pinned `[]` —
they depend on no axioms at all, being data.
:::

:::theorem "n0k_cutinv" (parent := "chain")
N0k — `cutInv`, cut at a negative formula in the inversion phase with an
empty pending zone:

$$`\mathsf{Inv}\ Γ\ [\,]\ \mathsf{tru}\ N \;→\; \mathsf{Inv}\ (N :: Δ)\ [\,]\ j\ ψ \;→\; \mathsf{Inv}\ (Γ +\!\!+ Δ)\ [\,]\ j\ ψ`

PROVED (§4.22), by *polarisation invariance* rather than by a cut-elimination
argument, in `LJF/OPolInv.lean`.  The transfer block `bLL`, `gA`, `sD`, `fT`,
`fS`, `bCtx`, and `polInvT`/`polInvL`/`cutInvNE`, pin at
`[propext, Quot.sound]`; `cutInv` itself at
`[propext, Classical.choice, Quot.sound]`, the choice entering through the
`Type` packaging of a `Nonempty` result across the `Prop`-valued bridge and
not through the argument.  The `◯`-free block
`polInvT_circFree`/`cutInv_circFree` was committed first.  The converse
`(A′)` is REFUTED (`notCanGoalConverse`).

This is what {uses "n3_equivalence"}[] was formerly stated relative to.
:::

:::theorem "n3_equivalence" (parent := "chain")
N3 — *stabilisation ⟺ uniform interpolation, per cell*.  PROVED BOTH WAYS,
`[propext, Classical.choice, Quot.sound]` (§4.22–§4.23), in
`wip/ui_routeB_n4.lean` and `wip/ui_routeB_n3_cut.lean`, with
{uses "n0k_cutinv"}[] discharging what the backward direction was previously
stated relative to.

Both directions run through the *interderivable* forms of
{uses "n1_stabilises"}[] — `hasUI_of_stabilises` forward,
`stabilises_of_hasUI` backward.  An earlier `hasUI_of_stabEq`, over the
literal forms, is not the live result: §4.23's dividing line is exactly its
hypothesis, so it has no instances.  That is worth stating plainly, because
the literal form is the one a reader would expect to be the stronger
statement, and here it is the empty one.

Depends on {uses "n1_stabilises"}[], {uses "n2_uipair"}[],
{uses "n0d_cofinal"}[] and {uses "n0k_cutinv"}[].
:::

:::theorem "n4_stabilisation_all" (parent := "chain")
N4 — `StabilisationAll`: every saturated cell stabilises, in the
interderivable form.  Since §4.24 this is the *only* obligation between
route (B) and `PLL_UI`, and it has been narrowed a long way since.

*The `◯`-free instance is PROVED* — `n4_circFree_uncond`,
`[propext, Classical.choice, Quot.sound]` (§4.23), by transport from
`LJFIPC.uniform_interpolation_IPC` through `polInvT` and N3 backward.  So the
question is not open across the board: it is open for `◯`.

*For PLL it is OPEN both ways*, and §4.25 reduced it from a question about
cells to two typed obligations about the recursion:

$$`\mathsf{n4\_of\_interpQ} : \mathsf{PQEquiv}\ p → \mathsf{QBound}\ p → ∀\ \mathit{done}\ G,\ \mathsf{EStabilises}\ p\ \mathit{done} × \mathsf{AStabilises}\ p\ \mathit{done}\ G`

`QBound` is PROVED (§4.26: `qBound`, on the measure $`μ = κ·W + ν`,
`[propext, Quot.sound]`).  `PQEquiv` — that `interpP` and `interpQ` agree at
every fuel and cell — is open, and since its easy halves are proved
(`pqEquiv_of_hard : PQHard p → PQEquiv p`, §4.27), **`PLL_UI` rests on
`PQHard` alone.**

What the record says about `PQHard`, as of §4.28: it survives its designed
refutation candidate at fuels 1–6; eighteen designed cells, six of them
Ghilardi–Zawadowski shapes, all bottom out; the naive per-state simultaneous
induction hypothesis is REFUTED on both halves; the per-station reset is
REFUTED on a `◯`-free cell; fuel monotonicity of both recursions is PROVED.
The obstruction to a per-fuel proof is stated exactly and a derivation-level
route proposed; the choice between routes is open.

The older reading of this node as *termination of the recursion* (§4.19) has
been withdrawn — the fuel is essential.

Either outcome remains a result: a non-stabilising cell would, with
{uses "n3_equivalence"}[], be a proof that PLL *lacks* uniform interpolation.
:::

:::theorem "n5_ljfo_ui" (parent := "chain")
N5 — uniform interpolation for LJF◯ at every saturated station.  PROVED
relative to {uses "n4_stabilisation_all"}[],
`[propext, Classical.choice, Quot.sound]` (§4.24), in
`wip/ui_routeB_wp4.lean`, where N4 is restated as `StabilisationAllP`.

The earlier draft `ljfo_ui_of_stabilisation` in
`wip/ui_routeB_blueprint.lean` still carries a `sorry`; that file's `interpF`
drafts of N1–N6 are superseded and are to be retired in one deliberate step
with a supersession note, so the `sorry` is stale bookkeeping rather than a
gap.
:::

:::theorem "n6_transport" (parent := "chain")
N6 — transport to PLL: `IsUIPairPLL`, `PLL_UI`, the polarisation fact
`pfree_roundTripN`, and the transport `pll_ui_of_ljfo′`.  All
`[propext, Classical.choice, Quot.sound]` (§4.22, §4.24).

*PROVED on IPC formulas.*  `cellsFor_circFree` and

$$`\mathsf{ipc\_ui\_routeB} : (∀ p,\ \mathsf{SatE2P}\ p) → (∀ p,\ \mathsf{SatA2P}\ p) → \mathsf{IPC\_UI\_routeB}`

tested against every `p`-free PLL formula, `◯` included, and — the part worth
pausing on — *agreeing* with `LJFIPC.uniform_interpolation_IPC` up to
interderivability (`routeB_agrees_IPC`).  Two independently constructed
interpolants, from different routes, giving the same answers: that is a
check on the construction that no single-route proof can provide.

*PROVED relative to {uses "n4_stabilisation_all"}[] alone* in general:
`cellsFor_of_stab` and `pll_ui_of_stabilisationAll`.  So the transport is no
longer conditional on anything but N4.

Depends on {uses "n3_equivalence"}[], {uses "n5_ljfo_ui"}[],
{uses "n0k_cutinv"}[] and {uses "n0b_rows"}[].
:::
