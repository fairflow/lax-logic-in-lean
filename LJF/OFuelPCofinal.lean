/-
LJF◯ — cofinality for the parking interpolant `interpP`, UNCONDITIONAL
(route (B), nodes N0c and N0d over node N0e).

`LJF/OFuelPCof.lean` states the two entry points `TInvP`/`UEntryP` and
proves everything downstream of them; `LJF/OFuelPFam.lean` inhabits them.
This module is the read-off: the two entry points, the antecedent
dispatch, `SatE2P`/`SatA2P`, and the two cofinality statements, each with
no parameter left.

## What made them unconditional

Until 2026-09-05 the family carried ONE typed obligation, `ParkAntP`
(`LJF/OFuelPCof.lean`) — the antecedent guard of the five parked
implications, at the antecedent's own goal `↑Q`.  It was a FIXPOINT
requirement, not a gap: `parkAntP_of_satA2P` derives it from `SatA2P p`,
which `satA2P_of_uentryP` derives from `UEntryP p`, so every dispatch is
an instance of the family's own `∀p` entry at the SAME station applied to
the antecedent's own subderivation.  What stood in the way was the
MEASURE: `LJF/O.lean`'s station-first pair cannot pay for a call at an
unchanged station (`docs/ui-ljfo-clause-table.md` §4.11).

The family is now founded on

    μ := (normalised derivation height, station weight, `sizeOf`)

with the height of `LJF/OFuelHeight.lean` Part 10, under which the
dispatch edge is strictly decreasing with the station unchanged
(`hgt_antDispatch`, `nativeParkAnt_edge`).  The guard is a native
recursive call, `ParkAntP` is a consequence rather than a hypothesis, and
`ECofinalP`/`ACofinalP` are inhabited outright.
-/
import LJF.OFuelPFam

namespace LJFO

variable {p : String}

/-! ## The two entry points, inhabited -/

/-- **The `∃p` traversal at a saturated station.** -/
def tinvP : TInvP p := tinvP_of

/-- **The `∀p` entry at a saturated station.** -/
def uentryP : UEntryP p := uentryP_of

/-- **The antecedent dispatch of the five parked implications** — the
former obligation, now a consequence of the family it used to be a
parameter of. -/
def parkAntP : ParkAntP p := parkAntP_of_satA2P (satA2P_of_uentryP uentryP)

/-- Cofinality at a saturated station, `∃p` side. -/
def satE2P : SatE2P p := satE2P_of_tinvP tinvP

/-- Cofinality at a saturated station, `∀p` side. -/
def satA2P : SatA2P p := satA2P_of_uentryP uentryP

/-! ## The two cofinality statements

Hoisted here from `wip/ui_routeB_statements.lean`, verbatim, so that the
statements and their inhabitants live in the production estate together. -/

/-- Cofinality, ∃ side: a `p`-free consequence of a saturated station is a
consequence of the approximant at some finite fuel, and the fuel is DATA. -/
def ECofinalP (p : String) : Type :=
  ∀ (done Δ : List Neg) (ψ : Neg), Saturated done → ParkedCtxP done →
    PFreeCtx p Δ → PFreeN p ψ →
    ∀ {j : JD} (d : Inv (done ++ Δ) [] j ψ),
      Σ f : Nat, Inv (interpP p f [] done none :: Δ) [] j ψ

/-- Cofinality, ∀ side, E-relativised as `ACofinalF` is. -/
def ACofinalP (p : String) : Type :=
  ∀ (done Δ : List Neg) (G : Neg), Saturated done → ParkedCtxP done →
    PFreeCtx p Δ →
    ∀ {j : JD} (d : Inv (done ++ Δ) [] j G),
      Σ f : Nat, Inv (interpP p f [] done none :: Δ) [] .tru
        (interpP p f [] done (some (jGoal j G)))

/-- `ECofinalP` follows from cofinality at a saturated station. -/
def ecofinalP_of_satE2P (s2 : SatE2P p) : ECofinalP p :=
  fun done Δ ψ hsat hP hΔ hψ _ d =>
    let w := s2 done Δ ψ hsat hP hΔ hψ d
    ⟨w.1, w.here⟩

/-- `ACofinalP` follows likewise, on the diagonal of the two fuels. -/
def acofinalP_of_satA2P (a2 : SatA2P p) : ACofinalP p :=
  fun done Δ G hsat hP hΔ _ d =>
    let w := a2 done Δ G hsat hP hΔ d
    ⟨w.1, w.here⟩

/-- `ECofinalP` from the `∃p` traversal. -/
def ecofinalP_of_tinvP (t : TInvP p) : ECofinalP p :=
  ecofinalP_of_satE2P (satE2P_of_tinvP t)

/-- `ACofinalP` from the `∀p` entry. -/
def acofinalP_of_uentryP (u : UEntryP p) : ACofinalP p :=
  acofinalP_of_satA2P (satA2P_of_uentryP u)

/-- **Cofinality, ∃ side — PROVED** (blueprint node N0c). -/
def ecofinalP : ECofinalP p := ecofinalP_of_tinvP tinvP

/-- **Cofinality, ∀ side — PROVED** (blueprint node N0d). -/
def acofinalP : ACofinalP p := acofinalP_of_uentryP uentryP

end LJFO

/-! ### Axiom audit

The measured set is the one `LJF/O.lean`'s weight-founded family has:
`Classical.choice` enters from the well-founded recursion, nothing else.
-/

#axioms_within LJFO.tinvP [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.uentryP [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.parkAntP [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.satE2P [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.satA2P [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.ecofinalP [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.acofinalP [propext, Classical.choice, Quot.sound]

#axioms_within LJFO.ecofinalP_of_satE2P [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.acofinalP_of_satA2P [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.ecofinalP_of_tinvP [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.acofinalP_of_uentryP [propext, Classical.choice, Quot.sound]
