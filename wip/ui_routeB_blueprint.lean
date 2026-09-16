/-
Route (B) — the BLUEPRINT after cofinality (drafted 2026-09-05, while the
height-first founding of the cofinality family is being built).

WORK IN PROGRESS, BY DIRECTION.  Bodies below are `sorry`.  Matthew set the
standing rule ("a sorry asserts") aside for blueprint work on 2026-09-05:
these declarations are the NODES of the plan, stated so that they can be
filled, reviewed and fed to a collaboration blueprint.  This module lives
in the Experimental library only; `lake build Production` never sees it.
Every claim here is OPEN until its `sorry` is gone and its axioms pinned.

Reading order of the nodes:

  N1  EStabilises / AStabilises   — the fuel chains are eventually constant
  N2  IsUIPair / HasUI            — the intrinsic (Pitts) uniform-interpolant pair of a cell
  N3  hasUI_of_stabilises, stabilises_of_hasUI — W ⟺ UI per cell
  N4  StabilisationAll            — THE theorem: every cell stabilises (open both ways)
  N5  ljfo_ui_of_stabilisation    — UI for LJF◯ at every saturated station
  N6  IsUIPairPLL / pll_ui_of_ljfo — transport to PLL through the focalization bridge

Inputs already PROVED (not restated here): `eSoundF`/`aSoundF`
(`LJF/OFuelSound.lean`), the processing phase `eMinFF`/`aMinFF` and the
reductions `ecofinalF_of_satE2F`/`acofinalF_of_satA2F` (`LJF/OFuelMin.lean`),
the bridge `bridge_iff` (`LJF/OBridge.lean`).  Input IN PROGRESS: the
saturated-station cofinality family (`SatE2F`/`SatA2F`), founded on
derivation height (agent build, base e273a32).
-/
import LJF.O
import LJF.OFuel
import LJF.OFuelSound
import LJF.OFuelMin
import LJF.OBridge
import wip.ui_routeB_statements

namespace LJFO

open PLLND

/-! ## N1 · Stabilisation of the fuel chains at a saturated station

`E_f := interpF p f [] done none` descends from `⊤`; `A_f := interpF p f []
done (some G)` ascends from `⊥`.  Stabilisation is stated up to
interderivability, the A-side MODULO `E_f` — the form cofinality delivers
(`E_f, Δ ⊢ A_f`) and the record's rule "stabilisation testing must be
logical, never syntactic". -/

/-- The ∃p-chain is eventually constant up to interderivability. -/
def EStabilises (p : String) (done : List Neg) : Type :=
  Σ f₀ : Nat, ∀ f, f₀ ≤ f →
    Inv [interpF p f₀ [] done none] [] .tru (interpF p f [] done none) ×
    Inv [interpF p f [] done none] [] .tru (interpF p f₀ [] done none)

/-- The ∀p-chain is eventually constant modulo `E_f`. -/
def AStabilises (p : String) (done : List Neg) (G : Neg) : Type :=
  Σ f₀ : Nat, ∀ f, f₀ ≤ f →
    Inv [interpF p f [] done none, interpF p f₀ [] done (some G)] [] .tru
      (interpF p f [] done (some G)) ×
    Inv [interpF p f [] done none, interpF p f [] done (some G)] [] .tru
      (interpF p f₀ [] done (some G))

/-! ## N2 · The uniform-interpolant pair of a cell, intrinsic

Pitts's pair for the sequent `done ⇒ G` and the variable `p`: `E` is the
strongest `p`-free consequence of the station, `A` the weakest `p`-free
formula sufficient for the goal, its minimality RELATIVE to `E` (exactly as
`SatA2` is stated).  Nothing here mentions a chain.  The goal judgment is
`tru`; the `lax` case is the same with `jGoal`. -/
structure IsUIPair (p : String) (done : List Neg) (G : Neg) (E A : Neg) : Type where
  pfreeE : PFreeN p E
  pfreeA : PFreeN p A
  /-- `Γ ⊢ E` -/
  soundE : Inv done [] .tru E
  /-- `Δ, Γ ⊢ ψ  →  Δ, E ⊢ ψ` for `p`-free `Δ`, `ψ` -/
  minE : ∀ (Δ : List Neg) (ψ : Neg), PFreeCtx p Δ → PFreeN p ψ →
    Inv (done ++ Δ) [] .tru ψ → Inv (E :: Δ) [] .tru ψ
  /-- `A, Γ ⊢ G` -/
  soundA : Inv (A :: done) [] .tru G
  /-- `Δ, Γ ⊢ G  →  Δ, E ⊢ A` for `p`-free `Δ` -/
  minA : ∀ (Δ : List Neg), PFreeCtx p Δ →
    Inv (done ++ Δ) [] .tru G → Inv (E :: Δ) [] .tru A

/-- The cell has a uniform-interpolant pair. -/
def HasUI (p : String) (done : List Neg) (G : Neg) : Type :=
  Σ (E A : Neg), IsUIPair p done G E A

/-! ## The cofinality inputs in their upward-closed form

The approved `ECofinalF`/`ACofinalF` give SOME fuel; the equivalence N3 in
the backward direction needs the fuel to work FROM SOME POINT ON (the
`UpFrom` witnesses of `LJF/OFuelMin.lean` deliver exactly this). -/
def ECofinalUp (p : String) : Type :=
  ∀ (done Δ : List Neg) (ψ : Neg), Saturated done → ParkedCtx done →
    PFreeCtx p Δ → PFreeN p ψ →
    ∀ {j : JD} (_d : Inv (done ++ Δ) [] j ψ),
      Σ f₀ : Nat, ∀ f, f₀ ≤ f → Inv (interpF p f [] done none :: Δ) [] j ψ

def ACofinalUp (p : String) : Type :=
  ∀ (done Δ : List Neg) (G : Neg), Saturated done → ParkedCtx done →
    PFreeCtx p Δ →
    ∀ {j : JD} (_d : Inv (done ++ Δ) [] j G),
      Σ f₀ : Nat, ∀ f, f₀ ≤ f →
        Inv (interpF p f [] done none :: Δ) [] .tru
          (interpF p f [] done (some (jGoal j G)))

/-! ## N3 · W ⟺ UI, per cell -/

/-- Forward: if both chains stabilise, the stabilised values are a
uniform-interpolant pair.  Soundness from `eSoundF`/`aSoundF`; minimality
from cofinality read at the stabilised fuel. -/
def hasUI_of_stabilises (p : String) (done : List Neg) (G : Neg)
    (_hsat : Saturated done) (_hP : ParkedCtx done)
    (_ec : ECofinalUp p) (_ac : ACofinalUp p)
    (_hE : EStabilises p done) (_hA : AStabilises p done G) : HasUI p done G := by
  sorry

/-- Backward: if the cell has a pair `(E, A)`, cofinality applied to `E` and
to `A` gives a fuel from which `E_f ⟛ E` and `E_f ∧ A_f ⟛ E_f ∧ A`, hence
both chains stabilise.  This is the direction that needs the upward-closed
form. -/
def stabilises_of_hasUI (p : String) (done : List Neg) (G : Neg)
    (_hsat : Saturated done) (_hP : ParkedCtx done)
    (_ec : ECofinalUp p) (_ac : ACofinalUp p)
    (_h : HasUI p done G) : EStabilises p done × AStabilises p done G := by
  sorry

/-! ## N4 · THE theorem: every cell stabilises

OPEN BOTH WAYS.  With N3, this is uniform interpolation for LJF◯ at the
saturated stations.  The record's proof prong: bound the fuel a cell needs
by loop-elimination over the finite state space of (station, goal) pairs
the recursion visits from the cell (stations read as sets).  The record's
refutation prong: a cell whose A-chain ascends without bound — the shape of
the Ghilardi–Zawadowski witnesses for S4 — refutes it, and with N3 refutes
UI for PLL.  Screening harness: `docs/ui-ljfo-clause-table.md` §4.12,
`wip/ui_screen/`. -/
def StabilisationAll (p : String) : Type :=
  ∀ (done : List Neg) (G : Neg), Saturated done → ParkedCtx done →
    EStabilises p done × AStabilises p done G

/-- The node to fill — or to refute. -/
def stabilisationAll (p : String) : StabilisationAll p := by
  sorry

/-! ## N5 · UI for LJF◯ at every saturated station -/
def ljfo_ui_of_stabilisation (p : String)
    (_ec : ECofinalUp p) (_ac : ACofinalUp p) (_st : StabilisationAll p) :
    ∀ (done : List Neg) (G : Neg), Saturated done → ParkedCtx done → HasUI p done G := by
  sorry

/-! ## N6 · Transport to PLL through the focalization bridge

A PLL formula is `p`-free iff its polarisation is.  The formula-level pair
`(∃p.φ, ∀p.φ)`: `∃p.φ` from the E-side of the station `[negOfO φ]`
(processed to saturation by `eMinFF`), `∀p.φ` from the A-side of the cell
`[] ⇒ negOfO φ`; derivability transports by `bridge_iff` in both
directions and `eraseNeg` recovers PLL formulas. -/
def PFreeF (p : String) (φ : PLLFormula) : Prop := PFreeN p (negOfO φ)

structure IsUIPairPLL (p : String) (φ : PLLFormula) (E A : PLLFormula) : Type where
  pfreeE : PFreeF p E
  pfreeA : PFreeF p A
  soundE : Nonempty (LaxND [φ] E)
  minE : ∀ ψ, PFreeF p ψ → Nonempty (LaxND [φ] ψ) → Nonempty (LaxND [E] ψ)
  soundA : Nonempty (LaxND [A] φ)
  minA : ∀ ψ, PFreeF p ψ → Nonempty (LaxND [ψ] φ) → Nonempty (LaxND [ψ] A)

/-- Uniform interpolation for PLL. -/
def PLL_UI : Type := ∀ (p : String) (φ : PLLFormula), Σ (E A : PLLFormula), IsUIPairPLL p φ E A

def pll_ui_of_ljfo
    (_ec : ∀ p, ECofinalUp p) (_ac : ∀ p, ACofinalUp p) (_st : ∀ p, StabilisationAll p) :
    PLL_UI := by
  sorry

end LJFO
