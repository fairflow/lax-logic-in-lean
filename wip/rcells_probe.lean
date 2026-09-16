import LJF.OBridge
import LJF.OSearch
import LaxLogic.RN.Rho
import LaxLogic.Interd

open PLLND LJFO RhoOrder

-- local copy of the two-sided proof side (wip/ljfo_link.lean), so the
-- Rewrite lib will not need a wip import
def decideSeq (Γ : List PLLFormula) (φ : PLLFormula) : LSeq :=
  .inv (Γ.map negOfO) [] .tru (negOfO φ)

def searchProves (f : Nat) (Γ : List PLLFormula) (φ : PLLFormula) : Bool :=
  LSeq.search f (decideSeq Γ φ)

theorem laxND_of_searchProves {f : Nat} {Γ : List PLLFormula}
    {φ : PLLFormula} (h : searchProves f Γ φ = true) :
    Nonempty (LaxND Γ φ) :=
  (bridge_iff Γ φ).mpr ⟨LSeq.search_sound f _ h⟩

-- CALIBRATION: one increment cell, ρ11 ∨ ρ18 ≡ ρ15, both directions by
-- kernel decide over the fueled search
theorem probe_or_11_18 :
    PLLND.SemUI.Interd ((rhoF 11).or (rhoF 18)) (rhoF 15) :=
  ⟨laxND_of_searchProves (f := 44) (by decide +kernel),
   laxND_of_searchProves (f := 44) (by decide +kernel)⟩
