import LaxLogic.PLLSemUILayered
import LaxLogic.PLLFrames

/-!
# `crankC` and rank preservation for PCLL (bare possibility)

Branch `ui-confluence`.  On mutually confluent models the ∀∃-clause for
◯ collapses to bare possibility, so a ◯-move costs ONE modal step, not
two.  `crankC` charges ◯ = +1 (vs `crank`'s +2), and
`force_iff_of_layeredC` is `force_iff_of_layered` with that recalibration
— identical on every connective except `somehow`, whose case now uses
`force_somehow_iff_of_confluent` and a single `mforth`/`mback`.

Interactive development (Matthew + Claude): the `somehow` case is the one
open goal.
-/

open PLLFormula

namespace PLLND
open SemUI

/-- **`crankC`**: like `crank`, but ◯ costs 1 (bare possibility spends a
single `Rₘ`-move, no preceding `Rᵢ`-move). -/
def crankC : PLLFormula → Nat
  | .prop _ => 0
  | .falsePLL => 0
  | .and φ ψ => max (crankC φ) (crankC ψ)
  | .or φ ψ => max (crankC φ) (crankC ψ)
  | .ifThen φ ψ => max (crankC φ) (crankC ψ) + 1
  | .somehow φ => crankC φ + 1

/-- **Rank preservation under bare possibility.**  A level-`n` layered
link transfers every formula of `crankC ≤ n` (protected atoms) between
mutually confluent models.  Only the `somehow` case differs from
`force_iff_of_layered`: it spends one modal move, not two. -/
theorem force_iff_of_layeredC {A : String → Prop} {M N : ConstraintModel}
    (hM : MutuallyConfluent M) (hN : MutuallyConfluent N)
    (B : LayeredBisim A M N) :
    ∀ {φ : PLLFormula} {n : Nat}, crankC φ ≤ n →
    (∀ a ∈ φ.atoms, A a) →
    ∀ {w : M.W} {w' : N.W}, B.Z n w w' → (M.force w φ ↔ N.force w' φ) := by
  intro φ
  induction φ with
  | prop a =>
      intro n _ hA w w' hZ
      simpa [ConstraintModel.force] using B.atoms hZ a (hA a (by simp))
  | falsePLL =>
      intro n _ _ w w' hZ
      simpa [ConstraintModel.force] using B.fall hZ
  | and φ ψ ihφ ihψ =>
      intro n hc hA w w' hZ
      have h1 : ∀ a ∈ φ.atoms, A a := fun a ha => hA a (by simp [ha])
      have h2 : ∀ a ∈ ψ.atoms, A a := fun a ha => hA a (by simp [ha])
      simp only [ConstraintModel.force]
      exact and_congr
        (ihφ (le_trans (le_max_left _ _) hc) h1 hZ)
        (ihψ (le_trans (le_max_right _ _) hc) h2 hZ)
  | or φ ψ ihφ ihψ =>
      intro n hc hA w w' hZ
      have h1 : ∀ a ∈ φ.atoms, A a := fun a ha => hA a (by simp [ha])
      have h2 : ∀ a ∈ ψ.atoms, A a := fun a ha => hA a (by simp [ha])
      simp only [ConstraintModel.force]
      exact or_congr
        (ihφ (le_trans (le_max_left _ _) hc) h1 hZ)
        (ihψ (le_trans (le_max_right _ _) hc) h2 hZ)
  | ifThen φ ψ ihφ ihψ =>
      intro n hc hA w w' hZ
      have h1 : ∀ a ∈ φ.atoms, A a := fun a ha => hA a (by simp [ha])
      have h2 : ∀ a ∈ ψ.atoms, A a := fun a ha => hA a (by simp [ha])
      have hc' : max (crankC φ) (crankC ψ) + 1 ≤ n := hc
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have hcφ : crankC φ ≤ m := by
        have h1 := le_max_left (crankC φ) (crankC ψ); omega
      have hcψ : crankC ψ ≤ m := by
        have h1 := le_max_right (crankC φ) (crankC ψ); omega
      simp only [ConstraintModel.force]
      constructor
      · intro hf v' hv' hφ'
        obtain ⟨v, hv, hZv⟩ := B.iback hZ hv'
        exact (ihψ hcψ h2 hZv).mp (hf v hv ((ihφ hcφ h1 hZv).mpr hφ'))
      · intro hf v hv hφv
        obtain ⟨v', hv', hZv⟩ := B.iforth hZ hv
        exact (ihψ hcψ h2 hZv).mpr (hf v' hv' ((ihφ hcφ h1 hZv).mp hφv))
  | somehow φ ihφ =>
      intro n hc hA w w' hZ
      have hc' : crankC φ + 1 ≤ n := hc
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have hcφ : crankC φ ≤ m := by omega
      rw [force_somehow_iff_of_confluent hM, force_somehow_iff_of_confluent hN]
      constructor
      · rintro ⟨u, hu, hφu⟩
        obtain ⟨u', hu', hZu⟩ := B.mforth hZ hu
        exact ⟨u', hu', (ihφ hcφ hA hZu).mp hφu⟩
      · rintro ⟨u', hu', hφu'⟩
        obtain ⟨u, hu, hZu⟩ := B.mback hZ hu'
        exact ⟨u, hu, (ihφ hcφ hA hZu).mpr hφu'⟩


/-- Audit: rank preservation under confluence is sorry-free. -/
#print axioms force_iff_of_layeredC

end PLLND
