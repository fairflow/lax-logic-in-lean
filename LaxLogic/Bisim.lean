import LaxLogic.PLLKripke
import LaxLogic.PLLG4Space

/-!
# A-bisimulation for constraint models, and its invariance theorem

The bisimulation primitives for PLL's constraint models, in the form
every consumer needs them.  An **A-bisimulation** is a zigzag for both
relations `Rᵢ` and `Rₘ` which matches fallibility and matches atoms
inside a protected alphabet `A`; `force_iff_of_bisim` is the resulting
invariance theorem, for formulas whose atoms lie in `A`.

The `⊃`-case spends one `Rᵢ`-zigzag.  The `◯`-case is the one with
content: PLL's forcing clause for `◯φ` is `∀∃` — an `Rᵢ`-move to a
future, then an `Rₘ`-move to a constraint witness — so transferring it
needs the zigzag in *both* relations, which is why `ABisim` carries
four zigzag fields rather than two.

## Provenance

The constraint models and the `∀∃` clause are Fairtlough and Mendler's
(Inf. Comput. 137(1), 1997, §4).  A-bisimulation and the invariance
theorem in this alphabet-relative form are ours.

## Status

`force_iff_of_bisim` and `ABisim.id` are PROVED and axiom-pinned below.
Nothing here is conditional and nothing is open.

This file was extracted verbatim from `LaxLogic/PLLSemUI.lean`, which
now imports it.  The extraction is code motion only — no statement and
no proof was changed.  It exists because these four declarations are
the general-purpose part of that file: `Reject/Bisim.lean` builds the
refutation calculus's `Bisim` on `ABisim (fun _ => True)`, while the
rest of `PLLSemUI.lean` belongs to the semantic uniform-interpolation
route, which is parked and unproved.
-/

open PLLFormula
namespace PLLND
namespace SemUI

/-- **A-bisimulation** between constraint models: zigzag for both
relations, matching fallibility, matching atoms in the protected
alphabet `A`. -/
structure ABisim (A : String → Prop) (M N : ConstraintModel) where
  Z : M.W → N.W → Prop
  atoms : ∀ {w w'}, Z w w' → ∀ a, A a → (w ∈ M.V a ↔ w' ∈ N.V a)
  fall  : ∀ {w w'}, Z w w' → (w ∈ M.F ↔ w' ∈ N.F)
  iforth : ∀ {w w'}, Z w w' → ∀ {v}, M.Ri w v → ∃ v', N.Ri w' v' ∧ Z v v'
  iback  : ∀ {w w'}, Z w w' → ∀ {v'}, N.Ri w' v' → ∃ v, M.Ri w v ∧ Z v v'
  mforth : ∀ {w w'}, Z w w' → ∀ {u}, M.Rm w u → ∃ u', N.Rm w' u' ∧ Z u u'
  mback  : ∀ {w w'}, Z w w' → ∀ {u'}, N.Rm w' u' → ∃ u, M.Rm w u ∧ Z u u'

/-- **Forcing is invariant under A-bisimulation** for formulas over the
protected alphabet.  The ⊃-case uses i-zigzag; the ◯-case uses i-zigzag
to move the future and m-zigzag to move the constraint witness. -/
theorem force_iff_of_bisim {A : String → Prop} {M N : ConstraintModel}
    (B : ABisim A M N) :
    ∀ {φ : PLLFormula}, (∀ a ∈ φ.atoms, A a) →
    ∀ {w : M.W} {w' : N.W}, B.Z w w' → (M.force w φ ↔ N.force w' φ) := by
  intro φ
  induction φ with
  | prop a =>
      intro hA w w' hZ
      simpa [ConstraintModel.force] using B.atoms hZ a (hA a (by simp))
  | falsePLL =>
      intro _ w w' hZ
      simpa [ConstraintModel.force] using B.fall hZ
  | and φ ψ ihφ ihψ =>
      intro hA w w' hZ
      have h1 : ∀ a ∈ φ.atoms, A a := fun a ha => hA a (by simp [ha])
      have h2 : ∀ a ∈ ψ.atoms, A a := fun a ha => hA a (by simp [ha])
      simp only [ConstraintModel.force]
      exact and_congr (ihφ h1 hZ) (ihψ h2 hZ)
  | or φ ψ ihφ ihψ =>
      intro hA w w' hZ
      have h1 : ∀ a ∈ φ.atoms, A a := fun a ha => hA a (by simp [ha])
      have h2 : ∀ a ∈ ψ.atoms, A a := fun a ha => hA a (by simp [ha])
      simp only [ConstraintModel.force]
      exact or_congr (ihφ h1 hZ) (ihψ h2 hZ)
  | ifThen φ ψ ihφ ihψ =>
      intro hA w w' hZ
      have h1 : ∀ a ∈ φ.atoms, A a := fun a ha => hA a (by simp [ha])
      have h2 : ∀ a ∈ ψ.atoms, A a := fun a ha => hA a (by simp [ha])
      simp only [ConstraintModel.force]
      constructor
      · intro hf v' hv' hφ'
        obtain ⟨v, hv, hZv⟩ := B.iback hZ hv'
        exact (ihψ h2 hZv).mp (hf v hv ((ihφ h1 hZv).mpr hφ'))
      · intro hf v hv hφv
        obtain ⟨v', hv', hZv⟩ := B.iforth hZ hv
        exact (ihψ h2 hZv).mpr (hf v' hv' ((ihφ h1 hZv).mp hφv))
  | somehow φ ihφ =>
      intro hA w w' hZ
      simp only [ConstraintModel.force]
      constructor
      · intro hf v' hv'
        obtain ⟨v, hv, hZv⟩ := B.iback hZ hv'
        obtain ⟨u, hu, hφu⟩ := hf v hv
        obtain ⟨u', hu', hZu⟩ := B.mforth hZv hu
        exact ⟨u', hu', (ihφ hA hZu).mp hφu⟩
      · intro hf v hv
        obtain ⟨v', hv', hZv⟩ := B.iforth hZ hv
        obtain ⟨u', hu', hφu'⟩ := hf v' hv'
        obtain ⟨u, hu, hZu⟩ := B.mback hZv hu'
        exact ⟨u, hu, (ihφ hA hZu).mpr hφu'⟩

/-- The identity bisimulation (any alphabet). -/
def ABisim.id (A : String → Prop) (M : ConstraintModel) : ABisim A M M where
  Z := fun w w' => w = w'
  atoms := by rintro w _ rfl a _; exact Iff.rfl
  fall := by rintro w _ rfl; exact Iff.rfl
  iforth := by rintro w _ rfl v hv; exact ⟨v, hv, rfl⟩
  iback := by rintro w _ rfl v' hv'; exact ⟨v', hv', rfl⟩
  mforth := by rintro w _ rfl u hu; exact ⟨u, hu, rfl⟩
  mback := by rintro w _ rfl u' hu'; exact ⟨u', hu', rfl⟩

/-- Bisimulation protecting every atom except `p`: its related worlds
are each other's *p-variants*. -/
abbrev PBisim (p : String) := ABisim (fun a => a ≠ p)

/-! ## Axiom audit (pinned) -/

/--
info: 'PLLND.SemUI.force_iff_of_bisim' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms force_iff_of_bisim

/--
info: 'PLLND.SemUI.ABisim.id' does not depend on any axioms
-/
#guard_msgs in
#print axioms ABisim.id

end SemUI
end PLLND
