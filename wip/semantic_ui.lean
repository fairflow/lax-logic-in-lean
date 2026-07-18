import LaxLogic.PLLKripke
import LaxLogic.PLLCompleteness
import LaxLogic.PLLG4Space

/-!
# The semantic route to uniform interpolation: bisimulation quantifiers

Ghilardi-style plan, adapted to constraint models.  The syntactic route
(task #9) builds ∃p/∀p by recursion over the calculus; this file instead
characterises them SEMANTICALLY, via bisimulation:

    w ⊨ ∃p.φ   iff   some p-variant of w forces φ
    w ⊨ ∀p.φ   iff   every p-variant of every Rᵢ-future of w forces φ

where a *p-variant* is a world related by a bisimulation protecting every
atom except p.  This file proves, over the full class of constraint
models (matching the library's `soundness`/`completeness`):

* `force_iff_of_bisim` — forcing is invariant under A-bisimulation, for
  formulas whose atoms lie in the protected alphabet A.  The ◯-case
  needs zigzag for BOTH relations; the ⊥-case needs matching
  fallibility.  PROVED.
* `ABisim.id` — the identity is an A-bisimulation.  PROVED.
* `semEx_upper`, `semEx_adjunction`, `semAll_lower`, `semAll_adjunction`
  — ANY formula satisfying the semantic spec has exactly the
  Pitts/Ghilardi universal property of the uniform interpolant.  PROVED
  (via `soundness` + `completeness`).

Consequently the whole of uniform interpolation for PLL compresses into
ONE open statement per quantifier: DEFINABILITY (`semEx_definable`,
`semAll_definable`) — the existence of a p-free formula meeting the
spec.  That is where Ghilardi's method must survive the ∀∃ ◯-clause and
the fallible worlds, and where the finite canonical model
(`PLLFinComp.lean`, choice-free) is the intended engine: its worlds are
closure-total triples (Γ, Δ, Θ), finitely many per closure, and the
candidate interpolant is a disjunction of promise-aware world
descriptions.  See docs/semantic-ui-route.md for the full plan and the
relation to the realisability semantics.
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

/-! ## The semantic specifications of the two quantifiers -/

/-- `ψ` is a **semantic ∃p-quantifier** for `φ`: p-free, and forced
exactly at the worlds having a p-variant forcing `φ`.  (Persistence of
the right-hand side follows from i-forth, so the spec is coherent.) -/
def IsSemEx (p : String) (φ ψ : PLLFormula) : Prop :=
  p ∉ ψ.atoms ∧
  ∀ (M : ConstraintModel) (w : M.W),
    M.force w ψ ↔
      ∃ (N : ConstraintModel) (B : PBisim p M N) (w' : N.W),
        B.Z w w' ∧ N.force w' φ

/-- `ψ` is a **semantic ∀p-quantifier** for `φ`: p-free, and forced
exactly at the worlds ALL of whose futures' p-variants force `φ` (the
Rᵢ-guard makes the right-hand side hereditary). -/
def IsSemAll (p : String) (φ ψ : PLLFormula) : Prop :=
  p ∉ ψ.atoms ∧
  ∀ (M : ConstraintModel) (w : M.W),
    M.force w ψ ↔
      ∀ v, M.Ri w v →
        ∀ (N : ConstraintModel) (B : PBisim p M N) (v' : N.W),
          B.Z v v' → N.force v' φ

/-! ## The universal properties (PROVED): a spec-satisfier IS the
uniform interpolant -/

/-- `φ ⊢ ∃p.φ`. -/
theorem semEx_upper {p : String} {φ ψ : PLLFormula} (h : IsSemEx p φ ψ) :
    Nonempty (LaxND [φ] ψ) := by
  refine completeness ?_
  intro M w hw
  exact (h.2 M w).mpr ⟨M, ABisim.id _ M, w, rfl, hw φ (by simp)⟩

/-- **The ∃p adjunction**: for p-free `χ`,  `φ ⊢ χ  iff  ∃p.φ ⊢ χ`. -/
theorem semEx_adjunction {p : String} {φ ψ : PLLFormula}
    (h : IsSemEx p φ ψ) {χ : PLLFormula} (hχ : p ∉ χ.atoms) :
    Nonempty (LaxND [φ] χ) ↔ Nonempty (LaxND [ψ] χ) := by
  have hAχ : ∀ a ∈ χ.atoms, a ≠ p := fun a ha he => hχ (he ▸ ha)
  constructor
  · rintro ⟨d⟩
    refine completeness ?_
    intro M w hw
    obtain ⟨N, B, w', hZ, hφ'⟩ := (h.2 M w).mp (hw ψ (by simp))
    have hχ' : N.force w' χ := by
      refine soundness d N w' ?_
      intro ξ hξ
      simp only [List.mem_singleton] at hξ
      exact hξ ▸ hφ'
    exact (force_iff_of_bisim B hAχ hZ).mpr hχ'
  · rintro ⟨d⟩
    refine completeness ?_
    intro M w hw
    have hψw : M.force w ψ :=
      (h.2 M w).mpr ⟨M, ABisim.id _ M, w, rfl, hw φ (by simp)⟩
    refine soundness d M w ?_
    intro ξ hξ
    simp only [List.mem_singleton] at hξ
    exact hξ ▸ hψw

/-- `∀p.φ ⊢ φ`. -/
theorem semAll_lower {p : String} {φ ψ : PLLFormula} (h : IsSemAll p φ ψ) :
    Nonempty (LaxND [ψ] φ) := by
  refine completeness ?_
  intro M w hw
  exact (h.2 M w).mp (hw ψ (by simp)) w (M.refl_i w) M (ABisim.id _ M) w rfl

/-- **The ∀p adjunction**: for p-free `χ`,  `χ ⊢ φ  iff  χ ⊢ ∀p.φ`. -/
theorem semAll_adjunction {p : String} {φ ψ : PLLFormula}
    (h : IsSemAll p φ ψ) {χ : PLLFormula} (hχ : p ∉ χ.atoms) :
    Nonempty (LaxND [χ] φ) ↔ Nonempty (LaxND [χ] ψ) := by
  have hAχ : ∀ a ∈ χ.atoms, a ≠ p := fun a ha he => hχ (he ▸ ha)
  constructor
  · rintro ⟨d⟩
    refine completeness ?_
    intro M w hw
    refine (h.2 M w).mpr ?_
    intro v hv N B v' hZ
    have hχv : M.force v χ := M.force_hered hv (hw χ (by simp))
    have hχv' : N.force v' χ := (force_iff_of_bisim B hAχ hZ).mp hχv
    refine soundness d N v' ?_
    intro ξ hξ
    simp only [List.mem_singleton] at hξ
    exact hξ ▸ hχv'
  · rintro ⟨d⟩
    refine completeness ?_
    intro M w hw
    have hψw : M.force w ψ := by
      refine soundness d M w ?_
      intro ξ hξ
      simp only [List.mem_singleton] at hξ
      exact hξ ▸ hw χ (by simp)
    exact (h.2 M w).mp hψw w (M.refl_i w) M (ABisim.id _ M) w rfl

/-! ## The single open target per quantifier: DEFINABILITY

This is the Ghilardi step, and the whole of uniform interpolation for
PLL now rests on it.  Intended engine: the finite canonical model of
`PLLFinComp.lean` — worlds are closure-total triples (Γ, Δ, Θ),
finitely many per subformula closure, so the candidate ∃p-interpolant
is a finite disjunction of *promise-aware world descriptions* over the
closure of φ with p removed.  The two PLL-specific hazards, in order of
expected difficulty:
  (i) the ∀∃ ◯-clause: amalgamating two p-variants must complete
      Rm-witnesses coherently (this is where S4-style failure would
      enter; PLL's full heredity is the counter-pressure);
  (ii) fallible worlds: every formula is forced there, so descriptions
      must carry the Θ-promises (the ¬◯⋁Θ shape of the consistency
      formula) to pin the ◯-behaviour.
The 1-pv evidence (five-class state spaces, stabilisation far below
threshold) suggests the finite type structure is very tame. -/

/-- OPEN (Ghilardi step, ∃-side). -/
theorem semEx_definable (p : String) (φ : PLLFormula) :
    ∃ ψ, IsSemEx p φ ψ := by
  sorry

/-- OPEN (Ghilardi step, ∀-side). -/
theorem semAll_definable (p : String) (φ : PLLFormula) :
    ∃ ψ, IsSemAll p φ ψ := by
  sorry

end SemUI
end PLLND
