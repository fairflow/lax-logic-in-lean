/-
STAGE 3, part (b): the Thm 5.1 WRAPPER — the confluent semantic ∃p at
one variable and its adjunction over `DerivU`.

The specification `IsSemExC` is the confluent-class analogue of
`IsSemEx` (PLLSemUI.lean), stated over WEAKLY p-pure mutually
confluent models with the variant ranged over by the witness-form
p-variant link `PBisimWit` — exactly the output format of
`oneVarConfluentAmalgamationW`.  PROVED here:

* any spec-satisfier is a `DerivU` POST-INTERPOLANT: `φ ⊢ ψ`
  (`semExC_upper`) and, for every closed `χ`,
  `φ ⊢ χ ⟺ ψ ⊢ χ` (`semExC_adjunction`) — so a spec-satisfier is
  THE strongest closed `DerivU`-consequence of `φ`;
* the bridge from arbitrary confluent models to the weakly p-pure
  class is the purification functor `pPurify` (same frame, non-p
  atoms restricted to the fallible worlds), which preserves
  confluence, forcing of `{p}`-atom formulas, and fallibility.

EXISTENCE of a spec-satisfier (`SemExC1Definable`) is stated and left
OPEN: `oneVarConfluentAmalgamationW` is the hard half (it produces the
variant from a closed-agreement link at the entry budget), and with
`ClosedCollapse 6` the remaining step is exactly the realised-theory
analysis — whether the exact closed theories of `φ`-realisers form an
up-closed family (the candidate interpolant is the disjunction of
`bigAnd S` over realised theories `S`).  UI for full PCLL and for PLL
remain OPEN.
-/
import wip.pcll1pv_stage3
import LaxLogic.PLLConfluentComplete

namespace PLLND
open FinComp
namespace SemUI

open Classical

variable {p : String} {M : ConstraintModel}

/-- The identity witness-form p-variant. -/
def ABisimWit.idW (A : String → Prop) (M : ConstraintModel) :
    ABisimWit A M M where
  Z := Eq
  atoms := by rintro w _ rfl a _; exact Iff.rfl
  fall := by rintro w _ rfl; exact Iff.rfl
  iforth := by rintro w _ rfl v hv; exact .inl ⟨v, hv, rfl⟩
  iback := by rintro w _ rfl v' hv'; exact .inl ⟨v', hv', rfl⟩
  mwit := by
    rintro w _ rfl ψ ⟨u, hu, hψ⟩
    exact ⟨u, u, hu, hψ, hu, .inl rfl⟩
  mback := by rintro w _ rfl u' hu'; exact ⟨u', hu', .inl rfl⟩

/-! ## The purification functor -/

/-- **Purification**: same frame, non-p atoms restricted to the
fallible worlds (the least decoration `full_F` allows). -/
def pPurify (p : String) (M : ConstraintModel) : ConstraintModel where
  W := M.W
  Ri := M.Ri
  Rm := M.Rm
  F := M.F
  V a := if a = p then M.V p else M.F
  refl_i := M.refl_i
  trans_i := M.trans_i
  refl_m := M.refl_m
  trans_m := M.trans_m
  sub_mi := M.sub_mi
  hered_F := M.hered_F
  hered_V := by
    intro a w v h hw
    by_cases hp : a = p
    · subst hp
      rw [if_pos rfl] at hw ⊢
      exact M.hered_V h hw
    · rw [if_neg hp] at hw ⊢
      exact M.hered_F h hw
  full_F := by
    intro a w hw
    by_cases hp : a = p
    · subst hp
      rw [if_pos rfl]
      exact M.full_F hw
    · rw [if_neg hp]
      exact hw

theorem pPurify_confluent (h : MutuallyConfluent M) :
    MutuallyConfluent (pPurify p M) :=
  fun hm hi => h hm hi

theorem pPurify_pPureF : PPureF p (pPurify p M) := by
  intro a ha w hw
  rw [show (pPurify p M).V a = M.F from if_neg ha] at hw
  exact hw

/-- Purification preserves forcing of `{p}`-atom formulas. -/
theorem force_pPurify {χ : PLLFormula} (hA : ∀ a ∈ χ.atoms, a = p) :
    ∀ w : M.W, ((pPurify p M).force w χ ↔ M.force w χ) := by
  induction χ with
  | prop a =>
      intro w
      have ha : a = p := hA a (by simp [PLLFormula.atoms])
      subst ha
      show w ∈ (if a = a then M.V a else M.F) ↔ w ∈ M.V a
      rw [if_pos rfl]
  | falsePLL => exact fun w => Iff.rfl
  | and φ ψ ihφ ihψ =>
      intro w
      exact and_congr
        (ihφ (fun a ha => hA a (by simp [PLLFormula.atoms, ha])) w)
        (ihψ (fun a ha => hA a (by simp [PLLFormula.atoms, ha])) w)
  | or φ ψ ihφ ihψ =>
      intro w
      exact or_congr
        (ihφ (fun a ha => hA a (by simp [PLLFormula.atoms, ha])) w)
        (ihψ (fun a ha => hA a (by simp [PLLFormula.atoms, ha])) w)
  | ifThen φ ψ ihφ ihψ =>
      intro w
      have h1 : ∀ a ∈ φ.atoms, a = p :=
        fun a ha => hA a (by simp [PLLFormula.atoms, ha])
      have h2 : ∀ a ∈ ψ.atoms, a = p :=
        fun a ha => hA a (by simp [PLLFormula.atoms, ha])
      constructor
      · intro hf v hv hφ
        exact (ihψ h2 v).mp (hf v hv ((ihφ h1 v).mpr hφ))
      · intro hf v hv hφ
        exact (ihψ h2 v).mpr (hf v hv ((ihφ h1 v).mp hφ))
  | somehow φ ih =>
      intro w
      have h1 : ∀ a ∈ φ.atoms, a = p :=
        fun a ha => hA a (by simp [PLLFormula.atoms, ha])
      constructor
      · intro hf v hv
        obtain ⟨u, hu, hφ⟩ := hf v hv
        exact ⟨u, hu, (ih h1 u).mp hφ⟩
      · intro hf v hv
        obtain ⟨u, hu, hφ⟩ := hf v hv
        exact ⟨u, hu, (ih h1 u).mpr hφ⟩

/-! ## The specification and the interpolant properties -/

/-- **The confluent semantic ∃p** (1-pv form): closed, and forced at
exactly the worlds of weakly p-pure confluent models having a
CONFLUENT witness-form p-variant forcing `φ`. -/
def IsSemExC (p : String) (φ ψ : PLLFormula) : Prop :=
  (∀ a ∈ ψ.atoms, a ∈ (∅ : Finset String)) ∧
  ∀ (M : ConstraintModel), MutuallyConfluent M → PPureF p M →
    ∀ w : M.W,
      M.force w ψ ↔
        ∃ (N : ConstraintModel), MutuallyConfluent N ∧
          ∃ (B : PBisimWit p M N) (w' : N.W), B.Z w w' ∧ N.force w' φ

/-- Closed formulas have every-atom-is-p vacuously. -/
private theorem closed_to_p {ψ : PLLFormula}
    (h : ∀ a ∈ ψ.atoms, a ∈ (∅ : Finset String)) :
    ∀ a ∈ ψ.atoms, a = p :=
  fun a ha => absurd (h a ha) (by simp)

/-- `φ ⊢ ∃p.φ` over `DerivU`. -/
theorem semExC_upper {φ ψ : PLLFormula}
    (hφ1 : ∀ a ∈ φ.atoms, a = p) (h : IsSemExC p φ ψ) :
    ConfluentU.DerivU [φ] ψ := by
  rw [ConfluentU.derivU_iff_confluent_valid]
  intro C hc w hw
  have hφw : (pPurify p C).force w φ :=
    (force_pPurify hφ1 w).mpr (hw φ (by simp))
  have hψw : (pPurify p C).force w ψ :=
    (h.2 _ (pPurify_confluent hc) pPurify_pPureF w).mpr
      ⟨pPurify p C, pPurify_confluent hc,
        ABisimWit.idW _ _, w, rfl, hφw⟩
  exact (force_pPurify (closed_to_p h.1) w).mp hψw

/-- **The ∃p adjunction over `DerivU`**: for closed `χ`,
`φ ⊢ χ ⟺ ψ ⊢ χ` — a spec-satisfier is THE strongest closed
`DerivU`-consequence, i.e. the uniform post-interpolant. -/
theorem semExC_adjunction {φ ψ χ : PLLFormula}
    (hφ1 : ∀ a ∈ φ.atoms, a = p)
    (hχc : ∀ a ∈ χ.atoms, a ∈ (∅ : Finset String))
    (h : IsSemExC p φ ψ) :
    ConfluentU.DerivU [φ] χ ↔ ConfluentU.DerivU [ψ] χ := by
  constructor
  · intro hd
    rw [ConfluentU.derivU_iff_confluent_valid] at hd ⊢
    intro C hc w hw
    have hψp : (pPurify p C).force w ψ :=
      (force_pPurify (closed_to_p h.1) w).mpr (hw ψ (by simp))
    obtain ⟨N, hN, B, w', hZ, hφ'⟩ :=
      (h.2 _ (pPurify_confluent hc) pPurify_pPureF w).mp hψp
    have hχ' : N.force w' χ := by
      refine hd N hN w' ?_
      intro ξ hξ
      simp only [List.mem_singleton] at hξ
      exact hξ ▸ hφ'
    have hχw : (pPurify p C).force w χ :=
      (force_iff_of_witOut (pPurify_confluent hc) B
        (fun a ha => fun he => by simpa using hχc a ha) hZ).mpr hχ'
    exact (force_pPurify (closed_to_p hχc) w).mp hχw
  · intro hd
    rw [ConfluentU.derivU_iff_confluent_valid] at hd ⊢
    intro C hc w hw
    have hφw : (pPurify p C).force w φ :=
      (force_pPurify hφ1 w).mpr (hw φ (by simp))
    have hψw : (pPurify p C).force w ψ :=
      (h.2 _ (pPurify_confluent hc) pPurify_pPureF w).mpr
        ⟨pPurify p C, pPurify_confluent hc,
          ABisimWit.idW _ _, w, rfl, hφw⟩
    have hχw : (pPurify p C).force w χ := by
      refine hd (pPurify p C) (pPurify_confluent hc) w ?_
      intro ξ hξ
      simp only [List.mem_singleton] at hξ
      exact hξ ▸ hψw
    exact (force_pPurify (closed_to_p hχc) w).mp hχw

/-- **1-pv definability over the confluent class — OPEN.**  The
amalgamation half is `oneVarConfluentAmalgamationW`; the remaining
step is the realised-theory analysis (see the file header). -/
def SemExC1Definable (p : String) : Prop :=
  ∀ φ : PLLFormula, (∀ a ∈ φ.atoms, a = p) → ∃ ψ, IsSemExC p φ ψ

/-! ## Pins -/

/--
info: 'PLLND.SemUI.semExC_upper' depends on axioms: [propext, choice, Quot.sound]
-/
#guard_msgs in
#print axioms semExC_upper

/--
info: 'PLLND.SemUI.semExC_adjunction' depends on axioms: [propext, choice, Quot.sound]
-/
#guard_msgs in
#print axioms semExC_adjunction

end SemUI
end PLLND
