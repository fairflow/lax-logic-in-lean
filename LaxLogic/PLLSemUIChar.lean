import LaxLogic.PLLSemUIFrag

/-!
# Characters over the finite fragment

The pointwise ingredients of the repaired pillar 2 (their Theorem
4.7, in the escape form): for a world `w` and a representative list
`L` of the rank-bounded p-free fragment, the CHARACTERS

  θ⁺ := ⋀ { D ∈ L | w ⊩ D },    θ⁻ := ⋁ { D ∈ L | w ⊮ D }

capture `w`'s fragment type: `w` forces θ⁺ (`force_charPos`); a
NON-fallible `w` refutes θ⁻ (`not_force_charNeg` — a fallible world
forces everything, which is exactly the refuted obstruction and why
the escape clauses carve fallible targets out); and any world forcing
θ⁺ while refuting θ⁻ agrees with `w` on the whole list
(`agree_of_char`).  With `frag_reps_exist'` supplying `L`, these are
the raw material for `Z α := agreement at rank α` satisfying the
`LayeredBisimE` clauses — that induction is the recorded next step.
-/

open PLLFormula

namespace PLLND
namespace SemUI

attribute [local instance] Classical.propDecidable

/-! ## Semantic forcing of the finite connectives -/

/-- Forcing `bigAnd` is forcing every conjunct (the empty conjunction
is `⊤` = `⊥ → ⊥`, forced everywhere). -/
theorem force_bigAnd_iff (C : ConstraintModel) (w : C.W) :
    ∀ (T : List PLLFormula),
      (C.force w (bigAnd T) ↔ ∀ D ∈ T, C.force w D) := by
  intro T
  induction T with
  | nil =>
      simp only [bigAnd]
      constructor
      · intro _ D hD
        exact absurd hD (List.not_mem_nil)
      · intro _ v _ h
        exact h
  | cons φ l ih =>
      cases l with
      | nil =>
          simp only [bigAnd]
          constructor
          · intro h D hD
            rcases List.mem_singleton.mp hD with rfl
            exact h
          · intro h
            exact h φ (List.mem_singleton_self _)
      | cons ψ l' =>
          have hstep : C.force w (bigAnd (φ :: ψ :: l')) ↔
              C.force w φ ∧ C.force w (bigAnd (ψ :: l')) := Iff.rfl
          rw [hstep, ih]
          constructor
          · rintro ⟨h1, h2⟩ D hD
            rcases List.mem_cons.mp hD with rfl | hD
            · exact h1
            · exact h2 D hD
          · intro h
            exact ⟨h φ (List.mem_cons_self ..),
              fun D hD => h D (List.mem_cons_of_mem _ hD)⟩

/-- Forcing a member of a list forces its `bigOr`. -/
theorem force_bigOr_of_mem {C : ConstraintModel} {w : C.W}
    {S : List PLLFormula} {τ : PLLFormula} (hm : τ ∈ S)
    (hτ : C.force w τ) : C.force w (bigOr S) := by
  induction S with
  | nil => exact absurd hm (List.not_mem_nil)
  | cons σ S ih =>
      rcases List.mem_cons.mp hm with rfl | hm
      · exact Or.inl hτ
      · exact Or.inr (ih hm)

/-! ## Characters -/

/-- The positive character of `w` on the list `L`: the conjunction of
the members it forces. -/
noncomputable def charPos (C : ConstraintModel) (w : C.W)
    (L : List PLLFormula) : PLLFormula :=
  bigAnd (L.filter (fun D => decide (C.force w D)))

/-- The negative character: the disjunction of the members it
refutes. -/
noncomputable def charNeg (C : ConstraintModel) (w : C.W)
    (L : List PLLFormula) : PLLFormula :=
  bigOr (L.filter (fun D => decide (¬ C.force w D)))

/-- A world forces its own positive character. -/
theorem force_charPos (C : ConstraintModel) (w : C.W)
    (L : List PLLFormula) : C.force w (charPos C w L) := by
  rw [charPos, force_bigAnd_iff]
  intro D hD
  exact of_decide_eq_true (List.mem_filter.mp hD).2

/-- A NON-fallible world refutes its own negative character.  (The
fallibility hypothesis is essential — the machine-checked obstruction
`layered_of_frag_agree_refuted` lives exactly here.) -/
theorem not_force_charNeg (C : ConstraintModel) {w : C.W}
    (hw : w ∉ C.F) (L : List PLLFormula) :
    ¬ C.force w (charNeg C w L) := by
  intro h
  rcases force_bigOr_cases h with ⟨τ, hm, hτ⟩ | hF
  · exact of_decide_eq_true (List.mem_filter.mp hm).2 hτ
  · exact hw hF

/-- **Character transfer**: a world forcing `w`'s positive character
and refuting its negative character agrees with `w` on the whole
list. -/
theorem agree_of_char {C N : ConstraintModel} {w : C.W} {v : N.W}
    {L : List PLLFormula}
    (hpos : N.force v (charPos C w L))
    (hneg : ¬ N.force v (charNeg C w L)) :
    ∀ D ∈ L, (C.force w D ↔ N.force v D) := by
  intro D hD
  constructor
  · intro hf
    exact (force_bigAnd_iff N v _).mp hpos D
      (List.mem_filter.mpr ⟨hD, decide_eq_true hf⟩)
  · intro hf
    by_contra hnf
    exact hneg (force_bigOr_of_mem
      (List.mem_filter.mpr ⟨hD, decide_eq_true hnf⟩) hf)

/-! ## Axiom audit (pinned) -/

/--
info: 'PLLND.SemUI.agree_of_char' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms agree_of_char

/--
info: 'PLLND.SemUI.not_force_charNeg' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms not_force_charNeg

end SemUI
end PLLND
