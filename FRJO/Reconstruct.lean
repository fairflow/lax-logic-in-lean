/-
# FRJ◯ W5, the base case — `Reconstruction` at a solo countermodel

The paper analysis (handoff, 2026-08-16): the stable zone must be the
world's THEORY restricted to `sfPlus`, and the four supporting lemmas
are `sf` transitivity, closure soundness (`clB` ⟹ derivable, via the
searcher's own certificate), fallible-solo triviality, and the Kripke
soundness composition.  All proved below, then the case itself:
`reconstruction_solo`.  The `join` case is the remaining campaign.
-/
import FRJO.Complete

namespace FRJO

open PLLND PLLFormula Classical

/-! ## sf transitivity and closure of the universe -/

theorem sf_trans : ∀ (ρ ψ φ : PLLFormula), ψ ∈ sf φ → φ ∈ sf ρ → ψ ∈ sf ρ := by
  intro ρ
  induction ρ with
  | prop a => intro ψ φ hψ hφ; simp [sf] at hφ; subst hφ; simpa [sf] using hψ
  | falsePLL => intro ψ φ hψ hφ; simp [sf] at hφ; subst hφ; simpa [sf] using hψ
  | and α β ihα ihβ =>
      intro ψ φ hψ hφ
      simp only [sf, List.mem_cons, List.mem_append] at hφ ⊢
      rcases hφ with rfl | hφ | hφ
      · simp only [sf, List.mem_cons, List.mem_append] at hψ; exact hψ
      · exact Or.inr (Or.inl (ihα ψ φ hψ hφ))
      · exact Or.inr (Or.inr (ihβ ψ φ hψ hφ))
  | or α β ihα ihβ =>
      intro ψ φ hψ hφ
      simp only [sf, List.mem_cons, List.mem_append] at hφ ⊢
      rcases hφ with rfl | hφ | hφ
      · simp only [sf, List.mem_cons, List.mem_append] at hψ; exact hψ
      · exact Or.inr (Or.inl (ihα ψ φ hψ hφ))
      · exact Or.inr (Or.inr (ihβ ψ φ hψ hφ))
  | ifThen α β ihα ihβ =>
      intro ψ φ hψ hφ
      simp only [sf, List.mem_cons, List.mem_append] at hφ ⊢
      rcases hφ with rfl | hφ | hφ
      · simp only [sf, List.mem_cons, List.mem_append] at hψ; exact hψ
      · exact Or.inr (Or.inl (ihα ψ φ hψ hφ))
      · exact Or.inr (Or.inr (ihβ ψ φ hψ hφ))
  | somehow α ihα =>
      intro ψ φ hψ hφ
      simp only [sf, List.mem_cons] at hφ ⊢
      rcases hφ with rfl | hφ
      · simp only [sf, List.mem_cons] at hψ; exact hψ
      · exact Or.inr (ihα ψ φ hψ hφ)

theorem sfPlus_closed {G : Cell} {φ ψ : PLLFormula}
    (hφ : φ ∈ sfPlus G) (hψ : ψ ∈ sf φ) : ψ ∈ sfPlus G := by
  simp only [sfPlus, List.mem_eraseDups, List.mem_flatMap] at hφ ⊢
  obtain ⟨ρ, hρ, hm⟩ := hφ
  exact ⟨ρ, hρ, sf_trans ρ ψ φ hψ hm⟩

/-! ## The closure is sound -/

theorem clB_sound {G : Cell} {b : Nat} {Δ : List PLLFormula}
    {φ : PLLFormula} (h : φ ∈ clB G b Δ) : Nonempty (LaxND Δ φ) := by
  simp only [clB, List.mem_filter] at h
  obtain ⟨-, h⟩ := h
  cases hd : Search.decide { findBudget := some b, emitClosureCap := 0 } Δ φ with
  | proved t => exact Search.proved_sound t
  | refuted w => rw [hd] at h; simp at h
  | unknown => rw [hd] at h; simp at h

/-! ## Fallible solo worlds force everything -/

theorem solo_fal_forces {V₀ : String → Prop} {fal : Prop}
    {hfull : fal → ∀ a, V₀ a} (hf : fal) (φ : PLLFormula) :
    (Reject.solo V₀ fal hfull).force () φ := by
  induction φ with
  | prop a => exact hfull hf a
  | falsePLL => exact hf
  | and φ ψ ihφ ihψ => exact ⟨ihφ, ihψ⟩
  | or φ ψ ihφ _ => exact Or.inl ihφ
  | ifThen φ ψ _ ihψ => intro v _ _; cases v; exact ihψ
  | somehow φ ihφ => intro v _; cases v; exact ⟨(), True.intro, ihφ⟩

/-! ## The base case -/

theorem reconstruction_solo (b : Nat) (Γ : List PLLFormula) (C : PLLFormula)
    (V₀ : String → Prop) (fal : Prop) (hfull : fal → ∀ a, V₀ a)
    (hΓ : ∀ φ ∈ Γ, (Reject.solo V₀ fal hfull).force () φ)
    (hC : ¬ (Reject.solo V₀ fal hfull).force () C) :
    ∃ S : Reg ⟨Γ, C⟩, S.goal = C ∧ Γ ⊆ S.stable ∧
      Nonempty (FRJD ⟨Γ, C⟩ b S) := by
  classical
  set M := Reject.solo V₀ fal hfull with hM
  -- the world is infallible, or it would force C
  have hnf : ¬ fal := fun hf => hC (solo_fal_forces hf C)
  -- the stable zone: the world's theory inside the universe
  set St : List PLLFormula :=
    (sfPlus ⟨Γ, C⟩).filter (fun φ => decide (M.force () φ)) with hSt
  have hStMem : ∀ {φ}, φ ∈ St ↔ (φ ∈ sfPlus ⟨Γ, C⟩ ∧ M.force () φ) := by
    intro φ
    simp [hSt, List.mem_filter]
  refine ⟨⟨St, C⟩, rfl, ?_, ⟨?_⟩⟩
  · intro φ hφ
    exact hStMem.mpr ⟨sfPlus_ctx _ φ hφ, hΓ φ hφ⟩
  · refine .world [] [] false (fun K hK => absurd hK (List.not_mem_nil)) ?_
    -- worldOK, conjunct by conjunct
    simp only [worldOK, Bool.and_eq_true, List.all_nil, List.zip_nil_left,
      List.all_eq_true, Bool.or_eq_false_iff, Bool.not_eq_true']
    refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · -- St inside the universe
      intro φ hφ
      simpa using List.elem_iff.mpr (hStMem.mp hφ).1
    · simpa using List.elem_iff.mpr (sfPlus_goal ⟨Γ, C⟩)
    · -- heredity over no kids: discharged by simp already
      trivial
    · -- ◯-positive: a forced box at a solo world forces its body here
      intro φ hφ
      match φ with
      | .prop _ | .falsePLL | .and _ _ | .or _ _ | .ifThen _ _ => simp
      | .somehow A =>
          simp only [List.any_nil, Bool.or_false, Bool.false_or]
          obtain ⟨hu, hfc⟩ := hStMem.mp hφ
          have hA : M.force () A :=
            (Reject.solo_force_somehow V₀ fal hfull A).mp hfc
          exact List.elem_iff.mpr (hStMem.mpr
            ⟨sfPlus_closed hu (by simp [sf, sf_self]), hA⟩)
    · -- the goal is not in the closure: closure-membership would make
      -- it derivable, hence forced (Kripke soundness), against hC
      cases hcl : (clB ⟨Γ, C⟩ b St).contains C
      · rfl
      · exfalso
        have hmem : C ∈ clB ⟨Γ, C⟩ b St := List.elem_iff.mp hcl
        obtain ⟨d⟩ := clB_sound hmem
        exact hC (soundness d M () (fun γ hγ => (hStMem.mp hγ).2))
    · -- a boxed goal: refuted at the root's own (reflexive) cone
      match C, hC with
      | .prop _, _ | .falsePLL, _ | .and _ _, _ | .or _ _, _
      | .ifThen _ _, _ => simp
      | .somehow A, hC =>
          simp only [Bool.and_eq_true, List.all_nil, and_true,
            Bool.not_eq_true']
          refine ⟨trivial, ?_⟩
          cases hcl : (clB ⟨Γ, .somehow A⟩ b St).contains A
          · rfl
          · exfalso
            have hmem : A ∈ clB ⟨Γ, .somehow A⟩ b St := List.elem_iff.mp hcl
            obtain ⟨d⟩ := clB_sound hmem
            have hA : M.force () A :=
              soundness d M () (fun γ hγ => (hStMem.mp hγ).2)
            exact hC ((Reject.solo_force_somehow V₀ fal hfull A).mpr hA)

/-! ## Pins -/

/-- info: 'FRJO.reconstruction_solo' depends on axioms: [propext, choice, Quot.sound] -/
#guard_msgs in
#print axioms reconstruction_solo

end FRJO
