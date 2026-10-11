import LaxLogic.PLL.Semantics.CtxCompleteness

/-!
# Theorem 6 in the paper's own wording

`Ctx.thm6` (`CtxCompleteness.lean`) is stated for *all* standard constraints
`C : StdCtx`, whose formulas `K`, `L` may be arbitrary PLL formulas, and with
PLL provability of `φ^C` on the right:

    PLL ⊢ φ  ⟺  ∀ C, PLL ⊢ φ^C.

The paper (Fairtlough–Mendler, TYPES 2000, Theorem 6) restricts `K`, `L` to IPL
formulas and has IPL provability on the right:

    PLL ⊢ φ  ⟺  ∀ C with K, L modality-free,  IPL ⊢ φ^C.

For the direction right-to-left this is the stronger statement, since its
hypothesis ranges over fewer constraints; it does not follow from `thm6` as
stated.  It does follow from the same proof: the completeness argument uses its
hypothesis at the single constraint `C0`, whose `K`, `L` are propositional
variables and disjunctions of them.  This file states and proves the paper's
form, `thm6_paper`.
-/

open PLLFormula

namespace PLLND
namespace Ctx

/-- A disjunction of IPL formulas is an IPL formula. -/
theorem bigOr_isIPL : ∀ {L : List PLLFormula}, (∀ q ∈ L, isIPL q) → isIPL (bigOr L)
  | [], _ => trivial
  | q :: _, h =>
      ⟨h q (List.mem_cons_self ..),
       bigOr_isIPL (fun r hr => h r (List.mem_cons_of_mem _ hr))⟩

/-- The constraint `C0` of Lemma 7 is an IPL constraint: its `K` are
propositional variables and its `L` disjunctions of propositional variables. -/
theorem C0_isIPL (M : ConstraintModel) [Fintype M.W] (φ₀ : PLLFormula) :
    CtxIsIPL (C0 M φ₀) := by
  intro p hp
  simp only [C0, List.mem_map] at hp
  obtain ⟨u, _, rfl⟩ := hp
  refine ⟨by simp [alpha], bigOr_isIPL ?_⟩
  intro q hq
  simp only [List.mem_map] at hq
  obtain ⟨v, _, rfl⟩ := hq
  simp [alpha]

/-- `IPLND` embeds into `LaxND` (local copy; `PLLND.IPLND.toLax` lives in
`UI/NoFallNF.lean`, which this file does not import). -/
theorem laxND_of_IPLND {Γ : List PLLFormula} {φ : PLLFormula}
    (h : IPLND Γ φ) : Nonempty (LaxND Γ φ) := by
  induction h with
  | iden h => exact ⟨.iden h⟩
  | falsoElim φ _ ih => obtain ⟨p⟩ := ih; exact ⟨.falsoElim φ p⟩
  | impIntro _ ih => obtain ⟨p⟩ := ih; exact ⟨.impIntro p⟩
  | impElim _ _ ih₁ ih₂ =>
      obtain ⟨p₁⟩ := ih₁; obtain ⟨p₂⟩ := ih₂; exact ⟨.impElim p₁ p₂⟩
  | andIntro _ _ ih₁ ih₂ =>
      obtain ⟨p₁⟩ := ih₁; obtain ⟨p₂⟩ := ih₂; exact ⟨.andIntro p₁ p₂⟩
  | andElim1 _ ih => obtain ⟨p⟩ := ih; exact ⟨.andElim1 p⟩
  | andElim2 _ ih => obtain ⟨p⟩ := ih; exact ⟨.andElim2 p⟩
  | orIntro1 _ ih => obtain ⟨p⟩ := ih; exact ⟨.orIntro1 p⟩
  | orIntro2 _ ih => obtain ⟨p⟩ := ih; exact ⟨.orIntro2 p⟩
  | orElim _ _ _ ih₀ ih₁ ih₂ =>
      obtain ⟨p₀⟩ := ih₀; obtain ⟨p₁⟩ := ih₁; obtain ⟨p₂⟩ := ih₂
      exact ⟨.orElim p₀ p₁ p₂⟩

/-- **Theorem 6, soundness direction, paper's form.**  If `φ` is a PLL theorem
then `φ^C` is an IPL theorem, for every IPL standard constraint `C`. -/
theorem thm6_soundness_paper (C : StdCtx) (hC : CtxIsIPL C) {φ : PLLFormula}
    (h : Nonempty (LaxND [] φ)) : IPLND [] (subC C φ) := by
  obtain ⟨p⟩ := thm6_soundness C h
  exact conservativity_IPL (subC_isIPL hC φ) (by simp) p

/-- **Theorem 6, completeness direction, paper's form.**  If `φ^C` is an IPL
theorem for every IPL standard constraint `C`, then `φ` is a PLL theorem.  The
hypothesis is used at the one constraint `C0`. -/
theorem thm6_completeness_paper {φ : PLLFormula}
    (h : ∀ C : StdCtx, CtxIsIPL C → IPLND [] (subC C φ)) : Nonempty (LaxND [] φ) := by
  by_contra hnp
  rw [finite_model_property] at hnp
  push Not at hnp
  obtain ⟨M, hMfin, w₀, hw₀⟩ := hnp
  haveI : Finite M.W := hMfin
  haveI : Fintype M.W := Fintype.ofFinite M.W
  have hcoin : (Mstar M φ).force w₀ φ ↔ M.force w₀ φ :=
    force_coincide M φ φ (fun w => nm_fresh M φ w) w₀
  have hMstar_nf : ¬ (Mstar M φ).force w₀ φ := fun hf => hw₀ (hcoin.mp hf)
  have hsub : ¬ (Mstar M φ).force w₀ (subC (C0 M φ) φ) := fun hf =>
    hMstar_nf ((force_subC_C0 M φ φ w₀).mp hf)
  obtain ⟨p⟩ := laxND_of_IPLND (h (C0 M φ) (C0_isIPL M φ))
  exact hsub (soundness_valid p (Mstar M φ) w₀)

/-- **Theorem 6** (Fairtlough–Mendler, TYPES 2000), in the paper's wording:
`φ` is a theorem of PLL iff `φ^C` is a theorem of IPL for every standard
constraint `C` built from IPL formulas. -/
theorem thm6_paper {φ : PLLFormula} :
    Nonempty (LaxND [] φ) ↔ ∀ C : StdCtx, CtxIsIPL C → IPLND [] (subC C φ) :=
  ⟨fun h C hC => thm6_soundness_paper C hC h, thm6_completeness_paper⟩

end Ctx
end PLLND

/-- info: 'PLLND.Ctx.thm6_soundness_paper' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.Ctx.thm6_soundness_paper

/-- info: 'PLLND.Ctx.thm6_paper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.Ctx.thm6_paper
