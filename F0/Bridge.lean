import LaxLogic.PLL.SubTab.Translate

/-!
# Composing certified entailments

2026-10-22.  `⊢ A ↠ B` and `⊢ B ↠ C` give `⊢ A ↠ C`, by the natural
deduction rules (no completeness theorem).  Used by `F0/Named` to bridge
an op result outside R to its family name through one shared certified
bridge, instead of one large tableau per op cell.
-/

namespace F0

open PLLND PLLND.SubTab

/-- Transitivity of `⊢ · ↠ ·`. -/
theorem holds_trans {A B C : PLLFormula} (h₁ : Holds (A.ifThen B)) (h₂ : Holds (B.ifThen C)) :
    Holds (A.ifThen C) := by
  obtain ⟨d₁⟩ := rn (Γ' := [A]) (fun _ h => absurd h List.not_mem_nil) h₁
  obtain ⟨d₂⟩ := rn (Γ' := [A]) (fun _ h => absurd h List.not_mem_nil) h₂
  exact ⟨.impIntro (.impElim d₂ (.impElim d₁ (.iden List.mem_cons_self)))⟩

end F0

#axioms_within F0.holds_trans [propext, Quot.sound]
