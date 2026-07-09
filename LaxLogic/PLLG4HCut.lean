import LaxLogic.PLLG4HCtr

/-!
# Toward cut for G4iLL″: pre-lemmas

The cut ladder (`docs/g4p-ladder.md`, revision 3) runs
`exfalso → cut_atom → K(w)`.  This file opens with the first:

* `exfalso_adm` — from `Γ ⇒ ⊥` conclude `Γ ⇒ E`.  No right rule
  concludes `⊥`, so a `⊥`-derivation is a tree of left rules over
  `botL` leaves; rebuild every rule at goal `E`, reusing the
  goal-independent auxiliary premises (`L→→`'s first premise, the two
  lax rules' box premises) verbatim.  Purely structural — no measure.
-/

open PLLFormula

namespace PLLND

namespace G4c

/-- **Ex falso, admissibly.** -/
theorem exfalso_adm : ∀ {n : Nat} {Γ : List PLLFormula} {G : PLLFormula},
    G4h n Γ G → G = falsePLL → ∀ (E : PLLFormula), G4c Γ E := by
  intro n Γ G d
  induction d with
  | init _ => intro e; cases e
  | botL h => intro _ E; exact botL h
  | andR _ _ _ _ => intro e; cases e
  | orR1 _ _ => intro e; cases e
  | orR2 _ _ => intro e; cases e
  | laxR _ _ => intro e; cases e
  | impR _ _ => intro e; cases e
  | laxL _ _ _ => intro e; cases e
  | andL h _ ih => intro e E; exact andL h (ih e E)
  | orL h _ _ ih₁ ih₂ => intro e E; exact orL h (ih₁ e E) (ih₂ e E)
  | impLProp h ha _ ih => intro e E; exact impLProp h ha (ih e E)
  | impLBot h _ ih => intro e E; exact impLBot h (ih e E)
  | impLAnd h _ ih => intro e E; exact impLAnd h (ih e E)
  | impLOr h _ ih => intro e E; exact impLOr h (ih e E)
  | impLImp h d₁ _ _ ih₂ => intro e E; exact impLImp h ⟨_, d₁⟩ (ih₂ e E)
  | impLLax h d₁ _ _ ih₂ => intro e E; exact impLLax h ⟨_, d₁⟩ (ih₂ e E)
  | impLLaxLax h hX d₁ _ _ ih₂ =>
      intro e E
      exact impLLaxLax h hX ⟨_, d₁⟩ (ih₂ e E)

/-- Ex falso at the working judgment. -/
theorem exfalso' {Γ : List PLLFormula} (d : G4c Γ falsePLL)
    (E : PLLFormula) : G4c Γ E := by
  obtain ⟨n, hd⟩ := d
  exact exfalso_adm hd rfl E

end G4c

end PLLND
