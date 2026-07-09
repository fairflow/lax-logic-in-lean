import LaxLogic.PLLG4HStr

/-!
# Summit base camp: atomic contraction for G4iLL″

Contraction of an *atom* is provable by a plain structural induction,
height-preservingly: atoms are never the principal formula of a left
rule (only `init`'s conclusion and `Lp→`'s side condition mention
them), so both copies travel into every premise and the only content
is permutation bookkeeping.  This is the standalone base that the cut
theorem's `init` case consumes; full contraction comes after cut, per
the acyclic ladder of `docs/g4p-ladder.md`.
-/

open PLLFormula

namespace PLLND

namespace G4h

/-- Push a fresh head past two designated copies. -/
private theorem push2 {x q : PLLFormula} {Γ : List PLLFormula} :
    (x :: q :: q :: Γ).Perm (q :: q :: x :: Γ) :=
  (List.Perm.swap q x _).trans ((List.Perm.swap q x Γ).cons q)

/-- Push a block of new formulas past the two copies. -/
private theorem pushL (L : List PLLFormula) {q : PLLFormula}
    {Δ Γ₀ : List PLLFormula} (hΔ : Δ.Perm (q :: q :: Γ₀)) :
    (L ++ Δ).Perm (q :: q :: (L ++ Γ₀)) :=
  (hΔ.append_left L).trans (List.perm_middle.trans (List.perm_middle.cons q))

/-- Cross-split: a context that exposes both a principal `P` and the
two copies of `q` (with `P ≠ q`) admits a common remainder. -/
private theorem cross_split {P q : PLLFormula} {Γ' Δ Γ : List PLLFormula}
    (h : Γ'.Perm (P :: Δ)) (hp : Γ'.Perm (q :: q :: Γ)) (hne : P ≠ q) :
    ∃ Γ₀, Δ.Perm (q :: q :: Γ₀) ∧ Γ.Perm (P :: Γ₀) := by
  rcases G4.perm_cons_cases (h.symm.trans hp) with ⟨e, _⟩ | ⟨l₁, hΔ, hm⟩
  · exact absurd e hne
  rcases G4.perm_cons_cases hm with ⟨e, _⟩ | ⟨l₂, hΓ, hl₁⟩
  · exact absurd e.symm hne
  exact ⟨l₂, hΔ.trans (hl₁.cons q), hΓ⟩

/-- **Height-preserving contraction of an atom.** -/
theorem contract_atom {p : String} :
    ∀ {n : Nat} {Γ' : List PLLFormula} {E : PLLFormula}, G4h n Γ' E →
    ∀ {Γ : List PLLFormula}, Γ'.Perm (prop p :: prop p :: Γ) →
    G4h n (prop p :: Γ) E := by
  intro n Γ' E d
  induction d with
  | init h =>
      intro Γ hp
      rcases List.mem_cons.mp (hp.subset h) with e | h'
      · exact .init (by rw [e]; exact .head _)
      rcases List.mem_cons.mp h' with e | h''
      · exact .init (by rw [e]; exact .head _)
      · exact .init (.tail _ h'')
  | botL h =>
      intro Γ hp
      rcases List.mem_cons.mp (hp.subset h) with e | h'
      · cases e
      rcases List.mem_cons.mp h' with e | h''
      · cases e
      · exact .botL (.tail _ h'')
  | andR _ _ ih₁ ih₂ => intro Γ hp; exact .andR (ih₁ hp) (ih₂ hp)
  | orR1 _ ih => intro Γ hp; exact .orR1 (ih hp)
  | orR2 _ ih => intro Γ hp; exact .orR2 (ih hp)
  | laxR _ ih => intro Γ hp; exact .laxR (ih hp)
  | @impR _ _ A _ _ ih =>
      intro Γ hp
      exact .impR ((ih ((hp.cons A).trans push2)).perm (List.Perm.swap _ _ _))
  | @andL _ _ Δ A B _ h _ ih =>
      intro Γ hp
      obtain ⟨Γ₀, hΔ, hΓ⟩ := cross_split h hp (by intro e; cases e)
      exact .andL ((hΓ.cons _).trans (List.Perm.swap _ _ _))
        ((ih (pushL [A, B] hΔ)).perm (List.perm_middle (l₁ := [A, B])).symm)
  | @orL _ _ Δ A B _ h _ _ ih₁ ih₂ =>
      intro Γ hp
      obtain ⟨Γ₀, hΔ, hΓ⟩ := cross_split h hp (by intro e; cases e)
      exact .orL ((hΓ.cons _).trans (List.Perm.swap _ _ _))
        ((ih₁ (pushL [A] hΔ)).perm (List.perm_middle (l₁ := [A])).symm)
        ((ih₂ (pushL [B] hΔ)).perm (List.perm_middle (l₁ := [B])).symm)
  | @laxL _ _ A _ h _ ih =>
      intro Γ hp
      have h' : A.somehow ∈ prop p :: Γ := by
        rcases List.mem_cons.mp (hp.subset h) with e | h'
        · cases e
        rcases List.mem_cons.mp h' with e | h''
        · cases e
        · exact .tail _ h''
      exact .laxL h'
        ((ih ((hp.cons A).trans push2)).perm (List.Perm.swap _ _ _))
  | @impLProp _ _ Δ a B _ h ha _ ih =>
      intro Γ hp
      obtain ⟨Γ₀, hΔ, hΓ⟩ := cross_split h hp (by intro e; cases e)
      have ha' : prop a ∈ prop p :: Γ₀ := by
        rcases List.mem_cons.mp (hΔ.subset ha) with e | h'
        · rw [e]; exact .head _
        rcases List.mem_cons.mp h' with e | h''
        · rw [e]; exact .head _
        · exact .tail _ h''
      exact .impLProp ((hΓ.cons _).trans (List.Perm.swap _ _ _)) ha'
        ((ih (pushL [B] hΔ)).perm (List.perm_middle (l₁ := [B])).symm)
  | @impLBot _ _ Δ B _ h _ ih =>
      intro Γ hp
      obtain ⟨Γ₀, hΔ, hΓ⟩ := cross_split h hp (by intro e; cases e)
      exact .impLBot ((hΓ.cons _).trans (List.Perm.swap _ _ _)) (ih hΔ)
  | @impLAnd _ _ Δ A B D _ h _ ih =>
      intro Γ hp
      obtain ⟨Γ₀, hΔ, hΓ⟩ := cross_split h hp (by intro e; cases e)
      exact .impLAnd ((hΓ.cons _).trans (List.Perm.swap _ _ _))
        ((ih (pushL [A.ifThen (B.ifThen D)] hΔ)).perm
          (List.perm_middle (l₁ := [A.ifThen (B.ifThen D)])).symm)
  | @impLOr _ _ Δ A B D _ h _ ih =>
      intro Γ hp
      obtain ⟨Γ₀, hΔ, hΓ⟩ := cross_split h hp (by intro e; cases e)
      exact .impLOr ((hΓ.cons _).trans (List.Perm.swap _ _ _))
        ((ih (pushL [A.ifThen D, B.ifThen D] hΔ)).perm
          (List.perm_middle (l₁ := [A.ifThen D, B.ifThen D])).symm)
  | @impLImp _ _ Δ A B D _ h _ _ ih₁ ih₂ =>
      intro Γ hp
      obtain ⟨Γ₀, hΔ, hΓ⟩ := cross_split h hp (by intro e; cases e)
      exact .impLImp ((hΓ.cons _).trans (List.Perm.swap _ _ _))
        ((ih₁ (pushL [B.ifThen D] hΔ)).perm
          (List.perm_middle (l₁ := [B.ifThen D])).symm)
        ((ih₂ (pushL [D] hΔ)).perm (List.perm_middle (l₁ := [D])).symm)
  | @impLLax _ _ Δ A B _ h _ _ ih₁ ih₂ =>
      intro Γ hp
      obtain ⟨Γ₀, hΔ, hΓ⟩ := cross_split h hp (by intro e; cases e)
      exact .impLLax ((hΓ.cons _).trans (List.Perm.swap _ _ _))
        (ih₁ hΔ)
        ((ih₂ (pushL [B] hΔ)).perm (List.perm_middle (l₁ := [B])).symm)
  | @impLLaxLax _ _ Δ A B X _ h hX _ _ ih₁ ih₂ =>
      intro Γ hp
      obtain ⟨Γ₀, hΔ, hΓ⟩ := cross_split h hp (by intro e; cases e)
      have hX' : X.somehow ∈ prop p :: Γ₀ := by
        rcases List.mem_cons.mp (hΔ.subset hX) with e | h'
        · cases e
        rcases List.mem_cons.mp h' with e | h''
        · cases e
        · exact .tail _ h''
      exact .impLLaxLax ((hΓ.cons _).trans (List.Perm.swap _ _ _)) hX'
        ((ih₁ ((hp.cons X).trans push2)).perm (List.Perm.swap _ _ _))
        ((ih₂ (pushL [B] hΔ)).perm (List.perm_middle (l₁ := [B])).symm)

end G4h

end PLLND
