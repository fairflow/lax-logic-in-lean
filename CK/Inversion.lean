import CK.Height

/-!
# `CK.Inversion` — the invertible left rules of G4CK

The inversion lemmas behind the contraction proof of van der Giessen and
Shillito, arXiv:2602.16880v2, §3, which the paper leaves to its Rocq
development and to Dyckhoff and Negri (2000).  Rocq, in
`theories/Sequent/G4CK/CKSequentProps.v` (commit `cd09fce`): `AndL_rev`,
`OrL_rev`, `TopL_rev`, `ImpLVar_rev`, `ImpLAnd_rev`, `ImpLOr_rev`,
`ImpLImp_prev`, `ImpLBox_prev`, `ImpLDiam_prev`, and `ImpR_rev`.

They are one theorem here, `G4CKh.inv`, over the relation `Inv P L` ("an
antecedent occurrence of `P` may be replaced by the formulas `L`"), and they
preserve the height bound.  The organisation is that of
`LaxLogic/PLL/G4/G4HInv.lean`.
-/

namespace CK

open scoped Form

/-- Two ways of exposing a head: the heads agree, or each tail contains the
other head. -/
theorem perm_cons_cases {a b : Form} {l m : List Form} (h : (a :: l).Perm (b :: m)) :
    (a = b ∧ l.Perm m) ∨ ∃ l', l.Perm (b :: l') ∧ m.Perm (a :: l') := by
  by_cases hab : a = b
  · subst hab; exact .inl ⟨rfl, h.cons_inv⟩
  · have hb : b ∈ l := by
      rcases List.mem_cons.1 (h.symm.subset List.mem_cons_self) with e | hb
      · exact absurd e.symm hab
      · exact hb
    obtain ⟨l', hl'⟩ := exists_perm_cons_of_mem hb
    refine .inr ⟨l', hl', ?_⟩
    -- b :: m ~ a :: l ~ a :: b :: l' ~ b :: a :: l'
    exact ((h.symm.trans (hl'.cons a)).trans (List.Perm.swap b a _)).cons_inv

/-- `L ++ (S ++ X) ~ S ++ (L ++ X)`. -/
theorem perm_shuffle (L S X : List Form) : (L ++ (S ++ X)).Perm (S ++ (L ++ X)) := by
  rw [← List.append_assoc, ← List.append_assoc]
  exact List.perm_append_comm.append_right X

theorem unbox_append : ∀ L Δ : List Form, unbox (L ++ Δ) = unbox L ++ unbox Δ
  | [], _ => rfl
  | .var _ :: L, Δ => unbox_append L Δ
  | .bot :: L, Δ => unbox_append L Δ
  | .and _ _ :: L, Δ => unbox_append L Δ
  | .or _ _ :: L, Δ => unbox_append L Δ
  | .imp _ _ :: L, Δ => unbox_append L Δ
  | .dia _ :: L, Δ => unbox_append L Δ
  | .box φ :: L, Δ => congrArg (φ :: ·) (unbox_append L Δ)

/-- `Inv P L`: an antecedent occurrence of `P` may be replaced by the
formulas `L`, at no cost in height (`G4CKh.inv`). -/
inductive Inv : Form → List Form → Prop
  /-- Rocq `AndL_rev`. -/
  | and (φ ψ : Form) : Inv (φ ⋏ ψ) [φ, ψ]
  /-- Rocq `OrL_rev`, first component. -/
  | or₁ (φ ψ : Form) : Inv (φ ⋎ ψ) [φ]
  /-- Rocq `OrL_rev`, second component. -/
  | or₂ (φ ψ : Form) : Inv (φ ⋎ ψ) [ψ]
  /-- Rocq `ImpLVar_rev`. -/
  | impVar (p : Nat) (φ : Form) : Inv (Form.var p ⟶ φ) [φ]
  /-- Rocq `TopL_rev`. -/
  | impBot (φ : Form) : Inv (⊥' ⟶ φ) []
  /-- Rocq `ImpLAnd_rev`. -/
  | impAnd (φ ψ χ : Form) : Inv ((φ ⋏ ψ) ⟶ χ) [φ ⟶ (ψ ⟶ χ)]
  /-- Rocq `ImpLOr_rev`. -/
  | impOr (φ ψ χ : Form) : Inv ((φ ⋎ ψ) ⟶ χ) [φ ⟶ χ, ψ ⟶ χ]
  /-- Rocq `ImpLImp_prev`. -/
  | impImp (φ ψ χ : Form) : Inv ((φ ⟶ ψ) ⟶ χ) [χ]
  /-- Rocq `ImpLBox_prev`. -/
  | impBox (φ ψ : Form) : Inv ((□φ) ⟶ ψ) [ψ]
  /-- Rocq `ImpLDiam_prev`. -/
  | impDia (φ ψ : Form) : Inv ((◇φ) ⟶ ψ) [ψ]

/-- An invertible formula is not a box. -/
theorem Inv.unbox_cons {P : Form} {L : List Form} (h : Inv P L) (Δ : List Form) :
    unbox (P :: Δ) = unbox Δ := by
  cases h <;> rfl

namespace G4CKh

/-- The modal premise survives an inversion in the conclusion: `□⁻¹` drops
the inverted formula, and `□⁻¹L` is added by weakening. -/
private theorem unbox_inv {n : Nat} {Θ l' L pre : List Form} {P φ : Form}
    (hInv : Inv P L) (hΘ : Θ.Perm (P :: l')) (d : G4CKh n (pre ++ unbox Θ) φ) :
    G4CKh n (pre ++ unbox (L ++ l')) φ := by
  have h₁ : (unbox Θ).Perm (unbox l') := by
    have := unbox_perm hΘ
    rwa [hInv.unbox_cons] at this
  rw [unbox_append]
  exact ((d.perm (h₁.append_left pre)).weakens (unbox L)).perm (perm_shuffle _ _ _)

/-- **Master inversion, height-preserving.** -/
theorem inv {n : Nat} {Γ : List Form} {C : Form} (d : G4CKh n Γ C) :
    ∀ {P : Form} {L Δ : List Form}, Inv P L → Γ.Perm (P :: Δ) → G4CKh n (L ++ Δ) C := by
  induction d with
  | botL h =>
      intro P L Δ hInv hp
      rcases List.mem_cons.1 (hp.subset h) with e | h'
      · subst e; cases hInv
      · exact .botL (List.mem_append.2 (.inr h'))
  | idP h =>
      intro P L Δ hInv hp
      rcases List.mem_cons.1 (hp.subset h) with e | h'
      · subst e; cases hInv
      · exact .idP (List.mem_append.2 (.inr h'))
  | andR _ _ ih₁ ih₂ => intro P L Δ hInv hp; exact .andR (ih₁ hInv hp) (ih₂ hInv hp)
  | orR1 _ ih => intro P L Δ hInv hp; exact .orR1 (ih hInv hp)
  | orR2 _ ih => intro P L Δ hInv hp; exact .orR2 (ih hInv hp)
  | @impR _ _ A₀ B₀ _ ih =>
      intro P L Δ hInv hp
      exact .impR ((ih hInv ((hp.cons A₀).trans (List.Perm.swap P A₀ Δ))).perm
        List.perm_middle)
  | @andL _ _ Θ A' B' _ h d₁ ih₁ =>
      intro P L Δ hInv hp
      rcases perm_cons_cases (h.symm.trans hp) with ⟨e, hΘΔ⟩ | ⟨l', hΘ, hΔ⟩
      · subst e; cases hInv
        exact (d₁.perm ((hΘΔ.cons B').cons A')).succ_mono
      · exact .andL ((hΔ.append_left L).trans List.perm_middle)
          ((ih₁ hInv ((hΘ.append_left [A', B']).trans List.perm_middle)).perm
            (perm_shuffle L [A', B'] l'))
  | @orL _ _ Θ A' B' _ h d₁ d₂ ih₁ ih₂ =>
      intro P L Δ hInv hp
      rcases perm_cons_cases (h.symm.trans hp) with ⟨e, hΘΔ⟩ | ⟨l', hΘ, hΔ⟩
      · subst e
        cases hInv with
        | or₁ _ _ => exact (d₁.perm (hΘΔ.cons A')).succ_mono
        | or₂ _ _ => exact (d₂.perm (hΘΔ.cons B')).succ_mono
      · exact .orL ((hΔ.append_left L).trans List.perm_middle)
          ((ih₁ hInv ((hΘ.append_left [A']).trans List.perm_middle)).perm
            (perm_shuffle L [A'] l'))
          ((ih₂ hInv ((hΘ.append_left [B']).trans List.perm_middle)).perm
            (perm_shuffle L [B'] l'))
  | @impAndL _ _ Θ A₁ B₁ D₁ _ h d₁ ih₁ =>
      intro P L Δ hInv hp
      rcases perm_cons_cases (h.symm.trans hp) with ⟨e, hΘΔ⟩ | ⟨l', hΘ, hΔ⟩
      · subst e; cases hInv
        exact (d₁.perm (hΘΔ.cons _)).succ_mono
      · exact .impAndL ((hΔ.append_left L).trans List.perm_middle)
          ((ih₁ hInv ((hΘ.append_left [A₁ ⟶ (B₁ ⟶ D₁)]).trans List.perm_middle)).perm
            (perm_shuffle L [A₁ ⟶ (B₁ ⟶ D₁)] l'))
  | @impOrL _ _ Θ A₁ B₁ D₁ _ h d₁ ih₁ =>
      intro P L Δ hInv hp
      rcases perm_cons_cases (h.symm.trans hp) with ⟨e, hΘΔ⟩ | ⟨l', hΘ, hΔ⟩
      · subst e; cases hInv
        exact (d₁.perm ((hΘΔ.cons _).cons _)).succ_mono
      · exact .impOrL ((hΔ.append_left L).trans List.perm_middle)
          ((ih₁ hInv ((hΘ.append_left [A₁ ⟶ D₁, B₁ ⟶ D₁]).trans List.perm_middle)).perm
            (perm_shuffle L [A₁ ⟶ D₁, B₁ ⟶ D₁] l'))
  | @impVarL _ _ Θ a' B' _ h ha d₁ ih₁ =>
      intro P L Δ hInv hp
      rcases perm_cons_cases (h.symm.trans hp) with ⟨e, hΘΔ⟩ | ⟨l', hΘ, hΔ⟩
      · subst e; cases hInv
        exact (d₁.perm (hΘΔ.cons B')).succ_mono
      · have ha' : Form.var a' ∈ L ++ l' := by
          rcases List.mem_cons.1 (hΘ.subset ha) with e | h'
          · subst e; cases hInv
          · exact List.mem_append.2 (.inr h')
        exact .impVarL ((hΔ.append_left L).trans List.perm_middle) ha'
          ((ih₁ hInv ((hΘ.append_left [B']).trans List.perm_middle)).perm
            (perm_shuffle L [B'] l'))
  | @impImpL _ _ Θ A₁ B₁ D₁ _ h d₁ d₂ ih₁ ih₂ =>
      intro P L Δ hInv hp
      rcases perm_cons_cases (h.symm.trans hp) with ⟨e, hΘΔ⟩ | ⟨l', hΘ, hΔ⟩
      · subst e; cases hInv
        exact (d₂.perm (hΘΔ.cons _)).succ_mono
      · exact .impImpL ((hΔ.append_left L).trans List.perm_middle)
          ((ih₁ hInv ((hΘ.append_left [B₁ ⟶ D₁]).trans List.perm_middle)).perm
            (perm_shuffle L [B₁ ⟶ D₁] l'))
          ((ih₂ hInv ((hΘ.append_left [D₁]).trans List.perm_middle)).perm
            (perm_shuffle L [D₁] l'))
  | @boxR _ Γ' A₁ d₁ _ =>
      intro P L Δ hInv hp
      exact .boxR (unbox_inv (pre := []) hInv hp d₁)
  | @impBoxL _ _ Θ A₁ B₁ _ h d₁ d₂ _ ih₂ =>
      intro P L Δ hInv hp
      rcases perm_cons_cases (h.symm.trans hp) with ⟨e, hΘΔ⟩ | ⟨l', hΘ, hΔ⟩
      · subst e; cases hInv
        exact (d₂.perm (hΘΔ.cons _)).succ_mono
      · exact .impBoxL ((hΔ.append_left L).trans List.perm_middle)
          (unbox_inv (pre := []) hInv hΘ d₁)
          ((ih₂ hInv ((hΘ.append_left [B₁]).trans List.perm_middle)).perm
            (perm_shuffle L [B₁] l'))
  | @impDiaL _ _ Θ G₁ A₁ B₁ _ h hγ d₁ d₂ _ ih₂ =>
      intro P L Δ hInv hp
      rcases perm_cons_cases (h.symm.trans hp) with ⟨e, hΘΔ⟩ | ⟨l', hΘ, hΔ⟩
      · subst e; cases hInv
        exact (d₂.perm (hΘΔ.cons _)).succ_mono
      · have hγ' : (◇G₁) ∈ L ++ l' := by
          rcases List.mem_cons.1 (hΘ.subset hγ) with e | h'
          · subst e; cases hInv
          · exact List.mem_append.2 (.inr h')
        exact .impDiaL ((hΔ.append_left L).trans List.perm_middle) hγ'
          (unbox_inv (pre := [G₁]) hInv hΘ d₁)
          ((ih₂ hInv ((hΘ.append_left [B₁]).trans List.perm_middle)).perm
            (perm_shuffle L [B₁] l'))
  | @diaL _ _ Θ A₁ B₁ h d₁ _ =>
      intro P L Δ hInv hp
      rcases perm_cons_cases (h.symm.trans hp) with ⟨e, _⟩ | ⟨l', hΘ, hΔ⟩
      · subst e; cases hInv
      · exact .diaL ((hΔ.append_left L).trans List.perm_middle)
          (unbox_inv (pre := [A₁]) hInv hΘ d₁)

/-- `(→R)` is invertible, height-preserving.  Rocq `ImpR_rev`. -/
theorem impR_inv {n : Nat} {Γ : List Form} {G : Form} (d : G4CKh n Γ G) :
    ∀ {φ ψ : Form}, G = (φ ⟶ ψ) → G4CKh n (φ :: Γ) ψ := by
  induction d with
  | botL h => intro φ ψ _; exact .botL (List.mem_cons_of_mem _ h)
  | idP h => intro φ ψ e; cases e
  | andR _ _ _ _ => intro φ ψ e; cases e
  | orR1 _ _ => intro φ ψ e; cases e
  | orR2 _ _ => intro φ ψ e; cases e
  | boxR _ _ => intro φ ψ e; cases e
  | diaL _ _ _ => intro φ ψ e; cases e
  | impR d _ => intro φ ψ e; cases e; exact d.succ_mono
  | andL h _ ih =>
      intro φ ψ e
      exact .andL ((h.cons φ).trans (List.Perm.swap _ _ _))
        ((ih e).perm ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons _)))
  | orL h _ _ ih₁ ih₂ =>
      intro φ ψ e
      exact .orL ((h.cons φ).trans (List.Perm.swap _ _ _))
        ((ih₁ e).perm (List.Perm.swap _ _ _)) ((ih₂ e).perm (List.Perm.swap _ _ _))
  | impAndL h _ ih =>
      intro φ ψ e
      exact .impAndL ((h.cons φ).trans (List.Perm.swap _ _ _))
        ((ih e).perm (List.Perm.swap _ _ _))
  | impOrL h _ ih =>
      intro φ ψ e
      exact .impOrL ((h.cons φ).trans (List.Perm.swap _ _ _))
        ((ih e).perm ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons _)))
  | impVarL h hv _ ih =>
      intro φ ψ e
      exact .impVarL ((h.cons φ).trans (List.Perm.swap _ _ _)) (List.mem_cons_of_mem _ hv)
        ((ih e).perm (List.Perm.swap _ _ _))
  | impImpL h d₁ _ _ ih₂ =>
      intro φ ψ e
      exact .impImpL ((h.cons φ).trans (List.Perm.swap _ _ _))
        ((d₁.weaken φ).perm (List.Perm.swap _ _ _)) ((ih₂ e).perm (List.Perm.swap _ _ _))
  | @impBoxL _ _ Θ _ _ _ h d₁ _ _ ih₂ =>
      intro φ ψ e
      refine .impBoxL ((h.cons φ).trans (List.Perm.swap _ _ _)) ?_
        ((ih₂ e).perm (List.Perm.swap _ _ _))
      rcases unbox_cons φ Θ with e' | ⟨χ, e'⟩
      · rw [e']; exact d₁
      · rw [e']; exact d₁.weaken χ
  | @impDiaL _ _ Θ G₁ _ _ _ h hγ d₁ _ _ ih₂ =>
      intro φ ψ e
      refine .impDiaL ((h.cons φ).trans (List.Perm.swap _ _ _)) (List.mem_cons_of_mem _ hγ) ?_
        ((ih₂ e).perm (List.Perm.swap _ _ _))
      rcases unbox_cons φ Θ with e' | ⟨χ, e'⟩
      · rw [e']; exact d₁
      · rw [e']; exact (d₁.weaken χ).perm (List.Perm.swap _ _ _)

end G4CKh

end CK

#print axioms CK.G4CKh.inv
#print axioms CK.G4CKh.impR_inv
