import CK.G4CK

/-!
# `CK.Structural` — exchange and weakening for G4CK

**Lemma 1** (`lemma:weakening`), rule `(wk)`, of van der Giessen and
Shillito, arXiv:2602.16880v2, §3:

    Γ ⇒ φ   /   Γ,Π ⇒ φ.

Rocq `weakening`, `generalised_weakeningR` in
`theories/Sequent/G4CK/CKSequentProps.v` (commit `cd09fce`).

Exchange is a theorem here and not a convention: antecedents are lists
(divergence D1), where Rocq's are multisets.
-/

namespace CK

open scoped Form

/-- `□⁻¹` as a `filterMap`. -/
def unboxOne : Form → Option Form
  | .box φ => some φ
  | _ => none

theorem unbox_eq_filterMap : ∀ Γ : List Form, unbox Γ = Γ.filterMap unboxOne
  | [] => rfl
  | .var _ :: Γ => by simp only [unbox, List.filterMap_cons, unboxOne]; exact unbox_eq_filterMap Γ
  | .bot :: Γ => by simp only [unbox, List.filterMap_cons, unboxOne]; exact unbox_eq_filterMap Γ
  | .and _ _ :: Γ => by simp only [unbox, List.filterMap_cons, unboxOne]; exact unbox_eq_filterMap Γ
  | .or _ _ :: Γ => by simp only [unbox, List.filterMap_cons, unboxOne]; exact unbox_eq_filterMap Γ
  | .imp _ _ :: Γ => by simp only [unbox, List.filterMap_cons, unboxOne]; exact unbox_eq_filterMap Γ
  | .dia _ :: Γ => by simp only [unbox, List.filterMap_cons, unboxOne]; exact unbox_eq_filterMap Γ
  | .box φ :: Γ => by
      simp only [unbox, List.filterMap_cons, unboxOne]; exact congrArg _ (unbox_eq_filterMap Γ)

/-- `□⁻¹` respects permutation. -/
theorem unbox_perm {Γ Γ' : List Form} (h : Γ.Perm Γ') : (unbox Γ).Perm (unbox Γ') := by
  rw [unbox_eq_filterMap, unbox_eq_filterMap]; exact h.filterMap _

/-- Adding one formula adds at most one formula under `□⁻¹`. -/
theorem unbox_cons (ψ : Form) (Γ : List Form) :
    unbox (ψ :: Γ) = unbox Γ ∨ ∃ χ, unbox (ψ :: Γ) = χ :: unbox Γ := by
  cases ψ <;> first | exact Or.inl rfl | exact Or.inr ⟨_, rfl⟩

namespace G4CK

/-- **Exchange**: provability depends on the antecedent up to permutation. -/
theorem perm {Γ : List Form} {φ : Form} (d : G4CK Γ φ) :
    ∀ {Γ' : List Form}, Γ.Perm Γ' → G4CK Γ' φ := by
  induction d with
  | botL h => intro Γ' hp; exact .botL (hp.mem_iff.1 h)
  | idP h => intro Γ' hp; exact .idP (hp.mem_iff.1 h)
  | andL h d _ => intro Γ' hp; exact .andL (hp.symm.trans h) d
  | andR _ _ ih₁ ih₂ => intro Γ' hp; exact .andR (ih₁ hp) (ih₂ hp)
  | orL h d₁ d₂ _ _ => intro Γ' hp; exact .orL (hp.symm.trans h) d₁ d₂
  | orR1 _ ih => intro Γ' hp; exact .orR1 (ih hp)
  | orR2 _ ih => intro Γ' hp; exact .orR2 (ih hp)
  | impR _ ih => intro Γ' hp; exact .impR (ih (hp.cons _))
  | impAndL h d _ => intro Γ' hp; exact .impAndL (hp.symm.trans h) d
  | impOrL h d _ => intro Γ' hp; exact .impOrL (hp.symm.trans h) d
  | impVarL h hv d _ => intro Γ' hp; exact .impVarL (hp.symm.trans h) hv d
  | impImpL h d₁ d₂ _ _ => intro Γ' hp; exact .impImpL (hp.symm.trans h) d₁ d₂
  | boxR _ ih => intro Γ' hp; exact .boxR (ih (unbox_perm hp))
  | impBoxL h d₁ d₂ _ _ => intro Γ' hp; exact .impBoxL (hp.symm.trans h) d₁ d₂
  | impDiaL h hγ d₁ d₂ _ _ => intro Γ' hp; exact .impDiaL (hp.symm.trans h) hγ d₁ d₂
  | diaL h d _ => intro Γ' hp; exact .diaL (hp.symm.trans h) d

/-- Weakening of the premise of a modal rule: `□⁻¹Δ ⇒ φ` gives
`□⁻¹(ψ,Δ) ⇒ φ`, from weakening by one formula. -/
private theorem unbox_weaken {Δ : List Form} {φ : Form} (ψ : Form)
    (ih : ∀ χ, G4CK (χ :: unbox Δ) φ) (d : G4CK (unbox Δ) φ) :
    G4CK (unbox (ψ :: Δ)) φ := by
  rcases unbox_cons ψ Δ with e | ⟨χ, e⟩
  · rw [e]; exact d
  · rw [e]; exact ih χ

/-- The same with one further formula `γ` in front. -/
private theorem unbox_weaken_cons {Δ : List Form} {γ φ : Form} (ψ : Form)
    (ih : ∀ χ, G4CK (χ :: γ :: unbox Δ) φ) (d : G4CK (γ :: unbox Δ) φ) :
    G4CK (γ :: unbox (ψ :: Δ)) φ := by
  rcases unbox_cons ψ Δ with e | ⟨χ, e⟩
  · rw [e]; exact d
  · rw [e]; exact (ih χ).perm (List.Perm.swap _ _ _)

/-- **Lemma 1, `(wk)`**, one formula: `Γ ⇒ φ` gives `ψ,Γ ⇒ φ`.
Rocq `weakening`. -/
theorem weaken {Γ : List Form} {φ : Form} (d : G4CK Γ φ) :
    ∀ ψ : Form, G4CK (ψ :: Γ) φ := by
  induction d with
  | botL h => intro ψ; exact .botL (List.mem_cons_of_mem _ h)
  | idP h => intro ψ; exact .idP (List.mem_cons_of_mem _ h)
  | andL h _ ih =>
      intro ψ
      exact .andL ((h.cons ψ).trans (List.Perm.swap _ _ _))
        ((ih ψ).perm (((List.Perm.swap _ _ _).trans
          ((List.Perm.swap _ _ _).cons _))))
  | andR _ _ ih₁ ih₂ => intro ψ; exact .andR (ih₁ ψ) (ih₂ ψ)
  | orL h _ _ ih₁ ih₂ =>
      intro ψ
      exact .orL ((h.cons ψ).trans (List.Perm.swap _ _ _))
        ((ih₁ ψ).perm (List.Perm.swap _ _ _)) ((ih₂ ψ).perm (List.Perm.swap _ _ _))
  | orR1 _ ih => intro ψ; exact .orR1 (ih ψ)
  | orR2 _ ih => intro ψ; exact .orR2 (ih ψ)
  | impR _ ih => intro ψ; exact .impR ((ih ψ).perm (List.Perm.swap _ _ _))
  | impAndL h _ ih =>
      intro ψ
      exact .impAndL ((h.cons ψ).trans (List.Perm.swap _ _ _))
        ((ih ψ).perm (List.Perm.swap _ _ _))
  | impOrL h _ ih =>
      intro ψ
      exact .impOrL ((h.cons ψ).trans (List.Perm.swap _ _ _))
        ((ih ψ).perm (((List.Perm.swap _ _ _).trans
          ((List.Perm.swap _ _ _).cons _))))
  | impVarL h hv _ ih =>
      intro ψ
      exact .impVarL ((h.cons ψ).trans (List.Perm.swap _ _ _)) (List.mem_cons_of_mem _ hv)
        ((ih ψ).perm (List.Perm.swap _ _ _))
  | impImpL h _ _ ih₁ ih₂ =>
      intro ψ
      exact .impImpL ((h.cons ψ).trans (List.Perm.swap _ _ _))
        ((ih₁ ψ).perm (List.Perm.swap _ _ _)) ((ih₂ ψ).perm (List.Perm.swap _ _ _))
  | boxR d ih => intro ψ; exact .boxR (unbox_weaken ψ ih d)
  | impBoxL h d₁ _ ih₁ ih₂ =>
      intro ψ
      exact .impBoxL ((h.cons ψ).trans (List.Perm.swap _ _ _))
        (unbox_weaken ψ ih₁ d₁) ((ih₂ ψ).perm (List.Perm.swap _ _ _))
  | impDiaL h hγ d₁ _ ih₁ ih₂ =>
      intro ψ
      exact .impDiaL ((h.cons ψ).trans (List.Perm.swap _ _ _)) (List.mem_cons_of_mem _ hγ)
        (unbox_weaken_cons ψ ih₁ d₁) ((ih₂ ψ).perm (List.Perm.swap _ _ _))
  | diaL h d ih =>
      intro ψ
      exact .diaL ((h.cons ψ).trans (List.Perm.swap _ _ _)) (unbox_weaken_cons ψ ih d)

/-- **Lemma 1, `(wk)`** (`lemma:weakening`): `Γ ⇒ φ` gives `Π,Γ ⇒ φ`
(`Π` is written `Θ` here; `Π` is a reserved token in Lean).
Rocq `generalised_weakeningR`. -/
theorem weakenList {Γ : List Form} {φ : Form} (d : G4CK Γ φ) :
    ∀ Θ : List Form, G4CK (Θ ++ Γ) φ
  | [] => d
  | ψ :: Θ => (weakenList d Θ).weaken ψ

end G4CK

end CK

#print axioms CK.G4CK.perm
#print axioms CK.G4CK.weakenList
