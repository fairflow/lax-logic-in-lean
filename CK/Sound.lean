import CK.G4CK
import CK.HilbertProps

/-!
# `CK.Sound` — every rule of G4CK is derivable in CKH

The left-to-right half of **Theorem 2** (`thm:equiv`) of van der Giessen and
Shillito, arXiv:2602.16880v2, §3:

    ⊢_{G4CK} Γ ⇒ φ   implies   Γ ⊢_{CKH} φ.

Rocq `G4CK_sound_CKH` in `theories/Sequent/G4CK/CKSoundComplete.v` (commit
`cd09fce`).  The paper has no semantics; this is the check that the rule
table is not over-permissive, made before cut or interpolation is attempted.
-/

namespace CK

open scoped Form

/-- **Theorem 2, left to right** (`thm:equiv`). -/
theorem G4CK.toCKH {Γ : List Form} {φ : Form} (d : G4CK Γ φ) : CKH (ctx Γ) φ := by
  induction d with
  | botL h => exact CKH.botE (.el h)
  | idP h => exact .el h
  | @andL Γ Δ φ ψ χ h _ ih =>
      have hm : (φ ⋏ ψ) ∈ Γ := h.mem_iff.2 List.mem_cons_self
      refine ih.subst fun x hx => ?_
      rcases List.mem_cons.1 hx with rfl | hx
      · exact CKH.andE1 (.el hm)
      rcases List.mem_cons.1 hx with rfl | hx
      · exact CKH.andE2 (.el hm)
      · exact .el (h.mem_iff.2 (List.mem_cons_of_mem _ hx))
  | andR _ _ ih₁ ih₂ => exact CKH.andI ih₁ ih₂
  | @orL Γ Δ φ ψ χ h _ _ ih₁ ih₂ =>
      have hΔ : ∀ x ∈ Δ, ctx Γ x := fun x hx => h.mem_iff.2 (List.mem_cons_of_mem _ hx)
      exact CKH.orE (.el (h.mem_iff.2 List.mem_cons_self)) (CKH.impI' ih₁ hΔ)
        (CKH.impI' ih₂ hΔ)
  | orR1 _ ih => exact CKH.orI1 ih
  | orR2 _ ih => exact CKH.orI2 ih
  | impR _ ih => exact CKH.impI ih
  | @impAndL Γ Δ φ ψ χ δ h _ ih =>
      have hm : ((φ ⋏ ψ) ⟶ χ) ∈ Γ := h.mem_iff.2 List.mem_cons_self
      refine ih.subst fun x hx => ?_
      rcases List.mem_cons.1 hx with rfl | hx
      · -- Γ ⊢ φ → (ψ → χ)
        have d : CKH (ctx (ψ :: φ :: Γ)) χ :=
          .mp (CKH.andI (.el (List.mem_cons_of_mem _ List.mem_cons_self))
              (.el List.mem_cons_self))
            (.el (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm)))
        exact CKH.impI (CKH.impI d)
      · exact .el (h.mem_iff.2 (List.mem_cons_of_mem _ hx))
  | @impOrL Γ Δ φ ψ χ δ h _ ih =>
      have hm : ((φ ⋎ ψ) ⟶ χ) ∈ Γ := h.mem_iff.2 List.mem_cons_self
      refine ih.subst fun x hx => ?_
      rcases List.mem_cons.1 hx with rfl | hx
      · exact CKH.impI (.mp (CKH.orI1 (.el List.mem_cons_self))
          (.el (List.mem_cons_of_mem _ hm)))
      rcases List.mem_cons.1 hx with rfl | hx
      · exact CKH.impI (.mp (CKH.orI2 (.el List.mem_cons_self))
          (.el (List.mem_cons_of_mem _ hm)))
      · exact .el (h.mem_iff.2 (List.mem_cons_of_mem _ hx))
  | @impVarL Γ Δ p φ χ h _ ih =>
      have hp : Form.var p ∈ Γ := h.mem_iff.2 List.mem_cons_self
      have hi : (Form.var p ⟶ φ) ∈ Γ :=
        h.mem_iff.2 (List.mem_cons_of_mem _ List.mem_cons_self)
      refine ih.subst fun x hx => ?_
      rcases List.mem_cons.1 hx with rfl | hx
      · exact .el hp
      rcases List.mem_cons.1 hx with rfl | hx
      · exact .mp (.el hp) (.el hi)
      · exact .el (h.mem_iff.2 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)))
  | @impImpL Γ Δ φ ψ χ δ h _ _ ih₁ ih₂ =>
      have hm : ((φ ⟶ ψ) ⟶ χ) ∈ Γ := h.mem_iff.2 List.mem_cons_self
      have hΔ : ∀ x ∈ Δ, CKH (ctx Γ) x := fun x hx =>
        .el (h.mem_iff.2 (List.mem_cons_of_mem _ hx))
      -- Γ ⊢ ψ → χ
      have d₁ : CKH (ctx Γ) (ψ ⟶ χ) :=
        CKH.impI (.mp (CKH.imp_of φ (.el List.mem_cons_self))
          (.el (List.mem_cons_of_mem _ hm)))
      have d₂ : CKH (ctx Γ) (φ ⟶ ψ) := ih₁.subst fun x hx => by
        rcases List.mem_cons.1 hx with rfl | hx
        · exact d₁
        · exact hΔ x hx
      refine ih₂.subst fun x hx => ?_
      rcases List.mem_cons.1 hx with rfl | hx
      · exact .mp d₂ (.el hm)
      · exact hΔ x hx
  | boxR _ ih =>
      exact CKH.boxI ih fun ψ hψ => .el (box_mem_of_mem_unbox hψ)
  | @impBoxL Γ Δ φ ψ δ h _ _ ih₁ ih₂ =>
      have hm : ((□φ) ⟶ ψ) ∈ Γ := h.mem_iff.2 List.mem_cons_self
      have hΔ : ∀ x ∈ Δ, x ∈ Γ := fun x hx => h.mem_iff.2 (List.mem_cons_of_mem _ hx)
      have d₁ : CKH (ctx Γ) (□φ) :=
        CKH.boxI ih₁ fun x hx => .el (hΔ _ (box_mem_of_mem_unbox hx))
      refine ih₂.subst fun x hx => ?_
      rcases List.mem_cons.1 hx with rfl | hx
      · exact .mp d₁ (.el hm)
      · exact .el (hΔ x hx)
  | @impDiaL Γ Δ γ φ ψ δ h _ _ ih₁ ih₂ =>
      have hg : (◇γ) ∈ Γ := h.mem_iff.2 List.mem_cons_self
      have hm : ((◇φ) ⟶ ψ) ∈ Γ :=
        h.mem_iff.2 (List.mem_cons_of_mem _ List.mem_cons_self)
      have hΔ : ∀ x ∈ Δ, x ∈ Γ := fun x hx =>
        h.mem_iff.2 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))
      -- Γ ⊢ □(γ → φ), hence Γ ⊢ ◇φ by K◇
      have d₁ : CKH (ctx Γ) (□(γ ⟶ φ)) :=
        CKH.boxI (CKH.impI ih₁) fun x hx => .el (hΔ _ (box_mem_of_mem_unbox hx))
      have d₂ : CKH (ctx Γ) (◇φ) := .mp (.el hg) (.mp d₁ (.ax (.kDia γ φ)))
      refine ih₂.subst fun x hx => ?_
      rcases List.mem_cons.1 hx with rfl | hx
      · exact .el hg
      rcases List.mem_cons.1 hx with rfl | hx
      · exact .mp d₂ (.el hm)
      · exact .el (hΔ x hx)
  | @diaL Γ Δ φ ψ h _ ih =>
      have hg : (◇φ) ∈ Γ := h.mem_iff.2 List.mem_cons_self
      have hΔ : ∀ x ∈ Δ, x ∈ Γ := fun x hx => h.mem_iff.2 (List.mem_cons_of_mem _ hx)
      have d₁ : CKH (ctx Γ) (□(φ ⟶ ψ)) :=
        CKH.boxI (CKH.impI ih) fun x hx => .el (hΔ _ (box_mem_of_mem_unbox hx))
      exact .mp (.el hg) (.mp d₁ (.ax (.kDia φ ψ)))

end CK

#print axioms CK.G4CK.toCKH
