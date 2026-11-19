import CK.Hilbert

/-!
# `CK.HilbertProps` — derived rules of CKH

Standard facts about the generalised Hilbert calculus of Figure 1
(arXiv:2602.16880v2, §2): substitution of derivations for hypotheses,
the deduction theorem, the intuitionistic introduction and elimination
rules, and the two modal steps the sequent rules need.  The Rocq
counterparts are in `theories/GHC/logic.v` and `theories/GHC/properties.v`
(commit `cd09fce`); the proofs here are written afresh.
-/

namespace CK

open scoped Form

/-- A list read as a set of hypotheses. -/
abbrev ctx (Γ : List Form) : Form → Prop := fun x => x ∈ Γ

/-- `ψ ∈ □⁻¹Γ` gives `□ψ ∈ Γ`.  Rocq `l_open_boxes_in`. -/
theorem box_mem_of_mem_unbox : ∀ {Γ : List Form} {ψ : Form}, ψ ∈ unbox Γ → (□ψ) ∈ Γ
  | [], _, h => nomatch h
  | .var _ :: _, _, h => List.mem_cons_of_mem _ (box_mem_of_mem_unbox (Γ := _) h)
  | .bot :: _, _, h => List.mem_cons_of_mem _ (box_mem_of_mem_unbox (Γ := _) h)
  | .and _ _ :: _, _, h => List.mem_cons_of_mem _ (box_mem_of_mem_unbox (Γ := _) h)
  | .or _ _ :: _, _, h => List.mem_cons_of_mem _ (box_mem_of_mem_unbox (Γ := _) h)
  | .imp _ _ :: _, _, h => List.mem_cons_of_mem _ (box_mem_of_mem_unbox (Γ := _) h)
  | .dia _ :: _, _, h => List.mem_cons_of_mem _ (box_mem_of_mem_unbox (Γ := _) h)
  | .box φ :: Γ, ψ, h => by
      have h' : ψ ∈ φ :: unbox Γ := h
      rcases List.mem_cons.1 h' with rfl | h''
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (box_mem_of_mem_unbox h'')

namespace CKH

/-- Derivations may be substituted for hypotheses. -/
theorem subst {Γ : Form → Prop} {φ : Form} (d : CKH Γ φ) :
    ∀ {S : Form → Prop}, (∀ x, Γ x → CKH S x) → CKH S φ := by
  induction d with
  | ax h => intro S _; exact .ax h
  | el h => intro S hS; exact hS _ h
  | nec d _ => intro S _; exact .nec d
  | mp _ _ ih₁ ih₂ => intro S hS; exact .mp (ih₁ hS) (ih₂ hS)

/-- Weakening. -/
theorem weaken {Γ S : Form → Prop} {φ : Form} (d : CKH Γ φ)
    (h : ∀ x, Γ x → S x) : CKH S φ :=
  d.subst fun x hx => .el (h x hx)

/-- `⊢ φ → φ`. -/
theorem imp_self {Γ : Form → Prop} (φ : Form) : CKH Γ (φ ⟶ φ) :=
  .mp (.ax (.a1 φ φ)) (.mp (.ax (.a1 φ (φ ⟶ φ))) (.ax (.a2 φ (φ ⟶ φ) φ)))

/-- From `Γ ⊢ ψ`, `Γ ⊢ φ → ψ`. -/
theorem imp_of {Γ : Form → Prop} {ψ : Form} (φ : Form) (d : CKH Γ ψ) : CKH Γ (φ ⟶ ψ) :=
  .mp d (.ax (.a1 ψ φ))

/-- The deduction theorem. -/
theorem deduction {Γ' : Form → Prop} {ψ : Form} (d : CKH Γ' ψ) :
    ∀ {Γ : Form → Prop} {φ : Form}, (∀ x, Γ' x → x = φ ∨ Γ x) → CKH Γ (φ ⟶ ψ) := by
  induction d with
  | ax h => intro Γ φ _; exact imp_of φ (.ax h)
  | el h =>
      intro Γ φ hsub
      rcases hsub _ h with rfl | h'
      · exact imp_self _
      · exact imp_of φ (.el h')
  | nec d _ => intro Γ φ _; exact imp_of φ (.nec d)
  | @mp _ χ ψ _ _ ih₁ ih₂ =>
      intro Γ φ hsub
      exact .mp (ih₁ hsub) (.mp (ih₂ hsub) (.ax (.a2 φ χ ψ)))

/-- `(→I)` for list contexts. -/
theorem impI {Γ : List Form} {φ ψ : Form} (d : CKH (ctx (φ :: Γ)) ψ) :
    CKH (ctx Γ) (φ ⟶ ψ) :=
  d.deduction fun _ hx => List.mem_cons.1 hx

/-- `(→I)` against a larger context: the hypotheses other than `φ` need only
be available in `S`. -/
theorem impI' {Θ : List Form} {S : Form → Prop} {φ ψ : Form} (d : CKH (ctx (φ :: Θ)) ψ)
    (h : ∀ x ∈ Θ, S x) : CKH S (φ ⟶ ψ) :=
  d.deduction fun x hx => (List.mem_cons.1 hx).imp id (h x)

/-- `(∧I)`. -/
theorem andI {Γ : Form → Prop} {φ ψ : Form} (d₁ : CKH Γ φ) (d₂ : CKH Γ ψ) :
    CKH Γ (φ ⋏ ψ) :=
  .mp d₁ (.mp (imp_of φ d₂) (.mp (imp_self φ) (.ax (.a8 φ φ ψ))))

/-- `(∧E₁)`. -/
theorem andE1 {Γ : Form → Prop} {φ ψ : Form} (d : CKH Γ (φ ⋏ ψ)) : CKH Γ φ :=
  .mp d (.ax (.a6 φ ψ))

/-- `(∧E₂)`. -/
theorem andE2 {Γ : Form → Prop} {φ ψ : Form} (d : CKH Γ (φ ⋏ ψ)) : CKH Γ ψ :=
  .mp d (.ax (.a7 φ ψ))

/-- `(∨I₁)`. -/
theorem orI1 {Γ : Form → Prop} {φ ψ : Form} (d : CKH Γ φ) : CKH Γ (φ ⋎ ψ) :=
  .mp d (.ax (.a3 φ ψ))

/-- `(∨I₂)`. -/
theorem orI2 {Γ : Form → Prop} {φ ψ : Form} (d : CKH Γ ψ) : CKH Γ (φ ⋎ ψ) :=
  .mp d (.ax (.a4 φ ψ))

/-- `(∨E)`, with the minor premises as implications. -/
theorem orE {Γ : Form → Prop} {φ ψ χ : Form} (d : CKH Γ (φ ⋎ ψ))
    (d₁ : CKH Γ (φ ⟶ χ)) (d₂ : CKH Γ (ψ ⟶ χ)) : CKH Γ χ :=
  .mp d (.mp d₂ (.mp d₁ (.ax (.a5 φ ψ χ))))

/-- `(⊥E)`. -/
theorem botE {Γ : Form → Prop} {φ : Form} (d : CKH Γ ⊥') : CKH Γ φ :=
  .mp d (.ax (.a9 φ))

/-- `chain [ψ₁,…,ψₙ] φ = ψₙ → … → ψ₁ → φ`. -/
def chain : List Form → Form → Form
  | [], φ => φ
  | ψ :: Δ, φ => chain Δ (ψ ⟶ φ)

/-- All hypotheses discharged: `Δ ⊢ φ` gives `∅ ⊢ chain Δ φ`. -/
theorem chain_of : ∀ {Δ : List Form} {φ : Form}, CKH (ctx Δ) φ →
    CKH (fun _ => False) (chain Δ φ)
  | [], _, d => d.weaken fun _ hx => nomatch hx
  | ψ :: Δ, φ, d => chain_of (Δ := Δ) (φ := ψ ⟶ φ) (impI d)

/-- `K□` iterated: `S ⊢ □(chain Δ φ)` and `S ⊢ □ψ` for each `ψ ∈ Δ` give
`S ⊢ □φ`. -/
theorem box_chain {S : Form → Prop} : ∀ {Δ : List Form} {φ : Form},
    CKH S (□(chain Δ φ)) → (∀ ψ ∈ Δ, CKH S (□ψ)) → CKH S (□φ)
  | [], _, d, _ => d
  | ψ :: Δ, φ, d, h =>
      .mp (h ψ List.mem_cons_self)
        (.mp (box_chain (Δ := Δ) d fun x hx => h x (List.mem_cons_of_mem _ hx))
          (.ax (.kBox ψ φ)))

/-- The step behind `(□R)`: `Δ ⊢ φ` gives `S ⊢ □φ` when `S ⊢ □ψ` for every
`ψ ∈ Δ`. -/
theorem boxI {S : Form → Prop} {Δ : List Form} {φ : Form} (d : CKH (ctx Δ) φ)
    (h : ∀ ψ ∈ Δ, CKH S (□ψ)) : CKH S (□φ) :=
  box_chain (.nec (chain_of d)) h

end CKH

end CK
