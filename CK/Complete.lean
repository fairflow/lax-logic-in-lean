import CK.Cut
import CK.Sound

/-!
# `CK.Complete` — G4CK captures CK

**Theorem 2** (`thm:equiv`) of van der Giessen and Shillito,
arXiv:2602.16880v2, §3, for CK:

    ⊢_{G4CK} Γ ⇒ φ   if and only if   Γ ⊢_{CKH} φ.

Rocq `G4CK_sound_CKH`, `G4CK_compl_CKH` in
`theories/Sequent/G4CK/CKSoundComplete.v` (commit `cd09fce`).  Left to right
is `CK.G4CK.toCKH`.  Right to left: every axiom is provable, `(El)` is the
generalised axiom, `(Nec)` is `(□R)` after weakening, and `(MP)` is cut.

Rocq's proof goes through the decision procedure, because its `Provable`
lives in `Type` and `CKH_prv` in `Prop`; with `Prop`-valued provability
(divergence D2) the induction on the Hilbert derivation is direct.
-/

namespace CK

open scoped Form

namespace G4CK

/-- Modus ponens, by cut. -/
theorem mpAdm {Γ : List Form} {φ ψ : Form} (d : G4CK Γ φ) (e : G4CK Γ (φ ⟶ ψ)) :
    G4CK Γ ψ :=
  d.cut e.impR_inv

/-- Every axiom of Figure 1 is provable in G4CK. -/
theorem ofAxiom {φ : Form} (h : Axiom φ) (Γ : List Form) : G4CK Γ φ := by
  cases h with
  | a1 φ ψ => exact .impR (.impR (id_of_mem (.tail _ (.head _))))
  | a2 φ ψ χ =>
      refine .impR (.impR (.impR ?_))
      have i₁ : G4CK (φ :: (φ ⟶ ψ) :: (φ ⟶ (ψ ⟶ χ)) :: Γ) φ := id_of_mem (.head _)
      have i₂ : G4CK (φ :: (φ ⟶ ψ) :: (φ ⟶ (ψ ⟶ χ)) :: Γ) (φ ⟶ ψ) :=
        id_of_mem (.tail _ (.head _))
      have i₃ : G4CK (φ :: (φ ⟶ ψ) :: (φ ⟶ (ψ ⟶ χ)) :: Γ) (φ ⟶ (ψ ⟶ χ)) :=
        id_of_mem (.tail _ (.tail _ (.head _)))
      exact mpAdm (mpAdm i₁ i₂) (mpAdm i₁ i₃)
  | a3 φ ψ => exact .impR (.orR1 (id _ _))
  | a4 φ ψ => exact .impR (.orR2 (id _ _))
  | a5 φ ψ χ =>
      refine .impR (.impR (.impR (.orL (List.Perm.refl _) ?_ ?_)))
      · exact mpAdm (id_of_mem (.head _)) (id_of_mem (.tail _ (.tail _ (.head _))))
      · exact mpAdm (id_of_mem (.head _)) (id_of_mem (.tail _ (.head _)))
  | a6 φ ψ => exact .impR (.andL (List.Perm.refl _) (id _ _))
  | a7 φ ψ => exact .impR (.andL (List.Perm.refl _) (id_of_mem (.tail _ (.head _))))
  | a8 φ ψ χ =>
      refine .impR (.impR (.impR (.andR ?_ ?_)))
      · exact mpAdm (id_of_mem (.head _)) (id_of_mem (.tail _ (.tail _ (.head _))))
      · exact mpAdm (id_of_mem (.head _)) (id_of_mem (.tail _ (.head _)))
  | a9 φ => exact .impR (.botL (.head _))
  | kBox φ ψ =>
      refine .impR (.impR (.boxR ?_))
      have i₁ : G4CK (φ :: (φ ⟶ ψ) :: unbox Γ) φ := id _ _
      have i₂ : G4CK (φ :: (φ ⟶ ψ) :: unbox Γ) (φ ⟶ ψ) := id_of_mem (.tail _ (.head _))
      exact mpAdm i₁ i₂
  | kDia φ ψ =>
      refine .impR (.impR (.diaL (List.Perm.refl _) ?_))
      have i₁ : G4CK (φ :: (φ ⟶ ψ) :: unbox Γ) φ := id _ _
      have i₂ : G4CK (φ :: (φ ⟶ ψ) :: unbox Γ) (φ ⟶ ψ) := id_of_mem (.tail _ (.head _))
      exact mpAdm i₁ i₂

/-- **Theorem 2, right to left** (`thm:equiv`).  Rocq `G4CK_compl_CKH`. -/
theorem ofCKH {S : Form → Prop} {φ : Form} (d : CKH S φ) :
    ∀ {Γ : List Form}, (∀ x, S x → x ∈ Γ) → G4CK Γ φ := by
  induction d with
  | ax h => intro Γ _; exact ofAxiom h Γ
  | el h => intro Γ hS; exact id_of_mem (hS _ h)
  | nec _ ih =>
      intro Γ _
      have h₀ := ih (Γ := []) (fun _ hx => hx.elim)
      have := h₀.weakenList (unbox Γ)
      rw [List.append_nil] at this
      exact .boxR this
  | mp _ _ ih₁ ih₂ => intro Γ hS; exact mpAdm (ih₁ hS) (ih₂ hS)

end G4CK

/-- **Theorem 2** (`thm:equiv`), for CK:
`⊢_{G4CK} Γ ⇒ φ` iff `Γ ⊢_{CKH} φ`. -/
theorem G4CK_iff_CKH {Γ : List Form} {φ : Form} : G4CK Γ φ ↔ CKH (ctx Γ) φ :=
  ⟨G4CK.toCKH, fun d => G4CK.ofCKH d fun _ hx => hx⟩

end CK

#print axioms CK.G4CK_iff_CKH
