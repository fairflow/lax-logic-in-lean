import CK.Structural

/-!
# `CK.Identity` — the generalised axiom for G4CK

**Lemma 1** (`lemma:weakening`), rule `(Id)`, of van der Giessen and
Shillito, arXiv:2602.16880v2, §3:

    Γ,φ ⇒ φ.

Rocq `generalised_axiom` in `theories/Sequent/G4CK/CKSequentProps.v` (commit
`cd09fce`).  As in Dyckhoff and Negri (2000), on which the paper relies for
these lemmas, the identity is proved together with a detachment lemma,

    Γ,ψ ⇒ δ   /   Γ,φ,φ→ψ ⇒ δ,

by induction on `φ`.
-/

namespace CK

open scoped Form

/-- A member can be brought to the front (proved here to stay choice-free:
core's `List.perm_cons_erase` depends on `Classical.choice`). -/
theorem exists_perm_cons_of_mem {φ : Form} : ∀ {Γ : List Form}, φ ∈ Γ →
    ∃ Δ, Γ.Perm (φ :: Δ)
  | [], h => nomatch h
  | a :: Γ, h => by
      rcases List.mem_cons.1 h with rfl | h
      · exact ⟨Γ, List.Perm.refl _⟩
      · obtain ⟨Δ, hΔ⟩ := exists_perm_cons_of_mem h
        exact ⟨a :: Δ, (hΔ.cons a).trans (List.Perm.swap _ _ _)⟩

namespace G4CK

private abbrev IdAt (φ : Form) : Prop := ∀ Γ : List Form, G4CK (φ :: Γ) φ

private abbrev MpAt (φ : Form) : Prop :=
  ∀ (Γ : List Form) (ψ δ : Form), G4CK (ψ :: Γ) δ → G4CK (φ :: (φ ⟶ ψ) :: Γ) δ

private theorem id_mp : ∀ φ : Form, IdAt φ ∧ MpAt φ
  | .var p =>
      ⟨fun _ => .idP List.mem_cons_self,
       fun _ _ _ d => .impVarL (List.Perm.swap _ _ _) List.mem_cons_self
         ((d.weaken _).perm (List.Perm.swap _ _ _))⟩
  | .bot =>
      ⟨fun _ => .botL List.mem_cons_self, fun _ _ _ _ => .botL List.mem_cons_self⟩
  | .and φ₁ φ₂ => by
      have ⟨i₁, m₁⟩ := id_mp φ₁
      have ⟨i₂, m₂⟩ := id_mp φ₂
      refine ⟨fun Γ => .andL (List.Perm.refl _)
          (.andR (i₁ _) ((i₂ _).perm (List.Perm.swap _ _ _))), fun Γ ψ δ d => ?_⟩
      -- φ₁∧φ₂, (φ₁∧φ₂)→ψ, Γ ⇒ δ
      refine .andL (List.Perm.refl _) ?_
      -- φ₁, φ₂, (φ₁∧φ₂)→ψ, Γ ⇒ δ
      refine .impAndL (Δ := φ₁ :: φ₂ :: Γ)
        (((List.Perm.swap _ _ _).cons _).trans (List.Perm.swap _ _ _)) ?_
      -- φ₁→(φ₂→ψ), φ₁, φ₂, Γ ⇒ δ
      have h₂ : G4CK (φ₂ :: (φ₂ ⟶ ψ) :: Γ) δ := m₂ Γ ψ δ d
      have h₁ : G4CK (φ₁ :: (φ₁ ⟶ (φ₂ ⟶ ψ)) :: φ₂ :: Γ) δ :=
        m₁ (φ₂ :: Γ) (φ₂ ⟶ ψ) δ (h₂.perm (List.Perm.swap _ _ _))
      exact h₁.perm (List.Perm.swap _ _ _)
  | .or φ₁ φ₂ => by
      have ⟨i₁, m₁⟩ := id_mp φ₁
      have ⟨i₂, m₂⟩ := id_mp φ₂
      refine ⟨fun Γ => .orL (List.Perm.refl _) (.orR1 (i₁ _)) (.orR2 (i₂ _)),
        fun Γ ψ δ d => ?_⟩
      -- φ₁∨φ₂, (φ₁∨φ₂)→ψ, Γ ⇒ δ
      refine .orL (List.Perm.refl _) ?_ ?_
      · -- φ₁, (φ₁∨φ₂)→ψ, Γ ⇒ δ
        refine .impOrL (Δ := φ₁ :: Γ) (List.Perm.swap _ _ _) ?_
        -- φ₁→ψ, φ₂→ψ, φ₁, Γ ⇒ δ
        have h : G4CK (φ₁ :: (φ₁ ⟶ ψ) :: (φ₂ ⟶ ψ) :: Γ) δ :=
          m₁ _ ψ δ ((d.weaken (φ₂ ⟶ ψ)).perm (List.Perm.swap _ _ _))
        exact h.perm (((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons _)))
      · refine .impOrL (Δ := φ₂ :: Γ) (List.Perm.swap _ _ _) ?_
        -- φ₁→ψ, φ₂→ψ, φ₂, Γ ⇒ δ
        have h : G4CK (φ₂ :: (φ₂ ⟶ ψ) :: (φ₁ ⟶ ψ) :: Γ) δ :=
          m₂ _ ψ δ ((d.weaken (φ₁ ⟶ ψ)).perm (List.Perm.swap _ _ _))
        exact h.perm ((List.Perm.swap _ _ _).trans
          (((List.Perm.swap _ _ _).cons _).trans (List.Perm.swap _ _ _)))
  | .imp φ₁ φ₂ => by
      have ⟨_, m₁⟩ := id_mp φ₁
      have ⟨i₂, _⟩ := id_mp φ₂
      have idImp : IdAt (φ₁ ⟶ φ₂) := fun Γ => .impR (m₁ Γ φ₂ φ₂ (i₂ Γ))
      refine ⟨idImp, fun Γ ψ δ d => ?_⟩
      -- φ₁→φ₂, (φ₁→φ₂)→ψ, Γ ⇒ δ
      refine .impImpL (Δ := (φ₁ ⟶ φ₂) :: Γ) (List.Perm.swap _ _ _) ?_ ?_
      · -- φ₂→ψ, φ₁→φ₂, Γ ⇒ φ₁→φ₂
        exact (idImp ((φ₂ ⟶ ψ) :: Γ)).perm (List.Perm.swap _ _ _)
      · -- ψ, φ₁→φ₂, Γ ⇒ δ
        exact (d.weaken (φ₁ ⟶ φ₂)).perm (List.Perm.swap _ _ _)
  | .box φ => by
      have ⟨i, _⟩ := id_mp φ
      refine ⟨fun Γ => .boxR (i (unbox Γ)), fun Γ ψ δ d => ?_⟩
      -- □φ, □φ→ψ, Γ ⇒ δ
      refine .impBoxL (Δ := (□φ) :: Γ) (List.Perm.swap _ _ _) (i (unbox Γ)) ?_
      exact (d.weaken (□φ)).perm (List.Perm.swap _ _ _)
  | .dia φ => by
      have ⟨i, _⟩ := id_mp φ
      refine ⟨fun Γ => .diaL (List.Perm.refl _) (i (unbox Γ)), fun Γ ψ δ d => ?_⟩
      -- ◇φ, ◇φ→ψ, Γ ⇒ δ
      exact .impDiaL (Δ := (◇φ) :: Γ) (List.Perm.swap _ _ _) List.mem_cons_self (i (unbox Γ))
        ((d.weaken (◇φ)).perm (List.Perm.swap _ _ _))

/-- **Lemma 1, `(Id)`** (`lemma:weakening`): `Γ,φ ⇒ φ`.
Rocq `generalised_axiom`. -/
theorem id (φ : Form) (Γ : List Form) : G4CK (φ :: Γ) φ := (id_mp φ).1 Γ

/-- `(Id)` with the formula anywhere in the antecedent. -/
theorem id_of_mem {φ : Form} {Γ : List Form} (h : φ ∈ Γ) : G4CK Γ φ :=
  let ⟨Δ, hp⟩ := exists_perm_cons_of_mem h; (id φ Δ).perm hp.symm

/-- Detachment: `Γ,ψ ⇒ δ` gives `Γ,φ,φ→ψ ⇒ δ`. -/
theorem mp (φ : Form) {Γ : List Form} {ψ δ : Form} (d : G4CK (ψ :: Γ) δ) :
    G4CK (φ :: (φ ⟶ ψ) :: Γ) δ := (id_mp φ).2 Γ ψ δ d

end G4CK

end CK

#print axioms CK.G4CK.id
#print axioms CK.G4CK.mp
#print axioms CK.G4CK.id_of_mem
