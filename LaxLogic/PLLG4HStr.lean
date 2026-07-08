import LaxLogic.PLLG4HAdm

/-!
# Bricks 4–6: spines, `weak_Imp`, and `L→→`-duplication for G4iLL″

* **Brick 4** — `Spine φ σ` (`φ = ◯^k σ`) with `laxR`-lifts: the
  bookkeeping for goals descending a `◯`-tower.
* **Brick 5** — `weak_Imp` (Dyckhoff–Negri Lemma 4.1, all antecedents):
  from `Γ ⇒ D` and `Γ, B ⇒ E` conclude `Γ, D→B ⇒ E`.  Induction on the
  first derivation (at `G4h`, since `∃`-wrapped judgments cannot be
  inducted on), conclusion at `G4c`.  The rule-ending table of
  `PLLG4PStr.lean` carries over; the two box rules give *shorter* cases
  than before, their premises already carrying the full context.
* **Brick 6** — `impLImp_dup` (Dyckhoff–Negri Lemma 4.2): a context
  occurrence of `(A→B)→D` may be replaced by `A, B→D, B→D`; plain
  structural induction, the principal case closed by `impR_inv` +
  `weak_Imp`.
-/

open PLLFormula

namespace PLLND

namespace G4c

/-- `Spine φ σ`: `φ = ◯^k σ` for some `k ≥ 0`. -/
inductive Spine : PLLFormula → PLLFormula → Prop
  | refl (φ : PLLFormula) : Spine φ φ
  | box {φ σ : PLLFormula} : Spine φ σ → Spine φ.somehow σ

/-- Climb a spine with `laxR`. -/
theorem Spine.lift {φ σ : PLLFormula} :
    Spine φ σ → ∀ {Γ : List PLLFormula}, G4c Γ σ → G4c Γ φ := by
  intro s
  induction s with
  | refl _ => exact fun d => d
  | box _ ih => exact fun d => laxR (ih d)

/-- Descend one `◯` at the target's top. -/
theorem Spine.unbox {φ σ : PLLFormula} :
    Spine φ σ.somehow → Spine φ σ := by
  intro s
  generalize hσ : σ.somehow = τ at s
  induction s with
  | refl φ => exact hσ ▸ .box (.refl σ)
  | box s ih => exact .box (ih hσ)

/-- **Weak implication** (D–N 4.1): from `Γ ⇒ D` and `Γ, B ⇒ E`
conclude `Γ, D→B ⇒ E`. -/
theorem weak_Imp : ∀ {n : Nat} {Γ : List PLLFormula} {D : PLLFormula},
    G4h n Γ D → ∀ {B E : PLLFormula}, G4c (B :: Γ) E →
    G4c (D.ifThen B :: Γ) E := by
  intro n Γ D d
  induction d with
  | init h =>
      intro B E side
      exact impLProp (List.Perm.refl _) h side
  | botL h =>
      intro B E _
      exact botL (.tail _ h)
  | andR d₁ d₂ ih₁ ih₂ =>
      intro B E side
      exact impLAnd (List.Perm.refl _) (ih₁ (ih₂ side))
  | orR1 d₁ ih =>
      intro B E side
      exact impLOr (List.Perm.refl _)
        (((ih side).weaken _).perm (List.Perm.swap _ _ _))
  | orR2 d₂ ih =>
      intro B E side
      exact impLOr (List.Perm.refl _) ((ih side).weaken _)
  | @impR _ _ D₁ D₂ d₁ _ =>
      intro B E side
      exact impLImp (List.Perm.refl _)
        (impR ⟨_, (d₁.weaken _).perm (List.Perm.swap _ _ _)⟩) side
  | laxR d₁ _ =>
      intro B E side
      exact impLLax (List.Perm.refl _) ⟨_, d₁⟩ side
  | @laxL _ Γ' A _ h d₁ _ =>
      -- box-keeping `laxL`: rebuild with `L◯→″`, box already present
      intro B E side
      exact impLLaxLax (List.Perm.refl _) h
        ⟨_, (d₁.weaken _).perm (List.Perm.swap _ _ _)⟩ side
  | @andL _ _ Θ A' B' _ h d₁ ih =>
      intro B E side
      have side' : G4c (B :: A' :: B' :: Θ) E :=
        (side.andL_inv ((h.cons B).trans (List.Perm.swap _ B Θ))).perm
          (List.perm_middle (l₁ := [A', B']))
      exact andL ((h.cons _).trans (List.Perm.swap _ _ Θ))
        ((ih side').perm (List.perm_middle (l₁ := [A', B'])).symm)
  | @orL _ _ Θ A' B' _ h d₁ d₂ ih₁ ih₂ =>
      intro B E side
      have side₁ : G4c (B :: A' :: Θ) E :=
        (side.orL_inv₁ ((h.cons B).trans (List.Perm.swap _ B Θ))).perm
          (List.perm_middle (l₁ := [A']))
      have side₂ : G4c (B :: B' :: Θ) E :=
        (side.orL_inv₂ ((h.cons B).trans (List.Perm.swap _ B Θ))).perm
          (List.perm_middle (l₁ := [B']))
      exact orL ((h.cons _).trans (List.Perm.swap _ _ Θ))
        ((ih₁ side₁).perm (List.perm_middle (l₁ := [A'])).symm)
        ((ih₂ side₂).perm (List.perm_middle (l₁ := [B'])).symm)
  | @impLProp _ _ Θ a B' _ h ha d₁ ih =>
      intro B E side
      have side' : G4c (B :: B' :: Θ) E :=
        (side.impLProp_inv ((h.cons B).trans (List.Perm.swap _ B Θ))).perm
          (List.perm_middle (l₁ := [B']))
      exact impLProp ((h.cons _).trans (List.Perm.swap _ _ Θ)) (.tail _ ha)
        ((ih side').perm (List.perm_middle (l₁ := [B'])).symm)
  | @impLBot _ _ Θ B' _ h d₁ ih =>
      intro B E side
      have side' : G4c (B :: Θ) E :=
        side.impLBot_inv ((h.cons B).trans (List.Perm.swap _ B Θ))
      exact impLBot ((h.cons _).trans (List.Perm.swap _ _ Θ)) (ih side')
  | @impLAnd _ _ Θ A₁ B₁ D₁ _ h d₁ ih =>
      intro B E side
      have side' : G4c (B :: A₁.ifThen (B₁.ifThen D₁) :: Θ) E :=
        (side.inv (.impAnd A₁ B₁ D₁)
          ((h.cons B).trans (List.Perm.swap _ B Θ))).perm
          (List.perm_middle (l₁ := [A₁.ifThen (B₁.ifThen D₁)]))
      exact impLAnd ((h.cons _).trans (List.Perm.swap _ _ Θ))
        ((ih side').perm
          (List.perm_middle (l₁ := [A₁.ifThen (B₁.ifThen D₁)])).symm)
  | @impLOr _ _ Θ A₁ B₁ D₁ _ h d₁ ih =>
      intro B E side
      have side' : G4c (B :: A₁.ifThen D₁ :: B₁.ifThen D₁ :: Θ) E :=
        (side.inv (.impOr A₁ B₁ D₁)
          ((h.cons B).trans (List.Perm.swap _ B Θ))).perm
          (List.perm_middle (l₁ := [A₁.ifThen D₁, B₁.ifThen D₁]))
      exact impLOr ((h.cons _).trans (List.Perm.swap _ _ Θ))
        ((ih side').perm
          (List.perm_middle (l₁ := [A₁.ifThen D₁, B₁.ifThen D₁])).symm)
  | @impLImp _ _ Θ A₁ B₁ D₁ _ h d₁ d₂ ih₁ ih₂ =>
      intro B E side
      have side' : G4c (B :: D₁ :: Θ) E :=
        (side.impLImp_inv₂ ((h.cons B).trans (List.Perm.swap _ B Θ))).perm
          (List.perm_middle (l₁ := [D₁]))
      exact impLImp ((h.cons _).trans (List.Perm.swap _ _ Θ))
        ⟨_, (d₁.weaken _).perm (List.perm_middle (l₁ := [B₁.ifThen D₁])).symm⟩
        ((ih₂ side').perm (List.perm_middle (l₁ := [D₁])).symm)
  | @impLLax _ _ Θ A₁ B₁ _ h d₁ d₂ ih₁ ih₂ =>
      intro B E side
      have side' : G4c (B :: B₁ :: Θ) E :=
        (side.impLLax_inv₂ ((h.cons B).trans (List.Perm.swap _ B Θ))).perm
          (List.perm_middle (l₁ := [B₁]))
      exact impLLax ((h.cons _).trans (List.Perm.swap _ _ Θ))
        ⟨_, d₁.weaken _⟩
        ((ih₂ side').perm (List.perm_middle (l₁ := [B₁])).symm)
  | @impLLaxLax _ Γ' Θ A₁ B₁ X _ h hX d₁ d₂ ih₁ ih₂ =>
      intro B E side
      have side' : G4c (B :: B₁ :: Θ) E :=
        (side.impLLax_inv₂ ((h.cons B).trans (List.Perm.swap _ B _))).perm
          (List.perm_middle (l₁ := [B₁]))
      exact impLLaxLax ((h.cons _).trans (List.Perm.swap _ _ Θ))
        (.tail _ hX)
        ⟨_, (d₁.weaken _).perm (List.Perm.swap X _ Γ')⟩
        ((ih₂ side').perm (List.perm_middle (l₁ := [B₁])).symm)

/-- `weak_Imp` at the working judgment. -/
theorem weak_Imp' {Γ : List PLLFormula} {D B E : PLLFormula}
    (d : G4c Γ D) (side : G4c (B :: Γ) E) : G4c (D.ifThen B :: Γ) E := by
  obtain ⟨n, hd⟩ := d
  exact weak_Imp hd side

open G4 (perm_cons_cases perm_shuffle) in
/-- **Duplication for `L→→`** (D–N 4.2, folded form): a context
occurrence of `(A→B)→D` may be replaced by `A, B→D, B→D`. -/
theorem impLImp_dup : ∀ {n : Nat} {Γ' : List PLLFormula} {E : PLLFormula},
    G4h n Γ' E → ∀ {A B D : PLLFormula} {Γ : List PLLFormula},
    Γ'.Perm ((A.ifThen B).ifThen D :: Γ) →
    G4c (A :: B.ifThen D :: B.ifThen D :: Γ) E := by
  intro n Γ' E d
  induction d with
  | init h =>
      intro A B D Γ hp
      rcases List.mem_cons.mp (hp.subset h) with e | h'
      · cases e
      · exact init (.tail _ (.tail _ (.tail _ h')))
  | botL h =>
      intro A B D Γ hp
      rcases List.mem_cons.mp (hp.subset h) with e | h'
      · cases e
      · exact botL (.tail _ (.tail _ (.tail _ h')))
  | andR _ _ ih₁ ih₂ =>
      intro A B D Γ hp
      exact andR (ih₁ hp) (ih₂ hp)
  | orR1 _ ih => intro A B D Γ hp; exact orR1 (ih hp)
  | orR2 _ ih => intro A B D Γ hp; exact orR2 (ih hp)
  | laxR _ ih => intro A B D Γ hp; exact laxR (ih hp)
  | @impR _ _ A₀ B₀ _ ih =>
      intro A B D Γ hp
      have h' := ih ((hp.cons A₀).trans (List.Perm.swap _ A₀ Γ))
      exact impR (h'.perm
        (List.perm_middle (l₁ := [A, B.ifThen D, B.ifThen D])))
  | @andL _ _ Θ A' B' _ h d₁ ih₁ =>
      intro A B D Γ hp
      rcases perm_cons_cases (h.symm.trans hp) with ⟨e, hΘΓ⟩ | ⟨l', hΘ, hΓ⟩
      · cases e
      · exact andL
          ((hΓ.append_left [A, B.ifThen D, B.ifThen D]).trans
            (List.perm_middle (l₁ := [A, B.ifThen D, B.ifThen D])))
          ((ih₁ ((hΘ.append_left [A', B']).trans List.perm_middle)).perm
            ((perm_shuffle [A, B.ifThen D, B.ifThen D] [A', B'] l')))
  | @orL _ _ Θ A' B' _ h d₁ d₂ ih₁ ih₂ =>
      intro A B D Γ hp
      rcases perm_cons_cases (h.symm.trans hp) with ⟨e, hΘΓ⟩ | ⟨l', hΘ, hΓ⟩
      · cases e
      · exact orL
          ((hΓ.append_left [A, B.ifThen D, B.ifThen D]).trans
            (List.perm_middle (l₁ := [A, B.ifThen D, B.ifThen D])))
          ((ih₁ ((hΘ.append_left [A']).trans List.perm_middle)).perm
            (perm_shuffle [A, B.ifThen D, B.ifThen D] [A'] l'))
          ((ih₂ ((hΘ.append_left [B']).trans List.perm_middle)).perm
            (perm_shuffle [A, B.ifThen D, B.ifThen D] [B'] l'))
  | @laxL _ Γ₀ A' _ h d₁ ih₁ =>
      intro A B D Γ hp
      -- the box is kept: transport the membership, recurse directly
      have hA : A'.somehow ∈ A :: B.ifThen D :: B.ifThen D :: Γ := by
        rcases List.mem_cons.mp (hp.subset h) with e | h'
        · cases e
        · exact .tail _ (.tail _ (.tail _ h'))
      exact laxL hA
        ((ih₁ ((hp.cons A').trans (List.Perm.swap _ A' Γ))).perm
          (List.perm_middle (l₁ := [A, B.ifThen D, B.ifThen D])))
  | @impLProp _ _ Θ a' B' _ h ha d₁ ih₁ =>
      intro A B D Γ hp
      rcases perm_cons_cases (h.symm.trans hp) with ⟨e, hΘΓ⟩ | ⟨l', hΘ, hΓ⟩
      · cases e
      · have ha' : prop a' ∈ A :: B.ifThen D :: B.ifThen D :: l' := by
          rcases List.mem_cons.mp (hΘ.subset ha) with e | h'
          · cases e
          · exact .tail _ (.tail _ (.tail _ h'))
        exact impLProp
          ((hΓ.append_left [A, B.ifThen D, B.ifThen D]).trans
            (List.perm_middle (l₁ := [A, B.ifThen D, B.ifThen D]))) ha'
          ((ih₁ ((hΘ.append_left [B']).trans List.perm_middle)).perm
            (perm_shuffle [A, B.ifThen D, B.ifThen D] [B'] l'))
  | @impLBot _ _ Θ B' _ h d₁ ih₁ =>
      intro A B D Γ hp
      rcases perm_cons_cases (h.symm.trans hp) with ⟨e, hΘΓ⟩ | ⟨l', hΘ, hΓ⟩
      · cases e
      · exact impLBot
          ((hΓ.append_left [A, B.ifThen D, B.ifThen D]).trans
            (List.perm_middle (l₁ := [A, B.ifThen D, B.ifThen D])))
          (ih₁ hΘ)
  | @impLAnd _ _ Θ A₁ B₁ D₁ _ h d₁ ih₁ =>
      intro A B D Γ hp
      rcases perm_cons_cases (h.symm.trans hp) with ⟨e, hΘΓ⟩ | ⟨l', hΘ, hΓ⟩
      · cases e
      · exact impLAnd
          ((hΓ.append_left [A, B.ifThen D, B.ifThen D]).trans
            (List.perm_middle (l₁ := [A, B.ifThen D, B.ifThen D])))
          ((ih₁ ((hΘ.append_left [A₁.ifThen (B₁.ifThen D₁)]).trans
            List.perm_middle)).perm
            (perm_shuffle [A, B.ifThen D, B.ifThen D]
              [A₁.ifThen (B₁.ifThen D₁)] l'))
  | @impLOr _ _ Θ A₁ B₁ D₁ _ h d₁ ih₁ =>
      intro A B D Γ hp
      rcases perm_cons_cases (h.symm.trans hp) with ⟨e, hΘΓ⟩ | ⟨l', hΘ, hΓ⟩
      · cases e
      · exact impLOr
          ((hΓ.append_left [A, B.ifThen D, B.ifThen D]).trans
            (List.perm_middle (l₁ := [A, B.ifThen D, B.ifThen D])))
          ((ih₁ ((hΘ.append_left [A₁.ifThen D₁, B₁.ifThen D₁]).trans
            List.perm_middle)).perm
            (perm_shuffle [A, B.ifThen D, B.ifThen D]
              [A₁.ifThen D₁, B₁.ifThen D₁] l'))
  | @impLImp _ _ Θ A₁ B₁ D₁ E₀ h d₁ d₂ ih₁ ih₂ =>
      intro A B D Γ hp
      rcases perm_cons_cases (h.symm.trans hp) with ⟨e, hΘΓ⟩ | ⟨l', hΘ, hΓ⟩
      · -- principal: `impR_inv` premise 1, close with `weak_Imp`
        cases e
        have p₁' : G4h _ (A₁ :: B₁.ifThen D₁ :: Θ) B₁ := d₁.impR_inv rfl
        have side : G4c (D₁ :: A₁ :: B₁.ifThen D₁ :: Θ) E₀ :=
          ⟨_, ((d₂.weaken A₁).weaken (B₁.ifThen D₁)).perm
            ((List.perm_middle (l₁ := [B₁.ifThen D₁, A₁])).trans
              (by exact (List.Perm.swap _ _ _).cons _))⟩
        have h' : G4c (B₁.ifThen D₁ :: A₁ :: B₁.ifThen D₁ :: Θ) E₀ :=
          weak_Imp p₁' side
        exact h'.perm ((List.Perm.swap _ _ _).trans
          (((hΘΓ.cons _).cons _).cons _))
      · exact impLImp
          ((hΓ.append_left [A, B.ifThen D, B.ifThen D]).trans
            (List.perm_middle (l₁ := [A, B.ifThen D, B.ifThen D])))
          ((ih₁ ((hΘ.append_left [B₁.ifThen D₁]).trans
            List.perm_middle)).perm
            (perm_shuffle [A, B.ifThen D, B.ifThen D] [B₁.ifThen D₁] l'))
          ((ih₂ ((hΘ.append_left [D₁]).trans List.perm_middle)).perm
            (perm_shuffle [A, B.ifThen D, B.ifThen D] [D₁] l'))
  | @impLLax _ _ Θ A₁ B₁ _ h d₁ d₂ ih₁ ih₂ =>
      intro A B D Γ hp
      rcases perm_cons_cases (h.symm.trans hp) with ⟨e, hΘΓ⟩ | ⟨l', hΘ, hΓ⟩
      · cases e
      · exact impLLax
          ((hΓ.append_left [A, B.ifThen D, B.ifThen D]).trans
            (List.perm_middle (l₁ := [A, B.ifThen D, B.ifThen D])))
          (ih₁ hΘ)
          ((ih₂ ((hΘ.append_left [B₁]).trans List.perm_middle)).perm
            (perm_shuffle [A, B.ifThen D, B.ifThen D] [B₁] l'))
  | @impLLaxLax _ Γ₀ Θ A₁ B₁ X _ h hX d₁ d₂ ih₁ ih₂ =>
      intro A B D Γ hp
      rcases perm_cons_cases (h.symm.trans hp) with ⟨e, hΘΓ⟩ | ⟨l', hΘ, hΓ⟩
      · cases e
      · have hX' : X.somehow ∈ A :: B.ifThen D :: B.ifThen D :: l' := by
          rcases List.mem_cons.mp (hΘ.subset hX) with e | h'
          · cases e
          · exact .tail _ (.tail _ (.tail _ h'))
        exact impLLaxLax
          ((hΓ.append_left [A, B.ifThen D, B.ifThen D]).trans
            (List.perm_middle (l₁ := [A, B.ifThen D, B.ifThen D]))) hX'
          ((ih₁ ((hp.cons X).trans (List.Perm.swap _ X Γ))).perm
            (List.perm_middle (l₁ := [A, B.ifThen D, B.ifThen D])))
          ((ih₂ ((hΘ.append_left [B₁]).trans List.perm_middle)).perm
            (perm_shuffle [A, B.ifThen D, B.ifThen D] [B₁] l'))

end G4c

end PLLND
