import CK.Inversion

/-!
# `CK.Contraction` — `(→L)`, duplication and contraction for G4CK

From van der Giessen and Shillito, arXiv:2602.16880v2, §3:

* **Lemma 1** (`lemma:weakening`), rule `(→L)`:
  `Γ ⇒ φ   ψ,Γ ⇒ δ  /  Γ,φ→ψ ⇒ δ`  (`G4CK.weakImp`; Rocq `weak_ImpL`);
* the duplication lemma of Dyckhoff and Negri (2000, Lemma 4.2)
  (`G4CK.impImpL_dup`; Rocq `ImpLImp_dup`);
* the unlabelled **Proposition**: contraction is admissible
  (`G4CK.contract`; Rocq `contraction`).

Rocq: `theories/Sequent/G4CK/CKSequentProps.v`, commit `cd09fce`.  The
proofs follow `LaxLogic/PLL/G4/G4HStr.lean` and `G4HCtr.lean` case by case,
with new cases for the four modal rules.  Contraction is by induction on
the weight of the contracted formula and then on the derivation; no cut.
-/

namespace CK

open scoped Form

theorem Form.weight_pos : ∀ φ : Form, 0 < φ.weight
  | .var _ => Nat.succ_pos _
  | .bot => Nat.succ_pos _
  | .and _ _ => Nat.succ_pos _
  | .or _ _ => Nat.succ_pos _
  | .imp _ _ => Nat.succ_pos _
  | .box _ => Nat.succ_pos _
  | .dia _ => Nat.succ_pos _

namespace G4CK

/-- The master inversion at `G4CK`. -/
theorem inv {Γ : List Form} {C : Form} (d : G4CK Γ C) {P : Form} {L Δ : List Form}
    (hInv : Inv P L) (hp : Γ.Perm (P :: Δ)) : G4CK (L ++ Δ) C :=
  let ⟨_, h⟩ := G4CKh.ofG4CK d; (h.inv hInv hp).toG4CK

/-- `(→R)` is invertible.  Rocq `ImpR_rev`. -/
theorem impR_inv {Γ : List Form} {φ ψ : Form} (d : G4CK Γ (φ ⟶ ψ)) : G4CK (φ :: Γ) ψ :=
  let ⟨_, h⟩ := G4CKh.ofG4CK d; (h.impR_inv rfl).toG4CK

/-- **Lemma 1, `(→L)`** (`lemma:weakening`): from `Γ ⇒ D` and `B,Γ ⇒ E`
conclude `D→B,Γ ⇒ E`.  Rocq `weak_ImpL`. -/
theorem weakImp {Γ : List Form} {D : Form} (d : G4CK Γ D) :
    ∀ {B E : Form}, G4CK (B :: Γ) E → G4CK ((D ⟶ B) :: Γ) E := by
  induction d with
  | botL h => intro B E _; exact .botL (List.mem_cons_of_mem _ h)
  | idP h => intro B E side; exact .impVarL (List.Perm.refl _) h side
  | andR _ _ ih₁ ih₂ =>
      intro B E side
      exact .impAndL (List.Perm.refl _) (ih₁ (ih₂ side))
  | orR1 _ ih =>
      intro B E side
      exact .impOrL (List.Perm.refl _) (((ih side).weaken _).perm (List.Perm.swap _ _ _))
  | orR2 _ ih =>
      intro B E side
      exact .impOrL (List.Perm.refl _) ((ih side).weaken _)
  | impR d₁ _ =>
      intro B E side
      exact .impImpL (List.Perm.refl _)
        (.impR ((d₁.weaken _).perm (List.Perm.swap _ _ _))) side
  | boxR d₁ _ => intro B E side; exact .impBoxL (List.Perm.refl _) d₁ side
  | @diaL Γ Θ A₁ _ h d₁ _ =>
      intro B E side
      have hu : (unbox Θ).Perm (unbox Γ) := (unbox_perm h).symm
      exact .impDiaL (Δ := Γ) (List.Perm.refl _) (h.mem_iff.2 List.mem_cons_self)
        (d₁.perm (hu.cons A₁)) side
  | @andL _ Θ A' B' _ h _ ih =>
      intro B E side
      have side' : G4CK (B :: A' :: B' :: Θ) E :=
        (side.inv (.and A' B') ((h.cons B).trans (List.Perm.swap _ B Θ))).perm
          (List.perm_middle (l₁ := [A', B']))
      exact .andL ((h.cons _).trans (List.Perm.swap _ _ Θ))
        ((ih side').perm (List.perm_middle (l₁ := [A', B'])).symm)
  | @orL _ Θ A' B' _ h _ _ ih₁ ih₂ =>
      intro B E side
      have side₁ : G4CK (B :: A' :: Θ) E :=
        (side.inv (.or₁ A' B') ((h.cons B).trans (List.Perm.swap _ B Θ))).perm
          (List.perm_middle (l₁ := [A']))
      have side₂ : G4CK (B :: B' :: Θ) E :=
        (side.inv (.or₂ A' B') ((h.cons B).trans (List.Perm.swap _ B Θ))).perm
          (List.perm_middle (l₁ := [B']))
      exact .orL ((h.cons _).trans (List.Perm.swap _ _ Θ))
        ((ih₁ side₁).perm (List.perm_middle (l₁ := [A'])).symm)
        ((ih₂ side₂).perm (List.perm_middle (l₁ := [B'])).symm)
  | @impVarL _ Θ a B' _ h ha _ ih =>
      intro B E side
      have side' : G4CK (B :: B' :: Θ) E :=
        (side.inv (.impVar a B') ((h.cons B).trans (List.Perm.swap _ B Θ))).perm
          (List.perm_middle (l₁ := [B']))
      exact .impVarL ((h.cons _).trans (List.Perm.swap _ _ Θ)) (List.mem_cons_of_mem _ ha)
        ((ih side').perm (List.perm_middle (l₁ := [B'])).symm)
  | @impAndL _ Θ A₁ B₁ D₁ _ h _ ih =>
      intro B E side
      have side' : G4CK (B :: (A₁ ⟶ (B₁ ⟶ D₁)) :: Θ) E :=
        (side.inv (.impAnd A₁ B₁ D₁) ((h.cons B).trans (List.Perm.swap _ B Θ))).perm
          (List.perm_middle (l₁ := [A₁ ⟶ (B₁ ⟶ D₁)]))
      exact .impAndL ((h.cons _).trans (List.Perm.swap _ _ Θ))
        ((ih side').perm (List.perm_middle (l₁ := [A₁ ⟶ (B₁ ⟶ D₁)])).symm)
  | @impOrL _ Θ A₁ B₁ D₁ _ h _ ih =>
      intro B E side
      have side' : G4CK (B :: (A₁ ⟶ D₁) :: (B₁ ⟶ D₁) :: Θ) E :=
        (side.inv (.impOr A₁ B₁ D₁) ((h.cons B).trans (List.Perm.swap _ B Θ))).perm
          (List.perm_middle (l₁ := [A₁ ⟶ D₁, B₁ ⟶ D₁]))
      exact .impOrL ((h.cons _).trans (List.Perm.swap _ _ Θ))
        ((ih side').perm (List.perm_middle (l₁ := [A₁ ⟶ D₁, B₁ ⟶ D₁])).symm)
  | @impImpL _ Θ A₁ B₁ D₁ _ h d₁ _ _ ih₂ =>
      intro B E side
      have side' : G4CK (B :: D₁ :: Θ) E :=
        (side.inv (.impImp A₁ B₁ D₁) ((h.cons B).trans (List.Perm.swap _ B Θ))).perm
          (List.perm_middle (l₁ := [D₁]))
      exact .impImpL ((h.cons _).trans (List.Perm.swap _ _ Θ))
        ((d₁.weaken _).perm (List.perm_middle (l₁ := [B₁ ⟶ D₁])).symm)
        ((ih₂ side').perm (List.perm_middle (l₁ := [D₁])).symm)
  | @impBoxL _ Θ A₁ B₁ _ h d₁ _ _ ih₂ =>
      intro B E side
      have side' : G4CK (B :: B₁ :: Θ) E :=
        (side.inv (.impBox A₁ B₁) ((h.cons B).trans (List.Perm.swap _ B Θ))).perm
          (List.perm_middle (l₁ := [B₁]))
      exact .impBoxL ((h.cons _).trans (List.Perm.swap _ _ Θ)) d₁
        ((ih₂ side').perm (List.perm_middle (l₁ := [B₁])).symm)
  | @impDiaL _ Θ G₁ A₁ B₁ _ h hγ d₁ _ _ ih₂ =>
      intro B E side
      have side' : G4CK (B :: B₁ :: Θ) E :=
        (side.inv (.impDia A₁ B₁) ((h.cons B).trans (List.Perm.swap _ B Θ))).perm
          (List.perm_middle (l₁ := [B₁]))
      exact .impDiaL ((h.cons _).trans (List.Perm.swap _ _ Θ)) (List.mem_cons_of_mem _ hγ) d₁
        ((ih₂ side').perm (List.perm_middle (l₁ := [B₁])).symm)

/-- A modal premise after an antecedent formula `P` that is not a box has
been replaced by a list `K`. -/
private theorem unbox_replace {Θ l' K pre : List Form} {P φ : Form}
    (hP : unbox (P :: l') = unbox l') (hΘ : Θ.Perm (P :: l'))
    (d : G4CK (pre ++ unbox Θ) φ) : G4CK (pre ++ unbox (K ++ l')) φ := by
  have h₁ : (unbox Θ).Perm (unbox l') := by
    have := unbox_perm hΘ
    rwa [hP] at this
  rw [unbox_append]
  exact ((d.perm (h₁.append_left pre)).weakenList (unbox K)).perm (perm_shuffle _ _ _)

/-- **Duplication for `(→→L)`** (Dyckhoff and Negri 2000, Lemma 4.2): an
antecedent occurrence of `(A→B)→D` may be replaced by `A, B→D, B→D`.
Rocq `ImpLImp_dup`. -/
theorem impImpL_dup {Γ' : List Form} {E : Form} (d : G4CK Γ' E) :
    ∀ {A B D : Form} {Γ : List Form}, Γ'.Perm (((A ⟶ B) ⟶ D) :: Γ) →
      G4CK (A :: (B ⟶ D) :: (B ⟶ D) :: Γ) E := by
  induction d with
  | botL h =>
      intro A B D Γ hp
      rcases List.mem_cons.1 (hp.subset h) with e | h'
      · cases e
      · exact .botL (.tail _ (.tail _ (.tail _ h')))
  | idP h =>
      intro A B D Γ hp
      rcases List.mem_cons.1 (hp.subset h) with e | h'
      · cases e
      · exact .idP (.tail _ (.tail _ (.tail _ h')))
  | andR _ _ ih₁ ih₂ => intro A B D Γ hp; exact .andR (ih₁ hp) (ih₂ hp)
  | orR1 _ ih => intro A B D Γ hp; exact .orR1 (ih hp)
  | orR2 _ ih => intro A B D Γ hp; exact .orR2 (ih hp)
  | @impR _ A₀ B₀ _ ih =>
      intro A B D Γ hp
      have h' := ih ((hp.cons A₀).trans (List.Perm.swap _ A₀ Γ))
      exact .impR (h'.perm (List.perm_middle (l₁ := [A, B ⟶ D, B ⟶ D])))
  | @andL _ Θ A' B' _ h _ ih₁ =>
      intro A B D Γ hp
      rcases perm_cons_cases (h.symm.trans hp) with ⟨e, _⟩ | ⟨l', hΘ, hΓ⟩
      · cases e
      · exact .andL
          ((hΓ.append_left [A, B ⟶ D, B ⟶ D]).trans
            (List.perm_middle (l₁ := [A, B ⟶ D, B ⟶ D])))
          ((ih₁ ((hΘ.append_left [A', B']).trans List.perm_middle)).perm
            (perm_shuffle [A, B ⟶ D, B ⟶ D] [A', B'] l'))
  | @orL _ Θ A' B' _ h _ _ ih₁ ih₂ =>
      intro A B D Γ hp
      rcases perm_cons_cases (h.symm.trans hp) with ⟨e, _⟩ | ⟨l', hΘ, hΓ⟩
      · cases e
      · exact .orL
          ((hΓ.append_left [A, B ⟶ D, B ⟶ D]).trans
            (List.perm_middle (l₁ := [A, B ⟶ D, B ⟶ D])))
          ((ih₁ ((hΘ.append_left [A']).trans List.perm_middle)).perm
            (perm_shuffle [A, B ⟶ D, B ⟶ D] [A'] l'))
          ((ih₂ ((hΘ.append_left [B']).trans List.perm_middle)).perm
            (perm_shuffle [A, B ⟶ D, B ⟶ D] [B'] l'))
  | @impVarL _ Θ a' B' _ h ha _ ih₁ =>
      intro A B D Γ hp
      rcases perm_cons_cases (h.symm.trans hp) with ⟨e, _⟩ | ⟨l', hΘ, hΓ⟩
      · cases e
      · have ha' : Form.var a' ∈ A :: (B ⟶ D) :: (B ⟶ D) :: l' := by
          rcases List.mem_cons.1 (hΘ.subset ha) with e | h'
          · cases e
          · exact .tail _ (.tail _ (.tail _ h'))
        exact .impVarL
          ((hΓ.append_left [A, B ⟶ D, B ⟶ D]).trans
            (List.perm_middle (l₁ := [A, B ⟶ D, B ⟶ D]))) ha'
          ((ih₁ ((hΘ.append_left [B']).trans List.perm_middle)).perm
            (perm_shuffle [A, B ⟶ D, B ⟶ D] [B'] l'))
  | @impAndL _ Θ A₁ B₁ D₁ _ h _ ih₁ =>
      intro A B D Γ hp
      rcases perm_cons_cases (h.symm.trans hp) with ⟨e, _⟩ | ⟨l', hΘ, hΓ⟩
      · cases e
      · exact .impAndL
          ((hΓ.append_left [A, B ⟶ D, B ⟶ D]).trans
            (List.perm_middle (l₁ := [A, B ⟶ D, B ⟶ D])))
          ((ih₁ ((hΘ.append_left [A₁ ⟶ (B₁ ⟶ D₁)]).trans List.perm_middle)).perm
            (perm_shuffle [A, B ⟶ D, B ⟶ D] [A₁ ⟶ (B₁ ⟶ D₁)] l'))
  | @impOrL _ Θ A₁ B₁ D₁ _ h _ ih₁ =>
      intro A B D Γ hp
      rcases perm_cons_cases (h.symm.trans hp) with ⟨e, _⟩ | ⟨l', hΘ, hΓ⟩
      · cases e
      · exact .impOrL
          ((hΓ.append_left [A, B ⟶ D, B ⟶ D]).trans
            (List.perm_middle (l₁ := [A, B ⟶ D, B ⟶ D])))
          ((ih₁ ((hΘ.append_left [A₁ ⟶ D₁, B₁ ⟶ D₁]).trans List.perm_middle)).perm
            (perm_shuffle [A, B ⟶ D, B ⟶ D] [A₁ ⟶ D₁, B₁ ⟶ D₁] l'))
  | @impImpL _ Θ A₁ B₁ D₁ E₀ h d₁ d₂ ih₁ ih₂ =>
      intro A B D Γ hp
      rcases perm_cons_cases (h.symm.trans hp) with ⟨e, hΘΓ⟩ | ⟨l', hΘ, hΓ⟩
      · -- principal: invert `(→R)` in premise 1, close with `(→L)`
        cases e
        have p₁' : G4CK (A₁ :: (B₁ ⟶ D₁) :: Θ) B₁ := d₁.impR_inv
        have side : G4CK (D₁ :: A₁ :: (B₁ ⟶ D₁) :: Θ) E₀ :=
          ((d₂.weaken A₁).weaken (B₁ ⟶ D₁)).perm
            ((List.perm_middle (l₁ := [B₁ ⟶ D₁, A₁])).trans
              ((List.Perm.swap _ _ _).cons _))
        have h' : G4CK ((B₁ ⟶ D₁) :: A₁ :: (B₁ ⟶ D₁) :: Θ) E₀ := weakImp p₁' side
        exact h'.perm ((List.Perm.swap _ _ _).trans (((hΘΓ.cons _).cons _).cons _))
      · exact .impImpL
          ((hΓ.append_left [A, B ⟶ D, B ⟶ D]).trans
            (List.perm_middle (l₁ := [A, B ⟶ D, B ⟶ D])))
          ((ih₁ ((hΘ.append_left [B₁ ⟶ D₁]).trans List.perm_middle)).perm
            (perm_shuffle [A, B ⟶ D, B ⟶ D] [B₁ ⟶ D₁] l'))
          ((ih₂ ((hΘ.append_left [D₁]).trans List.perm_middle)).perm
            (perm_shuffle [A, B ⟶ D, B ⟶ D] [D₁] l'))
  | boxR d₁ _ =>
      intro A B D Γ hp
      exact .boxR (unbox_replace (K := [A, B ⟶ D, B ⟶ D]) (pre := []) rfl hp d₁)
  | @impBoxL _ Θ A₁ B₁ _ h d₁ _ _ ih₂ =>
      intro A B D Γ hp
      rcases perm_cons_cases (h.symm.trans hp) with ⟨e, _⟩ | ⟨l', hΘ, hΓ⟩
      · cases e
      · exact .impBoxL
          ((hΓ.append_left [A, B ⟶ D, B ⟶ D]).trans
            (List.perm_middle (l₁ := [A, B ⟶ D, B ⟶ D])))
          (unbox_replace (K := [A, B ⟶ D, B ⟶ D]) (pre := []) rfl hΘ d₁)
          ((ih₂ ((hΘ.append_left [B₁]).trans List.perm_middle)).perm
            (perm_shuffle [A, B ⟶ D, B ⟶ D] [B₁] l'))
  | @impDiaL _ Θ G₁ A₁ B₁ _ h hγ d₁ _ _ ih₂ =>
      intro A B D Γ hp
      rcases perm_cons_cases (h.symm.trans hp) with ⟨e, _⟩ | ⟨l', hΘ, hΓ⟩
      · cases e
      · have hγ' : (◇G₁) ∈ A :: (B ⟶ D) :: (B ⟶ D) :: l' := by
          rcases List.mem_cons.1 (hΘ.subset hγ) with e | h'
          · cases e
          · exact .tail _ (.tail _ (.tail _ h'))
        exact .impDiaL
          ((hΓ.append_left [A, B ⟶ D, B ⟶ D]).trans
            (List.perm_middle (l₁ := [A, B ⟶ D, B ⟶ D]))) hγ'
          (unbox_replace (K := [A, B ⟶ D, B ⟶ D]) (pre := [G₁]) rfl hΘ d₁)
          ((ih₂ ((hΘ.append_left [B₁]).trans List.perm_middle)).perm
            (perm_shuffle [A, B ⟶ D, B ⟶ D] [B₁] l'))
  | @diaL _ Θ A₁ _ h d₁ _ =>
      intro A B D Γ hp
      rcases perm_cons_cases (h.symm.trans hp) with ⟨e, _⟩ | ⟨l', hΘ, hΓ⟩
      · cases e
      · exact .diaL
          ((hΓ.append_left [A, B ⟶ D, B ⟶ D]).trans
            (List.perm_middle (l₁ := [A, B ⟶ D, B ⟶ D])))
          (unbox_replace (K := [A, B ⟶ D, B ⟶ D]) (pre := [A₁]) rfl hΘ d₁)

/-! ## Contraction -/

private theorem push2 {x q : Form} {Γ : List Form} :
    (x :: q :: q :: Γ).Perm (q :: q :: x :: Γ) :=
  (List.Perm.swap q x _).trans ((List.Perm.swap q x Γ).cons q)

private theorem pushL (L : List Form) {q : Form} {Δ Γ₀ : List Form}
    (hΔ : Δ.Perm (q :: q :: Γ₀)) : (L ++ Δ).Perm (q :: q :: (L ++ Γ₀)) :=
  (hΔ.append_left L).trans (List.perm_middle.trans (List.perm_middle.cons q))

/-- The principal `P` is one of the two designated copies of `q`, or lives
beside them. -/
private theorem cross_split3 {P q : Form} {Γ' Δ Γ : List Form}
    (h : Γ'.Perm (P :: Δ)) (hp : Γ'.Perm (q :: q :: Γ)) :
    (P = q ∧ Δ.Perm (q :: Γ)) ∨ ∃ Γ₀, Δ.Perm (q :: q :: Γ₀) ∧ Γ.Perm (P :: Γ₀) := by
  rcases perm_cons_cases (h.symm.trans hp) with ⟨e, hΔ⟩ | ⟨l₁, hΔ, hm⟩
  · exact .inl ⟨e, hΔ⟩
  rcases perm_cons_cases hm with ⟨e, hl⟩ | ⟨l₂, hΓ, hl₁⟩
  · exact .inl ⟨e.symm, hΔ.trans (hl.symm.cons q)⟩
  · exact .inr ⟨l₂, hΔ.trans (hl₁.cons q), hΓ⟩

private theorem mem_contract {ψ q : Form} {Γ' Γ : List Form}
    (hp : Γ'.Perm (q :: q :: Γ)) (h : ψ ∈ Γ') : ψ = q ∨ ψ ∈ Γ := by
  rcases List.mem_cons.1 (hp.subset h) with e | h'
  · exact .inl e
  rcases List.mem_cons.1 h' with e | h''
  · exact .inl e
  · exact .inr h''

/-- Contraction at weight `≤ w`, as an induction hypothesis. -/
private abbrev CtrUpTo (w : Nat) : Prop :=
  ∀ {A : Form}, A.weight ≤ w → ∀ {Γ' : List Form} {E : Form}, G4CK Γ' E →
    ∀ {Γ : List Form}, Γ'.Perm (A :: A :: Γ) → G4CK (A :: Γ) E

/-- A modal premise under contraction of `A` in the conclusion: if `A` is a
box, its two opened copies are contracted, at a smaller weight. -/
private theorem unbox_contract {w : Nat} (ihw : CtrUpTo w) :
    ∀ {A : Form}, A.weight ≤ w + 1 → ∀ {Θ Γ pre : List Form} {φ : Form},
      Θ.Perm (A :: A :: Γ) → G4CK (pre ++ unbox Θ) φ → G4CK (pre ++ unbox (A :: Γ)) φ
  | .var _, _, _, _, pre, _, hΘ, d => d.perm ((unbox_perm hΘ).append_left pre)
  | .bot, _, _, _, pre, _, hΘ, d => d.perm ((unbox_perm hΘ).append_left pre)
  | .and _ _, _, _, _, pre, _, hΘ, d => d.perm ((unbox_perm hΘ).append_left pre)
  | .or _ _, _, _, _, pre, _, hΘ, d => d.perm ((unbox_perm hΘ).append_left pre)
  | .imp _ _, _, _, _, pre, _, hΘ, d => d.perm ((unbox_perm hΘ).append_left pre)
  | .dia _, _, _, _, pre, _, hΘ, d => d.perm ((unbox_perm hΘ).append_left pre)
  | .box χ, hA, _, Γ, pre, _, hΘ, d => by
      have hχ : χ.weight ≤ w := Nat.le_of_succ_le_succ hA
      have d' : G4CK (pre ++ χ :: χ :: unbox Γ) _ := d.perm ((unbox_perm hΘ).append_left pre)
      exact (ihw hχ d' (List.perm_middle.trans (List.perm_middle.cons χ))).perm
        List.perm_middle.symm

/-- **Bounded contraction**: two copies of a formula of weight `≤ w` collapse
to one. -/
theorem contract_bounded : ∀ (w : Nat) {A : Form}, A.weight ≤ w →
    ∀ {Γ' : List Form} {E : Form}, G4CK Γ' E →
    ∀ {Γ : List Form}, Γ'.Perm (A :: A :: Γ) → G4CK (A :: Γ) E := by
  intro w
  induction w with
  | zero => intro A hA; exact absurd hA (Nat.not_le_of_gt A.weight_pos)
  | succ w ihw =>
      intro A hA Γ' E d
      induction d with
      | botL h =>
          intro Γ hp
          rcases mem_contract hp h with e | h'
          · exact .botL (by rw [e]; exact .head _)
          · exact .botL (.tail _ h')
      | idP h =>
          intro Γ hp
          rcases mem_contract hp h with e | h'
          · exact .idP (by rw [e]; exact .head _)
          · exact .idP (.tail _ h')
      | andR _ _ ih₁ ih₂ => intro Γ hp; exact .andR (ih₁ hp) (ih₂ hp)
      | orR1 _ ih => intro Γ hp; exact .orR1 (ih hp)
      | orR2 _ ih => intro Γ hp; exact .orR2 (ih hp)
      | @impR _ A₀ _ _ ih =>
          intro Γ hp
          exact .impR ((ih ((hp.cons A₀).trans push2)).perm (List.Perm.swap _ _ _))
      | @andL _ Θ A₁ B₁ E₀ h d₁ ih =>
          intro Γ hp
          rcases cross_split3 h hp with ⟨e, hΔ⟩ | ⟨Γ₀, hΔ, hΓ⟩
          · subst e
            have hw₁ : A₁.weight ≤ w := by simp only [Form.weight] at hA; omega
            have hw₂ : B₁.weight ≤ w := by simp only [Form.weight] at hA; omega
            have hinv : G4CK (A₁ :: B₁ :: A₁ :: B₁ :: Γ) E₀ :=
              d₁.inv (.and A₁ B₁) (((hΔ.cons B₁).cons A₁).trans
                (List.perm_middle (l₁ := [A₁, B₁])))
            have c₁ : G4CK (A₁ :: B₁ :: B₁ :: Γ) E₀ :=
              ihw hw₁ hinv ((List.Perm.swap _ _ _).cons _)
            have c₂ : G4CK (B₁ :: A₁ :: Γ) E₀ := ihw hw₂ c₁ push2
            exact .andL (List.Perm.refl _) (c₂.perm (List.Perm.swap _ _ _))
          · exact .andL ((hΓ.cons _).trans (List.Perm.swap _ _ _))
              ((ih (pushL [A₁, B₁] hΔ)).perm (List.perm_middle (l₁ := [A₁, B₁])).symm)
      | @orL _ Θ A₁ B₁ E₀ h d₁ d₂ ih₁ ih₂ =>
          intro Γ hp
          rcases cross_split3 h hp with ⟨e, hΔ⟩ | ⟨Γ₀, hΔ, hΓ⟩
          · subst e
            have hw₁ : A₁.weight ≤ w := by simp only [Form.weight] at hA; omega
            have hw₂ : B₁.weight ≤ w := by simp only [Form.weight] at hA; omega
            have q₁ : G4CK (A₁ :: A₁ :: Γ) E₀ :=
              d₁.inv (.or₁ A₁ B₁) ((hΔ.cons A₁).trans (List.Perm.swap _ _ _))
            have q₂ : G4CK (B₁ :: B₁ :: Γ) E₀ :=
              d₂.inv (.or₂ A₁ B₁) ((hΔ.cons B₁).trans (List.Perm.swap _ _ _))
            exact .orL (List.Perm.refl _) (ihw hw₁ q₁ (List.Perm.refl _))
              (ihw hw₂ q₂ (List.Perm.refl _))
          · exact .orL ((hΓ.cons _).trans (List.Perm.swap _ _ _))
              ((ih₁ (pushL [A₁] hΔ)).perm (List.perm_middle (l₁ := [A₁])).symm)
              ((ih₂ (pushL [B₁] hΔ)).perm (List.perm_middle (l₁ := [B₁])).symm)
      | @impVarL _ Θ a B₁ E₀ h ha d₁ ih =>
          intro Γ hp
          rcases cross_split3 h hp with ⟨e, hΔ⟩ | ⟨Γ₀, hΔ, hΓ⟩
          · subst e
            have hw : B₁.weight ≤ w := by simp only [Form.weight] at hA; omega
            have ha' : Form.var a ∈ Γ := by
              rcases List.mem_cons.1 (hΔ.subset ha) with e' | h''
              · cases e'
              · exact h''
            have q : G4CK (B₁ :: B₁ :: Γ) E₀ :=
              d₁.inv (.impVar a B₁) ((hΔ.cons B₁).trans (List.Perm.swap _ _ _))
            exact .impVarL (List.Perm.refl _) ha' (ihw hw q (List.Perm.refl _))
          · have ha' : Form.var a ∈ A :: Γ₀ := by
              rcases mem_contract hΔ ha with e | h''
              · rw [e]; exact .head _
              · exact .tail _ h''
            exact .impVarL ((hΓ.cons _).trans (List.Perm.swap _ _ _)) ha'
              ((ih (pushL [B₁] hΔ)).perm (List.perm_middle (l₁ := [B₁])).symm)
      | @impAndL _ Θ A₁ B₁ D₁ E₀ h d₁ ih =>
          intro Γ hp
          rcases cross_split3 h hp with ⟨e, hΔ⟩ | ⟨Γ₀, hΔ, hΓ⟩
          · subst e
            have hw : (A₁ ⟶ (B₁ ⟶ D₁)).weight ≤ w := by
              simp only [Form.weight] at hA ⊢; omega
            have q : G4CK ((A₁ ⟶ (B₁ ⟶ D₁)) :: (A₁ ⟶ (B₁ ⟶ D₁)) :: Γ) E₀ :=
              d₁.inv (.impAnd A₁ B₁ D₁) ((hΔ.cons _).trans (List.Perm.swap _ _ _))
            exact .impAndL (List.Perm.refl _) (ihw hw q (List.Perm.refl _))
          · exact .impAndL ((hΓ.cons _).trans (List.Perm.swap _ _ _))
              ((ih (pushL [A₁ ⟶ (B₁ ⟶ D₁)] hΔ)).perm
                (List.perm_middle (l₁ := [A₁ ⟶ (B₁ ⟶ D₁)])).symm)
      | @impOrL _ Θ A₁ B₁ D₁ E₀ h d₁ ih =>
          intro Γ hp
          rcases cross_split3 h hp with ⟨e, hΔ⟩ | ⟨Γ₀, hΔ, hΓ⟩
          · subst e
            have hw₁ : (A₁ ⟶ D₁).weight ≤ w := by simp only [Form.weight] at hA ⊢; omega
            have hw₂ : (B₁ ⟶ D₁).weight ≤ w := by simp only [Form.weight] at hA ⊢; omega
            have q : G4CK ((A₁ ⟶ D₁) :: (B₁ ⟶ D₁) :: (A₁ ⟶ D₁) :: (B₁ ⟶ D₁) :: Γ) E₀ :=
              d₁.inv (.impOr A₁ B₁ D₁) (((hΔ.cons _).cons _).trans
                (List.perm_middle (l₁ := [A₁ ⟶ D₁, B₁ ⟶ D₁])))
            have c₁ : G4CK ((A₁ ⟶ D₁) :: (B₁ ⟶ D₁) :: (B₁ ⟶ D₁) :: Γ) E₀ :=
              ihw hw₁ q ((List.Perm.swap _ _ _).cons _)
            have c₂ : G4CK ((B₁ ⟶ D₁) :: (A₁ ⟶ D₁) :: Γ) E₀ := ihw hw₂ c₁ push2
            exact .impOrL (List.Perm.refl _) (c₂.perm (List.Perm.swap _ _ _))
          · exact .impOrL ((hΓ.cons _).trans (List.Perm.swap _ _ _))
              ((ih (pushL [A₁ ⟶ D₁, B₁ ⟶ D₁] hΔ)).perm
                (List.perm_middle (l₁ := [A₁ ⟶ D₁, B₁ ⟶ D₁])).symm)
      | @impImpL _ Θ A₁ B₁ D₁ E₀ h d₁ d₂ ih₁ ih₂ =>
          intro Γ hp
          rcases cross_split3 h hp with ⟨e, hΔ⟩ | ⟨Γ₀, hΔ, hΓ⟩
          · -- principal: duplicate into premise 1, contract the lighter
            -- pieces, re-abstract (Dyckhoff and Negri)
            subst e
            have hwA : A₁.weight ≤ w := by simp only [Form.weight] at hA; omega
            have hwK : (B₁ ⟶ D₁).weight ≤ w := by simp only [Form.weight] at hA ⊢; omega
            have hwD : D₁.weight ≤ w := by simp only [Form.weight] at hA; omega
            have r₀ : G4CK (A₁ :: (B₁ ⟶ D₁) :: (B₁ ⟶ D₁) :: (B₁ ⟶ D₁) :: Γ) (A₁ ⟶ B₁) :=
              impImpL_dup d₁ ((hΔ.cons _).trans (List.Perm.swap _ _ _))
            have r₁ : G4CK ((B₁ ⟶ D₁) :: A₁ :: (B₁ ⟶ D₁) :: Γ) (A₁ ⟶ B₁) :=
              ihw hwK r₀ push2
            have r₂ : G4CK ((B₁ ⟶ D₁) :: A₁ :: Γ) (A₁ ⟶ B₁) :=
              ihw hwK r₁ ((List.Perm.swap _ _ _).cons _)
            have r₃ : G4CK (A₁ :: (B₁ ⟶ D₁) :: A₁ :: Γ) B₁ := r₂.impR_inv
            have r₄ : G4CK (A₁ :: (B₁ ⟶ D₁) :: Γ) B₁ :=
              ihw hwA r₃ ((List.Perm.swap _ _ _).cons _)
            have q₂ : G4CK (D₁ :: D₁ :: Γ) E₀ :=
              d₂.inv (.impImp A₁ B₁ D₁) ((hΔ.cons _).trans (List.Perm.swap _ _ _))
            exact .impImpL (List.Perm.refl _) (.impR r₄) (ihw hwD q₂ (List.Perm.refl _))
          · exact .impImpL ((hΓ.cons _).trans (List.Perm.swap _ _ _))
              ((ih₁ (pushL [B₁ ⟶ D₁] hΔ)).perm (List.perm_middle (l₁ := [B₁ ⟶ D₁])).symm)
              ((ih₂ (pushL [D₁] hΔ)).perm (List.perm_middle (l₁ := [D₁])).symm)
      | boxR d₁ _ =>
          intro Γ hp
          exact .boxR (unbox_contract (pre := []) ihw hA hp d₁)
      | @impBoxL _ Θ A₁ B₁ E₀ h d₁ d₂ _ ih₂ =>
          intro Γ hp
          rcases cross_split3 h hp with ⟨e, hΔ⟩ | ⟨Γ₀, hΔ, hΓ⟩
          · subst e
            have hw : B₁.weight ≤ w := by simp only [Form.weight] at hA; omega
            have hu : (unbox Θ).Perm (unbox Γ) := by have := unbox_perm hΔ; exact this
            have q₂ : G4CK (B₁ :: B₁ :: Γ) E₀ :=
              d₂.inv (.impBox A₁ B₁) ((hΔ.cons _).trans (List.Perm.swap _ _ _))
            exact .impBoxL (List.Perm.refl _) (d₁.perm hu) (ihw hw q₂ (List.Perm.refl _))
          · exact .impBoxL ((hΓ.cons _).trans (List.Perm.swap _ _ _))
              (unbox_contract (pre := []) ihw hA hΔ d₁)
              ((ih₂ (pushL [B₁] hΔ)).perm (List.perm_middle (l₁ := [B₁])).symm)
      | @impDiaL _ Θ G₁ A₁ B₁ E₀ h hγ d₁ d₂ _ ih₂ =>
          intro Γ hp
          rcases cross_split3 h hp with ⟨e, hΔ⟩ | ⟨Γ₀, hΔ, hΓ⟩
          · subst e
            have hw : B₁.weight ≤ w := by simp only [Form.weight] at hA; omega
            have hu : (unbox Θ).Perm (unbox Γ) := by have := unbox_perm hΔ; exact this
            have hγ' : (◇G₁) ∈ Γ := by
              rcases List.mem_cons.1 (hΔ.subset hγ) with e' | h''
              · cases e'
              · exact h''
            have q₂ : G4CK (B₁ :: B₁ :: Γ) E₀ :=
              d₂.inv (.impDia A₁ B₁) ((hΔ.cons _).trans (List.Perm.swap _ _ _))
            exact .impDiaL (List.Perm.refl _) hγ' (d₁.perm (hu.cons G₁))
              (ihw hw q₂ (List.Perm.refl _))
          · have hγ' : (◇G₁) ∈ A :: Γ₀ := by
              rcases mem_contract hΔ hγ with e | h''
              · rw [e]; exact .head _
              · exact .tail _ h''
            exact .impDiaL ((hΓ.cons _).trans (List.Perm.swap _ _ _)) hγ'
              (unbox_contract (pre := [G₁]) ihw hA hΔ d₁)
              ((ih₂ (pushL [B₁] hΔ)).perm (List.perm_middle (l₁ := [B₁])).symm)
      | @diaL _ Θ A₁ _ h d₁ _ =>
          intro Γ hp
          rcases cross_split3 h hp with ⟨e, hΔ⟩ | ⟨Γ₀, hΔ, hΓ⟩
          · subst e
            have hu : (unbox Θ).Perm (unbox Γ) := by have := unbox_perm hΔ; exact this
            exact .diaL (List.Perm.refl _) (d₁.perm (hu.cons A₁))
          · exact .diaL ((hΓ.cons _).trans (List.Perm.swap _ _ _))
              (unbox_contract (pre := [A₁]) ihw hA hΔ d₁)

/-- **Proposition** (unlabelled, §3): contraction is admissible in G4CK,
`Γ,ψ,ψ ⇒ δ  /  Γ,ψ ⇒ δ`.  Rocq `contraction`. -/
theorem contract {Γ' Γ : List Form} {A E : Form} (d : G4CK Γ' E)
    (hp : Γ'.Perm (A :: A :: Γ)) : G4CK (A :: Γ) E :=
  contract_bounded A.weight (Nat.le_refl _) d hp

end G4CK

end CK

#print axioms CK.G4CK.weakImp
#print axioms CK.G4CK.impImpL_dup
#print axioms CK.G4CK.contract
