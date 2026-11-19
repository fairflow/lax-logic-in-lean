import CK.Order

/-!
# `CK.Cut` — additive cut for G4CK

The unlabelled **Theorem** of §3 of van der Giessen and Shillito,
arXiv:2602.16880v2:

    Γ ⇒ φ    φ,Γ ⇒ ψ   /   Γ ⇒ ψ.

Rocq `additive_cut` in `theories/Sequent/G4CK/CKCut.v` (commit `cd09fce`).
As there: induction on the weight of the cut formula `φ`, then on the measure
of the conclusion `Γ ⇒ ψ` (`CK.sw`), then by cases on the last rule of the
left premise; when that rule is `(→R)`, `(□R)` or `(◇L)`, by cases on the
last rule of the right premise (`cut_impR`, `cut_boxR`, `cut_diaL`).
-/

namespace CK

open scoped Form

/-- Cut on `φ` at the sequent `Γ₀ ⇒ ψ₀`. -/
abbrev CutAt (φ : Form) (Γ₀ : List Form) (ψ₀ : Form) : Prop :=
  G4CK Γ₀ φ → G4CK (φ :: Γ₀) ψ₀ → G4CK Γ₀ ψ₀

/-- Cut on every formula of weight `≤ w`. -/
abbrev CutUpTo (w : Nat) : Prop :=
  ∀ {φ : Form}, φ.weight ≤ w → ∀ {Γ : List Form} {ψ : Form}, CutAt φ Γ ψ

/-! ## Measure of the premises of the right rules -/

theorem sw_andR₁ (Γ : List Form) (A B : Form) : sw Γ A < sw Γ (A ⋏ B) := by
  have := pow5_lt (x := A.weight) (e := A.weight + B.weight + 2) (by omega)
  show wt Γ + 5 ^ A.weight < wt Γ + 5 ^ (A.weight + B.weight + 2)
  omega

theorem sw_andR₂ (Γ : List Form) (A B : Form) : sw Γ B < sw Γ (A ⋏ B) := by
  have := pow5_lt (x := B.weight) (e := A.weight + B.weight + 2) (by omega)
  show wt Γ + 5 ^ B.weight < wt Γ + 5 ^ (A.weight + B.weight + 2)
  omega

theorem sw_orR₁ (Γ : List Form) (A B : Form) : sw Γ A < sw Γ (A ⋎ B) := by
  have := pow5_lt (x := A.weight) (e := A.weight + B.weight + 1)
    (by have := B.weight_pos; omega)
  show wt Γ + 5 ^ A.weight < wt Γ + 5 ^ (A.weight + B.weight + 1)
  omega

theorem sw_orR₂ (Γ : List Form) (A B : Form) : sw Γ B < sw Γ (A ⋎ B) := by
  have := pow5_lt (x := B.weight) (e := A.weight + B.weight + 1)
    (by have := A.weight_pos; omega)
  show wt Γ + 5 ^ B.weight < wt Γ + 5 ^ (A.weight + B.weight + 1)
  omega

theorem sw_impR (Γ : List Form) (A B : Form) : sw (A :: Γ) B < sw Γ (A ⟶ B) := by
  have := two_pow5_lt (x := A.weight) (y := B.weight) (e := A.weight + B.weight + 1)
    (by have := B.weight_pos; omega) (by have := A.weight_pos; omega)
  show 5 ^ A.weight + wt Γ + 5 ^ B.weight < wt Γ + 5 ^ (A.weight + B.weight + 1)
  omega

/-- `5^x + 5^y + 5^z < 5^e` when `x, y, z < e`: the reason for the base 5. -/
theorem three_pow5_lt {x y z e : Nat} (hx : x + 1 ≤ e) (hy : y + 1 ≤ e) (hz : z + 1 ≤ e) :
    5 ^ x + 5 ^ y + 5 ^ z < 5 ^ e := by
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
  have h₁ : 5 ^ x ≤ 5 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
  have h₂ : 5 ^ y ≤ 5 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
  have h₃ : 5 ^ z ≤ 5 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
  have h₄ : 5 ^ (k + 1) = 5 ^ k * 5 := Nat.pow_succ ..
  have h₅ := pow5_pos k
  omega

/-- The first premise of `(→→L)`, read with `(→R)` inverted, is below the
conclusion. -/
theorem sw_impImp₁ {Γ l' : List Form} {A B D : Form} (ψ : Form)
    (hΓ : Γ.Perm (((A ⟶ B) ⟶ D) :: l')) : sw (A :: (B ⟶ D) :: l') B < sw Γ ψ := by
  have h₁ : wt Γ = 5 ^ (A.weight + B.weight + 1 + D.weight + 1) + wt l' := wt_perm hΓ
  have h₂ := three_pow5_lt (x := A.weight) (y := B.weight + D.weight + 1) (z := B.weight)
    (e := A.weight + B.weight + 1 + D.weight + 1) (by omega) (by omega) (by omega)
  have h₃ := pow5_pos ψ.weight
  show 5 ^ A.weight + (5 ^ (B.weight + D.weight + 1) + wt l') + 5 ^ B.weight
    < wt Γ + 5 ^ ψ.weight
  omega

/-! ## Helpers -/

namespace G4CK

/-- An implication in the antecedent may be replaced by its consequent.
Rocq `imp_cut`. -/
theorem impL_inv : ∀ (A : Form) {B θ : Form} {Γ : List Form},
    G4CK ((A ⟶ B) :: Γ) θ → G4CK (B :: Γ) θ
  | .var p, B, _, _, d => d.inv (.impVar p B) (List.Perm.refl _)
  | .bot, B, _, _, d => (d.inv (.impBot B) (List.Perm.refl _)).weaken B
  | .and A₁ A₂, B, _, _, d =>
      impL_inv A₂ (impL_inv A₁ (d.inv (.impAnd A₁ A₂ B) (List.Perm.refl _)))
  | .or A₁ A₂, B, _, _, d =>
      have d₁ := impL_inv A₁ (d.inv (.impOr A₁ A₂ B) (List.Perm.refl _))
      have d₂ := impL_inv A₂ (d₁.perm (List.Perm.swap _ _ _))
      d₂.contract (List.Perm.refl _)
  | .imp A₁ A₂, B, _, _, d => d.inv (.impImp A₁ A₂ B) (List.Perm.refl _)
  | .box A₁, B, _, _, d => d.inv (.impBox A₁ B) (List.Perm.refl _)
  | .dia A₁, B, _, _, d => d.inv (.impDia A₁ B) (List.Perm.refl _)

end G4CK

/-- A member other than the head. -/
theorem mem_of_perm_cons_ne {Δ l' : List Form} {φ Y : Form} (hΔ : Δ.Perm (φ :: l'))
    (h : Y ∈ Δ) (hne : Y ≠ φ) : Y ∈ l' := by
  rcases List.mem_cons.1 (hΔ.subset h) with e | h'
  · exact absurd e hne
  · exact h'

/-- Commuting a cut past an invertible left rule of the right premise. -/
theorem rc {φ ψ X : Form} {Γ Δ l' L : List Form}
    (IHW : ∀ {Γ₀ : List Form} {ψ₀ : Form}, sw Γ₀ ψ₀ < sw Γ ψ → CutAt φ Γ₀ ψ₀)
    (HPφ : G4CK Γ φ) (hInv : Inv X L) (hΓ : Γ.Perm (X :: l')) (hΔ : Δ.Perm (φ :: l'))
    (e : G4CK (L ++ Δ) ψ) : G4CK (L ++ l') ψ :=
  IHW (sw_replace_lt ψ hΓ hInv.wt_lt) (HPφ.inv hInv hΓ)
    ((e.perm (hΔ.append_left L)).perm List.perm_middle)

/-- The first premise of `(→→L)` in the right premise, when the cut formula
is not principal (Rocq, case V-d). -/
theorem rcImpImp₁ {φ ψ A₁ B₁ D₁ : Form} {Γ Δ l' : List Form}
    (IHW : ∀ {Γ₀ : List Form} {ψ₀ : Form}, sw Γ₀ ψ₀ < sw Γ ψ → CutAt φ Γ₀ ψ₀)
    (HPφ : G4CK Γ φ) (hΓ : Γ.Perm (((A₁ ⟶ B₁) ⟶ D₁) :: l')) (hΔ : Δ.Perm (φ :: l'))
    (e₁ : G4CK ((B₁ ⟶ D₁) :: Δ) (A₁ ⟶ B₁)) : G4CK ((B₁ ⟶ D₁) :: l') (A₁ ⟶ B₁) := by
  have leftD : G4CK (A₁ :: (B₁ ⟶ D₁) :: l') φ :=
    ((HPφ.impImpL_dup hΓ).contract
      (Γ := A₁ :: l') ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons _))).perm
      (List.Perm.swap _ _ _)
  have rightD : G4CK (φ :: A₁ :: (B₁ ⟶ D₁) :: l') B₁ :=
    e₁.impR_inv.perm (((hΔ.cons _).cons _).trans
      (List.perm_middle (l₁ := [A₁, B₁ ⟶ D₁])))
  exact .impR (IHW (sw_impImp₁ ψ hΓ) leftD rightD)

/-! ## The left premise ends in `(→R)` -/

theorem cut_impR {w : Nat} (IHw : CutUpTo w) {A B ψ : Form} {Γ : List Form}
    (hw : (A ⟶ B).weight ≤ w + 1)
    (IHW : ∀ {Γ₀ : List Form} {ψ₀ : Form}, sw Γ₀ ψ₀ < sw Γ ψ → CutAt (A ⟶ B) Γ₀ ψ₀)
    (d : G4CK (A :: Γ) B) :
    ∀ {Γ' : List Form}, G4CK Γ' ψ → Γ'.Perm ((A ⟶ B) :: Γ) → G4CK Γ ψ := by
  have HPφ : G4CK Γ (A ⟶ B) := .impR d
  intro Γ' HPψ hp
  cases HPψ with
  | botL h =>
      rcases List.mem_cons.1 (hp.subset h) with e | h'
      · cases e
      · exact .botL h'
  | idP h =>
      rcases List.mem_cons.1 (hp.subset h) with e | h'
      · cases e
      · exact .idP h'
  | andR e₁ e₂ =>
      exact .andR (IHW (sw_andR₁ _ _ _) HPφ (e₁.perm hp)) (IHW (sw_andR₂ _ _ _) HPφ (e₂.perm hp))
  | orR1 e => exact .orR1 (IHW (sw_orR₁ _ _ _) HPφ (e.perm hp))
  | orR2 e => exact .orR2 (IHW (sw_orR₂ _ _ _) HPφ (e.perm hp))
  | @impR _ C₁ C₂ e =>
      exact .impR (IHW (sw_impR _ _ _) (HPφ.weaken C₁)
        (e.perm ((hp.cons C₁).trans (List.Perm.swap _ _ _))))
  | @andL _ Δ A' B' _ h e =>
      rcases perm_cons_cases (h.symm.trans hp) with ⟨e', _⟩ | ⟨l', hΔ, hΓ⟩
      · cases e'
      · exact .andL hΓ (rc IHW HPφ (.and A' B') hΓ hΔ e)
  | @orL _ Δ A' B' _ h e₁ e₂ =>
      rcases perm_cons_cases (h.symm.trans hp) with ⟨e', _⟩ | ⟨l', hΔ, hΓ⟩
      · cases e'
      · exact .orL hΓ (rc IHW HPφ (.or₁ A' B') hΓ hΔ e₁) (rc IHW HPφ (.or₂ A' B') hΓ hΔ e₂)
  | @impVarL _ Δ p B' _ h ha e =>
      rcases perm_cons_cases (h.symm.trans hp) with ⟨e', hΔΓ⟩ | ⟨l', hΔ, hΓ⟩
      · -- principal: `A = p`, `p ∈ Γ`
        obtain ⟨rfl, rfl⟩ : A = Form.var p ∧ B = B' := by cases e'; exact ⟨rfl, rfl⟩
        have hB : B.weight ≤ w := by simp only [Form.weight] at hw; omega
        obtain ⟨Γ₀, hΓ₀⟩ := exists_perm_cons_of_mem (hΔΓ.subset ha)
        have dB : G4CK Γ B := (d.contract (hΓ₀.cons _)).perm hΓ₀.symm
        exact IHw hB dB (e.perm (hΔΓ.cons _))
      · exact .impVarL hΓ (mem_of_perm_cons_ne hΔ ha (by intro e'; cases e'))
          (rc IHW HPφ (.impVar p B') hΓ hΔ e)
  | @impAndL _ Δ A₁ B₁ D₁ _ h e =>
      rcases perm_cons_cases (h.symm.trans hp) with ⟨e', hΔΓ⟩ | ⟨l', hΔ, hΓ⟩
      · obtain ⟨rfl, rfl⟩ : A = (A₁ ⋏ B₁) ∧ D₁ = B := by cases e'; exact ⟨rfl, rfl⟩
        have hK : (A₁ ⟶ (B₁ ⟶ D₁)).weight ≤ w := by simp only [Form.weight] at hw ⊢; omega
        have dK : G4CK Γ (A₁ ⟶ (B₁ ⟶ D₁)) :=
          .impR (.impR ((d.inv (.and A₁ B₁) (List.Perm.refl _)).perm (List.Perm.swap _ _ _)))
        exact IHw hK dK (e.perm (hΔΓ.cons _))
      · exact .impAndL hΓ (rc IHW HPφ (.impAnd A₁ B₁ D₁) hΓ hΔ e)
  | @impOrL _ Δ A₁ B₁ D₁ _ h e =>
      rcases perm_cons_cases (h.symm.trans hp) with ⟨e', hΔΓ⟩ | ⟨l', hΔ, hΓ⟩
      · obtain ⟨rfl, rfl⟩ : A = (A₁ ⋎ B₁) ∧ D₁ = B := by cases e'; exact ⟨rfl, rfl⟩
        have hK₁ : (A₁ ⟶ D₁).weight ≤ w := by simp only [Form.weight] at hw ⊢; omega
        have hK₂ : (B₁ ⟶ D₁).weight ≤ w := by simp only [Form.weight] at hw ⊢; omega
        have dA : G4CK Γ (A₁ ⟶ D₁) := .impR (d.inv (.or₁ A₁ B₁) (List.Perm.refl _))
        have dB : G4CK Γ (B₁ ⟶ D₁) := .impR (d.inv (.or₂ A₁ B₁) (List.Perm.refl _))
        have e' : G4CK ((B₁ ⟶ D₁) :: (A₁ ⟶ D₁) :: Γ) ψ :=
          e.perm ((((hΔΓ.cons _).cons _)).trans (List.Perm.swap _ _ _))
        exact IHw hK₁ dA (IHw hK₂ (dB.weaken _) e')
      · exact .impOrL hΓ (rc IHW HPφ (.impOr A₁ B₁ D₁) hΓ hΔ e)
  | @impImpL _ Δ A₁ B₁ D₁ _ h e₁ e₂ =>
      rcases perm_cons_cases (h.symm.trans hp) with ⟨e', hΔΓ⟩ | ⟨l', hΔ, hΓ⟩
      · obtain ⟨rfl, rfl⟩ : A = (A₁ ⟶ B₁) ∧ D₁ = B := by cases e'; exact ⟨rfl, rfl⟩
        have hK : (B₁ ⟶ D₁).weight ≤ w := by
          have := A₁.weight_pos; simp only [Form.weight] at hw ⊢; omega
        have hAB : (A₁ ⟶ B₁).weight ≤ w := by
          have := D₁.weight_pos; simp only [Form.weight] at hw ⊢; omega
        have hD : D₁.weight ≤ w := by simp only [Form.weight] at hw; omega
        have dK : G4CK Γ (B₁ ⟶ D₁) := .impR (G4CK.impL_inv A₁ d)
        have dAB : G4CK Γ (A₁ ⟶ B₁) := IHw hK dK (e₁.perm (hΔΓ.cons _))
        have dD : G4CK Γ D₁ := IHw hAB dAB d
        exact IHw hD dD (e₂.perm (hΔΓ.cons _))
      · exact .impImpL hΓ (rcImpImp₁ IHW HPφ hΓ hΔ e₁)
          (rc IHW HPφ (.impImp A₁ B₁ D₁) hΓ hΔ e₂)
  | boxR e =>
      have hu : (unbox Γ').Perm (unbox Γ) := by have := unbox_perm hp; exact this
      exact .boxR (e.perm hu)
  | @impBoxL _ Δ A₁ B₁ _ h e₁ e₂ =>
      rcases perm_cons_cases (h.symm.trans hp) with ⟨e', hΔΓ⟩ | ⟨l', hΔ, hΓ⟩
      · obtain ⟨rfl, rfl⟩ : A = (□A₁) ∧ B = B₁ := by cases e'; exact ⟨rfl, rfl⟩
        have hA : (□A₁).weight ≤ w := by
          have := B.weight_pos; simp only [Form.weight] at hw ⊢; omega
        have hB : B.weight ≤ w := by simp only [Form.weight] at hw; omega
        have dBox : G4CK Γ (□A₁) := .boxR (e₁.perm (unbox_perm hΔΓ))
        exact IHw hB (IHw hA dBox d) (e₂.perm (hΔΓ.cons _))
      · have hu : (unbox Δ).Perm (unbox l') := by have := unbox_perm hΔ; exact this
        exact .impBoxL hΓ (e₁.perm hu) (rc IHW HPφ (.impBox A₁ B₁) hΓ hΔ e₂)
  | @impDiaL _ Δ G₁ A₁ B₁ _ h hγ e₁ e₂ =>
      rcases perm_cons_cases (h.symm.trans hp) with ⟨e', hΔΓ⟩ | ⟨l', hΔ, hΓ⟩
      · obtain ⟨rfl, rfl⟩ : A = (◇A₁) ∧ B = B₁ := by cases e'; exact ⟨rfl, rfl⟩
        have hA : (◇A₁).weight ≤ w := by
          have := B.weight_pos; simp only [Form.weight] at hw ⊢; omega
        have hB : B.weight ≤ w := by simp only [Form.weight] at hw; omega
        obtain ⟨Γ₀, hΓ₀⟩ := exists_perm_cons_of_mem (hΔΓ.subset hγ)
        have hu : (unbox Δ).Perm (unbox Γ₀) := by
          have := unbox_perm (hΔΓ.trans hΓ₀); exact this
        have dDia : G4CK Γ (◇A₁) := .diaL hΓ₀ (e₁.perm (hu.cons G₁))
        exact IHw hB (IHw hA dDia d) (e₂.perm (hΔΓ.cons _))
      · have hu : (unbox Δ).Perm (unbox l') := by have := unbox_perm hΔ; exact this
        exact .impDiaL hΓ (mem_of_perm_cons_ne hΔ hγ (by intro e'; cases e'))
          (e₁.perm (hu.cons G₁)) (rc IHW HPφ (.impDia A₁ B₁) hΓ hΔ e₂)
  | @diaL _ Δ A₁ _ h e =>
      rcases perm_cons_cases (h.symm.trans hp) with ⟨e', _⟩ | ⟨l', hΔ, hΓ⟩
      · cases e'
      · have hu : (unbox Δ).Perm (unbox l') := by have := unbox_perm hΔ; exact this
        exact .diaL hΓ (e.perm (hu.cons A₁))

end CK

#print axioms CK.cut_impR
