import CK.Contraction

/-!
# `CK.Order` — the sequent measure

**Definition 2** (unlabelled, "Sequent ordering") of van der Giessen and
Shillito, arXiv:2602.16880v2, §3, in the form the Rocq development
mechanises it (`env_weight`, `env_order`, `pointed_env_order` in
`theories/Sequent/G4CK/CKOrder.v`, commit `cd09fce`):

    wt Γ := Σ_{φ ∈ Γ} 5^{w(φ)},        Γ ⇒ φ  ≺  Π ⇒ ψ   iff   wt(Γ,φ) < wt(Π,ψ).

**Divergence D5.**  The paper defines `≺` as the Dershowitz–Manna multiset
extension of the order by weight.  Rocq uses the natural number above, and
so does this file: it needs no well-foundedness theorem beyond `<` on `ℕ`
(Mathlib's Dershowitz–Manna theorem depends on `Classical.choice`), and it
decreases on every premise of every rule, which is all the paper uses.
-/

namespace CK

open scoped Form

/-- `wt Γ = Σ_{φ ∈ Γ} 5^{w(φ)}`.  Rocq `env_weight`. -/
def wt : List Form → Nat
  | [] => 0
  | φ :: Γ => 5 ^ φ.weight + wt Γ

/-- The measure of a sequent `Γ ⇒ φ`.  Rocq `pointed_env_order` compares
these. -/
def sw (Γ : List Form) (φ : Form) : Nat := wt Γ + 5 ^ φ.weight

theorem wt_perm {Γ Γ' : List Form} (h : Γ.Perm Γ') : wt Γ = wt Γ' := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (5 ^ a.weight + ·) ih
  | swap a b l => exact Nat.add_left_comm _ _ _
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem wt_append : ∀ L Δ : List Form, wt (L ++ Δ) = wt L + wt Δ
  | [], Δ => (Nat.zero_add _).symm
  | φ :: L, Δ => by
      show 5 ^ φ.weight + wt (L ++ Δ) = 5 ^ φ.weight + wt L + wt Δ
      rw [wt_append L Δ, Nat.add_assoc]

theorem pow5_pos (n : Nat) : 0 < 5 ^ n := Nat.pow_pos (by decide)

/-- Core's `Nat.pow_lt_pow_right` depends on `Classical.choice`; this does
not. -/
theorem pow5_lt {x e : Nat} (h : x + 1 ≤ e) : 5 ^ x < 5 ^ e := by
  have h₁ : 5 ^ (x + 1) ≤ 5 ^ e := Nat.pow_le_pow_right (by decide) h
  have h₂ : 5 ^ (x + 1) = 5 ^ x * 5 := Nat.pow_succ ..
  have h₃ := pow5_pos x
  omega

/-- `5^x + 5^y < 5^e` when `x, y < e`. -/
theorem two_pow5_lt {x y e : Nat} (hx : x + 1 ≤ e) (hy : y + 1 ≤ e) :
    5 ^ x + 5 ^ y < 5 ^ e := by
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
  have h₁ : 5 ^ x ≤ 5 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
  have h₂ : 5 ^ y ≤ 5 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
  have h₃ : 5 ^ (k + 1) = 5 ^ k * 5 := Nat.pow_succ ..
  have h₄ := pow5_pos k
  omega

/-- `□⁻¹` does not increase the measure. -/
theorem wt_unbox_le : ∀ Γ : List Form, wt (unbox Γ) ≤ wt Γ
  | [] => Nat.le_refl _
  | .var _ :: Γ => Nat.le_trans (wt_unbox_le Γ) (Nat.le_add_left _ _)
  | .bot :: Γ => Nat.le_trans (wt_unbox_le Γ) (Nat.le_add_left _ _)
  | .and _ _ :: Γ => Nat.le_trans (wt_unbox_le Γ) (Nat.le_add_left _ _)
  | .or _ _ :: Γ => Nat.le_trans (wt_unbox_le Γ) (Nat.le_add_left _ _)
  | .imp _ _ :: Γ => Nat.le_trans (wt_unbox_le Γ) (Nat.le_add_left _ _)
  | .dia _ :: Γ => Nat.le_trans (wt_unbox_le Γ) (Nat.le_add_left _ _)
  | .box φ :: Γ => by
      show 5 ^ φ.weight + wt (unbox Γ) ≤ 5 ^ (φ.weight + 1) + wt Γ
      have := wt_unbox_le Γ
      have := Nat.le_of_lt (pow5_lt (Nat.le_refl (φ.weight + 1)))
      omega

/-- Each inversion strictly decreases the measure. -/
theorem Inv.wt_lt {P : Form} {L : List Form} (h : Inv P L) : wt L < 5 ^ P.weight := by
  cases h with
  | and φ ψ =>
      show 5 ^ φ.weight + (5 ^ ψ.weight + 0) < 5 ^ (φ.weight + ψ.weight + 2)
      have := two_pow5_lt (x := φ.weight) (y := ψ.weight) (e := φ.weight + ψ.weight + 2)
        (by omega) (by omega)
      omega
  | or₁ φ ψ =>
      show 5 ^ φ.weight + 0 < 5 ^ (φ.weight + ψ.weight + 1)
      have := pow5_lt (x := φ.weight) (e := φ.weight + ψ.weight + 1)
        (by have := ψ.weight_pos; omega)
      omega
  | or₂ φ ψ =>
      show 5 ^ ψ.weight + 0 < 5 ^ (φ.weight + ψ.weight + 1)
      have := pow5_lt (x := ψ.weight) (e := φ.weight + ψ.weight + 1)
        (by have := φ.weight_pos; omega)
      omega
  | impVar p φ =>
      show 5 ^ φ.weight + 0 < 5 ^ (1 + φ.weight + 1)
      have := pow5_lt (x := φ.weight) (e := 1 + φ.weight + 1) (by omega)
      omega
  | impBot φ => exact pow5_pos _
  | impAnd φ ψ χ =>
      show 5 ^ (φ.weight + (ψ.weight + χ.weight + 1) + 1) + 0
        < 5 ^ (φ.weight + ψ.weight + 2 + χ.weight + 1)
      have := pow5_lt (x := φ.weight + (ψ.weight + χ.weight + 1) + 1)
        (e := φ.weight + ψ.weight + 2 + χ.weight + 1) (by omega)
      omega
  | impOr φ ψ χ =>
      show 5 ^ (φ.weight + χ.weight + 1) + (5 ^ (ψ.weight + χ.weight + 1) + 0)
        < 5 ^ (φ.weight + ψ.weight + 1 + χ.weight + 1)
      have := two_pow5_lt (x := φ.weight + χ.weight + 1) (y := ψ.weight + χ.weight + 1)
        (e := φ.weight + ψ.weight + 1 + χ.weight + 1)
        (by have := ψ.weight_pos; omega) (by have := φ.weight_pos; omega)
      omega
  | impImp φ ψ χ =>
      show 5 ^ χ.weight + 0 < 5 ^ (φ.weight + ψ.weight + 1 + χ.weight + 1)
      have := pow5_lt (x := χ.weight) (e := φ.weight + ψ.weight + 1 + χ.weight + 1) (by omega)
      omega
  | impBox φ ψ =>
      show 5 ^ ψ.weight + 0 < 5 ^ (φ.weight + 1 + ψ.weight + 1)
      have := pow5_lt (x := ψ.weight) (e := φ.weight + 1 + ψ.weight + 1) (by omega)
      omega
  | impDia φ ψ =>
      show 5 ^ ψ.weight + 0 < 5 ^ (φ.weight + 1 + ψ.weight + 1)
      have := pow5_lt (x := ψ.weight) (e := φ.weight + 1 + ψ.weight + 1) (by omega)
      omega

/-- Replacing an antecedent formula `X` by a lighter list decreases the
measure of the sequent. -/
theorem sw_replace_lt {Γ Δ L : List Form} {X : Form} (ψ : Form) (h : Γ.Perm (X :: Δ))
    (hL : wt L < 5 ^ X.weight) : sw (L ++ Δ) ψ < sw Γ ψ := by
  have h₁ : wt Γ = 5 ^ X.weight + wt Δ := wt_perm h
  have h₂ := wt_append L Δ
  unfold sw
  omega

end CK

#print axioms CK.Inv.wt_lt
#print axioms CK.sw_replace_lt
#print axioms CK.two_pow5_lt
#print axioms CK.pow5_lt
#print axioms CK.wt_unbox_le
#print axioms CK.wt_perm
