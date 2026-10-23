import Mathlib.Order.Completion
import Mathlib.Order.Nucleus
import Mathlib.Data.Sum.Order
import Mathlib.Order.Heyting.Basic
import Mathlib.Order.Nat
import Meta.Audit

/-!
# REFUTED: uniqueness of the nuclear extension to the MacNeille completion

2026-10-22.  `wip/f0MacNeille.lean` extends a nucleus `j` on a Heyting algebra
`H` to the nucleus

    k X = ⨅ { ↓(j a) : a ∈ H, X ≤ ↓a }

on `DM(H)` and proves it the GREATEST monotone extension.  Is it the only
nuclear extension?  No.  One designed witness (CLAUDE.md rule 9):

* `G = ℕ ⊕ₗ ℕᵒᵈ`, the chain `0 < 1 < 2 < ⋯ < ⋯ < 2' < 1' < 0'`, a bounded
  chain and so a Heyting algebra;
* `j` fixes the lower copy of `ℕ` and sends the upper copy to `⊤`;
* `DM(G)` has one new point, the gap cut `m = ⨆ n, ↓n`;
* `k₁ X = (X ≤ m ? X : ⊤)` and `k₂ X = (X < m ? X : ⊤)` are nuclei on `DM(G)`,
  both extend `j`, and `k₁ m = m ≠ ⊤ = k₂ m`.

(`k₂` is the greatest extension of `wip/f0MacNeille.lean`, `k₁` the least.)
The statement `nucleus_extension_not_unique` is about Mathlib's `DedekindCut`,
with no Heyting structure on `DM(G)` used, so it does not meet the scoped frame
instance of `wip/f0MacNeille.lean` (Mathlib's own linear-order structure on
`DedekindCut G` is the one in force here).

Whether uniqueness holds at F0 itself is a separate question and stays OPEN.
-/

namespace MacNeilleNonUnique

open DedekindCut

/-! ## Threshold nuclei on a chain -/

section Threshold

variable {L : Type*} [LinearOrder L] [OrderTop L]

/-- On a chain with top, `X ↦ (P X ? X : ⊤)` is a nucleus whenever `P` is a
down-set. -/
noncomputable def threshold (P : L → Prop) (hP : ∀ X Y, X ≤ Y → P Y → P X) : Nucleus L :=
  have mono : ∀ X Y : L, X ≤ Y →
      (open Classical in if P X then X else ⊤) ≤ (open Classical in if P Y then Y else ⊤) := by
    intro X Y hXY
    classical
    by_cases hY : P Y
    · rw [if_pos (hP X Y hXY hY), if_pos hY]
      exact hXY
    · rw [if_neg hY]
      exact le_top
  { toFun := fun X => open Classical in if P X then X else ⊤
    map_inf' := by
      intro X Y
      rcases le_total X Y with h | h
      · rw [inf_eq_left.mpr h, inf_eq_left.mpr (mono X Y h)]
      · rw [inf_eq_right.mpr h, inf_eq_right.mpr (mono Y X h)]
    idempotent' := by
      intro X
      classical
      by_cases hX : P X
      · simp only [if_pos hX]
        exact le_rfl
      · simp only [if_neg hX]
        split_ifs <;> exact le_rfl
    le_apply' := by
      intro X
      classical
      split_ifs
      · exact le_rfl
      · exact le_top }

theorem threshold_apply_pos (P : L → Prop) (hP) {X : L} (h : P X) : threshold P hP X = X := by
  classical
  show (if P X then X else ⊤) = X
  rw [if_pos h]

theorem threshold_apply_neg (P : L → Prop) (hP) {X : L} (h : ¬ P X) : threshold P hP X = ⊤ := by
  classical
  show (if P X then X else ⊤) = ⊤
  rw [if_neg h]

end Threshold

/-! ## The witness -/

/-- The chain `0 < 1 < 2 < ⋯ < ⋯ < 2' < 1' < 0'`. -/
abbrev G := ℕ ⊕ₗ ℕᵒᵈ

/-- A bounded chain is a Heyting algebra; so `G` is one. -/
noncomputable instance : HeytingAlgebra G :=
  (LinearOrder.toBiheytingAlgebra (α := G)).toHeytingAlgebra

/-- The lower copy of `ℕ`. -/
def lo (n : ℕ) : G := toLex (Sum.inl n)

/-- The upper copy, reversed. -/
def hi (d : ℕ) : G := toLex (Sum.inr (OrderDual.toDual d))

theorem cases_G (x : G) : (∃ n, x = lo n) ∨ (∃ d, x = hi d) := by
  rcases x with n | d
  · exact .inl ⟨n, rfl⟩
  · exact .inr ⟨OrderDual.ofDual d, rfl⟩

theorem lo_le_hi (n d : ℕ) : lo n ≤ hi d := Sum.Lex.inl_le_inr _ _

theorem not_hi_le_lo (n d : ℕ) : ¬ hi d ≤ lo n := Sum.Lex.not_inr_le_inl

theorem hi_le_hi_iff (d e : ℕ) : hi d ≤ hi e ↔ e ≤ d := by
  rw [hi, hi, Sum.Lex.inr_le_inr_iff, OrderDual.toDual_le_toDual]

theorem lo_lt_lo (n : ℕ) : lo n < lo (n + 1) := by
  rw [lo, lo, Sum.Lex.inl_lt_inl_iff]
  exact Nat.lt_succ_self n

/-- The lower copy is a down-set. -/
def IsLo (x : G) : Prop := ∃ n, x = lo n

theorem isLo_down (x y : G) (hxy : x ≤ y) (hy : IsLo y) : IsLo x := by
  obtain ⟨n, rfl⟩ := hy
  rcases cases_G x with ⟨k, rfl⟩ | ⟨d, rfl⟩
  · exact ⟨k, rfl⟩
  · exact absurd hxy (not_hi_le_lo n d)

theorem not_isLo_hi (d : ℕ) : ¬ IsLo (hi d) := by
  rintro ⟨n, h⟩
  exact not_hi_le_lo n d h.le

/-- The nucleus `j` on `G`: identity on the lower copy, `⊤` on the upper. -/
noncomputable def j : Nucleus G := threshold IsLo isLo_down

/-- The gap cut. -/
noncomputable def m : DedekindCut G := ⨆ n : ℕ, principal (lo n)

theorem principal_lo_le_m (n : ℕ) : principal (lo n) ≤ m := le_iSup (fun n => principal (lo n)) n

theorem not_principal_hi_le_m (d : ℕ) : ¬ principal (hi d) ≤ m := by
  intro h
  have hm : m ≤ principal (hi (d + 1)) :=
    iSup_le fun n => principal_le_principal.mpr (lo_le_hi n (d + 1))
  have := principal_le_principal.mp (h.trans hm)
  rw [hi_le_hi_iff] at this
  omega

theorem principal_lo_lt_m (n : ℕ) : principal (lo n) < m :=
  lt_of_lt_of_le (principal_lt_principal.mpr (lo_lt_lo n)) (principal_lo_le_m (n + 1))

theorem principal_top_G : principal (⊤ : G) = ⊤ := by
  apply DedekindCut.ext
  ext x
  simp

theorem m_ne_top : m ≠ ⊤ := by
  intro h
  apply not_principal_hi_le_m 0
  rw [h]
  exact le_top

/-- The least extension: the gap point is fixed. -/
noncomputable def k₁ : Nucleus (DedekindCut G) :=
  threshold (· ≤ m) (fun _ _ hXY hY => hXY.trans hY)

/-- The greatest extension: the gap point goes to `⊤`. -/
noncomputable def k₂ : Nucleus (DedekindCut G) :=
  threshold (· < m) (fun _ _ hXY hY => lt_of_le_of_lt hXY hY)

theorem j_lo (n : ℕ) : j (lo n) = lo n := threshold_apply_pos _ _ (⟨n, rfl⟩ : IsLo (lo n))

theorem j_hi (d : ℕ) : j (hi d) = ⊤ := threshold_apply_neg _ _ (not_isLo_hi d)

theorem k₁_pos {X : DedekindCut G} (h : X ≤ m) : k₁ X = X := threshold_apply_pos _ _ h

theorem k₁_neg {X : DedekindCut G} (h : ¬ X ≤ m) : k₁ X = ⊤ := threshold_apply_neg _ _ h

theorem k₂_pos {X : DedekindCut G} (h : X < m) : k₂ X = X := threshold_apply_pos _ _ h

theorem k₂_neg {X : DedekindCut G} (h : ¬ X < m) : k₂ X = ⊤ := threshold_apply_neg _ _ h

theorem k₁_ext (a : G) : k₁ (principal a) = principal (j a) := by
  rcases cases_G a with ⟨n, rfl⟩ | ⟨d, rfl⟩
  · rw [k₁_pos (principal_lo_le_m n), j_lo]
  · rw [k₁_neg (not_principal_hi_le_m d), j_hi, principal_top_G]

theorem k₂_ext (a : G) : k₂ (principal a) = principal (j a) := by
  rcases cases_G a with ⟨n, rfl⟩ | ⟨d, rfl⟩
  · rw [k₂_pos (principal_lo_lt_m n), j_lo]
  · rw [k₂_neg (fun h => not_principal_hi_le_m d h.le), j_hi, principal_top_G]

theorem k₁_m : k₁ m = m := threshold_apply_pos _ _ (le_refl m)

theorem k₂_m : k₂ m = ⊤ := threshold_apply_neg _ _ (lt_irrefl m)

/-- **REFUTED: the nuclear extension to the MacNeille completion is unique.**
`G` is a Heyting algebra (a bounded chain), `j` a nucleus on it, and two
different nuclei on `DM(G)` extend `j` along `principal`. -/
theorem nucleus_extension_not_unique :
    ∃ (j : Nucleus G) (k k' : Nucleus (DedekindCut G)),
      (∀ a, k (principal a) = principal (j a)) ∧
      (∀ a, k' (principal a) = principal (j a)) ∧ k ≠ k' :=
  ⟨j, k₁, k₂, k₁_ext, k₂_ext, fun h => m_ne_top (by rw [← k₁_m, h, k₂_m])⟩

end MacNeilleNonUnique

/-! ## Pins (each watched failing at `[]` first, 2026-10-22) -/

#axioms_within MacNeilleNonUnique.nucleus_extension_not_unique [propext, Classical.choice, Quot.sound]
#axioms_within MacNeilleNonUnique.k₁_ext [propext, Classical.choice, Quot.sound]
#axioms_within MacNeilleNonUnique.k₂_ext [propext, Classical.choice, Quot.sound]
