import LaxLogic.ClosedFragmentLattice
import wip.floor
import wip.f0Minkowski
import Mathlib.Order.Completion
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Tactic.DeriveCountable
import Meta.Audit

/-!
# Points of the MacNeille completion of F0

2026-10-25, Paper III v0.5.  `F* = DedekindCut RNClass`, the cuts `(L, U)` of
F0 with `U = Lᵘ` and `L = Uˡ`.

* **(D) A point of F* that is not principal** (`exists_nonprincipal`): the
  gap cut `⋀ { ↓g_k : k ≥ 1 }`.  Were it `↓a`, then `a` would be a greatest
  lower bound of the gaps in F0, against `L_no_greatest` (`wip/floor.lean`).
* **(C) |F*| = 2^ℵ₀** (`card_eq_continuum`).  Above: a cut is determined by
  its left set, and F0 is countable (onto it from a countable syntax of
  variable-free formulas, `CF`).  Below: `r ↦ X_r = ⋁ { ↓f'(q) : q < r }`,
  `f'` the choice-free embedding of ℚ (`rat_embedding_cf`), is one-to-one on
  ℝ: for `r < r'` take rationals `r < q₁ < q₂ < r'`; then
  `X_r ≤ ↓f'(q₁) < ↓f'(q₂) ≤ X_r'`.

Pins: `[propext, Classical.choice, Quot.sound]`, each watched failing at
`[propext, Quot.sound]` (2026-10-25).  Choice enters (`#choice_path`) through
Mathlib's order on cuts (`Concept.instPartialOrder`, by
`Set.instCompleteAtomicBooleanAlgebra`), through `L_no_greatest` (excluded
middle in `plain_trace_dichotomy`, `wip/floor.lean`) and the completeness
theorem behind `le_iff_nonempty` for (D), and through ℝ (`Real.linearOrder`),
the cardinals and `Countable` for (C).
-/

open PLLFormula

namespace PLLND
namespace F0
namespace Points

open SemUI RNEmbed LaxInfinite
open DedekindCut

/-- The class of a closed formula. -/
def cl (φ : PLLFormula) (h : atomFree φ = true) : RNClass := Quotient.mk _ (Closed.mk φ h)

/-- The order of F0 is derivability. -/
theorem mk_le_iff {c d : Closed} :
    (Quotient.mk _ c : RNClass) ≤ Quotient.mk _ d ↔ Deriv [c.1] d.1 := le_iff_nonempty

/-! ## (D) A non-principal point: the gap cut -/

/-- The gaps `g_k`, `k ≥ 1`, in F0. -/
def gaps : Set RNClass := {x | ∃ k, 1 ≤ k ∧ x = cl (gap k) (gap_atomFree k)}

/-- **The gap cut** `⋀ { ↓g_k : k ≥ 1 }`. -/
noncomputable def gapCut : DedekindCut RNClass := sInf (principal '' gaps)

/-- **The gap cut is not principal.** -/
theorem gapCut_ne_principal (a : RNClass) : gapCut ≠ principal a := by
  intro h
  obtain ⟨c, rfl⟩ := Quotient.exists_rep a
  apply L_no_greatest
  refine ⟨c.1, c.2, fun k hk => ?_, fun ψ hψ hlow => ?_⟩
  · have : principal (Quotient.mk _ c) ≤ principal (cl (gap k) (gap_atomFree k)) := by
      rw [← h]
      exact sInf_le ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    exact mk_le_iff.mp (principal_le_principal.mp this)
  · have : principal (cl ψ hψ) ≤ gapCut := by
      apply le_sInf
      rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      exact principal_le_principal.mpr (mk_le_iff.mpr (hlow k hk))
    rw [h] at this
    exact mk_le_iff.mp (principal_le_principal.mp this)

/-- **(D)** F* has a point that is not principal. -/
theorem exists_nonprincipal : ∃ x : DedekindCut RNClass, ∀ a, x ≠ principal a :=
  ⟨gapCut, gapCut_ne_principal⟩

/-! ## (C) |F*| = 2^ℵ₀ -/

/-- Variable-free formulas as a syntax of their own, countable by Mathlib's
deriving handler. -/
inductive CF where
  | bot
  | and (a b : CF)
  | or (a b : CF)
  | imp (a b : CF)
  | box (a : CF)
  deriving Countable

/-- The formula of `c`. -/
def CF.toF : CF → PLLFormula
  | .bot => .falsePLL
  | .and a b => .and a.toF b.toF
  | .or a b => .or a.toF b.toF
  | .imp a b => .ifThen a.toF b.toF
  | .box a => .somehow a.toF

theorem CF.toF_atomFree : ∀ c : CF, atomFree c.toF = true
  | .bot => rfl
  | .and a b | .or a b | .imp a b => by
      simp [CF.toF, atomFree, CF.toF_atomFree a, CF.toF_atomFree b]
  | .box a => by simp [CF.toF, atomFree, CF.toF_atomFree a]

/-- Every variable-free formula is `toF` of some `c`. -/
theorem CF.onto : ∀ φ : PLLFormula, atomFree φ = true → ∃ c : CF, c.toF = φ
  | .prop _, h => by simp [atomFree] at h
  | .falsePLL, _ => ⟨.bot, rfl⟩
  | .and a b, h => by
      simp only [atomFree, Bool.and_eq_true] at h
      obtain ⟨ca, rfl⟩ := CF.onto a h.1
      obtain ⟨cb, rfl⟩ := CF.onto b h.2
      exact ⟨.and ca cb, rfl⟩
  | .or a b, h => by
      simp only [atomFree, Bool.and_eq_true] at h
      obtain ⟨ca, rfl⟩ := CF.onto a h.1
      obtain ⟨cb, rfl⟩ := CF.onto b h.2
      exact ⟨.or ca cb, rfl⟩
  | .ifThen a b, h => by
      simp only [atomFree, Bool.and_eq_true] at h
      obtain ⟨ca, rfl⟩ := CF.onto a h.1
      obtain ⟨cb, rfl⟩ := CF.onto b h.2
      exact ⟨.imp ca cb, rfl⟩
  | .somehow a, h => by
      obtain ⟨ca, rfl⟩ := CF.onto a h
      exact ⟨.box ca, rfl⟩

/-- **F0 is countable.** -/
instance : Countable RNClass := by
  have hs : Function.Surjective (fun c : CF => cl c.toF c.toF_atomFree) := by
    intro x
    obtain ⟨d, rfl⟩ := Quotient.exists_rep x
    obtain ⟨c, hc⟩ := CF.onto d.1 d.2
    exact ⟨c, congrArg (Quotient.mk _) (Subtype.ext hc)⟩
  exact hs.countable

/-- `f'(q)` (`ratFormulaCF`, `wip/f0Minkowski.lean`) in F0. -/
def fq (q : ℚ) : RNClass := cl (ratFormulaCF q) (rat_vf_cf q)

theorem fq_lt {q q' : ℚ} (h : q < q') : fq q < fq q' :=
  lt_of_le_not_ge (mk_le_iff.mpr (rat_embedding_cf h).1)
    (fun h' => (rat_embedding_cf h).2 (mk_le_iff.mp h'))

/-- `X_r = ⋁ { ↓f'(q) : q < r }`. -/
noncomputable def X (r : ℝ) : DedekindCut RNClass :=
  sSup (principal '' (fq '' {q : ℚ | (q : ℝ) < r}))

theorem X_lt {r r' : ℝ} (hlt : r < r') : X r ≠ X r' := by
  obtain ⟨q₁, h1, h1'⟩ := exists_rat_btwn hlt
  obtain ⟨q₂, h2, h2'⟩ := exists_rat_btwn h1'
  intro h
  have hup : X r ≤ principal (fq q₁) := by
    apply sSup_le
    rintro _ ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    have hq' : (q : ℝ) < q₁ := lt_trans hq h1
    exact principal_le_principal.mpr (fq_lt (by exact_mod_cast hq')).le
  have hlow : principal (fq q₂) ≤ X r' := le_sSup ⟨_, ⟨q₂, h2', rfl⟩, rfl⟩
  rw [h] at hup
  have h12 : q₁ < q₂ := by exact_mod_cast h2
  exact absurd (principal_le_principal.mp (hlow.trans hup)) (not_le_of_gt (fq_lt h12))

/-- `r ↦ X_r` is one-to-one. -/
theorem X_injective : Function.Injective X := by
  intro r r' h
  rcases lt_trichotomy r r' with hlt | heq | hgt
  · exact absurd h (X_lt hlt)
  · exact heq
  · exact absurd h.symm (X_lt hgt)

/-- **(C)** `|F*| = 2^ℵ₀`. -/
theorem card_eq_continuum : Cardinal.mk (DedekindCut RNClass) = Cardinal.continuum := by
  apply le_antisymm
  · calc Cardinal.mk (DedekindCut RNClass) ≤ Cardinal.mk (Set RNClass) :=
          Cardinal.mk_le_of_injective Concept.extent_injective
      _ = 2 ^ Cardinal.mk RNClass := Cardinal.mk_set
      _ ≤ 2 ^ Cardinal.aleph0 := Cardinal.power_le_power_left two_ne_zero Cardinal.mk_le_aleph0
      _ = Cardinal.continuum := Cardinal.two_power_aleph0
  · rw [← Cardinal.mk_real]
    exact Cardinal.mk_le_of_injective X_injective

end Points
end F0
end PLLND

/-! ## Pins (each watched failing at `[propext, Quot.sound]`) -/

#axioms_within PLLND.F0.Points.gapCut_ne_principal [propext, Classical.choice, Quot.sound]
#axioms_within PLLND.F0.Points.exists_nonprincipal [propext, Classical.choice, Quot.sound]
#axioms_within PLLND.F0.Points.X_injective [propext, Classical.choice, Quot.sound]
#axioms_within PLLND.F0.Points.card_eq_continuum [propext, Classical.choice, Quot.sound]
