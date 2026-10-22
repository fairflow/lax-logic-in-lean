import wip.f0Dyadic
import Mathlib.Order.CountableDenseLinearOrder
import Meta.Audit

/-!
# ℚ embeds in F0 (corollary)

    ∃ f : ℚ → variable-free PLL formulas,   q < q'  ⟹  f q ⊢ f q'  ∧  f q' ⊬ f q

(`rat_embedding`, `rat_vf`).  The dyadic rationals strictly between `0` and `1`
(`DyQ`) form a countable dense linear order without endpoints, so Cantor's
theorem (`Order.iso_of_countable_dense`) gives an order isomorphism
`ℚ ≃o DyQ`; composing with the dyadic embedding of `wip/f0Dyadic.lean`
(`dyadic_embedding`, pinned `[propext, Quot.sound]`) gives the map.

**Axioms.**  This corollary carries `Classical.choice` (Cantor's theorem is used
through `Classical.choice`, and a representation `m / 2^n` of each dyadic is
chosen); its pins say so.  The main theorem `dyadic_embedding` does not.
-/

open PLLFormula

namespace PLLND
namespace F0

open SemUI RNEmbed
open PLLND.LaxInfinite (atomFree)

/-- `q` is a dyadic rational. -/
abbrev IsDyadic (q : ℚ) : Prop := ∃ n m : ℕ, q = (m : ℚ) / 2 ^ n

/-- The dyadic rationals strictly between `0` and `1`. -/
abbrev DyQ : Type := {q : ℚ // 0 < q ∧ q < 1 ∧ IsDyadic q}

theorem two_pow_pos_q (n : ℕ) : (0 : ℚ) < 2 ^ n := by positivity

instance : DenselyOrdered DyQ where
  dense a b hab := by
    obtain ⟨ha0, ha1, n, m, hm⟩ := a.2
    obtain ⟨hb0, hb1, n', m', hm'⟩ := b.2
    have hab' : a.1 < b.1 := hab
    refine ⟨⟨(a.1 + b.1) / 2, by linarith, by linarith, n + n' + 1,
      m * 2 ^ n' + m' * 2 ^ n, ?_⟩, ?_, ?_⟩
    · rw [hm, hm']
      push_cast
      field_simp
      ring
    · show a.1 < (a.1 + b.1) / 2
      linarith
    · show (a.1 + b.1) / 2 < b.1
      linarith

instance : NoMinOrder DyQ where
  exists_lt a := by
    obtain ⟨ha0, ha1, n, m, hm⟩ := a.2
    refine ⟨⟨a.1 / 2, by linarith, by linarith, n + 1, m, ?_⟩, ?_⟩
    · rw [hm, pow_succ, div_div]
    · show a.1 / 2 < a.1
      linarith

instance : NoMaxOrder DyQ where
  exists_gt a := by
    obtain ⟨ha0, ha1, n, m, hm⟩ := a.2
    refine ⟨⟨(a.1 + 1) / 2, by linarith, by linarith, n + 1, m + 2 ^ n, ?_⟩, ?_⟩
    · rw [hm]
      push_cast
      field_simp
      ring
    · show a.1 < (a.1 + 1) / 2
      linarith

instance : Nonempty DyQ := ⟨⟨1 / 2, by norm_num, by norm_num, 1, 1, by norm_num⟩⟩

/-- Cantor: `ℚ ≃o DyQ`. -/
noncomputable def ratIso : ℚ ≃o DyQ :=
  Classical.choice (Order.iso_of_countable_dense ℚ DyQ)

/-- Every element of `DyQ` is `m / 2^n` with `m ≤ 2^n`, i.e. a `Dy`. -/
theorem dy_rep (x : DyQ) : ∃ d : Dy, (x.1 : ℚ) = (d.num : ℚ) / 2 ^ d.exp := by
  obtain ⟨_, hx1, n, m, hm⟩ := x.2
  have hlt : m < 2 ^ n := by
    have h : (m : ℚ) / 2 ^ n < 1 := by rw [← hm]; exact hx1
    rw [div_lt_one (two_pow_pos_q n)] at h
    exact_mod_cast h
  exact ⟨⟨m, n, Nat.le_of_lt hlt⟩, hm⟩

/-- A chosen representation. -/
noncomputable def toDy (x : DyQ) : Dy := Classical.choose (dy_rep x)

theorem toDy_spec (x : DyQ) :
    (x.1 : ℚ) = ((toDy x).num : ℚ) / 2 ^ (toDy x).exp :=
  Classical.choose_spec (dy_rep x)

theorem toDy_lt {x y : DyQ} (h : x < y) : (toDy x).lt (toDy y) := by
  have h' : (x.1 : ℚ) < y.1 := h
  rw [toDy_spec x, toDy_spec y, div_lt_div_iff₀ (two_pow_pos_q _) (two_pow_pos_q _)] at h'
  show (toDy x).num * 2 ^ (toDy y).exp < (toDy y).num * 2 ^ (toDy x).exp
  exact_mod_cast h'

/-- The formula of a rational: through Cantor's isomorphism onto the dyadics
in `(0, 1)`, then `f`. -/
noncomputable def ratFormula (q : ℚ) : PLLFormula := (toDy (ratIso q)).formula

/-- Every `ratFormula q` is variable-free. -/
theorem rat_vf (q : ℚ) : atomFree (ratFormula q) = true := dyadic_vf _

/-- **ℚ embeds in F0**:  `q < q'  ⟹  f q ⊢ f q'  ∧  f q' ⊬ f q`. -/
theorem rat_embedding {q q' : ℚ} (h : q < q') :
    Deriv [ratFormula q] (ratFormula q') ∧ ([ratFormula q'] ⊬ ratFormula q) :=
  dyadic_embedding _ _ (toDy_lt (ratIso.lt_iff_lt.mpr h))

end F0
end PLLND

#axioms_within PLLND.F0.rat_vf [propext, Classical.choice, Quot.sound]
#axioms_within PLLND.F0.rat_embedding [propext, Classical.choice, Quot.sound]
