import wip.f0FreeHAn
import Meta.Audit

/-!
# Is `(x₀, x₁)` a free pair of generators of a Heyting subalgebra of `[σ²⊥, ⊤]`?

Follow-up to `wip/f0FreeHAn.lean` (Matthew, 2026-10-27).  There the candidate
pair

    x₀ = ◯σ²⊥ = σ²(◯⊥),     x₁ = σ²⊥ ∨ ((◯Y ↠ t3) ↠ t3),     Y = t4 ∨ ¬t4,

passed the necessary condition that all four sign patterns are realised over
`σ²⊥` (`twoGenPatterns_x0_x1`).  The question here is whether the pair freely
generates a copy of the free Heyting algebra `H₂` on two generators inside the
interval `[σ²⊥, ⊤]` of F0, with F0's own `∧`, `∨`, `↠` and bottom `σ²⊥`.

## The statement (committed before any proof, METHOD.md §1)

The generator assignment `xs` sends `pvar 0 = p` to `x₀`, `pvar 1 = pp` to `x₁`,
and every other variable to `x₀` (irrelevant: the formulas below have
`varsBelow 2`).  With `b = σ²⊥ = base 2` and `relB b xs A = A[a := xs a, ⊥ := b]`:

    FreePair :  ∀ A B ◯-free with varsBelow 2,
                  [A] ⊢ B  ⟺  [relB σ²⊥ xs A] ⊢ relB σ²⊥ xs B.

The direction `⟹` is substitution (every `relB`-image is `≥ σ²⊥`); the content
is `⟸` (faithfulness).  Corollary: `FreePair → FreeHAnAbove (base 2) 2`
(`freeHAn_of_freePair`).

Fragment first (CLAUDE.md rule 8): the ◯-free variable-free fragment of PLL is
`{⊥, ⊤}`, in which there is no interval to carry generators; the IPC instance
of the question is the textbook fact that `H₂` is free on `p, q` (no content),
so the fragment-first stage is degenerate here and recorded as such.

Status note: `wip/f0FreePair-STATUS.md`.
-/

open PLLFormula

namespace PLLND
namespace F0
namespace Pair

open SemUI RNEmbed Sig FreeIPL FreeHAn
open PLLND.LaxInfinite (atomFree)

/-! ## The statement -/

/-- The base `b = σ²⊥ = ◯t3 ∨ (◯t3 ↠ t3)`. -/
abbrev b2 : PLLFormula := base 2

/-- **The generator assignment**: `pvar 1 ↦ x₁`, every other variable `↦ x₀`
(so `pvar 0 ↦ x₀`). -/
def xs (a : String) : PLLFormula := if a = pvar 1 then x1 else x0

theorem pvar0_ne_pvar1 : pvar 0 ≠ pvar 1 := by decide

theorem xs_p0 : xs (pvar 0) = x0 := if_neg pvar0_ne_pvar1

theorem xs_p1 : xs (pvar 1) = x1 := if_pos rfl

/-- **FreePair**: the relativisation `A ↦ A[p := x₀, pp := x₁, ⊥ := σ²⊥]` is
faithful on the ◯-free formulas in the two variables `p`, `pp`:

    ∀ A B ◯-free with varsBelow 2,  [A] ⊢ B  ⟺  [relB σ²⊥ xs A] ⊢ relB σ²⊥ xs B. -/
def FreePair : Prop :=
  ∀ A B : PLLFormula, boxFree A = true → boxFree B = true →
    varsBelow 2 A = true → varsBelow 2 B = true →
    (Deriv [A] B ↔ Deriv [relB b2 xs A] (relB b2 xs B))

theorem x0_vf : atomFree x0 = true := rfl

theorem x1_vf : atomFree x1 = true := rfl

theorem xs_vf (a : String) : atomFree (xs a) = true := by
  unfold xs
  split
  · exact x1_vf
  · exact x0_vf

theorem b2_le_x0 : Deriv [b2] x0 :=
  (Deriv.iden (.head _) : Deriv [b2] b2).elim fun d => ⟨.laxIntro d⟩

theorem b2_le_x1 : Deriv [b2] x1 := Deriv.orIntro1 (Deriv.iden (.head _))

theorem b2_le_xs (a : String) : Deriv [b2] (xs a) := by
  unfold xs
  split
  · exact b2_le_x1
  · exact b2_le_x0

/-- **The corollary**: `FreePair` gives a copy of `H₂` in `[σ²⊥, ⊤]`. -/
theorem freeHAn_of_freePair (h : FreePair) : FreeHAnAbove (base 2) 2 :=
  ⟨xs, xs_vf, b2_le_xs, h⟩

end Pair
end F0
end PLLND

/-! ## Axiom pins -/

#axioms_within PLLND.F0.Pair.xs_vf [propext, Quot.sound]
#axioms_within PLLND.F0.Pair.b2_le_xs [propext, Quot.sound]
#axioms_within PLLND.F0.Pair.freeHAn_of_freePair [propext, Quot.sound]
