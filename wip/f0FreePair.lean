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

/-! ## Stage 1: the designed cells (refutation stage, CLAUDE.md rules 7 and 9)

The four sign patterns passed in `wip/f0FreeHAn.lean`.  The next structural
risks: `x₁`, a relative double negation over `t3`, might be `¬¬`-stable
relative to `σ²⊥` (C1, C2), or the pair might be linearly ordered (C3); C4
is the cheap check on `x₀ = σ(◯t3)`.  With `¬A = A → ⊥`, `p = pvar 0`,
`q = pvar 1`:

    C1 = ¬¬q → q,   C2 = ¬q ∨ ¬¬q,   C3 = (p → q) ∨ (q → p),   C4 = ¬¬p → p.

None is a theorem of IPC (`ipc_C1` … `ipc_C4`, two- and three-world Kripke
models).  For freeness each image `relB σ²⊥ xs Cᵢ` must be no theorem of PLL.
Certificates: the subframe tableau (`refbench fact`, untrusted producer)
returned countermodels of 37, 37, 30, 19 worlds, minimised to 10, 14, 12, 8;
the kernel checks them (`SubTab.no`, `decide +kernel`) against the images as
computed here by `relB`.  All four cells PASS. -/

/-- `p = pvar 0`. -/
def pP : PLLFormula := .prop (pvar 0)

/-- `q = pvar 1`. -/
def qP : PLLFormula := .prop (pvar 1)

/-- `¬A = A → ⊥`. -/
def negF (A : PLLFormula) : PLLFormula := A.ifThen .falsePLL

/-- C1 = `¬¬q → q`. -/
def C1 : PLLFormula := (negF (negF qP)).ifThen qP

/-- C2 = `¬q ∨ ¬¬q`. -/
def C2 : PLLFormula := (negF qP).or (negF (negF qP))

/-- C3 = `(p → q) ∨ (q → p)`. -/
def C3 : PLLFormula := (pP.ifThen qP).or (qP.ifThen pP)

/-- C4 = `¬¬p → p`. -/
def C4 : PLLFormula := (negF (negF pP)).ifThen pP

set_option maxRecDepth 100000

/-- IPC: `⊬ ¬¬q → q` (two worlds, `q` at the top). -/
theorem ipc_C1 : ¬ Deriv [] C1 :=
  SubTab.no.verdict C1
    { n := 2, root := 0, le := [[true, true], [false, true]], S := [false, false],
      val := [[], ["pp"]] }

/-- IPC: `⊬ ¬q ∨ ¬¬q` (a fork, `q` at one top). -/
theorem ipc_C2 : ¬ Deriv [] C2 :=
  SubTab.no.verdict C2
    { n := 3, root := 0, le := [[true, true, true], [false, true, false], [false, false, true]],
      S := [false, false, false], val := [[], ["pp"], []] }

/-- IPC: `⊬ (p → q) ∨ (q → p)` (a fork, `p` at one top, `q` at the other). -/
theorem ipc_C3 : ¬ Deriv [] C3 :=
  SubTab.no.verdict C3
    { n := 3, root := 0, le := [[true, true, true], [false, true, false], [false, false, true]],
      S := [false, false, false], val := [[], ["p"], ["pp"]] }

/-- IPC: `⊬ ¬¬p → p`. -/
theorem ipc_C4 : ¬ Deriv [] C4 :=
  SubTab.no.verdict C4
    { n := 2, root := 0, le := [[true, true], [false, true]], S := [false, false],
      val := [[], ["p"]] }

/-- **Cell C1 PASSES**: `⊬ ((x₁ ↠ σ²⊥) ↠ σ²⊥) ↠ x₁`; `x₁` is not `¬¬`-stable
relative to `σ²⊥` (tableau countermodel, minimised to 10 worlds). -/
theorem cell_C1 : ¬ Deriv [] (relB b2 xs C1) :=
  SubTab.no.verdict (relB b2 xs C1)
    { n := 10, root := 0, le := [[true, true, true, true, true, true, true, true, true, true], [false, true, true, true, false, false, false, false, false, false], [false, false, true, false, false, false, false, false, false, false], [false, false, false, true, false, false, false, false, false, false], [false, false, false, false, true, true, true, true, true, true], [false, false, false, false, false, true, true, false, false, false], [false, false, false, false, false, false, true, false, false, false], [false, false, false, false, false, false, false, true, true, true], [false, false, false, false, false, false, false, false, true, false], [false, false, false, false, false, false, false, false, false, true]], S := [false, true, true, false, false, true, false, false, true, false], val := [[], [], [], [], [], [], [], [], [], []] }

/-- **Cell C2 PASSES**: `⊬ (x₁ ↠ σ²⊥) ∨ ((x₁ ↠ σ²⊥) ↠ σ²⊥)` (14 worlds). -/
theorem cell_C2 : ¬ Deriv [] (relB b2 xs C2) :=
  SubTab.no.verdict (relB b2 xs C2)
    { n := 14, root := 0, le := [[true, true, true, true, true, true, true, true, true, true, true, true, true, true], [false, true, true, true, true, true, true, false, false, false, false, false, false, false], [false, false, true, true, false, false, false, false, false, false, false, false, false, false], [false, false, false, true, false, false, false, false, false, false, false, false, false, false], [false, false, false, false, true, true, true, false, false, false, false, false, false, false], [false, false, false, false, false, true, false, false, false, false, false, false, false, false], [false, false, false, false, false, false, true, false, false, false, false, false, false, false], [false, false, false, false, false, false, false, true, true, true, true, true, true, true], [false, false, false, false, false, false, false, false, true, true, true, false, false, false], [false, false, false, false, false, false, false, false, false, true, false, false, false, false], [false, false, false, false, false, false, false, false, false, false, true, false, false, false], [false, false, false, false, false, false, false, false, false, false, false, true, true, true], [false, false, false, false, false, false, false, false, false, false, false, false, true, false], [false, false, false, false, false, false, false, false, false, false, false, false, false, true]], S := [false, false, true, false, false, true, false, false, false, true, false, true, true, false], val := [[], [], [], [], [], [], [], [], [], [], [], [], [], []] }

/-- **Cell C3 PASSES**: `⊬ (x₀ ↠ x₁) ∨ (x₁ ↠ x₀)`; the pair is not linearly
ordered (12 worlds). -/
theorem cell_C3 : ¬ Deriv [] (relB b2 xs C3) :=
  SubTab.no.verdict (relB b2 xs C3)
    { n := 12, root := 0, le := [[true, true, true, true, true, true, true, true, true, true, true, true], [false, true, true, true, true, true, true, true, false, false, false, false], [false, false, true, true, true, false, false, false, false, false, false, false], [false, false, false, true, false, false, false, false, false, false, false, false], [false, false, false, false, true, false, false, false, false, false, false, false], [false, false, false, false, false, true, true, true, false, false, false, false], [false, false, false, false, false, false, true, false, false, false, false, false], [false, false, false, false, false, false, false, true, false, false, false, false], [false, false, false, false, false, false, false, false, true, true, true, true], [false, false, false, false, false, false, false, false, false, true, true, true], [false, false, false, false, false, false, false, false, false, false, true, false], [false, false, false, false, false, false, false, false, false, false, false, true]], S := [false, false, false, true, false, true, true, false, true, false, true, false], val := [[], [], [], [], [], [], [], [], [], [], [], []] }

/-- **Cell C4 PASSES**: `⊬ ((x₀ ↠ σ²⊥) ↠ σ²⊥) ↠ x₀` (8 worlds). -/
theorem cell_C4 : ¬ Deriv [] (relB b2 xs C4) :=
  SubTab.no.verdict (relB b2 xs C4)
    { n := 8, root := 0, le := [[true, true, true, true, true, true, true, true], [false, true, true, true, true, true, true, true], [false, false, true, true, true, true, true, true], [false, false, false, true, true, false, false, false], [false, false, false, false, true, false, false, false], [false, false, false, false, false, true, true, true], [false, false, false, false, false, false, true, false], [false, false, false, false, false, false, false, true]], S := [false, true, false, true, false, false, true, false], val := [[], [], [], [], [], [], [], []] }

end Pair
end F0
end PLLND

/-! ## Axiom pins -/

#axioms_within PLLND.F0.Pair.xs_vf [propext, Quot.sound]
#axioms_within PLLND.F0.Pair.b2_le_xs [propext, Quot.sound]
#axioms_within PLLND.F0.Pair.freeHAn_of_freePair [propext, Quot.sound]
#axioms_within PLLND.F0.Pair.ipc_C1 [propext, Quot.sound]
#axioms_within PLLND.F0.Pair.ipc_C2 [propext, Quot.sound]
#axioms_within PLLND.F0.Pair.ipc_C3 [propext, Quot.sound]
#axioms_within PLLND.F0.Pair.ipc_C4 [propext, Quot.sound]
#axioms_within PLLND.F0.Pair.cell_C1 [propext, Quot.sound]
#axioms_within PLLND.F0.Pair.cell_C2 [propext, Quot.sound]
#axioms_within PLLND.F0.Pair.cell_C3 [propext, Quot.sound]
#axioms_within PLLND.F0.Pair.cell_C4 [propext, Quot.sound]
