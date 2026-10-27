import wip.f0SigOnto
import wip.f0Normal
import Meta.Audit

/-!
# Does `[t3, ⊤]` contain the free Heyting algebra on countably many generators?

F0 is the Lindenbaum algebra of the variable-free PLL formulas; `t3 = ◯⊥ ∨ ¬◯⊥`,
and `[t3, ⊤]` is a Heyting algebra with bottom `t3`, the `∧`, `∨`, `↠` of F0 and
the relative negation `x ↦ x ↠ t3` (`[t3, ⊤]` is closed under them since
`b ≤ a ↠ b`).

## The statement (Matthew, 2026-10-27)

For a generator assignment `x : String → PLLFormula` (the propositional
variables are the strings; `x a` is the variable-free formula substituted for
the variable `a`), the relativisation is

    h A := A[a := x a, ⊥ := t3]                       (`relG x`)

and the statement is

    FreeIPLInAboveT3 :=
      ∃ x, (∀ a, atomFree (x a)) ∧ (∀ a, t3 ≤ x a) ∧
        ∀ A B ◯-free,  [A] ⊢ B  ⟺  [h A] ⊢ h B.

The left side is IPC derivability (`LaxND` on ◯-free formulas, by
conservativity).  The brief's candidate generators are the odd gaps
`oddGap i = g(2i+1)` (`gap`, `wip/gapWidth.lean`), independent in F0
(`indep`, `wip/f0Indep.lean`).

## Status

Statement committed first (METHOD.md §1).  Refutation stage and proofs follow
in this file; see `wip/f0FreeIPL-STATUS.md`.
-/

open PLLFormula

namespace PLLND
namespace F0
namespace FreeIPL

open SemUI RNEmbed Sig
open PLLND.LaxInfinite (atomFree)

/-! ## The relativisation and the statement -/

/-- **The relativisation** `h A = A[a := x a, ⊥ := t3]` for a generator
assignment `x`; homomorphic in the connectives (and in `◯`, which never occurs
in the ◯-free formulas the statement is about). -/
def relG (x : String → PLLFormula) : PLLFormula → PLLFormula
  | .prop a => x a
  | .falsePLL => t3
  | .and A B => .and (relG x A) (relG x B)
  | .or A B => .or (relG x A) (relG x B)
  | .ifThen A B => .ifThen (relG x A) (relG x B)
  | .somehow A => .somehow (relG x A)

/-- The relative negation in `[t3, ⊤]`: `x ↦ x ↠ t3`. -/
def Rneg (φ : PLLFormula) : PLLFormula := .ifThen φ t3

/-- **The statement**: `[t3, ⊤]` contains a copy of the free Heyting algebra on
the countably many generators `x a`, as the relativisation `h = relG x`:

    ∃ x, (∀ a, atomFree (x a)) ∧ (∀ a, [t3] ⊢ x a) ∧
      ∀ A B, boxFree A → boxFree B → ([A] ⊢ B ↔ [h A] ⊢ h B). -/
def FreeIPLInAboveT3 : Prop :=
  ∃ x : String → PLLFormula,
    (∀ a, atomFree (x a) = true) ∧ (∀ a, Deriv [t3] (x a)) ∧
    ∀ A B : PLLFormula, boxFree A = true → boxFree B = true →
      (Deriv [A] B ↔ Deriv [relG x A] (relG x B))

/-! ## The candidate generators -/

/-- The brief's candidate: the odd gaps `g(2i+1) = ◯t(4i+3) ↠ t(4i+3)`. -/
def oddGap (i : Nat) : PLLFormula := gap (2 * i + 1)

/-- A two-generator assignment: `p ↦ x₀`, `q ↦ x₁`, every other variable `↦ t3`. -/
def gen2 (x₀ x₁ : PLLFormula) (a : String) : PLLFormula :=
  if a = "p" then x₀ else if a = "q" then x₁ else t3

/-- The odd gaps as a generator assignment on the two variables `p`, `q`:
`p ↦ g1`, `q ↦ g3`. -/
def oddGapGen2 : String → PLLFormula := gen2 (oddGap 0) (oddGap 1)

/-! ## The two-generator question, and the one-generator one -/

/-- `x` or its relative negation `x ↠ t3`, by a sign. -/
def sgn (b : Bool) (x : PLLFormula) : PLLFormula := if b then x else Rneg x

/-- **The two-generator statement for a fixed pair**: no signed conjunction of
two variable-free `x₀`, `x₁` collapses to the relative bottom,

    ∀ ε : Bool × Bool,  ⊬ (x₀^ε₁ ∧ x₁^ε₂) ↠ t3,        x^true = x, x^false = x ↠ t3.

In the free Heyting algebra on `p, q` with bottom `⊥`, none of `¬(p ∧ q)`,
`¬(p ∧ ¬q)`, `¬(¬p ∧ q)`, `¬(¬p ∧ ¬q)` is a theorem; so this is a necessary
condition for `h` to be faithful on the two generators `x₀`, `x₁`. -/
def TwoGenFaithful (x₀ x₁ : PLLFormula) : Prop :=
  ∀ ε : Bool × Bool, ¬ Deriv [] (Rneg ((sgn ε.1 x₀).and (sgn ε.2 x₁)))

/-- The one-variable relativisation `p ↦ ◯t3 = σ(◯⊥)`, `⊥ ↦ t3`:
`h₁ A = σ (A[p := ◯⊥])`. -/
def h1 (A : PLLFormula) : PLLFormula := sig (embed A)

/-- Every atom of the formula is the distinguished variable `p`. -/
def onlyP : PLLFormula → Bool
  | .prop a => decide (a = pv)
  | .falsePLL => true
  | .and A B => onlyP A && onlyP B
  | .or A B => onlyP A && onlyP B
  | .ifThen A B => onlyP A && onlyP B
  | .somehow A => onlyP A

/-- **The one-generator statement**: `[t3, ⊤]` contains the free Heyting
algebra on one generator (the Rieger–Nishimura lattice), as `h₁`:

    [t3] ⊢ h₁ p  ∧  ∀ A B ◯-free over p,  [A] ⊢ B  ⟺  [h₁ A] ⊢ h₁ B. -/
def FreeIPL1InAboveT3 : Prop :=
  Deriv [t3] (h1 (.prop pv)) ∧
  ∀ A B : PLLFormula, boxFree A = true → boxFree B = true →
    onlyP A = true → onlyP B = true → (Deriv [A] B ↔ Deriv [h1 A] (h1 B))

end FreeIPL
end F0
end PLLND
