import wip.f0FreeIPL
import Meta.Audit

/-!
# Free Heyting algebras on `n` generators inside the filters `[σᵐ⊥, ⊤]` of F0

Follow-up to `wip/f0FreeIPL.lean` (Matthew, 2026-10-27).  There, `[t3, ⊤]` was
shown to contain no copy of the free Heyting algebra on two generators closed
under F0's own `∧`, `∨`, `↠` with bottom `t3` (`not_FreeIPLInAboveT3`), by a
count: a world maximal among those refuting `t3` has one of only three
variable-free theories, while two free generators need all four sign patterns.

This module states the same question for the bases `σᵐ⊥` (`sigN m ⊥`;
`σ⁰⊥ = ⊥`, `σ¹⊥ = t3`, `σ²⊥ = σ(t3) = ◯t3 ∨ (◯t3 ↠ t3)`) and `n` generators,
and makes the counting criterion precise.

## Statements (committed before any proof, METHOD.md §1)

* `relB b x A = A[a := x a, ⊥ := b]`, the relativisation to the base `b`.
* `FreeHAnAbove b n`: generators `x₀, …, x_{n-1} ≥ b` such that for all ◯-free
  `A`, `B` in the variables `p0, …, p(n-1)`,

      [A] ⊢ B  ⟺  [A[pᵢ := xᵢ, ⊥ := b]] ⊢ B[pᵢ := xᵢ, ⊥ := b].

  `FreeHAωAbove b` is the same with all variables (ℵ₀ generators);
  `FreeIPLInAboveT3` of `wip/f0FreeIPL.lean` is `FreeHAωAbove t3`.
* `BMax b M w`: `w` refutes `b` and no proper successor does.
* `TypeBound b K` (k(b) ≤ K): a function `ty` assigning to every world of every
  finite subframe model one of `K` Boolean valuations `Ts`, such that every
  `b`-maximal world forces exactly the variable-free formulas its valuation
  makes true.  `Distinct b K` (k(b) ≥ K): `K` `b`-maximal worlds, in finite
  subframe models, with pairwise different variable-free theories.
* `Conjecture`: `∀ n ∃ m, FreeHAnAbove (σᵐ⊥) n`.
* `Companion`: for every variable-free `b < ⊤`, `k(b)` is finite
  (`TypesFinite b := ∃ K, TypeBound b K`), so no single `[b, ⊤]` holds free IPL
  on ℵ₀ generators.
* `CountingCriterion`: `FreeHAnAbove b n → TypeBound b K → 2ⁿ ≤ K`.
* `TwoGenPatterns b x₀ x₁`: no signed conjunction of `x₀`, `x₁` lies below `b`,

      ∀ ε,  ⊬ (x₀^ε₁ ∧ x₁^ε₂) ↠ b,     x^true = x, x^false = x ↠ b,

  the two-generator sign-pattern condition (necessary for `FreeHAnAbove b 2`
  with these generators).  The candidate pair high up, in `[σ²⊥, ⊤]`:

      x₀ = ◯σ²⊥ = σ²(◯⊥),     x₁ = σ²⊥ ∨ ((◯Y ↠ t3) ↠ t3),   Y = t4 ∨ ¬t4,

  where `◯Y ↠ t3` is the relative negation of `◯Y` in `[t3, ⊤]`.

Status note: `wip/f0FreeHAn-STATUS.md`.
-/

open PLLFormula

namespace PLLND
namespace F0
namespace FreeHAn

open SemUI RNEmbed Sig FreeIPL
open PLLND.LaxInfinite (atomFree)
open SubframeModel.CF

/-! ## The relativisation to a base and the `n`-generator statement -/

/-- **The relativisation to the base `b`**, `A[a := x a, ⊥ := b]`. -/
def relB (b : PLLFormula) (x : String → PLLFormula) : PLLFormula → PLLFormula
  | .prop a => x a
  | .falsePLL => b
  | .and A B => .and (relB b x A) (relB b x B)
  | .or A B => .or (relB b x A) (relB b x B)
  | .ifThen A B => .ifThen (relB b x A) (relB b x B)
  | .somehow A => .somehow (relB b x A)

/-- The `i`-th propositional variable, `"p0"`, `"p1"`, …. -/
def pvar (i : Nat) : String := "p" ++ toString i

/-- Every atom of the formula is among `p0, …, p(n-1)`. -/
def varsBelow (n : Nat) : PLLFormula → Bool
  | .prop a => (List.range n).any fun i => decide (a = pvar i)
  | .falsePLL => true
  | .and A B => varsBelow n A && varsBelow n B
  | .or A B => varsBelow n A && varsBelow n B
  | .ifThen A B => varsBelow n A && varsBelow n B
  | .somehow A => varsBelow n A

/-- **`[b, ⊤]` contains the free Heyting algebra on `n` generators** as a
Heyting subalgebra (F0's `∧`, `∨`, `↠`, bottom `b`):

    ∃ x, (∀ a, atomFree (x a)) ∧ (∀ a, [b] ⊢ x a) ∧
      ∀ A B ◯-free in p0 … p(n-1),  [A] ⊢ B  ⟺  [relB b x A] ⊢ relB b x B. -/
def FreeHAnAbove (b : PLLFormula) (n : Nat) : Prop :=
  ∃ x : String → PLLFormula,
    (∀ a, atomFree (x a) = true) ∧ (∀ a, Deriv [b] (x a)) ∧
    ∀ A B : PLLFormula, boxFree A = true → boxFree B = true →
      varsBelow n A = true → varsBelow n B = true →
      (Deriv [A] B ↔ Deriv [relB b x A] (relB b x B))

/-- **`[b, ⊤]` contains the free Heyting algebra on ℵ₀ generators** (every
variable a generator); `FreeIPLInAboveT3 = FreeHAωAbove t3`. -/
def FreeHAωAbove (b : PLLFormula) : Prop :=
  ∃ x : String → PLLFormula,
    (∀ a, atomFree (x a) = true) ∧ (∀ a, Deriv [b] (x a)) ∧
    ∀ A B : PLLFormula, boxFree A = true → boxFree B = true →
      (Deriv [A] B ↔ Deriv [relB b x A] (relB b x B))

/-- The bases `σᵐ⊥`: `base 0 = ⊥`, `base 1 = t3`, `base 2 = σ(t3) = ◯t3 ∨ (◯t3 ↠ t3)`. -/
def base (m : Nat) : PLLFormula := sigN m .falsePLL

theorem base_zero : base 0 = .falsePLL := rfl
theorem base_one : base 1 = t3 := rfl
theorem base_two : base 2 = (chainF 1).or (gap 1) := rfl

/-- **The conjecture**: every free Heyting algebra on finitely many generators
occurs in some `[σᵐ⊥, ⊤]`. -/
def Conjecture : Prop := ∀ n, ∃ m, FreeHAnAbove (base m) n

/-! ## Types of `b`-maximal worlds -/

section Types

variable (b : PLLFormula) (M : SubframeModel)

/-- A world refuting `b` with no proper successor refuting `b`
(`FreeIPL.RMax` is `BMax t3`). -/
def BMax (w : M.W) : Prop := ¬ M.force w b ∧ ∀ v, M.le w v → ¬ M.force v b → M.le v w

/-- The world `w` has the type `T`: it forces exactly the variable-free
formulas `T` makes true. -/
def HasType (w : M.W) (T : PLLFormula → Bool) : Prop :=
  ∀ φ : PLLFormula, atomFree φ = true → (M.force w φ ↔ T φ = true)

end Types

/-- **`k(b) ≤ K`**: `K` valuations `Ts` and a type function `ty` on the worlds
of the finite subframe models, such that every `b`-maximal world has the type
`Ts (ty w)`. -/
def TypeBound (b : PLLFormula) (K : Nat) : Prop :=
  ∃ (Ts : Fin K → PLLFormula → Bool) (ty : ∀ (M : SubframeModel) [FinDec M], M.W → Fin K),
    ∀ (M : SubframeModel) [FinDec M] (w : M.W), BMax b M w → HasType M w (Ts (ty M w))

/-- A cell: a finite subframe model with a `b`-maximal world. -/
structure Cell (b : PLLFormula) where
  M : SubframeModel
  fin : FinDec M
  w : M.W
  max : BMax b M w

/-- Two cells have different theories: some variable-free formula holds at one
and fails at the other. -/
def Cell.Separated {b : PLLFormula} (c c' : Cell b) : Prop :=
  ∃ φ : PLLFormula, atomFree φ = true ∧ ¬ (c.M.force c.w φ ↔ c'.M.force c'.w φ)

/-- **`k(b) ≥ K`**: `K` `b`-maximal worlds with pairwise different
variable-free theories. -/
def Distinct (b : PLLFormula) (K : Nat) : Prop :=
  ∃ cs : Fin K → Cell b, ∀ i j, i ≠ j → (cs i).Separated (cs j)

/-- `k(b)` is finite. -/
def TypesFinite (b : PLLFormula) : Prop := ∃ K, TypeBound b K

/-- **The companion**: for every variable-free `b < ⊤` the type count is finite. -/
def Companion : Prop := ∀ b : PLLFormula, atomFree b = true → ¬ Deriv [] b → TypesFinite b

/-- **The counting criterion**: a copy of free IPL on `n` generators in `[b, ⊤]`
needs at least `2ⁿ` types of `b`-maximal world. -/
def CountingCriterion : Prop :=
  ∀ (b : PLLFormula) (n K : Nat), atomFree b = true → FreeHAnAbove b n → TypeBound b K → 2 ^ n ≤ K

/-- The same, in the form the proof gives: the `2ⁿ` sign patterns are realised
by pairwise separated `b`-maximal cells. -/
def PatternsRealised (b : PLLFormula) (n : Nat) : Prop :=
  ∃ cs : (Fin n → Bool) → Cell b, ∀ ε ε', ε ≠ ε' → (cs ε).Separated (cs ε')

/-! ## The two-generator sign-pattern condition, and the candidate pair -/

/-- The relative negation in `[b, ⊤]`, `x ↦ x ↠ b`. -/
def RnegB (b φ : PLLFormula) : PLLFormula := .ifThen φ b

/-- `x` or `x ↠ b`, by a sign. -/
def sgnB (b : PLLFormula) : Bool → PLLFormula → PLLFormula
  | true, x => x
  | false, x => RnegB b x

/-- **The sign-pattern condition for a pair** over the base `b`:

    ∀ ε : Bool × Bool,  ⊬ (x₀^ε₁ ∧ x₁^ε₂) ↠ b.

Necessary for `x₀`, `x₁` to be free generators over `b`
(`FreeIPL.TwoGenFaithful` is the case `b = t3`). -/
def TwoGenPatterns (b x₀ x₁ : PLLFormula) : Prop :=
  ∀ ε : Bool × Bool, ¬ Deriv [] (RnegB b ((sgnB b ε.1 x₀).and (sgnB b ε.2 x₁)))

/-- `Y = t4 ∨ ¬t4`, `t4 = ¬¬◯⊥`: fails exactly at the worlds that see both a
world forcing `◯⊥` and one forcing `¬◯⊥`. -/
def Yf : PLLFormula := t4.or (t4.ifThen .falsePLL)

/-- `x = ◯Y`, the generator of a Rieger–Nishimura ladder inside `[t3, g1]`. -/
def xf : PLLFormula := .somehow Yf

/-- The candidate pair in `[σ²⊥, ⊤]`: `x₀ = ◯σ²⊥ = σ²(◯⊥)`. -/
def x0 : PLLFormula := .somehow (base 2)

/-- `x₁ = σ²⊥ ∨ ((◯Y ↠ t3) ↠ t3)`. -/
def x1 : PLLFormula := (base 2).or ((xf.ifThen t3).ifThen t3)

theorem x0_eq : x0 = sigN 2 e := rfl

end FreeHAn
end F0
end PLLND
