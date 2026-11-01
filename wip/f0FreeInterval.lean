import wip.f0FreeBase3
import Meta.Audit

/-!
# Nested relativisation of the free Heyting algebra inside F0: interval copies

Follow-up to `wip/f0FreeBase3.lean` (campaign approved by Matthew 2026-11-01).
There `freeHAωAbove_base3 : FreeHAωAbove (base 3)` gives a copy of the free
Heyting algebra `H_ω` inside `[σ³⊥, ⊤]`, by `relB σ³⊥ xω`.  Here the copy is
relativised again, to a sub-interval `[rel(ξ), rel(ζ)]`, and the construction
is stated for ANY faithful interval copy, so that it applies to its own output.

## The statements (committed before any proof, METHOD.md §1)

The interval translation for `[a, b]` with generators `x : String → PLLFormula`:

    rel a b x ⊥ = a,   rel a b x p = x p,   ∧, ∨ componentwise,
    rel a b x (A → B) = (rel A ↠ rel B) ∧ b,   rel a b x (◯A) = ◯(rel A) ∧ b

(the `◯` clause is used only by the PLL statement `NestPLL`).

    FreeIn a b x :  (∀ p, [a] ⊢ x p) ∧ (∀ p, [x p] ⊢ b) ∧
                      ∀ A B ◯-free,  [A] ⊢ B  ⟺  [rel a b x A] ⊢ rel a b x B
    FreeHAωIn a b : ∃ x, (∀ p, x p variable-free) ∧ FreeIn a b x

Fresh variables: `Fresh ρ ξ ζ` says that `ρ : String → String` is injective and
no `ρ p` occurs in `ξ` or `ζ`.  The core generators are

    coreGen ξ ζ ρ p = (ρ p ∨ ξ) ∧ ζ,     nestGen a b x ξ ζ ρ p = rel a b x (coreGen ξ ζ ρ p).

    CoreLemma :   ξ, ζ ◯-free,  [ξ] ⊢ ζ,  [ζ] ⊬ ξ,  Fresh ρ ξ ζ   ⟹   FreeIn ξ ζ (coreGen ξ ζ ρ)
    Nest :        FreeIn a b x,  ξ, ζ ◯-free,  [ξ] ⊢ ζ,  [ζ] ⊬ ξ,  Fresh ρ ξ ζ
                    ⟹   FreeIn (rel a b x ξ) (rel a b x ζ) (nestGen a b x ξ ζ ρ)
    MainTheorem : a, b, x variable-free,  FreeIn a b x,  ξ, ζ ◯-free,  [ξ] ⊢ ζ,  [ζ] ⊬ ξ
                    ⟹   FreeHAωIn (rel a b x ξ) (rel a b x ζ)
    Bridge :      (∀ p, [b] ⊢ x p) ∧ (∀ A B ◯-free, [A] ⊢ B ⟺ [relB b x A] ⊢ relB b x B)
                    ⟹   FreeIn b ⊤ x
    Bridge3 :     FreeIn σ³⊥ ⊤ xω
    NestTwo :     depth two inside the base-3 copy (level one by `nestGen`, level two
                    by `MainTheorem`)

OPEN, not in scope (CLAUDE.md rule 8, the PLL stage): `NestPLL`, the same as `Nest`
for all formulas, `◯` included, with the `◯` clause of `rel`.

Status note: `wip/f0FreeInterval-STATUS.md`.
-/

open PLLFormula

namespace PLLND
namespace F0
namespace Interval

open SemUI FreeHAn Base3
open PLLND.LaxInfinite (atomFree)
open SubframeModel.CF (FinDec)

/-! ## The interval translation and the statements -/

/-- **The interval translation for `[a, b]`** with generators `x`:
`⊥ ↦ a`, `p ↦ x p`, `∧` and `∨` componentwise, `A → B ↦ (rel A ↠ rel B) ∧ b`,
`◯A ↦ ◯(rel A) ∧ b`. -/
def rel (a b : PLLFormula) (x : String → PLLFormula) : PLLFormula → PLLFormula
  | .prop p => x p
  | .falsePLL => a
  | .and A B => .and (rel a b x A) (rel a b x B)
  | .or A B => .or (rel a b x A) (rel a b x B)
  | .ifThen A B => .and (.ifThen (rel a b x A) (rel a b x B)) b
  | .somehow A => .and (.somehow (rel a b x A)) b

/-- `⊤ = ⊥ ↠ ⊥`. -/
abbrev topF : PLLFormula := FreeIPL.topF

/-- **A faithful interval copy of `H_ω` in `[a, b]`**: the generators lie in
`[a, b]`, and the interval translation reflects and preserves derivability of
◯-free sequents,

    (∀ p, [a] ⊢ x p) ∧ (∀ p, [x p] ⊢ b) ∧
      ∀ A B ◯-free,  [A] ⊢ B  ⟺  [rel a b x A] ⊢ rel a b x B. -/
def FreeIn (a b : PLLFormula) (x : String → PLLFormula) : Prop :=
  (∀ p, Deriv [a] (x p)) ∧ (∀ p, Deriv [x p] b) ∧
    ∀ A B : PLLFormula, boxFree A = true → boxFree B = true →
      (Deriv [A] B ↔ Deriv [rel a b x A] (rel a b x B))

/-- **`[a, b]` contains a copy of `H_ω` inside F0**: a faithful interval copy
with variable-free generators. -/
def FreeHAωIn (a b : PLLFormula) : Prop :=
  ∃ x : String → PLLFormula, (∀ p, atomFree (x p) = true) ∧ FreeIn a b x

/-- The atom `c` occurs in the formula. -/
def occ (c : String) : PLLFormula → Bool
  | .prop a => decide (a = c)
  | .falsePLL => false
  | .and A B => occ c A || occ c B
  | .or A B => occ c A || occ c B
  | .ifThen A B => occ c A || occ c B
  | .somehow A => occ c A

/-- **A fresh renaming for `ξ`, `ζ`**: injective, and no image occurs in `ξ` or
`ζ`. -/
def Fresh (ρ : String → String) (ξ ζ : PLLFormula) : Prop :=
  (∀ p q, ρ p = ρ q → p = q) ∧ ∀ p, occ (ρ p) ξ = false ∧ occ (ρ p) ζ = false

/-- **The core generators** `coreGen ξ ζ ρ p = (ρ p ∨ ξ) ∧ ζ`. -/
def coreGen (ξ ζ : PLLFormula) (ρ : String → String) (p : String) : PLLFormula :=
  ((PLLFormula.prop (ρ p)).or ξ).and ζ

/-- **The nested generators**: the core generators of `[ξ, ζ]` carried into
the copy `rel a b x`. -/
def nestGen (a b : PLLFormula) (x : String → PLLFormula) (ξ ζ : PLLFormula)
    (ρ : String → String) (p : String) : PLLFormula :=
  rel a b x (coreGen ξ ζ ρ p)

/-- **The core lemma (★)**: for ◯-free `ξ`, `ζ` with `[ξ] ⊢ ζ` and `[ζ] ⊬ ξ`
and a fresh renaming `ρ`, the generators `(ρ p ∨ ξ) ∧ ζ` give a faithful copy
of `H_ω` in `[ξ, ζ]`. -/
def CoreLemma : Prop :=
  ∀ (ξ ζ : PLLFormula) (ρ : String → String), boxFree ξ = true → boxFree ζ = true →
    Deriv [ξ] ζ → ¬ Deriv [ζ] ξ → Fresh ρ ξ ζ → FreeIn ξ ζ (coreGen ξ ζ ρ)

/-- **Transport and nesting, explicit generators**: a faithful interval copy
carries the core copy of `[ξ, ζ]` to a faithful copy in `[rel ξ, rel ζ]`. -/
def Nest : Prop :=
  ∀ (a b : PLLFormula) (x : String → PLLFormula) (ξ ζ : PLLFormula) (ρ : String → String),
    FreeIn a b x → boxFree ξ = true → boxFree ζ = true →
    Deriv [ξ] ζ → ¬ Deriv [ζ] ξ → Fresh ρ ξ ζ →
    FreeIn (rel a b x ξ) (rel a b x ζ) (nestGen a b x ξ ζ ρ)

/-- **The main theorem**: inside F0, every faithful interval copy with
variable-free data contains a copy of `H_ω` in each strict sub-interval
`[rel ξ, rel ζ]`, ◯-free `ξ`, `ζ`. -/
def MainTheorem : Prop :=
  ∀ (a b : PLLFormula) (x : String → PLLFormula) (ξ ζ : PLLFormula),
    atomFree a = true → atomFree b = true → (∀ p, atomFree (x p) = true) → FreeIn a b x →
    boxFree ξ = true → boxFree ζ = true → Deriv [ξ] ζ → ¬ Deriv [ζ] ξ →
    FreeHAωIn (rel a b x ξ) (rel a b x ζ)

/-- **The bridge**: a faithful copy above a base `b` (the form of
`FreeHAωAbove`) is a faithful interval copy in `[b, ⊤]`. -/
def Bridge : Prop :=
  ∀ (b : PLLFormula) (x : String → PLLFormula), (∀ p, Deriv [b] (x p)) →
    (∀ A B : PLLFormula, boxFree A = true → boxFree B = true →
      (Deriv [A] B ↔ Deriv [relB b x A] (relB b x B))) →
    FreeIn b topF x

/-- **The base-3 copy as an interval copy**: `FreeIn σ³⊥ ⊤ xω`. -/
def Bridge3 : Prop := FreeIn (base 3) topF xω

/-- **Depth-two nesting inside the base-3 copy**: level one `[rel ξ₁, rel ζ₁]`
with the nested generators, level two `[rel₁ ξ₂, rel₁ ζ₂]` inside it. -/
def NestTwo : Prop :=
  ∀ (ξ₁ ζ₁ ξ₂ ζ₂ : PLLFormula) (ρ₁ : String → String),
    boxFree ξ₁ = true → boxFree ζ₁ = true → Deriv [ξ₁] ζ₁ → ¬ Deriv [ζ₁] ξ₁ → Fresh ρ₁ ξ₁ ζ₁ →
    boxFree ξ₂ = true → boxFree ζ₂ = true → Deriv [ξ₂] ζ₂ → ¬ Deriv [ζ₂] ξ₂ →
    FreeHAωIn
      (rel (rel (base 3) topF xω ξ₁) (rel (base 3) topF xω ζ₁) (nestGen (base 3) topF xω ξ₁ ζ₁ ρ₁) ξ₂)
      (rel (rel (base 3) topF xω ξ₁) (rel (base 3) topF xω ζ₁) (nestGen (base 3) topF xω ξ₁ ζ₁ ρ₁) ζ₂)

/-! ## The PLL statement (OPEN, not in scope) -/

/-- A faithful interval copy of PLL in `[a, b]`, `◯ ↦ ◯(·) ∧ b`, all formulas. -/
def FreeInPLL (a b : PLLFormula) (x : String → PLLFormula) : Prop :=
  (∀ p, Deriv [a] (x p)) ∧ (∀ p, Deriv [x p] b) ∧
    ∀ A B : PLLFormula, (Deriv [A] B ↔ Deriv [rel a b x A] (rel a b x B))

/-- **OPEN**: `Nest` for PLL, `◯` included. -/
def NestPLL : Prop :=
  ∀ (a b : PLLFormula) (x : String → PLLFormula) (ξ ζ : PLLFormula) (ρ : String → String),
    FreeInPLL a b x → boxFree ξ = true → boxFree ζ = true →
    Deriv [ξ] ζ → ¬ Deriv [ζ] ξ → Fresh ρ ξ ζ →
    FreeInPLL (rel a b x ξ) (rel a b x ζ) (nestGen a b x ξ ζ ρ)

end Interval
end F0
end PLLND
