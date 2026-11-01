# wip/f0FreeInterval.lean — status

The nested relativisation of the free Heyting algebra `H_ω` inside F0, the
closed fragment of PLL.  Campaign approved by Matthew 2026-11-01; brief from
the LaxLogic manager the same day.  Follow-up to `wip/f0FreeBase3.lean`
(`freeHAωAbove_base3 : FreeHAωAbove (base 3)`, the copy `relB σ³⊥ xω` of `H_ω`
in `[σ³⊥, ⊤]`).  Public order theory about F0.

## Stage 1: the statements (committed before any proof, METHOD.md §1)

Interval translation for `[a, b]` with generators `x : String → PLLFormula`:

    rel a b x ⊥ = a,   rel a b x p = x p,   ∧, ∨ componentwise,
    rel a b x (A → B) = (rel A ↠ rel B) ∧ b,   rel a b x (◯A) = ◯(rel A) ∧ b

    FreeIn a b x :  (∀ p, [a] ⊢ x p) ∧ (∀ p, [x p] ⊢ b) ∧
                      ∀ A B ◯-free,  [A] ⊢ B  ⟺  [rel a b x A] ⊢ rel a b x B
    FreeHAωIn a b : ∃ x, (∀ p, x p variable-free) ∧ FreeIn a b x

    Fresh ρ ξ ζ :   ρ injective, no ρ p occurs in ξ or ζ
    coreGen ξ ζ ρ p = (ρ p ∨ ξ) ∧ ζ
    nestGen a b x ξ ζ ρ p = rel a b x (coreGen ξ ζ ρ p)

    CoreLemma :   ξ, ζ ◯-free, [ξ] ⊢ ζ, [ζ] ⊬ ξ, Fresh ρ ξ ζ  ⟹  FreeIn ξ ζ (coreGen ξ ζ ρ)
    Nest :        FreeIn a b x, ξ, ζ ◯-free, [ξ] ⊢ ζ, [ζ] ⊬ ξ, Fresh ρ ξ ζ
                    ⟹  FreeIn (rel a b x ξ) (rel a b x ζ) (nestGen a b x ξ ζ ρ)
    MainTheorem : a, b, x variable-free, FreeIn a b x, ξ, ζ ◯-free, [ξ] ⊢ ζ, [ζ] ⊬ ξ
                    ⟹  FreeHAωIn (rel a b x ξ) (rel a b x ζ)
    Bridge :      (∀ p, [b] ⊢ x p), relB b x faithful on ◯-free sequents  ⟹  FreeIn b ⊤ x
    Bridge3 :     FreeIn σ³⊥ ⊤ xω
    NestTwo :     depth two inside the base-3 copy

    OPEN (PLL stage, not in scope):  NestPLL, `Nest` for all formulas, ◯ included

## Status table

| statement | declaration | status |
|-----------|-------------|--------|
| `CoreLemma` | `CoreLemma` (Prop) | OPEN (stage 1) |
| `Nest` | `Nest` (Prop) | OPEN (stage 1) |
| `MainTheorem` | `MainTheorem` (Prop) | OPEN (stage 1) |
| `Bridge`, `Bridge3` | `Bridge`, `Bridge3` (Props) | OPEN (stage 1) |
| `NestTwo` | `NestTwo` (Prop) | OPEN (stage 1) |
| `NestPLL` | `NestPLL` (Prop) | OPEN, not in scope |

No theorem is sorried; every open statement is a `Prop` definition.

## Builds

Registered in `lakefile.toml` (the `wip` glob list, after `wip.f0FreePLL`).
Bare `lake build` skips `wip` modules: build with
`gtimeout 3600 lake build wip.f0FreeInterval`.
