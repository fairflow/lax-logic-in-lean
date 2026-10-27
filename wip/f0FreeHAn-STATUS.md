# wip/f0FreeHAn.lean — status

Free Heyting algebras on `n` generators inside the filters `[σᵐ⊥, ⊤]` of F0,
and the counting criterion (Matthew, 2026-10-27; follow-up to
`wip/f0FreeIPL.lean`, PR #97).  Public order theory about F0.  Pins
`[propext, Quot.sound]` unless stated.

## A. Statements (`def … : Prop`, committed before any proof)

    relB b x A       = A[a := x a, ⊥ := b]
    FreeHAnAbove b n = ∃ x ≥ b vf, ∀ A B ◯-free in p0 … p(n-1),
                         [A] ⊢ B ⟺ [relB b x A] ⊢ relB b x B
    FreeHAωAbove b   = the same for every variable        (FreeIPLInAboveT3 = FreeHAωAbove t3)
    base m           = σᵐ⊥                                 (base 0 = ⊥, base 1 = t3, base 2 = ◯t3 ∨ (◯t3 ↠ t3))
    Conjecture       = ∀ n ∃ m, FreeHAnAbove (base m) n
    BMax b M w       = w refutes b, no proper successor refutes b
    TypeBound b K    = k(b) ≤ K: K valuations Ts, a type function ty on all worlds of all
                       FinDec subframe models, every b-maximal w has type Ts (ty w)
    Distinct b K     = k(b) ≥ K: K b-maximal cells with pairwise different vf theories
    TypesFinite b    = ∃ K, TypeBound b K
    Companion        = ∀ b vf, ⊬ b → TypesFinite b
    CountingCriterion= FreeHAnAbove b n → TypeBound b K → 2ⁿ ≤ K
    PatternsRealised b n = cells indexed by the sign patterns Fin n → Bool, pairwise separated
    TwoGenPatterns b x₀ x₁ = ∀ ε, ⊬ (x₀^ε₁ ∧ x₁^ε₂) ↠ b

The candidate pair high up (in `[σ²⊥, ⊤]`):

    Y  = t4 ∨ ¬t4,   x = ◯Y,
    x₀ = ◯σ²⊥ = σ²(◯⊥),   x₁ = σ²⊥ ∨ ((◯Y ↠ t3) ↠ t3).

## Status table

| statement | status | theorem |
|-----------|--------|---------|
| (to be filled as results land) | | |

## Log

* 2026-10-27: statements written and committed before any proof (METHOD.md §1).
