# wip/f0MeetCount.lean — status

The meet-only counting criterion (Matthew, 2026-10-27), on top of
`wip/f0FreeHAn.lean` (PR #99).  Public order theory about F0.  Pins
`[propext, Quot.sound]`; no `sorry`, no `native_decide`, no `Classical.choice`.

## Statements (`def … : Prop`, committed before any proof)

    MeetEmb n f      = f has vf values on the ◯-free formulas in p0 … p(n-1),
                       A ⊣⊢ B ⟺ f A ⊣⊢ f B, and f (A ∧ B) ⊣⊢ f A ∧ f B
    MeetCounting     = ∀ n K f, MeetEmb n f → TypeBound (f ⊥) K → 2ⁿ ≤ K
    NoMeetCopyH2 b   = ¬ ∃ f, MeetEmb 2 f ∧ f ⊥ ⊣⊢ b
    NoFreeHA2AnyNeg  = ∀ x₀ x₁ vf, ∀ y₀ y₁, [x₀ ∧ y₀] ⊢ t3 → [x₁ ∧ y₁] ⊢ t3 →
                         ∃ ε, ⊢ (x₀^ε₁ ∧ x₁^ε₂) ↠ t3   (x^false read as y)
    MeetEmbH1        = MeetEmb 1 h₁

with `d_ε = signedConj n ε = ⋀_{i<n} pᵢ^εᵢ` (`conjUpTo`, `padB`).

## Status table

| statement | status |
|-----------|--------|
| (to be filled as results land) | |

## Log

* 2026-10-27: statements written and committed before any proof (METHOD.md §1).
