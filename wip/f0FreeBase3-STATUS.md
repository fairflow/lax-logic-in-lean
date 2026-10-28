# wip/f0FreeBase3.lean — status

Does one family of generators above `σ³⊥ = base 3` freely generate the free
Heyting algebra on every finite number of generators?  (Brief 2026-10-28,
follow-up to `wip/f0FreePair.lean`.)  Public order theory about F0.  Pins
`[propext, Quot.sound]` throughout; no `Classical.choice`, no `sorry`, no
`native_decide`.

## The statement (committed before any proof, METHOD.md §1)

    σ³⊥  = ◯σ²⊥ ∨ (◯σ²⊥ ↠ σ²⊥)                          (`base_three`, by `rfl`)
    φ_k  = relX (rn (2k+1))                              (`phiK`)
    c_r  = φ_{r+1} ∨ (φ_{r+2} ↠ σ²⊥)                     (`sepC`)
    x₀   = ◯σ³⊥,   x_r = σ³⊥ ∨ ((c_r ↠ σ²⊥) ↠ σ²⊥)  (r ≥ 1)   (`gen`)
    x3 a = gen (utf8ByteSize a - 1),  so x3 (pvar i) = gen i    (`x3`)

    Free3 :  ∀ n A B ◯-free with varsBelow n,
               [A] ⊢ B  ⟺  [relB σ³⊥ x3 A] ⊢ relB σ³⊥ x3 B

    FreeFamily3 :  ∃ x, (∀ a, x a variable-free) ∧ (∀ a, [σ³⊥] ⊢ x a) ∧
                      ∀ n A B ◯-free with varsBelow n,
                        [A] ⊢ B ⟺ [relB σ³⊥ x A] ⊢ relB σ³⊥ x B

    Free3 → FreeFamily3 → ∀ n, FreeHAnAbove (σ³⊥) n → Conjecture

Side cell: `⊢? (g1 ↠ g3) ∨ (g3 ↠ g1)`, `g1 = oddGap 0`, `g3 = oddGap 1`
(`sideCell`).

Fragment first (CLAUDE.md rule 8): degenerate, as in `f0FreePair` (the ◯-free
variable-free fragment is `{⊥, ⊤}`).

## Status table

| statement | theorem | status |
|-----------|---------|--------|
| `σ³⊥ = ◯σ²⊥ ∨ (◯σ²⊥ ↠ σ²⊥)` | `base_three` | PROVED (`rfl`) |
| generators variable-free, above `σ³⊥` | `x3_vf`, `b3_le_x3` | PROVED |
| `Free3 → FreeFamily3` | `freeFamily3_of_free3` | PROVED (packaging) |
| `FreeFamily3 → ∀ n, FreeHAnAbove (σ³⊥) n` | `freeHAnAbove_of_family` | PROVED (packaging) |
| `(∀ n, FreeHAnAbove (σ³⊥) n) → Conjecture` | `conjecture_of_base3` | PROVED (packaging) |
| `Free3` | — | OPEN |
| side cell | — | OPEN |

## Log

* 2026-10-28: Stage 0, statement written and built
  (`lake build wip.f0FreeBase3`, 35 s), committed before any proof.
