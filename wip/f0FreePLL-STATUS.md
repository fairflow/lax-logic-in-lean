# wip/f0FreePLL.lean — status

Does PLL embed faithfully into its own closed fragment, `◯` included?  Drop
the generator `x₀ = ◯σ³⊥` of `wip/f0FreeBase3.lean`, keep only its readers
`gen (r+1)`, and map `◯` to `◯`.  (Conjecture approved by Matthew
2026-10-28; brief from the manager the same day.)  Public order theory
about F0.

## The statement (committed before any proof, METHOD.md §1)

    y a = gen (code a + 1)                                         (`xr`)

    FreeReaders :       ∀ A B,  [A] ⊢ B  ⟺  [relB σ³⊥ y A] ⊢ relB σ³⊥ y B

    FreePLLAbove b :    ∃ x, (∀ a, x a variable-free) ∧ (∀ a, [b] ⊢ x a) ∧
                           ∀ A B,  [A] ⊢ B  ⟺  [relB b x A] ⊢ relB b x B
    target:             FreePLLAbove (σ³⊥)

    FreePLLnAbove b n : the same, A and B over pvar 0, …, pvar (n-1)

    Stage A (rule 8):   FreeReadersIPC : the same as FreeReaders, A and B ◯-free

Designed cells (Stage B), atoms `a0 = ""` (code 0, read by `gen 1`) and
`a1 = "\x00"` (code 1, read by `gen 2`):

    O1 = ◯p → p,    O2 = ◯p ∨ ¬◯p,    O3 = ◯(p ∨ q) → ◯p ∨ ◯q

## Status table

| statement | theorem | status |
|-----------|---------|--------|
| `FreeReadersIPC` | — | OPEN |
| `FreeReaders` | — | OPEN |
| `FreePLLAbove (σ³⊥)` | — | OPEN |

## Log

* 2026-10-28: Stage 0, statement written and checked (`lake env lean`),
  committed before any proof.
