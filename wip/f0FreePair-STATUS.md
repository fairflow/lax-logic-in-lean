# wip/f0FreePair.lean — status

Does the pair `(x₀, x₁)` of `wip/f0FreeHAn.lean` freely generate a copy of
the free Heyting algebra `H₂` on two generators inside `[σ²⊥, ⊤]` of F0,
with bottom `σ²⊥`?  (Matthew, 2026-10-27.)  Public order theory about F0.
Pins `[propext, Quot.sound]` throughout; no `Classical.choice`, no `sorry`,
no `native_decide`.

## The statement (committed before any proof, METHOD.md §1)

    b  = σ²⊥ = ◯t3 ∨ (◯t3 ↠ t3)                      (`b2 = base 2`)
    x₀ = ◯σ²⊥,   x₁ = σ²⊥ ∨ ((◯Y ↠ t3) ↠ t3),   Y = t4 ∨ ¬t4
    xs (pvar 0) = x₀,  xs (pvar 1) = x₁,  xs a = x₀ otherwise        (`xs`)

    FreePair :  ∀ A B ◯-free with varsBelow 2,
                  [A] ⊢ B  ⟺  [relB σ²⊥ xs A] ⊢ relB σ²⊥ xs B

    freeHAn_of_freePair :  FreePair → FreeHAnAbove (σ²⊥) 2

`pvar 0 = p`, `pvar 1 = pp` (written `p`, `q` below).  `⟹` is substitution;
the content is `⟸`.

Fragment first (CLAUDE.md rule 8): the ◯-free variable-free fragment is
`{⊥, ⊤}`; it has no interval to carry generators, and the IPC instance of
the question (`H₂` free on `p, q`) is the definition.  Degenerate here.

## Status table

| statement | theorem | status |
|-----------|---------|--------|
| `FreePair → FreeHAnAbove (base 2) 2` | `freeHAn_of_freePair` | PROVED (packaging) |
| `FreePair` | — | OPEN |

## Log

* 2026-10-27 19:38: statement written and built (`lake build wip.f0FreePair`),
  committed before any proof.
