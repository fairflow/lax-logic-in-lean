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
| readers variable-free, above `σ³⊥` | `xr_vf`, `b3_le_xr` | PROVED |
| the readers' gadget: cells embed, killer facts, `w_k ⊮ σ³⊥`, back condition, for every `S` on the copies | `GadR.zforce`, `GadR.kn_*`, `GadR.w_not_b3`, `GadR.w_back` | PROVED |
| `w_k ⊩ gen (s+1) ⟺ ¬ Dr (s+1) k`; `w_k ⊩ xr a ⟺ k ⊩ a` | `GadR.w_gen_succ`, `GadR.w_read` | PROVED |
| ◯-free transfer, every `S` on the copies | `GadR.transferIPC` | PROVED |
| **`FreeReadersIPC`** (Stage A) | `freeReadersIPC` | **PROVED** |
| `FreeReaders` | — | OPEN |
| `FreePLLAbove (σ³⊥)` | — | OPEN |

## Stage A (rule 8): the ◯-free fragment, PROVED

The gadget `GadR.MS K Sw` is `Base3.Gad.MK` with two changes: `w_k ∈ S`
iff `Sw k` (a parameter), and the reading `Dr`: `Dr 0` empty (the `S`-killer,
the bottom of `ZL 0`, sits above every copy in `Base3.Gad.Le` whatever `D 0`
is), `Dr (r+1) k ⟺ k` refutes every atom of code `r`.  The order is
`Base3.Gad.Le K (Dr K)` unchanged, so `Base3.Gad.Le.refl`/`Le.trans` are
reused; the lemmas `zforce` … `w_gen_succ` are those of `Base3.Gad` with the
model replaced (none of them looks at the `S` of a copy).  `relB_transferω`
of `f0FreeBase3` gives `transferIPC` for every `Sw`; the direction `⟸` uses
`Sw = ∅`, the direction `⟹` is `relB_preservesω`.  No
`wip/f0FreeAnyFamily` was on main (da627e0), so nothing to cite.

## Log

* 2026-10-28: Stage 0, statement written and checked (`lake env lean`),
  committed before any proof.
* 2026-10-28: Stage A, `FreeReadersIPC` PROVED, pins `[propext, Quot.sound]`.
