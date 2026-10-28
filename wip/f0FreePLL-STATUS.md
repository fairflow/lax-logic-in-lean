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
| `⊬ O1`, `⊬ O2`, `⊬ O3` in PLL | `pll_O1`, `pll_O2`, `pll_O3` | PROVED (1-, 2-, 3-world countermodels) |
| Stage B images `relB σ³⊥ xr Oᵢ` no theorems | `cell_O1`, `cell_O2`, `cell_O3` | PROVED (gadget tables, 11, 12, 13 worlds) |
| base facts and readings on the three tables | `baseFacts_K1/K2/K3`, `reads_K1/K2/K3` | PROVED |
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

## Stage B (rule 9): three designed cells, all PASS

| cell | PLL formula | `K` | gadget `gadT K` | image | theorem |
|------|-------------|-----|-----------------|-------|---------|
| O1 | `◯p → p` | one world, `∉ S`, no atoms | 11 worlds | PASS (no theorem) | `cell_O1` |
| O2 | `◯p ∨ ¬◯p` | `k₀ ∈ S` below `k₁ ∉ S` | 12 worlds | PASS | `cell_O2` |
| O3 | `◯(p ∨ q) → ◯p ∨ ◯q` | `k₀ ∉ S` below `S`-tops `k₁ ⊩ p`, `k₂ ⊩ q` | 13 worlds | PASS | `cell_O3` |

`p = a0 = ""`, `q = a1 = "\x00"`, so `xr p = gen 1`, `xr q = gen 2` (the
kernel computes `code` on these literals; the code of `"p"` is 113, whose
reader `gen 114` would be far too large to evaluate).  `gadT K` builds the
table in Lean from `K`: the upper worlds `0 … 9` of `f0FreeBase3`
(`e₀ n₀ L₀ L₁ L₂ f m₀ m₁ m₂ kn`), then the copy `10 + i` of each world `i`,
in `S` iff `i ∈ S`, seeing `e₀ n₀ L₀ f m₀ kn` always, `m₁` and `L₁` iff
`i ⊮ p`, `m₂`, `L₁`, `L₂` iff `i ⊮ q`.  On each table `f0FreeBase3`'s
`baseFacts` holds, and `readsB`: at every copy `xr p`, `xr q` hold iff `p`,
`q` hold at the world, and the copy is in `S` iff the world is.

## Log

* 2026-10-28: Stage 0, statement written and checked (`lake env lean`),
  committed before any proof.
* 2026-10-28: Stage A, `FreeReadersIPC` PROVED, pins `[propext, Quot.sound]`.
* 2026-10-28: Stage B, three designed cells PASS (`decide +kernel` on the
  gadget tables), base facts and readings kernel-checked.
