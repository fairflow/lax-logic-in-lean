# wip/f0NestPLL.lean — status

Faithful copies of PLL (`◯` included) in nested intervals of F0, for ◯-free
endpoints; and a cover check above `σ³⊥`.  Brief from the LaxLogic manager,
2026-11-02, two tasks approved by Matthew the same day.  Follow-up to
`wip/f0FreeInterval.lean` (the `H_ω` nesting, IPC fragment), `wip/f0FreePLL.lean`
(the readers' copy `relB σ³⊥ xr` of PLL in `[σ³⊥, ⊤]`) and
`wip/f0Endpoints.lean` (`necBox`, `realize`).  Public order theory about F0.

## Stage 1: the statements (committed before any proof, METHOD.md §1)

`rel a b x` the interval translation (`⊥ ↦ a`, `p ↦ x p`, `∧ ∨` kept,
`A → B ↦ (rel A ↠ rel B) ∧ b`, `◯A ↦ ◯(rel A) ∧ b`), `coreGen ξ ζ ρ p = (ρ p ∨ ξ) ∧ ζ`,
`nestGen a b x ξ ζ ρ p = rel a b x (coreGen ξ ζ ρ p)`, `xr a = gen (code a + 1)`,
`gR = relB σ³⊥ xr`.

    FreeInPLL a b x :  (∀ p, [a] ⊢ x p) ∧ (∀ p, [x p] ⊢ b) ∧
                         ∀ A B,  [A] ⊢ B  ⟺  [rel a b x A] ⊢ rel a b x B
    FreePLLIn a b :    ∃ x, (∀ p, x p variable-free) ∧ FreeInPLL a b x   (= Endpoints.ClosedStep)

Task 1:

    (P1) CoreLemmaPLL :  ξ, ζ ◯-free, [ξ] ⊢ ζ, [ζ] ⊬ ξ, Fresh ρ ξ ζ  ⟹  FreeInPLL ξ ζ (coreGen ξ ζ ρ)
    (P2) NestPLLFree :   FreeInPLL a b x, ξ, ζ ◯-free, [ξ] ⊢ ζ, [ζ] ⊬ ξ, Fresh ρ ξ ζ
                           ⟹  FreeInPLL (rel a b x ξ) (rel a b x ζ) (nestGen a b x ξ ζ ρ)
                         (= Interval.NestPLL, OPEN in wip/f0FreeInterval.lean)
    (P3) MainPLL :       a, b, x variable-free, FreeInPLL a b x, ξ, ζ ◯-free, [ξ] ⊢ ζ, [ζ] ⊬ ξ
                           ⟹  FreePLLIn (rel a b x ξ) (rel a b x ζ)
    (P4) BridgePLL3 :    FreeInPLL σ³⊥ ⊤ xr
    (P5) NestAllPLL :    tower from (σ³⊥, ⊤, xr), steps (rel_d ξ_d, rel_d ζ_d, nestGen … (freshRen ξ_d ζ_d)),
                         TowerHyp:  ∀ d,  FreeInPLL a_d b_d x_d,  x_d p variable-free,  [b_d] ⊬ a_d,
                           [a_d] ⊢ a_{d+1},  [a_{d+1}] ⊢ b_{d+1},  [b_{d+1}] ⊢ b_d
    NestOnePLL :         ξ, ζ ◯-free, [ξ] ⊢ ζ, [ζ] ⊬ ξ  ⟹  FreePLLIn (rel σ³⊥ ⊤ xr ξ) (rel σ³⊥ ⊤ xr ζ)

    CoreLemmaPLLAnyXi :    (P1) without "ξ ◯-free"
    CoreLemmaPLLAnyZeta :  (P1) without "ζ ◯-free"
    CoreNoStrictPLL :      (P1) without "[ζ] ⊬ ξ"

Task 2 (`Covers` of `wip/f0Covers.lean`):

    CoverSig3 :          Covers σ³⊥ (◯σ³⊥)
    RangeNoCover :       [A] ⊢ B, [B] ⊬ A  ⟹  ¬ Covers (gR A) (gR B)
    Sig3ImageNotCover :  c, d variable-free, [c] ⊢ d, [d] ⊬ c  ⟹  ¬ Covers (σ³c) (σ³d)
    RangeBelowSig2T5 :   [gR A] ⊢ σ²t5  ⟹  [A] ⊢ ⊥
    CoverSig2T5 :        Covers σ³⊥ (σ²t5)                          (OPEN, not attempted)

## Status table

| statement | declaration | status |
|-----------|-------------|--------|
| (P1) `CoreLemmaPLL` | `CoreLemmaPLL` (Prop) | OPEN (stage 2) |
| (P2) `NestPLLFree` = `Interval.NestPLL` | `NestPLLFree` (Prop) | OPEN (stage 2) |
| (P3) `MainPLL` | `MainPLL` (Prop) | OPEN (stage 2) |
| (P4) `BridgePLL3` | `BridgePLL3` (Prop) | OPEN (stage 2) |
| (P5) `NestAllPLL` | `NestAllPLL` (Prop) | OPEN (stage 2) |
| `NestOnePLL` | `NestOnePLL` (Prop) | OPEN (stage 2) |
| `CoreLemmaPLLAnyXi` | `not_coreLemmaPLLAnyXi` | **REFUTED** |
| `CoreLemmaPLLAnyZeta` | `not_coreLemmaPLLAnyZeta` | **REFUTED** |
| `CoreNoStrictPLL` | `not_coreNoStrictPLL` | **REFUTED** |
| `CoverSig3` | `not_coverSig3` | **REFUTED** |
| `RangeNoCover`, `Sig3ImageNotCover`, `RangeBelowSig2T5` | Props | OPEN (stage 2) |
| `CoverSig2T5` | Prop | OPEN, not attempted |

No theorem is sorried; every open statement is a `Prop` definition.

## Stage 2: the designed cells (refutation stage, CLAUDE.md rules 7 and 9)

Read off the pen argument; no sweep.  Every cell kernel-checked (`SubTab.no`
by `decide +kernel`, or a derivation), pins `[propext, Quot.sound]`.

### Task 1

Inside the readers' copy: `[a₁, b₁] = [rel σ³⊥ ⊤ xr ξ, rel σ³⊥ ⊤ xr ζ]`,
`ξ = p₀ ∧ p₁`, `ζ = p₁` (`p₀ = ""`, `p₁ = "\x00"`), `x₁ = nestGen σ³⊥ ⊤ xr ξ ζ ρc1`
(`ρc1 : "" ↦ "\x01", "\x00" ↦ "\x02"`).  Depth two:
`[a₂, b₂] = [rel₁ ⊥, rel₁ p]`, `x₂ = nestGen a₁ b₁ x₁ ⊥ p ρc2` (`ρc2 : "" ↦ "\x00"`).
`O1 = ◯p → p`, `O3 = ◯(p ∨ q) → ◯p ∨ ◯q` (`p = ""`, `q = "\x00"`).

| cell | statement | declaration | verdict |
|------|-----------|-------------|---------|
| (i) | `[rel₁ ⊤] ⊬ rel₁ O1` | `Cells.cell1_O1` | **PASS** (13-world table `gadP 3 rd3 KO1`) |
| (i) | `[rel₁ ⊤] ⊬ rel₁ O3` | `Cells.cell1_O3` | **PASS** (17-world table `gadP 4 rd4 KO3`) |
| (i) theorem | `⊢ ◯◯p → ◯p` and `[rel₁ ⊤] ⊢ rel₁(◯◯p → ◯p)` | `Cells.pll_CP`, `Cells.cell1_pos` | **PASS** (semantic proof) |
| (i) gate | the table of `cell1_O1` does not refute the transferred theorem | `Cells.gate_watch` | watched failing |
| (ii) | `[rel₂ ⊤] ⊬ rel₂ O1`, depth two | `Cells.cell2_O1` | **PASS** (15-world table `gadP 4 rd4 KT1`) |
| readings | `gen r` reads the atom of code `r - 1` at every copy; copies carry `K`'s `S` | `Cells.reads_KO1`, `reads_KO3`, `reads_KT1` | PROVED |
| (iii) | `¬ FreeInPLL a a x` for all `a`, `x` | `cell_diagPLL` | **FAIL, as designed** |
| (iii) | (P1) without `[ζ] ⊬ ξ` | `not_coreNoStrictPLL` | **REFUTED** (`ξ = ζ = ⊥`) |
| (iii) | `ξ = ζ = p₀ ∧ p₁` in the base copy | `cell3_base3P` | **FAIL, as designed** |
| remark | `[◯a] ⊢ a ⟹ ¬ FreeInPLL a b x` | `not_freeInPLL_of_fixed` (via `Endpoints.necBox`) | PROVED |
| remark | `[b] ⊢ ◯a ⟹ ¬ FreeInPLL a b x` | `not_freeInPLL_of_top_box` | PROVED |
| remark | (P1) with `◯` in `ξ` | `not_coreLemmaPLLAnyXi` | **REFUTED** (`ξ = ◯p`, `ζ = ⊤`) |
| remark | (P1) with `◯` in `ζ` | `not_coreLemmaPLLAnyZeta` | **REFUTED** (`ξ = ⊥`, `ζ = ◯⊥`) |

The tables are the pen proof's construction.  The PLL countermodel of `C`
(`O1`: one world outside `S`; `O3`: `FreePLL.K3`) is glued into the one-world
countermodel of `[ζ] ⊢ ξ`; the worlds above `w` force `ξ`, hence every
relativised formula, and are dropped.  Then the readers' gadget over the
result, `gadP R rd K` = `Interval.Cells.gadW R rd K` with the copies carrying
`K`'s own `S`.

Why ◯-free endpoints, for this route: the gluing keeps `ξ`, `ζ` at their
values at `w` on the copy of `K` (`Glue.collapse`), and the copy carries
`K`'s `S`, unrelated to `N`'s; a `◯`-subformula of `ξ` or `ζ` would read that
`S`.  The two REFUTED variants show the hypothesis cannot simply be dropped:
the known necessary conditions `[◯a] ⊬ a` and `[b] ⊬ ◯a` (`NecCells` of
`wip/f0Endpoints.lean`) fail for `ξ = ◯p` and for `ζ = ◯⊥` respectively.

### Task 2

| candidate `x` (`[σ³⊥] ⊢ x ⊢ ◯σ³⊥`) | `[x] ⊢? σ³⊥` | `[◯σ³⊥] ⊢? x` | verdict |
|-----------------------------------|--------------|----------------|---------|
| `x₁ = ◯σ³⊥ ∧ gen 1 = gR(◯⊥ ∧ p)` | `⊬` (`c1_not_lo`, 11-world table `gadT KA`) | `⊬` (`c1_not_hi`, `gadT K1`) | **strictly between** |
| `◯σ³⊥ ∧ (σ³⊥ ∨ ¬◯⊥)` | `⊢` (`cy_ne_lo`) | `⊬` (`cy_ne_hi`) | collapses to `σ³⊥` |
| `◯σ³⊥ ∧ (σ³⊥ ∨ t4)` | `⊢` (`cy_t4_lo`) | `⊬` (`cy_t4_hi`) | collapses to `σ³⊥` |
| `◯σ³⊥ ∧ (σ³⊥ ∨ t3)` | `⊢` (`cy_t3_lo`) | `⊬` (`cy_t3_hi`) | collapses to `σ³⊥` |

So **`CoverSig3` is REFUTED** (`not_coverSig3`): `[σ³⊥, ◯σ³⊥]` is not a cover
of F0.  The three collapses have one pen reason: `¬◯⊥ ⊢ t3`, `t4 ⊢ t5`, and
`t3, t5 ⊢ σ²⊥ ⊢ σ³⊥` (`t3_b2`, `t5_b2` through `SigOnto.t5_le_g1F`, `b2_b3`),
so `σ³⊥ ∨ y ⊣⊢ σ³⊥`.  The `⊬` side is `[◯σ³⊥] ⊬ σ³⊥` (`base3_not_box`).
`x₁` is the copy's image of `◯⊥ ∧ p`, strictly between `⊥` and `◯⊥` in PLL.

Also: `[σ³⊥] ⊢ σ²t5` and `[σ²t5] ⊬ σ³⊥` (`sig2t5_lo`, `sig2t5_strict`), the
strict pair of the OPEN candidate `CoverSig2T5`.

Cross-check: the subframe tableau (`SubTab.solve`, untrusted, interpreted, in
`_out/nestprobe.lean`, untracked) gave the same verdicts on the six cells of
the three collapsing candidates (closed tableaux for `[x] ⊢ σ³⊥`;
countermodels of 14, 15, 15 worlds, minimised to 11, for `[◯σ³⊥] ⊬ x`) and on
`σ³⊥ ⊢ σ²t5` (closed) and `σ²t5 ⊬ σ³⊥` (19 worlds, minimised to 8); the
designed tables of Task 1 refute their formulas there too, and the gate table
does not.  None of these runs is evidence; the module re-checks every verdict
in the kernel.

## Builds

Registered in `lakefile.toml` (the `wip` glob list, on its own last line after
`wip.f0Endpoints`).  Build cache seeded by `cp -Rc` from
`~/Lean/nightly/lax-logic-in-lean/.lake` (nightly at `ff86542`; no Lean source
differs from this branch's base `4a1b755`).

| stage | command | exit | wall time | free disk before |
|-------|---------|------|-----------|------------------|
| 1 | `gtimeout 3600 lake build wip.f0NestPLL` | 0 | 15.1 s | 100,476 MB |
| 2, probe | `gtimeout 900 lake env lean _out/nestprobe.lean` | 0 | 37.6 s | 100,476 MB |
| 2 | `gtimeout 3600 lake build wip.f0NestPLL -q` | 0 | 21.1 s | 100,375 MB |

Only `wip.f0NestPLL` was built; every other module replayed.  Skips and caps:
none.
