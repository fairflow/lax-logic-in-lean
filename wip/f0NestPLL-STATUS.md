# wip/f0NestPLL.lean — status

Faithful copies of PLL (`◯` included) in nested intervals of F0, for ◯-free
endpoints; and a cover check above `σ³⊥`.  Brief from the LaxLogic manager,
2026-11-02, two tasks approved by Matthew the same day.  Follow-up to
`wip/f0FreeInterval.lean` (the `H_ω` nesting, IPC fragment), `wip/f0FreePLL.lean`
(the readers' copy `gR = relB σ³⊥ xr` of PLL in `[σ³⊥, ⊤]`) and
`wip/f0Endpoints.lean` (`necBox`).  Public order theory about F0.

## Summary

All pins `[propext, Quot.sound]`; no `Classical.choice`, no `sorry`, no
`native_decide`.

**The statement (PROVED, `pllInGRInterval`).**  For ◯-free PLL formulas
`ξ`, `ζ` with `[ξ] ⊢ ζ` and `[ζ] ⊬ ξ`, the interval `[gR ξ, gR ζ]` of F0
carries a faithful copy of the free PLL algebra on `ω` generators, `◯`
included: there are variable-free `x p` in `[gR ξ, gR ζ]` with

    [A] ⊢ B   ⟺   [rel A] ⊢ rel B          for all PLL formulas A, B,

where `rel` sends `⊥ ↦ gR ξ`, `p ↦ x p`, keeps `∧`, `∨`, and sends
`A → B ↦ (rel A ↠ rel B) ∧ gR ζ`, `◯A ↦ ◯ rel A ∧ gR ζ`.  The construction
iterates.  Inside any such copy with variable-free data, each `[rel ξ, rel ζ]`
(◯-free `ξ < ζ`) carries another (`mainPLL`), at every finite depth, each
interval inside the previous one and non-degenerate (`nestAllPLL`).

**Conditions.**  `[◯a] ⊬ a` and `[b] ⊬ ◯a` are necessary for any faithful
copy in `[a, b]` (`not_freeInPLL_of_fixed`, `not_freeInPLL_of_top_box`).  The
core lemma with `◯` allowed in `ξ` is REFUTED (`ξ = ◯p`, `ζ = ⊤`), and so is
the core lemma with `◯` allowed in `ζ` (`ξ = ⊥`, `ζ = ◯⊥`).

**Not inside every interval (PROVED, `noPLLInSig3Box`).**  No sub-interval of
`[σ³⊥, ◯σ³⊥]` carries a faithful copy of PLL.  The interval does carry a copy
of `H_ω` (`hωInSig3Box`).

**Covers.**  `[σ³⊥, ◯σ³⊥]` is NOT a cover (REFUTED, `not_coverSig3`): the
element `◯σ³⊥ ∧ gen 1 = gR(◯⊥ ∧ p)` lies strictly between.  No cover of F0
has both ends in the range of `gR` (`rangeNoCover`); in particular no
`σ³`-image of a cover is a cover (`sig3ImageNotCover`).  The `σ²`-image
`[σ³⊥, σ²t5]` of the cover `t3 ⋖ t5` meets the range of `gR` only at its
bottom (`rangeBelowSig2T5`, `sig2t5_not_in_range`).  Whether it is a cover is
OPEN (`CoverSig2T5`, not attempted).

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

Added at stage 3 (each stated as a `Prop` before its proof, in the same commit):

    PLLInGRInterval :  ξ, ζ ◯-free, [ξ] ⊢ ζ, [ζ] ⊬ ξ  ⟹  FreePLLIn (gR ξ) (gR ζ)
    NoPLLBelowBox :    [b] ⊢ ◯a, [a] ⊢ a′, [b′] ⊢ b  ⟹  ¬ FreeInPLL a′ b′ x
    NoPLLInSig3Box :   [σ³⊥] ⊢ a′, [b′] ⊢ ◯σ³⊥  ⟹  ¬ FreeInPLL a′ b′ x
    HωInSig3Box :      Interval.FreeHAωIn σ³⊥ (◯σ³⊥)

## Status table

| statement | declaration | status |
|-----------|-------------|--------|
| **(P1) `CoreLemmaPLL`** | `coreLemmaPLL` | **PROVED** |
| **(P2) `NestPLLFree` = `Interval.NestPLL`** | `nestPLL`, `nestPLL_interval` | **PROVED** |
| **(P3) `MainPLL`** | `mainPLL` | **PROVED** |
| **(P4) `BridgePLL3`** | `bridgePLL3` | **PROVED** |
| **(P5) `NestAllPLL`** | `nestAllPLL` (with `freePLLIn_tower`) | **PROVED** |
| `NestOnePLL` | `nestOnePLL` | PROVED |
| **`PLLInGRInterval`** (stage 3) | `pllInGRInterval` | **PROVED** |
| `CoreLemmaPLLAnyXi` | `not_coreLemmaPLLAnyXi` | **REFUTED** |
| `CoreLemmaPLLAnyZeta` | `not_coreLemmaPLLAnyZeta` | **REFUTED** |
| `CoreNoStrictPLL` | `not_coreNoStrictPLL` | **REFUTED** |
| `NoPLLBelowBox`, `NoPLLInSig3Box` (stage 3) | `noPLLBelowBox`, `noPLLInSig3Box` | PROVED |
| `HωInSig3Box` (stage 3) | `hωInSig3Box` | PROVED |
| **`CoverSig3`** | `not_coverSig3`, `not_coverSig3'` | **REFUTED** |
| `RangeNoCover` | `rangeNoCover` | PROVED |
| `Sig3ImageNotCover` | `sig3ImageNotCover` | PROVED |
| `RangeBelowSig2T5` | `rangeBelowSig2T5` (and `sig2t5_not_in_range`) | PROVED |
| `CoverSig2T5` | Prop | OPEN, not attempted |

No theorem is sorried; the one open statement is a `Prop` definition.

Estate check of the module: `#axiom_sweep [wip.f0NestPLL] allowing [propext,
Quot.sound]` passes on all 127 declarations; with `allowing []`, 70 of 127
escape, and the pin `#axioms_within coreLemmaPLL [propext]` is rejected (both
gates watched failing, `_out/nestsweep.lean`, untracked).

Supporting lemmas, all PROVED:

| lemma | declaration |
|-------|-------------|
| preservation `a ≤ x p ≤ b`, `[A] ⊢ B ⟹ [rel A] ⊢ rel B`, all formulas | `rel_preservesPLL` |
| `⟸` of (P1) by the gluing, all formulas | `core_reflectsPLL` |
| a faithful copy is non-degenerate, `[b] ⊬ a` | `freeInPLL_strict` |
| the induction on the depth | `towerP_props` |
| `rel` respects `⊣⊢` of the endpoints; copies carried along `⊣⊢` | `rel_congr_force`, `freeInPLL_congr` |
| `rel σ³⊥ ⊤ xr A ⊣⊢ gR A` | `rel_top_interd_gR` |
| setting an atom that does not occur changes nothing | `setAtom`, `force_setAtom`, `force_setAtom_q` |
| `[B] ⊬ A ⟹ A < B ∧ (A ∨ q) < B` for `q` fresh | `nd_between` |
| `σ²t5 = σ³⊥ ∨ (σ³⊥ → ◯σ²⊥)`; every copy world of the readers' gadget refutes it | `sig2t5_eq`, `w_not_sig2t5` |
| `rel σ³⊥ ⊤ xω p₀ = ◯σ³⊥` | `code_empty`, `xω_empty` |

## Stage 3: the proofs

Task 1, the pen argument of the brief, mechanised as planned; it was right.

* Preservation: `relB_preservesO` (`wip/f0FreePLL.lean`, all formulas), through
  `rel_iff_relB_gen` (`wip/f0MovingTop.lean`: at a world forcing the top, `rel`
  and `relB` agree on every formula, `◯` included), since every `rel`-image
  forces the top (`force_rel_b`).
* Reflection: the gluing `Interval.Glue.G` of the IPC proof, unchanged.  The
  copy of `K` keeps `K`'s own `S` (`Glue.SG`, built that way at the IPC stage
  for this purpose), so the relativisation lemma with `◯` (`relB_transferO`)
  applies with `inl k ∈ S ⟺ k ∈ K.S` by `Iff.rfl`.  `Glue.collapse`, which is
  ◯-free only, is used for `ξ` and `ζ` alone: this is where "◯-free endpoints"
  enters.  At an `S`-point above the copy that is not itself a copy, `ξ`
  holds, hence every relativised formula: those worlds are inert for `◯` and
  `→`, as the brief said.
* Nesting, main theorem, bridge, depth one, tower: the IPC proofs with `FreeIn`
  replaced by `FreeInPLL`; `rel_comp` already covered `◯`.
* The clearest form: `rel σ³⊥ ⊤ xr A ⊣⊢ gR A` and copies carried along `⊣⊢`.

Task 2: `gR (B ∧ (A ∨ q))`, `q` fresh, lies strictly inside `[gR A, gR B]`:
on a countermodel of `[B] ⊢ A`, set `q` true (for `⊬ A`), resp. false (for
`B ⊬`), then the faithfulness of `gR`.  At closed `c`, `d`, `gR c = σ³c`
(`Endpoints.gR_closed`).  For `σ²t5`: a copy world of the gadget sees the
`S`-killer, which forces `σ³⊥` and refutes `◯σ²⊥`.

Stage 3 additions: `NoPLLBelowBox` is one line, `[b′] ⊢ b ⊢ ◯a ⊢ ◯a′` and then
`not_freeInPLL_of_top_box`.  Within `[σ³⊥, ◯σ³⊥]` every `◯u ∧ b′` is `b′`,
so the interval operation `◯` is trivial there.  `HωInSig3Box` is
`Interval.nestOne` at `ξ = ⊥`, `ζ = p₀`, since `◯σ³⊥ = x₀` in the `xω` copy.

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
the necessary conditions `[◯a] ⊬ a` and `[b] ⊬ ◯a` (`NecCells` of
`wip/f0Endpoints.lean`) fail for `ξ = ◯p` and for `ζ = ◯⊥` respectively.

### Task 2

| candidate `x` (`[σ³⊥] ⊢ x ⊢ ◯σ³⊥`) | `[x] ⊢? σ³⊥` | `[◯σ³⊥] ⊢? x` | verdict |
|-----------------------------------|--------------|----------------|---------|
| `x₁ = ◯σ³⊥ ∧ gen 1 = gR(◯⊥ ∧ p)` | `⊬` (`c1_not_lo`, 11-world table `gadT KA`) | `⊬` (`c1_not_hi`, `gadT K1`) | **strictly between** |
| `◯σ³⊥ ∧ (σ³⊥ ∨ ¬◯⊥)` | `⊢` (`cy_ne_lo`) | `⊬` (`cy_ne_hi`) | collapses to `σ³⊥` |
| `◯σ³⊥ ∧ (σ³⊥ ∨ t4)` | `⊢` (`cy_t4_lo`) | `⊬` (`cy_t4_hi`) | collapses to `σ³⊥` |
| `◯σ³⊥ ∧ (σ³⊥ ∨ t3)` | `⊢` (`cy_t3_lo`) | `⊬` (`cy_t3_hi`) | collapses to `σ³⊥` |

The three collapses have one pen reason: `¬◯⊥ ⊢ t3`, `t4 ⊢ t5`, and
`t3, t5 ⊢ σ²⊥ ⊢ σ³⊥` (`t3_b2`, `t5_b2` through `SigOnto.t5_le_g1F`, `b2_b3`),
so `σ³⊥ ∨ y ⊣⊢ σ³⊥`.  The `⊬` side is `[◯σ³⊥] ⊬ σ³⊥` (`base3_not_box`).
`x₁` is the copy's image of `◯⊥ ∧ p`, strictly between `⊥` and `◯⊥` in PLL.
Also: `[σ³⊥] ⊢ σ²t5` and `[σ²t5] ⊬ σ³⊥` (`sig2t5_lo`, `sig2t5_strict`).

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
| 3 | `gtimeout 3600 lake build wip.f0NestPLL -q` | 0 | 17.5 s | 100,335 MB |
| 3, sweep | `gtimeout 900 lake env lean _out/nestsweep.lean` | 1 (the two gate lines, by design) | 12.6 s | — |
| 3, header | `gtimeout 3600 lake build wip.f0NestPLL -q` | 0 | 16.9 s | 100,335 MB |
| 3, sweep again | `gtimeout 900 lake env lean _out/nestsweep.lean` | 1 (the two gate lines, by design) | 12.8 s | — |

Proof bodies were tried first with `gtimeout 900 lake env lean` on scratch
copies (14–16 s each).  Only `wip.f0NestPLL` was built; every other module
replayed.  No `lake exe`.  Skips and caps: none.

Stale elsewhere (not edited here): the module docstring and status note of
`wip/f0FreeInterval.lean` still list `NestPLL` as OPEN; it is PROVED here
(`nestPLL_interval`).
