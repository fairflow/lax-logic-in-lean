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

    CoreLemmaPLLAnyXi :    (P1) without "ξ ◯-free"     (expected REFUTED, ξ = ◯q, ζ = ⊤)
    CoreLemmaPLLAnyZeta :  (P1) without "ζ ◯-free"     (expected REFUTED, ξ = ⊥, ζ = ◯⊥)
    CoreNoStrictPLL :      (P1) without "[ζ] ⊬ ξ"      (expected REFUTED, ξ = ζ = ⊥)

Task 2 (`Covers` of `wip/f0Covers.lean`):

    CoverSig3 :          Covers σ³⊥ (◯σ³⊥)                          (expected REFUTED)
    RangeNoCover :       [A] ⊢ B, [B] ⊬ A  ⟹  ¬ Covers (gR A) (gR B)
    Sig3ImageNotCover :  c, d variable-free, [c] ⊢ d, [d] ⊬ c  ⟹  ¬ Covers (σ³c) (σ³d)
    RangeBelowSig2T5 :   [gR A] ⊢ σ²t5  ⟹  [A] ⊢ ⊥
    CoverSig2T5 :        Covers σ³⊥ (σ²t5)                          (OPEN, not attempted)

## Status table

| statement | declaration | status |
|-----------|-------------|--------|
| (P1) `CoreLemmaPLL` | `CoreLemmaPLL` (Prop) | OPEN (stage 1) |
| (P2) `NestPLLFree` = `Interval.NestPLL` | `NestPLLFree` (Prop) | OPEN (stage 1) |
| (P3) `MainPLL` | `MainPLL` (Prop) | OPEN (stage 1) |
| (P4) `BridgePLL3` | `BridgePLL3` (Prop) | OPEN (stage 1) |
| (P5) `NestAllPLL` | `NestAllPLL` (Prop) | OPEN (stage 1) |
| `NestOnePLL` | `NestOnePLL` (Prop) | OPEN (stage 1) |
| `CoreLemmaPLLAnyXi`, `CoreLemmaPLLAnyZeta`, `CoreNoStrictPLL` | Props | OPEN (stage 1) |
| `CoverSig3`, `RangeNoCover`, `Sig3ImageNotCover`, `RangeBelowSig2T5` | Props | OPEN (stage 1) |
| `CoverSig2T5` | Prop | OPEN, not attempted |

No theorem is sorried; every open statement is a `Prop` definition.

## Builds

Registered in `lakefile.toml` (the `wip` glob list, on its own last line after
`wip.f0Endpoints`).  Build cache seeded by `cp -Rc` from
`~/Lean/nightly/lax-logic-in-lean/.lake` (nightly at `ff86542`; no Lean source
differs from this branch's base `4a1b755`).

| stage | command | exit | wall time | free disk before |
|-------|---------|------|-----------|------------------|
| 1 | `gtimeout 3600 lake build wip.f0NestPLL` | 0 | 15.1 s | 100,476 MB |

Only `wip.f0NestPLL` was built; every other module replayed.  Skips and caps:
none.
