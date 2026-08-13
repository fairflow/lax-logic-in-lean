# The closed fragment of PCLL — the certified catalogue

*Created 2026-08-13 from the closed-fragment probe
(`wip/closed_frag_report.md`, worktree agent, integrated at commit
`482de49`).  This document is the canonical catalogue; the probe report
holds the method detail, `wip/closed_frag_pins.lean` the 57 kernel
certificates (`#print axioms`: propext, Quot.sound), and
`wip/closed_frag_out.txt` the full 680-cell stream.  The display lives
in the RN(◯,{}) explorer (v13, "PCLL — the confluent quotient" tab):
https://claude.ai/code/artifact/7470ba90-1a37-4c46-aa68-abeff8442b53*

PCLL = PLL + ◯(A∨B) ⊃ (◯A∨◯B); derivability-from-premises is
`PLLND.ConfluentU.DerivU`.  Complexity is `crank` (atoms/⊥ 0, ∧/∨ max,
⊃ +1, ◯ +2).

## The headline

**The closed (variable-free) fragment of PCLL does not collapse at any
crank ≤ 7** — new `DerivU`-interderivability classes appear at every
stratum, and on this evidence the fragment is infinite exactly as
PLL's is (the Curry-paper RN(◯,{}) infinity survives the quotient).
Distribution's entire visible effect at crank ≤ 7 is FOUR merges.

| crank | new classes | cumulative | status |
|---|---|---|---|
| 0 | 1 | 1 | exact (flag-free) |
| 1 | 1 | 2 | exact |
| 2 | 1 | 3 | exact |
| 3 | 2 | 5 | exact |
| 4 | 2 | 7 | exact |
| 5 | 4 | 11 | exact — the crank-≤5 quotient is fully certified |
| 6 | 8 | 19 | lower bound (26 flags) |
| 7 | 3 | 22 | lower bound (140 raised, 109 final flags) |

Collapse hypotheses: **R₀ ≤ 5 REFUTED unconditionally** (the class of
q8 = ◯¬◯⊥ ⊃ (¬◯⊥∨◯⊥) is crank-6-minimal; strata ≤ 5 are
flag-free-complete).  **R₀ = 6 fails modulo the 26 stratum-6 flags**
(three min-crank-7 classes, each separated from all 19 known crank-≤6
classes; all 57 boundary separations kernel-pinned).

## The 22 classes

`ρi` are the representative numbers of the probe report (written
`r0…r21` there; renamed here to avoid the explorer's `r k` antichain
family).  "PLL name" is the explorer's unified `t/c/g/s/r/w`
labelling, given where the bridge is certified; "was" is the q-name
dictionary of `wip/rnc_probe.lean`.

| class | crank | representative | PLL name | was | notes |
|---|---|---|---|---|---|
| ρ0 | 0 | ⊥ | t 0 | q0 | |
| ρ1 | 1 | ⊤ | ⊤ | q1 | |
| ρ2 | 2 | ◯⊥ | t 1 | q2 | |
| ρ3 | 3 | ¬◯⊥ | t 2 | q3 | |
| ρ4 | 3 | ¬◯⊥ ∨ ◯⊥ | t 3 | q4 | |
| ρ5 | 4 | ¬¬◯⊥ | t 4 | q6 | crank-4-minimal (unconditional) |
| ρ6 | 4 | ¬¬◯⊥ ∨ ¬◯⊥ | t 5 | q7 | |
| ρ7 | 5 | ◯¬◯⊥ | c 1 | q5 | crank-5-minimal (unconditional) |
| ρ8 | 5 | ¬¬◯⊥ ⊃ ◯⊥ | t 6 | q10 | |
| ρ9 | 5 | ¬¬◯⊥ ∨ ◯¬◯⊥ | s 1 | q9 | **PCLL merge**: absorbs q12 and ◯q9 |
| ρ10 | 5 | (¬¬◯⊥ ⊃ ◯⊥) ∨ ¬¬◯⊥ | t 7 | q11 | **PCLL merge**: absorbs ◯q11 |
| ρ11 | 6 | ◯¬◯⊥ ⊃ (¬◯⊥ ∨ ◯⊥) | g 1 | q8 | crank-6-minimal — refutes R₀ ≤ 5 |
| ρ12 | 6 | (¬¬◯⊥ ⊃ ◯⊥) ⊃ ◯¬◯⊥ | r 1 | q14 | |
| ρ13 | 6 | (¬¬◯⊥ ⊃ ◯⊥) ⊃ (¬◯⊥ ∨ ◯⊥) | — | q10 ⊃ q4 | **NEW** — outside the 19-candidate dictionary |
| ρ14 | 6 | (¬¬◯⊥ ∨ ◯¬◯⊥) ⊃ (¬◯⊥ ∨ ◯⊥) | w 1 | w16 | **PCLL merge**: w15 ≡ w16 ≡ w17 ≡ w18 |
| ρ15 | 6 | (◯¬◯⊥ ⊃ (¬◯⊥ ∨ ◯⊥)) ∨ ◯¬◯⊥ | g 1 ∨ c 1 | q8 ∨ q5 | |
| ρ16 | 6 | ((¬¬◯⊥ ∨ ◯¬◯⊥) ⊃ (¬◯⊥ ∨ ◯⊥)) ∨ ◯¬◯⊥ | w 1 ∨ c 1 | w16 ∨ q5 | |
| ρ17 | 6 | ¬¬◯⊥ ∨ ((¬¬◯⊥ ∨ ◯¬◯⊥) ⊃ (¬◯⊥ ∨ ◯⊥)) | t 4 ∨ w 1 | q6 ∨ w16 | |
| ρ18 | 6 | ((¬¬◯⊥ ∨ ◯¬◯⊥) ⊃ (¬◯⊥ ∨ ◯⊥)) ∨ (¬¬◯⊥ ∨ ◯¬◯⊥) | w 1 ∨ s 1 | w16 ∨ q9 | |
| ρ19 | 7 | (◯¬◯⊥ ⊃ (¬◯⊥ ∨ ◯⊥)) ⊃ ◯¬◯⊥ | g 1 ⊃ c 1 | q8 ⊃ q5 | min-crank 7; 19 pinned separations |
| ρ20 | 7 | (◯¬◯⊥ ⊃ (¬◯⊥ ∨ ◯⊥)) ⊃ (¬¬◯⊥ ∨ ¬◯⊥) | g 1 ⊃ t 5 | q8 ⊃ q7 | min-crank 7; pinned |
| ρ21 | 7 | ((¬¬◯⊥ ∨ ◯¬◯⊥) ⊃ (¬◯⊥ ∨ ◯⊥)) ⊃ ◯¬◯⊥ | w 1 ⊃ c 1 | w16 ⊃ q5 | min-crank 7; pinned |

## What distribution does (all of it, at crank ≤ 7)

Only four equivalences in the 680-cell run needed the scheme;
everything else is plain PLL:

1. q12 ≡ q9 (the one merge already known from the 19-candidate probe);
2. ◯q9 ≡ q9 and 3. ◯q11 ≡ q11 — ◯ is idempotent on the ∨-classes
   under distribution;
4. w15 ≡ w16 ≡ w17 ≡ w18 — the four zigzag closure witnesses fuse into
   the single class ρ14, resolving cells the old rnc runs left UNKNOWN
   (w17 needed one distribution-instance premise).

Every one of the fifteen PLL dictionary classes survives into the
quotient.  Also settled: ◯⊤ ≡ ⊤ (plain PLL, crank 3 → 1).

## Flags (the only gap)

109 final flags at strata 6–7, each "candidate ?≡ representative",
vector-identical on the entire ≤5-world mutually confluent battery
(9,075 frames ≤ 4 worlds + 1,459 rooted 5-world orbits) but not proved
interderivable within budget; clustered at the lattice top
(⊤: 21, ρ10: 21, ρ21: 20).  Flags can only ADD classes — every listed
class is separation-certified.  Settling one needs a ≥6-world
confluent countermodel or a deeper positive search.  One reported
skip: the seed q13 (crank 8 > cap).

## Consequence for the interpolation campaign

The `ClosedCollapse 6` hypothesis of the stage-2 kernel closures
(docs/pcll-1pv-ui-plan.md) is vacated by this catalogue: the closed
fragment does not collapse at any bounded crank a level-promotion
argument could exploit.  Contrast PICLL: over the infallible class the
fragment collapses at rank 1 (`closedCollapseInf_one`,
`wip/pcll1pv_stage4.lean`) — fallibility is exactly what makes the
fragment infinite.

## Replay

    lake build closedfrag
    .lake/build/bin/closedfrag            # full sweep, ~23 min
    .lake/build/bin/closedfrag pin        # regenerate the pin lines
    lake env lean wip/closed_frag_pins.lean   # kernel audit
