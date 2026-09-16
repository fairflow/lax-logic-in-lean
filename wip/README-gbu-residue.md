# The `Gbu◯` / FRJW residue left in `wip/` (packed 2026-09-02)

The decision chain (`Gbu◯`, FRJW, `decideGbuW`, `decidePLL`, the
syntactic bridge to `LaxND`) was promoted to `FRJ/Gbu/` on 2026-09-02
(lakefile library `FRJGbu`, in `defaultTargets`; the from → to table
is in `docs/frjw-compaction.md`, "Promotion").  What follows is what
stayed here, why, and how to build it.  Nothing in `FRJ/Gbu/` imports
anything in this list.

Build the residue by explicit name (a bare `lake build` does not
cover `wip/`):

    lake build wip.gbu_ljfo wip.gbu_ljfo_transport wip.gbu_ljfo_support \
               wip.gbu_ndrules wip.gbu_weakening wip.gbu_search_circ \
               wip.frjw_gcc wip.rbar wip.quot_cm

Green at the promotion (8603 jobs).

## The LJF◯ route to `Gbu◯` completeness (not core, by ruling)

Matthew, 2026-09-02: "promote the core, which I think excludes LJF◯
route to GBUW completeness.  Interesting, not for publication, not
unless we find a parallel to FRJ◯ to partner with LJF◯."

| file | lines | what | status |
|---|---|---|---|
| `gbu_ljfo_support.lean` | 242 | stage F3 support layer for the translation `T : LJF◯ → Gbu◯` | green; `transportRC`/`transportIC` and the `≐` helpers were hoisted OUT to `FRJ/Gbu/Transport.lean` |
| `gbu_ljfo_transport.lean` | 149 | the `↓↑`-freedom invariant and the saturation measure | green; imports `FRJ.Gbu.Transport` |
| `gbu_ljfo.lean` | 898 | the translation and its composition with `bridge_iff`: `gbuC_complete : Nonempty (LaxND [] φ) → ProvableGbuC (ofPLL φ)`, `gbuC_sequent_complete`, both `[propext, Quot.sound]` | green, pins in place |

Import chain: `gbu_ljfo ← gbu_ljfo_transport ← gbu_ljfo_support ←
FRJ.Gbu.Transport`; `gbu_ljfo` also imports `LJF.OBridge` and
`FRJ.Bridge`.  No file outside this trio imports any of them.

The partner Matthew's condition asks for now exists on the other side:
`laxND_of_provableGbuC : ProvableGbuC G → Nonempty (LaxND [] (toPLL G))`
(`FRJ/Gbu/LaxND.lean`, `[propext, Quot.sound]`), so `Gbu◯` ↔ `LaxND`
is closed syntactically in both directions, one direction by this
route.  Whether that makes the route publishable is Matthew's call;
the FRJW route (`gbuw_complete` + `soundnessW`) proves the same
completeness independently and is the one in core.

## Probes, refutations and superseded proposals

| file | lines | what | status |
|---|---|---|---|
| `gbu_weakening.lean` | 232 | tag-preserving weakening for FRJV | REFUTED (kernel-checked); imports `FRJ.Gbu.Search`; imported by `gbu_search_circ` |
| `gbu_search_circ.lean` | 1354 | Theorem 8◯, the correctness of `BSearch` for `Gbu◯`, and `residues_unsatisfiable` (the FRJ database route to `Gbu◯` completeness is RETIRED: its two supplies are jointly unsatisfiable) | green; the retirement record cited by `docs/calculus-map.md`; imported by `frjw_gcc` |
| `frjw_gcc.lean` | 63 | stage W4: an irregular FRJW disproof of `◯(◯p ⊃ p)`, the three facts that motivated `Lift` | green |
| `rbar.lean` | 127 | the proposed irregular rule `(R̄)` and its soundness, from before FRJW | superseded by FRJW's rule set; kept as the record of the proposal (exists only on this branch) |
| `gbu_ndrules.lean` | 115 | derivability of SC's `laxL`/`laxR` inside `Gbu◯` (the derivable half) | green; corollary of completeness now |
| `quot_cm.lean` | 86 | the four-world constraint model refuting "the ≤-quotient of a finite preorder model preserves `◯`-forcing" (why the FMP bridge had to be syntactic) | REFUTATION, `[propext]`; imports `LaxLogic.PLLKripke` only |
| `cornersweep.lean` (+ `_out.txt`) | 161 | the V-free corner sweep over the chase-revisit residual's hypotheses | probe, pre-FRJW |
| `frjv_corner_probe.lean` | 154 | corner-trigger probe over the residue frames (FRJV completeness campaign) | probe, FRJV line |
| `gbu_residue_probe.lean`, `gbu_seam1_probe.lean` | 63, 87 | seam-1 probes from the FRJV residue analysis | probes, `--run` scripts |

## Untrusted engineering evidence for the promoted chain

| file | what | how to run |
|---|---|---|
| `decidepll_smoke.lean` (+ `_out.txt`) | `decidePLL`/`decideGbuWData` on five tiny cells with verdicts fixed in advance; the gate was watched to fail | `lake env lean --run wip/decidepll_smoke.lean <atom|bot|circbot|impid|unit>` and `… data <atom|unit>` |
| `frjw_trace.lean` (+ `_out.txt`) | round-by-round store and proof-tree printers for the explainer's two runs | `lake env lean --run wip/frjw_trace.lean <unit|circp_p|G2> <store|tree>` |

Both import `FRJ.Gbu.W.Saturate`; they taint nothing and prove
nothing.
