# Progress towards completeness — FRJV / FRJW / FRJX, 1 September 2026

Branch `FRJX`.  Written for Matthew; safe to hand to whoever picks this up.

## Two targets, not one

    Gbu◯ completeness for PLL :   PLL G  →  ProvableGbuC G
    FRJV/W/X completeness     :   ¬ PLL G  →  G has a regular disproof

They are the two halves of one duality.  On the `◯`-FREE fragment both are
DONE and machine-checked: `search` (Theorem 8) with `gbu_frj_duality`
(Theorem 9) and `provableV_of_not_pll`, transferred to `Gbu◯` by
`provableGbuC_iff_provableGbu`.  Everything below concerns the modal case.

## The obstruction, located and kernel-checked

The duality fails at `◯(◯Z ⊃ Z)` with BOTH sides empty:

| fact | name |
|---|---|
| FRJV has no irregular disproof of `◯(◯Z ⊃ Z)`, for any `G, Z, Σ, Θ` | `no_irregular_circ_imp_self` |
| `Gbu◯` cannot prove `∅ →g ◯(◯p ⊃ p)` — and must not, by `soundIC` | `not_gbuIC_Gcc` |
| yet a REGULAR disproof exists, by the barren `⋈^◯` join | `provableV_Gcc` |

Consequence: `residues_unsatisfiable` — Theorem 8◯'s two supplies `BigAnte`
and `CleanReg` are JOINTLY UNSATISFIABLE, so `searchO` asserts nothing for
any modal `G`.  Not a gap to be filled; a false hypothesis.  The route is
retired.  `cirr_circ_to_irr` separately shows the former single open point
(★) was never needed.

## The repair, and what screening cost it

`(Lift)`: a regular disproof becomes an irregular one over any retained
`Ĝ`-context inside `Cl(Γ)`.  Two screening results shaped the design before
any of it was built on:

* `not_saturated_liftClosed` — `(Lift)` as a property of the DATABASE is
  contradictory with `Saturated`.  It must extend DERIVABILITY.  This killed
  the first design draft.
* `not_X14` — the `L⊃ᵢ` size-condition residue is REFUTED, at
  `Ω = {p, ◯p ⊃ p}`, `A = ◯p`, `Z = r`; and so is its natural correction, by
  the same cell at `Z := p`.  `gbuIC_omegaX_circp` shows the node is
  discharged by `R◯ᵢ` then `Ax`, so the `hsz` residue was an ORDERING
  artefact in `searchO`, not a gap.  The sorried `bigAnte_closed` has been
  removed from the plan: it asserted a statement now proved false.

## The denominator

| | closed | open |
|---|---|---|
| port surface (`wipx/frjx_ports.lean`) | **12** | 8 |
| plan (`wipx/frjx_plan.lean`) | 4 of 19 | **15** |

Sorry-free and pinned: 21 declarations in `wipx/frjx_screen.lean`; and in the
ports file `satInsert`, `satExtractR`, `satExtractI`, `relift`, `gbuInv2'`,
`gbuInv5'`, `gbuInv6'`, `gbuInv7'`, `gbuInv9'`, `evalR_of_refutedCleanly'`,
`evalI_axI'`, `unrefutedBelow_of_gHat'`.

The 8 open ports all break at one place — `SaturatedOver`'s extraction lands
in `LiftClosure`, not `FDerivable` — and `satExtractI` with `relift` are
exactly the tools for it; each needs its own `mk` constructor.

Of the 15 open plan lemmas, **X6 `evalI_of_evalR` is the keystone**: three
lines if right (take `Θ := Ω`), and X7 `(∨-inv)` and X8 `(★)` are its
corollaries.  Those two were the search's unmet needs, and neither motivated
`(Lift)`; that they fall out is the design's coherence check.

## Honest position

Completeness is **OPEN**, and not close.  What has changed is that the
obstruction is no longer diffuse: one named gap, a repair whose soundness is
checked (`not_force_of_rootAbove`), which survived two screening tests, and
whose consequences are 15 stated lemmas rather than an unbounded search.
FRJV's own unrestricted completeness is likewise open, with the
frame-conditioned and goal-guarded partials unchanged.

FRJW (Fable's branch): W1–W4 landed, and on 31 August the completeness route
changed to LJF◯ focalisation via `bridge_iff`, standing down the database
line.  FRJX has been kept deliberately blind to that work; it is the
controlled test of the route FRJW abandoned.
