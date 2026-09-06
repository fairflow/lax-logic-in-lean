# The pair-recording loop check `interpR`: design and the Stage 0 campaign

Route (B), node **N4**, WP12 (Matthew, 2026-09-06 09:45: "one agent,
refute-first, a selective and short campaign we hope, followed by a genuine
proof attempt if the campaign does not refute the planned results").  Every
claim below is PROVED (a named Lean declaration, pin measured), REFUTED
(kernel-checked countermodel), decided by the certified decider
(`PROVED`/`REFUTED` with an in-process certificate), or OPEN; a run past its
deadline is `TIMEOUT — SKIPPED, no verdict`.

Provenance: the WP12 run built the definition, the cells and the harness and
completed R1 and R2, then was killed at the start of R3 by an
organisation-level refusal of Claude Code access (HTTP 403, about 11:25; the
refusal was transient).  Its files were recovered uncommitted, verified in
the campaign worktree (`lake build wip.ui_routeB_r_def wip.ui_routeB_r_cells`
55 s, 56 pins, sorry-free; commit 688f35a), and R3/R4 were run there one at a
time under 300 s deadlines.

Modules: `wip/ui_routeB_r_def.lean` (the definition), `wip/ui_routeB_r_cells.lean`
(the cells, kernel-certified), `_probe/r_stage0.lean` + `_probe/r_run.sh`
(the decider harness; modes `control`, `R2-ix`, `R2-iii`, `R2-vii`, `R3`,
`R4-v1`, `R4-v2`, `R4-s1`).

## 1 · The definition

`interpR` is `interpG` (`wip/ui_routeB_n4q.lean`) with the recording test
changed.  `seen : SeenR := List (Pos × List Neg)`; a guard call for
`Qa ⊃ N` at station `done` records `(Qa, done)`; a re-attack of `Qa ⊃ N` is
cut — `⊥` in a ∀p aggregate, `⊤` in an ∃p aggregate, the SYMMETRIC check —
exactly when some recorded `(Qa, T)` has `T` set-equal to the current station
(`sameSet`, by `negMem` both ways).  So a re-attack at a strictly larger
station is NOT cut.  This is the blueprint's per-station policy that
`docs/n4-loopcheck.md` §2 refuted with the station read as a list, read as a
set.  Written in step form, structural in the fuel; builds in 12 s.

## 2 · R1 — termination: every designed cell bottoms out (kernel, `[propext]`)

Literal constancy certified at `T+1, T+2, T+3` above each measured threshold
`T` (never one fuel: false fixpoints below).

| cell | ∀p threshold | ∃p threshold | note |
|---|---|---|---|
| (i) `[(a∨b) ⊃ ↑c] ⇒ ↑(a∨b)` | 4 | 3 | |
| (ii) the 2-cycle | 8 | 8 (other goal) | |
| **(iii)** `[↓(a ⊃ ↑b) ⊃ ↑c] ⇒ ↑↓(a ⊃ ↑b)` | **13** | 13 | the list-based reset climbed here; the set stabilises after one round; ∃p false fixpoint at 9 |
| (iv) shift | 4 | — | |
| (v) unsaturated control | 3 | — | |
| (vi) nested guards | 7 | 8 (inner goal) | |
| (vii) Dyckhoff, disjunctive inner antecedent | 17 | 17 | ∃p false fixpoint at 13 |
| (ix) `[(a∨b) ⊃ ↑c, c ⊃ ↑a] ⇒ ↑a` | 7 | 7 | |
| (m1) | 4 | — | |
| (m2) | 6 (guard goal) | 5 (◯-goal) | |
| (m3) box re-creating a parked implication | 7 | — | |
| (m4) fire re-creating a box | 6 | — | |
| (m5) box and ◯-implication | 9 | — | |
| **(m6)** nested guards through a box | **34** | 34 | a false fixpoint 29 fuels below the threshold (repeats at 5, moves at 7) |
| (m7)–(m9), (m11) | 12, 9, …, 10 | — | |
| (m10) the S1 variant | 34 | 33 (false fixpoint at 30) | |
| S1 at `↑e` / at `◯g` / ∃p | 30 / 31 / 30 | | |

Gates watched failing: `gate_cell3_below` and `gate_m10_below` — the level
one below the threshold is NOT the threshold's, kernel-checked `= false`
(a claim one fuel too low would be a success if the recorded threshold were
wrong by one).  **R1 not refuted.**

## 3 · R2 — the escape property (decider, in-process certificates)

Same-station residue, cell (ix): `r = (done ⇒ ↑a | [(a∨b, done)])`,
`g = (done ⇒ ↑(a∨b) | …)`; fuels 5–7 (`|A^R(r)| = 3`, `|A^R(g)| = 9`):

    b sufficient at r:  b, done ⊢ ↑a                         PROVED
    NO escape:          b ⊢ A^R(r)           (expect REFUTED) REFUTED
    ESCAPE:             b ⊢ A^R(r) ∨ A^R(g)  (expect PROVED)  PROVED
    the escape lands at the guard:  b ⊢ A^R(g)                PROVED

Larger-station residues, cells (iii) (`↑a :: done ⇒ ↑b`, `(q3, done)`
recorded) and (vii) (`↑a :: done ⇒ ↑c`, `(q7, done)` recorded), fuels 3–8:
the re-attack is not cut, `A^R = A^P` at these states literally
(`|A^R| = |A^P|` at fuels 3–6; at (iii) fuels 7–8 `|A^P|` grows, 17 and 27,
`A^R` stays 7) and `A^R ⊢ A^P`, `A^P ⊢ A^R` both PROVED.  The bare test
"every sufficient datum reaches `A^R`" measures the wrong statement: the
datum `a ⊃ b` is sufficient at (iii) (`(a⊃b), station ⊢ b` PROVED) and is
NOT reached by `A^R` — nor by `A^P` (`(a⊃b) ⊢ A^P` REFUTED at the same
fuels), so this is the E-relativisation of the `∀p` cofinality statement
(`SatA2P` gives `E_e, Δ ⊢ A_f`, not `Δ ⊢ A_f`), not a loss; the data `b`
and `c` ARE reached by both.  With the leg restated as an `interpR` against
`interpP` comparison at those states, **R2 clean**.

## 4 · R3 — soundness (decider), campaign worktree

Cells (i), (ix) and (iii)-variant, fuels 3–6, `done ⊢ E^R` and `A^R ∧ done ⊢ G`:
every decided run PROVED (sizes 3–25 after normalisation); the third cell's
formulas at fuels 5–6 (`|E^R| = 23`) past the 300 s deadline — SKIPPED.
Control batch PROVED/REFUTED as required.  **R3 not refuted.**

## 5 · R4 — top-level cofinality on the recorded validation cells

`{◯p ⊃ r, ◯q} ⇒ ◯p` (instance χ = ⊥): fuels 4, 8, 12 — `◯⊥ ⊢ A^R` (the
instance is absorbed) PROVED at every fuel; `E^R ⊢ (◯⊥ ⊃ r) ∧ ◯q` (the
⊥-instance is reached) PROVED at fuel 4; the chains literally constant from
fuel 8 (`|A^R| = 31`, `|E^R| = 32` at 8 and 12); the larger checks SKIPPED.

`{◯p ⊃ r, s ⊃ ◯p} ⇒ r` (χ = s, datum `T = (◯s ⊃ r) ⊃ r`): fuels 4, 8, 12 —
soundness cross-check `A^R ⊢ T` PROVED at every fuel; the UNRELATIVISED
`T ⊢ A^R` REFUTED at fuels 8 and 12 with `A^R` constant (size 6) — as for
`interpP` (§4.10: validated at station fuel 10 in the E-relativised form),
the statement cofinality makes is `E^R_e, T ⊢ A^R_f`, whose run was past the
deadline (SKIPPED, `|E^R| = 20`).  No verdict on the relativised form; no
refutation.

S1 `[◯(d ⊃ p) ⊃ a, c ⊃ ◯p] ⇒ a`, Δ = c: fuels 8, 14, 20 — SKIPPED at every fuel (formula sizes 18/34, 129/143,
166/180 after normalisation; the decider settles nothing of that size within
300 s).  No verdict, no refutation; S1's cofinality for `interpR` is a matter
for the proof, not the decider.

## 6 · Verdict of the campaign

No planned result is refuted.  What the campaign could not decide at the
deadline is reported as skips (the larger E-relativised checks, sizes 20 and
above, which the decider does not settle within 300 s — as calibrated in
`docs/pqhard-cases.md`).  Per Matthew's instruction the proof stage
follows: `docs/n4-pair-proof.md` (WP12b).
