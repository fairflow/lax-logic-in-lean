# Where the FRJW engine's time goes (measured 2026-09-03)

Opened after the 99-cell batch left two cells undecided at 10 s
(`docs/decider-outputs-design.md` §9.6) and Matthew asked to look at the
engine's efficiency savings — none had ever been sought.

Cell: `(◯◯p ∧ ◯q) ⊃ ◯(◯p ∧ q)`, `jmax=3 pmax=2 lamCap=24`.
Profiler: `scratch prof.lean/prof2.lean/prof3.lean` (not committed; the
numbers are reproducible from the recipe below).

## 1. The store is tiny; the enumeration is not

| rounds ≤ | time | rs | is | fams | pfams | fams×pfams |
|---|---|---|---|---|---|---|
| 1 | 14 ms | 13 | 9 | 129 | 91 | 11 739 |
| 2 | 365 ms | 26 | 9 | 129 | 351 | 45 279 |
| 3 | 1636 ms | 35 | 9 | 129 | 630 | 81 270 |
| 4 | 3970 ms | 37 | 9 | 129 | 703 | 90 687 |
| 5 | 6598 ms | 37 | 9 | 129 | 703 | 90 687 |

Saturation completes in 5 rounds over **37 regular and 9 irregular
rows**.  The cost is entirely combinatorial in the enumeration, not in
the store.

## 2. It is the promise-join cross product, and nothing else

Over one round's worth of pairs (48 modal families × 703 promise
families = 33 744 pairs):

| what | cost |
|---|---|
| full `mkJoinPW` over all pairs (emits **74 625** candidate rows) | 2468 ms |
| the round itself | 2628 ms |

**94% of the engine is `newJP` in `roundStepO`** (`FRJ/Search/Core.lean`).
The 74 625 rows are then subsumption-tested into a store that converges
at 37.

## 3. REFUTED: hoisting the loop-invariant check

`j1j2CheckW a rest` depends only on the family, yet sits inside the
703-iteration loop over promise families — 33 744 calls for 48 distinct
answers.  It looks like the obvious win.  Measured:

| | |
|---|---|
| `j1j2CheckW` inside the loop (33 744 calls) | **125 ms** |
| the same, once per family (48 calls) | 0 ms |
| full `mkJoinPW` over the same pairs | 2468 ms |

**5% of the cost.**  All 129 families pass the check, so it prunes
nothing either.  Not worth the `Ops` interface change.  Recorded because
the idea is attractive and wrong, and the next reader will have it too.

## 4. The real waste: full rounds after convergence

Rows added per round are 13, 13, 9, 2, **0**, while every round pays the
full 33 744-pair price:

| round | rows added | time |
|---|---|---|
| 3 | 9 | 1271 ms |
| 4 | 2 | 2334 ms |
| 5 | **0** | 2628 ms |

Round 5 exists only to observe the fixpoint and costs 40% of the run.

## 5. The fix: semi-naive (differential) evaluation

Fire a (family, promise-family) pair only when it contains a row NEW
since the last round; old×old was fired in an earlier round and cannot
yield anything fresh.

The enumerator is built and VALIDATED (scratch `delta.lean`): for
`new`, `old`, `k`,

    famsDeltaUpTo new old k  ++  famsUpTo old k   =   famsUpTo (new ++ old) k

as sets of families — checked on seven shapes including both degenerate
ends.

    def famsDeltaUpTo {α : Type} (new old : List α) (k : Nat) : List (α × List α) :=
      (combosLe k new).flatMap (fun s =>
        match s with
        | [] => []
        | a :: srest => (combosLe (k - s.length) old).map (fun t => (a, srest ++ t)))

On the shape round 4 actually hits (2 new regular rows against 35 old,
`k = 2`): **703 promise families → 73**, a 9.6× cut.

Projected on the round data above: **6.6 s → ~1.2 s, about 5×**, and the
saving grows with store size, the waste being quadratic in it.

## 6. BUILT (2026-09-03): `Config.semiNaive`, default OFF

`FRJ/Search/Core.lean` now carries a differential round, `roundStepG`,
selected by `Config.semiNaive` (`FRJ/Search/Engine.lean`).  With the flag
`false` — the default — `saturateO` IS the previous definition
(`saturateNaiveO`), so the paper and V engines are untouched;
`lake exe frjvrun diff` stays ALL AGREE.

**How the generation is identified.**  Not positionally.  `O.RS`/`O.IS`
have no `DecidableEq` and `insertRO` filters subsumed rows, so a row's
index is not a stable name for it.  The store is instead SPLIT —
`DBG` = `rsN`/`rsO`, `isN`/`isO` — and `insertRG` is `insertRO` with the
same test and the same filter applied to both halves, so
`viewG d = { rs := d.rsN ++ d.rsO, … }` is exactly the `DBO` the naive
loop holds at that point.  Rows are never identified, only kept apart.

**One gap in §5's enumerator, found by `#guard`.**  At `k = 0` the
identity FAILS, in the unsafe direction: `famsUpTo` reaches
`combosLe (k - 1)` and truncates, so `famsUpTo l 0 = famsUpTo l 1` (all
singletons), while `combosLe 0 new = [[]]` makes `famsDeltaUpTo _ _ 0 =
[]`.  `roundStepG` therefore passes `max k 1`.  The `#guard`s at
`famsDeltaUpTo` record the failure as well as the passing shapes.

**The `max` compensation is now itself guarded** (2026-09-04).  `deltaOK`
states the identity at a SINGLE `k` and so says nothing about the shape
`roundStepG` actually calls — the delta at `max k 1` against
`famsUpTo old k`.  Until `deltaOKmax` was added that step was asserted
only in the prose above; `jmax = 0` and `pmax = 0` are admissible
`Config` values, so the corner is reachable rather than hypothetical.
Gate watched failing: replacing `max k 1` by `k` in `deltaOKmax` turns
the two `k = 0` lines with a NON-EMPTY delta red, and only those.

**Measured** (compiled binaries; §1–§4's absolute numbers are from the
interpreted profiler and run ~10× slower).  Engine time only,
`lake exe wscreen prof`, re-measured 2026-09-04 (the 2026-09-03 figures
it replaces were within 6% on every row):

| cell | budget | naive | semiNaive | speedup |
|---|---|---|---|---|
| `(◯◯p ∧ ◯q) ⊃ ◯(◯p ∧ q)` | jmax=3 pmax=2 | 559 ms | 218 ms | 2.6× |
| `◯(◯p ∨ ◯q) ⊃ (◯p ∨ ◯q)` | jmax=3 pmax=2 | 211 ms | 120 ms | 1.8× |
| `(◯◯p ∧ ◯q) ⊃ ◯(◯p ∧ q)` | jmax=5 pmax=4 | 79 739 ms | 38 776 ms | 2.1× |
| `◯(◯p ∨ ◯q) ⊃ (◯p ∨ ◯q)` | jmax=5 pmax=4 | 19 846 ms | 14 441 ms | 1.4× |

**§5's ~5× projection is not reached, and the projection was wrong.**  It
read the 9.6× cut off ROUND 4 and applied it to the whole run.  Rounds 2
and 3 are where most of the work is and almost everything in them is
new, so the differential barely shrinks them; the elimination is
concentrated in the last rounds, which is a constant-factor 2–3×, not
5×.

**End to end, and a correction (re-measured 2026-09-04).**  The
2026-09-03 entry read "185.5 s → 139.2 s and 55.3 s → 48.6 s (1.33× and
1.14×) … `checkClosed` plus the decision extraction cost ~100 s and
~34 s".  Re-run as `pll φ --rounds=40 --jmax=5 --pmax=4 [--semi-naive]`,
wall clock from the shell, the binary called directly with no other
flags:

| cell | verdict | naive | semi-naive | speedup | engine's share (naive) |
|---|---|---|---|---|---|
| `(◯◯p ∧ ◯q) ⊃ ◯(◯p ∧ q)` | PROVABLE | 85.0 s | 46.3 s | **1.84×** | 79.7 s = 94% |
| `◯(◯p ∨ ◯q) ⊃ (◯p ∨ ◯q)` | DISPROVABLE | 53.6 s | 48.1 s | 1.11× | 19.8 s = 37% |

The second row reproduces (55.3 → 48.6 against 53.6 → 48.1); **the first
does not, and the conclusion drawn from it was wrong.**  On the PROVABLE
cell the engine is 94% of `pll`'s run, not "under half", and the round's
2.1× carries almost undiminished to 1.84× end to end.

**And the residue is not `checkClosed`.**  `lake exe checkprobe` reports
`check=0ms` on all 20 of its cells, against engine times up to 2 s; the
store `checkClosed` scans is the 37-row one of §1, whatever the budget
that produced it.  What costs 33.8 s on the DISPROVABLE cell — and only
5.3 s on the PROVABLE one — is the OUTPUT LAYER on the refutation path:
countermodel minimisation, the SVG, and the two-pass kernel certificate.
So the next measurement belongs there, not in the certificate and not in
the round.

**Fixpoint.**  `lake exe wscreen snd` compares the two stores per cell
under three notions — `EXACT` (same rows, same order), `PERM` (same
rows, different order, zones compared as lists), `SET` (matched only up
to set-equality of the zones, i.e. different representatives of a
mutual-subsumption class).  18/18 curated cells agree: 14 `EXACT`, 4
`PERM`, 0 `SET`, 0 `DIFFER`; the four profile runs above are all `PERM`.

## 7. Corpus agreement over `batch/formulas.txt` (2026-09-04)

The claim §6 has to survive is a COMPLETENESS one.  `checkClosed`
verifies the engine's store whatever the strategy, so a defect in the
delta logic cannot produce an unsound verdict — it can only produce an
INCOMPLETE store, and the symptom would be a cell the naive loop settles
and the differential one reports `not-closed-within-bound`.  That is
what this sweep hunts.

`lake exe pllbench --engine=frjw`, one mode on one cell per process
under a 20 s wall cap, over all 129 cells; wall clock from the shell.
Raw rows in `batch/semi-naive-agreement.tsv`.

**129 / 129 cells agree, verdict for verdict**: 74 `valid`, 45
`invalid`, 10 timeout, identically in both modes.  Not one cell that
naive settles goes `don't-know` under semi-naive, and no cell settles
that naive could not.  The ten timeouts are the SAME ten cells —
083, 107, 111, 112, 118, 119, 120, 123, 124, 125 — so **none of the
level-3 residue is rescued by this optimisation.**

**End-to-end aggregate over the 119 settled cells: 132 440 ms →
127 588 ms, 1.04×**, and the largest single win is 1.8×:

| cell | formula | naive | semi-naive | speedup |
|---|---|---|---|---|
| 094 | `((◯p ⊃ ◯q) ⊃ ◯p) ⊃ ◯p` | 950 ms | 521 ms | 1.8× |
| 090 | `((◯p ⊃ q) ⊃ q) ⊃ (◯p ∨ q)` | 668 ms | 466 ms | 1.4× |
| 117 | `(◯(p ∨ q) ∧ (p ⊃ r) ∧ (q ⊃ r)) ⊃ ◯r` | 721 ms | 580 ms | 1.2× |
| 103 | `◯(◯(◯p ∧ q) ⊃ q) ⊃ ◯q` | 10 538 ms | 8 772 ms | 1.2× |
| 076 | `(◯p ⊃ ◯q) ⊃ ◯(p ⊃ q)` | 511 ms | 461 ms | 1.1× |
| 082 | `(◯◯p ∧ ◯q) ⊃ ◯(◯p ∧ q)` | 10 520 ms | 10 155 ms | 1.04× |
| 113 | `(¬¬(p ∨ ¬p)) ⊃ ((p ⊃ q) ∨ (q ⊃ p))` | 13 319 ms | 13 183 ms | 1.01× |
| 126 | `◯(◯p ⊃ ◯q) ⊃ (◯p ⊃ ◯q)` | 18 846 ms | 18 860 ms | 1.00× |
| 069 | `¬(p ∧ q) ⊃ (¬p ∨ ¬q)` | 6 022 ms | 6 143 ms | 0.98× |

**A 2× engine buys 1.04× at this budget, and the split is the one §6
ends on.**  The cells where the round IS the cost (094, 090, 117, 103)
carry the whole visible win; the ones at the top of the table are
dominated by the output layer and barely move.  0.98× on 069 is
run-to-run noise, not a regression — the two modes reach identical
stores there.

The aggregate is low because `jmax=3 pmax=2` is a budget at which the
round is cheap for most cells.  Raise the budget until the round is the
work — §6's `--jmax=5 --pmax=4` row — and the same optimisation is
worth 1.84×.  So: **real, and its size is entirely a function of how
much of the run is saturation.**  Worth having, worth leaving OFF by
default until a caller needs it, and NOT the thing that will settle the
ten residual cells.

## 8. The original open design decision (settled by §6)

Semi-naive must identify which rows are new, and `O.RS`/`O.IS` carry no
`DecidableEq`; the clean route is generation-tagged rows in `DBO`.  That
changes `FRJ/Search/Core.lean` — the loop SHARED by the paper, V and W
engines and guarded by the differential runner that checks the paper
instance against the legacy engine row for row.  Semi-naive reaches the
same fixpoint, but subsumption-based insertion is order-sensitive, so
which of several mutually-subsuming rows survives may differ and that
runner may legitimately go red.

Recommended: a `Config.semiNaive` flag, default OFF, so the paper and V
engines are untouched and the W engine opts in; validate with
`wscreen`, `checkprobe` and a batch re-run before it becomes a default.

**Built as recommended, and all three validations are now run**
(2026-09-04): `wscreen` 18/18 PASS and `wscreen semi` 18/18 PASS, both
`no alarms`; `checkprobe` and `checkprobe --semi-naive` both
`alarms=0 gate-failures=0`, row counts and decisions identical cell for
cell; the 129-cell batch re-run of §7 agreeing verdict for verdict; and
`frjvrun diff` still ALL AGREE, so the flag-OFF path is the legacy
engine unchanged.  The remaining decision — whether the flag ever
becomes the DEFAULT — is Matthew's, and §7 is the argument for taking
it slowly: the gain is 1.04× at the batch's own budget.

## 9. A family where the engines reverse (2026-09-04)

Two hand-crafted sequents from the uniform-interpolation analysis
(`docs/ui-ljfo-clause-table.md`, in preparation): the separating sequent
of `PLLG4Gap.lean`, which needs two uses of `◯p ⊃ r` in G4-style search,
and its one-deeper nesting, which needs three —

    sep2   ◯((◯p ⊃ r) ⊃ ◯p) ⊃ ((◯p ⊃ r) ⊃ r)
    sep3   ◯((◯p ⊃ r) ⊃ ◯((◯p ⊃ r) ⊃ ◯p)) ⊃ ((◯p ⊃ r) ⊃ r)

| cell | `pll` (FRJW, default `Config`) | `pllbench --engine=g4c` |
|---|---|---|
| sep2 | **unsettled**: one run killed at 19 min 32 s, a second at 172 s | `valid`, ms |
| sep3 | **unsettled after the full 900 s alarm** | `valid`, ms |

Both G4c verdicts are `.proved` with a proof object behind them, so
they are sound as validity claims (13 s wall for the pair, all of it
process startup).  §7 measured FRJW at 1.04× of itself and G4c as the
faster oracle on most cells; this family is the sharp end of that: a
provable sequent whose proof needs repeated use of one hypothesis is
exactly what a refutation engine cannot short-cut — it must exhaust the
store — and exactly what goal-directed search finds at once.  Recorded
because the batch's 20 s cap would have filed sep2 as a mere timeout,
and because "needs three uses" (a hand argument, OPEN as a theorem) is
the kind of claim the UI work will keep generating.

The practical rule that follows: a single validity check of a
hand-crafted sequent goes to the G4c oracle via a two-column TSV and
`lake exe pllbench --engine=g4c --cells=<file>`, never to `lake exe pll`.
