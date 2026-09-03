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

## 6. The open design decision

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
NOT YET BUILT — awaiting Matthew's call between the flag and changing
the loop outright with a re-baselined differential runner.
