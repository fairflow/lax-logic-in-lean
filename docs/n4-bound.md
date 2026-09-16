# The measure that founds `interpQ`: `QBound` discharged

Route (B), node N4, **WP9**.  `docs/n4-loopcheck.md` §7 left two obligations
over the loop-checked recursion `interpQ`:

    QBound p  := Σ′ μ : QState → Nat, QFounded id p μ        -- OPEN, WP8
    PQEquiv p := the redundancy lemma, as data                -- OPEN

This package discharges the FIRST.  Every claim below is PROVED (named Lean
declaration, pin measured), REFUTED (kernel-checked counterexample) or OPEN.

Modules: `wip/ui_routeB_n4q_meas.lean` (the measure and the edge mirror,
stage 0), `wip/ui_routeB_n4q_gate.lean` (the gates, watched failing),
`wip/ui_routeB_n4q_clos.lean` (the closure and the two flattening lemmas),
`wip/ui_routeB_n4q_cong.lean` (the mirror is complete),
`wip/ui_routeB_n4q_bound.lean` (the descent, `qBound`, and N4 over
`PQEquiv` alone).

---

## 1 · The measure, and why it is a `Nat` after all

`docs/n4-loopcheck.md` §4 forces the shape

    μ s = (K s − |seen|, ν s)   lexicographic,
    ν (todo, done, goal, _) = 2·sum3 todo + sum3 done + goalW goal,

and observes that a lexicographic pair is not a `Nat`, which is what
`QBound` asks for.  It can be flattened, because the SECOND component is
bounded, along the recursion, by a quantity that is itself non-increasing.
Write

    clSt s   the subformula closure of `todo ++ done ++ goal`, Dyckhoff-closed
    κ s      the number of DISTINCT antecedents of `clSt s` not in `seen`
    W s      3 ^ (mxW (clSt s) + 1),  `mxW` = the largest `wNeg` in `clSt s`
    ν s      2·sum3 todo + sum3 done + goalW goal

and put

    **μ s  =  κ s · W s + ν s**              (`qMu`)

Two arithmetic facts do all the work (`wip/ui_routeB_n4q_clos.lean` Part 5):

* `qMu_lt_of_ordinary` — from `clSt t ⊆ clSt s`, `seen` carried, and
  `ν t < ν s`:

      κ t · W t + ν t  ≤  κ s · W s + ν t  <  κ s · W s + ν s .

* `qMu_lt_of_guard` — from `clSt t ⊆ clSt s`, `seen t = Q′ :: seen s` with
  `Q′ ∈ caOf (clSt s)` and `Q′ ∉ seen s`, and `ν t < ν s + W s`:

      κ t · W t + ν t  ≤  κ t · W s + ν t  <  (κ t + 1) · W s + ν s
                       ≤  κ s · W s + ν s .

The guard edge's hypothesis `ν t < ν s + W s` is where `W` is spent: the
guard target is `([], done, ↑Q′, Q′ :: seen)` with `done` UNCHANGED, so
`ν t = sum3 done + 3 ^ wPos Q′` against `ν s = sum3 done + goalW g`, and it
is enough that `3 ^ wPos Q′ < W s`.  That is `pow_ant_lt_bigW`: the member
`Q′ ⊃ N` is in `clSt s`, so `wPos Q′ < wNeg (Q′ ⊃ N) ≤ mxW (clSt s)`.

So `QBoundW` — the generalisation of `QFounded` to a well-founded order,
scoped as stage 1 of this package — is **not needed**, and is not built.
A `Nat` measure exists, `QBound` is discharged as stated, and
`n4_of_interpQ` applies unchanged.  (It is also the better outcome: a
well-founded `μ` alone does NOT give the `Nat` threshold `QStabLitE` asks
for, since the set `{t : μ t < μ s}` is infinite and the threshold would
need a supremum over it; with a `Nat` measure the threshold is `μ s + 1`,
by `interpG_stab_of_founded`.)

## 2 · The closure

`subN M` (`wip/ui_routeB_n4q_meas.lean` Part 1) is the subformula closure in
the polarised sense — `↑P` AND `◯P` for every positive subformula `P`, since
the lax prefix moves a `◯` goal to `◯` of a subformula — closed in addition
under the **Dyckhoff residual**

    ↓(Q′ ⊃ N′) ⊃ N   ↦   ↓N′ ⊃ N                       (`subD`)

which is the ONE row of `interpQ` that manufactures an implication not
already present (`eRowsQ`'s Dyckhoff arm, the `res` argument of
`parkRowE`).  The closure is finite because the residual strictly shrinks
its own antecedent; `subP`/`subN`/`subD` are defined by well-founded
recursion on `sizePos`/`sizeNeg`.

Without the Dyckhoff clause the closure is NOT non-increasing: the residual
row would introduce `↓N′` as a compound antecedent absent from the closure
of the original cell, and `κ` could rise.  This is the one place where the
closure is more than "subformulas".

## 3 · The edge table

Every edge of one `stepQ` unfolding, the lemma that discharges it, and which
of the two flattening lemmas it uses.  `wip/ui_routeB_n4q_bound.lean`.

| edge | lemma | `κ` | `ν` |
|---|---|---|---|
| `↑a :: todo` parks; `Q ⊃ N :: todo` parks (5 shapes); `◯Q :: todo` parks | `park_lt` | carried | down (`p3_pos`) |
| `⊥ ⊃ N :: todo` dropped | `drop_lt` | carried | down |
| `↑(P∨Q) :: todo` → `b ++ todo`, both modes | `todoRepl_lt` + `invertPos_lt` | carried | down |
| `↑↓M :: todo` → `M :: todo` | `todoRepl_lt` + `p3_strict` | carried | down |
| `M ∧ N :: todo` → `M :: N :: todo` | `todoRepl_lt` + `p3_add` | carried | down |
| the atom fire `findFire` | `parkSecond_lt` (`dec_parkFire`) | carried | down |
| `∃p`/`∀p` atom-implication row `A/E(N :: rest)` | `parkSecond_lt` | carried | down |
| a parked row's second component `E(N :: rest)`, `A(N :: rest ⇒ G)` | `parkSecond_lt` | carried | down |
| a parked row's `∃p` residual `E(rest)` | `parkRes_lt` (`dec_cimp3`) | carried | down |
| the Dyckhoff residual `E([↓N′ ⊃ N] ++ rest)` | `dykRes_lt` (`dec_dykRes`) | carried | down |
| opening a parked box, `∃p` and both `∀p` halves | `boxOpen_lt` (`dec_boxE`) | carried | down |
| `∀p` goal inversion at `↑(P₁∨P₂)`, `↑↓M`, `∧`, and the whole lax prefix | `goalMove_lt` (`p3_strict`) | carried | down (goal) |
| `∀p` at an implication goal `Q ⊃ N` (`invertPos Q` grows the STATION) | `impGoal_lt` (`dec_ainv`) | carried | down (`dec_ainv`) |
| **the guard edges** `→ A(done ⇒ ↑Q′)` at `Q′ :: seen` | **`guard_lt`** | **strictly down** | may RISE, bounded by `W` |

The `∀p` implication goal is the subtle row named in `docs/n4-loopcheck.md`
§4: `invertPos Q` moves branches INTO the station, which is the growth that
refuted the per-station reset policy (§2 there).  The closure still does not
grow, because every branch of `invertPos Q` consists of subformulas of `Q`
(`invert_sub`), and `Q` is a subformula of the goal.

The guard edges are the only ones where `ν` can rise, and the only ones
where `seen` grows — which is exactly the property that recording at the
guard CALL SITE (and not at the aggregate) was chosen for.

## 4 · The mirror, and why it is sound to reason edge by edge

`edgesQ s` (`wip/ui_routeB_n4q_meas.lean` Part 3) lists the states
`stepQ id p prev` reads `prev` at.  Two facts turn the table of §3 into
`QFounded`:

    stepQ_congr    : (∀ t ∈ edgesQ s, atSt prev₁ t = atSt prev₂ t) →
                     atSt (stepQ id p prev₁) s = atSt (stepQ id p prev₂) s
    edges_decrease : ∀ t ∈ edgesQ s, qMu t < qMu s

`stepQ_congr` is the statement that the mirror is COMPLETE — that `edgesQ`
omits no consulted state — and it is proved structurally, one congruence
lemma per row function (`parkRowE_congr`, `parkRowA_congr`, `eRowsQ_congr`,
`aRowsQ_congr`, `laxPrefixQ_congr`, `aggQ_congr`), with no mention of the
measure.  `QFounded id p qMu` is their composition, and `qBound` is
`⟨qMu, qFounded p⟩`.

## 5 · Stage 0: the designed cells, and the gates watched failing

Rule 9: designed cells, no enumeration.  Before the descent proof was
scoped, `qMu` was written as a computable function and CHECKED on the cells
of `wip/ui_routeB_n4q_cells.lean` — the six ◯-free cells first (rule 8),
then the modal ones — by kernel decision:

* `adeq_circFree`, `adeq_modal` — the mirror is ADEQUATE at each cell: a
  level below masked to `edgesQ s` gives the same `stepQ` at `s`, so
  `edgesQ s` covers every consulted state.  (This is the decidable
  instance of what `stepQ_congr` later proves in general.)
* `desc_circFree`, `desc_modal` — `qMu` strictly decreases along EVERY edge
  out of EVERY state reachable within three steps of the cell.

**The gates, watched failing** (`wip/ui_routeB_n4q_gate.lean`), each a
kernel-checked `= false`:

* `gate_nu_goal_term` — drop `3 ^ wNeg goal` from `ν` and the check goes red
  at the ◯-free cell (i).  The term is there for the `∀p` implication goal,
  which pays for `invertPos Q` entering the station out of the goal's own
  weight; without it that edge RAISES the measure.
* `gate_kappa`, `gate_kappa_A` — drop `κ` and the check goes red at cell (i)
  in both modes: the guard edge raises `ν`, which is the failure the loop
  check exists to repair and the reason the measure is a product and not a
  sum.
* `gate_control` — the committed `qMu` passes at the same cell and the same
  depth, so neither gate is vacuous.

## 5b · The thresholds the measure predicts, against the observed ones

`interpG_stab_of_founded` gives the explicit threshold `μ s + 1`.  Measured
against the kernel-checked constancy fuels of
`wip/ui_routeB_n4q_cells.lean` (a bound BELOW an observed threshold would
be a contradiction; above is sound and merely crude):

| cell | `κ` | `W` | `ν` | predicted `qMu s + 1` | observed |
|---|---|---|---|---|---|
| (i) `∀p` `[(a∨b) ⊃ ↑c] ⇒ ↑(a∨b)` | 1 | 729 | 270 | 1000 | 4 |
| (i) `∃p` | 1 | 729 | 243 | 973 | 3 |
| (iii) `∀p` `[↓(a ⊃ ↑b) ⊃ ↑c] ⇒ ↑↓(a ⊃ ↑b)` | 3 | 2187 | 810 | 7372 | 12 |
| (iii) `∃p` | 3 | 2187 | 729 | 7291 | 9 |
| (m10) `∀p` | 3 | 59049 | 21879 | 199027 | 16 |
| (m10) `∃p` | 3 | 59049 | 21870 | 199018 | 15 |

Every prediction is far ABOVE the observed threshold, as it must be: the
bound is `κ · W + ν` with `W` a power of three over the whole closure, so
it counts every state the recursion COULD visit, while the observed
threshold counts the fuels the interpolant actually moves at.  Nothing here
is a contradiction; the gap is the price of a bound that is uniform in the
cell.  The `κ` column is the one that matches the qualitative reading of
`docs/n4-loopcheck.md` §5 — cell (i) has one recordable antecedent, cells
(iii) and (m10) three — and it is the component that grows with the DEPTH
of the guard graph.

## 6 · Status after WP9

| claim | status |
|---|---|
| `subP`/`subN`/`subD`, the Dyckhoff-closed closure, terminating | PROVED (elaborates) |
| `clSt t ⊆ clSt s` along every edge | PROVED, per edge (§3) |
| `κ` monotone, strictly down at a guard edge | PROVED (`kap_le`, `kap_lt`) |
| `W` monotone, above every antecedent weight | PROVED (`bigW_mono`, `pow_ant_lt_bigW`) |
| the flattening (`qMu_lt_of_ordinary`, `qMu_lt_of_guard`) | PROVED |
| `stepQ_congr` — the edge mirror is complete | PROVED |
| `edges_decrease` — the descent | PROVED |
| **`QBound p`** | **PROVED** (`qBound`) — was OPEN at WP8 |
| a `ν` without the goal term founds the recursion | **REFUTED** (`gate_nu_goal_term`) |
| a measure without `κ` founds the recursion | **REFUTED** (`gate_kappa`) |
| `PQEquiv p` (the redundancy lemma) | **OPEN** — the only obligation left |
| N4 for PLL | **OPEN**, over `PQEquiv` alone (`n4_of_pqequiv`) |

The conclusion of the package is

    n4_of_pqequiv : PQEquiv p → ∀ done G, EStabilises p done × AStabilises p done G

— N4 for `interpP` at EVERY cell, with no saturation, no parking and no
◯-freeness hypothesis, over one obligation instead of two.
