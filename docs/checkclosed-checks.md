# `checkClosed`: the checks before the build

*2026-09-02, night.  The pre-build stage of `METHOD.md` for the
verified checker of the practical decision procedure: the statement to
build, attacked for refutation against the actual `DBClosed` clauses;
every clause classified for finite checkability; the lemmas the build
leans on located.  Verdict at the end: READY TO BUILD, with one
reduction still to prove first and one engine repair.*

## 1. What is to be built

The verified consumer exists: `decideGbuW_of_dbClosed db (h : DBClosed
G db)` (`FRJ/Gbu/W/Closure.lean`).  `DBClosed` has 21 clauses, one per
FRJW rule, each saying: every instance of the rule over STORED premises
has a stored subsumer (`WSubsumes`).  The eight join clauses quantify
over families of every arity; A2 (`docs/a2-arity.md`) shows no bound
uniform in G exists.  The build is therefore in two parts:

    DBClosedDG G db      the same contract with the join clauses
                         restricted to irregular families with PAIRWISE
                         DISTINCT GOALS (∀ i j, i ≠ j → rhs i ≠ rhs j)
                         and promise families of size ≤ |dedupF (gCirc G)|

    dbClosed_of_dg       : DBClosedDG G db → DBClosed G db
    checkClosed          : Form → List (WRow G) → Bool
    checkClosed_sound    : checkClosed G db = true → DBClosedDG G db
    decideGbuW_of_check  : checkClosed G db = true → ProvableGbuC G ⊕' DisprovableW G

The full contract stays the consumer's interface (§4 says why); the
restricted one is what a checker can enumerate.

## 2. The 21 clauses, classified

`db`-polynomial means bounded by a polynomial in the store size; the
G-exponential factors are the same kind as the universe `univList G`
itself (`(3 + |Sf^R|)·2^|Ĝ|·|Sf^R| + 4^|Ĝ|·|Sf^R|`).

| clause | quantified over | after reduction | reduction | status |
|---|---|---|---|---|
| `axR`, `axI` | `F ∈ Sf^R` prime | |Sf^R| | none needed | scan |
| `andR1`, `andR2`, `impIn`, `circIn` | stored regular row × shape in `Sf^R` (+ `Clo`, `Covers`, decidable) | db-poly × |Sf^R| | none needed | scan |
| `andI1`, `andI2` | stored irregular row × shape in `Sf^R` | db-poly × |Sf^R| | none needed | scan |
| `orI` | two stored irregular rows × `∨` in `Sf^R` | db² × |Sf^R| | none needed | scan |
| `lift`, `circNotIn` | stored regular row (zone `maxTh` deterministic) | db-poly | none needed | scan |
| `impInI` | stored irregular row × Λ ⊆ Θ × `⊃` in `Sf^R` | db × 2^|Θ| × |Sf^R| | NONE: rows with different Λ have different stable zones and `WSubsumes` on irregular rows needs `Ξ ≐`, so they are pairwise incomparable; the consumer instantiates the derivation's own Λ (`Closure.lean:1656`) | G-exponential, intrinsic |
| `axIC` | `ats ⊆ gAt` with `classForce ats F = false` × `◯` in `Sf^R` | 2^|gAt| × |Sf^R| | NONE: `vacZoneA` is not monotone in `ats` | G-exponential, intrinsic |
| `joinAt`, `joinOr` (strict J2) | irregular families, any arity | cliques of stored irregular rows with distinct goals: arity ≤ |Sf^R| | B1: `ctxAt_sub`, `ctxOr_sub` PROVED | reduced |
| `joinCirc` (RELAXED J2) | irregular families, any arity | same | B1 by induction on formula size: PLAUSIBLE, cell passes, NOT yet proved (§3) | build item 1 |
| `joinAtF`, `joinOrF` | irregular families | same | B1: `joinCtxAtF_sub`, `joinCtxOrF_sub` PROVED | reduced |
| `joinAtP`, `joinOrP`, `joinCircP` | irregular × promise families | distinct-goal cliques × promise sub-families of size ≤ |Ĝ^◯| | B1: `joinCtxAtP_sub`, `joinCtxOrP_sub`; B2′: `joinCtxAtP_cut`, `joinCtxOrP_cut`, all PROVED | reduced |

So after the reductions the checker is polynomial in the store and
exponential only in G: |Sf^R| for join arity, |Ĝ^◯| for promise arity,
2^|Θ| for `impInI`, 2^|gAt| for `axIC`.  That is the class of the
store itself.  The engine caps the last two (`lamCap`, the `|gAt| ≤ 4`
cut in `seedsICW`); the checker may not.

## 3. Refutation attempts on the corollary

The corollary `dbClosed_of_dg` needs, for every join clause: an
arbitrary family satisfying the clause's hypotheses reduces to a
distinct-goal (and, for promise joins, size-bounded) sub-family whose
conclusion context contains the family's and which satisfies the
hypotheses; then the restricted clause gives a stored subsumer and
`wSubsumes_trans` (`Closure.lean:972`) closes.  Attacks:

* **The relaxed (J2) of `joinCirc`.**  A dropped premise's stable
  implication `x` owes its licence to `RefAt` over `base ++ kept`,
  possibly through a kept link `L`; the sub-family must re-derive `x`
  through its own kept chain.  A 2-cycle (`x` owes `L`, `L` owes `x`)
  would refute B1 here.  It cannot be written: `Cl` sees an implication
  only through its consequent (`cloB`, `FRJ/Basic.lean:1228`), so a
  `RefAt`/`Clo` certificate over a context uses only members of size
  at most the formula's, and dependencies descend in size.  Hence B1
  holds for `joinCirc` by strong induction on formula size, transferring
  `Clo` and `RefAt` certificates from `base ++ kept` to the sub-family's
  context; every member used is an atom, a survivor's stable formula, a
  kept link or a dropped stable implication whose own licence is
  smaller.  The cell `b1_relaxed_dropA/B` (`wip/b1b2_cells.lean`,
  kernel-decided) is the shape that induction handles: `xa`'s
  antecedent refuted only via the kept link `L`, `L`'s via an atom and
  `⊥`; strict (J2) fails for the family, the relaxed one holds, both
  drops subsume.  The relaxation is essential (the corner discharges it
  with `RefAt` certificates, `FRJ/Gbu/W/Corner.lean:205–215`; relaxed
  2026-09-01 with Matthew's sign-off), so the lemma must be proved for
  the relaxed form: build item 1.
* **Same goal, incomparable stable zones.**  Either duplicate is
  droppable (`b1a_drop0`, `b1a_drop1`; the general B1 does not choose).
* **The blocked branch of `joinAtP`/`joinOrP`** (`t' = .blocked`): no
  (J7), only (J5′), (J6); B2′ needs only those.  Survives.
* **Repeated rows, non-injective cuts.**  Distinct goals force distinct
  rows; B2′ is stated for any `e`, injective or not.  Survives.
* **The promise bound.**  A minimal hitting family for the witnessed
  modal formulas of `⋃Ξ^◯ ++ ⋂Θ^◯` has at most |witnessed formulas| ≤
  |dedupF (gCirc G)| members, and by B2′ it subsumes.  The naive bound
  (hit `⋃Ξ^◯` only) was REFUTED by `b2_naive_refuted`.  Survives.

## 4. The consumer, checked

`tCr`/`tCi` (`Closure.lean:1519–1674`) instantiate the join clauses at
`pk.Ξs' pk.Θs' rhs` — the reindexed STORED subsumers of a derivation's
premises (`irrPick`/`regPick`), of the derivation's own arity, with
duplicate goals whenever the derivation has them — and `impInI` at the
derivation's own Λ, `axIC` at its own `ats`.  So the full `DBClosed`
is exactly what the consumer needs; `DBClosedDG` may not replace it,
only imply it.  The reindexing pack (`reindex_irr`, `reindex_reg`,
`SameIrr`, `SameReg`, `W/Saturate.lean` S5) is available but not needed
for the corollary, which is stated over stored families already.  The
Boolean subsumer search exists: `subsumesB`, `findSub`,
`findSub_sub` (`Closure.lean` ~1150).

## 5. The A3 finding: the engine's `⋈^◯` is strict

`FRJ/Search/OpsW.lean:291–292` fires `joinCirc` with the strict (J2)
lifted by `.ups`; the contract's clause is the relaxed one.  An engine
store can therefore lack the conclusion of a relaxed instance over its
own rows and fail the check, so the checker would FLAG a store the
engine considers saturated.  Repair (untrusted side, no proof impact):
guard the engine's `⋈^◯` implications with `refAtB true Υ (base ++
kept)` on their antecedents, as `emitJoinCirc` does.  Build item 6.

## 6. Build plan

| # | item | depends on | estimate |
|---|---|---|---|
| 1 | `ctxOr_sub_relaxed`: B1 for the relaxed `joinCirc`, by induction on formula size (`Clo`/`RefAt` certificate transfer) | — | 3–5 h |
| 2 | `toDistinctGoals`: for each of the eight clause shapes, iterate B1 (strong induction on arity; the duplicate search is decidable over `Fin`) to an injective `e` with pairwise distinct goals, contexts ⊆, hypotheses transferred | 1, `wip/b1b2_lemmas.lean` | 6–10 h |
| 3 | `hittingCut`: the B2′ sub-family of size ≤ |dedupF (gCirc G)| (choose one witness per witnessed modal formula; index the chosen list) | `wip/b1b2_lemmas.lean` | 3–5 h |
| 4 | `DBClosedDG` and `dbClosed_of_dg` (eight join clauses via 2, 3 and `wSubsumes_trans`; the other thirteen verbatim) | 2, 3 | 4–6 h |
| 5 | `checkClosed` + `checkClosed_sound`: thirteen scans; distinct-goal cliques of `irrTs` under `subB`-(J1) (a `famsUpToC`-style enumerator); promise sublists of bounded size; Λ over `Θ.sublists`; `ats` over `(gAt G).sublists`; subsumer search by `findSub` | 4 | 15–25 h |
| 6 | `decideGbuW_of_check`; `rowsOfDBO` (engine rows into `WRow`); the engine's relaxed `⋈^◯` guard | 5 | 2–3 h |

Gate watch for 5: take a store the saturation closes, delete one
join-built row, and see `checkClosed` go `false` before trusting a
`true`.

Where it lives: items 1–4 extend `wip/b1b2_lemmas.lean` (promotable to
`FRJ/Gbu/W/Arity.lean`); 5–6 in a new `FRJ/Gbu/W/Check.lean`.  Pins
`[propext, Quot.sound]` throughout; `Fin` lemmas from Mathlib are
checked one by one (`Fin.succAbove_ne` already caught).

## 7. Not claimed

* B1 for the relaxed `joinCirc` is PLAUSIBLE (argument + one cell),
  not PROVED.
* No statement yet asserts `DBClosedDG → DBClosed`; the plan is the
  proof outline, not the proof.
* The A3 repair changes only the engine's generation; whether the
  engine's stores then pass `checkClosed` on the corpus is an empirical
  question for after the build, and a FLAG there is not a verdict.
* The G-exponential factors of `impInI` and `axIC` are intrinsic to
  the contract as designed; a contract with fewer Λ or fewer `ats`
  would need a new completeness proof and is not proposed.

## 8. Build status (2026-09-02, night): BUILT

All six items of §6 are built, sorry-free, pins `[propext, Quot.sound]`
throughout (`#guard_msgs`-guarded `#print axioms` in every file).

| # | item | where | status |
|---|---|---|---|
| 1 | B1 for the relaxed `joinCirc` (`ctxOr_sub_relaxed`, `j2r_comp`), by formula-size induction with `Clo`/`RefAt` certificate transfer | `wip/b1b2_relaxed.lean` | PROVED |
| 2 | `Shape.toDistinct`: one reindexing lemma over a clause *shape* (context map + hypothesis + one B1 step), iterated to an injective `e` with pairwise distinct goals | `wip/dbclosed_dg.lean` | PROVED |
| 3 | `hittingCut`: the promise sub-family of size ≤ `(dedupF (gCirc G)).length` | `wip/b1b2_hitting.lean` | PROVED |
| 4 | `DBClosedDG` (21 fields: the eight join clauses restricted to distinct goals / bounded promise arity, the thirteen others verbatim) and `dbClosed_of_dg : DBClosedDG G db → DBClosed G db` | `wip/dbclosed_dg.lean` | PROVED |
| 5 | `chkScan` (thirteen non-join checks + `chkScan_sound`), `chkJoins` (eight join checks over `famsDG`/`pfams` + soundness, needing `(db.map (·.s)).Nodup`), `checkClosed := Nodup && chkScan && chkJoins`, `checkClosed_sound : checkClosed G db = true → DBClosedDG G db`, `dbClosed_of_check` | `wip/check_scan.lean`, `wip/check_join.lean`, `wip/check_closed.lean` | PROVED |
| 6 | `decideGbuW_of_check (db) (h : checkClosed G db = true) : ProvableGbuC G ⊕' DisprovableW G`; `rowsOfDBO`, `engineRows`, `decideByEngine : Form → Config → Option (…)`; the engine's relaxed `⋈^◯` (`mkJoinCircRelaxedW`, fired when the strict guard fails) | `wip/check_closed.lean`, `FRJ/Search/OpsW.lean` | BUILT |

The statement, displayed:

    checkClosed G db = true  →  DBClosed G db                 (dbClosed_of_check)
    checkClosed G db = true  →  ProvableGbuC G ⊕' DisprovableW G   (decideGbuW_of_check)

### The gate watch (`lake exe checkprobe`, `tools/CheckProbe.lean`)

Twenty cells (the `wscreen` set plus `G₂`, `G₃`), engine at `rounds 16,
jmax 3, pmax 2, lamCap 24`.  Per cell: engine store → `rowsOfDBO` →
`checkClosed` → `decideGbuW_of_check`, beside the G4c oracle; then the
gate watch on the certified store: delete every join-built row and
require `false`; delete the first row and require `false`.  Output in
`wip/checkprobe_out.txt`.

| outcome | cells |
|---|---|
| store certified, decision agrees with the oracle (PASS) | 20 / 20 |
| ALARM (certified store, decision ≠ oracle) | 0 |
| FLAG (store not certified at this budget) | 0 |
| gate-join went `false` (stores with join rows) | 14 / 14 |
| gate-drop went `false` | 20 / 20 |

Notably every cell with `caps=jmax,pmax` (the engine's arity cap was
binding, so families were omitted) still certifies: the restricted
contract of §1 asks only for the arities B1/B2′ leave, which is the
point of the corollary.  Timings: engine ≤ 2 s per cell (big-ante
variant), `checkClosed` under a millisecond on these stores (≤ 49
rows).

### What §7 said, now

* B1 for the relaxed `joinCirc`: PROVED (item 1).
* `DBClosedDG → DBClosed`: PROVED (item 4).
* The A3 repair is in and the corpus question is answered on the
  twenty cells above (no FLAG); larger cells remain an empirical
  question, and a FLAG is still not a verdict.
* The G-exponential factors stand as designed.

Not promoted yet: the files sit under `wip/` (module list in
`lakefile.toml`); promotion to `FRJ/Gbu/W/Arity.lean` + `Check.lean`
is a mechanical move for a later commit.
