# The FRJW–GBUW compaction — stage 1 (2026-09-01, evening)

Opened on Matthew's instruction after the goal closed at `a97787b`
(decideGbuW, the completeness pair, decidePLL — all
`[propext, Quot.sound]`).  Every retirement below carries its
constraint-supersession table; nothing is retired bare.

## Stage-1 actions

1. **Stripped**: the searchW goal-set invariant — the `WVinv` motive
   component, its ~30 per-site transfer payloads, and the defs
   `WVinv`/`vinvNil`/`vinvStep` plus the orphaned `sf_single`/`clo_id`
   (net ≈ −130 lines in `wip/gbu_frjw_search.lean`).  The measure-side
   components (`hVsf`, `hregV`) are NOT part of the invariant and stay.
2. **Archived in place**: the nine standalone T-B `_mono` defs in
   `wip/gbu_frjw_closure.lean` — kept compiled and pinned, marked in
   the module header; zero code consumers.
3. **Verified**: full project build green (8678 jobs), every
   `#guard_msgs` pin unchanged, and the decidePLL smoke cell `impid`
   re-run PASS after the strip.

## Supersession check: goal-set invariant → `totalityW`

| constraint | source | goal-set invariant | `totalityW` | verdict |
|---|---|---|---|---|
| the both-unrefuted-`∨` corner (old K1): a stuck antecedent's refutability must be re-establishable at corner time after `∨`-descents abandoned siblings | docs/searchw-architecture.md §7; the K1 analysis | one `RefAtG` certificate per visited pair, consumed at the corner | the corner settles EVERY `Sf^R`-form outright (refuted-or-derivable), no history needed; mechanically: `refAtG_to_refAt` had ZERO call sites before the strip, and the strip compiled sorry-free with the pins (`searchW`/`dichotomyW` at `[propext, Quot.sound]`) byte-identical — nothing consumed the invariant | DISCHARGED |
| maintainability at every recursion site without measure cost | the invariant's own design brief (§7) | the ~30 `vinvStep` transfers | requirement attached to the invariant itself; with the invariant gone there is nothing to maintain | LAPSED |
| the true story preserved: the invariant was the ladder that produced totality | proof-state observability (standing); §9 of the architecture doc | the code itself was the record | §9 keeps the narrative; git history keeps the code (strip commit reverts cleanly); this table keeps the verdict | DISCHARGED |

Re-opened constraints: **none**.

## Supersession check: T-B `_mono` defs → emitters + transfer lemmas

Scope: `joinCirc_mono`, `joinOr_mono`, `joinAt_mono`, `joinAtP_mono`,
`joinOrP_mono`, `joinCircP_mono`, `circIn_mono`, `orI_mono`,
`impInI_mono`.  NOT retired (still live): the `_of_swap` transfer
lemmas, the `ctx_sub` lemmas, `lift_max`, `circNotIn_max`,
`orI_mono_sub`, `impInI_mono_sub`.

| constraint | source | `_mono` defs | survivors | verdict |
|---|---|---|---|---|
| T-B on the record as standalone pinned statements (the method's target statements) | docs/frjw-fixpoint-attack.md (T-B); closure file header | the defs themselves | the defs are KEPT, compiled and `#guard_msgs`-pinned — archived in place, not deleted | DISCHARGED |
| rule-refiring with derivations under premise swap, for the closedness proof | closure file header (the original plan) | direct formalisation | the emitters fire constructors at stored rows (derivation-carrying), and the T-C induction crosses hypotheses with the `_of_swap` lemmas — the same content in use | DISCHARGED |
| derivation-carrying refiring for a FUTURE engine-checker route | the practical-DP plan (thread 3) | would serve arbitrary subsumers | a checker consumes derivations at STORED rows, which the emitters provide; the extra generality has no present consumer — if the checker design ever needs arbitrary-subsumer refiring, the archived defs are still compiled | DISCHARGED |

Re-opened constraints: **none**.

## Deferred (each needs its own check before action)

* **The two GBUW completeness routes** (LJF◯ translation vs the
  dichotomy): NO retirement now; both stand, and their independence is
  itself evidence.  Any future demotion runs this check first.
* **The `RefAtG` kit** (`wip/gbu_frjw_corner.lean`): pinned banked
  results, now without a consumer in searchW; untouched this stage.
* **The re-founding conjecture** (Matthew: "the closed db proof is the
  heart, the proof rules merely decoration"): evaluate whether
  searchW's corner manufacture can become closure-db queries, making
  the closure primary.  A design note first, not surgery — stage 2.
* **Promotion** wip/ → FRJ/ (core admission): after stage 2, with the
  closure-measurement discipline.
