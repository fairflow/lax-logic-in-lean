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

# Stage 2 (2026-09-02) — the corner runs straight through totality

## Actions

1. **Stripped the chase apparatus at the corner** of `searchW`: the
   `QD` decision (refuted-or-chase-blocked), `findNotT QD`, the
   all-refuted fast path (`refutedCleanly_circ` strict), `hstuck`, the
   unused `decRP` test, and the whole chase branch (`L⊃ᵢ` into an
   unrefuted antecedent with pair-`V` bookkeeping, `wgW_chase`).  The
   corner now goes: `findCMT` → `R₀` → the certificate test →
   `refutedCleanly_circ_certs` or `totalityW` → `L⊃ᵢ` by size-drop.
   Compiled first time; pins byte-identical; full build green; smoke
   cells `impid`/`unit` re-run PASS.
2. **`decRP` removed from the chain**: the linter showed `searchW` no
   longer references its pledged-query supply; removed from `searchW`,
   `dichotomyW`, and the `decideGbuW_of` call.  `decWEvalRP`/`WEvalRP`
   stay defined (archive); nothing in the decision chain consumes them.
3. **Orphans deleted**: `wgW_chase`, `unclosed_ctxEq`, the
   irregular-corner `upsToImp`.
4. Sizes: `wip/gbu_frjw_search.lean` 1189 (goal closed) → 1092 (stage 1)
   → 939 (stage 2), −21%.

## Supersession check: the chase → the totality tail

| constraint | source | the chase | totality tail | verdict |
|---|---|---|---|---|
| a critical `◯Z`-cell with an unrefuted, non-small, modal context antecedent must still be decided (derive `◯Z` or exhibit the row) | architecture §3 (the corner), §4 | `L⊃ᵢ` into the antecedent, paid by the visited-pair measure | `totalityW` decides EVERY `Sf^R`-form at a critical cell structurally (refuted-or-derivable); a derivable antecedent feeds `L⊃ᵢ` with the consequent recursion paid by `seqSize`; a refuted one enters the certificate test.  Mechanically verified: the chase branch deleted, `searchW` compiles sorry-free with pins unchanged | DISCHARGED |
| re-chasing the same antecedent under a different goal must be measure-payable (why PAIRS, not antecedents) | §4 | the pair set `V` | no chase, nothing to pay; `V` is never pushed at any remaining call site (verified by grep: every `IHW` call passes `[]`) | LAPSED |
| a `V`-revisit certifies an open ancestor frame (the §4 "consequence") | §4 | analysis load-bearing for the invariant | no revisits exist | LAPSED |
| the all-refuted fast path (`refutedCleanly_circ`, strict `.ups` chain) | the pre-J2 corner | separate manufacture when every antecedent is refuted | subsumed: every refuted antecedent is in `R₀`, so the certificate test passes on the left disjunct and `refutedCleanly_circ_certs` fires | DISCHARGED |
| the pledged-row exclusion at the corner (`gbuInv13` via `decRP`) | the pre-totality corner | needed by the old certificate-conversion branch | that branch is gone; no remaining step consumes a pledged-row fact (linter: `decRP` unreferenced) | LAPSED |
| the true story (§4 pair-V as "Innovation 1") | proof-state observability; §4, §9 | the code | §4 stays as history with a note; git history holds the code; this table holds the verdict | DISCHARGED |

Re-opened constraints: **none**.

# Stage 3 (2026-09-02) — the pair-`V` measure retired

Proposed after stage 2 (evidence: `V` is constant `[]` through the
whole recursion — both surviving `IHW` sites pass `[]`), dry-run in
scratch, and executed on Matthew's go ("Continue to stage 3").

## Actions

1. **Measure reverted** to the original triple `wgC = (unclosed, tpC,
   seqSize)` with `WgLt`/`wgLt_wf` (from `wip/gbu.lean`).  Deleted:
   `sfPairs`, `vRem`, `wgW`, `WgLtW`, `wgLtW_wf`, `wgW_of_wgC`,
   `wgW_drop`, and the `V`/`hVsf`/`hregV` plumbing at every call site.
   The two induction hypotheses `IH`/`IHW` collapse into one; the
   fixpoint is `wgLt_wf.fix` over `main : ∀ x, ∀ p, wgC G p.1 p.2.1
   p.2.2 = x → WSearchOk G D p`.
2. **A strip hazard, recorded**: the vacuous payload
   `(fun h => Bool.noConfusion h)` served two masters — the `hregV`
   side condition AND the `hΩc` clause of `WSearchOk` at a `◯`-shaped
   goal.  A blanket deletion broke five sites; the five `hΩc` lambdas
   were re-inserted.  (Opus's plan §C.2 counted these six sites
   separately for the same reason.)
3. Sizes: `wip/gbu_frjw_search.lean` 939 (stage 2) → 852 (stage 3);
   1189 → 852 overall, −28%.
4. **Verified** (see the commit): `lake build wip.gbu_frjw_search
   wip.gbu_frjw_closure wip.gbu_frjw_saturate` green (the wip library
   is NOT in `defaultTargets`; bare `lake build` proves nothing about
   it), every `#guard_msgs` pin unchanged, smoke cells re-run PASS.

## Supersession check: the pair-`V` measure → `wgC`

| constraint | source | pair-`V` measure | `wgC` | verdict |
|---|---|---|---|---|
| termination of the chase (`L⊃ᵢ` from goal `◯Z` into an antecedent `A` whose size the goal does not bound) | architecture §2, §4 | `\|Sf^R × Sf^R ∖ V\|` strictly drops on every chase | the chase was retired at stage 2 (its own table above); no remaining step descends into an unbounded antecedent — the `L⊃ᵢ` sites are paid by `seqSize` (the consequent recursion) or by `unclosed` (the `R⊃ₙ` callback from `totalityW`) | LAPSED |
| re-chasing the same antecedent under a different goal must be measure-payable | §4 | pairs rather than antecedents | no chase | LAPSED |
| `V` confined to irregular mode, reset for free at `R⊃ₙ` (`hregV`, `wgW_drop`) | search file, the fixpoint's side conditions | side conditions carried by every recursive call | no `V` | LAPSED |
| the `unclosed`-first ordering of the measure (an `R⊃ₙ` step grows the context, so nothing else can pay for it) | §2 | first component | unchanged: still the first component of `wgC` | DISCHARGED |
| the `tpC` grading by `hasCirc`, not `isCirc` (`R∧ᵢ` at `C₁ ∧ ◯C₂`) | gbu_circ.lean, the `tpC` comment | third component | unchanged: second component of `wgC` | DISCHARGED |
| the true story: §4 was announced as "Innovation 1" | proof-state observability; architecture §4, §9 | the code | §2/§4 of the architecture doc carry a dated note; git history holds the code (commits a97787b … dd88424); this table holds the verdict | DISCHARGED |

Re-opened constraints: **none**.

What is left of the measure is exactly what `searchO` (the retired
`◯`-free predecessor) used; the FRJW search adds no measure component
of its own.  Termination is bought by `unclosed` (context growth),
`tpC` (mode release) and `seqSize` (structure), and by `totalityW`'s
structural recursion on the goal formula.
