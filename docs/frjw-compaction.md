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

Scope (eleven defs; the count "nine" given here until 2026-09-02 was
wrong, corrected on the complexity comparison's finding):
`joinCirc_mono`, `joinOr_mono`, `joinAt_mono`, `joinAtP_mono`,
`joinOrP_mono`, `joinCircP_mono`, `joinAtF_mono`, `joinOrF_mono`,
`circIn_mono`, `orI_mono`, `impInI_mono`.  NOT retired (still live): the `_of_swap` transfer
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

# The C-items (2026-09-02, late morning) — reusable combinators

From the Opus survey (docs/frjw-recursion-explainer-plan.md, Part C),
executed on Matthew's instruction ("Do C.3, C.7 and C.6 while Opus
runs").  These are re-expressions of proof text, not retirements: no
statement, no pin, no rule changes; the supersession check therefore
degenerates to one row each (the constraint that the proof text keep
naming what it does), recorded inline.

| item | file | before → after | what | verified |
|---|---|---|---|---|
| C.3 | `wip/gbu_frjw_search.lean` | 852 → 737 | `Focus`/`focusCtx` (split at a member with its `≐`, rest-membership and size equation), `clo_focus` (the `Clo`-coverage of a descended context; auto-param finds the one-/two-cons rest inclusion), `forall_cons` (`sfL`/`gHat` preservation member by member), `Focus.lt1`/`lt2` (the size drops).  Six focus sites (corner `L⊃ᵢ`, both `L◯`, the non-`Ĝ` member, `limpStep`, the non-critical left rules) and three `A :: Ψ` lambdas rewritten.  Every left rule now reads "focus, cover, descend, apply the constructor". | elaborated clean first time; chain rebuilt; pins unchanged; smoke 7/7 |
| C.7 | `wip/gbu_frjw_saturate.lean` | 2531 → 2434 | `emitters G db : List (List (WRow G))`, `stepAll := (emitters G db).flatten`, one `sub_stepAll (hl : l ∈ emitters G db)` via `List.mem_flatten` (checked choice-free) replaces the nineteen `Or.inl`-chain lemmas; 25 call sites read `sub_stepAll (by simp [emitters]) _ hemit`.  Nothing else unfolds `stepAll` (`stepNew`, `closureDB_fixed`, `stored_of_emitted` use it opaquely).  Constraint "each coverage site names the rule it fires": DISCHARGED, `hemit` names the emitter. | build green; pins unchanged; smoke PASS (Opus subagent, cherry-picked as `60aee6d`) |
| C.6 | `wip/gbu_frjw_closure.lean` | 1804 → 1803 | `regUp`/`irrUp` (a stored subsumer's shape, as an existential over tag and context / over the two zones) and `downReg`/`downIrr` (subsumption transport) close all 21 T-C cases: 9 unary cases take the two-line "ascend, refire, descend" form, the 8 join cases keep `irrPick`/`regPick` for their families and use the descent half, the 3 axiom cases are one-line term-mode entries.  Net line count is flat because the four lemmas with docstrings cost what the scaffold saved; the effect is deduplication: inside the `mutual` block `wSubsumes_trans` 21 → 0, `reg_shape`/`irr_shape` 9 → 0, the `rw [← hshape]; exact List.mem_map.mpr …` incantation 9 → 0, block 226 → 183 lines. | build green; `tCr`/`tCi`/`tC_of_closed`/`decideGbuW_of_dbClosed` pins re-checked in scratch, unchanged; smoke PASS (Opus subagent, cherry-picked as `1fbdef7`) |

| sweep | `wip/gbu_frjw_search.lean` | 737 → 725 | The stage-3 residue found by the stage-4 plan (§C.10): `wgTpLt` and `tpC_free_lt_circ` (both private, zero consumers; they paid for the chase's `◯`-free-antecedent release) deleted, the bare alias `have IHW := IH` removed and its two uses read `IH`. | build green; pins unchanged; smoke 7/7 |

C.3 also removes the `subst hsplit` at the non-critical left rules: the
member is recovered from the split and focused like every other site,
so `Ψ` stays a variable throughout `searchW`.

Core after the C-items: search 725 + closure 1803 + saturate 2434 =
4962 lines (goal-closed state: 1189 + 1805 + 2471 = 5465; −9%
overall, −39% on the search file).  The stage-4 plan
(docs/frjw-recursion-explainer-plan.md, written against `aa13537`)
recommends AGAINST the remaining tactic-shaped candidates: `byDecNeg`
fits one site (re-costed), and a `first`-over-the-inversion-bank tactic
saves nothing, destroys the per-site documentation of which duality
clause is used, and risks build time.  The bank is the strategy; the
sites stay named.

# Promotion (2026-09-02, evening) — the chain leaves `wip/`

Matthew: "do the promotion when it feels right to you" and, on scope,
"promote the core, which I think excludes LJF◯ route to GBUW
completeness.  Interesting, not for publication, not unless we find a
parallel to FRJ◯ to partner with LJF◯."  Executed by a subagent in its
own worktree (branch `promote-gbu`, cut from `ef9e131`), cherry-picked
here on top of the syntactic bridge (`0a4d8f3`), then the two bridge
modules moved into the promoted tree.

## What moved

| from | to |
|---|---|
| `wip/gbu.lean`                | `FRJ/Gbu/Base.lean` |
| `wip/gbu_db.lean`             | `FRJ/Gbu/DB.lean` |
| `wip/gbu_search.lean`         | `FRJ/Gbu/Search.lean` |
| `wip/gbu_measure.lean`        | `FRJ/Gbu/Measure.lean` |
| `wip/gbu_circ.lean`           | `FRJ/Gbu/Circ.lean` |
| (hoisted out of `wip/gbu_ljfo_transport.lean`) | `FRJ/Gbu/Transport.lean` |
| `wip/gbu_frjw_dichotomy.lean` | `FRJ/Gbu/W/Dichotomy.lean` |
| `wip/gbu_frjw_db.lean`        | `FRJ/Gbu/W/DB.lean` |
| `wip/gbu_frjw_circdb.lean`    | `FRJ/Gbu/W/CircDB.lean` |
| `wip/gbu_frjw_corner.lean`    | `FRJ/Gbu/W/Corner.lean` |
| `wip/gbu_frjw_search.lean`    | `FRJ/Gbu/W/Search.lean` |
| `wip/gbu_frjw_closure.lean`   | `FRJ/Gbu/W/Closure.lean` |
| `wip/gbu_frjw_exclusion.lean` | `FRJ/Gbu/W/Exclusion.lean` |
| `wip/gbu_frjw_saturate.lean`  | `FRJ/Gbu/W/Saturate.lean` |
| `wip/gbu_laxnd.lean`          | `FRJ/Gbu/LaxND.lean` |
| `wip/gbu_frjw_laxnd.lean`     | `FRJ/Gbu/W/LaxND.lean` |

The hoist: `transportRC`/`transportIC` with `ctxEq_cons`/`clo_ctxEq`
are `≐`-transports of `Gbu◯` derivations, a property of the calculus
and not of the LJF◯ route; they now live in `FRJ/Gbu/Transport.lean`
(imports `FRJ.Gbu.Circ` only, namespace `FRJ.Gbu`), and
`wip/gbu_ljfo_transport.lean` imports them.  `W/Exclusion.lean` had
imported `wip.gbu_ljfo` for `pll_of_provableGbuC`, which in fact lives
at `FRJ/Gbu/Circ.lean:1485`; its import is now `FRJ.Gbu.Circ` +
`FRJ.SoundW`.  Nothing in `FRJ/Gbu/` reaches the LJF◯ route.

**The core-admission gate, measured.**  Transitive import closure of
the crown `FRJ.Gbu.W.Saturate`, repo-local: 36 modules, namely the 14
`FRJ.Gbu.*` modules, 21 `FRJ.*` core modules and `Meta.Slime`; no
`wip.` module, no `LJF.` module, and `FRJ.Bridge` is not reached.  The
bridge module `FRJ.Gbu.W.LaxND` additionally reaches `FRJ.Bridge` and
the `LaxLogic` natural-deduction core, by design.

**Lakefile.**  New `[[lean_lib]] FRJGbu` with the sixteen modules,
added to `defaultTargets` beside `LaxLogic`, so a bare `lake build`
now covers the chain.  The globs are an explicit list: on this
toolchain (v4.31.0) `globs = ["FRJ.Gbu.*"]` (and `["FRJ.Gbu.W.*"]`,
and `["FRJ.Search.*"]`) makes `lake build FRJGbu` fail with `some
modules have bad imports` although every module builds and the
explicit list is green; `["Meta.*"]` is green.  Recorded, not
diagnosed.  The `wipshared` globs lose the sixteen moved entries and
keep the residue (`wip.gbu_weakening`, `wip.gbu_search_circ`,
`wip.rbar`, `wip.frjw_gcc`, `wip.gbu_ndrules`, the three LJF◯ files,
`wip.quot_cm`).

**The Greek rename** (`docs/notation.md`) followed in the next commit:
3194 identifier occurrences, no proof text changed, three flagged
residues recorded in the register.

## Verification

* bare `lake build`: green, 8718 jobs (the FRJGbu library included).
* `lake build` of the nine residual wip modules by explicit name:
  green (8603 jobs).
* Pins: the `#guard_msgs`-checked `#print axioms` lines of the sixteen
  moved files, 131 lines, compared as sets against the `wip/` originals
  at `0a4d8f3`: identical both ways.
* Smoke, `lake env lean --run wip/decidepll_smoke.lean`: 7/7 PASS
  (`wip/decidepll_smoke_out.txt`, dated block).
* `lake env lean --run wip/frjw_trace.lean unit tree` prints the `Gbu◯`
  proof tree.
* `git diff --stat 0a4d8f3 HEAD` over the V-family files: empty.

## Supersession check: the `wip/` placement → the `FRJGbu` library

| constraint | source | `wip/` placement | `FRJ/Gbu/` placement | verdict |
|---|---|---|---|---|
| every importer compiles after the move ("compilation is tricky when files move") | Matthew, 2026-09-02 | n/a | all importers re-pointed; bare build + explicit residue build green | DISCHARGED |
| core-admission gate: never exclude a finished result for its campaign; measure the closure; hoist stranded shared definitions | memory `core-admission-gate` | — | closure measured (36 modules, no `wip.`/`LJF.`); `transportIC` hoisted; the LJF◯ route is excluded on Matthew's ruling as a second route whose publishability is pending, not for its campaign | DISCHARGED |
| the explainer's and the architecture notes' `file:line` anchors stay resolvable | `docs/frjw-explainer.md` Provenance | paths existed | anchors are hash-pinned (`git show b2f2525:wip/gbu_frjw_search.lean`); a file-map note added at the head of both documents | DISCHARGED |
| pins byte-identical across the move | CLAUDE.md rule 1 | 131 lines | 131 lines, set difference empty both ways | DISCHARGED |
| FRJV files byte-for-byte untouched | memory `frjw-naming-discipline` | — | V-family diff empty | DISCHARGED |
| build wip modules by explicit name before trusting dependents | memory `bare-lake-build-skips-wip` | the only way to build the chain | the chain is in `defaultTargets`: a bare `lake build` is now a verification of it | LAPSED for the chain (the requirement is met by the build system); STANDS for the residue in `wip/` |

Re-opened constraints: none.

## Deferred (each needs its own supersession check before it is done)

* Archive the FRJ◯ and FRJV lines physically (comparison doc's
  recommendation).
* Retire the corner's dead kit (`RefAtG`, `refutedCleanly_circ_kept`,
  `refutedCleanly_circ_axI`) and `SaturateV`.
* `W/Exclusion.lean` namespace `FRJ.Gbu.LJFT → FRJ.Gbu.W` (changes
  pinned names).

Not deferred: the three rename residues of `docs/notation.md` were
accepted as they stand by Matthew on 2026-09-02; no family rename pass.
