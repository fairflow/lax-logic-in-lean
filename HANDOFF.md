# HANDOFF — lax-logic-in-lean (fairflow/lax-logic-in-lean)

## 2026-08-25c — FRJ◯ #80/#81 PROVED as incompleteness THEOREMS; CompletenessFRJ REFUTED; the RefAt repair validated

Branch `claude/frj-incompleteness-80-81-251e7f` (merges
`claude/frj-redevelopment-69005f` @ 393194c, so this branch IS the live
FRJ◯ line plus today's work).  Full report with proof states and
derivation trees: the session artifact "FRJ(◯) Witnesses 80 and 81".

**PROVED (kernel-checked, sorry-free, `[propext, Quot.sound]`, pinned):**

    FRJ80.frj_incompleteness_80 : ¬ PLL G80 ∧ ¬ Provable G80   (wip/frj80_noprov.lean)
    FRJ81.frj_incompleteness_81 : ¬ PLL G81 ∧ ¬ Provable G81   (wip/frj81_noprov.lean)
    FRJ80.not_CompletenessFRJ   : ¬ Certified.CompletenessFRJ

with G80 = ρ12 ⊃ ρ9, G81 = ρ13 ⊃ ρ6.  These are the first CALCULUS-level
incompleteness results (all prior evidence was cap-free saturation
closure, a statement about the search).  The FinCM → FRJ.Kripke
unification was NOT needed: the 5-world `sepM` frame was rebuilt
natively as a `Search.Tab` and `decide`-checked, and `¬ Provable` is a
last-rule case analysis whose semantic steps are discharged by the
already-proved `lemma39R` and `tag_cone`.  The same template converts
any Frontier79 candidate into a theorem (per-cell case analysis needed).

**The mechanism (one sentence):** join contexts cannot retain an
implication forced VACUOUSLY at the world being created (its antecedent
ι = ¬¬◯⊥ ⊃ ◯⊥ is refuted with the new world itself as witness) — `Cl`
and the Υ-restriction are both blind to it; this is the Ax^I◯ blindness
one level up, at internal worlds.  #80 additionally has NO derivable
irregular sequent with rhs ◯¬◯⊥ at all (◯∉ premise dies on a
tag/fallibility contradiction; Ax^I◯ dies since classForce [] ¬◯⊥ =
true).

**The repair (engine-validated, NOT yet mechanised):** one relaxation,
`RefAt(Υ, ctx)` = closure of Υ under { ⊥ } ∪ { A⊃B | A ∈ Cl(ctx), B ∈
RefAt } ∪ { ◯Z | Z ∈ RefAt, barren joins only } ∪ ∨/∧-clauses,
replacing the three "refuted at the new root" tests (⋈^∨ hC, ⋈^◯ hZ,
and the Θ^⊃/Υ retention, which becomes a bounded monotone fixpoint).
Per-clause soundness argument in the report; the typed mechanisation
(Calculus + Extract + Sound) is the designated next chunk, and needs
one new lemma class: "a join root refutes EVERY premise rhs" (today
implicit in the join cases).

**Validation** (`wip/frjx.lean` untyped engine mirror + `wip/frjx_run.lean`,
exe `frjxrun`; patch off = row-for-row identical to `FRJ.Search.saturate`
on 8 goals):

* both witnesses DERIVED: `[barren] ρ12 ⇒ G80`, `[barren] ρ13 ⇒ G81`,
  exactly along the predicted trees (#81 needs only the retention
  clause; #80 also the ◯-clause for σ ∈ RefAt);
* 462-cell sweep vs two-sided ground truth (`wip/frjx_sweep_out.txt`):
  **ALARMS 0** (no hit on any of the 158 ⊢ cells), **297/303 refutable
  cells found** (was 62%); 6 residual misses at the capped budget
  (consequent ρ18 / antecedent ρ20 family) = the next residue shape;
* **ρ12 ⊢? ρ15, the ONE open cell of the matrix, got a HIT** (7.9 s,
  `wip/frjx_cell1215_out.txt`) — ENGINE-CLAIMED ONLY, certifies
  nothing; an independent G4c stage-3 probe (`wip/rho1215_probe.lean`)
  was left running for kernel confirmation.  Do NOT bank anything from
  this until a FinCM exists.

**Next session:** (1) outcome of the ρ12/ρ15 probe → bank or escalate;
(2) typed mechanisation of RefAt; (3) the 6-cell residue at uncapped
arity (profile-style engine for FRJX); (4) Frontier79 → theorems via
the #80/#81 template; (5) Matthew decides placement of the two proof
files (currently wip/; they import only FRJ.Sound + Search.Pin +
Certified.Register).

## 2026-08-19 — CORRECTION: the sixteen refutations were not new

`tools/rn-bank-gen.sh` reads `wip/rnDict.lean`, the ROUND-1 dictionary
(15 representatives).  I never checked for a later one.  There is one:
`wip/rnDict2.lean`, round 2, **16 representatives** (the 15 plus
`q15 = q9 ⊃ q4`, the single class the four §40 witnesses collapse to,
`wip/rnSep.lean`), and it is FULLY RESOLVED — 58 sorried cells, every
one REFUTED, none open.  Each has a sorry-free kernel-checked witness in
`wip/rnDictRefute2.lean` of the form

    refute_<cell> : ∀ k : Fin 16, ¬ Interd (combination) (rep2 k)

which is universally quantified over ALL representatives.  My
certificates only eliminate the one to three candidates that round 1's
candidate list named, so they are strictly weaker, and all sixteen of my
cells are already REFUTED in round 2.

Live figure: **the closure fails at 58 cells against 16
representatives.**  Not 4, not 13.  The §2026-08-18 entry below is
corrected accordingly; its engineering results stand, its mathematical
novelty does not.

The rule that was broken is the standing one: search the repo record
before treating a finding as new.  The process fix is in the plan —
one live dictionary, a version stamp on the generator, and refutation
statements quantified over the representative set rather than over a
candidate shortlist.

## 2026-08-18 — FRJ◯ search: the stack built end to end, and 15+ RN(◯,{}) cells refuted

Built the design of `docs/frjo-search-design.md` (§9 now records the
measured results).  Matthew's steer set the order: RN bridge first,
`PLLFormula` primary and FRJ's `Form` derived, "much more depends on the
original design than on the FRJ◯ one".

**`FRJ/Bridge.lean` (new).**  `ofPLL`/`toPLL` mutually inverse
(`[propext]`), and the forgetful `Kripke.toConstraint` with

    force_toConstraint : K.toConstraint.force w φ ↔ K.force w (ofPLL φ)

**axiom-free**.  Hence `not_entails_of_countermodel`: an FRJ(◯) model
refutes the ORIGINAL `LaxND` judgment, not a private copy of it.  When
the two syntaxes are merged, these lemmas become a renaming.

**The engine.**  `wip/frj_sat.lean` is FROZEN as the reference
implementation and differential oracle; it was ported verbatim into
`FRJ/Search/Engine.lean`.  `FRJ/Search/Fast.lean` is the fast engine.
Three exact optimisations, no change of semantics:

1. (J1) is a conjunction over ORDERED PAIRS, so admissible families are
   exactly the CLIQUES of `compatI` — `cliquesLe` prunes at every
   extension instead of filtering `C(|IS|, ≤jmax)` subsets;
2. `j1j2Check` runs once per promise family, not once per consumer;
3. given-clause incrementality — a round only forms joins touching a
   sequent new since the previous round.

Measured: **6× on the four known-false cells, 10.3× on the hardest
(164 s → 15.9 s)**.  Differential against the frozen reference over
every cell it completed: **77 cells / 154 goals, ZERO disagreements**,
cell-verdict and per-goal.

**The pinning path.**  `FRJ/Search/Pin.lean`: `Tab` (frame as boolean
tables), `okB` decidable, `toKripke`, and `minimise` — greedy world
deletion, root self-protecting.  Extracted models have 13 worlds;
minimised, **5 to 8**, which is what makes kernel `decide` affordable.

**The result.**  `wip/rnBank.lean` (generated from `wip/rnDict.lean` by
`tools/rn-bank-gen.sh`) carries all 323 dictionary cells tagged
proved/refuted/open.  Sweeping it with `lake exe rnfrj --engine=fast`:

* must-not-refute (236 certified `Interd` cells): **0 ENGINE-BUGs**;
* must-refute (4 cells known FALSE): **4/4**;
* **16 `open` cells REFUTED** — new mathematics, not a regression test.

All sixteen are kernel-checked in `wip/rnFRJCerts.lean`, sorry-free,
each `[propext, Quot.sound]` — no `Classical.choice`, no
`native_decide` — with a degeneracy control (the same model must still
force `q1 = ⊤`) per certificate.

These cells were open because the exhaustive ≤4-world battery cannot
reach a 5–8-world countermodel.  FRJ(◯)'s model size is bounded by the
derivation, not by an enumeration bound: that is "more efficient than
brute force" discharged on a workload where brute force had stopped.

IMPORTANT, and easy to get wrong: an open cell of `wip/rnDict.lean`
carries a CANDIDATE LIST and is sorried at the FIRST open candidate, so
a refutation eliminates one candidate and closes the cell only when that
candidate was the last.  I recorded this wrongly first (as nineteen
closure failures) and corrected it the same session.

`--cand=K` was therefore added to `lake exe rnfrj` and `lake exe rnpin`:
it retargets a cell at representative `qK` instead of the one the table
assigns, so the survivors can be attacked in turn.  Control: `--cand=1`
reproduces all eleven `q1` hits.  Walking the eleven narrowed cells
against `q11` and `q13`:

| cell | q1 | q11 | q13 | outcome |
|---|---|---|---|---|
| `cOr_10_12`  | ✗ | ✗ | ✗ | closure FAILS |
| `cOr_11_12`  | ✗ | ✗ | ✗ | closure FAILS |
| `cImp_12_11` | ✗ | ✗ | ✗ | closure FAILS |
| `cBox_11`    | ✗ | ✗ | ✗ | closure FAILS |
| `cOr_8_10` `cOr_8_11` `cOr_10_14` `cOr_11_14` | ✗ | survives | ✗ | {q11} |
| `cAnd_11_13` `cOr_8_12` | ✗ | ✗ | survives | {q13} |
| `cOr_8_14` | ✗ | survives | survives | {q11, q13} |

Every survival is at a FIXPOINT, not at a budget, so each is a settled
narrowing.  Each exhausted cell is one kernel-checked conjunction
`<cell>_no_candidate : ¬ Interd lhs q1 ∧ ¬ Interd lhs q11 ∧ ¬ Interd lhs
q13`.  ITS SCOPE IS EXACTLY THE THREE CANDIDATES NAMED — the other
twelve representatives were eliminated by the ≤4-world battery that
produced the candidate list, recorded in `wip/rnDict.lean`, not
re-proved.

**RUNNING TOTAL: the closure fails at THIRTEEN cells** — the four
already known, five sorried at their last candidate, four exhausted by
the `--cand` walk.  Seven cells are narrowed but still open.

The frontier is clear.  24 of the 67 open cells stopped at budget; the
first escalation guess (raise `jmax` to 4) was wrong and measurably so —
they had stopped at rounds 6-8 of 10 with |RS| ≤ 37, |IS| ≤ 86 against
caps of 800, so `lamCap` was binding.  At `lamCap=16` all 24 reach a
genuine fixpoint with zero new refutations (729 s).  No verdict on this
bank now rests on a budget.

WHAT IS NOT SHOWN: the engine is sound, not known complete.  A fixpoint
means no FRJ(◯) derivation within the relevance restriction — evidence
about a cell, not a proof of it.  Statement (A) remains OPEN and nothing
here bears on it.

Design doc comments A/B/C answered in place: §4.3 is now one FORWARD
layer (the backward-search proposal is retracted, with reasons); §5
records `circ_iff_nn` — on infallible `Rm = ≤` models `◯A ↔ ¬¬A`, so
that oracle class is a control, not a discriminator, and the open
region is `id ⊊ Rm ⊊ ≤`; §7 reordered so the RN ladder came first.

## 2026-08-18 — FRJ◯ as a countermodel SEARCH engine: review + design

`docs/frjo-search-design.md` (new, shareable).  Task: use the sound
FRJ◯ calculus as a fast countermodel finder, independently of the OPEN
completeness question — a derivation IS a countermodel (`Mod(D)`,
proved), so search is untrusted-but-safe.

Measured diagnosis: the regular state space of the worst corpus goal is
~5·10^3 sequents (|Ĝ| ≤ 8, |Sf^R| ≤ 14), yet `roundStep` considers
~5·10^6 join candidates per round at base budget (~4·10^8 at raised),
recomputed every round; the 37-cell corpus takes 87 s.  Three cost
centres: subset enumeration of join families (`famsUpTo`), no
incrementality, `List Form` contexts.

Design: bitmask zones indexed once per goal; **demand-driven join
construction** (repair (J1)/(J2) from an rhs-index instead of
enumerating families — the same reasoning `metR_prime` performs);
given-clause forward layer for the irregular cell library; goal-directed
`partial def refute?` with dominance memo + budget (partial is FORCED —
the demand cycle is the §9 measure dichotomy; safety comes from
returning typed derivations, as in `PLLG4Term.proveM`).  Test
scaffolding: four oracles (◯-free completeness; §15's
`completeness_of_rmFull_of_circFreeL`, which newly decides 21/32 corpus
cells; differential vs `PLLSearch.verdict`; model round-trip through
`FRJ/Extract` + `decide`), the retired CERTAIN vocabulary, and cap
reporting incl. `seedsIC`'s unreported 4-atom cap.

Nothing built yet; Matthew's call on whether to proceed and in what
order (milestones §7 of the doc).

## 2026-08-17 (engine-gap chip) — `dn_circ_and` false negative located and closed

The `frjsat` miss on the ◯-free erasure `¬¬(p∧q) ⊃ (p∧q)` was in the
`⊃∉` zone enumeration (`stepNotIn`): only `Θmax` and `Θmax` purged of
SINGLE generators of the antecedent were tried, so the jointly-generated
`A = p∧q` never got the zone `{q, ¬¬(p∧q)}` (= `Λ*` of the root) that
the PROVED construction uses.  Fixed by enumerating the ⊆-maximal
admissible zones from the `Cl` grammar (`thetaCandidates`); `⊃∉` is now
monotone in the context, so the RS-subsumption's documented exception is
gone.  Corpus: `dn_circ_and` → `transfer:pass` at both bounds ((E) attack
8/8); every other line byte-identical.  Record: `docs/frj-w4.md` §14
second addendum (the earlier hand-trace there was not a legal
derivation — (J1) fails; the real route and the method note are in the
addendum).  Untrusted-layer lesson: "engine-CERTAIN" is relative to
enumeration completeness, not only faithfulness.

## 2026-08-17 (erasure-transfer session) — the (E) build opened

Matthew redirected to the erasure-transfer lemma.  Landed, all green,
pins in Audit: FRJ/Erase.lean — `erase`/`noCirc`/`erase_hcf`;
`force_erase` (semantic half, axiom-FREE); `completeness_of_transparent_of_lift`
(conditional wiring); `force_circ_transparent`,
`circPart_lamStar_nil_of_transparent` (transparency kills the pledge
supply), `completeness_of_transparent_of_circSupply`; `clo_lift` + zone
shape helpers.  Engine attack on (E): 7/7 informative pass (four
classically-valid erasures, nested ◯◯); `dn_circ_and` exposed an ENGINE
gap (fixpoint-miss on a provably-derivable ◯-free goal — chip filed).
Key insight recorded in docs §14 addendum: the transfer recurses on the
erased derivation tree + decoration size, bypassing the §9 measure
dichotomy that still blocks every semantic route (even transparently).
NEXT: barren subfamily FRJbr/FRJbi + embedding (new file, safe);
Minimal retarget (type ascriptions; touches the proved file — surfaced
to Matthew before doing it); then the lift itself.

## 2026-08-17 — FRJ◯ completeness campaign: retrospective at stop

Goal (Stop-hook, now cleared): unconditional completeness (A).
**Not reached; the approach was not converging.**  State at close:

- PROVED (sorry-free, pins `[propext, Quot.sound]`, guards in
  `FRJ/Audit.lean`): `completeness_of_supply : PledgeSupply K G →
  CircSupply K G → ¬K.valid G → Provable G`;
  `provable_root_countermodel` ((B) forward, unconditional);
  `completeness_of_discrete`; `completeness_via_closure` (◯-free case).
- REFUTED: minMod as structural recursion (§9 measure dichotomy:
  Υ-edges force phase priority, ◯-body edges force size priority; the
  resolving order is model-dependent).
- OPEN: (A); both supply kernels — as STATEMENTS: neither proved nor
  extensionally attacked.

Non-convergence mechanism: four interface-refinement cycles (anchor-
local Λ* → OWit origin transport → θ-riding → origin-circ ground),
each dissolving its blocking instance and regenerating the same
residue shape — pledge components refuting the goal while Clo-covering
◯-bodies — one level up.  Theorem yield per window: large (org +
conditional theorem) → medium ((γ),(β1) removed side conditions) →
zero (interfaces and design notes only).

Worked: refute-before-build (§9 killed the literal plan before an
opaque proof-build failure); the conditional decomposition (the gap is
two precisely stated kernels, not "completeness is hard"); the corpus
attack (14 corner families, 28 pass / 5 control / 0 unresolved — the
END statement stayed credible throughout); choice-free Type-valued
builders (clean pins).

Failed (method): (1) the supplies never got the standing extensional
attack — each refinement introduced a new quantified statement that
went to another analysis window instead of a model search; (2) no
stop-rule on isomorphic residues — the second identical residue shape
should have triggered a change of tack, not cycles 3–4; (3) a goal
hook unreachable in-window drove grinding past diminishing returns.

If resumed: attack `PledgeSupply`/`CircSupply` extensionally FIRST
(harness exists: `wip/frj_sat.lean`); check the TOCL 2020 completeness
organisation at source (the saturation-closure organisation is OURS,
flagged per provenance discipline); only then decide build vs
re-statement.

## 2026-08-17 (continuation 3) — θ-riding dissolves the §13 impossibility

Antecedent discharges ride θ (fat zones, no hJ2), their Υ-obligations
met by axIC syntactically; the certified row's remaining semantic
question is the origin-Λ*-circ ground at promise joins (hbody one
level up).  (β2) design: bottom-up row construction with a θ-obligation
accumulator.  OWit interface landed previously; docs §13 addendum.

## 2026-08-17 (continuation 2) — BUILD (β1) LANDED: graded visit

FRWit + free threading + fallible joins (metR_primeF/metR_orF,
unconditional at circ-carrying worlds); SatStmt t=2; supR takes free
wits; free-◯ routes through certified.  All green, choice-free.
PledgeSupply now exercised only on certified chains.  NEXT ((β2)): the
transported-cov refinement — metI_circ needs only the DEMANDING
world's Λ* through the row; anchor-Λ*-cov is over-specification and
contains the one provably-unsatisfiable pledge instance (◯p ∈ Λ*_w at
body-p anchors); with transported cov the pledged retention ranges
over b-forced circs only.  docs §13.

## 2026-08-17 (close of window) — graded-demand refinement recorded

tOK is consumed ONLY by ◯-feeding demands: AllMet can be graded
(certified grade for minRef-anchors of ◯-demands; free grade elsewhere,
where fallible joins discharge circ-carrying worlds UNCONDITIONALLY).
PledgeSupply narrows to tOK-graded circ-carrying anchors.  Build order
for (β): graded split + fallible builders (mechanical), then the
sharpened pledge question, then CircSupply member-wise.  docs §12
addendum.

## 2026-08-17 (continuation) — BUILD (γ) LANDED: hloc eliminated

metR_primeP/metR_orP (promise joins pledging the goal; PledgeFam
against Λ* discharges hJ5/hJ7s/restrictP/restrictC) + visit branching
per world.  MAIN THEOREM NOW: completeness_of_supply : PledgeSupply →
CircSupply → ¬valid G → Provable G — statement (A) for EVERY model,
no hloc, choice-free, audit-guarded.  completeness_of_discrete
re-derived.  Remaining: build (β) = member-wise discharge of the two
supplies.  docs §12.

## 2026-08-17 (close) — promise-port design pinned

(γ)-design fixed by two proved constraints: Λ*-circ retention is
FORCED (unforced bodies can never ride Clo, barren joins have no
θ-circ zone), and prime promise-pledges must equal the goal (Covers at
prime = refl only).  So (γ) = promise branches of metR_prime/metR_or
taking a PledgeSupply input (component family for F over cone(a),
tOK-shaped, hJ5/hJ7s-satisfying); hloc is then replaced by
PledgeSupply, and full (A) = member-wise discharge of CircSupply +
PledgeSupply.  docs §11 fourth addendum.

## 2026-08-17 (late night) — kernel discharge routes at four; killer probe green

Stuck-member analysis: forced `a ⊮ W` + corner-shaped consequent; NEW
∃-ats Ax^I◯ route (decidable; blocked only by Λ* ⊨_cl Z′); the
all-routes-blocked configuration self-destructs semantically
(conjecture: kernel dischargeable member-wise everywhere).  Killer
probe corner_taut_body PASSES (28/5/0, thirteen corner cells).  Route
to unconditional (A): seen-mechanism + member-wise discharge + promise
port (docs §11 third addendum).

## 2026-08-17 (night) — residue probes green; seen-mechanism designed

corner_residue / corner_residue_poisoned / corner_selfloop all PASS
(27/5/0).  Self-loop reading: classForce(◯Z⊃Z) is a tautology, so the
Ax^I◯ zone always carries the self-loop imp.  The seen-mechanism
(visit parameter of in-flight ◯-bodies, measure (ht, |sfR|−|seen|, t,
|C|)) is designed in docs §11 second addendum — it reduces CircSupply
to the Z ∈ seen self-referential instance, to be discharged member-wise.
Next builds: seen-parameter implementation; promise-mode port for hloc.

## 2026-08-17 (evening) — kernel weakened + discharged in two regimes

`minRef` rewire: the visit floats the irregular ◯-demand to ANY proper
Z-refuter; `CircSupply` fires only at [every proper extension forces
Z].  Discharges PROVED: maximal worlds (`circWit_of_maximal`, via the
polarity-split classical correspondence `force_classForce`, pins
[propext]) and Clo-groundable rows (`metI_circ_syn`).  NEW UNCONDITIONAL
instance: `completeness_of_discrete` (statement (A) over discrete
models, full modal goals).  Remaining to full (A): non-maximal corner
residue + promise-join port for hloc.  docs §11 addendum.

## 2026-08-17 (later) — saturation-closure gluing LANDED

FRJ/Saturate.lean: the full §10 organisation is in, sorry-free,
choice-free, audit-guarded.  `completeness_of_supply` proves W4
statement (A) modulo two named conditions: `hloc` (world-wise circ-free
Λ*) and `CircSupply` (a tagged grounding Z-row at sole-minZeta-candidate
worlds — THE open kernel).  The builder layer is complete
(metI_*/metR_*), `visit` is total on (ht, t, |C|), and the ◯-free case
re-derives through the closure (`completeness_via_closure`).  Next:
discharge/weaken CircSupply; port promise joins to lift hloc.  docs
§11.

## 2026-08-17 — corner attack survived; (B)-soundness half landed modally

The §9 configuration was attacked with poisoned-vacZone cells
(A := p∨(p⊃q)); both derive (one needed jmax=4 — width cap, recorded).
Seven corner cells green, no completeness counterexample.  NEW theorem
`provable_root_countermodel` (Provable G → root-infallible countermodel,
no ◯-freeness), pinned [propext, Quot.sound], audit-guarded.  FRJ◯
completeness (A) remains OPEN; saturation-closure decomposition recorded
at docs/frj-w4.md §10.  Corpus 24/5/0.

## 2026-08-16 late — completeness obstruction pinned; OPEN, route redesigned

The §8 pledged-visit build hit a second obstruction: the irregular ◯-case
demands a same-world regular premise in the sole-minZeta-candidate
configuration, creating the call cycle I(◯Z) → R(Z) → I(Y ⊇ ◯Z) that no
lexicographic measure founds (docs/frj-w4.md §9). Both corner shapes
probe-PASS on the engine (peirce_compound, circ_ante_circ_goal), so this
is a proof-recipe failure, not a calculus gap. FRJ◯ completeness is OPEN;
recommended next design is saturation-closure completeness (induct on the
engine's round order, axIC seeds break the cycle at the base). All round-2
material remains green; corpus 19/5/0.

**Last updated:** 2026-08-25 by Fable 5 — §2026-08-25c: witnesses #80/#81 PROVED as incompleteness theorems, CompletenessFRJ refuted, RefAt repair validated (branch claude/frj-incompleteness-80-81-251e7f); earlier: merge of claude/frj-redevelopment-69005f (through §2026-08-25)
**Repo state:** `main` @ 925bc10 — `lake build` clean, every `#guard_msgs` audit green; no live feature branch (`ui-confluence` merged 2026-08-06)
**Deployed:** n/a (library). Merged: `main` @ PR #5 (the summit theorems). **PR #6 OPEN** (commentary + comment sweep) — awaiting Matthew's personal prose review; do not merge it yourself.

**Start here:**
* **`docs/calculus-map.md`** — the summary of results: which of the seven proof
  systems each result belongs to, what is proved about it, and whose it is
  (ours vs Fairtlough–Mendler 1997). Read it before asserting provenance.
* **`LaxLogic/LJFOAudit.lean`** — since 2026-08-13 the seven LJF◯ axiom pins
  live here and are NOT built by `lake build LaxLogic.LJFO`. Run
  `lake build LaxLogic.LJFOAudit` before any commit that changes a proof (§12).
* **`docs/next-session.md`** — the live threads as of 2026-08-07, one section
  each, with the next action and who decides. Read it before starting work.

## 1. What this project is (3 sentences max)

A Lean 4 mechanisation of Fairtlough–Mendler Propositional Lax Logic (I&C 1997): natural deduction (`LaxND`), an intrinsically-typed term calculus (`Tm`) with kernel-checked strong normalisation, a cut-free G3 sequent calculus (`SC`), a **machine-checked refutation of the completeness of Iemhoff's G4iLL** (`PLLG4Gap.lean`), and the repaired calculus **G4iLL″** proven complete with cut, contraction and weakening all admissible: `G4c = SC = LaxND = Tm` (`PLLG4HComp.lean`, audits pinned). The owner is Matthew Fairtlough, co-creator of PLL; he reviews prose personally and merges PRs (or explicitly authorises you to). Current targets: **decidability** (F&M Thm 2.8) via a termination discipline for G4iLL″, then **uniform interpolation** (open again — our refutation voided the published proof).

## 2. Current state

- **What works** (all kernel-checked, `#guard_msgs`-audited):
  - The gap: `PLLG4Gap.lean` — separating sequent SC-derivable / G4-refuted (`[propext]` only), two-copy variant axiom-free ⟹ contraction inadmissible. `PLLG4Tower.lean` — Howe's original sequent G4-underivable; naive tower needs only 2 copies.
  - The calculus: `PLLG4H.lean` (G4h/G4c, three retention repairs, height-indexed) with `toSC`, `ofG4p`.
  - The ladder: hp exchange/weakening (`PLLG4H`), master inversion + `impR_inv` (`PLLG4HInv`), `andR_inv` (`PLLG4HCut`), rule lifters + identity + MP (`PLLG4HAdm`), `weak_Imp` + `impLImp_dup` (`PLLG4HStr`), **contraction cut-free** (`PLLG4HCtr.G4c.contract`), `exfalso_adm` + `cut_atom` + **`cut`** + **`selfAbsorb`** (`PLLG4HCut`), **`completeness`** + `equiv_sc/nd/tm` (`PLLG4HComp`).
  - Side artifacts: `KleeneBrouwer.lean` (constructive KB well-foundedness, ZERO axioms), `PLLRun.lean` (normalizer demos, `pll_g4c` tactic — the earlier `pll_g4` was retired 2026-07-17: it ran the incomplete naive calculus under `native_decide`), `docs/annotated/` (infoview-snapshot proof readings), `docs/surveys/` (4 research briefings), `docs/commentary.md` (the human story, PR #6).
- **What is in progress:**
  - PR #6 review (Matthew).  Termination design: route sketched in `docs/g4p-ladder.md` final section + the memory file — set contexts (licensed by admissible contraction) + subformula closure ⟹ finite search space ⟹ history/loop-check termination.
  - Note to Iemhoff: not yet drafted.
- **What is broken / known-bad (cosmetic only):**
  - `PLLDecide.lean` / `PLLTopTop.lean` carry stale "chunk" labels; `PLLTopTop.lean:1191` has an unused-variable lint. Both flagged in PR #6, deliberately untouched.
  - `PLLG4.lean`'s "Howe smoke test" is a historically mis-bracketed sequent (docstring now explains; kept as archaeology).
  - `G4p ≟ G4c` equivalence unproven and retired (only `ofG4p` needed).

## 3. Verification commands (run these FIRST, before changing anything)

```bash
cd /Users/matthew/Lean/Sources/lax-logic-in-lean/.claude/worktrees/g4ill   # the working worktree
lake build            # expect: "Build completed successfully."; known cosmetic warnings in PLLSequent/PLLTopTop
lake env lean LaxLogic/PLLG4HComp.lean   # expect: silence — the summit audits are inside
```

- The `#guard_msgs` blocks ARE the golden tests: they pin decider verdicts (`PLLG4Gap`, `PLLG4Tower`) and axiom sets (`[propext, Classical.choice, Quot.sound]` for the summit; `[propext]` for the refutation; **no axioms** for `KleeneBrouwer.wellFounded_kb`). A guard failing means your change is wrong.
- Single-file iteration: `lake env lean LaxLogic/<file>.lean` (build dependencies first if oleans are missing: `lake build LaxLogic.<Dep>`).
- Git flow: work on `worktree-g4ill` (this worktree; the repo root checkout sits on `FablePLL`), push, `gh pr create --repo fairflow/lax-logic-in-lean --base main`; **Matthew merges** unless he says "accept pr". Never commit without a green compile of every touched file.

## 4. Decisions and rationale (DO NOT RE-LITIGATE)

| Decision | Rationale | Rejected alternatives and why |
|---|---|---|
| `SC` (G3, membership-keeping) is ground truth; everything is measured against it | Proven equivalent to `LaxND`/`Tm` (`cutElimination`, `curry_howard`) | Trusting G4iLL: refuted, kernel-checked |
| Three **retention** repairs (laxL keeps box; both `◯→` rules keep full first-premise context) | Each forced by a machine-found countermodel (rev 3: `j=id, φ:=p, ψ:=p∧q, E:=q`); they are what make contraction cut-free and `selfAbsorb` structural | "Optimising" premises back to consuming form re-opens the gap |
| Height index (`G4h n Γ C`) + Perm-hypothesis rule style + additive rules | hp-transports (perm/weaken/invert) are measure-invisible for the (weight, height-sum) inductions; exchange is one line per rule | Multiplicative contexts: pushes contraction into every case. `Prop`-only: cut's transports break |
| "Contraction-free" claims use the weak/strong distinction: G4iLL″ is a **localization** theorem (all needed contraction lives in the ◯-rules), NOT a refutation of strong Howe | Matthew's correction, 2026-07-09 evening — the retention rules absorb contraction | Claiming Howe refuted: wrong, the strong (reductive) form is open and *supported* by our evidence |
| UI waits on **termination**, not completeness (we have completeness) | Pitts's method needs both; Iemhoff had termination without completeness — we hold the dual | Running Pitts now: repeats her error shape. Trusting literature that "PLL-UI is settled": refuted here — correct any agent that reports it |

Longer log: `docs/g4p-ladder.md` is the design history (this repo's DECISIONS.md-equivalent — document reality, don't rename).

## 5. Invariants — things that must remain true

- **No `sorry` is ever committed.** No axioms beyond `[propext, Classical.choice, Quot.sound]` in the G4h tower; `PLLG4Gap`'s refutation stays `[propext]`-only; `KleeneBrouwer` stays axiom-free.
- `lake build` green (including every `#guard_msgs`) before every commit; guards are frozen — a failing guard indicts the change.
- `PLLTerms/PLLTopTop/PLLSequent/PLLNDCore` are **frozen** (proven, load-bearing): comment edits at most, recompile after.
- New G4h lemmas declare their height discipline: height-preserving (`G4h n → G4h n`) or bumping (`→ G4c`) — never hide a bump behind `Exists.imp`.
- The three lax rules keep their retention shapes exactly (see §4 row 2).
- Machine-check any claim adjacent to the Iemhoff refutation before writing it in prose.

## 6. Pitfalls already hit (don't rediscover these)

- **Symptom:** type mismatch `C✝`/`Γ✝` vs your named variable in `have`-ascriptions inside `induction` cases (bit us TWICE: 8 errors, then 4) → **Cause:** `induction` generalises the target's indices; the outer names go stale → **Fix:** bind case-locals in `@`-patterns (`E₀`, `Γ₀`) and ascribe with those.
- **Symptom:** rule lifter/`Exists.imp` won't typecheck across a height bump → **Cause:** `Exists.imp` maps same-index only → **Fix:** `obtain ⟨n, h⟩ := d; exact ⟨n+1, .rule …⟩`.
- **Symptom:** `induction d` fails "index is not a variable" (e.g. goal formula `falsePLL`, `A.somehow`) → **Fix:** the eq-trick (`G4h n Γ G → G = ◯A → …`); conversely `cases d` handles non-variable indices and auto-dismisses impossible constructors.
- **Symptom:** `injection e with e₁ e₂` errors "too many identifiers" → **Cause:** outer constructors CLASH (e.g. `and` vs `ifThen`), injection closes the goal itself → **Fix:** outer-clash `cases e`; same-outer `injection e with …` then `cases` the clashing component.
- **Symptom:** `omega` can't see weight facts → **Fix:** `simp only [PLLFormula.weight] at hA` first.
- **Symptom:** doc-comment before `#guard_msgs` → parse error → **Fix:** plain `--` comment there.
- **Symptom:** Edit tool refuses a file you created via heredoc → **Fix:** Read it once first.
- **Symptom:** a failing script step didn't stop the git commit after it → **Cause:** separate command lines don't short-circuit like `&&` → **Fix:** guard commits with `if lake env lean <file>; then git commit …; fi`.
- **Symptom:** your `git add -A` commits a background agent's half-written files (shared worktree) → **Fix:** `git status` before staging when agents run; scope the add.

## 7. Next actions (each sized for ONE session; tracker = THIS list — no beads; mirror to `gh issue` if a queue is wanted)

1. [x] **Termination A** — done 2026-07-10 (`PLLG4Space.lean`, PR #7).
2. [x] **Termination B** — done 2026-07-10 (`PLLG4Set.lean`, PR #7): fully *cumulative* set calculus (design refinement: nothing erased, `impLBot` vanishes, `weaken_subset` replaces all structural plumbing).
3. [x] **Termination C** — done 2026-07-10 (`PLLG4Dec.lean`, PR #7): fuel-structural visited-set search; `search_complete` via minimal heights + the visited-invariant; `instance decidablePLL : Decidable (Nonempty (Tm Γ φ))` — **F&M Thm 2.8 decidability, mechanised**. Note: `#eval` guards use tiny sequents (the gap sequent's space is astronomically large — the instance is total but exponential; fuel is computed arithmetically, never the powerset).
4. [ ] *(Fable session)* **Uniform interpolation**: Pitts `∃p/∀p` over the terminating search; adequacy from `completeness`. (Session task #9.)
5. [ ] **Multiplicity-3 hunt**: decider sweep for a sequent needing 3 copies (strong-Howe dichotomy); record either outcome in `PLLG4Tower.lean`. — *Done when:* a pinned witness or a documented negative sweep.
6. [ ] **Draft `docs/note-to-iemhoff.md`** from `docs/commentary.md` + `docs/g4ill-gap-review.md`: the gap, the repair, the offer. Matthew edits and sends personally. — *Done when:* draft committed; NOT sent.
7. [ ] **`TACTICS.md` + `LaxLogic/Tactics/`** per the handoff convention's Lean extra: package the recurring moves (perm plumbing `push2/pushL/rot3`, cross-splits, hp-transport idioms) with worked examples. — *Done when:* file exists, one tactic family extracted and used somewhere.
8. [ ] *(Matthew)* Review & merge PR #6.
9. [ ] **Mathlib PR prep**: `KleeneBrouwer` (zero-axiom) as the first candidate; check mathlib conventions, draft the PR. — *Done when:* branch ready for Matthew's go.
10. [ ] *(Fable sessions)* Session tasks #7 (Pfenning–Davies judgmental PLL) and #8 (G4iK□/G4iKD□ audit via the counterexample methodology).

## 8. Out of scope / deferred (so the model doesn't wander)

- Do NOT re-open the `G4p` ladder (superseded; only `ofG4p` matters) or refactor frozen proof files for style.
- Do NOT "fix" `PLLDecide.lean`'s semantics — it decides **G4-original** (the incomplete calculus), which is exactly its job in the refutation; it does NOT decide PLL.
- Do NOT claim strong Howe refuted, or that PLL-UI is settled (either way), anywhere.
- Do NOT contact Iemhoff or anyone externally; drafts only, Matthew sends.
- Multimodal lax logic (`◯₁ ⊔ ◯₂`, joins of nuclei at the term level) is the *successor project*, not this repo's scope.
- The zombie background-task chips in the session UI are harmless orphans; ignore or stop them, don't investigate.

## 9. Update — 2026-07-12: uniform interpolation paused

- **Stopped** (Matthew, budget): mechanising uniform interpolation for PLL over `G4c` is paused — not a dead end, see below.
- **State:** the whole development compiles down to one unproved lemma, `cascade_low_pos_box` (`wip/absorb_base.lean`) — the sole `sorry` anywhere in the UI work, and it concerns ◯-involving goals specifically; the ◯-free fragment is already unconditional, giving uniform interpolation for plain IPC with no gap.
- **Search:** three rounds of semantic countermodel search this week (`wip/refute3.lean`, `wip/refute4.lean`; the full 34-pair finite-algebra test collection, ~454 configurations at the lemma's own threshold) found zero counterexamples; current `∃p`/`∀p` definitions need no revision on present evidence.
- **Write-up:** `docs/ui-attempts-table.md` (this session) — plain-English attempt-by-attempt table for readers outside the project; `docs/iemhoff-note.md` (drafted in parallel) — the human-readable note on G4iLL's incompleteness and the two flaws located in Iemhoff's own printed uniform-interpolation proof (`wip/g4ill_ui.lean`).
- **Toolchain:** bumped to `leanprover/lean4:v4.31.0`.
- **Late addendum, same day:** `uniform_interpolation_IPC` landed sorry-free (box-free crown, pinned audit `[propext, Classical.choice, Quot.sound]`) — proved by an Opus agent from a mapped brief; the two missing facts and the method are recorded in `docs/opus-handover.md`, the handover strategical for delegated proof agents.

## 10. Update — 2026-08-07: uniform interpolation SHELVED; the threads are in `docs/next-session.md`

**Where the record is.** Two documents govern, and both are newer than
everything above:

| document | what it is |
|---|---|
| **`docs/calculus-map.md`** | **the summary of results** — the seven proof systems (`LaxND`, `SC`, `G3iLL`, `G4iLL`, `G4h`/`G4c`, `DerivU`, `DerivUNoFall`), what each is, what is proved about it here, what depends on it, and the provenance summary (ours vs F&M 1997). It ends with a "which system is a given result really about?" table. Written because the calculi had been confused in conversation more than once. |
| **`docs/next-session.md`** | **the live threads**, 2026-08-07: shelved UI and the confluent idea; the testing layer (frontier sampler, catpart, what is missing); the case study; the `omega`/`⊥` issue and the Zulip question; the belief paper; the Q○.K thread; the new RN(◯,{}) mathematics; the standing constraints. |

**State, superseding §2.** `main` @ 925bc10, `lake build` green. Sorries:
five in `LaxLogic/` (all in the semantic-UI extension line —
`PLLSemUIChar.lean:322,327`, `PLLSemUILayered.lean:827`,
`PLLSemUIHenkin.lean:341,352`), one that matters in `wip/`
(`cascade_boxgoal_pos`, `wip/absorb_base.lean:2281`), two routine ones in
`wip/G4conf.lean`. `uniform_interpolation_IPC` is sorry-free;
`uniform_interpolation_PLL` still carries `sorryAx`.

**The UI campaign's verdict (PROGRESS §§57–68, rounds 1–9).** The *room-free*
route is REFUTED, kernel-checked at `Γ = []`: `BoxDesc`, `CompProd` and
`GoalRowAbsorb` each fall, and `¬BoxDesc` is re-derived twice more through
rounds 7's and 8's own upgrade theorems. The refuted cell is strictly
sub-room, so the room-carrying `cascade_boxgoal_pos` survives — the room is
the sole countermodel excluder for the third time. §65 then proved that the
surviving statement's live regime is **not decide-feasible** wherever a
γ-clause is present, so it cannot be screened in either direction: it has to
be built. That is why the campaign is shelved rather than continued.

**Status of §7's list.** Items 1–3 done (2026-07-10). Item 4 (uniform
interpolation) — shelved, as above. Item 6 (note to Iemhoff) — drafted as
`docs/iemhoff-note.md`, still not sent, still Matthew's to send. Items 5, 7,
9, 10 untouched. Item 8 (PR #6) still Matthew's.

**Two new invariants for §5.** (i) A *false statement* compiles the whole
stack and passes every axiom pin, because it is a `sorry` — check statements
against the repo's own refutations before believing a clean build. (ii) A
clean screen is a statement about the screen: screen the **degenerate end** of
every axis first (round 9's fault needed empty context × untied fuel ×
missing frame simultaneously, and no sweep had ever emptied a context).


---

## 2026-08-17 — FRJ◯ (forward refutation with ◯): campaign PAUSED, retrospective

New since §10, all on branch `claude/frj-redevelopment-69005f` (NOT merged;
worktree hello-8a60f1): a mechanisation of Fiorentini–Ferrari FRJ(G)
(TOCL 21(3) 2020) extended to PLL's ◯.  The ◯-FREE completeness is PROVED
there (`FRJ/Minimal.lean`: `frj_iff_not_IPL` — `Provable G ↔ ¬ IPL G` for
circ-free `G`, the paper's Thm 6.2(i)+3.1).  The ◯-extension's completeness
campaign was paused 2026-08-17: the approach was not converging.

- PROVED (`FRJ/Saturate.lean`, pins `[propext, Quot.sound]`, guards in
  `FRJ/Audit.lean`): `completeness_of_supply : PledgeSupply K G →
  CircSupply K G → ¬K.valid G → Provable G` (conditional statement (A));
  `provable_root_countermodel` ((B) forward, unconditional);
  `completeness_of_discrete` (discrete models — these collapse to a single
  classical world, ◯ transparent, so this is only the classical shadow);
  `completeness_via_closure` (the ◯-free case re-derived through the new
  organisation — a consistency check, no new territory).
- REFUTED: the paper's triple-induction structure extended to ◯
  (`minMod`-as-recursion; measure dichotomy, branch `docs/frj-w4.md` §9).
- OPEN: unconditional (A); BOTH supply kernels as statements — never
  extensionally attacked (first move if resumed).  Candidate cheap
  extension: an erasure-transfer lemma for ◯-inessential countermodels
  (`Rm = id`), reducing that class to the proved ◯-free completeness.

Method lessons (banked in memory + branch HANDOFF): a lemma-statement
introduced by interface refinement owes the standing extensional attack
BEFORE the next analysis window; two isomorphic residues = change tack;
an in-window-unreachable goal hook drives grinding.

Full trail: branch HANDOFF.md (ten dated §§), branch `docs/frj-w4.md`
§§8–13, engine `wip/frj_sat.lean` (corpus 28 pass / 5 control-ok /
0 unresolved).

*[2026-08-25 note: the branch described above is now MERGED into this file — its full dated record follows below (§13 onward through §2026-08-25).]*

## 11. Update — 2026-08-11: the LJF◯ campaign and the review round

The LJF◯ route to UI for PLL (branch `ljf-pll`) reached: E1/A1 proved
outright and pinned; E2/A2 sorry-free conditional on the single typed
obligation `CimpAnt`; route-(B) infrastructure (heights, universes, the
decider round-trip, the fuel-founded `interpF`) green. Layer 4 is
PAUSED pending Matthew's decisions after the review round:
`docs/ljfo-review-2026-08-11.md` (efficiency scorecard, the
three-blocker comparison, the `CimpAnt` frontier attack, three proposed
simplification rounds). The live thread is `docs/next-session.md`;
the campaign dossier is `docs/ljfo-plan.md`. A repo `CLAUDE.md` now
exists (created in the review round) with the testing-for-counterexamples
doctrine.

## 12. Update — 2026-08-13: simplification rounds 2 and 3 CLOSED; the audit is now batched

Branch `ljf-pll`. Rounds 2 and 3 of the LJF◯ simplification are complete and
pushed; **layer 4 (the full-UI attempt) is still PAUSED and is the next
thread**, unchanged in scope. Nothing in this section touches a statement:
`satE2`, `satA2`, `CimpAnt`, `eSound`, `aSound` and all seven axiom pins keep
their exact statements throughout, and **UI for PLL remains OPEN**.

### What changed in the source

* **`LaxLogic/LJFORows.lean`** is now the single home of every station map
  and every aggregate equation, sitting between the frozen core and the tail
  (round 2 reversed batch 1's dependency, so `LaxLogic.LJFO` imports it):
  `eConjRows` (∃p), `truStationRows` (shifted goals), `laxRows = laxPrefix ++
  circStationRows` (◯-goal), the nine equations, the `rowMem`/`rowMemR`
  membership combinators, and `Saturated`. Each map used to be spelled out
  verbatim at every statement about it — six times, four times and seven
  times respectively.
* **The seven `interpA_circ*_eq` lemmas and `interpCircShape` are gone**,
  replaced by one `interp_circ_laxRows`; `UEntry`'s seven ◯-goal arms are one
  shape-generic clause; `UStab`'s seven `.laxOf` arms share one
  `laxRows_of_eq` opening. Superseded proofs in
  `Archive/ljfo-simp-round2-superseded.lean`.
* **`LaxLogic/LJFOCore.lean` was unfrozen twice, narrowly**: to delete the
  dead `(simp_arith; done)` alternative from both decreasing farms, and to
  move its five axiom pins out (below). No definition, rule or statement in
  that file has changed.
* **`LaxLogic/LJFOAudit.lean` is NEW and is the one thing to remember.**

### The audit is no longer in the build path — READ THIS BEFORE COMMITTING

All seven `#print axioms` pins now live in `LaxLogic/LJFOAudit.lean`, which
nothing imports. Matthew's direction, 2026-08-13: **by design this development
uses no `sorry` outside `wip/` unless Matthew authorises one**, so the pins
are a periodic check rather than a per-edit one.

A second reason was offered and then MEASURED AWAY, recorded here so nobody
re-derives it: the round-3 trace profile showed `#print axioms LJFO.satE2` at
~223 s of the tail's ~1160 s build, which looked like a fifth of the build in
audit cost.  It is not.  After the move the tail takes 27:50 against 26:03
with the pins in place — no saving — and `lake build LaxLogic.LJFOAudit`
completes in **1.8 s**.  The kernel check of `satE2` happens when
`LJFO.olean` is written; `#print axioms` merely awaited that asynchronous
task.  It is proof cost, not audit cost.  The good news is the other side of
the same measurement: **the full audit costs 1.8 s**, so there is never a
reason to skip it.

    lake build LaxLogic.LJFOAudit      # run before any commit that changes a proof

`lake build LaxLogic.LJFO` no longer re-checks the axiom profile of anything.
A regression introducing `sorryAx` into a pinned result will NOT be caught by
the default build. `collectAxioms` remains the only sound oracle;
`native_decide` taints and is not used here.

### What round 3 established about compile time — and what not to try

Three findings, all in `docs/ljfo-plan.md` items 9, 17–22:

1. **Source duplication and elaboration cost are independent here.** Round 2
   removed 341 built lines and left elaboration flat (1126 → 1163 s); round
   3's tru-side map was line-neutral and ~3 min slower. Naming a map adds a
   delta-unfolding step to many defeq checks. These refactors buy a single
   point of truth — keep them for that, and stop predicting speedups.
2. **There is no hot spot.** At a 250 ms threshold, three tactic nodes in the
   whole tail exceed it. The 811 s of `simp` is thousands of individually
   cheap calls inside `decreasing_by`.
3. **Do not trim the decreasing farms.** `(simp_arith; done)` was dead and is
   removed, but with no hot spot, trimming can only shave a fraction. The
   lever is the *goals*: eighteen mutually recursive functions over a
   lexicographic measure containing `3 ^ wNeg G` on large terms. Fewer
   functions in the mutual, or a cheaper measure, would move the needle.
   **Recommendation on record: stop the farm work.**

Instrument note: `-Dprofiler=true` gives per-COMMAND aggregates (one number
for the whole mega-mutual); `-Dtrace.profiler=true` nests by tactic
invocation and is the one to reach for. With tracing on the `#guard_msgs`
pins fail and `lean` exits 1 — trace text is appended to the compared
message. Artifact, not a broken tree.

### New documents

* **`docs/ljfo-fidelity.md`** — the calculus-fidelity table: per clause of
  `interp`, the move, the LJF◯ rule it answers, whether soundness and
  minimality run on raw rules or a named toolkit lemma, and whether
  Pitts/Dyckhoff make the corresponding move. §4 is the four forced
  departures from paper practice; §5 the PROVED/conditional/OPEN ledger. The
  correspondence column is expository, not machine-checked, and says so.
* **`docs/calculus-map.md` now has an LJF◯ entry**, with a warning that
  belongs on a provenance page: the θ-chain results (`thetaStabilises`,
  `thetaNotStrict`, the GZ-candidate cell) are **`LaxND`** statements about
  the *cell*, not LJF◯ results, and would stand unchanged if LJF◯ were
  abandoned.

### Two corrections made while writing those documents

Both were assertions I had made and then checked against the source:

* **`dykAnt` is not unconditional.** It is `dykAntC cAnt …`, inside the
  section parameterised by `variable (cAnt : CimpAnt p)`. `DykAnt` is not
  open, but it is discharged *relative to* `CimpAnt`, which remains the
  single open obligation of the development.
* **`LaxLogic/LJF.lean` is not a Liang–Miller port.** Its header records that
  it is built from its own rules, importing nothing, so that "the *technique*
  is what is under test". The focusing discipline is LJF-style; no metatheory
  is borrowed.

### Branch and worktree state

`origin/ljf-pll` carries this work. Another session is pushing PCLL documents
to the same branch (`docs/pcll-picll-arc-report.md`,
`docs/pcll-1pv-ui-plan.md`); two rebases were needed and there was no file
overlap either time — check before assuming a conflict is real. The
`ljf-pll` local ref is checked out in the
`discovery-toolkit-output-countermodels-a6efda` worktree and has been kept
fast-forwarded; it carries an untracked `wip/pcll1pv_stage0.lean` belonging
to that other session.

### Next

**Layer 4, unchanged**: the two lemmas over `interpF` — fuel-soundness
(`eSoundF`/`aSoundF`) and cofinal fuel-minimality (`satE2F`/`satA2F`) — which
together make, cell by cell, (the fuel chain stabilises) ⟺ (the cell's
uniform interpolant exists). Plus the two named adjuncts: normaliser
soundness and substitution admissibility. `docs/next-session.md` has the
resume brief; `docs/ljfo-fidelity.md` §3.2/§3.3 says which row families
`interpF` will grow, and round 3's lesson says to name them from the start.

---

## 13. Update — 2026-08-16: FRJ over IPC PROVED; FRJ◯ restarted from scratch on `frj-lax`

**FRJ(G) over IPC is PROVED**, sorry-free, on branch `frj-ipc` (tag
`frj-classical-complete`): soundness (Thm 3.1, via Lemma 3.4, `wf`,
Lemma 3.9, Thm 3.10) and completeness (§6: Λ*, Lemma 6.5, `minMod` =
Lemma 6.4, Thm 6.2(i)), giving
`frj_iff_not_IPL : Provable G ↔ ¬ IPL G`. Transcribed from the arXiv
LaTeX source of arXiv:1804.06689, with every divergence recorded in
`docs/frj-fidelity.md`. Two divergences are real: Lemma 6.5's stated
set equality is literally false (both directions actually used are true
and are proved), and the regular `C₁ ∧ C₂` case cites (IH2) where it
must be (IH3).

**Choice.** The `Classical.choice` in the development was never in the
mathematics. Two sources: Mathlib's `Finset` union/erase/image are
choice-tainted AT THE DEFINITION LEVEL (`Finset.instUnion`,
`Finset.erase`, `Finset.image`, `Multiset.ndunion`), so any term
mentioning them carries choice however proved — only `Finset.filter` is
clean, and the `List` API is axiom-free at definition level (avoid
`List.dedup`/`List.erase`, both classical); and the `tauto` tactic.
Branch `frj-choicefree` (`734d49a`) converts `Basic`, `Calculus`,
`Step`, `Model` to `List` and verifies the result — several theorems
depend on NO axioms at all, the rest on `[propext]` or
`[propext, Quot.sound]`. It does **not** build: `Extract.lean` has 16
errors and `Sound`/`Complete`/`Minimal` are unconverted. It is a
reference, not a base.

**FRJ◯ restarted.** `FRJO/` is abandoned: `ExtractForces` is REFUTED
for `worldOK` v3 by three kernel-checked cells (`4730e30`), the root
cause being that its rule table was formalised from the in-repo
paraphrase `docs/frj-lifting.md` rather than from the paper source.
Matthew's instruction (2026-08-16): start afresh in a new branch and
directory, import nothing from `FRJO/`, use the FRJ calculus, and make
it effective and choice-free, following PLL's slime-free inductive-type
templates. Branch **`frj-lax`** (cut from `frj-ipc`), directory
**`FRJLax/`**. The full brief is `docs/frj-lax-handoff.md`: the two
hard constraints (Type-valued and slime-free per
`LaxLogic/PLLNDCore.lean`; choice-free per the findings above), the
W0–W6 staging with exit criteria, the six observed failure modes, and
three decisions explicitly reserved for Matthew — the syntax staging,
the saturation half of the v4 zone repair, and every modal rule
statement.

## 14. Update — 2026-08-16 20:49 BST: FRJ◯ W0 and W1 done; the source is not the version we thought

Branch **`claude/frj-redevelopment-69005f`**, fast-forwarded from
`frj-lax` (`cc6ed4b`), tip `fa7348a`.  Three commits: the plan, the
fidelity renumbering, W1.

### The finding: the arXiv LaTeX source is not the journal version

`docs/frj-lax-handoff.md`, `docs/frj-fidelity.md` and `FRJ/Basic.lean` all
describe `frj-corr.tex` as "the full journal version".  It is not; it is a
close variant.  Both were read at source this session (the arXiv LaTeX in
full for §2, §3, §3.1, §3.2, §6 **and Appendix A**; the published ACM TOCL
21(3) text for §2, §3, §3.2, §6).  Inside the in-scope material the
journal

* adds **Lemma 3.9** — `⊢ Σ;Θ → C` implies `|H| < |C|` for every `H ∈ Σ` —
  whose proof **uses restriction (RS1)**;
* states the key soundness lemma's part (ii) with hypothesis `σ_p ⊩ Σ`
  along a new relation `⇢` (irregular chain entering a join), where the
  arXiv has `σ_p ⊩ Σ ∩ Sf⁻(C)` along `↦`;
* swaps (P2)/(P3), renames (PS1)–(PS4) to (RS1)–(RS4), names (J3)/(J4),
  and moves the height bounds to Theorem 6.1.

The arXiv form of (ii) is the **stronger** statement and needs no (RS)
restriction, so the plan cites journal numbering but proves the arXiv
form, and the rule table carries no minimality or maximality side
conditions.  Full account: `docs/frj-lax-plan.md` §1.

### The numbering was wrong in the record

`docs/frj-fidelity.md` cited five results by numbers that exist in neither
published version.  Matthew's call: renumbered throughout, with a dated
table under its Scope section.  `Lemma 3.4 → 3.5`, `Lemma 3.9 → 3.10`,
`Theorem 3.10 → 3.12`, `Lemma 6.4 → 6.3`, `Lemma 6.5 → 6.7`,
`Theorem 6.2(i) → 5.13(i)`, and the section references to the journal's
(its §3.1 is *Restrictions*, §3.2 *Countermodels and Soundness*, §3.3
*Termination*).  Only citations changed; no mathematics.  **Still
uncorrected**: `FRJ/Basic.lean`'s header repeats the false provenance
claim.

### W0 — the plan

`docs/frj-lax-plan.md`: what was read, the arXiv/journal divergence, the
three numbering systems, **every numbered result to be reproduced** with
its stage, the module plan with the slime-free constructor shapes written
out, the choice-free budget, the two screening rounds, the paper's own
worked formulas as a corpus, and the open decisions.

### W1 — done, builds, pinned

Decision 1 settled by Matthew: **`◯` and constraint models from line
one**, with `FinCM` as the eventual extraction target.

* `FRJLax/Core.lean`, **zero imports**: `Form` with `circ`, `size`, `Bool`
  shape predicates, `rm`/`cap` and the membership-equality relation `≐`
  that will keep the rule table free of green slime, `Sf`/`Sf⁻`,
  `Sf^L`/`Sf^R` with `SfClosed` proved of the computed sets, the zones,
  and `Cl` with (Cl2)–(Cl6).
* `FRJLax/Model.lean`: rooted, antisymmetric, constructively finite
  Fairtlough–Mendler constraint models; six forcing clauses;
  monotonicity; (Cl1); validity and countermodels.

Two results worth naming.  `force_of_fallible` — a fallible world forces
every formula — is the coherence check that makes the `◯`-free fragment of
this model class validate exactly IPC, since `full_F` is stated for atoms
only.  `decForce` — forcing is decidable, `◯`-clause included, **with no
axioms at all** — is what will let `Λ*_α` be an ordinary `List.filter` at
W4.

`Classical.choice` is absent throughout.  25 `#guard_msgs`-guarded axiom
pins live in the modules themselves, twelve of them "does not depend on
any axioms".  No `Finset` anywhere.  `lake build FRJLax` takes under two
seconds from clean.

### Recorded and deliberately not acted on

Two W5 findings, in `docs/frjlax-fidelity.md` divergences 4 and 5 and in
`FRJLax/Core.lean` under "The third zone":

1. `Cl` is transcribed **verbatim, with no `◯` clause**.  One is available
   and (Cl1) would survive it (`force_circ_of_force` is proved and used
   nowhere), but `Cl` occurs in the side conditions of `⊃∈` and `⊃∉`, so
   extending it changes the *rules*.
2. `◯` fits neither of FRJ's two context zones and is **not** absorbed by
   `Cl` the way `∧` and `∨` are: `◯A` can be forced at `α` without `A`
   being forced there, exactly as `A ⊃ B` can be forced without `B`.  So
   W5 is not "add a `◯` right-introduction rule": it is
   `Ĝ = Ĝ_at ∪ Ĝ_imp ∪ Ĝ_◯` with a three-zone join and an analogue of the
   support condition (J2).  `gCirc`, `circPart` and `isCirc` are defined
   and unused against that.

### Next

W2: the rule table, `◯`-free rules only, every return-type index a
variable.  Then round A of the screen — the three cells that killed
`FRJO/` v3 (`[⊥] ⇒ p`, `[p ∧ q] ⇒ p`, `[p, p ⊃ q] ⇒ q`) must be
underivable, and the paper's own valid `G = (p ∧ H) ⊃ (q₁ ∨ q₂)` with
`H = p ⊃ q₁ ∨ q₂` must not be refutable although an irregular sequent
carrying it is derivable — before any soundness proof is scoped.

## §2026-08-17 — FRJ◯: soundness landed; W4 (completeness) opened

Branch `claude/frj-redevelopment-69005f`.  The faithful FRJ
mechanisation (`FRJ/`, TOCL 21(3) 2020 read at source) now carries the
full modal extension with SOUNDNESS PROVED: `soundness : Provable G →
¬ PLL G` on `[propext, Quot.sound]` — the promise join (families of
regular premises become declared `Rm`-successors), the fallible join
(`⋈^⊥`, refutes `¬◯⊥` and `◯p ⊃ p` inside the calculus), and the
pledge `Tag` with `tag_cone`.  Records: `docs/frj-promise-join.md`,
`docs/frj-fidelity.md` (provenance map; the JLC 2021 S4 paper is
UNOBTAINABLE — decision 2026-08-17, every modal device is OURS),
`paper/frj-modal/` §9–§10.

W4 = completeness with modal goals, design in `docs/frj-w4.md`.  Done
today: the missing irregular rule `◯∉` (`FRJi.circNotIn` — repairs a
genuine W3 completeness gap; witness cell `provable_circ_peirce` for
`(◯p ⊃ q) ⊃ q`); the `⊩*`/`Λ*` modal clause with Lemma 6.5
(`mem_clo_lamStar`) generalised to the full signature (`hcf` DROPPED);
`circPart_lamStar_nil_of_maximal`; Screen 4 (`FRJ/Modal.lean`)
settling the pledge-float corner by anchor choice.  Next: (T2) the
forward-saturation engine + certified corpus, then the pledged `minMod`
visit.  `lake build FRJ` green, 8570 jobs, pins pass.

## §2026-08-17 (later) — FRJ◯ W4 (T2): the saturation engine, and a defect it caught

`wip/frj_sat.lean` / `lean_exe frjsat`: bounded forward saturation for
FRJ◯, DERIVATION-CARRYING (rows pack their own `FRJr`/`FRJi` terms, so
rule-faithfulness bugs are type errors and a hit inhabits `Provable G`).
Corpus run (verdicts from pinned repo results): 10 PLL-underivable
formulas PASS, 4 PLL-derivable controls saturate underived, and ONE
GENUINE FLAG — `¬¬◯⊥` is NOT derivable in the current calculus (engine
fixpoint at 7 rows + the cycle argument): `◯∉`'s zone is capped by
`Cl` of its premise context, which is empty in the atom-free signature,
while the realising world forces `¬◯⊥` vacuously — a `t=0 → t=1`
equal-height edge the paper's measure forbids.  Repair sketched
(`docs/frj-w4.md` §7): the modal irregular axiom `Ax^I◯` (prime seeds,
sound by the final-world cone), compound-body lifts, and a
join-variant-dependent `Υ`-restriction (fallible joins must not consume
`◯`-right premises).  `nn_circ_bot` stays a standing flag until the
repair turns it green.

## §2026-08-17 (evening) — FRJ◯ W4: the `Ax^I◯` repair LANDED; corpus fully green

The §7 flag is repaired.  New axiom (`FRJi.axIC`):

    Ax^I◯ :  ⊢  [] ; vacZone(F) → ◯F,    F prime, ◯F ∈ Sf^R(G)

`vacZone G F` = the classical theory, restricted to `Ĝ`, of the
`F`-refuting BARE final world (`classForce` = Boolean evaluation with
`◯`-clause `classForce (◯A) = classForce A`), and the axiom MOUNTS that
world into the extraction (`preI := PreModel.leaf (vacZone G F)`), so
every consuming join — fallible included — finds the `◯F`-refutation
witness above its root via `RootAbove`.  Soundness cases proved via
`leaf_force_iff` (single-world forcing IS `classForce`); the sketched
join-variant `Υ`-restriction was WRONG and is withdrawn in §7 (the
variance worry applies only to world-less designs).  Semantic reading
(Matthew): `◯⊥` is an honorary atom — `u ⊩ ◯⊥ iff ∀v≥u ∃f∈F, v Rm f` —
and the maximal infallible worlds split bare/`◯⊥`-false vs
decorated/`◯⊥`-true; `Ax^I◯` supplies the bare half of the seed
enumeration, the fallible join the decorated half.  Recorded in
`docs/frj-w4.md` §7.

Witness cell `provable_nn_circ_bot` / `not_PLL_nn_circ_bot_by_calculus`
pinned `[propext, Quot.sound]` (`FRJ/Fallible.lean`).  Engine seeds
`seedsIC` wired into `frjsat`; corpus run 3: **11 pass / 4 control-ok /
0 flags** (`nn_circ_bot` pass at rounds=3; `circ_peirce` one round
faster; controls hold).  `lake build FRJ` + `frjsat` green, pins pass.
Next (docs §5): item 6, the pledged `minMod` visit = completeness
proper.

## §2026-08-17 (night) — FRJ◯ calculus round 2 LANDED; completeness build in progress

Goal: `minMod` for the full modal signature = FRJ◯ completeness.  Probe
cells first (testing mandate) found TWO more calculus gaps, both
repaired, soundness re-proved, corpus 17 pass / 5 control-ok / 0 flags
(commits a70007e, 4e454a2): the modal joins `⋈^◯`/`⋈^◯,p` (◯-goals
concluded directly from irregular premises with `Z ∈ Υ` — `◯∈` cannot
reach `◯(A⊃B)`-refutations whose antecedent witness sits strictly above
the root; cell `circ_circ_imp`), and `Ax^I◯` generalised to arbitrary
`F` over arbitrary classical valuations (`¬¬◯◯⊥`; cell
`nn_circ_circ_bot`).  Support devices: the `Covers` chain-certificate
order replacing equality in every pledge comparison (sound via
`covers_refutes`), and (J7) turned into a `restrictP` filter on the
promise contexts (side condition now `hJ7s`, stable zones only).
Lemma 6.5 (`mem_clo_lamStar`) and `lamStar_mono` now take `¬Fal` at the
single world that needs it; `minZeta` (the `◯`-analogue of `minEta`)
added.  REMAINING: the pledged visit `minModP` + `minMod`'s modal cases
+ statements (A)/(B) — full blueprint and the ONE open corner (pledged
⊃-float onto a modally-loaded anchor; conjectured unrealisable, engine
is the arbiter) recorded in `docs/frj-w4.md` §8.

## §2026-08-24 — profile engine, ρ-certificates, the RNDB database, and the Deriv/Interd hoist

Branch `claude/frj-redevelopment-69005f`, at `3c1b616`.  Four days'
campaign, summarised for the next reader; every claim below is pushed and
pin-guarded.

**Engine.**  `FRJ/Profile.lean` (43 thms, sorry-free, choice-free) proves
the Profile Lemma: join conclusions and side conditions factor through
the aggregates (Σ, Θ, M, Υ), J1-extendability through (Σ, M) alone, the
promise side through (E, A).  `FRJ/Search/Profile.lean` implements the
profile-indexed search — one witness family per profile, NO arity caps —
alongside `Fast` and the frozen oracle, both untouched.  Differential
tests (`lake exe frjdiff`, with a G4c ground-truth column): zero
defects over 460+ goals, 13–28× faster, three countermodels `Fast`
misses.  `FRJ.Search.Stats` now records `jmaxBinding`/`pmaxBinding`;
the old `fixpoint` verdict (wrong on 119/119 measured negatives) is
deleted; `closed-no-cap-bound` is reported only when every cap is
observed slack.  Engine ranking is REGIME-DEPENDENT: LJF◯ wins on small
closed sequents, the G4c battery+search on larger ones (300–700× on the
frjhard ladder) — `tools/Engines.lean` records both measurements;
`enginecmp` (deferred, MUST REVISIT) is what keeps that from decaying
into folklore again.

**Refutation capability, measured.**  Against G4c ground truth on the
462 ρ-order cells: FRJ(◯) profile constructs countermodels for 62% of
the known-refutable cells; the misses are CONSEQUENT-shaped (five
disjunction/implication-over-modal-compound shapes are never refuted,
0/56).  79+ cap-free closures against certified countermodels stand as
incompleteness CANDIDATES for FRJ(◯) — they become witnesses only via
the FinCM → FRJ.Kripke link, which does not exist; Matthew's instruction
is to UNIFY the two model definitions, not bridge them (recorded in
`docs/frj-profile-search.md`).

**Certificates.**  `lake exe rhobank` swept all 462 cells and banked
every refutation found: `Certified/RhoRefutations.lean`, 185
kernel-checked certificates, all `[propext, Quot.sound]`, stated with
`⊬` — 137 confirm known-refutable cells, **48 settle cells the two-sided
ground truth left unknown**, zero conflicts.

**Database (layer 3).**  `RNDB/` — schema (`Types.lean`: Claim with
MANDATORY scope on negatives / Evidence / Entry with the un-sorriable
`ok` field / Frontier) plus 1,776 entries in six modules
(`allEntries_hold` pinned): ρ 185 + round-1 236 (the `rndSet` harvest) +
round-2 82 + rnFRJCerts 24 (the corpus is 24 countermodels backing 135
theorems, not "135 certificates") + derived 321 (symm closure + q15
trans triangle — first evidence-DAG edges) + escapes 928 (the 58
universal escapes DECOMPOSE into directional nle entries; no Rel
extension was needed).  Statuses live in data, `open` claims get no
declaration, duplicates across sources are corroboration (any future
dedup must COUNT sources, not drop them).

**The hoist and admissibility.**  `Deriv` (verbatim from
publication/core) and `Interd` (new, same pattern) are hoisted to
`LaxLogic/{Deriv,Interd}.lean`; `PLLSemUIFrag` imports them.
Consequence, verified by TWO independent measurements (mine and the
lax-logic-in-lean-3f session running core-audit's own rule sets over
this tree): `RNDB.EscEntries`'s closure is 29 modules, zero wip/, zero
PLLSemUI*, zero sorry, zero NUL, zero trimmed — **928 entries (52% of
the database) are admissible to publication/core's boundary today**.
Two documentation-check failures (`FormattingUtils`, `PLLFormula`
lacking module docstrings) are BRANCH ARTEFACTS: publication/core's
versions carry the docstrings; do NOT add them here — let that branch's
versions win at merge.

**Open, in Matthew's hands.**  (1) The publication/core branch strategy
— reconciliation cost now measured twice; remaining hoist surface is
ladder8/rnEmbed (mechanical), ljfo_link (mechanism-only Rewrite import
to confirm), rho_order/rnSep/rnSepColl (declaration-level, rnSepColl
last).  (2) FinCM/Kripke unification.  (3) The `tools/`–`Tools/` case
collision (gate: `sh tools/check-twins.sh`, section 4).  (4) H5 forward
(`◯((q8∧q11)⊃q13) ⊃ (q14∨q15)`) still unsettled at budget 2×10⁶.

## §2026-08-24b — the order view settled: ρ-catalogue PLL Hasse diagram complete (scoped)

* **Notation (Matthew):** strict order is `<`/`>` (scoped `LT PLLFormula`
  instance in `RNDB`); `≺/≻` removed (order-theory texts reserve `≺` for
  covering).  Covers: `a ⋖[S] b` scoped, converse `a ⋗[S] b`; bare
  `⋖`/`⋗` (`RNDB.Covers`, interval empty over ALL formulas) stated,
  uninhabited.  Symbols: ⋖ U+22D6, ⋗ U+22D7.
* **The two frontier cells were already settled — by lookup.**  The
  2026-08-15 record (`wip/rho_order_out.txt`, DerivU matrix) separates
  both on the confluent battery; `rhoorder pin` re-emitted the pin lines.
  One 5-world frame (`RNDB.sepM`) settles both at world 0:
  `rho12_nle_rho9 : [ρ12] ⊬ ρ9` and `rho13_nle_rho6 : [ρ13] ⊬ ρ6`
  (via `¬DerivU → ¬Deriv`).  Consequences, all kernel-checked
  `[propext, Quot.sound]`: `not_covers_rho6_rho12 : ¬(ρ6 ⋖[ρScope] ρ12)`
  (ρ9 interposes) and `rho6_lt_rho13` (hand term `nd_6_13`).  Banked as
  entries `ord-0001`/`ord-0002` (`Engine.finCM`); `DB.allEntries` now
  **1778**.
* **Item 2, the catalogue-wide cover sweep: `lake exe rhocover`**
  (`Tools/Cover.lean`).  PLL status per cell (battery separation ⊬;
  G4c oracle + LJF◯ ladder ≤48 ⊢), then every strict pair classified
  COVER / BLOCKED / OPEN with frontier emission; control = the ρ6/ρ12
  kernel theorem, run refuses a summary without it.  Result
  (`wip/rhocover_out.txt`): 462 cells = 158 ⊢, 302 ⊬, 2 open (exactly
  the standing flags ρ12⊢?ρ15, ρ20⊢?ρ10); 158 strict pairs; **37 cover
  edges, 121 blocked, 0 open** — the scoped Hasse diagram is COMPLETE,
  and the 37 edges agree 1:1 with `docs/rho-order.md`'s table.  The two
  flags touch no existing edge (opposite directions battery-settled);
  each could only ADD a strict pair if resolved ⊢.  `frontierOrder` now
  carries exactly those two `le` claims.  Diagram:
  `docs/rho-hasse-pll.svg`.
* **Raised-budget FRJ(◯)/LJF◯ runs on the two ex-frontier cells** were
  launched before the lookup landed; results go to the FRJ
  incompleteness file when they finish (a cap-free FRJ closure on these
  now-known-refutable cells = two new incompleteness candidates).

## §2026-08-25 — Hasse pipeline tool; ρ20⊬ρ10 flag resolved by lookup; FRJ incompleteness witnesses #80/#81; missing-class predictions

* **`tools/rho-hasse.sh`** = sweep → `wip/rhocover_out.txt` →
  `docs/rho-hasse-pll.svg`, fully data-driven (labels/★ emitted by the
  exe; the drawer refuses failed-control or incomplete runs).  Run it
  whenever the order data changes.
* **`rhocover` now overlays the DATABASE** before classifying: banked
  kernel entries beat engine verdicts; a conflict aborts.  First run
  caught `ρ20 ⊬ ρ10` (entry rho-0167, FRJ 8-world, kernel-pinned) —
  the two-sided record's "genuine flag" `ρ20 ⊢? ρ10` was ALREADY
  REFUTED; restated as `RNDB.rho20_nle_rho10`.  The whole 462-cell PLL
  matrix now has ONE open cell: `ρ12 ⊢? ρ15` (= `frontierOrder`, one
  claim).
* **Raised-budget FRJ(◯) on the two ex-frontier cells
  (`wip/frontier2_run.txt`)**: CLOSED-CAP-FREE in ~100 ms each (Profile
  engine, NO arity caps) on cells whose refutability is kernel-pinned →
  the first two FULL FRJ(◯)-incompleteness witnesses (#80, #81):
  kernel-certified `ρ12 ⊬ ρ9` / `ρ13 ⊬ ρ6`, saturation-certified
  FRJ-unreachable.  LJF◯ burned its 45-min cap on each proof side, as
  expected on refutable cells.
* **Structure of the diagram** (analysis, on-paper from settled cells):
  graded, rank profile 1-2-2-3-5-5-3-1; interval [ρ4, ρ18] is a PERFECT
  CUBE 2³ on atoms {ρ6, ρ7, ρ14}; the RN(p) ladder under p:=◯⊥ is the
  left rail (ρ13★ = rn₉); the dual upper cube over ρ9 on {ρ12, ρ18,
  ρ20} is missing its joins.  The 22 are NOT a lattice: the failures
  predict MISSING CLASSES, two of them unconditional and mutually
  distinct — class(ρ9∨ρ19) and class(ρ18∨ρ20) (disjunction property
  forbids ⊤) — plus candidates ρ10∧ρ20, ρ10∧ρ21, ρ12∨ρ18,
  ρ18∨ρ20∨ρ12, and flag-conditional ρ7∨ρ13, ρ12∧ρ15.  NEXT PROBE:
  order these candidate formulas against the 22 (two-sided machinery);
  each lands as a known class or a certified 23rd/24th class.
* **Pin gap for the incomparability claim**: 73 no-path pairs; 72 fully
  settled both directions (exception {ρ12,ρ15}: one open half); but
  only 187/303 ⊬ cells are kernel-pinned in-repo — the other 116 are
  battery separations with machine-emitted `by decide` pin lines not
  yet compiled.  NEXT: compile them (Certified/RhoSeparations.lean) and
  bank the entries; then the no-edge ⇒ both-⊬ reading is kernel-complete.
