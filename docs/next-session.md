# THE DICTIONARY MODULE (2026-08-20): `LaxLogic/RN/Reps.lean`

The fifteen RN(◯,{}) representatives now have ONE stable home outside
`wip/`.  Before this they were transcribed FIVE times — `wip/rho_order`,
`wip/rnDict`, `wip/rnBank`, `wip/closed_frag`, `wip/rnc_probe` — all in
agreement (verified by diff) with nothing enforcing it.

**The append-only rule: `qk` never changes meaning.**  New classes take
new indices at the end; a representative found to be wrong gets a NEW
index and the old one stays, deprecated in place.  That is what makes the
module safe under concurrent sessions: a certificate pinned against `q10`
cannot be invalidated by anyone else's append, and two sessions can
extend the dictionary at once without conflicting away from the tail.

**Not yet done, by Matthew's decision (land on this branch only):** the
five `wip/` copies are UNTOUCHED.  They should import `RNReps` and delete
their own definitions, but that touches files peer sessions are working
in, so it waits for him to merge and coordinate.

`lake exe frjcert` now imports only `FRJ.Search.Pin` and
`LaxLogic.RN.Reps` — nothing from `wip/` — and the generated certificates
do the same.


**Added 2026-08-17 — FRJ◯ thread (PAUSED).** Fiorentini–Ferrari FRJ(G) + ◯
on branch `claude/frj-redevelopment-69005f`: ◯-free completeness PROVED
(`FRJ/Minimal.lean`, `frj_iff_not_IPL`); the ◯-case paused at the
conditional `completeness_of_supply` — the two supply kernels are OPEN and
were never extensionally attacked.  See the final § of `HANDOFF.md`
(2026-08-17) and, on the branch, `docs/frj-w4.md`.  First moves if resumed:
extensional attack on the supply statements; the TOCL 2020 §6 organisation
read at source.

---

# PENDING (2026-08-20): the route-B derivation emitter

**Not implemented, by Matthew's decision on 2026-08-20 — do not build it
without asking him first.**

There are two extraction routes off one FRJ(◯) search.

* **Route A (fast, wired end to end).** `lake exe frjcert "<sequent>"`
  parses the sequent, searches, keeps `modR r.der`, minimises, writes a
  self-contained certificate plus a labelled SVG, and RUNS `lake env
  lean` on the certificate, reporting Lean's own exit code and
  `#print axioms` output.  The certificate is a finite `Search.Tab`,
  frame check and refutation by `decide`, consumed by
  `FRJ.not_entails_of_countermodel`.  It never mentions
  `FRJ.soundness`.

* **Route B (derivation-preserving, PARTIAL).** `lake exe frjderive
  <cell> <→|←> [rounds] [--tree]` keeps the ROW rather than the model.
  A row with `rhs = G` is a witness for

      Provable G := ∃ t Γ, Nonempty (FRJr G t Γ G)

  and `FrjDerive.provable_of_hitRow` proves exactly that
  (`[propext, Quot.sound]`).  `sizeR`/`sizeI` and `renderR`/`renderI`
  are structural — they recurse through the join constructors'
  `∀ j : Fin (n+1), FRJi …` premise families, so there is no fuel and
  no cap.  Measured on `cAnd_10_13←`: derivation size 25.

**What is missing** is only the last step: emitting the `FRJr` term as
Lean source so the kernel typechecks the DERIVATION and the refutation
goes through `FRJ.soundness` (via `not_derivable_of_provable` /
`not_entails_of_provable`, both already in `FRJ/Bridge.lean`) instead of
through the semantic bridge.  Feasibility was established before the
work was stopped:

* every side condition of every constructor is decidable — `isPrime`,
  `∈ sfR G`, (J1), (J2), `hcirc`, `hFnot`, `hC`, `hJ5`/`hJ7s` via
  `decClo`, `htag` via `decCovers`, `classForce`, and all the `Fin`
  quantifiers;
* the one exception is the context equation `Γ ≐ Δ := ∀ x, x ∈ Γ ↔ x ∈ Δ`,
  which quantifies over all of `Form` and is NOT `decide`-able — it
  discharges instead as `CtxEq.of_subset (by decide) (by decide)`
  (`FRJ/Basic.lean:1084`), since `⊆` on concrete lists is decidable;
* 25 nodes is small enough that source emission is economical.

The open design question is how to emit the join constructors' premise
families (`![…]` / `Fin.cons`, and whether the dependent motive is
inferred), which is why this wants a session rather than a patch.

**Separate idea, also Matthew's, also unbuilt:** the q-numbering of the
RN(◯,{}) representatives is arbitrary.  It would be better if the
subscripts were arithmetic — some index that computes rather than a
serial number assigned in discovery order.

---

# LIVE THREAD (2026-08-13): the DISPROOF investigation

**FRJ◯ (2026-08-17): PAUSED at `completeness_of_supply`** (conditional
completeness; (A) OPEN, minMod-as-recursion REFUTED, supplies
unattacked).  Retrospective in HANDOFF.md §2026-08-17.  Next two moves
if resumed: extensional attack on the supply statements; TOCL 2020
completeness organisation at source.

The live front is `docs/disproof-handoff.md` — a dedicated handover
for building a calculus in which non-provability is a POSITIVE
derivation (`Reject/`, after Fiorentini-Ferrari's FRJ(G)).  Next task
is T1, the JOIN rule.

**The UI campaign is PARKED** by Matthew's decision (2026-08-13): no
UI work until the disproof side has more machinery and results.  Its
state is below and in `docs/pcll-1pv-ui-plan.md`; note that the
closed-fragment probe REFUTED `ClosedCollapse`, so stage 2's kernels
(`StableCore`, `CornerCoreW`) are OPEN again and the live repair is
level re-founding on promise-depth.

---

# Note for the next session — the live thread

*Trimmed 2026-08-11 at Matthew's direction. The previous full note
(2026-08-07, covering the shelved semantic/G4c routes, the case study,
the RN(◯,{}) results and the ranked tidy-list) is archived verbatim at
`docs/archive/next-session-2026-08-07-full.md`; git history holds every
revision. `HANDOFF.md` (repo root) is the standing handover;
`docs/calculus-map.md` is **the** summary of results — read it before
asserting provenance about anything.*

---

## Operational constraints (carried over — do not rediscover)

* **Delivery.** Matthew cannot open paths into a worktree, and often not
  into the repo either, from the session UI. Static documents → publish
  as an Artifact and give the URL. Dynamic HTML → a shell command
  (`open <path>`) or a local server; artifact links do not work for
  those. Short content → inline it in full.
* **The machine-checked mandate.** Every theoretical claim that will
  stand in a paper must be Lean-checked, sorry-free, with a pinned
  `#print axioms`. Anything else is OPEN or a conjecture, labelled so.
* **Never remove a worktree to tidy up** (vetoed 2026-07-20 — it kills
  live agent sessions).
* **Browser**: the Claude-desktop browser tools time out here. Use
  claude-in-chrome (Comet), which rewrites `file://`; serve local pages
  with `python3 -m http.server`.
* **Delegation**: file-editing subagents must run with
  `isolation: worktree`; subagents do not commit or push — the
  coordinator integrates.
* **Search memory before treating a project-history finding as new.**
  The recurring failure is not forgetting but re-deriving without
  checking.
* **Testing before proving**: see `CLAUDE.md` §Testing for
  counterexamples (added 2026-08-11) — statement failures are a testing
  problem; frontier/boundary/corpus discipline runs before any proof
  build is scoped.

---

## LJF◯ / PLL-UI thread (2026-08-11, branch `ljf-pll`) — THE LIVE THREAD

*Full dossier: `docs/ljfo-plan.md` (read its 2026-08-10/11 sections top
to bottom); memory note `ljfo-cimpant-terminus` guards against
re-derivation of the exhausted miner designs.*

**Standing results (all pinned, green commits on `ljf-pll`):**

* `LaxLogic/LJFOCore.lean` (frozen, zero imports): the lax-flagged
  focused calculus, the box-wrapped modal `interp` with the uniformised
  antecedent `A(rest ⇒ ↑↓◯Q′)`, termination, `interp_pfree`,
  **E1 (`eSound`) and A1 (`aSound`) proved outright**, the G4iLL-blocker
  standing test, five axiom pins.
* `LaxLogic/LJFORows.lean` (imports only the core, since round 2 batch 2):
  the station maps named once — `eConjRows` (the `∃p` conjunct rows),
  `laxRows = laxPrefix ++ circStationRows` (the ◯-goal rows) — with the two
  aggregate equations `interpE_eq` and `interp_circ_laxRows`, the five
  `*ConjMem` projections, and the `rowMem`/`rowMemR` membership
  combinators.
* `LaxLogic/LJFO.lean` (imports the core through `LJFORows`): the complete
  minimality development — **E2/A2 (`satE2`/`satA2`) sorry-free and
  machine-checked, conditional on the single isolated typed obligation
  `CimpAnt`** (the modal antecedent miner, staged exactly as `DykAnt`
  was).
* `wip/ljfo_eval.lean`: the calibrated evaluator bank (certificate
  engines; reproduces forced change #3 as a certified failure).
  `wip/ljfo_attack.lean` (2026-08-11): the frontier attack on `CimpAnt`
  — corpus replay, crossed-χ strata, boundary cells.
* Route (B) infrastructure, direction-neutral, all green:
  `LJFOHeight.lean` (height-indexed judgments + equivalence),
  `LJFOUniverse.lean` (subformula closures, transitivity, `uClosed_ctx`),
  `LJFOSearch.lean` (the decider round-trip: derivable ⟺ searchable at
  existential fuel, `search_sound` rebuilding kernel derivations),
  `LJFOFuel.lean` (`interpF`, the fuel-founded retention interpolant —
  see the resume brief below).

**The one open point:** `CimpAnt`'s discharge fails for every
consumed-implication architecture at χ-uses inside crossed-station
material (Howe's ①/② duplication). The repair is the `L◯→″` retention
discipline, whose termination the commentary records as absent (not
DM-decreasing); options (A′) Bílková-style order / (B) the
finite-space/fuel discipline / (C) stand conditional are costed in the
plan. Matthew directed (B); its infrastructure is banked through the
decider round-trip and `interpF`.

**Claim discipline:** UI for PLL remains OPEN. Nothing in this thread
claims otherwise; every result stands exactly as strong as its pin.

### THE FRESH SESSION'S GOAL: the full-UI attempt (layer 4)

*Everything in this session after the marathon — the review, the
frontier attack, the kernel escalations, the stabilisation probe, the
simplification rounds, the two background attacks on the candidate
cell — is PREPARATION.  The fresh session attempts full UI.*

**Its first target, valuable whichever way the answer goes:** the two
layer-4 lemmas over `interpF` — fuel-soundness (`eSoundF`/`aSoundF`)
and cofinal fuel-minimality (`satE2F`/`satA2F`, whose retention guard
makes the modal miner a native `UEntry` call).  Together they make,
cell by cell: (the fuel chain stabilises) ⟺ (the cell's uniform
interpolant exists) — the machine-checkable form of the campaign core
W (see the plan's "core extracted" section AND its correction: the
1-pv scope of the old routes' blockers, the withdrawn union claim).
Then: prove stabilisation (pigeonhole over the finite sequent space
bounds heights, hence fuel) ⟹ UI for LJF◯.  **The candidate cell is
RESOLVED (2026-08-11, both agents, convergent): NOT a GZ witness —
the chain stabilises at f = 6 with limit θmax = ((◯⊥⊃r) ∧ ◯q) ⊃ ◯⊥ =
the station's ⊥-instance ⊃ ◯⊥; W held.**  See the plan's two
resolution sections: the θ_k family (kernel-pinned fixpoint), the
⊥-instance maximality mechanism, the double filter for any next GZ
candidate (crank without X-free disjunct AND goal not settled by ◯⊥),
and the two named adjunct lemmas (normaliser soundness; substitution
admissibility).  Stabilisation testing must be logical, not syntactic.

Alternative preparation routes Matthew has named (plan, same section):
1-pv restriction of `CimpAnt`; PCLL (◯ distributes over ∨); both;
the bi-lax unification thread.

### Layer 4 resume brief (2026-08-11 03:20; status updated after the review round)

**STATUS 2026-08-11 (updated after the review round): layer 4 is
PAUSED; the simplification rounds are RUNNING at Matthew's direction**
(`docs/ljfo-review-2026-08-11.md` holds the full review). The frontier
attack on `CimpAnt` concluded with zero certified failures; both
engine-unreachable survivors settled TRUE at kernel level via
`LJFOSearch.search` (fuels 32/48), including the φ★ cross-route check
against the proved `∃p.φ★ = ¬¬◯⊥`. The focused kernel search is the
escalation engine of record; the `bchi` screening-horizon stations are
its named next stratum. **Round 3 is DONE too (2026-08-12)**: the tail's
1163 s is **68 % `simp` inside `decreasing_by`** (not the WF packing, not
the aggregate `rfl` checks); the farms have no duplicate alternatives but
`(simp_arith; done)` is dead in both and is removed; the tru-side station
map is named (`truStationRows`) and all nine aggregate equations now live
in `LJFORows.lean`; `docs/ljfo-fidelity.md` is the calculus-fidelity table.
Further farm trimming needs batched delete-and-build probes at ~30 min a
bit. Simp round 1 (support modules) is logged in
the plan; **round 2 (the `laxRows` collapse + the merged LJFO.lean
dedup) is DONE, both batches, 2026-08-12** — the tail is 2726 → 2202
lines (2807 → 2466 built, −12.1 %) with every statement and axiom pin
unchanged, but **elaboration time is FLAT: 1126 s → 1163 s like-for-like,
so the design pin's "beat 1773 s" was not met** and no speedup should be
quoted for it (plan, "Simp round 2" — the seven `rfl`s survive as the
seven branches of one lemma; only the restatement went). Round 3 =
farms/profiling/fidelity table, NOT started; the timing attribution is
its job. Resume layer 4 after the rounds, on Matthew's go.

The layer-4 foundation, in place and green:

* `LaxLogic/LJFOFuel.lean` — `interpF`, the fuel-founded RETENTION
  interpolant: `interp` mirrored clause for clause on structural fuel,
  the modal rows carrying the (b)-guard `A(done ⇒ ↑↓◯Q′)` at the FULL
  station (12 sites), sound defaults at fuel 0 (⊤/⊥). Compiled first
  build. Retention dissolves the crossed-station obstruction: χ is a
  member of every station the mining visits, so `CimpAnt`'s analogue is
  a native `UEntry`-style call — no χ-class, no descent machinery.
* The decider round-trip (`LJFOSearch.lean`): derivable ⟺ searchable at
  existential fuel — heights are available for every derivation via
  `toH`.
* First step when resumed: run the `interpF` evaluator cells
  (`wip/ljfo_eval.lean`, tail section — fuel0 lowered to 6 after the
  fuel-24 values ground the bounded prover; the `howeCell` family
  targets the ①/② configuration directly). If green, build the
  parallel fuel-founded tail: `eSoundF`/`aSoundF`, the minimality
  family, the native miner, unconditional `satE2F`/`satA2F`, pins.
  Fuel-sufficiency/stabilisation is the one open design point — decide
  whether the UI statements quantify fuel existentially (heights via
  `toH`) or need the pigeonhole-computable bound.

**Note on what layer 4 changes and does not change** (recorded after
Matthew's 2026-08-11 question): the CALCULUS is untouched — LJF◯'s
rules are exactly those frozen in `LJFOCore.lean`, and the
height-indexed presentation is proved equivalent (`toH`/`ofH`). What
layer 4 introduces is a SECOND interpolant definition, `interpF`
(retention rows, fuel-founded), for which all four UI statements would
be proved afresh; the existing `interp` results stand unchanged
alongside. The UI theorem is an existence statement, so which
interpolant witnesses it is strategy, not content.


## 2026-08-24 refresh (see HANDOFF.md §2026-08-24 for the full state)

Live threads, in order: (1) Matthew's publication/core branch decision —
all measurements in; (2) migrate the incompleteness candidates into
`RNDB` as `Frontier` members and wire the miner; (3) `PartialRNDict` as
a computed view + the order DAG (store `<`, covers only relative to a
named set); (4) prove the second Profile-Lemma engine against
`wip/frj_sat.lean` row-for-row if the profile engine is to REPLACE Fast
rather than sit beside it; (5) `enginecmp` — deferred, must revisit.

## QUEUED (2026-08-26, Matthew): certificate-passing for the proof side — after the RCells campaign

Replace fueled kernel re-search with tree-checking, mirroring what the
refutation side already has (`Reject.certifies` needs no fuel):

1. A concrete derivation-tree datatype for LJF◯ (the rule table already
   exists — `LSeq.search_sound` rebuilds derivations from search wins).
2. `partial def emitTree` — the emitter runs COMPILED and is UNTRUSTED:
   no termination proof, no correctness proof.  It does not have to be
   proven correct, because nothing rests on it (G4c fix pattern).
3. `checkDeriv : Tree → LSeq → Bool` — structural, fuel-free — plus the
   ONE soundness theorem `provable_of_checkDeriv : checkDeriv t s = true
   → provable s`.  Built once; works in every later campaign.
4. Campaign theorems become `laxND_of_checkDeriv (by decide)` on a tree
   literal: `decide` cost linear in tree size, fuel eliminated from the
   statement entirely, no failing-branch blowup anywhere.

Rationale (Matthew): unnecessary fuel is what hurt G4c search; the
fueled `decide` gate in the current RCells campaign is fail-closed and
minimal-fuel-metered, so it is safe — but the tree route removes the
fuel question permanently for the one-time price of a checker soundness
proof.

## CAMPAIGN (2026-08-26, Matthew): FRJV completeness via model-to-tree

The architecture, agreed without further spelling out:

    [] ⊬ φ  ⟹  Built-class TREE countermodel   (not_laxND_iff_built;
                                                the G4c/classical side)
            ⟹  FRJVr derivation of ofPLL φ     (THE NEW LEMMA: the hand
                                                recipe as a recursion
                                                over the tree)
            ⟹  ProvableV (ofPLL φ)             — completeness of FRJV.

The new lemma formalises METHOD.md Appendix A: structural recursion
over the finite tree model, one world per join, with two sub-lemmas
carrying the content: (i) kept-link adoptability = RefAt-vs-truth
alignment at each world (which implications true at a world are
KeptChain-adoptable); (ii) premise-row existence for every cone-false
formula (the induction hypothesis).  This is the W4 progress lemma in
semantic clothing.  Interactive skill base: the five hand witnesses +
`wip/frjv_interactive_114.lean` (goal-first, rules-only, trace_state
proofviews; the ProvableV metavariable pattern solves the context by
unification).  Next skill step before scoping the recursion: run the
interactive construction on 3–5 more banked ⊬ cells of DIFFERENT
shapes (a promise-join cell, an axIC/vacuous cell, a 2-premise orI
cell) to force the remaining rule families through the same discipline.

UPDATE (same date, Matthew's question answered YES): the completeness
recursion should consume `Reject/`'s Built-class trees (`Tab`), not the
general `Kripke` structure — they are concrete inductive data the
calculus side already constructs and checks, `not_laxND_iff_built`
guarantees one for every underivable sequent, and tree shape is what
world-per-join transcription wants.  Caveat carried: that existence
theorem uses Classical.choice, so the composed completeness statement is
Prop-level; the recursion itself stays constructive over the tree.

TACTIC KIT (from the interactive corpus): `frjv_side`
(wip/frjv_interactive_94.lean) — eight closed moves covering every side
condition in all seven witnesses; a rule application is
`refine Rule (…premises…) <;> all_goals frjv_side`, one line per node.
Second exercise file covers the remaining rule families: joinOrP
(promise) and axIC (vacuous cone), first-pass.  For the GENERAL lemma
the decide arms die (side conditions no longer closed) — but each arm
names exactly one helper obligation of the recursion: keptOf_ok and
CtxEq.refl are already generic; zoneSplit generalises with one
membership lemma; hJ2/hJ5's Boolean checks become carried invariants of
the tree; `cloB_iff.mp ∘ decide` becomes the truth-vs-Clo alignment
lemma.  The witness corpus's decide-sites are a SPECIFICATION of the
completeness proof's helper list.

CORRECTIONS (Matthew, 2026-08-26 evening):
1. The countermodel-existence side can be CHOICE-FREE: the G4c
   decidability/completeness chain ([propext, Quot.sound], the
   axiom-hygiene campaign's result) constructs a finite countermodel on
   the refutation branch.  So the source-model class is a DESIGN CHOICE
   with three candidates, none yet committed: (a) the G4c decider's
   finite models (choice-free, but not tree-shaped); (b) Reject/ Built
   trees (tree-shaped, matching the recipe, but existence via choice,
   and Matthew doubts the simple constructions match FRJV); (c) FRJV's
   own modR-image class (self-normal-form).  Pick whichever makes the
   two sub-lemmas provable; that pick is the first task of the campaign.
2. NON-DETERMINISM CONCERN (Matthew): FRJV may be too non-deterministic
   for a completeness recursion.  Assessment from the hand corpus: the
   saturation engine is already the canonical deterministic strategy
   (maximal Θ, full row closure — the hand witnesses' choices were
   shortcuts through that space, not essential creativity), so the
   determinism question reduces to the W4 AllMet progress question.
   The two REAL risks, both measured: join ARITY growth (jmax 3→4
   needed on six cells; unbounded arity kills any bounded-family
   recursion — the syntactic none_ex question), and the UN-REPAIRED
   PROMISE JOINS (paper-strict; the hand work needed the Υ-enrichment
   trick exactly to get hypotheses through the promise restriction — a
   completeness proof must show the trick always suffices, and if it
   does not, the next refinement cycle relaxes the promise joins as
   RefAt relaxed the barren ones).
3. PARKING CRITERION (Matthew's decision rule): if neither this
   semantic route nor the peer session's W4 route succeeds, FRJV is
   PARKED as an instructive failed extension of Fiorentini–Ferrari's
   IPC refutation calculus to PLL — keeping soundnessV, the ρ12⊬ρ15
   settlement, the witness corpus, and the method lessons.

STEP 0 (Matthew, 2026-08-26 late): before attempting the FRJV
completeness recursion, RUN THE METHOD ON THE ◯-FREE FRAGMENT — FRJV
restricted to ◯-free goals is essentially Fiorentini–Ferrari's FRJ(G),
whose IPC completeness is PROVED on paper (TOCL 2020).  So the fragment
is a CONTROL with a known answer: if the method fails there, the fault
is our formalisation or the method's Lean shape, not the calculus — and
it certainly fails for full FRJV (the fragment's rules are a subset in
action).  If it succeeds, the entire risk mass is isolated in the
◯-delta: the promise joins and join arity.  The paper's own
completeness proof is the scaffold for the recursion's shape.

FAMILY COVERAGE COMPLETE (interactive III, wip/frjv_interactive_92_90.lean):
[ρ9]⊬ρ2 forces joinCircP and [ρ9]⊬ρ0 forces joinAtP (the final ⊃∈
needs b in context; only the promise formers carry a ◯-formula; the
conclusions rule out joinOrP).  Both four-node trees, first-pass, via
the hoisted kit.  Every join family of FRJV has now been driven
goal-first at least once.  KIT HOISTED: FRJ/WitnessKit.lean (generic
helpers + frjv_side), answering the review point that the helpers were
stranded in WitnessV1215's namespace.

ROUND 1 OF THE ◯-DELTA LANDED (2026-08-26 22:02): `wip/minmodv.lean`
extends `minMod` past `.circ` on the template (Matthew's method
directive: existing proofs as firm templates, never a fresh strategy —
now also a section of the calculus-adoption skill).  `minModV` +
`completenessV_of_supply` compile FIRST PASS, pins
`[propext, Quot.sound]` guarded.  Hypotheses of round 1: `hloc`
(world-wise circ-free Λ*), global infallibility, and `CircSupplyV`
(the §9 sole-candidate corner as a named supply).  Regular `◯`-goals
need no float (Rm reflexivity); irregular `◯`-demands float on height
or hit the supply.  Smoke test `wip/minmodv_test.lean`: Peirce cell
end-to-end on `Kripke.point`, supply discharged by `Ax^I◯`.  NEXT:
(1) discharge `CircSupplyV` (four W4 §11 routes + the NEW V-lever —
kept chains turn stuck-member retention into decidable `RefAt`);
(2) lift `hloc` = promise-join port with `PledgeSupplyV`;
(3) `hinf` → root-only infallibility (per-wit `wfal`).  Parking
criterion unchanged: if neither this nor the peer W4 route closes,
FRJV parks as an instructive failure.

ROUND 2 DONE (2026-08-26 22:12): `CircSupplyV` DISCHARGED on
cone-grounded frames (`circSupplyV_of_coneGrounded`: corner →
cone-trivial → maximal → generalised `Ax^I◯`, embedded by `toVi`), and
`completenessV_of_endpoints` gives FRJV completeness UNCONDITIONAL over
endpoint-seeing models (no hloc/inf/supply) by composing the peer's
`completeness_of_endpoints` with the embedding.  Chosen-valuation route
landed as `circWitV_of_ats` (decidable per world; blocked exactly on
`Λ*_a ⊨_cl Z`).  Peer refutation absorbed: no supply-form organisation
of the promise side is possible (`V.PledgeSupply` FALSE; kept members
are implications only) — the corner supply is unaffected (its world is
provably circ-free).  REMAINING FRONTIER: (a) non-endpoint frames —
where #80/#81 live and FRJV must exceed FRJ; the open kernel is the
cone-trivial non-maximal corner with a poisoned Λ*-implication, V-lever
= kept chains on the circNotIn premise row; (b) the hloc-lift by
instance-wise promise families (hand-witness pattern), NOT a supply;
(c) hinf → root-only infallibility for the minModV route (the
endpoint route already needs neither).

RESIDUE ATTACKED (2026-08-26 22:24, wip/minmodv_residue.lean): the
cone-trivial non-maximal corner is REALISED (KR: a<b, Rm=id; GR =
(A⊃w)⊃◯w, A = p∨(p⊃q)); route 3 (chosen valuation) REFUTED by
certificate (`route3_blocked`, A is a classForce-tautology); the corner
SERVED anyway by the Υ-enrichment wit (paper second zone; RefAt not
needed); `provableV_residue` runs minModV end-to-end on the instance.
NEXT CONCRETE STEP for the unconditional discharge: the
seen-parametrised minModV — measure (ht, |sfR|−|seen|, t, |C|), corner
branch BUILDS the Υ-enriched join instead of consuming CircSupplyV.

ROUND 3 DONE (2026-08-27 07:38, wip/minmodv_seen.lean): the
seen-mechanism is BUILT (minModS, measure (ht, |sfR|−|seen|, t, |C|);
push drops budget, floats reset).  The flight analysis pinned the true
kernel: I(◯Z) re-arises inside its own row ONLY through upsPrime; under
the decidable guard "left-implication antecedents hereditarily ◯-free"
(guardB) the flight branch is unreachable and
`completenessV_of_circAnteFree` gives SUPPLY-FREE, FRAME-UNCONDITIONAL
FRJV completeness (pins [propext, Quot.sound]).  The residue cell is
re-closed supply-free (provableV_residue_guarded).  REMAINING KERNEL
(sharp): unguarded goals where a fat ⊃∈ⁱ premise stabilises (◯Z⊃W) —
closures on file: support-restricted Lemma 6.5 (thin the fat cells), or
calculus round 3 relaxing hJ2 to RefAt (soundness = the refAt_refutes
vacuity the kept clause already uses).

CALCULUS ROUND 3 DONE (2026-08-27 08:18): barren (J2) relaxed to RefAt
(divergence V5, docs/refat-plan.md); soundnessV re-proved FIRST PASS via
the sf-bounded refAt_refutes_sf/clo_forces_sf (all certificate leaves
are subformulas of the target — the size induction survives); whole
stack green (8915 jobs), pins hold, TOOLS row updated.  Demo:
wip/minmodv_round3_demo.lean — the flight-shaped, guard-violating
(◯w⊃q)⊃◯w in four nodes; M_kept (RefAt-kept) vs M_not_ups_kept (paper
zone cannot).  BOTH obstructions to guard-free completeness are now
cleared (measure: seen-mechanism; calculus: round 3); the remaining
work is the flight-branch corner-join CONSTRUCTION in minModS (thin
premises; kept-completeness by antecedent-size induction; the
support-restricted Lemma 6.5).  Screening step first: hunt the
poison+flight discriminating cell (round-2-FRJV vs round-3-FRJV).

ROUND 3 REVERTED (2026-08-28, option B executed): the relaxation was
UNWITNESSED — its own demo's (J2) was vacuous (the V1 kept chain did
the work), and the revert rebuilt the ENTIRE stack green (8906 jobs) =
corpus-level conservativity verified.  Strict (J2) stands; the
sf-bounded lemmas (clo_forces_sf, refAt_refutes_sf, sf_sub_*) stay in
FRJ/RefAt.lean; licence discipline in refat-plan V5: barren-(J2)
relaxation re-enters only with a kernel-checked separating cell.  THE
CONSTRUCTION PATH (no calculus change): close minModS's flight branch
in the round-2 calculus via thin premise families (empty stable zones →
(J2) vacuous) + the stratified kept chain.  First bricks:
(1) keptOf_saturated — the greedy kept chain is a fixpoint (anything
RefAt-addable over base++kept is already kept);
(2) the corner coverage induction at cone-trivial worlds (forced →
Clo(base++kept); refuted → RefAt), plain size induction since every
Clo/RefAt leaf is a subformula (the refAt_refutes_sf observation);
(3) assemble as the flight-branch join in minModS, dropping the guard.
