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
