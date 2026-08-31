# HANDOFF — lax-logic-in-lean (fairflow/lax-logic-in-lean)

## 2026-08-29a — `TagLeafV` is REFUTED: the lift's interface is uninhabited, and (LIFT) must be reached another way

Branch `claude/frj-redevelopment-69005f`.  The campaign's open item 1
("prove reached `TagLeafV` instances always constructible") is **closed
in the negative**, kernel-checked.  Two increments, both sorry-free and
pinning `[propext, Quot.sound]`.

### 1. The interface was first SHRUNK (wip/minmodv_liftmain.lean)

`RegWitV` constrains the derivation's world only through `K.le a wld`
and `Λ*_wld ⊆ ctx`; the goal must be refuted at `a`, NOT at `wld`.  Two
moves the round-2 recursion did not use, both decidable, both inserted
in the grade-1 prime/or branch ahead of `tl`:

* `RegWitV.mono : K.le a b → RegWitV K G b C → RegWitV K G a C` — a wit
  transports DOWNWARD along `≤` unchanged.  Hence the **strict-refuter
  walk** `strictRef K a C` (the `v > a` still refuting `C`): re-anchor
  there, `ht` drops, recurse.  Run to exhaustion it leaves the demand
  only at a SOLE REFUTER.
* The **coverage re-anchor** `axAnchor K G a C`: `Ax^R` is barren with
  no semantic side condition, so a PRIME goal closes outright as soon
  as some `v ≥ a` has `Λ*_v ⊆ Ĝ_at \ {C}` — a world where the goal may
  even be FORCED.  (`regPrimeV_ax` with its `hloc`/`impPart` hypotheses
  replaced by one subset test, at a world that may be strictly above.)

`TagLeafV` accordingly gained `hsole` and `hax`; `tagLeafV_of_hloc` is
still vacuous, `completenessV_of_hloc` still re-derives `completenessV`,
and both instance cells (`provableV_residue_lifted`,
`provableV_circ_peirce_lifted`) revalidate.

### 2. Then the shrunken interface was REFUTED (wip/tagleaf_refute.lean)

    theorem V.not_clo_of_tagged (d : FRJVr G t Γ C)
        (ht : t = .barren ∨ ∃ W, t = .chain W ∧ Covers Γ W C) :
        ¬ Clo Γ C ∧ ¬ Clo Γ (◯C)

`lemma39R` forces the whole of `Γ` at the root of `Mod(d)` and refutes
`C` there; `tag_cone` refutes `C` on the rest of the root's modal cone;
so the root forces neither `C` nor `◯C`.  **A tagged row can retain
neither its own goal nor the goal's `◯`.**

The separating cell.  `K₂` = the 2-chain `⊥ ≤ ⊤`, `Rm = ≤`, `p` at `⊤`
only, infallible; `G = ◯p ⊃ p` (the co-unit).  Then `Λ*_⊥ = [◯p]`
(circ-carrying) and `Λ*_⊤ = [p]`, the root refutes `G` and refutes
`C = p` while `⊤ ⊩ p`; `⊥` is a sole refuter; `Ĝ_at \ {p} = []` so
`hax` holds.  Every `TagLeafV` hypothesis is DISCHARGED, and its
conclusion would need a tagged row containing `◯p` (anchor `⊥`) or `p`
(anchor `⊤`) — both refuted above.

    theorem tagLeafV_K2_GC_uninhabited : TagLeafV K2 GC → False
    theorem no_universal_tagLeafV :
      ¬ (∀ K G, K.Infallible → ¬ K.valid G → Nonempty (TagLeafV K G))

The refutation uses only `hcirc`/`hsucc`/`hsole`/`hax`, so it kills the
ROUND-2 interface as well, not just the shrunken one.

### 3. What this does and does not say

It does NOT refute (LIFT).  The control is in the same file:
`provableV_GC : ProvableV GC`, via `completenessV_of_endpoints` (`K₂` is
cone-grounded).  The V-engine exhibits the derivation concretely —
`{◯p} ⇒ ◯p ⊃ p` with a **blocked** tag, i.e. through a fallible join,
which `minModL`'s FREE grade accepts and the TAGGED grade cannot.  So
the tagged demand is strictly stronger than provability: the interface
is the wrong object to inhabit.  For `(K₂, ◯p⊃p)`, `completenessV_lift`
is VACUOUS — a false hypothesis — while the goal is provable.

Where the tagged demand comes from, exactly: grade 1 is entered ONLY
from the irregular `◯Z` case, at `mz.e`/`mr.m`, both of which CONE-REFUTE
`Z` — and at a cone-refuted goal `tagPrimeP_join` fires, never `tl`.
Cone-refutation survives the `∧`-descent (a forced conjunct transports)
but NOT the `⊃`-descent to `minEta`'s world.  **So `tl` is reachable only
through a `⊃`-descent (or the corner's regular float) that loses
cone-refutation** — which is where the repair belongs.

### 3a. The criterion — CONSTRUCTED, not enumerated (Matthew, 2026-08-29)

The battery sweep below answered "how often is the interface empty?"
with a statistic.  That is the wrong instrument: the answer is a
theorem, read off two `Λ*` computations with no enumeration.

    theorem tagLeafV_empty_of_stuckAtom {K G w} {x : String}
        (hCR : atom x ∈ sfR G) (hCL : atom x ∈ sfL G)
        (hOCL : ◯(atom x) ∈ sfL G)
        (hnf : ¬ K.force w (atom x)) (hOC : K.force w (◯(atom x)))
        (hsole : ∀ u, K.le w u → u ≠ w → K.force u (atom x)) :
        TagLeafV K G → False

Call `(w, p)` a **stuck atom**: a variable occurring on both sides of
`G` (with `◯p` on the left), refuted at `w`, with `w ⊩ ◯p`, and forced
at every strict `≤`-extension of `w`.  Then `◯p ∈ Λ*_w` and `p ∈ Λ*_v`
for every `v > w`, so every anchor a `RegWitV` could choose is poisoned:
at `w` it must swallow `◯p`, above `w` it must swallow `p`, and
`not_mem_of_tagged` forbids both.  `tagLeafV_K2_GC_uninhabited'`
re-derives the `K₂` cell from the criterion as a consistency control.

So `completenessV_lift` is VACUOUS on the whole stuck-atom class — for
every goal carrying `p` and `◯p` on the left and `p` on the right, and
every model with such a world.  That is not a corner.

### 3b. Where the conflict can and cannot arise

Sharper, and the repair target.  The grade-1 entry worlds `mz.e`/`mr.m`
CONE-REFUTE `Z`, and cone-refutation is exactly incompatible with
`◯Z ∈ Λ*_{w₁}` (forcing `◯Z` needs an `Rm`-successor forcing `Z`).
**So at the entry worlds the conflict cannot happen.**  It is introduced
by the `⊃`-descent to `minEta`'s world, which drops cone-refutation
(the `∧`-descent keeps it).  A grade-1 recursion that preserved
cone-refutation would be conflict-free by construction; restoring it at
the `⊃`-descent — or replacing that descent — is the open design
question, and it is a STATEMENT question for review, not a proof grind.

### 4. The census, SUPERSEDED by §3a (wip/tagleaf_probe.lean, `lake exe tagleafprobe`)

Retained only as the record of how the shapes were first spotted; the
criterion subsumes its evidential role and its brute-force method is
retired (standing rule: construct countermodels, do not sweep).


Battery of 9 infallible models (wf-gated, watched negative control
`Mbad`, two independent circ-carrying detectors cross-checked, and a
watched POSITIVE control for the coverage re-anchor) × exhaustive goals
over `{p,q,⊥}` × the typed V-engine.

| stratum | tl-configs | closed by re-anchor | closed by walk | residue | residue with a RegWitV row |
|---|---|---|---|---|---|
| size ≤ 5 | 76 | 16 | 12 | 48 | 0 |
| size ≤ 6 | 1691 | 282 | 271 | 1138 | 68 |

Cone-trivial refuters: 0 at both strata — the walk never lands on the
easy case.  The residue is one shape: **`C` is an atom occurring on the
LEFT of `G` too**, so `hsole` puts it into `Λ*_v` at every world above
and no anchor escapes.  `wip/tagleaf_probe6_out.txt` banks the run.
(Caveat: the census enumerates configurations MATCHING the predicate,
not configurations the recursion VISITS — see §3 for the reachability
characterisation, which is the open question.)

### 5. Open, restated

1. **Repair the demand, not the interface.**  Either restore
   cone-refutation at the grade-1 `⊃`-descent, or weaken what `circNotIn`
   asks of its premise row.  A third candidate, not yet built: the
   **axiom-pledged join** — `joinAtP` pledging `C` with `Ax^R C` as the
   single promise row, legal whenever the stable zones are empty
   (`hJ5`/`hJ7s` vacuous).  It is decidable per cell.
2. Root-only infallibility (unchanged).
3. Curation (unchanged), now including `tagleafprobe` in TOOLS.md.

## 2026-08-25d — RefAt MECHANISED: FRJV typed calculus, soundnessV PROVED, engines modular, ρ12⊢?ρ15 SETTLED — the matrix has no open cell

Same branch (`claude/frj-incompleteness-80-81-251e7f`).  Plan (review
PENDING, per the calculus-adoption gate): `docs/refat-plan.md`.  All six
deliverables landed sorry-free; `FRJ/AuditV.lean` guard-pins the stack
(gate negative-tested); `#slime` = 0 on both new families.

**The stack** (all new files; nothing existing edited except `FRJ.lean`
and `lakefile.toml`):

* `FRJ/RefAt.lean` — `RefAt` (cone-gated), decider+iff, the stratified
  `KeptChain` certificate, greedy `keptOf` with PROVED `keptOf_ok`, and
  `refAt_refutes` (AXIOM-FREE).  The stratification is load-bearing:
  the unstratified retention condition admits mutually-justifying kept
  pairs and was rejected at design time.
* `FRJ/CalculusV.lean` (+`CalculusVLemmas`) — `FRJVr`/`FRJVi`: the paper
  family with the three BARREN joins generalised (explicit kept zone +
  `KeptChain`; hC/hZ via `RefAt`).  A SEPARATE family, deliberately: the
  ¬Provable theorems are exhaustive case analyses over the paper family
  and survive verbatim.  `toVr`/`toVi` embed paper ⊆ repaired
  (`provableV_of_provable`).
* `FRJ/StepV.lean`, `FRJ/ExtractV.lean`, `FRJ/SoundV.lean` — the ↦
  relation/Lemma 3.4, extraction, and **`soundnessV : ProvableV G →
  ¬ PLL G`** `[propext, Quot.sound]`; the three changed join cases use
  the layered proof (base-(P2)/(P3) size induction unchanged; kept zone
  by chain induction with `refAt_refutes`).
* `FRJ/Search/Core.lean` — **the engine functor `Ops G`: the calculus is
  now an INPUT to the saturation loop.**  `paperOps` = the legacy engine
  (row-for-row differential on 8 goals: AGREE); `FRJ/Search/OpsV.lean` =
  the RefAt instance (kept zones via `keptOf`+`keptOf_ok`, no decision
  procedure runs for the chain).  Runner `lake exe frjvrun
  [diff|cells|cell i j]`.  A typed V-hit IS a derivation, so with
  `soundnessV` every hit is sound by construction — no alarm sweep
  needed.  `Fast`/`Profile` over the functor: follow-up (non-scope).
* `FRJ/BridgeV.lean` — `not_derivable_of_provableV`,
  `not_entails_of_provableV`.

**Witnesses and consequences** (kernel-checked, pins green):

* `wip/frjv_witness.lean` — hand-built `ProvableV G80`, `ProvableV G81`.
* `wip/frjv_consequences.lean` — `¬Deriv [ρ12] ρ9`, `¬Deriv [ρ13] ρ6`
  re-derived THROUGH the repaired calculus (third independent route).
* **`wip/frjv_witness_1215.lean` + `rho12_nle_rho15 : ¬ Deriv [rhoF 12]
  (rhoF 15)`** — the ONE open cell of the 462-cell matrix, settled
  NEGATIVE through the repaired calculus.  With the converse
  battery-settled, {ρ12, ρ15} is INCOMPARABLE; no Hasse edge moves.
  BANKING (an `RNDB` entry via `Engine.frj`-successor provenance +
  retiring `frontierOrder`) is a DATA-layer edit — Matthew's decision;
  nothing is banked yet.  NB the witness derivation never uses `Ax^I◯`:
  its bottom layer runs through the kept chain (`[barren] ν ⇒ ⊥` with ν
  adopted by the ◯-clause over ⊥), machine-verified deviation recorded
  in the file.

**Typed-engine spot checks** (`frjvrun cell`): 4/4 known-refutable
sample cells HIT, residue cell ρ20⊢?ρ12 no-hit (expected), ρ12⊢?ρ15 HIT
(now also settled by hand, above).

**Open / next:** FRJV completeness (untouched, OPEN); the 6-cell residue
(consequent ρ18 / antecedent ρ20) at uncapped arity; `Fast`/`Profile`
instances of the functor; the long-term single policy-parameterised
family (recorded in the plan's non-scope); Matthew: review
`docs/refat-plan.md`, decide banking of ρ12⊬ρ15 and placement of the
witness/consequence files.

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
  nothing; the independent G4c stage-3 probe (`wip/rho1215_probe.lean`,
  emitcap 40, budget 10^5) returned `allStagesMissed` — no countermodel,
  no proof; the cell stays two-sidedly OPEN and the FRJX hit is an
  untrusted lead.  If it is right, the model lies outside the emitter's
  closure-frame class; if the patch leaks, this cell would be the first
  to show it.  Do NOT bank anything from this until a FinCM exists or
  the typed mechanisation lands.

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

**Last updated:** 2026-08-25 by Fable 5 — §2026-08-25d: RefAt mechanised (FRJV + soundnessV + modular engines), ρ12⊢?ρ15 settled negative — no open cell in the matrix; §2026-08-25c: witnesses #80/#81 PROVED as incompleteness theorems, CompletenessFRJ refuted, RefAt repair validated (branch claude/frj-incompleteness-80-81-251e7f); earlier: merge of claude/frj-redevelopment-69005f (through §2026-08-25)
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

## §2026-08-25b — (b)+(a) done: all ⊬ cells kernel-pinned; the catalogue is provably INCOMPLETE — at least 2 (likely 5+) missing classes located

* **(b)** `Certified/RhoSeparations.lean` + `RNDB/SepEntries.lean`
  (generated by `lake exe rhocover emit`): the 95 battery-⊬ cells the
  DB lacked, each kernel-pinned `[propext, Quot.sound]`; DB = 1873.
  Every ⊬ cell of the 462-matrix is now a kernel theorem.
* **(a)** `lake exe rhocover probe` (`wip/rhoprobe_out.txt`): the 12
  candidate joins/meets ordered against the 22 and each other, lattice
  laws first (`⋁S ⊢ k ⟺ ∀a∈S. a ⊢ k`; dually for meets), modest
  search residual, opens FLAGGED.  Verdicts:
  - **Confirmed identities among candidates**:
    ρ5∨ρ19 ≡ ρ6∨ρ19 ≡ ρ9∨ρ19 (=: X₁);
    ρ7∨ρ13 ≡ ρ9∨ρ13 ≡ **ρ12∧ρ15** (=: X₂ — a join equal to a meet);
    ρ10∧ρ20 < ρ18∨ρ20 strictly.
  - **Unconditionally NEW** (banked cells only): X₃ = class(ρ18∨ρ20)
    — fwd/bwd blocked at every k.  X₅ = class(ρ12∨ρ18∨ρ20) — new on
    banked cells + the disjunction property (its only open identity is
    with ⊤, excluded since all three disjuncts are strictly < ⊤,
    kernel-banked).
  - **NEW modulo one open cell each**: X₁ (unless ρ20 ⊢ ρ9∨ρ19, which
    would make X₁ ≡ ρ20); X₂ (unless ρ12 ⊢ ρ7∨ρ13 → X₂ ≡ ρ12);
    X₄ = class(ρ12∨ρ18) (tied to the standing flag ρ12 ⊢? ρ15).
  - X₁…X₅ are PAIRWISE DISTINCT by the candidate matrix regardless of
    the opens; the meets ρ10∧ρ20 ≤ ρ10∧ρ21 and X₂ ≤ ρ15∧ρ21 have open
    converses.
  - So RN(◯,{})'s catalogue has ≥ 24 classes (22 + X₃ + X₅), and
    24–27+ pending three cells.  X₃ sits exactly where the upper-cube
    model predicted a missing vertex (join of ρ18, ρ20 over ρ9).
* **New decision cells surfaced** (next probes, none dropped):
  `ρ20 ⊢? ρ9∨ρ19`, `ρ12 ⊢? ρ7∨ρ13`, `ρ10∧ρ21 ⊢? ρ10∧ρ20`,
  `ρ15∧ρ21 ⊢? ρ12∧ρ15`, plus the standing `ρ12 ⊢? ρ15`.
* NEXT: kernel-certify X₃/X₅ distinctness (hand or-elim terms + the
  banked cells — mechanical), append the new representatives to the
  catalogue (append-only rule), re-run `tools/rho-hasse.sh`.

## §2026-08-25c — probe round 2: 17 distinct new-class candidates; ◯-laws; R2 correction

* Round 2 (`wip/rhoprobe2_out.txt`, 36 candidates): 12 identities
  certified incl. ◯(a∨¬a) ≡ b, ◯¬¬a ≡ ¬¬a, ◯(¬¬a⊃a) ≡ ¬¬a⊃a (ρ5, ρ8
  ◯-FIXED; ◯ρ6 ≡ ◯ρ9); 22 NEW verdicts → **17 distinct new classes**
  (mutual-⊢ dedup; ρ8∨ρ20 fully settled, no open cells).  Catalogue
  heading 22 → ≈39.
* CORRECTION recorded in docs/rho-structure.md: poset-lub ≠ class-join;
  "ρ8 ≡ ρ16∨ρ19 / ρ11 ≡ ρ13∨ρ17 / ρ21 ≡ ρ12∨ρ20" were overclaims —
  now explicit OPEN cells (`ρ8 ⊢? ρ16∨ρ19` flagged by the probe;
  ρ11/ρ21 identities untested).  Certified instead: ρ10 ≡ ρ8∨ρ18,
  ρ15 ≡ ρ11∨ρ18, ρ18 ≡ any two-of-{ρ9,ρ16,ρ17} joins; [ρ4,ρ18] cube
  identities now class-level.
* Hasse rerun after the 95 pins: byte-identical (stability check ✓).
* NEXT: kernel-certify the unconditional new classes; extend the
  catalogue (append-only) once identities distilled; FRJ(◯) on custom
  sequents for the open identity cells; ρ21 ≡? ρ12∨ρ20 and
  ρ11 ≡? ρ13∨ρ17 to round 3 candidates.

## §2026-08-25d — first inhabitants of the cover notion, and its refutation for open formulas

* `RNDB/Order.lean`: `CoversVF` (interposers over the CLOSED fragment,
  the covering relation of RN(◯,{})).  PROVED, kernel-pinned:
  - `obot_decides` / `nbot_decides` — the theories of ◯⊥ and ¬◯⊥ are
    COMPLETE over closed formulas ([propext] only!): structural
    induction `decides_of_somehow` with the ◯-case a parameter.
  - `bot_coversVF_obot : ⊥ ⋖ ◯⊥` and `bot_coversVF_nbot : ⊥ ⋖ ¬◯⊥`
    in the closed fragment (strictness via banked rho-0014/rho-0016)
    — theorems finite testing cannot decide (Matthew's point, 2026-08-25).
  - `not_covers_bot_obot` — the ALL-formulas cover `⊥ ⋖ ◯⊥` is
    REFUTED: `◯⊥ ∧ p` interposes, both countermodels kernel `decide`.
* Explorer v18 rebuild delegated to an Opus agent (own worktree,
  running); brief includes operation table (? / ∉D), embedding ladder,
  formal dictionary-inclusion definition, families c_k/g_k/r_k/◯(g_k)/
  zigzag/Gmeet, ≈39-class data with distinctness caveats, and fresh
  rwscreen substantiation of the simplifier claim.

## §2026-08-25e — explorer v18 delivered; audit corrections (◯-laws NOT new; floor ∈ [14,25]; Catalogue "45 open" is wrong)

* **v18 delivered**: `docs/rn-catalogue.html` ("RN(◯,{}) catalogue",
  v18, successor of rn-explorer v17, which is untouched).  Artifact:
  https://claude.ai/code/artifact/63620d1b-1f7f-4476-8cd2-0c975bddae2b
  Built by an Opus agent; verified in-browser both themes/widths, zero
  console errors.  All rwscreen figures REPRODUCED EXACTLY (89% / 34%
  / 319→28 / 3996→25 / 40%; pins green).
* **CORRECTIONS (all also on the page)**:
  1. The probe's four "◯-laws" were already kernel-proved and in
     `rndSet` (rnDict cBox_4/6/9/10) — cross-validation, not
     discovery.  §2026-08-25b/c overclaimed; docs/rho-structure.md §4
     corrected (also: 37 candidates not 36; 15+1 identities not 12;
     ρ10∧ρ20 also fully settled).
  2. **The "floor of 15" has no standing**: its rationale is refuted
     by banked certificates (q8∧q10 ∉ D₁₅; refute_cOr_8_10).  New tool
     `wip/floor_probe.lean` (`lake exe floorprobe`): 25 = certified
     upper bound, max battery-separated subset = 14 ⇒ floor ∈ [14,25].
  3. `Rewrite/Catalogue.lean`'s header "45 remain genuinely open" is
     WRONG: all 45 are REFUTED CELLS with sorry-free refute_* theorems
     in round 2; the advertised open target list is empty.  (Header
     NOT yet edited — put before Matthew first, since that file's
     docstring is load-bearing for the dictionary campaign.)
  4. ◯(g_k): ONE infinite antichain (bg_incomparable/bg_pairwise
     uniform in indices, k ≥ 2), not many size-3 ones; the size-3
     look was v17's three-level rendering.  Gap: `◯(g k) ⊢? ◯(g 1)`
     uncovered; whether ◯(g 1) ≡ q13 joins is open.  The ◯-collapses
     have NO instance in the family (gap_not_rung/q9/chain).
  5. c_k ascending chain HOLDS unchanged (chainStrict.lean pins);
     c 1 ≡ ρ7 and c 2 ≡ ◯ρ6 are cBox_4/cBox_9 in disguise;
     c 3 = ◯q11 certified ∉D₁₅/∉D₁₆.

## §2026-08-25f — the sorry story ends: dictionary purged to fixpoint; D₁₅/D₁₆ decommissioned

* Matthew's directive: the ρ-catalogue **R** (open-ended, 22 now) is THE
  reference set; forget 15/16; operation tables write **∉R** (certified
  outside the known classes) or `?`, never ∉D; delete every sorried
  dictionary result and iterate to fixpoint (genuine-theory wip sorries
  may stay).  Recorded as standing memory.
* Purge executed: wip/rnDict.lean 87 sorried cells + the refuted closure
  layer (and_ok/or_ok/imp_ok/box_ok, andIdx15 tables, rnDict15) DELETED
  → exactly the 236 proved theorems remain; wip/rnDict2.lean 58 sorried
  + closure layer (rnDict16) DELETED → the 82 proved remain.  Zero
  sorry tokens in both.  Cascade rebuild: RNDB, Certified, Tools,
  Rewrite, rwscreen, rnDictGen, rhocover, wipshared + spot-checks all
  green ON THE FIRST PASS — the proved layer was self-contained;
  fixpoint reached with no external breakage.

## §2026-08-25g — ρ12⊬ρ15 banked; the 462-cell matrix is TOTAL; frontier EMPTY

* Peer branch merged twice (incompleteness theorems #80/#81 + FRJV
  repaired calculus with soundnessV PROVED; then the hoist 89ba5cc:
  witnesses → FRJ/WitnessV*.lean, consequences → Certified/RhoFRJV.lean,
  wip stub kept).  Matthew: promote + bank.
* `Engine.frjv` added to the provenance enum (verdict via soundnessV on
  a kernel-checked FRJV derivation; countermodel extracted by
  FRJ.V.modR).  `RNDB.rho12_nle_rho15` restated wip-free; entry
  `ord-0003` (11-world extracted model, computed); `orderEntries` = 3;
  DB = **1874**; `frontierOrder = []` — every cell of the 462-matrix
  settled (158 ⊢ engine-certified, 304 ⊬ kernel-pinned).
* Consequence for the cubes: `class(ρ12∨ρ18)` (X₄) is now
  UNCONDITIONALLY new (its last candidate identity needed ρ12 ≤ ρ15);
  all three new ρ9-cube vertices unconditional.  Remaining cube
  question: `ρ21 ≡? ρ12∨ρ20` (untested).
* CORRECTION: my peer message claimed RNDB.DB's closure was wip-free —
  false (DictEntries always imported wip/rnDict.lean); it is Order.lean
  whose closure is wip-free, preserved via Certified/RhoFRJV.

## §2026-08-26 — catalogue page v19 (R-centred); last 15-index data deleted; Catalogue header corrected

* **v19 published to the SAME Artifact URL** (label v19-R-tables); page =
  docs/rn-catalogue.html.  Grep-clean of ∉D/D₁₅/D₁₆/rnDict15/sorried;
  membership stated φ ∈ R ⟺ ∃k<22. Interd φ (ρk); the four R operation
  tables are the interactive centrepiece (independently re-counted,
  matches wip/rtable_out.txt exactly); FRJV chain + total matrix + DB
  1874 + empty frontier displayed; embedded Hasse copy drops the
  now-settled dashed (12,15) line (docs/rho-hasse-pll.svg untouched).
* **v19 audit findings acted on**: (1) wip/rnDict.lean's dead 15-indexed
  closure tables (andT/orT/impT/boxT + Fin-15 wrappers) DELETED — zero
  external references; (2) Rewrite/Catalogue.lean header corrected (the
  "45 remain genuinely open" claim was false — all 45 are refuted cells
  with sorry-free refute_* theorems; sorried statements now deleted);
  (3) the v18 floor-refutation argument replaced on-page by the R-native
  fact: closing the ten generators under the ∧/∨ tables reaches exactly
  17 ρ-classes and hits NO ∉R cell (four open join cells); bounds
  [14,25] unaffected.  (4) Synthesis: 8 of the 17 probe candidates are
  now certified ∉R (7 direct + ρ7∨ρ13 by transport through ρ12∧ρ15);
  8 of the 16 ∉R cells were never probe candidates; 9 candidates remain
  unsettled against R.  rho-structure §4 was already corrected on the
  branch (agent read a pre-merge copy).

## §2026-08-26b — ρ21 ≡? ρ12∨ρ20 hardened OPEN; covers: density of full PLL + the cube THEOREM

* (a) `ρ21 ⊢? ρ12∨ρ20` (rtable cell `or 12 20 = ?`): NOT closed.  New
  compiled probe `rhocover jcell 21 12 20 56`: NO battery separation
  exists (10534 frames), LJF◯ deep ladder capped at 50 min without a
  proof.  Same profile as the two former genuine flags, both of which
  fell to beyond-battery countermodels — first-rank FRJV target.  By R6
  the cell IS the identity ρ21 ≡? ρ12∨ρ20 (the ρ9-cube's 4th vertex).
* (b) Matthew's cover programme, assessed:
  - Full PLL: bare ⋖ is EMPTY — the order is DENSE: for a < b and p
    fresh, a ∨ (b∧p) interposes (strictness by substituting p:=⊤/⊥;
    c ⊢ b by orElim from a ⊢ b).  PROVABLE on paper; Lean needs the
    substitution-preserves-LaxND lemma.  Instance a=⊥,b=◯⊥ already
    kernel-checked (not_covers_bot_obot).
  - In the FRAGMENT (CoversVF): the cube conjecture is a THEOREM of
    distributive-lattice algebra for GENUINE covers: S ⊆ U ↦ n∨⋁S
    order-embeds 2^U whenever U is a finite set of covers of n (proof:
    distribute, the cover collapses [n,y] to two elements, distinct
    covers meet at n).  No conditions on n.  The scoped-⋖[K] version
    lacks the interval collapse — that is why it degenerated to testing.
  - First full instance PROVABLE from pinned lemmas: U(⊥) = {◯⊥, ¬◯⊥}
    exactly (consistency split + the completeness lemmas), cube = the
    bottom diamond ρ0,ρ2,ρ3,ρ4.
  - Mechanisation queue: (i) cube lemma at class level; (ii) U(⊥);
    (iii) full-PLL density (subst lemma).

## §2026-08-26c — the cube embedding is a THEOREM, and RN(◯,{}) is formally a bounded distributive lattice

Matthew's Theorem 2 (the covers programme) is mechanised, in its
conditional form (the cover set enters as a hypothesis — this is "prove 2
subject to the existence premise"):

- `LaxLogic/CubeEmbedding.lean` — abstract, over any `DistribLattice`
  with `⊥` (used only for `Finset.sup`), via Mathlib's `CovBy`:
  `cube_le_iff : (∀ y ∈ U, n ⋖ y) → S ⊆ U → T ⊆ U →
  (n ⊔ ⋁S ≤ n ⊔ ⋁T ↔ S ⊆ T)`, plus `cube_inj`.  Sorry-free, pinned
  `[propext, Classical.choice, Quot.sound]`.
- `LaxLogic/ClosedFragmentLattice.lean` — the application home:
  `DistribLattice`/`OrderBot`/`OrderTop`/`BoundedOrder` instances on
  `RNClass := Quotient closedSetoid` (the closed-fragment Lindenbaum
  quotient of `PLLLaxInfinite.lean`).  Every lattice law incl.
  distributivity is pointwise in the Kripke forcing clauses against the
  semantic `Le` — one-line proofs, no ND terms.  `⊥` and `⊤ = ⊥⊃⊥` are
  classes of the fragment itself: NOTHING had to be added.
  `rn_cube_le_iff`/`rn_cube_inj` instantiate the cube theorem at
  RN(◯,{}) verbatim.  Both modules imported by `LaxLogic.lean`.

THE OPEN PREMISE (no Lean declaration — a sorry asserts; recorded here
and on the page):

    For a class n of ◯-depth k, is there a set U(n) of GENUINE fragment
    covers of n with |U(n)| = f(k), f strictly monotone a.e.?

Known: f-data at ⊥ (depth 0): U(⊥) ⊇ {◯⊥, ¬◯⊥} is kernel-proved
(`bot_coversVF_obot/nbot`); exactness U(⊥) = that pair is argued
(consistency split + `obot_decides`/`nbot_decides`) but its mechanisation
is still queue item (ii).  NOTE the embedding needs only MEMBERSHIP, not
exactness: the two proved covers already force the bottom diamond
{⊥, ◯⊥, ¬◯⊥, ◯⊥∨¬◯⊥} = 2² — the first full instance — once the
`CoversVF` ⇄ quotient-`CovBy` bridge lemma is stated (VarFree vs
atomFree alignment; next mechanisation step, with (ii)).

Per-edge programme (the empirical content after the theorem): each
scoped cover a ⋖[R] b of the Hasse diagram upgrades to a genuine cover
only by a relative-completeness argument in the style of the ⊥ case —
proof, never testing.  Page updated to v23: genuine-covers status, the
DL statement, and the previously-undefined ◯-depth (boxDepth + DepthLe)
now in the Definitions tab.

Also this date (§ earlier): the FRJV/FRJX side-by-side record located
(`wip/frjx_sweep_out.txt`, 2026-08-25: ALARMS=0, 297/303, six misses all
with jmax/pmax binding); raised-budget re-run of the six in flight
(`wip/frjx_missrerun_out.txt`); `rhocover matrix` GT dump total at 462
(`wip/rho_matrix_out.txt`).

## §2026-08-26d — bridge lemma + bottom diamond PROVED; simplifier pegged to R

`RNDB/Diamond.lean` (new module, in the RNDB lib), all sorry-free,
pins `[propext, Classical.choice, Quot.sound]`:

- `varFree_iff_atomFree` — the two closedness spellings agree.
- `mkC_le_iff` / `mkC_lt_iff` — quotient ≤/< are `Deriv`/`Lt` on
  representatives (via `le_iff_nonempty`; definitional through
  `Quotient.lift₂`).
- `covBy_of_coversVF` — THE BRIDGE: a `CoversVF` cover on formulas is a
  Mathlib `⋖` cover on classes (interposer quantifiers match because
  every class has an atomFree representative).
- `bot_covBy_obotC`, `bot_covBy_nbotC` — the two ⊥-covers on classes;
  `obotC_ne_nbotC` from `RhoCerts.rho_2_nle_3` (ρ2/ρ3 are ◯⊥/¬◯⊥
  syntactically, `decide +kernel`).
- `bottom_diamond` / `bottom_diamond_inj` — {⊥, ◯⊥, ¬◯⊥, ◯⊥∨¬◯⊥} ≅ 2²,
  the FIRST FULL INSTANCE of the cube embedding, from cover MEMBERSHIP
  alone (exactness of U(⊥) not needed).
- `cube_bottomU_eq_rho4` — the diamond's top corner is ρ4 on the nose.

PREMISE RESTATED (Matthew's correction, 2026-08-26): the outer
quantifier is ∃f —

    ∃ f : ℕ → ℕ, f strictly monotone a.e., such that every class n of
    ◯-depth k has a genuine-cover set U(n) with |U(n)| = f(k)

("a.e." precisely to tolerate low-k oddities; the alternative — excluding
the first so-many k — was considered and rejected as less flexible).
Status OPEN; known data: |U(⊥)| ≥ 2 at depth 0 (now on classes, above);
exactness of U(⊥) remains queue item (ii).

SIMPLIFIER PEGGED TO R (standing rule, Matthew): the rule set is
R-indexed; when R grows, the new class's kernel-proved `Interd` cells
join the set; the set NEVER shrinks. The 795 engine-classed R-table
cells are the promotion queue (engine verdict → kernel `Interd` theorem
→ `RwRule`). Recorded in TOOLS.md §1 and on the page (Simplifier tab);
the "fifteen earliest representatives" framing is retired. Page → v24.

## §2026-08-26e — the simplifier pegged to R AND updated: 679 rules, banked

Matthew's directive executed end to end.  The route matters as much as
the result: the first design (LJF◯ fueled search re-run under kernel
`decide`, per-cell minimal-fuel metering) was WORKING but wrong-shaped —
Matthew asked why fuel was in the statement at all, and the answer was
in the repo: `rnDictGen`'s G4c certificate pattern (untrusted compiled
`G4cTm.findBounded`, budget 4·10⁵ nodes; found proof TERMS printed as
Lean source; the kernel only type-checks literals).  A record-search
failure on my part — the pattern built the original 236 rules.

- `tools/RCellsGen.lean` (`lake exe rcellsgen`): the R-increment
  generator, self-contained copy of the RNGen printer (rnDictGen
  exports a root `main`, so it cannot be imported by another exe).
- `wip/rcells.lean` GENERATED: 442 kernel-checked `Interd` cells over
  ρ13–ρ21 (of 445 classed: 2 SKIP — fwd ρ20∧ρ21, fwd ρ20∨ρ21, the
  G4-search-resistant implication shapes, hand-term candidates in the
  `rncCertPos` precedent — and 1 TRIV, ρ5∨ρ14 syntactically ρ17).
  Whole file kernel-checks in 27 s.
- `Rewrite/Catalogue.lean`: `fullSet := pllSet ++ rndSet ++ rcSet`,
  679 rules, pins UNCHANGED `[propext, Quot.sound]` (guards passed).
- `rwscreen` re-measured (wip/rwscreen_out2.txt): flat 330 cells 89%
  rewritten, crank −34%, distinct forms 319 → 27; NESTED corpus
  3,996 → **18** distinct forms (was 25), crank −40%.  All 679 rules
  crank-oriented.
- Page v26: simpset panels updated (counts, measurement, queue = the
  two skips); TOOLS.md §1 row updated.

The LJF-fuel byproducts are kept as cross-checks (`tools/RCFuel.lean`,
`wip/rcfuel_out.txt`, 255 cells fueled).  The certificate-passing
proof-side engine for LJF◯ (queued in docs/next-session.md) remains
worth building for LJF-specific work; for table promotion the G4c
route is the standing mechanism.

## §2026-08-26f — the two hand cells: the promotion queue is EMPTY

Matthew's interactive-proof exercise, done by anticipating the steps
rather than engine search.  Both skips are absorptions reducing to ONE
fact,  ρ20 ⊢ ρ21 :  [(b⊃ρ4)⊃ρ6] ⊢ (ρ9⊃ρ4)⊃b  (a = ◯⊥, b = ◯¬a).
Proof: from K : ρ9⊃ρ4, `fun hb => K (inl hb)` inhabits b⊃ρ4, so the
hypothesis yields ρ6 = ¬a ∨ ¬¬a; case ¬a → the unit; case ¬¬a → K at
inr gives ρ4 = a ∨ ¬a, where a = ◯⊥ binds over falsum to ◯¬a and ¬a is
absurd against ¬¬a.  The G4 searcher's failure was compound-identity
expansion (atomic init, no atoms in the fragment); ND's `iden` at every
formula is why hand terms win.  The term elaborated FIRST PASS.

- `wip/rcells_hand.lean`: `nd2021` (context-polymorphic, weakening
  free), `rc_and_20_21`, `rc_or_20_21`, pins **[propext]** (cleaner
  than the generated cells' [propext, Quot.sound]).
- `fullSet` = 681 rules; ALL 445 classed R-table cells now
  kernel-checked; rwscreen re-measured (wip/rwscreen_out3.txt, metrics
  unchanged — the absorptions complete the table, not the corpus).
- Page v27: queue EMPTY.

## §2026-08-26g — the four remaining sweep misses HAND-DERIVED in FRJV: the corpus carries NO incompleteness witness

Matthew's directive: pause the raised-budget FRJX computations (up to
2 h/cell) and construct the derivations by hand, anticipating the steps.
Done — all four, EACH COMPILING ON THE FIRST PASS, guided by the cells'
banked countermodels and probed zone vocabularies (sfR/gHat/Clo checked
computationally before each design; the `by decide` side conditions
were the safety net, never the designer):

- `FRJ/WitnessV1918.lean` — [ρ19]⊬ρ18.  Bottom half = WitnessV1215's
  tree at the alphabet a=◯⊥, ¬a, b=◯¬a; the promise `⋈^∨` over the
  ¬a-world gives the ρ4-refuting world 1; root `⋈^∨` with
  RefAt ρ9 = or(circ(ups ¬a), ups ¬¬a).
- `FRJ/WitnessV2018.lean` — [ρ20]⊬ρ18.  Same tree + the Υ-ENRICHMENT:
  orI(i_a, i_na) merges to a ρ4-row, impInI Λ={b} stabilises to a
  ρ11-row (st=[b]; its hJ5 discharged by Clo Γ2 ¬a) — putting ρ11 ∈ Υ
  lets ρ20 ride the promise join's restricted zone.
- `FRJ/WitnessV2013.lean` — [ρ20]⊬ρ13.  New device: the ¬a-world's
  KeptChain adopts ρ8 = ¬¬a⊃a as its SECOND link (ante ¬¬a
  RefAt-refuted through the imp-clause once ¬a is kept) — ρ8 then
  rides Clo everywhere; two nested impIn at the top.
- `FRJ/WitnessV2012.lean` — [ρ20]⊬ρ12.  As 2013, plus a barren `⋈^◯`
  root (RefAt ¬a by ups; kept ρ8, ρ20) for the ◯-target b, under the
  two impIn.

Consequences hoisted into `Certified/RhoFRJV.lean`
(`rho{19,20}_nle_rho{18,13,12}_viaV`, pins [propext, Quot.sound]).
With the two engine hits at jmax=4 (ρ12⊬ρ18, ρ13⊬ρ18, ~2 h each), ALL
SIX of the FRJX sweep's misses are now derived inside the repaired
calculus: the 462-cell corpus yields ZERO incompleteness witnesses for
FRJV — every miss was the join-arity cap.  (Paused computations killed;
the hand route was ~100× cheaper than the engine at jmax=4 and produced
kernel objects instead of logs.)

Lesson for METHOD.md's skill list: the witness idiom is
model-→-tree transcription: probe sfR/gHat/Clo first, one world per
join, promise joins where Rm matters, axIC for vacuous cones,
KeptChain/Υ-enrichment as the two levers when a hypothesis must reach
the root context.

## §2026-08-26e(ii) — FRJV completeness campaign opened: plan approved, native scaffolding ported, target reduced to two supply lemmas

Session (worktree `intelligent-sanderson`, branch
`claude/frj-incompleteness-80-81-251e7f`, synced to redevelopment tip
`6ab559f` then advanced).  Matthew reviewed `docs/refat-plan.md` in
session: plan RATIFIED, architecture ACCEPTED (with the fidelity-anchor
wording corrected — `FRJ/Calculus.lean` is FRJ(G) + the W4 devices, not
TOCL 2020 verbatim), divergences V1–V3 accepted, and FRJV COMPLETENESS
pulled INTO scope.  Campaign plan `docs/frjv-completeness-plan.md`
APPROVED: the target is the UNCONDITIONAL statement

    completenessV : ∀ {K : Kripke} {G : Form}, ¬ K.valid G → ProvableV G

with repair₂ (RefAt at the promise/fallible joins) only if screening
forces it.

Landed, all sorry-free, pins `[propext, Quot.sound]` in `FRJ/AuditV.lean`
(negative-tested):

* `FRJ/CompleteV.lean` (`3ceec1c`) — transfer baseline:
  `completenessV_of_{endpoints,coneGrounded,discrete,supply}`,
  `completenessV_via_closure`, free via `provableV_of_provable`.
* `FRJ/SaturateV.lean` (`7560a98`) — the NATIVE port of the full
  completeness scaffolding to `FRJVr`/`FRJVi` (1,590 lines; the
  mechanical retarget collapsed to three real edits: the soundness half
  over `V.modR_countermodel`, and the two barren-join builder bodies
  via `restrict_keptChain` + `joinCtx*_eq_base` — the paper case is the
  kept-zone special case, as designed).  `V.visit`/`visitMax`/`visitG`,
  `V.completeness_of_endpoints` etc. all native now.

THE REDUCTION: `V.completeness_of_supply` is proved, so the
unconditional target is exactly two `Type`-valued construction lemmas —

    Lemma A:  ∀ K G, V.PledgeSupply K G     (pledge families at
              circ-carrying worlds; the PAPER analogue is FALSE by
              #80/#81, so the kept zone must carry the difference)
    Lemma B:  ∀ K G, V.CircSupply K G      (the §9 stuck corner; the
              frj-w4 §11 self-destruction conjecture, 28 probes pass)

Screening S0 (gating, RUNNING): the six sweep-missed refutable cells.
Settled so far: (ρ12,ρ18) HIT and (ρ13,ρ18) HIT at raised budget
(the redevelopment worktree's own re-run, ~2 h/cell) — budget misses as
the frame analysis predicted (both refuted on sepM).  Outstanding: the
four two-modal-edge cells (ρ19,ρ18), (ρ20,ρ18), (ρ20,ρ12), (ρ20,ρ13),
running in both worktrees at two budget points.  A cap-free miss on any
would falsify Lemma A or B for that configuration and trigger repair₂.
S1 (corner probes vs V) discharged by inclusion: paper ⊆ repaired.

Late addendum (same date, evening): the statement screen KILLED the
supply route before any proof build — `∀ K G, V.PledgeSupply K G` is
FALSE (`FRJ.V.not_pledgeFam_of_circ_mem`, kernel, `◯F ∈ Λ*_a` defect
site; realised on sepM/G80/F=⊥ in `wip/frjv_pledge_refute.lean`).  Two
probes then re-founded the route: `wip/frjv_corner_probe.lean` (every
residue-frame CircSupply demand is Z=⊥ with axIC available) and
`wip/frjv_demand_trace.lean` (a V-routed visit simulator: frame 9900 +
(20,13) trace CLEAN; the one residual demand — `I(◯⊥)@1` on sepM,
axIC blocked by classically-false δ — is served by the kernel witness
via an axIC row INSIDE a join, showing the paper visit's Λ*-coverage
invariants over-demand).  Revised construction target: weakened wit
invariants (witness pattern: axIC rows in joins, classically-true stab
discipline, tag-blind impNotIn floats); the pledge machinery is
expected to drop out entirely.  Full record:
`docs/frjv-completeness-plan.md` (route revision + demand-trace §§).
S0 unchanged: 2/6 HIT, four hard cells still running in both worktrees.
## §2026-08-26h — STEP 0 CLOSED AS FOUND: ◯-free completeness was already proved

Matthew's instruction "check we didn't already prove completeness for
FRJ(G)" hit gold before any new proof was scoped: `FRJ/Minimal.lean`
mechanises Fiorentini–Ferrari THEOREM 6.2(i) —

    completenessData : ◯-free G → K infallible → ¬ K.valid G →
                       Derivation G          (data: model ⟶ derivation)
    completeness     : … → Provable G
    frj_iff_countermodel : the constructive biconditional

pins [propext, Quot.sound] (FRJ/Audit.lean, guarded).  The construction
IS the campaign's planned recursion: `minMod` recurses over (phase,
goal) at each world, `MinModStmt` carries the two invariants (`sub`,
`cov`) the campaign predicted as its sub-lemmas, and the `.circ` match
arm is the explicitly marked ◯-boundary ("out of scope until the modal
rules arrive").

NEW: `FRJ/CompleteV0.lean` — `completenessV_circFree`, the one missing
composition (Theorem 6.2(i) ∘ `provableV_of_provable`): ◯-free
completeness holds for the REPAIRED calculus too, [propext, Quot.sound].

CONSEQUENCES for the campaign: the method is VALIDATED on the control
(it not only works — it is already written); the full FRJV completeness
task is now precisely "extend `minMod` past its `.circ` case", i.e. the
◯-delta alone: promise joins and join arity.  The infallibility
hypothesis is the first ◯-lesson: fallible countermodels carry no data
the calculus can consume (`¬◯⊥` validated by every infallible model),
so the ◯-extension must both handle ◯-goals in `minMod` AND admit
fallible worlds in the source models — the two halves of the delta.

## §2026-08-26i — the ◯-delta ROUND 1: `minModV` extends the template past `.circ`, first-pass green

Matthew's directives, both mid-turn: (1) extend `minMod` past `.circ` by
USING THE EXISTING PROOF AS A FIRM TEMPLATE (same witnesses, recursion,
measure; new cases only — never a fresh proof strategy; lesson added to
`.claude/skills/calculus-adoption/SKILL.md` as the "Extending an adopted
calculus" section and banked in memory); (2) the tweak recorded in the
calculus-adoption skill.

**Landed (`wip/minmodv.lean`, compiles first pass, pins
`[propext, Quot.sound]`, `#guard_msgs`-guarded):**

- `IrrWitV`/`RegWitV`/`MinModStmtV` — the template's witness records,
  V-valued; `RegWitV` carries the tag and the `tOK` obligation
  (`t = barren ∨ ∃ W, t = chain W ∧ Covers ctx W C`) that
  `circIn`/`circNotIn` consume, threaded through every case by
  `tOK_lift` (the `Covers` clauses).
- `regPrimeV_join`/`regPrimeV_ax`/`regOrV_join` — the three regular
  cases on the V-formers.  The paper's `Θ^⊃/Υ` second zone is recreated
  as `restrict (thPool th) Υ` with certificate `keptChain_restrict`
  (via `keptChain_of_ups`); the `hcf`-discharges are replaced by
  `hloc : ∀ b, circPart (Λ*_b) = []`.
- `minModV` — the full recursion, same measure `(ht, t, |C|)`.  NEW
  cases: regular `◯Z` needs NO float at all (`Rm` reflexive gives
  `a ⊮ ◯Z → a ⊮ Z`; recurse on `Z`, close with `circIn`); irregular
  `◯Z` floats to any proper extension refuting `Z` (height drops,
  `circNotIn` with `Λ*`-transport), and when NONE exists — every
  `u > a` forces `Z` — the named supply `CircSupplyV` fires.  That
  corner is the §9 wall of `docs/frj-w4.md` (no lexicographic measure
  orders `I(◯Z)@a → R(Z)@a`); it is a hypothesis consumed at exactly
  that branch and nowhere else.
- `completenessV_of_supply : hloc → Infallible → CircSupplyV →
  ¬valid G → ProvableV G` — round-1 completeness with `G` MODAL on both
  sides.

**Smoke test (`wip/minmodv_test.lean`)**: the Peirce cell
`(◯p ⊃ q) ⊃ q` on `Kripke.point` drives every new branch end to end
(imp case, join with MODAL `Υ`-member `◯p`, irregular `◯`-demand, supply
discharged by the generalised `Ax^I◯` at the empty valuation); pin
guarded, and the guard was WATCHED FAILING on an intermediate sorried
build before the fix (gate discipline).

**Round 2 (the remaining delta, in order of expected yield):**
1. discharge `CircSupplyV` — the four W4 §11 routes (maximal-world
   `Ax^I◯`, chosen-valuation `Ax^I◯`, `Clo`-grounding, member-wise
   analysis), PLUS the new V-fact: the kept chains make the stuck-member
   retention (`(◯Z⊃W) ∈ Λ*` inside the supply row) a decidable `RefAt`
   question rather than a circular `Υ`-demand;
2. lift `hloc` — the promise-join port (`joinAtP`/`joinOrP`/`joinCircP`
   branches at circ-carrying worlds; family = the `Rm`-cone, the §8
   pledge-existence question enters as `PledgeSupplyV`);
3. weaken `hinf` to root-infallibility (per-wit `wfal`, fallible joins
   for the free-graded demands).

## §2026-08-26j — ROUND 2: `CircSupplyV` DISCHARGED (cone-grounded frames); FRJV completeness over endpoint-seeing models unconditional

The supply of round 1 is gone as a hypothesis wherever the frame allows
it, all in `wip/minmodv.lean`, all first-pass, pins
`[propext, Quot.sound]` guarded:

- `IrrWit.toV` — the paper wit embeds (`toVi`), so every FRJ-side
  discharge route serves FRJV.
- `circSupplyV_of_coneGrounded : K.ConeGrounded → CircSupplyV K G` —
  the corner is cone-trivial (`coneTrivial_of_corner`,
  hypothesis-free), cone-groundedness makes it `≤`-maximal, and
  `circWit_of_maximal` (generalised `Ax^I◯` over the world's classical
  theory) closes it.  Covers every `Rm = ≤` model and every discrete
  model.
- `completenessV_of_coneGrounded : hloc → Infallible → ConeGrounded →
  ¬valid G → ProvableV G` — round 1 with NO supply.
- `completenessV_of_endpoints : K.Endpoints → ¬valid G → ProvableV G`
  — UNCONDITIONAL (no `hloc`, no infallibility, no supply): the peer
  campaign's two-tier recursion (`completeness_of_endpoints`,
  `FRJ/Saturate.lean`) composed with the embedding.  The #80/#81
  incompleteness witnesses live on non-endpoint frames — which is
  exactly where FRJV must eventually exceed FRJ.
- `circWitV_of_ats` — the chosen-valuation route (frj-w4 §11 route 3)
  as maximality-free machinery: decidable per world, blocked exactly on
  the poisoned residue `Λ*_a ⊨_cl Z`.
- Smoke test extended: `provableV_circ_peirce_discharged` re-derives
  the Peirce cell with the DERIVED supply (point is discrete →
  cone-grounded); the hand-built supply stays as documentation.

**Peer refutation absorbed (Matthew, mid-turn):** `∀ K G, V.PledgeSupply
K G` is FALSE (`not_pledgeFam_of_circ_mem`; `PledgeFam` uninhabited
whenever `◯F ∈ Λ*_a`, realised at `F = ⊥` on sepM), and kept members
are IMPLICATIONS, full stop.  Consequences recorded in the file header
of the round-2 section: (i) `CircSupplyV` is NOT touched — its corner
is provably circ-free, so `◯F ∈ Λ*_a` cannot arise there; (ii) round
2's `hloc`-lift must NOT be organised through any supply-form
hypothesis on the promise side — instance-wise promise families (the
hand-witness pattern) or a semantic argument, not a `PledgeSupplyV`.

**The residue** (open, both calculi): the corner at cone-trivial
NON-maximal worlds, where a poisoned `Λ*`-implication defeats every
chosen valuation.  The V-lever is the kept chain on the `circNotIn`
premise row — for poisoned IMPLICATIONS only.

## §2026-08-26k — the RESIDUE attacked: realised, route 3 refuted by certificate, and SERVED by Υ-enrichment

`wip/minmodv_residue.lean` (first-pass green except one `Decidable`
unfold), the instance

    KR:  a < b,  V(a) = ∅,  V(b) = {p, w},  Rm = identity, infallible
    GR = (A ⊃ w) ⊃ ◯w,     A := p ∨ (p ⊃ q)   (the poisoned antecedent)

- `residue_corner`: the corner FIRES at `a` for body `w`, `cone(a) =
  {a}`, `a` NOT `≤`-maximal — the exact configuration round 2's
  frame-condition discharge cannot reach.
- `route3_blocked` (pins `[propext]`): `A` is a classForce-TAUTOLOGY,
  so NO valuation satisfies `Λ*_a = {A⊃w}` and refutes `w` — the first
  kernel-checked witness that the chosen-valuation route (frj-w4 §11
  route 3) is insufficient.
- `residueWit`: the demanded `IrrWitV` EXISTS anyway.  Tree: `Ax^I p`;
  `Ax^R q` (whose context grounds `p` and, through the consequent `w`,
  the poisoned `A⊃w`); `⊃∉` gives `· ; {A⊃w} → p⊃q`; `orI` merges to
  `· ; {A⊃w} → A` — **Υ-enrichment**: the poisoned antecedent becomes a
  premise right formula; the `⋈^At` over that row keeps `A⊃w` in the
  PAPER second zone (`keptChain_restrict`, ups-route — the `RefAt`
  relaxation was NOT needed); `◯∉` closes `· ; Λ*_a → ◯w`.
- `supplyR` totalises the supply for the instance and
  `provableV_residue` (pins `[propext, Quot.sound]`) runs `minModV`
  END TO END on the residue model.

**Design consequence for the general discharge**: at any corner, the
poisoned antecedents are `sfR`-members unforced at the corner world —
exactly the demands the recursion's irregular layer already serves; the
corner's regular `Z`-row is a join over those `I(A)`-cells with the
second zone doing the retention.  The missing piece is ONLY the measure
that lets `I(◯Z)@a` call `I(A)@a` (the seen-mechanism, frj-w4 §11
second addendum): no calculus gap, no new supply, and the kept chains
stay in reserve.  Next concrete step: the seen-parametrised `minModV`
(measure `(ht, |sfR| − |seen|, t, |C|)`), whose corner branch builds the
join in place of consuming `CircSupplyV`.

## §2026-08-26l — the ◯-delta ROUND 3: the seen-mechanism BUILT; supply-free completeness for guarded goals on ALL frames

Matthew asked for the next step "not hopeful"; the design pass first
located exactly where the hope should have failed, then walled it off:

**The flight analysis** (recorded in the header of
`wip/minmodv_seen.lean`): the corner push `I(◯Z)@a → R(Z)@a` is fine on
the seen-measure, but inside the `Z`-row the demand `I(◯Z)` can
RE-arise — only through `upsPrime`, i.e. whenever `(◯Z ⊃ W) ∈ Λ*_a`.
At that flight corner the current calculus has no new route (the kept
chain covers the SECOND zone via `RefAt.circ` from an `I(Z)`-premise,
but a Υ-member with an `a`-forced antecedent forces a fat `⊃∈ⁱ` premise
whose STABILISED zone re-demands antecedents in Υ literally — strict
hJ2).  Candidate closures, not needed this round: support-restricted
Lemma 6.5, or calculus round 3 relaxing hJ2 to `RefAt` (its soundness
obligation is the same `refAt_refutes` vacuity the kept clause uses).

**The build** (`wip/minmodv_seen.lean`, first-pass modulo one
choice-taint fix — `List.mem_dedup` carries `Classical.choice`, so the
budget runs over `sfR G` un-dedup'd; the subperm bound needs only the
seen-list Nodup):

- `minModS` — `minModV` with `seen` threaded on the measure
  `(ht a, |sfR G| − |seen|, t, |C|)`: corner pushes drop the budget,
  floats reset `seen` under a height drop; the join helpers re-typed
  with `upsPrime`-membership `ih`s (`regPrimeS_join`, `regOrS_join`) so
  the caller can establish the invariant
  `hCseen : ∀ Y, ◯Y ∈ seen → ◯Y ∉ sf C`.
- The FLIGHT branch is closed by `hCseen` + `self_mem_sf` — a
  contradiction, not a supply — because the guard

      hguard : ∀ A B, (A ⊃ B) ∈ Sf^L(G) → ∀ X ∈ sf A, ¬ X.isCirc

  (decidable: `guardB`/`guard_of_guardB`) makes `upsPrime`-goals
  hereditarily ◯-free, so no in-flight `◯` can be re-demanded.

**The theorem** (pins `[propext, Quot.sound]`, guarded):

    completenessV_of_circAnteFree :
      hguard → hloc → K.Infallible → ¬ K.valid G → ProvableV G

— NO supply and NO frame condition: the first goal-conditioned FRJV
completeness.  Frame-conditioned (rounds 1–2) and goal-conditioned
(this) now cover complementary regimes; neither supersedes the other.

**Instance closed supply-free**: `provableV_residue_guarded`
(`wip/minmodv_residue.lean`) re-derives the residue cell through the
guarded recursion on its cone-trivial non-maximal frame — the exact
configuration rounds 1–2 needed a hand supply for.

**The remaining kernel, sharpened**: unguarded goals whose `Λ*` carries
`(◯Z ⊃ W)` AND whose corner Υ needs a fat premise stabilising it.  The
two candidate closures above; the Υ-enrichment instance
(§2026-08-26k) shows the thin-premise route works when no fat premise
is forced.

## §2026-08-27a — CALCULUS ROUND 3: barren (J2) relaxed to RefAt; soundness re-proved size-founded; whole stack green

Matthew's directive ("try the hJ2 relaxation — this reminds me of the
issues with duplication in G4iLL" — the same disease: a search-friendly
side condition too strict for completeness).  Executed as the tight
template loop, one rule change + downstream fixes, all green in one
session (8915 jobs across LaxLogic/FRJ/wipshared/Certified/Tools/
Rewrite/RNDB):

- **The rule change** (`FRJ/CalculusV.lean`, divergence V5 in
  `docs/refat-plan.md`): `joinAt`/`joinOr`/`joinCirc` (J2) becomes
  `RefAt true Υ base A` in place of `A ∈ Υ`; promise/fallible joins
  stay paper-strict (V3 discipline).  `toVr` embeds old derivations by
  `RefAt.ups`.
- **Soundness, first pass** (`FRJ/SoundV.lean`): the (P2) branch of the
  size-mutual induction now refutes stable antecedents by
  `refAt_refutes_sf` — a new `sf`-bounded variant (with
  `clo_forces_sf`, `FRJ/RefAt.lean`) whose point is that every
  `ups`-leaf AND every `Clo`-leaf of a certificate is a SUBFORMULA of
  its target, so the induction stays founded where the naive
  `refAt_refutes` would demand full-context forcing at arbitrary sizes.
  `hcone`/`hinf` are frame facts and hoisted above the induction.
- **Downstream**: `baseAtV/OrV_imp_head`, `StepV` binder types (barren
  constructors only), `OpsV` barren builders (`.ups`-wrapped — the
  V-engine now admits strictly MORE barren rows), `WitnessKit` gains
  `hJ2R_of_impAnteB` + a `frjv_side` arm, witness files patched at
  barren sites only, both recursions re-wrapped.  Pins all hold
  (`[propext, Quot.sound]` throughout; soundnessV re-cleared).
- **The device, live** (`wip/minmodv_round3_demo.lean`):
  `G3 = (◯w ⊃ q) ⊃ ◯w` — guard-violating, flight-shaped — derived in
  four nodes; `M_kept` certifies the kept chain adopts `◯w ⊃ q` via
  `RefAt.circ∘ups`, and `M_not_ups_kept` certifies the PAPER zone
  cannot (no separation claim: this cell is also axIC-servable; the
  discriminating cell needs poison + flight together — next screening).
- TOOLS.md row updated in the same commit (engine behaviour changed).

**What round 3 unblocks**: the flight corner's stable-zone deadlock is
gone — a stable `(◯Z ⊃ W)` discharges (J2) by `RefAt.circ` over an
`I(Z)`-premise (t-drop legal).  The remaining build for guard-free
completeness: the corner-join construction inside `minModS`'s flight
branch (thin premises + kept-completeness by antecedent-size induction
with the support-restricted Lemma 6.5).  The measure obstruction and
the calculus obstruction are now BOTH cleared; what remains is
construction, not repair.

## §2026-08-27b — ROUND 3 REVERTED under the conservativity screening: unwitnessed, and the kept chain suffices

Matthew flagged the calculus change ("that would be a flag") and chose
option (B): prove round 3 conservative over round 2, and on success
revert.  The screening's operational form was the tight loop in
reverse — revert the rule and rebuild everything; a breakage would BE
the separating witness.  Outcome:

- **The vacuity finding** (the decisive fact, a correction to
  §2026-08-27a): the round-3 "device live" demo never exercised the
  relaxed rule — its join has an EMPTY stable implication zone, so its
  (J2) was vacuous; the retention that served the flight-shaped cell is
  the V1 KEPT CHAIN, which already carries full `RefAt` power in round
  2.  Round 3 had no witnessed instance of necessity.
- **Design dry-runs** (recorded here as the screening's second leg):
  every attempted blocking configuration self-destructs into a kept
  reroute — (i) a stable `(◯Z⊃W)` with in-flight `◯Z` is keptable via
  `RefAt.circ` over an `I(Z)`-premise; (ii) the demotion-blocking shape
  (`X = ◯w⊃v` Clo-load-bearing inside a forced conjunction) reroutes by
  keeping `X` FIRST (context-free `RefAt.circ∘ups`) and the dependent
  member second — the stratification handles it; (iii) the kept-pool
  intersection over thin premises survives because `⊃∉`-premises may
  take `Θ ∋` any `Λ*`-forced member (Lemma 6.5 at the float anchor).
  Conjecture (OPEN, recorded not asserted): full conservativity
  `ProvableV₃ → ProvableV₂`; corpus-level conservativity is now
  VERIFIED — the whole stack (8906 jobs) rebuilds green on strict (J2),
  including the flight demo BY THE SAME TREE
  (`wip/minmodv_round3_demo.lean`, reheadered as the vacuity witness).
- **Kept from round 3** (calculus-independent): `sf_sub_*`,
  `clo_forces_sf`, `refAt_refutes_sf` in `FRJ/RefAt.lean` — the
  sf-bounded semantic lemmas, useful machinery regardless.
- **Licence discipline going forward** (V5, `docs/refat-plan.md`): a
  barren-(J2) relaxation re-enters only with a kernel-checked
  separating cell.  Rounds V1/V2 keep their #80/#81 licence.

**The construction path this clarifies**: the flight branch of
`minModS` should be closed IN THE ROUND-2 CALCULUS by thin premise
families (empty stable zones → (J2) vacuous) + the stratified kept
chain; the enabling brick is `keptOf_saturated` (the greedy chain is a
fixpoint: anything `RefAt`-addable over base++kept is already kept) and
the corner coverage induction (forced → `Clo(base++kept)`; refuted →
`RefAt`), which closes on plain size because every leaf is a
subformula.  No calculus change is on that path.

## §2026-08-28a — the two flight bricks PROVED: `keptOf_saturated` and the corner coverage induction

Both bricks of the guard-free flight closure are kernel-checked,
choice-free (`[propext, Quot.sound]`, `#guard_msgs`-pinned):

**Brick 1, `keptOf_saturated`** (`FRJ/RefAt.lean`, with
`growChain_extends`/`growChain_saturated`): the greedy kept chain is a
FIXPOINT —

    (A ⊃ B) ∈ pool → RefAt true Υ (base ++ keptOf Υ base pool) A →
    (A ⊃ B) ∈ keptOf Υ base pool.

Fuel `pool.length` cannot run out before saturation: each round adopts
a FRESH pool member, and a Nodup sublist of `pool` has at most
`pool.length` members (`length_le_of_nodup_subset`, hoisted here from
the seen file).  Consequence: kept membership IS `RefAt`-derivability
over the final context — the mutual retention knot is cut.

**Brick 2, `corner_coverage`** (`wip/minmodv_flight.lean`): at a
cone-trivial infallible world with an adequate Υ/base/pool triple
(`CornerSupply`: forced sfL-atoms in base; forceStar implications in
pool; Υ covering refuted sfR-atoms, imps without a local
counter-witness, and ◯s with locally-forced body), ONE plain size
induction gives both halves:

    (F)  X ∈ Sf^L(G), a ⊩ X  ⟹  Clo (base ++ keptOf Υ base pool) X
    (R)  Y ∈ Sf^R(G), a ⊮ Y  ⟹  RefAt true Υ (base ++ keptOf …) Y

— (F) at a forceStar implication calls (R) at its antecedent (proper
subformula, opposite polarity) and lands it in the kept zone by
brick 1; forced `◯X'` descends by cone-triviality.  Corollary
`corner_lamStar_clo`: `Λ*_a ⊆ Clo(base ++ kept)` — the `hTh`
obligation of the flight branch's `◯∉` cell.

**Two hygiene catches** (both by tooling, per the discipline):
`by_cases` was replaced by explicit `Decidable.em` splits, and —
the real culprit, found by `#choice_path` — **`omega` on a CONJUNCTION
goal pulls `Classical.propDecidable`** through its De Morgan
normalisation (`Lean.Omega.Decidable.or_not_not_of_not_and`); single
comparison goals are clean.  Standing fix: split conjunction goals
before omega.  Recorded in the axiom-hygiene memory.

**Remaining for the guard-free flight closure** (the assembly): inside
`minModS`'s flight branch, build the thin premise family that
discharges `CornerSupply` — `Ax^I` rows for refuted atoms (Υ), `⊃∉`
floats for imps refuted only above (Υ), fresh-corner pushes for ◯s
(seen-budget), the base/pool zones from the same rows — then the
barren join over it (empty stable zones, so strict (J2) is vacuous),
`◯∉` via `corner_lamStar_clo`, replacing the guard.  No calculus
change anywhere.

## §2026-08-28b — THE ASSEMBLY COMPLETE: supply-free, guard-free, frame-free FRJV completeness

The campaign statement is PROVED, kernel-checked, choice-free
(`wip/minmodv_assembly.lean`, pins `[propext, Quot.sound]` guarded):

    completenessV : (∀ b, circPart (Λ*_b) = []) → K.Infallible →
                    ¬ K.valid G → ProvableV G

— `◯` unrestricted on both sides of the goal, NO supply, NO goal guard,
NO frame condition, in the STRICT round-2 calculus, on the round-1
measure `(ht, t, |C|)`.  End-to-end instances re-derived through it
with nothing supplied: the residue cell (`provableV_residue_assembled`)
and the Peirce cell (`provableV_circ_peirce_assembled`).

**How the corner fell.**  Two semantic vacuities sharpened everything:
a refuted implication has a REFUTED consequent, and a refuted `◯` has a
REFUTED body — so at the corner no `◯`-cell is ever demanded (the SEEN
machinery died on the spot) and `rowFor`'s descent is total:

- the thin premise family (`familyRows`): `Ax^I` rows for every refuted
  `Sf^R`-prime + `⊃∉` float rows for every refuted-antecedent
  `Sf^R`-imp, the floats' regular premises built by the recursion at
  the `minEta` witness STRICTLY ABOVE (height drops — the only
  recursive calls the corner makes); nonemptiness by descending the
  refuted skeleton (`familyRows_ne`);
- the float rows' Θ-zones are the FILTERED good zones
  (`Ĝ ∩ Clo(w.ctx) ∩ forced-at-a`), giving `thGoodAt` — so the joint
  atom zone and the kept pool absorb everything forced (`cc_interAt`,
  `cc_pool`) while `hAnot` still discharges (members a-forced,
  antecedent a-refuted);
- all stable zones empty → strict (J2) VACUOUS, hJ1 trivial;
- `CornerSupply` discharges (`cc_supply`) — the over-provisioned
  clauses (`Or.inr`, `hUcirc`) by the vacuities — and the two bricks
  (`corner_coverage`, `keptOf_saturated`) give `(F)`/`(R)` coverage
  over each leaf base;
- `rowFor` descends `Z` structurally to the three barren-join leaves
  (`atLeaf`/`orLeaf`/`circLeaf`: hC/hZ from `(R)`, `⊃∈`'s `Clo` from
  `(F)`), and `◯∉` closes the irregular cell with `hTh` =
  `corner_lamStar_clo`'s content.

**Hygiene catches this round** (tool-found, both banked): `Decidable.em`
match cannot eliminate into data (use `dite`); a bare `simp` on
membership-in-filter over `force`-atoms pulled classical `not_forall` —
hand-roll with `decide_eq_false_iff_not`; `#choice_path` named both.

**What remains of the FRJV completeness question**: lift `hloc`
(promise-join port at circ-carrying worlds — instance-wise families,
NOT a supply, per the peer's refutation) and weaken `K.Infallible` to
root-infallibility (per-wit `wfal`, fallible joins).  The corner — the
open kernel since W4 — is CLOSED.

## 2026-08-28c — hloc-lift round 1: the regular ◯-case closes hloc-free (wip/minmodv_lift.lean)

Matthew's goal: "lift hloc then: the promise-join port".  The design
pass split `completenessV`'s `hloc` into its three consumption points
and closed the first the same evening.

**PROVED** (pins `[propext, Quot.sound]`, choice-free):

  * `corner_lamStar_mem` — at a cone-trivial infallible world,
    `Λ*_m ⊆ base ++ keptOf Υ base pool` as LITERAL membership (not
    just `Clo`-coverage): atoms sit in the joint atom zone; every
    `Λ*`-implication has a refuted antecedent (`forceStar`), so
    `keptOf_saturated` adopts it into the kept chain; `Λ*`-circs are
    impossible at cone-trivial worlds.  This is exactly `RegWitV.cov`.
  * `circRegWit` — the hloc-free regular `◯Z`-witness at ANY world of
    ANY infallible model: `minZeta` picks `e ≥ a` whose whole Rm-cone
    refutes `Z`; `maxRmAbove` walks Rm-up inside that cone to a
    cone-trivial `m` (cone-refutation transports along Rm, so `m ⊮ Z`
    and `m ⊮ ◯Z`); ONE barren `⋈^◯` over the corner family with
    `(R)`-coverage concludes `◯Z` there — no `Z`-row, no descent into
    `Z`, tag `.barren` for free — and the `RegWitV` floats back to `a`
    with `wld := m`.

Why the peer's pledge refutation does not bite here: nothing is
pledged (barren join), and a cone-refuted `Z` can never have
`◯Z ∈ Λ*_m` — `m ⊩ ◯Z` would place a `Z`-forcing successor inside the
refuting cone.  Pledging is safe exactly on cone-refuted formulas,
which is the paper's own discipline; `PledgeSupply`-as-universal
quantified over the unsafe instances too, hence its refutation.

**The refined map** (recorded in docs/next-session.md): the
free-grade prime/or port at circ-carrying worlds looks mechanical
(fallible joins, Λ*-thick premises — the `Λ*`-circs ride through the
modal zones because every premise's invariant carries them); after it
and this brick, EVERYTHING remaining funnels into one residual —
tagged `Z`-rows at arbitrary circ-carrying worlds for `◯∉`'s premise,
where structural descent loses cone-refutation (a cone refuting
`Z₁ ∧ Z₂` splits per world).  That is the §8 corner's V-form and is
genuinely OPEN.  Next step per METHOD.md: refute-first — hunt a
model+goal realising the residual configuration before scoping any
build.

Stack green (8811 jobs), `wip.minmodv_lift` in the wipshared globs.

## 2026-08-28d — THE hloc-LIFT LANDS: the promise-join port, built and green

Same evening as §2026-08-28c, under Matthew's /goal "lift hloc then:
the promise-join port".  Four staged commits, every stage green and
pinned `[propext, Quot.sound]`, choice-free throughout (two
Classical.choice intrusions caught by the pins and removed: push_neg
and a by_cases on a bounded ∀, both replaced by the constructive
filter-match device).

**PROVED** (wip/minmodv_port.lean, wip/minmodv_liftmain.lean):

  * Stage 1 — the free grade: `FreeWitV` (RegWitV minus the tag
    obligation) + `regPrimeF_join`/`regOrF_join`: fallible joins at
    ANY world, `Λ*`-thick premises, the modal zone kept by
    `joinCtxCircF`; family `C :: upsPrime` headed by the fat `Ax^I`
    cell (`axIWitV`), so no emptiness dichotomy.
  * Stage 2 — the pledged joins: `tagPrimeP_join`/`tagOrP_join`:
    chain-tagged rows for CONE-REFUTED prime/or goals; promise family
    = one tagged row per proper `Rm`-successor pledging the goal
    (`htag`'s per-row condition is `RegWitV.tOK` verbatim); (J5) and
    the `restrictC`-zone grounded by each `Λ*`-circ's own
    `Rm`-witness, which is a proper successor hence IN the family;
    `restrictP` survived by forced-ness (`mem_clo_lamStar`).
  * Stages 3–4 — `minModL` (wip/minmodv_liftmain.lean): three grades
    (0 = irregular, 1 = tagged, ≥2 = free) on the assembly's measure
    `(ht, grade, size)`; `ht_le`/`ht_lt_of_le` (height antitonicity)
    for the re-anchored floats; the `(0, ◯Z)`-cell routes through
    `minZeta` (anchor strictly above → tagged row there) or
    `maxRmAbove` (`Rm`-walk to a cone-trivial world ≠ a) or the
    assembly's corner in place (a itself cone-trivial); `circRegWit`
    serves every regular `◯`-goal.  **The theorem:**

        completenessV_lift : TagLeafV K G → K.Infallible →
          ¬ K.valid G → ProvableV G

    where `TagLeafV` is the ONE named residual: a tagged prime/or wit
    at a circ-carrying world where the goal is refuted but some proper
    `Rm`-successor forces it (not cone-refuted).  `hloc` makes it
    vacuous: `completenessV_of_hloc` re-derives the assembly theorem
    through the lift (the supersession gate), and both instance cells
    (residue, Peirce) are re-validated through it.

**The refute-first probe** (wip/frjv_probe.lean, `lake exe frjvprobe`):
closed formulas are constant across infallible models (`◯⊥ ≡ ⊥`
there), so the ρ-matrix cannot test the lift — the probe enumerates
variable-carrying goals over {p,q,⊥} against a battery of small
infallible circ-carrying models (wf-gated, negative control watched
failing) and runs the typed V-engine (`vOps`, a HIT is an FRJVr
derivation) on every refuted survivor.  Strata ≤5/≤6/≤7: 608/2702/
16696 refuted goals, 19/236/1027 at circ-carrying configurations,
**zero misses** — every target derivable, `(LIFT)` unrefuted; the
corpus-replay mode (residue/flight/witness shapes) also all-HIT.
Size-8 (116k formulas, 9-model battery) launched.  The probe also
showed the engine's winning rows are often barren with the `Λ*`-circ
only in irregular Θ-zones — provability routes around retention.

**OPEN, sharply:** discharge or refute `TagLeafV`-freeness — either
(a) a semantic argument that reached interface instances are always
constructible (the probe's zero-miss evidence points this way), or
(b) a kernel-checked cell whose lifted derivation genuinely needs an
un-cone-refuted tagged leaf, which would be the next calculus-round
licence.  Also still open: root-only infallibility (the second
remaining hypothesis), and a hand end-to-end instance on a genuinely
circ-carrying model (M2-style) with `tl` hand-supplied.

## 2026-08-29b — Gbu(G) stage 3 complete over IPC; the three ◯-seams named

Branch `claude/frjv-completeness-693c52`, worktree `strange-thompson-902a24`.

Continuing the track opened in §2026-08-29a (reconstruct `Gbu(G)` from
the recovered arXiv source, prove §5, then derive `Gbu◯` from unmet
obligations rather than guessing rules).

**Done.**  §5 of Fiorentini–Ferrari is now fully mechanised over IPC:

* Lemma 12 `gbuSuccOr` (the `∨` success lemma) — `wip/gbu_db.lean`;
* Theorem 8 `search` (correctness of `BSearch`) — `wip/gbu_search.lean`,
  by well-founded recursion on `Wg`, every case DECIDED (the
  `Decidable (EvalI …)` argument is the paper's own database query, so
  the proof is a procedure, not an appeal to excluded middle);
* `saturated_fderivable` — `Subsumes` is reflexive, so the set of all
  derivable sequents is a saturated database;
* Theorem 9 `gbu_frj_duality`: `⊢_Gbu(G) G ↔ ⊬_FRJV(G) G`;
* Theorem 10: `provableV_of_not_pll` is **FRJV completeness on the
  ◯-free fragment**, relative to a saturated database with a decidable
  evaluation relation.

Everything pins `[propext, Quot.sound]`.

**Open on the IPC layer**: the finite saturated database of §4 with a
decidable `▷` (stage 4).  Saturation is not the obstruction; finiteness
and decidability are.

**The deliverable for the ◯ extension** is `docs/gbu-circ-seams.md`.
Theorem 8 takes ◯-freeness as two hypotheses; they are consumed at
exactly three points, and each determines its rule from the `FRJV` rule
with the matching conclusion:

1. `Ψ, ◯Z ⇒g C` → `L◯` with an **◯-shaped goal** (unrestricted is
   unsound); invertibility free from `Clo.circ`; measure fine.  But ◯
   still enters the critical zone, so Lemmas 11/12 must be re-proved
   over `joinAtP`/`joinOrP`, whose `hJ5` is a NEW database query.  At a
   **prime** goal with `◯Y ∈ Ω` no rule can exist — a candidate site for
   the residual incompleteness, to be tested against the 6-cell residue
   BEFORE any rule is written.
2. `Ψ ⇒g ◯Z` → `R◯`, unconditional and sound; the cost is a condition
   on the database (the `Covers`/`KeptChain` retention obligation, the
   same object as LJF◯'s `CimpAnt`).
3. `Ω →g ◯Z` → `R◯ₙᵢ`, focus-**releasing**; no focus-preserving `R◯ᵢ`
   can exist (its FRJ direction is unsound, and correspondingly no such
   `FRJVi` rule is in the table).  **It breaks the measure `Wg`** — `tp`
   rises with nothing added to the left zone.  Settling the measure is
   the first task; a used-implication history is conjectured (untested)
   to fix it.

**Next session**: (1) settle the `Wg◯` measure; (2) test the seam-1
prime-goal gap against the residue; (3) only then add the three rules
and re-prove Lemmas 11/12, keeping every ◯-free case of `search`
compiling verbatim.

### 2026-08-29c — the `Wg◯` measure, settled

`wip/gbu_measure.lean`.  Two results, both machine-checked.

**Negative.**  The step relation of `Gbu◯(G)` on sequents alone has a
two-cycle, for every `G`: with `Γ = ◯Z ⊃ B, Ψ`,

    Γ →g ◯Z  is a premise of  Γ ⇒g Z    by L⊃ on ◯Z ⊃ B
    Γ ⇒g Z   is a premise of  Γ →g ◯Z   by R◯ni

`not_wf_stepC` (axiom-free), and hence `no_measure_stepC`: **no** measure
from sequents into **any** well-founded order can work.  The conjecture
in §2026-08-29b — that a reordering of `Wg` might do — is REFUTED, not
merely unproved.

**Positive.**  Carrying a store `U` of the implications already focused
on at the current context, the measure

    Wg◯(τ, U) = ⟨ |Sf^L(G) \ Cl(Ψ)| , Σ_{X∈Ψ}|X| , |Ψ^⊃ \ U| , |C| ⟩

lexicographic, decreases on all twenty steps (`wgo_step`), so `stepU_wf`.
`tp` disappears — it existed for exactly one step, `L⊃`'s left premise,
and it is precisely what `R◯ni` increases; `ctxSize` replaces it as the
component the context-shrinking left rules decrease, which is what lets
the store count be reset when the context changes (`L∧` can expose
implications that were not in `Ψ^⊃` before).  `stepC_of_stepU` certifies
that this is bookkeeping, not a different calculus: every `StepU` step
erases to a `StepC` step.

The gate was negative-tested: injecting a non-decreasing step turns
`wgo_step` red and taints the pin with `sorryAx`.

**Consequence for `BSearch◯`**: when Lemma 11's witness is already
banked, the left premise must be supplied from the store rather than
re-derived, and only the right premise is recursed on (its `ctxSize`
drops).  So `U` should store DERIVATIONS.  Lemma 11 itself is unchanged,
so the strategy stays complete.

**Next**: rebuild `SearchOk` over the store-carrying state `SeqU`, then
items 2–4 of `docs/gbu-circ-seams.md`.

### 2026-08-29d — the cycle is REACHABLE (FRJV used to settle it)

Matthew's reminder mid-session — "you can use FRJV to construct
countermodels" — closes the one real gap in §2026-08-29c.  `not_wf_stepC`
is about the abstract step relation, and the fair objection is that
`BSearch` only visits sequents the database does NOT refute, so a cycle
among unreachable states would be harmless.  It is not.  With

    Γ  =  ◯z ⊃ ⊥ ,  p ,  p ⊃ z

`Γ ⊢ z` and `Γ ⊢ ◯z`, so neither `Γ ⇒g z` nor `Γ →g ◯z` is refutable —
for EVERY database (`cyc_notRefuted`) — while `L⊃` on `◯z ⊃ ⊥` and
`R◯ni` connect them in both directions.  `Γ ⊆ Ĝ` for the concrete
`cycG = p ⊃ ((p ⊃ z) ⊃ ((◯z ⊃ ⊥) ⊃ z))`.

Two lemmas were needed and are reusable:

* `frjv_countermodel` — sequent-form soundness of FRJV: a derivation of
  `Γ ⇒ C` carries a model whose root forces `Γ` and refutes `C` (this is
  `lemma39R` plus `preR_root_lbl`, which nothing had packaged before);
* `not_evalR_of_valid` / `not_evalI_circ_of_valid` — a semantically
  valid sequent is refuted by no database.  The irregular case turns on
  the observation that only `circNotIn` and `axIC` can conclude `◯Z`,
  and `axIC` is excluded by a `classForce` computation.

`not_evalR_of_valid` is worth keeping in view for the whole campaign: it
converts "this is PLL-valid" into "no database refutes it", which is the
(BSr1) side of every `BSearch` argument.

## 2026-08-30a — seam 1 CLOSED (the fallible join); §5 reorganised into paper order

Branch `claude/frjv-completeness-693c52`, worktree `strange-thompson-902a24`.

**Item 2 of `docs/gbu-circ-seams.md` answered, and the prediction was
wrong.**  The seam-1 prime-goal gap does not exist.  I had reasoned that
`Ω ⇒g F` (F prime, `◯Y ∈ Ω`) would be neither Gbu◯-provable nor
FRJV-refutable, because the PROMISE join's `hJ5` asks, at `Y = F`, for a
row refuting `F` whose context closes `F`.  What I missed: the promise
join is not the only one.  The FALLIBLE join `⋈^At_F` has no modal side
condition and keeps the whole modal zone.  Kernel-checked, in FRJ◯, not
in the search engine:

* `provableV_counit` — the derivation of `◯p ⊃ p` written out (`Ax^I`
  gives `∅ ; {◯p} → p`; `⋈^At_F` puts `◯p` in the context; `⊃∈`);
* `gbuSuccAtF` / `gbuSuccOrF` — Lemmas 11 and 12 with `Ω ⊆ Ĝ` in FULL
  three-zone form, by swapping `⋈^At`/`⋈^∨` for their fallible twins.
  The `hcirc = []` premise was the only place ◯-freeness was used.
  Negative-tested: reinstating it leaves an unsolved goal.

Two supporting findings.  (1) The **6-cell residue was already CLOSED**
(2026-08-26): 4/6 kernel-checked in `Certified/RhoFRJV.lean`, 2/6 engine
hits at jmax=4; every miss was the join-arity cap.  My memory was a day
stale — the standing rule "search the record before treating a finding
as new" caught it only after I had re-derived part of it.  (2) A
462-cell syntactic sweep (`wip/gbu_residue_probe.lean`) shows the
seam-1 configuration reachable in 283/297 of the cells the engine DID
refute, so it could never have discriminated the six; the residue
concentrates on consequent ρ18 (4/10 vs a 2% baseline) and antecedent
ρ20, i.e. the ∨-side.  And the ρ-corpus is CLOSED, so its only prime
formula is `⊥` and it contains no instance of seam 1 at a genuine atom
(`wip/gbu_seam1_probe.lean` supplies them; all six PLL-invalid cells
HIT, all three valid ones `none`).

**`wip/gbu_circ.lean` reorganised into the paper's own order** (Lemma 7,
Thm 6, Lemma 8, Thm 7, Lemma 9 clauses 11–13, Lemma 10, Lemma 11, Lemma
12, Thms 8–10), with a status ledger at the head, and TWO re-run points
so a change to either calculus edits one declaration:

* `TagClean G D Z` — everything the modal layer takes from FRJ◯.  `◯∈`
  and `◯∉` both carry `t = barren ∨ (t = chain W ∧ Covers Γ W Z)`, so a
  row for `Z` lifts to `◯Z` only when its tag is clean.  Lemma 9's two
  modal clauses (`gbuInv12`, `gbuInv13`) are then THEOREMS, and
  `frjCircKit_of_tagClean` is the single declaration to edit when FRJ◯'s
  tag discipline changes.
* `FRJCircKit G D` — the whole interface as one record.
* The three rules are given SEMANTICALLY, one lemma each, independent of
  any inductive: `sound_lcirc` (pins `[propext]`), `sound_rcirc`
  (axiom-FREE).  Writing the extended inductive later is a one-line
  dispatch per constructor.

`lcirc_goal_must_be_circ` REFUTES the unrestricted `L◯` with a two-world
countermodel, so the ◯-shaped goal is a fact, not a style choice.

**The live obligation, sharpened.**  `gbuSuccAtF`/`gbuSuccOrF` deliver
`Tag.blocked` rows, and `blocked` is NOT clean: `◯∈`/`◯∉` cannot lift
it.  So the fallible route and the `◯`-introduction route currently have
INCOMPATIBLE TAGS.  That, not seam 1, is what stands between here and
Theorem 8◯.

**Next**: (a) settle the tag conflict — either a fallible `◯∈` (the way
`RefAt` relaxed the barren joins) or a route that avoids `blocked`;
(b) rebuild `SearchOk` over the store-carrying state `SeqU`.

## 2026-08-30b — Gbu◯(G) built: P2 adopted, left rule admitted, conservativity gated

Matthew's decisions this session: settle the open question first, then go
with (P2); admit the left rule in the irregular judgment, conservativity
being proved, and RE-CHECK conservativity whenever the rules change.

**The open question (docs/gbu-tag-proposal.md §5) — both horns fail.**
With `Ω = {p, p⊃◯q}`, `Z = q`: `Ω ⊨ ◯q` so `Ω →g ◯q` is refuted by NO
database (`not_evalI_omegaNI`) — (BSr1) holds, `Ax` does not fire, `L◯`
cannot apply — yet `Ω ⊭ q`, so `Ω ⇒g q`, `R◯ni`'s only premise, is not
derivable at all (`not_gbuR_omegaNI`).  `R◯ni` is needed AND
insufficient.  What `Ω ⊢ ◯q` uses is modus ponens, a LEFT rule.

**The tag conflict, settled negatively.**  `◯∈` needs the root's whole
modal cone to refute `Z`; a `blocked` row's model has a fallible world
there, which forces everything.  So excluding `blocked` is forced by
soundness, and `rcirc_not_invertible` / `rcircNI_not_invertible` refute
Lemma 9's clauses 12 and 13 outright, on
`Gtc = (◯p ⊃ p) ⊃ (◯p ⊃ p)` (chosen so `◯p` is in both `Sf^L` and
`Sf^R`, meeting the clauses' own side condition).

**The PLL-completeness reading**, which unifies several loose ends: the
canonical model's `Rm Γ Δ iff {A : ◯A ∈ Γ} ⊆ Δ` IS the joins' `hJ5`; the
fallible worlds PLL's completeness requires ARE `Tag.blocked` and the
fallible joins; a fallible world realises every body at once, which is
why `⋈^At_F`/`⋈^∨_F` need no `hJ5` and why Lemmas 11–12 extended for
free.  And there is no `⋈^◯_F` because a `⋈^◯` must REFUTE `◯Z` at the
root, which a fallible successor makes impossible — so the tag conflict
and the missing fallible `◯`-join are the same fact.

**Built** (`wip/gbu_circ.lean`, all sorry-free):

* `gbuSuccCirc` — Lemma 13, P2's licence, via `⋈^◯` (`hZ : Z ∈ Υ` is
  `⋈^∨`'s `hC` with one element).  Caveat: `⋈^◯` has no fallible
  variant, so the modal-zone case needs `⋈^◯_P` and its `hJ5` — OPEN.
* `GbuRC`/`GbuIC` — the calculus, 12 + 9 constructors, `#slime` 0.  Six
  new rules: `L◯` (regular and irregular), `L⊃ᵢ` at a `◯`-goal, `R◯`
  (irregular premise, per P2), `R◯ni` (regular premise).
* `soundRC`/`soundIC` (Lemma 7) and `pll_of_provableGbuC` (Theorem 6).
* **The conservativity gate**: `deCircR`/`deCircI`, a TOTAL translation
  `Gbu◯(G) → Gbu(G)` for `◯`-free `G`; `ofGbuR`/`ofGbuI` the converse;
  `provableGbuC_iff_provableGbu`.  Divergence D9: the new constructors
  carry the blanket sequent-language condition on their `◯`-formula
  (`Gbu(G)`'s do not, see D2) precisely so the discharge is mechanical.
  **Negative-tested**: injecting an unrestricted `L⊃ᵢ` makes BOTH
  `soundIC` and `deCircI` report the missing case and taints the pin.
  A future rule that can fire on `◯`-free input cannot slip through.

**Next**: Theorem 8◯ — rebuild `SearchOk` over the store-carrying `SeqU`
with the ◯ critical cases; and the modal-zone case of Lemma 13.

### 2026-08-30c — Lemma 13 modal case; `L⊃ᵢ`'s soundness isolated

`sound_limp` (pins `[propext]`) answers Matthew's "`L⊃ᵢ` doesn't look
valid": it is valid, and MORE generally than the rule states — plain
modus ponens, for ANY goal and in either judgment.  The `◯`-shaped goal
on `GbuIC.limpLI` is not a soundness condition; it is there only so the
rule cannot fire on a `◯`-free goal, i.e. purely to keep `deCircI`
total.  What the rule does change is the READING of `→g` (the paper's
frozen context), which is the design cost already accepted.

`gbuSuccCircP` — Lemma 13 for the MODAL zone, via `⋈^◯_P`.  `⋈^◯` has no
fallible variant, and that is forced: a `⋈^◯` must make its root REFUTE
`◯Z`, so its whole modal cone must refute `Z`, which a fallible world
forbids.  The extra hypothesis is `PromiseWorld G Ω Z` — a derivation
refuting `Z` from a `Δ` that covers `Ω`, carries a liftable tag, and
REALISES every body of `Ω`'s modal zone.  That clause is the canonical
model's `Rm Ω Δ iff {Y : ◯Y ∈ Ω} ⊆ Δ` from PLL's completeness theorem,
turned into a database query.  Negative-tested: drop it and `hJ5` is
underivable (the proof needs a sorry).

Both pin `[propext, Quot.sound]` / `[propext]`.

### 2026-08-30d — the two-rule change adopted; Theorem 8◯ localised

Pushed to `origin/claude/frjv-completeness-693c52` (explicit refspec;
`push.default = upstream` and no upstream was set, so nothing had gone
out before — that is why the campaigns looked out of sync).

**Adopted** (Matthew, 2026-08-30): `R◯ni` (regular premise) replaced by

    Ω →g Z
    ──────── R◯i        premise IRREGULAR
    Ω →g ◯Z

and `L⊃ᵢ` restricted by `|A| < |◯C|`.  Motivation: `no_measure_stepC`
forced a store, and the store cannot carry the recursion (the spec's
only useful reading of a banked implication is "its left premise is
built", and the `∉U` branch recurses for exactly that premise —
circular).  With the change the PAPER's weight `⟨unclosed, tp, |τ|⟩`
decreases on every step: `wg_stepO`, `stepO_wf`, no store.  The size
restriction is what kills the cycle of `cyc_notRefuted`, and both
motivating cells survive (`{p,p⊃◯q} →g ◯q` by `L⊃ᵢ`, `{p} →g ◯p` by
`R◯i`).  `#slime` 0 on both families; `deCircI` re-checked conservativity
automatically, per the standing rule.

`no_measure_stepC` and the store-carrying `Wg◯` stay in
`wip/gbu_measure.lean` as the record of WHY `R◯ni` was abandoned.

**Theorem 8◯, case analysis done.**  Three findings.

* GOOD — the regular `◯` goal needs NO promise world.  `L◯` is
  invertible for free (`gbuInv11`) and fires whenever the goal is
  `◯`-shaped, so search strips the modal zone EAGERLY; by the time a
  `◯`-goal sequent is critical its context has no top-level `◯`, and
  `gbuSuccCirc` suffices.  `gbuSuccCircP` is not needed by the search.
* OBSTRUCTION 1 — the irregular `◯` goal `Ω →g ◯Z` has no success
  lemma.  Its rules (`Ax`, `L◯ᵢ`, `L⊃ᵢ`, `R◯i`) are none of them
  invertible: `EvalI` is membership-based, not `Clo`-based, so `L◯ᵢ`
  does not come free the way `gbuInv11` does.  The only `FRJVi` rules
  concluding `◯Z` are `Ax^I◯` and `◯∉`, whose premise is REGULAR — the
  same mismatch `rcircNI_not_invertible` exposed, now confined to ONE
  case.
* OBSTRUCTION 2 — `L◯ᵢ` breaks the invariant `Ω ⊆ Ĝ`: it replaces `◯Y`
  by `Y`, which need not be an atom/implication/`◯`, and the irregular
  judgment has no `L∧`/`L∨` to recover.  `circ_body_escapes_gHat`
  (`G = ◯(p∧q) ⊃ p`) is a kernel-checked instance.  Fixes: admit
  `L∧ᵢ`/`L∨ᵢ` (further departure), or restrict `L◯ᵢ` to bodies in `Ĝ`
  and check completeness of that restriction.

**Next**: obstruction 2 first (it is a choice between two rule sets, and
the answer decides what obstruction 1's success lemma has to cover).

### 2026-08-30e — obstruction 2 CLEARED

`L◯ᵢ` replaces `◯Y` by `Y`, which need not lie in `Ĝ`
(`circ_body_escapes_gHat`, `G = ◯(p∧q) ⊃ p`).  `sfL_dec` settles what can
escape, exhaustively: a left subformula is an atom, an implication or a
`◯`-formula — already in `Ĝ` — or else `⊥`, `∧`, `∨`.  Nothing else.

So `L⊥ᵢ`, `L∧ᵢ`, `L∨ᵢ` were admitted, each at a `◯`-shaped goal like the
other irregular left rules.  Cost, checked in each direction:

* soundness — the regular proofs transplant verbatim (`soundIC`);
* termination — all three shrink `ctxSize`, so the PAPER's weight still
  decreases (`wg_stepO`, `stepO_wf`), no store;
* conservativity — each carries `◯C ∈ Sf^R(G)`, so none can fire on a
  `◯`-free goal; `deCircI` stays total.  Negative-tested: injecting
  `L∧ᵢ` WITHOUT the `◯`-goal condition makes both `soundIC` and
  `deCircI` report the missing case and taints the pin.

`GbuIC` is now 12 constructors (`GbuRC` 12), `#slime` 0 on both.

The design has a clean statement: **at a `◯`-shaped goal the irregular
judgment has exactly the regular judgment's rules; elsewhere it stays
focused.**  That is PLL's `◯`-elimination demanding left access, and
nothing more.  It also bears on obstruction 1: since the two judgments
now have the SAME rules at a `◯` goal, the success lemma the irregular
`◯` goal needs should be `gbuSuccCirc`'s, differing only in whether the
database query is `EvalR` or `EvalI`.

**Next**: obstruction 1 — the success lemma for `Ω →g ◯Z`.

## 2026-08-30f — Obstruction 1 CLEARED: the clean-refutation layer

Obstruction 1 was that the irregular `◯` goal `Ω →g ◯Z` had no success
lemma. The cause was in the DATABASE model, not the calculus.

`FDerivable (.reg Γ C)` is `∃ t, Nonempty (FRJVr G t Γ C)` — the tag is
existentially quantified away — and (DB2) answers a query with a
SUBSUMING row, whose tag is then unknown. But the only two `FRJVi`
rules that conclude `◯Z` are `Ax^I◯` and `◯∉` (`FRJ/CalculusV.lean:250`),
and `◯∉` carries

    htag : t = .barren ∨ ∃ W, t = .chain W ∧ Covers Γ W Z

so it needs a tag the database has already forgotten. That is the same
mismatch `rcircNI_not_invertible` exposed, seen from the other side.

**The fix: ask before the database forgets.** `RefutedCleanly G Ω C` —
an `FRJV` derivation of `Γ ⇒ C` with a liftable tag and `Γ` covering `Ω`
— localises `TagClean` to one derivation instead of imposing it on the
whole database. That matters, because `TagClean D` is FALSE for the real
database: `⋈^At_F` and `⋈^∨_F` store `blocked` rows, and they must, since
fallible worlds are what make `¬◯⊥` refutable.

| | | pin |
|---|---|---|
| `RefutedCleanly` | the localised query | — |
| `evalR_of_refutedCleanly` | clean ⟹ refuted | `[propext, Quot.sound]` |
| `refutedCleanly_mono`, `_clo` | antitone in the covered context | same |
| **`gbuSuccCircI`** | **Lemma 14**: `RefutedCleanly G Ω Z → EvalI D Ω (◯Z)` | same |

Lemma 14 is short, and — the surprise — needs NO query on `Υ`: the
antecedents are already carried by `Γ`'s covering of `Ω`. It is
semantically exactly right. `a ⊮ ◯Z` iff `Z` fails at some `Rm`-successor,
that successor is the root of its own REGULAR refutation, and `Ω` is
forced there too because `Rm ⊆ ≤`. A fallible successor cannot serve,
because a fallible world forces `Z` for free — which is why `◯∉` carries
the tag, and why there is no `⋈^◯_F`.

**The suppliers are complete.** Every shape of `Z` has one, and each was
obtained by splitting an existing lemma at its (DB2) step rather than by
a new proof — `gbuSuccAt` and `gbuSuccOr` are now one-line wrappers:

| `Z` | supplier | rule |
|---|---|---|
| prime | `refutedCleanly_at` | `Ax^R` / `⋈^At` — both `barren` |
| `∨` | `refutedCleanly_or` | `⋈^∨` — `barren` |
| `∧` | `refutedCleanly_and1/2` | `∧R₁/₂`, tag kept, `Covers.andL/.andR` |
| `⊃` | `refutedCleanly_imp` | `⊃∈`, tag kept, `Covers.imp` |
| `◯` | `refutedCleanly_circIn` | `◯∈`, tag kept, `Covers.circ` |
| `◯` (join) | `refutedCleanly_circ` | `⋈^◯` — `barren` |

Negative test: weakening the tag disjunct to `t = .barren ∨ True` makes
`gbuSuccCircI` fail at its `◯∉` argument (`wip/gbu_circ.lean:906`), and
`refutedCleanly_circIn` at its `◯∈` argument. Restored, green.

**FOR REVIEW — a divergence from the paper.** The suppliers above are
closed under exactly the regular search's moves, so Theorem 8◯ should be
re-based with `¬ RefutedCleanly G Ψ C` in place of `¬ EvalR D Ψ C` on the
regular side. That is a STRONGER theorem (`RefutedCleanly → EvalR`, so the
hypothesis is weaker), and the top level survives it: `¬ ProvableV G`
gives `¬ RefutedCleanly G [] G` immediately. But `RefutedCleanly` does not
mention `D` at all, so re-basing weakens the paper's own point — Gbu(G)'s
backtracking-freedom comes from querying the database, and on the regular
side that query would no longer be a lookup. Two readings, and the choice
is Matthew's:

  (i) accept it: Gbu◯ is complete w.r.t. clean FRJV refutations, and the
      database survives on the irregular side only;
  (ii) restore the lookup by making the database tag-aware — add a
      `regC` clause to `FSeq`. Blocked on whether FRJV admits
      tag-preserving weakening, since (DB2) returns `Γ ⊆ Γ'`; FRJ contexts
      are exact, so this is not obviously available.

No rule of `GbuRC`/`GbuIC` changed this session, so the conservativity
gate `deCircR`/`deCircI` is untouched and still green.

## 2026-08-30g — Tag-preserving weakening REFUTED; option (ii) adopted (D9)

**The question.** (DB2) answers a query with a SUBSUMING row, `Γ ⊆ Γ'`.
Option (ii) — restore the database lookup at the modal rules by recording
tags — turns on whether cleanliness survives that enlargement:

> **(W)** If `Γ ⇒ C` has a derivation with a liftable tag, `Γ ⊆ Γ'`, and
> `Γ' ⇒ C` is derivable, then `Γ' ⇒ C` has a derivation with a liftable tag.

**REFUTED**, kernel-checked, `wip/gbu_weakening.lean`, `[propext, Quot.sound]`.

The general obstruction first (`not_clean_of_clo_circ`):

> If `Clo Γ (◯C)` then NO derivation of `Γ ⇒ C` carries a liftable tag.

Proof — three lines, and it is the ◯-clause's existential form that makes
it work. The root forces `◯C`, and forcing is
`a ⊩ ◯A  iff  ∀b ≥ a. ∃c. b Rm c ∧ c ⊩ A`, so SOME `Rm`-successor `c` of
the root forces `C`. `tag_cone` (`FRJ/SoundV.lean:1510`) says every PROPER
successor refutes `C`. Hence `c` is the root, so the root forces `C` —
contradicting `lemma39R`, which has the root refuting the goal.

The witness is the sharp one, `G = ◯p ⊃ p` (`tag_weakening_refuted`):

| | | tag |
|---|---|---|
| `[] ⇒ p` | `Ax^R` | `barren` — clean |
| `[] ⊆ [◯p]` | `gAt G = [p]`, so `rm (gAt G) p = []` | |
| `[◯p] ⇒ p` | `⋈^At_F`, whole modal zone kept | `blocked` |
| `[◯p] ⇒ p` | no clean derivation exists | by the above |

Note what this is: the same fact as `FRJ.provable_circ_imp`, read from the
tag side. `◯p ⊃ p` is refutable only through a fallible successor, and a
fallible successor is exactly what no tag can certify.

**Decision: (ii), via a SEPARATE stratum (divergence D9).** W's failure
does not block (ii); it dictates its shape. Cleanliness cannot be a flag
on a `reg` row, because it is not inherited along subsumption. It can be
a clause of its own, subsumed only by clean rows:

    FSeq.regC Γ C
    FDerivable (.regC Γ C) = ∃t. FRJVr G t Γ C ∧ (t = barren ∨ ∃W. t = chain W ∧ Covers Γ W C)
    Subsumes (.regC Γ₁ C₁) (.regC Γ₂ C₂) = C₁ = C₂ ∧ Γ₁ ⊆ Γ₂
    EvalRC D Ψ C = ∃Γ. D (.regC Γ C) ∧ ∀X ∈ Ψ. Clo Γ X

and then, the point of the exercise —

    evalRC_iff_refutedCleanly :  Saturated G D →  (EvalRC D Ψ C ↔ RefutedCleanly G Ψ C)

`RefutedCleanly` quantifies over derivations; `EvalRC` is a lookup; on a
saturated database they coincide. So **Lemma 14 becomes a (BSr1) query
like every other** (`gbuSuccCircIC`, and the contrapositive
`not_evalRC_of_not_evalI_circ` that the search will consume), and Gbu◯
keeps the paper's backtracking-free character at the modal rules. The
regular side stays on `EvalR`; the divergence from §5 is one extra
database clause, not a change to what the search computes.

Realisability at the interface: `saturated_fderivable` extends by one
line — reflexive subsumption — so the enlarged axiom set is satisfiable.
That is consistency of the interface, NOT a claim that FRJ's saturation
procedure as implemented emits `regC` rows; that is a separate obligation,
and it is stage 4 work, not stage 3.

Cost across the codebase: one constructor, three match arms, one lemma.
Every existing `match s', hsub` stayed exhaustive on its own (the
cross-stratum cases reduce to `False`).

Negative test: allowing `Subsumes (.regC …) (.reg …)` makes
`evalRC_iff_refutedCleanly` report "Missing cases" at
`wip/gbu_db.lean:418`. Restored, green.

No rule of `GbuRC`/`GbuIC` changed, so the conservativity gate
`deCircR`/`deCircI` is untouched.

## 2026-08-30h — Theorem 8◯: regular branch PROVED, three residues named

`wip/gbu_search_circ.lean`, sorry-free, `[propext, Quot.sound]`.
`searchO` is the modal `BSearch` correctness theorem, over THREE modes:

| mode | sequent | (BSr1) query |
|---|---|---|
| `reg` | `Ψ ⇒g C` | `¬ D ▷ (Ψ ⇒g C)` |
| `irr` | `Ω →g C` | `¬ D ▷ (Ω →g C)` |
| `cirr` | `Ω →g C` | `¬ D ▷ᶜ (Ω ⇒g C)` |

The third is forced by `R◯ᵢ`: its licence is `gbuSuccCircI`, whose
hypothesis is the CLEAN lookup, and the two irregular queries are
incomparable. `cirr` also carries the `Υ` queries the clean success
lemmas consume.

**Weight.** The paper's `Wg` is unchanged; a mode-graded `tp` was tried
and REFUTED — `R∧ᵢ` at `C₁ ∧ ◯C₂` turns a non-modal goal into a modal
one, so the mode cannot be graded by the goal's shape. What pays for
`L⊃ᵢ`, whose premises are both irregular, is the rule's own `hsz`.

**Proved outright: the whole REGULAR branch**, `L◯` and `R◯` included.
`L◯` is invertible (`gbuInv11`) so the search exhausts it first, which
is exactly what leaves `Ψ ⊆ Ĝ_at ∪ Ĝ_imp` for `⋈^◯` at `R◯`. The
irregular branch is proved at every non-modal goal, and at a modal goal
over a critical context; the clean branch is proved outright.

**New: Lemma 9 clause 14** (`gbuInv14`) — `D ▷ (Ω' →g ◯Z)` transfers to
any `Ω ⊆ Ĝ` with `Ω ⊆ Cl(Ω')`. Not `EvalI`'s own monotonicity: it holds
because only `◯∉` and `Ax^I◯` conclude a `◯` goal, `◯∉` admits any
`Cl(Γ)`-member of `Ĝ` into its zone, and `Ax^I◯`'s zone is `Ĝ` filtered
by a CLASSICAL valuation — closed under `Clo` because `Clo` has
introduction clauses only (`clo_classForce`). This licenses `L◯ᵢ` and
`L⊃ᵢ`, and removed the supply I expected to need for them.

### The three residues, as named hypotheses

**(S1) `BigAnte`** — `L⊃ᵢ` carries `hsz : |A| < |◯C|`, so modus ponens on
an implication with a large antecedent is unavailable, and the `Υ` query
the clean mode needs cannot be discharged.

    Ω ⊆ Ĝ_at ∪ Ĝ_imp,  A ⊃ B ∈ Ω,  ◯Z ∈ Sf^R(G),
    D ⋫ (Ω →g A),  |A| ≥ |◯Z|   ⟹   Ω →g ◯Z

`hsz` is not removable: without it `Ω = {◯r ⊃ s, ◯s ⊃ r}` cycles
`Ω →g ◯s → Ω →g ◯r → Ω →g ◯s`. A weakening to
`A.isCirc = false ∨ |A| < |◯C|` would kill that cycle and close S1 for
all non-modal antecedents — but it is a change to the FORM of a rule, so
it is PROPOSED here, not implemented.

**(S2) `NonHatCirc`** — and this one is a finding, not a gap to fill.
`L⊥ᵢ`/`L∧ᵢ`/`L∨ᵢ` (obstruction 2) are UNLICENSED by (BSr1). Their
premises need `gbuInv14`, whose `Ω ⊆ Ĝ` hypothesis fails exactly when
the context carries the `⊥`/`∧`/`∨` they decompose. And such a context
can never be covered by an irregular row at all — every `FRJVi` zone is
a subset of `Ĝ` — so (BSr1) is satisfied VACUOUSLY there and carries no
information. The root cause is upstream: `L⊃ᵢ`'s second premise
`B :: Ψ →g ◯C` puts an arbitrary `B ∈ Sf^L(G)` into an irregular
context, breaking the `Ω ⊆ Ĝ` invariant (BSr2) that the whole irregular
judgment rests on. Obstruction 2's repair kept the CALCULUS complete but
did not restore the invariant, and the search can only see the
invariant. Either `L⊃ᵢ`'s second premise becomes regular (and then its
licence needs a clean tag — the `rcircNI` problem again), or (BSr2) is
weakened and `gbuInv14` generalised past `Ĝ`. Matthew's call.

**(S3) `CleanReg`** — the clean-regular search that `R⊃ₙᵢ` releases into
from the clean mode. Its own residue is a critical context carrying a
`◯` at a non-modal goal, where only the FALLIBLE joins apply and no
clean row exists — the same fact as `tag_weakening_refuted`, met from
the other direction.

Top-level corollary `provableGbuC_of_not_provableV` is proved from the
three supplies plus `¬ D ▷ ([] ⇒g G)`, and `not_evalR_root` shows that
hypothesis IS `⊬_{FRJV(G)} G` on the canonical database.

The clean-stratum divergence is renumbered **D9**: `wip/gbu_search.lean`
already used D8 for ◯-freeness-as-a-hypothesis.

## 2026-08-30i — `L⊃ᵢ`'s `hsz` weakened, but NOT to the form I proposed

Matthew authorised the `hsz` weakening. Implementing it refuted the
form I had proposed, so the adopted condition is strictly stronger than
the authorised one — recorded here because that is a deviation.

**What I proposed** (§2026-08-30h):

    hsz : A.isCirc = false ∨ |A| < |◯C|

**REFUTED** (`not_wf_stepW`, `[propext]`). `R∧ᵢ` puts the modality
straight back, giving a two-cycle:

    Ω = { (◯z ∧ ⊥) ⊃ ⊥ }
    Ω →g ◯z ∧ ⊥   is a premise of   Ω →g ◯z        by the weakened L⊃ᵢ
    Ω →g ◯z       is a premise of   Ω →g ◯z ∧ ⊥    by R∧ᵢ

`◯z ∧ ⊥` is not `◯`-SHAPED, so the proposed condition admits it; but it
is not `◯`-FREE, and the conjunct walks straight back to a modal goal.

**What is ADOPTED**:

    hsz : A.hasCirc = false ∨ |A| < |◯C|

`◯`-freeness, not `◯`-shapedness. A `◯`-free goal decomposes only into
`◯`-free goals, so the sub-search under `L⊃ᵢ`'s first premise can never
return to a modal one, and the cycle above cannot form.

**What pays for it: `Wg◯`.** The paper's `tp` is graded by the goal:

    tpC(reg, C) = 2        tpC(irr, C) = 1 if `◯` occurs in C, else 0

Grading by "the goal IS `◯`-shaped" fails — `R∧ᵢ` at `C₁ ∧ ◯C₂` would
raise it, which is what I recorded as refuting mode-grading in §h.
Grading by "the goal CONTAINS a `◯`" works, because that IS monotone
under subformula: every goal decomposition keeps it or lowers it, and
`L⊃ᵢ` into a `◯`-free antecedent strictly lowers it. `wgC_step` re-proves
the paper's own eighteen steps against the graded weight, case for case
against `wg_step`; `StepO`/`wg_stepO`/`stepO_wf` are re-founded on it.

**Effect on the residues.** (S1) `BigAnte` shrinks to antecedents that
BOTH carry a `◯` and are too large:

    Ω ⊆ Ĝ_at ∪ Ĝ_imp,  A ⊃ B ∈ Ω,  ◯Z ∈ Sf^R(G),  D ⋫ (Ω →g A),
    ¬(A is `◯`-free ∨ |A| < |◯Z|)   ⟹   Ω →g ◯Z

(S2) `NonHatCirc` and (S3) `CleanReg` are untouched. `searchO` and
`provableGbuC_of_not_provableV` remain sorry-free at
`[propext, Quot.sound]`, and the whole repository builds.

**Conservativity re-checked**, per the standing instruction. `deCircR`
and `deCircI` are unchanged and still total; negative-tested by
injecting an `L⊃ᵢ` variant with no `◯`-goal condition, which makes both
`soundIC` (`:1415`) and `deCircI` (`:1499`) report "Missing cases" and
taints `provableGbuC_iff_provableGbu` with `sorryAx`. Restored, green.

## 2026-08-30j — S2 CLEARED: the irregular `◯` goal carries its `Ĝ` ancestor

`NonHatCirc` is gone; `searchO` now takes two supplies, not three, and is
still sorry-free at `[propext, Quot.sound]`.

**The diagnosis in §h was right but the conclusion was too pessimistic.**
`L⊃ᵢ`'s second premise `B :: Ψ →g ◯C` puts an arbitrary `B ∈ Sf^L(G)`
into an irregular context, and there the bare (BSr1) is vacuous — no
`FRJVi` zone reaches outside `Ĝ`, so nothing can refute such a context
and `D ⋫ (Ω →g ◯C)` carries no information. What I missed is that the
licence does not have to come from the PARENT. It comes from the last
`Ĝ`-context on the branch, which is unrefuted and lies `Clo`-below the
current one — and `Clo` is transitive, so every left rule preserves it.

    UnrefutedBelow G D Ω C  :=  D ⋫ (Ω →g C)  ∧
      ∃ Ω₀ ⊆ Ĝ.  Ω₀ ⊆ Cl(Ω)  ∧  D ⋫ (Ω₀ →g C)

Two facts make it the right invariant:

* `unrefutedBelow_of_gHat` — on a `Ĝ` context it IS (BSr1) (take
  `Ω₀ = Ω`), so nothing is lost where the paper's invariant holds;
* `unrefutedBelow_step` — at a `◯` goal it survives any context move
  `Ω ⊆ Cl(Ω')`, because `gbuInv14` turns the ancestor back into (BSr1)
  at `Ω'`.

With it, `L⊥ᵢ`, `L∧ᵢ` and `L∨ᵢ` are licensed and the non-`Ĝ` branch of
the search is proved outright, by `sfL_dec` on the offending member.
`unrefutedBelow_of_gHat` is axiom-free bar `[propext]`.

Negative test: weakening the `Ω₀ ⊆ Cl(Ω)` conjunct to plain membership
`Ω₀ ⊆ Ω` (same arity, so no shape error) breaks `unrefutedBelow_step` at
exactly the `clo_trans` transport. Restored, green; whole repo builds.

**Residues remaining: two.**

* **(S1) `BigAnte`** — `L⊃ᵢ` on an antecedent that both carries a `◯`
  and is too large for the measure.
* **(S3) `CleanReg`** — the clean-regular search that `R⊃ₙᵢ` releases
  into from the clean mode; its own residue is a critical context
  carrying a `◯` at a non-modal goal, where only the fallible joins
  apply.

The (S2) numbering is kept in the source so the three are still
distinguishable across the record.

## 2026-08-30k — S3 cannot be cleared: it is FALSE

`CleanReg` is not a gap to be filled. It is refuted, kernel-checked
(`not_cleanReg`, `[propext, Quot.sound]`), by the sharpest cell in the
development:

    G = ◯p ⊃ p,    Ψ = { ◯p },    C = p

* **`D ⋫ᶜ (Ψ ⇒g p)`** (`not_evalRC_circ_self`). A clean derivation of
  `Γ ⇒ p` with `◯p ∈ Cl(Γ)` contradicts `not_clean_of_clo_circ`: the root
  forces `◯p`, so SOME `Rm`-successor forces `p`; `tag_cone` says every
  PROPER successor refutes it; so that successor is the root, and the
  root forces `p`, contradicting `lemma39R`. This is exactly
  `tag_weakening_refuted`'s fact, now stated about the database.
* **But `Ψ ⇒g p` is not derivable** (`not_gbuRC_circ_self`): `soundRC`
  would give `◯p ⊨ p`, and `Kmc` refutes it.

**Consequence, stated plainly: Theorem 8◯ is currently VACUOUS for any
`G` with a modal subformula.** `searchO` takes `CleanReg G D` as a
hypothesis; that hypothesis is false; so the theorem asserts nothing
where it matters. §h reported the regular branch as proved, and it is —
but the theorem it sits in cannot be discharged along this route. The
correction belongs on the record.

**Where the fault is.** `CleanReg` is consumed at exactly one place:
`R⊃ₙᵢ` in the `cirr` mode. `cirr` at goal `A ⊃ B` with `¬ Cl(Ω) ∋ A` has
only `R⊃ₙᵢ`, whose premise is a REGULAR sequent — and the clean query
does not survive that release, because a clean row for `A :: Ω ⇒ B` need
not exist even when no clean row for `Ω ⇒ A ⊃ B` does. Putting the
antecedent into the context can introduce a `◯` whose body is the goal,
which is precisely the configuration `not_clean_of_clo_circ` forbids.

**What I did NOT settle.** The obvious repair is to have `cirr` carry
the parent's `D ⋫ (Ω →g ◯C)` alongside the clean query, so that
`R⊃ₙᵢ`'s premise can go to the PLAIN regular mode via `gbuInv9`. Whether
that is sound depends on a question I have not answered: is
`◯(◯p ⊃ p)` PLL-valid? If it is, then `⊢ ◯(◯p ⊃ p)` must be derivable,
the only applicable rule at `[] ⇒g ◯(◯p⊃p)` is `R◯`, its premise
`[] →g ◯p ⊃ p` is invalid, and **`Gbu◯` is incomplete** — a much sharper
finding than S3, and the one worth settling next. Semantic attempts to
refute `◯(◯p⊃p)` all collapsed (if `b ⊩ ◯p` then some `Rm`-successor
forces `p` and hence `◯p ⊃ p` by monotonicity; if `b ⊮ ◯p` the
implication tends to hold vacuously at `b` itself), which is evidence
FOR validity, but it is evidence, not a proof, and it is recorded here
as OPEN.

Residues now: **(S1) `BigAnte`** — still a genuine open obligation;
**(S3) `CleanReg`** — false, kept in the source only so the shape of the
obligation stays visible.

## 2026-08-30l — `◯(◯p ⊃ p)` is NOT valid; FRJV drove the countermodel

The question left OPEN in §k is closed, NEGATIVELY, and I got it wrong
twice over first.

**Matthew's argument.** If `◯(◯p ⊃ p)` were a theorem then so would be
its substitution instance at `p := ⊥`,

    ◯(◯⊥ ⊃ ⊥)  =  ◯¬◯⊥  =  q5  =  ρ7

and ρ7 is provably distinct from `⊤` in the ρ-order.

**The verdict was already in the repository.** `PLLND.RNC.rnc_ref_1_5`
(`wip/rncCert.lean:32`) kernel-checks `¬ ConfluentU.DerivU [q1] q5` on

    ⟨3, ≤ = [(1,0),(2,0),(2,1)], Rm = [(1,0)], Fal = {0}, V = ∅⟩,  w = 2

— a chain `w₂ ≤ w₁ ≤ w₀` with `w₀` fallible and one non-reflexive modal
edge `w₁ ⊳ w₀`. The standing rule (memory: RNC certificate lookup) is to
DECODE AND LOOK UP before searching. I did not. I asserted a semantic
hunch instead, recorded it as "evidence for validity", and it was wrong.
Second error, same turn: told to get a countermodel I hand-built a
Kripke structure by transcribing that certificate, which is not the
calculus finding anything. Matthew: "don't just construct a countermodel
from thin air. Drive FRJ◯ to find it."

**Driven.** `provableV_Gcc : ProvableV (◯(◯p ⊃ p))`, three steps, each
forced by the rule set, compiled first try:

| | rule | result | tag |
|---|---|---|---|
| 1 | `Ax^I`, then `⋈^At_F` | `◯p ⇒ p` | `blocked` |
| 2 | `⊃∉` with an EMPTY moveable zone | `∅ ; ∅ → ◯p ⊃ p` | — |
| 3 | `⋈^◯` | `∅ ⇒ ◯(◯p ⊃ p)` | `barren` |

Step 1 is the fallible atomic join, which keeps the whole modal zone —
the extracted world reaches `p` only through a fallible successor, which
is exactly why `◯p ⊃ p` fails there. Step 2's side condition
`¬ Cl(Θ) ∋ ◯p` is met by taking `Θ = ∅`: the antecedent is closed by the
PREMISE's context, not by the moveable zone. Step 3 must be the JOIN and
not `◯∈`, because step 1's tag is `blocked` and `not_clean_of_clo_circ`
forbids `◯∈` there. The dirty tag is the whole content of the cell.

Then `soundnessV` gives `not_pll_Gcc : ¬ PLL (◯(◯p ⊃ p))`, and
`modR_countermodel` gives `countermodel_Gcc : ∃ K, Countermodel K Gcc`
— the model EXTRACTED from the derivation, not transcribed into it. All
`[propext, Quot.sound]`, `#guard_msgs`-pinned; whole repo builds.

**Consequence for Gbu◯.** The incompleteness I feared in §k does not
arise: `⊢ ◯(◯p ⊃ p)` is not an obligation, so `R◯`'s irregular premise
is not refuted by that cell. The repair direction for (S3) is therefore
back on the table — have `cirr` carry the parent's `D ⋫ (Ω →g ◯C)`
alongside the clean query, so `R⊃ₙᵢ`'s premise can go to the PLAIN
regular mode via `gbuInv9`. That is the next thing to try.

## 2026-08-30m — S3 re-framed; four of its five cases discharged

**FRJV sweep, partial: no incompleteness found.** 205/462 cells run,
every banked `⊬` cell among them HIT, zero MISS. `tools/frjv-sweep-check.py`
(new, registered in `TOOLS.md` §3) closes the "compare externally" gap in
`sweepMain`'s docstring: it extracts the banked `⊬` cells from `RNDB/`
— `sepEntry`/`nleEntry`/`frjCertEntry`/`escEntry`, each a kernel-checked
`¬ Deriv [ρi] ρj`, so PLL-level — and joins them against the sweep. A
MISS on a banked cell is an incompleteness candidate; a HIT on a banked
`⊢` cell is a soundness alarm. Neither has appeared.

**S3: the approach was wrong, not just the statement.** I kept trying to
patch the search around a false hypothesis. `CleanReg` is false and
cannot be discharged; what makes the false nodes go away is an
INVARIANT, not a supply. The clean mode is entered from
`(irr, Ω, ◯C)` by `R◯ᵢ`, so it can carry the parent's
`D ⋫ (Ω →g ◯C)` — and the `◯p ⊃ p` cell that refutes `CleanReg` sits
under `(irr, ∅, ◯(◯p ⊃ p))`, which IS refutable (`provableV_Gcc`), so
that node is unreachable on a saturated database.

Two new results carry it:

* **`gbu_of_clo`** (`[propext]`) — `Cl(Ψ) ∋ C` implies both `Ψ ⇒g C` and
  `Ψ →g C`, stated over any supercontext so `R⊃ₙᵢ` can extend it. `Clo`
  has introduction clauses only and `Gbu◯` has a rule for each, so this
  part of the obligation needs no database at all.
* **`evalI_circ_and1/_and2/_imp/_circ`** — the `◯`-goal refutation lifts
  along the clean mode's own rules. Both `FRJVi` rules that conclude a
  `◯` goal cooperate: `◯∉` because `∧R`/`⊃∈`/`◯∈` keep the tag and
  `Covers` has a clause for each, and `Ax^I◯` because `classForce` is a
  homomorphism for exactly those connectives — the antecedent's value in
  the `⊃` case coming from `clo_classForce`.

**Four of the five `cirr` rules therefore maintain the invariant.** The
residue is one rule:

| rule | premise | lifts? |
|---|---|---|
| `R∧ᵢ` | `Cᵢ` | ✓ `evalI_circ_and1/2` |
| `R∨ᵢ` | `Cᵢ`, into `irr` | ✓ nothing needed |
| `R⊃ᵢ` | `B` | ✓ `evalI_circ_imp` |
| `R◯ᵢ` | `Z` | ✓ `evalI_circ_circ` |
| **`R⊃ₙᵢ`** | `B` at `A :: Ω`, REGULAR | **✗** |

`R⊃ₙᵢ` needs `D ▷ (A,Ω ⇒g B) ⟹ D ▷ (Ω →g ◯(A ⊃ B))`. `gbuInv9` gets as
far as `D ▷ (Ω →g A ⊃ B)`; the missing step is from there to the modal
goal. `◯∉` would need a CLEAN REGULAR row for `A ⊃ B`, which an
irregular one does not give, and `⊃∈` propagates its premise's tag —
dirty here, because the premise carries a `◯`-antecedent
(`not_clean_of_clo_circ`).

Semantically the step is unproblematic: a world refuting `A ⊃ B` sits
above a fresh barren root that also refutes it (forcing is monotone
upward), and a barren root discharges every `tag_cone` obligation
vacuously. So what FRJV lacks is a way to introduce a fresh barren root
below an existing refutation while keeping a chosen `Ĝ`-context — the
regular-side analogue of what `⋈^◯` does modally. That is a CALCULUS
proposal, not a search fix, and it is now the live question for FRJV
completeness. Not implemented: changing a rule's form is Matthew's call,
and this one needs its own soundness case (the fresh root must force the
kept context, which is exactly the `Λ*` obligation).

## 2026-08-30n — S3 without amending the calculus: carry the PLAIN query

Matthew: "is there ANY other way to deal with `R⊃ₙᵢ` without amending
the original calculus?" There is, and it needs no new lemma at all for
that rule.

**The clean mode should carry `¬ D ▷ (Ω ⇒g C)`, not `¬ D ▷ᶜ (Ω ⇒g C)`.**
The plain query is strictly stronger (`evalR_of_evalRC`), so nothing is
lost — and `R⊃ₙᵢ`'s REGULAR premise then gets its own (BSr1) directly
from a lemma proved back in the IPC layer:

    gbuInv6 :  D ▷ (A,Ω ⇒g B)  →  D ▷ (Ω ⇒g A ⊃ B)

No new rule, no changed rule, no supply. Checking the rest, the plain
query propagates through every `cirr` rule by an existing inversion —
`gbuInv2` at `R∧ᵢ`, `gbuInv5` at `R⊃ᵢ`, `gbuInv6` at `R⊃ₙᵢ`; the prime
and `∨` cases close by contradiction via `refutedCleanly_at`/`_or` —
with ONE exception: `R◯ᵢ`, which needs

    D ▷ (Ω ⇒g Z)  →  D ▷ (Ω ⇒g ◯Z)

i.e. Lemma 9 clause 12. That clause is REFUTED in general
(`rcirc_not_invertible`) — **but its counterexample is `Gtc` with
`Ψ = {◯p}`, a context CARRYING a `◯`**, and the clean mode's contexts
are `Ω ⊆ Ĝ_at ∪ Ĝ_imp`, `◯`-free. The counterexample does not reach the
case that is needed. So the residue is the restricted clause:

**(★) `Ω ⊆ Ĝ_at ∪ Ĝ_imp`, every antecedent of `Ω`'s implications
refuted, `◯Z ∈ Sf^R(G)`: `D ▷ (Ω ⇒g Z)` ⟹ `D ▷ (Ω ⇒g ◯Z)`.**

and since `refutedCleanly_circIn` already lifts a CLEAN row through
`◯∈`, (★) follows from

**(★★) under the same hypotheses, `D ▷ (Ω ⇒g Z)` ⟹ `D ▷ᶜ (Ω ⇒g Z)`**

— on a critical `◯`-free context with dead implications, every
refutation can be taken CLEAN. Plausible for the right reason: the
suppliers available there are `refutedCleanly_at`, `refutedCleanly_or`
and the shape lifts, and every one of them concludes at `barren`.

So the whole of S3 now rests on ONE database lemma, provable or
refutable without touching a rule. The amendment I proposed in §m (a
fresh-barren-root rule) is NOT needed unless (★★) turns out false.

Sweep meanwhile: 205+/462 cells, every banked ⊬ cell HIT, zero MISS.

## 2026-08-31a — (★★) REFUTED; and the sweep finished with SIX misses

### (★★) is false

`not_starstar` (`wip/gbu_weakening.lean`, `[propext, Quot.sound]`).
Instance: `G = ◯p ⊃ p`, `Ω = ∅`, `Z = ◯p ⊃ p`.

* The hypotheses hold trivially — `∅` is critical, `◯`-free, and has no
  implications at all, so the `Υ` condition is vacuous.
* `∅ ⇒ ◯p ⊃ p` IS refutable: `⋈^At_F` then `⊃∈` (`evalR_imp_self`).
* It is NOT cleanly refutable (`not_refutedCleanly_imp_self`): `⊃∈`
  propagates its premise's tag, and the premise's context closes `◯p`,
  which `not_clean_of_clo_circ` makes dirty. The `chain` escape —
  pledging the GOAL — is closed by `tag_cone`: the modal successor `◯p`
  supplies forces `p`, hence forces `◯p ⊃ p`, so it cannot be a proper
  cone member of a `chain (◯p ⊃ p)` root.

The `⊃` case is exactly where an induction proving (★★) would leave its
own hypotheses, since `⊃∈` hands the sub-derivation the context `A :: Ω`.
Refute-first found it in the first place I looked.

### (★) survives, and the reduction was the error

Reducing (★) to (★★) through `refutedCleanly_circIn` was too LOSSY: it
demanded a CLEAN row where (★) needs only a row. At the (★★)
counterexample (★) is not even in scope (`◯(◯p ⊃ p) ∉ Sf^R(◯p ⊃ p)`),
and at the `G` where it is — `Gcc = ◯(◯p ⊃ p)` — its conclusion holds
outright, by `provableV_Gcc`. The corrected target is

**(★′) `D ▷ (Ω ⇒g Z)` ⟹ `D ▷ (Ω →g Z)`** over a critical `◯`-free
context with dead implications,

after which `gbuSuccCirc` (`⋈^◯`, which concludes at `barren`) gives
`D ▷ (Ω ⇒g ◯Z)` with no cleanliness demand. (★′) holds at the (★★)
counterexample by `⊃∉` with an empty moveable zone — step 2 of
`provableV_Gcc`.

### The sweep finished: SIX candidate incompleteness witnesses

462/462 cells. 280 banked `⊬` cells; **274 HIT, 6 MISS**:

    ρ12 ⊬ ρ18    ρ13 ⊬ ρ18    ρ19 ⊬ ρ18
    ρ20 ⊬ ρ12    ρ20 ⊬ ρ13    ρ20 ⊬ ρ18

This CORRECTS the interim reports in §m and §n, which said zero misses —
the misses are concentrated late in the matrix and the partial runs had
not reached them.

These are not budget artefacts. Every one reports `r=8` against
`rounds=12` with `lamCapped=false dbCapped=false`, i.e. the saturation
reached a FIXPOINT before the round cap; re-run at `maxRS/IS=20000` the
first still misses at `r=8`. A higher-budget pass (rounds=30, lamCap=60)
is running.

Five of the six target ρ18 = `((◯¬◯⊥ ∨ ¬¬◯⊥) ⊃ (◯⊥ ∨ ¬◯⊥)) ∨
(◯¬◯⊥ ∨ ¬¬◯⊥)` — a DISJUNCTION — and three have ρ20 = `q8 ⊃ q7` as
source. A disjunctive goal is refuted by `⋈^∨`, so the shape to
interrogate first is the `∨`-join's side conditions.

Standing caveat (TOOLS.md): a MISS is not-found-within-bound, never a
verdict. But a converged saturation with no binding cap is much stronger
evidence than a timeout, and six of them clustered on one target is a
pattern, not noise. **The working assumption that FRJV is complete is no
longer safe**, and these six cells are the place to settle it.

## 2026-08-31b — the ∨-join hypothesis was WRONG; two true theorems, no explanation yet

I proposed that the six misses come from `⋈^∨`'s irregular premises.
**The sweep's own data refutes that**, and I should have looked before
building: `VCELL 1 9 HIT` and `VCELL 1 18 HIT` — FRJV refutes both
`q9 = ◯¬◯⊥ ∨ ¬¬◯⊥` and `ρ18` from `⊤`. My step "`⋈^∨` needs an
irregular refutation of each disjunct" is false: the disjunct condition
is `RefAt`, which is deliberately RELAXED (that is what "`RefAt`-relaxed
disjunct conditions" means in the rule's own docstring), so a disjunct
need not be any premise's `rhs`.

Two theorems came out of the attempt. They are TRUE and pinned, and they
do not explain the misses:

* **`not_clean_imp_self`** — `◯Z ⊃ Z` has no cleanly tagged regular
  refutation, for ANY `Z`. `⊃∈` propagates its premise's tag and the
  premise's context closes `◯Z`; the `chain` escape (pledging the goal)
  is closed by `tag_cone`, since the successor `◯Z` supplies forces `Z`
  and hence forces `◯Z ⊃ Z`. This generalises
  `not_refutedCleanly_imp_self` off the atom.
* **`no_irregular_circ_imp_self`** — `◯(◯Z ⊃ Z)` has no irregular
  refutation at all. Only `◯∉` and `Ax^I◯` conclude a `◯` goal; `◯∉`
  needs the clean row the previous theorem forbids, and `Ax^I◯` needs
  `classForce ats (◯Z ⊃ Z) = false`, impossible because `◯` is
  transparent to `classForce` and the body is the classical tautology
  `¬x ∨ x`.

Both `[propext, Quot.sound]`. `q5 = ρ7 = ◯¬◯⊥` is this shape at `Z := ⊥`,
so `ρ7` is irregularly irrefutable — a real structural fact about FRJV,
just not the one that explains the sweep.

**What the data actually says.** The six banked misses are

    (12,18) (13,18) (19,18) (20,12) (20,13) (20,18)

Four target ρ18, three have ρ20 as source — but `⊤ ⊃ ρ18` HITs, and each
of ρ12, ρ13, ρ19, ρ20 hits 15–18 other targets. So neither the goal
shape nor the source alone discriminates: it is the PAIR. The next step
is data, not another hypothesis — `lake exe frjvrun cell 12 18` dumps
the saturated database's regular rows for one miss, and that is running.

## 2026-08-31c — (★) resolved by refutation of the specification it served

Directive: "now go back to proving (★)".  (★) is not provable-or-refutable
as posed, because it is not needed and because the clause it was meant to
repair is itself false.  Two results, both in `wip/gbu_search_circ.lean`,
both `[propext, Quot.sound]`.

**1. (★) is unnecessary.**  It arose only in the redesign of the `cirr`
mode that carries the plain regular query, at `R◯ᵢ`.  But `rcircI`'s
premise is IRREGULAR, and the `irr` mode accepts it directly — the query
transfers by the already-proved

    gbuSuccCirc :  D ▷ (Ω →g Z)  ⟹  D ▷ (Ω ⇒g ◯Z)

whose contrapositive IS (BSr1) for the premise.  Recorded as

    cirr_circ_to_irr :  Ω ⊆ Ĝ_at ∪ Ĝ_imp → ◯Z ∈ Sf^R(G) →
      (∀ A ⊃ B ∈ Ω, D ▷ (Ω →g A)) → ¬ D ▷ (Ω ⇒g ◯Z) →
      UnrefutedBelow G D Ω Z

With `R⊃ₙᵢ` closed by `gbuInv6` (§2026-08-31a), the `cirr` mode needs
neither (S3) nor (★).

**2. The `irr` clause of `SearchOkO` is FALSE**, at a cell neither mode
touches: `G = Ω-goal = Gcc = ◯(◯p ⊃ p)`, `Ω = ∅`.  Both sides of the
irregular duality are empty.

* `not_evalI_Gcc : ¬ EvalI (FDerivable G) Ω Gcc` — for EVERY `G` and
  EVERY `Ω`, from `no_irregular_circ_imp_self` (§2026-08-31b).
* `not_gbuIC_Gcc : ¬ Nonempty (GbuIC G [] Gcc)` — and this is FORCED:
  `soundIC` gives the irregular judgment the same semantic reading as
  the regular one, `∀w. w ⊩ Ψ → w ⊩ C`, and `Gcc` is refuted by the
  model `GccWitness` extracts (`countermodel_Gcc`).
* hence `not_searchOkO_irr : ¬ SearchOkO Gcc (FDerivable Gcc) (.irr, [], Gcc)`
* hence `residues_unsatisfiable` : for any decidability suppliers,
  `¬ (BigAnte Gcc D ∧ CleanReg Gcc D)`.  The residues are not open —
  they are jointly unsatisfiable, so no discharge of (S1)/(S3) and no
  repair of `cirr` can make `searchO` non-vacuous for modal `G`.

The `∨` case of the regular mode makes this reachable rather than an
artefact of the ∀-statement: it picks a disjunct by testing
`D ▷ (Ω →g Cᵢ)`, and by `not_evalI_Gcc` that test can NEVER succeed at
`Cᵢ = ◯(◯Z ⊃ Z)`, so the search commits to such a disjunct
unconditionally, whatever is available on the right.

**Diagnosis.**  The fault is on the FRJV side: an incompleteness of the
IRREGULAR judgment.  `⊬ ◯(◯Z ⊃ Z)`, yet FRJV has no irregular refutation
of it, because `◯∉` demands a clean regular row for `◯Z ⊃ Z` and
`not_clean_imp_self` forbids one.

**Calculus proposal, for review — NOT implemented.**  A fresh barren
root below an existing refutation, keeping a chosen `Ĝ`-context:

        Γ ⇒ C          Θ ⊆ Ĝ,   Θ ⊆ Cl(Γ)
    ─────────────────────────────────────────  (R^bar)
                    Θ → C

i.e. `◯∉` with the cleanliness DEMAND replaced by the CONSTRUCTION of a
clean root.  Soundness obligation: the fresh root forces `Θ`, refutes
`C`, and has modal cone `{root}`.  The third conjunct is the one to
screen first — `◯` refutation at the new root quantifies over the whole
upper cone, not just the root.

## 2026-08-31d — FRJW opens; see `docs/frjw-plan.md`

New campaign, new branch `frjw-dev`. The plan document is
`docs/frjw-plan.md` and it is self-contained: what FRJW is (FRJV plus
`Lift`, minus `⊃∉`), why, what is already machine-checked, and stages
W1–W6 with their obligations. Read that, not this file, to start.

Terminology fixed here: an object of `FRJVr`/`FRJVi` is a **disproof**,
regular or irregular. "Proof" is reserved for the provability calculi
— Gbu◯, LaxND, G4c, SC. `ProvableV G` reads the wrong way round: it
means *G has an FRJV disproof*.

Retired, do not inherit: `searchO`, `BigAnte`, `CleanReg`
(`residues_unsatisfiable`).

## 2026-08-31e — route change: Gbu◯ completeness via LJF◯ focalisation

FRJW W1–W4 are DONE and pushed on `frjw-dev` (family + conservativity +
fresh soundness `soundnessW` + the duality-gap witness at `◯(◯p ⊃ p)`),
with the pre-W5 check `wip/gbu_ndrules.lean`: SC's `laxL` is a derived
rule of Gbu◯ in both judgments; `laxR` over an irregular premise is
`rcirc`/`rcircI` verbatim; `laxR` at the regular judgment is OPEN and
is focalization-shaped (sticks at `randR`/`rimpI` polarity, resp.
`limpLI`'s size condition).

Matthew's decision: do NOT pursue completeness through the FRJ
database/search route (old W5/W6) — previous attempts kept failing
there.  Go via **LJF◯ focalisation**: `bridge_iff` in `LJF/OBridge.lean`
(already on `frjw-dev`; the calculus map's "unmerged t1 branch" note was
stale and is corrected) gives `LaxND ↔ LJF◯`; the new work is a
structural translation `T : LJF◯ → Gbu◯`, then
`gbuC_complete : Nonempty (LaxND [] φ) → ProvableGbuC (ofPLL φ)`.

The full amended plan — chain, judgment map, risk register R1–R3
(antecedent hyper-focus at `LFoc.impL`; `limpLI`'s size condition;
`Sf`/`Clo` plumbing), stages F1–F4, and what stands down — is the
"Route change" section of `docs/frjw-plan.md`.  Read that to continue.

## 2026-08-31f — F4 PROVED: Gbu◯ is complete in itself

    gbuC_complete : Nonempty (LaxND [] φ) → ProvableGbuC (ofPLL φ)

Sorry-free, `#guard_msgs`-pinned **[propext, Quot.sound]** (choice-free),
in `wip/gbu_ljfo.lean`; support/transport in
`wip/gbu_ljfo_support.lean` / `wip/gbu_ljfo_transport.lean`.  Route:
`bridge_iff` (LJF◯ focalisation) → `tInv` (mode-generic CPS translation
LJF◯ → Gbu◯; the `Kit` two-mode architecture, forced by two
kernel-checked screens: `GbuIC` non-monotone, no modus ponens) →
`nf_negOfO`.  The licenced `|◯C|` adaptation of `GbuIC.limpLI` is
consumed at exactly one site (`irrKit.impOpen`).  Full stage record
appended to the "Route change" section of `docs/frjw-plan.md`.
