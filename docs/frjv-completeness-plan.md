# FRJV completeness plan — statement (A) for the repaired calculus

**Status: PLAN APPROVED by Matthew 2026-08-26 ("go ahead with the
unconditional statement; repair₂ if S0 forces it").  The target is the
unconditional statement (A) below; the `EndpointsV` fallback of route
step 2 remains a fallback, not the declared goal.  Free transfer
baseline landed (`FRJ/CompleteV.lean`, commit `3ceec1c`).**

Goal issued by Matthew 2026-08-26 ("complete a completeness proof for
FRJV", `docs/refat-plan.md` review section).  Base: the repaired
calculus `FRJVr`/`FRJVi` (`FRJ/CalculusV.lean`), soundness
`FRJ.soundnessV` PROVED `[propext, Quot.sound]`.

## The target statement

    completenessV : ∀ {K : Kripke} {G : Form}, ¬ K.valid G → ProvableV G

`Kripke` is finite by construction (`elems`/`complete`,
`FRJ/Basic.lean:204`), so this is the fully unconditional statement (A)
for the repaired calculus — the statement that is REFUTED for the paper
family (`FRJ80.not_CompletenessFRJ`).  With `soundnessV` it would give

    ProvableV G  ↔  ∃ K, ¬ K.valid G        (FRJV = countermodel search)

and through the bridge (`FRJ/BridgeV.lean` + PLL semantic completeness)

    [] ⊬ φ  →  ProvableV (ofPLL φ).

STATUS: OPEN.  Per the standing rule it gets NO Lean declaration until
proved or refuted; this file is the record of the campaign.

## Why it might be true — and the known threat

FOR: (i) the paper family is complete on endpoint-seeing frames with no
supply (`completeness_of_endpoints`, unconditional; transfers to `FRJV`
as `completenessV_of_endpoints`); the open territory is exactly frames
with `id ⊊ Rm ⊊ ≤` failing `Endpoints`.  (ii) On such frames the paper
construction needed the two open supplies, and the RefAt kept zone
removes their raison d'être at barren joins: a `Λ*`-circ `◯Y` with
`a ⊩ ◯Y`, `a ⊮ Y` — the configuration that FORCED promise joins
(`docs/frj-w4.md` §11 fourth addendum, "there is no retention-free
route") — is keepable in a V-barren join via the ◯-clause of `RefAt`
(`Y` is refuted at the join world, so `◯Y ∈ RefAt` through Υ).  The
kernel-checked G80 witness (`FRJ/WitnessV.lean`) exercises exactly this.
(iii) The V-engine sweep: 297/303 kernel-refutable ρ-cells derived,
0 alarms.

AGAINST (the threat): the 6-cell sweep residue — (ρ12,ρ18), (ρ13,ρ18),
(ρ19,ρ18), (ρ20,ρ12), (ρ20,ρ13), (ρ20,ρ18), all kernel-refutable, all
missed at sweep budget with jmax/pmax binding.  Frame analysis
(2026-08-26): (ρ12,ρ18)/(ρ13,ρ18) are refuted on sepM itself (one modal
edge — the frame the witnesses already build; plausibly budget misses);
the other four are refuted only on frames with TWO non-reflexive modal
edges at distinct worlds ((1R2,4R3) and (1R4,2R3) variants, one fallible
world), i.e. two promise-style rows — and the promise/fallible joins are
UNCHANGED in FRJV (divergence V3).  If any of the four survives a
cap-free closure underived, statement (A) is likely refutable for FRJV
and the campaign target becomes repair₂ (RefAt at the promise joins)
before any completeness proof.

## Screening before proving (gating, in order)

S0. **Six-cell raised-budget ladder** (RUNNING, untyped engine
    `frjxrun cellat`, rounds 16→20, lamCap 20→24, jmax 4→5, pmax 3→4,
    RS/IS 8000; `none_at` discipline — a run is evidence only if no cap
    binds).  Outcomes: all six HIT → threat retired, proceed.  Any
    cap-free MISS → attempt a `¬ ProvableV` kernel proof for that cell
    (the #80/#81 template over the V-family) → statement refuted →
    repair₂ first.
S1. **Corner probes**: re-run the 28 CircSupply-corner probes
    (`docs/frj-w4.md` §11 third addendum) against the V-engine; the
    stuck configuration `cone(a) = {a}`, `a ⊮ Z`, `∀ v > a : v ⊩ ◯Z`
    is where the §9 induction cycle lives.
S2. Only then scope the proof build.

## The proof route (deliverables, once screening passes)

1. `FRJ/SaturateV.lean` — the V-witness grades (`MRWitV`/`FRWitV` over
   `FRJVr`) and the ported case builders.  Only two builders change
   shape: `metR_primeV` and `metR_orV`, which take the V-barren joins
   WITHOUT `hloc : circPart (lamStar K a G) = []`.  Their new
   obligation, the SEMANTIC RETENTION LEMMA, is the heart of the
   campaign:

       given: rows for the Υ-zone (refuted-at-a members), the join
       base, and the Λ*_a data (each ◯Y ∈ Λ* has a ⊩ ◯Y, a ⊮ Y)
       build: kept ⊇ the Λ*-implications and Λ*-circs, with
       `KeptChain (Υ) base pool kept` certified from the semantic
       refutations (◯-clause for circs, Cl/Υ-clauses for implications)

   discharging at one stroke what `hloc`, `PledgeSupply` and the fat
   (J7) restriction each worked around.
2. The corner: a V-analogue of the `CircSupply` discharge.  The §9
   cycle `I(◯Z)@a → R(Z)@a → I(Y)@a → I(◯Z)@a` must be broken by the
   V-row route (`metI_circ_syn` over a V-joinAt row whose kept zone is
   certified by deliverable 1) — the measure analysis
   (`(ht, t, size)`) is the risky step.  FALLBACK if it does not
   close: a WEAKER frame condition `EndpointsV ⊋ Endpoints` with the
   residual class characterised, landed as a conditional theorem (still
   strictly beyond the paper family), and the residual class attacked
   by countermodel search.
3. `visitV`/`completenessV` assembly (mirroring `visit`/`visitMax`/
   `visitG`; expected to SIMPLIFY: with retention free, the graded
   FRWit tier may be unnecessary).
4. Audit: pins in `FRJ/AuditV.lean` (`[propext, Quot.sound]`,
   choice-free), negative-tested; `#slime` stays 0; divergence log
   in `docs/refat-plan.md` extended if any rule is touched (none is
   expected to be — this campaign writes NO new calculus rules).
5. End-to-end validation: the six residue cells re-derived THROUGH
   `completenessV` applied to their banked countermodels; the 462-cell
   sweep replayed with the typed V-engine.

## Non-scope

Repair₂ (RefAt at promise/fallible joins) unless S0 forces it;
FRJV cut-type results; the erasure route (E) (superseded on this
front if (A) lands, though its transparent-frame use stands); engine
Fast/Profile ports; unifying the FRJ/FRJV families.

## Fidelity

No new rules and no rule changes are proposed: the campaign proves a
theorem ABOUT `FRJV` as already reviewed.  Any discovered need to touch
a rule is a STOP: back to Matthew with the failure analysis.

## Route revision — 2026-08-26 statement screen (REFUTATION of route step 1)

The frj-w4 §§8–16 design-doc audit plus two probes settled the route
BEFORE the proof build, and the original route step 1 is DEAD:

* **REFUTED: "kept ⊇ the Λ*-circs".**  Kept members are implications
  only (`KeptChain` pool = `thPool = impPart (interAll th)`;
  `keptChain_isImp`), and the barren V-bases carry no modal zone, so a
  barren V-join's conclusion context contains NO ◯-formula and — since
  `MRWit.cov` is literal containment — a barren V-join can never serve
  a circ-carrying world.  The RefAt ◯-clause certifies kept ANTECEDENTS
  and join disjunct/body conditions, never retention of a ◯.  The
  "Why it might be true" claim (ii) above is withdrawn accordingly.
* **REFUTED: Lemma A as stated.**  `PledgeFam K G a F` is uninhabited
  whenever `◯F ∈ Λ*_a`: kernel theorem
  `FRJ.V.not_pledgeFam_of_circ_mem` (`FRJ/SaturateV.lean`, from
  `lemma39R` + `preR_root_lbl` + `clo_forces`), realised concretely on
  sepM/G80/F=⊥ (`wip/frjv_pledge_refute.lean`, pinned).  So
  `∀ K G, V.PledgeSupply K G` is FALSE and `completeness_of_supply` is
  vacuous on the very frames at issue — this is the §13
  provably-unsatisfiable instance, now in the kernel.
* **Corner probe** (`wip/frjv_corner_probe.lean`): on all four residue
  frames every `CircSupply` demand is `Z = ⊥` with the `axIC`
  empty-valuation route available (incl. the non-maximal fires on
  frame 9900) — Lemma B never blocks on the residue corpus.

REVISED ROUTE (unconditional target unchanged):

1'. **Lemma A′ (transported-cov pledge)** — the §13 refinement designed
    2026-08-17 and never built: parameterise the pledge family by the
    DEMANDING world `b` (`hlam`/`hbody` over `lamStar K b G`; the
    demand has `b ⊮ ◯F`, so `◯F ∉ Λ*_b` and the defect site vanishes),
    thread a demand-origin parameter through the tagged tier of
    `visit`.  Three of four fields come free
    (`exists_common_witness_list` + `clo_mono`/`lamStar_mono` +
    `mem_clo_lamStar`; recursion legal, `ht` strictly drops at the
    common witness).  THE one semantic question left: at a
    circ-carrying anchor `a` for prime demand `F`, does the common
    witness `u ∈ cone(a)` (forcing all Λ*-circ bodies) refute `F`?
    Screen it on the residue frames before proving (next probe).
2'. **The ⊥-pledge pattern** (from the ρ12⊬ρ15 witness, node `Q`):
    pledge `⊥` and consume tag-blind through `impNotIn` — a promise
    row any infallible successor can fill.  Unformalised; candidate
    fallback where A′'s semantic question fails.
3'. Lemma B unchanged: `circWit_of_maximal` + `axIC` chosen-valuation +
    `metI_circ_syn` + the self-destruction argument; already closed on
    cone-grounded and Endpoints frames.

## Demand-trace stage (2026-08-26 evening, wip/frjv_demand_trace.lean)

A visit simulator traced the V-routed demand graph on all four residue
frames.  V-routing = three repair-exploiting deviations from the paper
visit, each grounded in a kernel witness: (i) ∨-join disjunct
conditions are `RefAt`, so their row demands are the RefAt-descent
LEAVES (the G80 ROOT: σ needs only the irregular ν-row, no tagged
◯-machinery); (ii) `axIC` serves `I(◯Z)` at ANY world whose `Λ*` is
classically satisfiable with `Z` refuted, not corner-only (the G80 R2
node); (iii) irregular ⊃-floats land in the FREE tier (fallible joins,
no pledge).

RESULT: frame 9900 (both cells) and (20,13) trace CLEAN — no pledges,
corners, or floats.  The RESIDUAL bad path (sepM ×3, (20,12)):

    I(◯⊥)@1 with Λ*₁ = {ρ12, δ}: cl(δ) = false blocks axIC; not a
    corner; minRef escalates to tagged ⊥@2 — the dead pledge.

The G80 kernel witness serves this exact demand: `R2 = axIC ⊥ []` used
as a ROW inside `R4 = joinAt {T2, R2}` — legitimate because the join
needs only pairwise hJ1 (T2's stab {ν} is classically true), not the
visit's blanket Λ*-coverage.  CONCLUSION: the paper visit's wit
invariants (`IrrWit.cov`/`MRWit.cov` = Λ*-coverage) are sufficient but
NOT necessary, and they are what manufactures the unsatisfiable pledge.
The construction must run on WEAKENED invariants reverse-engineered
from the witness pattern:

1''. Formulate the V-wit invariants: rows either Λ*-covering OR
     axIC-shaped (stab = [], th = vacZone), with the join discipline
     "every sibling stab classically true at the axIC valuation";
     floats absorbed by `impNotIn` (tag-blind).
2''. Re-run the visit port on the weakened wits; the pledge machinery
     (`metR_primeP`/`metR_orP` + `PledgeSupply`) should fall out of the
     construction entirely — matching the ablation datum that promise
     joins were never needed on the 32-cell corpus.
3''. The demand tracer is the screen: any frame/goal whose trace shows
     a demand the weakened wits cannot serve is a counterexample
     candidate BEFORE proof work resumes.
