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
