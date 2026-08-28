# RefAt mechanisation plan — the vacuous-retention extension of FRJ(◯)

**Status: DELIVERED 2026-08-25 (same session; Matthew's review of this
plan is PENDING — flagged per the calculus-adoption gate, which normally
requires review before Lean.  Everything on branch
`claude/frj-incompleteness-80-81-251e7f`, nothing merged.)  Deliverable
status: 1–6 ALL LANDED, sorry-free, pins green (`FRJ/AuditV.lean`,
negative-tested); `#slime` reports 0 on both V-families; `refAt_refutes`
is AXIOM-FREE, `keptOf_ok` `[propext]`, `soundnessV`
`[propext, Quot.sound]`.  The functor+paperOps differential agrees with
the legacy engine row-for-row on 8 goals; the typed V-engine derives
#80/#81 and (spot-checks) 4/4 known-refutable sample cells, misses the
ρ20⊢?ρ12 residue cell as expected, and derives the open cell ρ12⊢?ρ15.
End-to-end: `wip/frjv_consequences.lean` re-derives ¬Deriv[ρ12]ρ9 and
¬Deriv[ρ13]ρ6 THROUGH the repaired calculus (witness ∘ soundnessV ∘
bridge), a third independent kernel route.**

Source: not a paper — our own repair, designed and extensionally screened
2026-08-25 (session report artifact "FRJ(◯) Witnesses 80 and 81",
HANDOFF.md §2026-08-25c).  The base calculus is the FRJ(◯) of
`FRJ/Calculus.lean` (Fiorentini–Ferrari TOCL 2020 + the W4 modal devices).

## The capability

The paper calculus PROVABLY misses refutable formulas
(`FRJ80.frj_incompleteness_80`, `FRJ81.frj_incompleteness_81`,
`FRJ80.not_CompletenessFRJ` — all kernel-checked).  The repair, validated
by the untyped probe engine (`wip/frjx.lean`: both witnesses derived,
462-cell sweep, 0 alarms, 297/303): replace the three "refuted at the new
root" tests of the BARREN joins by membership in

    RefAt(Υ, ctx) ::= Υ | ⊥ | A⊃B (A ∈ Cl(ctx), B ∈ RefAt)
                    | ◯Z (Z ∈ RefAt; barren cone only) | ∨ both | ∧ either

used in ⋈^∨'s hC, ⋈^◯'s hZ, and the Θ^⊃/Υ retention (which becomes a
STRATIFIED chain: each kept implication's antecedent is RefAt over the
base context plus the EARLIER kept members — the stratification is
load-bearing; mutually-justifying kept sets are NOT screened sound and
are excluded by the chain condition).

## Architectural decision (recorded, with the supersession check)

The extension CANNOT be new constructors on `FRJr`/`FRJi`: `Provable` would
silently change meaning and the two incompleteness theorems (whose `cases`
are exhaustive over the paper family) would break — they are theorems
ABOUT the paper calculus and must survive verbatim.  So:

* a SEPARATE mutual family `FRJVr`/`FRJVi` (`FRJ/CalculusV.lean`), all
  constructors as in the paper family except the three barren joins,
  which take an explicit `kept` zone with a `KeptChain` certificate and
  RefAt-relaxed hC/hZ.  The paper rules are the special case
  (kept = Θ^⊃/Υ, every antecedent in Υ by the base clause), witnessed by
  an embedding `toV : FRJr → FRJVr`.
* NOTHING is superseded: `FRJ/Calculus.lean` + `Sound.lean` remain the
  fidelity anchor to the paper and the subject of the incompleteness
  theorems; `FRJV` is the repaired calculus.  Constraints the old family
  discharges (paper fidelity, the ¬Provable theorems, every existing
  completeness-side result, all Audit pins) are each retained by keeping
  it untouched; `FRJV` adds capability only.
* engines become a FUNCTOR over the calculus: `FRJ/Search/Core.lean`
  takes the rule operations as an input structure (`Ops G`), with two
  instances — the paper calculus (the existing step/join functions) and
  the RefAt calculus.  A typed hit in the V-instance is a derivation, so
  `soundnessV` makes every hit sound BY CONSTRUCTION — no alarm sweep
  needed for the typed engine.

## Numbered deliverables

1. `FRJ/RefAt.lean` — `RefAt` (cone-gated inductive), decider
   `refAtB` + iff, `KeptChain`, the computed fixpoint chain and its
   certificate, and the semantic kill lemma
   `refAt_refutes : (∀C∈Υ, ¬force r C) → forces r ctx →
    (∀c, Rm r c → c = r) → ¬Fal r → RefAt true Υ ctx X → ¬force r X`.
2. `FRJ/CalculusV.lean` — `FRJVr`/`FRJVi`, transport, `ProvableV`,
   `toV` embedding (paper ⊆ repaired).
3. `FRJ/ExtractV.lean` — `preRV`/`preIV`/`modRV`; the V-join root is
   labelled `base ++ kept`.
4. `FRJ/SoundV.lean` — `lemma39RV`, `tag_coneV`,
   `soundnessV : ProvableV G → ¬ PLL G`.  Proof layering for the three
   V-join cases: (i) the existing size induction gives base-(P2) and
   (P3) unchanged (kept feeds neither); (ii) chain induction over
   `KeptChain` gives forcing of the kept zone at the root, the at-root
   step by `refAt_refutes` (Υ-refutations := (P3), context forcing :=
   base + earlier links); (iii) hC/hZ by `refAt_refutes` over the full
   context.  Choice-free throughout; pins `[propext, Quot.sound]`.
5. `FRJ/Search/Core.lean` — the engine functor; paper instance
   differential-identical to the legacy engine; V instance derives both
   witnesses; witness derivations ALSO pinned as hand terms
   (`ProvableV G80`, `ProvableV G81`) so the repair is kernel-checked
   end to end: `soundnessV` applied to them re-derives ¬PLL G80/G81.
6. `FRJ/AuditV.lean` — `#guard_msgs` axiom pins for 1–5; `#slime` clean
   on the new family; divergence log below kept current.

## Fidelity / divergence log

| # | Divergence from the PAPER | Where | Why |
|---|---|---|---|
| V1 | kept zone + `KeptChain` replaces `Θ^⊃/Υ` in ⋈^At, ⋈^∨ | CalculusV | ours; the witnesses' vacuous-retention gap |
| V2 | hC/hZ via `RefAt` instead of `∈ Υ` (barren joins) | CalculusV | ours; #80 needs the ◯-clause |
| V3 | promise/fallible joins UNCHANGED (no ◯-clause is sound there; the rest not needed) | CalculusV | scope control |
| V4 | everything already diverging in `FRJ/Calculus.lean` (⋈^◯, ⋈^◯p, Ax^I◯, tags) carries over verbatim | CalculusV | inherited |
| V5 | **round 3 (2026-08-27), REVERTED same day**: (J2) on the three barren joins was relaxed from `A ∈ Υ` to `RefAt`, soundness re-proved (`refAt_refutes_sf`/`clo_forces_sf`, kept in `FRJ/RefAt.lean`), the whole stack rebuilt green — and then the conservativity screening (Matthew's flag) found the relaxation UNWITNESSED: its own demo's (J2) was vacuous (the V1 kept chain did the retention), and every design-level blocking configuration reroutes through the kept chain.  Reverted; the strict-(J2) family stands.  Licence discipline: a barren-(J2) relaxation re-enters only with a kernel-checked separating cell (V₂-underivable, V₃-derivable).  The vacuity witness: `wip/minmodv_round3_demo.lean` now derives the flight-shaped cell in the STRICT calculus. |

## Screening record (counterexample-first)

* Statement screening: the self-referential (unstratified) retention
  condition admits mutually-justifying kept pairs with no soundness
  argument — rejected at design time; `KeptChain` is the fix.
* Extensional screening: untyped engine, 462 ρ-cells vs two-sided kernel
  ground truth — 0 hits on 158 proved cells; 297/303 refutable found;
  both witnesses derived along the predicted trees
  (`wip/frjx_sweep_out.txt`, `wip/frjx_cells_out.txt`).
* Soundness-before-completeness: soundness (deliverable 4) is the
  session's target; completeness of FRJV is explicitly NOT claimed.

## Non-scope

Completeness of FRJV; relaxing the promise/fallible joins; the 6-cell
residue (consequent ρ18 / antecedent ρ20); `Fast`/`Profile`
re-optimisation over the functor (follow-up; the reference instance is
the correctness anchor); unifying `FRJ` and `FRJV` into one
policy-parameterised family (recorded as the long-term shape, not
attempted here).
