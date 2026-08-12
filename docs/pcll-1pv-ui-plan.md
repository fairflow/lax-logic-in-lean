# Finishing the one-variable semantic PCLL UI — the job plan

*2026-08-12, planned before execution at Matthew's direction, from the
final states of the semantic-route files. This plan CORRECTS the arc
report's §0 headline: PROGRESS §39's "one obligation from done" was
superseded by §§40–44 — the constant link consumes `D : RNDict` (a
finite variable-free dictionary), and that premise FELL (the 15-class
closure kernel-refuted in `wip/rnDictRefute.lean`; ≥ 25 classes with
no plateau by §44; the Curry-problem thread aims to prove RN(◯,{})
infinite outright). A correction note is appended to
`docs/pcll-picll-arc-report.md`.*

## 1. Previous attempts, final states (read before building anything)

1. **The constant link** — `wip/stabilise.lean`, the most instructive
   file. PROVED, conditional on `D : RNDict`: `dict_collapse`,
   `dict_agree_stab` (vf-agreement at rank `D.crankBound` is agreement
   everywhere), `vfB` (the constant family is a lawful layered
   bisimulation with the m-clauses as hypotheses `VfMwit`/`VfMback`),
   `vfB_mforthResidue` (the residue PAID), and
   `restricted_amalgamation_oneVar` (the full p-variant conclusion at
   fixed entry budget). Axiom-pinned. **Blocked at the premise**: all
   evidence says no finite dictionary exists (for RN or RNC — §§43–44:
   "the tower continues past distribution"). The machinery is reusable
   verbatim IF a dictionary exists for a relevant subfragment; do not
   attempt to inhabit `RNDict` as stated.
2. **The band link** — `wip/bandM.lean`, `bandW`, `bandStabilise`,
   `bandRefute`: the plateau weakened to a band; `BandCollapse`
   unsupported below crank ~8 (§43). Dead on the same axis as 1.
3. **The per-instance route** — `wip/bii_probe.lean`, `mwit_*`:
   the mforth residue is VACUOUS on the battery (0/13,204
   configurations; negative control passed), d ≤ 2 shut paper-level,
   d ≥ 3 open; `mforthResidue_of_sameTraceBase` PROVED. §43's recorded
   route forward: "the mforth choice-freedom refactor + the
   per-instance residue treatment, over whichever of PLL/PCLL the
   Thm 5.1 assembly targets."
4. **The confluent redesign** — `docs/confluent-ui-plan.md`: on
   mutually confluent models the ∀∃-clause collapses to bare
   possibility, refuting `◯χ` becomes LOCAL, there is no promising
   successor, hence no `2d / 2d−1` bookkeeping — the wall of the
   general route does not arise (§3's three-step argument;
   `PLLConfluentComplete.lean` proves the canonical diamond case with
   no promise component). The crux moves to **`amalgam_confluent`**:
   the amalgamated model must itself be confluent (plan line ~115).
   Caveat inherited: this is a SEMANTIC route; the proof-theoretic
   PCLL calculus is mined (`g4confGap`) and is not needed here.
5. **The general-PLL sorries** — `PLLSemUIChar.lean:322,327`
   (mforth/mback), `PLLSemUILayered.lean:827`,
   `PLLSemUIHenkin.lean:341,352`. The PCLL 1-pv route goes AROUND
   these, not through them.

## 2. The route chosen, and why

Target: the Thm 5.1 assembly (`docs/semantic-ui-route.md:1767` — "the
Thm 5.1 assembly, which is bookkeeping once those fall") instantiated
at ONE variable over the CONFLUENT class. Rationale: confluence is
PCLL's semantic home (calculus `DerivU`; refutation instrument
`not_derivU_of_checkConf` exists); bare possibility deletes exactly
the clause family where every prior attempt died; and the 1-pv scope
matches the U/V blockers, giving route (4) its proved anchor.
The dictionary is NOT assumed anywhere.

## 3. Stages (testing doctrine applied; refute before build at every step)

**Stage 0 — statements and screens, no proofs.** Write the target
statement (1-pv PCLL post-interpolant existence, the Thm 5.1 form) and
the DIAMOND m-clauses for the amalgam construction. Battery-screen
both, using the standing confluent machinery (`wip/confl_core.lean`,
the fork/gadget/lobTower frames of `wip/confl_results.txt`,
`Config.accept := RNC.confB`): in particular screen
**`amalgam_confluent`** — build the amalgam on battery pairs and CHECK
confluence of the result computationally before proving anything. A
certified failure here redirects the whole job and costs a day, not a
month.

**Stage 1 — `amalgam_confluent`.** The crux. Prove the amalgamated
model of `amalgamation_assembledC`'s construction confluent when both
inputs are (or repair the construction until it is; the battery screen
says which). Everything else in this plan is believed bookkeeping;
this is the one genuinely new lemma.

**Stage 2 — the diamond truth-lemma clauses.** mforth/mback for the
amalgam under bare possibility, template `PLLConfluentComplete`'s
canonical case: locality should make both clauses one-step, with no
residue and no promise component. If any ∀∃ remnant survives into a
d ≥ 3 configuration, stop and re-screen (that is the §43 open region
resurfacing; the per-instance treatment is the fallback).

**Stage 3 — assembly and pins.** The Thm 5.1 wrapper at 1-pv/PCLL;
`#print axioms` pins transcribed from output; the claim stated in the
calculus map (a NEW row: which system, whose result); UI for full PCLL
and for PLL remain OPEN and are stated so.

**Stage 4 — corollaries and transfer.** PICLL (the infallible
subclass): re-screen which battery certificates survive `¬◯⊥`; the
prover gains and the refuter loses exactly as the arc report records.
Then the transfer note: what stage 1–2 machinery says about the
general-PLL sorries (expected: nothing directly — the wall is real
there; but the choice-freedom refactor of §43 may inherit the
diamond-case shape).

## 4. Risks, stated

* `amalgam_confluent` may genuinely fail — the 2026-08-07 note already
  flagged that the obvious calculus route was refuted and the semantic
  route "may harden" as well as simplify. The stage-0 screen decides
  cheaply.
* `DerivU`-completeness for the confluent class: verify the exact
  statement and its pin before consuming it in stage 3.
* Estimation: my cost estimates run ~4× pessimistic and my benefit
  estimates optimistic (method ledger items 9/15) — so: stage 0 is
  hours; stages 1–3 are a focused session each IF the screen passes;
  no compile-time promises are made at all.

## Stage 0 executed (2026-08-12 afternoon) — GREEN; stage 1 is go

* Statements landed (`wip/pcll1pv_stage0.lean`, elaborates clean):
  `AmalgamConfluent`, `CornerTriple` (the isolated crux content — the
  amalgam's Ri/Rm are componentwise, so confluence = component
  confluences + a triple at the corner), `ConfResidue`,
  `OneVarConfluentAmalgamation` (the stage-3 target, N confluent), and
  the proved glue `amalgamConfluent_of_corner`.
* S1 assessed on paper: `MutuallyConfluent (canonFinC cl)` looks
  provable by design under `OBoxAdeq` — `RmC`'s anticipation clause
  restricts Rm-successors to promised content, Ri-extensions inherit
  the promises, `Ri` demands only val-inclusion, and joint consistency
  at the corner is the `Backed`/primeness machinery's purpose.
* S2/S3 implemented and run (`wip/pcll1pv_screens.lean`, exe
  `s0screens`): **128 cells, 0 flags** — 2,624 corner checks (S2, the
  `CornerTriple` proxy) and 504 infallible-M-move checks (S3, the
  `ConfResidue` vacuity proxy) all pass over nine law-closed frames
  (incl. a depth-3 frame for the old d ≥ 3 region) × two ◯-adequate
  closures; 68 non-vacuous / 60 vacuous cells counted.  Proxy
  semantics: canonical worlds proxied by traces, link by constant
  bounded-rank vf-agreement; failures would have been FLAGS, passes
  are genuine support.  Finding: the `top` escape is SUBSUMED by
  `proper` under the constant link (fallible worlds agree on
  everything), so `topTriples = 0` is structural, not vacuity.
* Stage 1 order confirmed: (1) `MutuallyConfluent (canonFinC cl)`
  under `OBoxAdeq` (the paper argument above); (2) `CornerTriple` —
  the one genuinely new maintenance lemma; then the glue to
  `OneVarConfluentAmalgamation` via `amalgamation_assembledC`.

## Stage 1 executed (2026-08-12 evening) — items 1 and 3 outright, item 2 modulo one minimal Prop

`wip/pcll1pv_stage1.lean`, all pins `#guard_msgs`-transcribed at
`[propext, Classical.choice, Quot.sound]`, no sorryAx:

* **Item 1 was already in-repo**: `FinComp.canonFinC_confluent`
  (wip/canonFinC.lean) — the finite canonical component IS mutually
  confluent under `OBoxAdeq`, witnessed by `obInvW` (the
  promise-collecting successor).  Found by the read-before-prove
  discipline; pinned, not re-derived.
* **Item 2, the corner**: PROVED — `rmC_le_obInv` (`obInvW c₁` is the
  MAXIMUM `RmC`-successor and dominates the b-side: an Rm-successor's
  content is promised, promises persist up Ri), `obInvForth_of_core`
  (BOTH escape families discharged: the `⊥`-region tops out via
  `boxUnit`; the `MBack`-fallible pair tops out via bare possibility —
  one fallible Rm-successor forces `◯⊥` at the base under K's
  confluence), `cornerTriple_of_core`, `amalgamConfluent_of_core` —
  all conditional on the single minimal Prop **`ObInvForthCore`**: at
  a proper-region triple with the MBack-LINKED partner in hand
  (`Z_{2d−1} κ u`, `Rm k κ`, `k` tracing to `Δ`), produce a triple at
  `obInvW Δ`.  This is exactly PROGRESS §43's choice-freedom
  configuration (κ has the link, not the trace; the directed witness
  has the trace, not the link), isolated as `DykAnt`/`MforthResidue`
  were; its discharge is stage 2's m-clause work by the plan's own
  assignment.
* **Item 3 PROVED OUTRIGHT**: `oneVarConfluentAmalgamation_holds` —
  the assembly with the confluence conjunct, by
  `amalgamation_assembledC`'s own proof term.

Stage 2 therefore has a single sharpened target list: `ObInvForthCore`
+ the agreement-side m-clauses + `ConfResidue`, all of one family, all
under bare possibility.

## Stage 2 design pin (2026-08-12 ~21:50, BEFORE implementation — survives compaction)

The sorry sites (`layered_of_frag_agree_W`, PLLSemUIChar.lean:322/327)
are the mforth/mback of the AGREEMENT family `Z α w w' := agreement on
V-formulas of crank ≤ 2α`.  The i-clauses are proved there via the
implication-refutation trick + `agree_of_char`; the m-clauses have no
such trick in general PLL.  Under BOTH models confluent, the WITNESS
form is provable by the **σ-ping-pong**:

* σ(t) := {D ∈ L : t ⊩ D}, L the finite rank-(2α−2) V-formula list
  (the char machinery's list).  ⋀σ is transferable: crank(⋀σ) ≤ 2α−2,
  crank(◯⋀σ) ≤ 2α−1 ≤ 2α.
* Bare possibility (`force_somehow_iff_of_confluent`) turns
  `t ⊩ ⋀σ` at an Rm-successor into `base ⊩ ◯⋀σ` and back — LOCAL
  witness extraction on both sides (the ∀∃ collapse; extraction at the
  reflexive point needs nothing).
* Ping-pong: seed σ₀ := σ(u) (∪ the demanded ψ for mwit); transfer
  ◯⋀σ across the agreement, extract the other side's witness, its σ
  is ⊇; alternate.  σ ascends in the FINITE lattice of subsets of L →
  stabilises; at stabilisation the two witnesses have EQUAL σ, i.e.
  rank-(2α−2) V-agreement — `Z (α−1)`-linked.  Termination: strong
  induction on `L.card − σ.card`.
* This serves the WITNESS clauses (`mwit`, and `MBack` dually), which
  re-choose the K-side witness — exactly §43's "mforth choice-freedom
  refactor", now with a concrete argument.  The choice-free clause
  (answer the GIVEN u) is NOT claimed and is not needed by the
  amalgamation.

Implementation order: (a) read `LayeredBisimWit`'s exact mwit/MBack
field types (levels!); (b) the σ-kit over the char list (σ as a
Finset, ⋀σ crank/atoms lemmas); (c) the ping-pong lemma
(`confluent_sigma_match`); (d) `agree_mwit`/`agree_mback` under
`MutuallyConfluent M ∧ MutuallyConfluent N`; (e) the confluent
`layered_of_frag_agree_Wit` with NO sorries; (f) then revisit
`ObInvForthCore` and `ConfResidue` with the proved link clauses (the
missing corner base-link may now be constructible: the ping-pong can
seed σ with the promise set — the directed witness AND the link from
one argument).  File: `wip/pcll1pv_stage2.lean`.  All in-repo
ingredients: charPos/charNeg/agree_of_char/crank lemmas (Char file),
force_somehow_iff_of_confluent (PLLFrames), directedness by iterated
confluence (new small lemma).

## Stage 2 progress (2026-08-12 late evening) — the m-clause heart PROVED

DONE, pinned `[propext, choice, Quot.sound]`, no sorryAx
(`wip/pcll1pv_stage2.lean`, commits 9193fc6/e209911/eb3fc0f):

* `confluent_directed` — Rm-row directedness from mutual confluence.
* `confluent_char_match` — **THE σ-PING-PONG**, with strict-growth
  termination (`filter_length_lt`) and the two fallible bounces (◯⊥).
  crank note: ◯ costs 2 (`crank (somehow φ) = crank φ + 2`); the
  budget closes because `bigAnd` is crank-free on cons — `◯charPos` is
  transferred only when the filter is nonempty (else the reflexive Rm
  witness serves), `◯D₀` and `◯⊥` fit under r+2 always.
* `agree_mwit` / `agree_mwitN` — the confluent WITNESS-form m-clauses
  of the agreement family (K-side `mwit`-shaped, M-side `MWitM`-shaped),
  closed to full rank-2α agreement via `frag_reps_exist'` +
  `agree_of_char` + `force_of_deriv` (the agree_iforth closer).
  These discharge, for the CONFLUENT class in witness form, the exact
  clause family whose general-PLL forms are the standing sorries.

REMAINING for stage 2:
* (e) the Wit-family assembly: build the `LayeredBisimWit (· ∈ V)`-style
  family with Z α := rank-2α agreement, i-clauses := agree_iforth/iback,
  mwit := agree_mwit; MWitM := agree_mwitN.  Mechanical.  CHECK FIRST:
  whether the amalgamation chain accepts MWitM in place of MBack
  (`witTriple_mwit` exists per the structure's doc comment — find its
  consumers; if only the MBack-form `wit_pbisimC` exists, an
  MWitM-form variant must be built or MBack proved for agreement,
  which the ping-pong does NOT give).
* (f) `ObInvForthCore` + `ConfResidue`.  THE CRUX, stated exactly: the
  proper triple constructor demands a BASE link `Z_{2d'} k* u` at the
  FIXED M-world `u`, but the ping-pong (like every witness-form move)
  produces its OWN M-side world; links at fixed worlds come only from
  MBack.  Candidate resolutions, in order: (i) seed the ping-pong from
  the promise-realiser (directedness gives κ₀ realising ALL of
  obInv(Δ).val; heredity keeps this along the growth; the matched κ̂
  then traces EXACTLY to obInv-val — proved-shape) and take the
  ping-pong's own u' as the triple's M-world, reconciling the corner's
  Ri-b₂ demand via M-side directedness THEN re-running the ping-pong
  ABOVE the reconciled world (the link-at-u₂ gap is the open step);
  (ii) relax WitTripleC's base to an Ri-predecessor slot (a
  construction repair — the plan allows it; check every consumer);
  (iii) switch the whole assembly to witness-form maintenance
  (witTriple_mwit) so no fixed-world base links are ever demanded —
  the cleanest if the chain supports it.  Start with (iii)'s
  feasibility check.
