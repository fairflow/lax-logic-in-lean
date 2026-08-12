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
