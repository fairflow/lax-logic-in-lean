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

### The (f)-lead found at the context boundary (2026-08-12 ~22:15)

The witness-form chain EXISTS AND IS PROVED in-repo
(`wip/witOut.lean`: `witTriple_mwit`, `wit_pbisimW`,
`amalgamation_assembledW`, pinned) — it consumes `MWitM` (proved
today, `agree_mwitN`) and `MwitResidue`, never MBack.  So route (iii)
is real: the 1-pv confluent chain is
  levelled agreement family (V := ∅ over p-pure models — the
  DICTIONARY-FREE repair of §39: levels finance what the dictionary
  was for) + agree_iforth/iback + agree_mwit/agree_mwitN
  + MwitResidue + amalgamation_assembledW + AmalgamConfluent.
Remaining open: `MwitResidue` for this family, and the corner
(`ObInvForthCore` or its witness-form analogue for the W-assembly).

**NEW vacuity lead for MwitResidue (agreement family, confluent M):**
in the residue configuration both κ (same-trace, level 2d−1) and kv
(grown-trace, level 2d) are agreement-linked to the SAME witness u'.
Agreement is an iff, so κ and kv agree WITH EACH OTHER on every
formula of crank ≤ 2·(2d−1).  If `2·(2d−1) ≥ max crank over cl`, the
traces are determined by those agreements: trace κ = trace kv —
CONTRADICTING the configuration's same/grown split.  So the residue
is VACUOUS in the high-depth region `4d − 2 ≥ maxCrank cl`; the
low-depth remainder is the region the old analysis shut on paper
(d ≤ 2).  NEXT ACTION: compute both bounds for ◯-adequate closures
and check whether the regions COVER (if maxCrank cl ≤ 6 the whole
range is covered by d ≤ 2 ∪ 4d−2 ≥ 6, i.e. always); if a gap remains,
it is finitely many d per closure — screen it.  Then the corner by
the same two-region analysis.

### Stage 2(e) DONE + a correction to the vacuity lead (2026-08-12 ~22:20)

(e) PROVED and pinned (`wip/pcll1pv_stage2e.lean`): `lvlB` — the
LEVELLED variable-free agreement Wit-family over p-pure confluent
models (Z α := rank-2α closed-formula agreement; i-clauses by the
character argument at V = ∅, mwit by the σ-ping-pong, atoms by purity)
— plus `lvlB_mwitM`.  The dictionary-free constant link, assembled.

CORRECTION to the (f) vacuity lead: the κ~kv comparison runs THROUGH
the M-side witness u′, so it constrains CLOSED formulas only — for
`lvlB` the links are closed-formula agreement, and cl's P-CARRYING
members are untouched.  The high-d conclusion is therefore NOT
vacuity but a structural constraint: in the residue configuration at
`4d−2 ≥ maxCrank cl`, trace(kv) agrees with Δ.val on every CLOSED
member — the same/grown split is witnessed by a p-carrying formula
only.  (f) stands as real work with that sharpened target; the
remaining routes: exploit p-purity of K (kv's p-decoration is
constrained by hPK: p-carrying formulas at p-pure worlds reduce
toward their ⊥/⊤-instances — check whether forcing of p-carrying cl
members at K-worlds is DETERMINED by closed data on p-pure models;
if yes, vacuity is restored!), the low-d mechanisation, the corner,
or the construction repair (ii).  NOTE the promising specific: on a
p-pure model, w ∈ V p is the ONLY p-fact; forcing φ(p) at w is
determined by the closed theory PLUS the V p-decoration pattern of
the cone above w — screen whether the residue split can live in that
pattern.

### (f) reduced to the promise-stable kernel (2026-08-12 ~22:30, derivation pinned before implementation)

Working `MwitResidue` for `lvlB` with the symmetric ping-pong
(`agree_mwitN` at the base pair (k, m), M-side seed u′ carrying ψ):

* **Fallible branch DISCHARGES**: the matched pair goes fallible →
  `top` at `traceC t̂` (`Rm k t̂` gives the canonical RmC-move; force ψ
  rides on the fallible side).
* **Grown branch DISCHARGES**: matched `t̂ ~ u″` at level 2d−1 with
  `trace t̂ ≠ Δ.val` strictly grown → depth drop finances a fresh
  reflexive proper triple at `traceC t̂` (2d″+1 ≤ 2d−1), exactly the
  `witTriple_mforth` strict-growth pattern.
* **The stuck branch**: `trace t̂ = Δ.val`.  Iterating cannot help in
  general, BUT if the stuck branch recurs for every choice then every
  `Rm`-successor of k traces to Δ, which forces **promise-stability**:
  `obInv(Δ) =val Δ` (all promises already honoured), and then EVERY
  canonical `RmC`-successor of Δ is val-Δ — so the conclusion demands
  a SAME-trace triple, whose base link at the fixed M-witness is ONE
  level short (2d−1 vs 2d).  This is the invariant one-short wall in
  its final, minimal form.

**The residual Prop** (to isolate): at promise-stable Δ, a same-trace
matched pair at 2d−1 promotes to a triple (equivalently: level
promotion at promise-stable worlds).  Two discharge designs, ranked:
(1) LEVEL RE-FOUNDING on promise-depth — the triple's 2d financing is
calibrated for the general descent; at promise-stable Δ the remaining
descent is 0, so the true need should be O(1); re-found `WitTripleC`'s
levels on `pdepth Δ := number of strict obInv-growths remaining`
(≤ canonDepthC), making promise-stable worlds cheap.  A principled
construction repair (the plan licenses it), touching witTripleC's
level arithmetic throughout.  (2) The isolation: state
`StableCore`, prove `mwitResidue_lvlB_of_stableCore` (the two
discharged branches above are machine-checkable NOW), and SCREEN the
promise-stable configuration on the battery (it is finitely checkable
— stage-2's own text licenses exactly this: isolate the surviving
configuration and re-screen).  Stage-2 completion = the m-clauses
(DONE) + this reduction + the screen + the corner's analogous
treatment.

## STAGE 2 COMPLETE (2026-08-12 ~23:00)

The criterion set above — the m-clauses + the residue reduction + the
screen + the corner's analogous treatment — is met in full:

* **(f) the residue**: `mwitResidue_of_stableCore`
  (`wip/pcll1pv_stage2f.lean`, commit 8e9ddd5) — `MwitResidue` for
  `lvlB` modulo the single kernel `StableCore` (the same-trace matched
  pair one level short at a promise-stable world); fallible branch by
  `top` at the partner's trace, grown branch financed by the depth
  drop.  Pin `[propext, choice, Quot.sound]`.
* **(g) the corner**: `amalgamConfluent_of_coreW`
  (`wip/pcll1pv_stage2g.lean`) — `AmalgamConfluent` for `lvlB` modulo
  the kernel `CornerCoreW`, with NO adversarial clause anywhere: the
  corner's M-move is also an `Rᵢ`-move (`sub_mi`), so the K-partner
  comes from the family's proved `iback`; the fallible escape closes
  by bare possibility + the family's own `◯⊥`-transfer.  Pin
  `[propext, choice, Quot.sound]`.
* **Two screen-forced statement repairs** (S5, the testing doctrine
  working as designed — both were NO-CASE corner defects caught
  before any discharge was scoped):
  1. The first kernel anchored the corner triple AT `obInvW Δ`;
     REFUTED in the promised-`⊥` region: `◯⊥ ∈ Δ.val` puts `⊥` in the
     promise set, and a triple there with an infallible `u` is
     impossible (`top` needs `u ∈ M.F`; a `proper` K-slot traces
     through `⊥`, so the fall clause forces `u ∈ M.F` too).  Repair:
     b-side world as data, existential corner world.  **Stage 1's
     `ObInvForthCore` shares the anchor — treat it as superseded; do
     not scope a discharge of the anchored form.**
  2. The freed b-side then flagged `⊥ ∈ Δb` against infallible `u` —
     unreachable in the real corner (`⊥ ∈ val b₁` makes `b₂` fallible
     through b's own triple, and fallibility is hereditary along
     `Rᵢ b₂ v₂`).  Repair: the maintenance carries the tie
     `⊥ ∈ Δb.val → u ∈ M.F` (discharged at the consumer exactly so);
     the kernel is gated on `⊥ ∉ Δb.val`.
* **The kernel screens** (S4 `StableCore`, S5 `CornerCoreW`,
  `wip/pcll1pv_screens.lean`, compiled `s0screens`): **0 flags on all
  128 battery cells**.  Non-vacuity: S4 exercised 3,366
  configurations, 862 with p-CARRYING ψ (the corrected vacuity
  analysis's live region); S5 exercised 2,154 corner configurations,
  all answered by proper triples (`top=0` in the gated region is
  expected — the `top` answers live in the PROVED branches).

**Stage-3 wiring (pinned for the wrapper):** the Thm 5.1 chain is now
  `lvlB` + `agree_iforth/iback` (i-clauses) + `lvlB_mwitM` (M-witness
  clause) + `mwitResidue_of_stableCore` (residue) +
  `amalgamation_assembledW` (assembly) +
  `amalgamConfluent_of_coreW` (confluence of the p-variant),
entirely MBack-free.  The open Props after stage 2 are exactly the two
screened kernels, `StableCore` and `CornerCoreW`.  Discharge designs,
ranked as before: (1) level re-founding on promise-depth (`pdepth`)
making promise-stable worlds cheap — a principled construction repair;
(2) for `CornerCoreW`, the promise-seeded ping-pong (directedness
realises all of `obInv(Δ).val` at one κ₀; `traceC κ₀` is an
`RmC`-successor by `traceC_mforth` and covers every promise-dominated
b-side; budget wall: transferring `◯⋀promises` needs
`maxCrank + 2 ≤ 4d − 2`, so the low-depth region needs (1) or the
ψ₀-refinement).

## STAGE 2 KERNELS CLOSED + STAGE 3 COMPLETE (2026-08-13 early)

Matthew's completion spec included CLOSING the two kernels, not just
isolating them.  Both are now closed modulo ONE Prop:

**`ClosedCollapse 6`** (`wip/pcll1pv_stage2i.lean`): every closed
formula is force-equivalent over the mutually confluent class to a
closed representative of crank ≤ 6.  Finitely certifiable: `DerivU`
interderivability certificates + `derivU_sound` both ways.  A
background probe is computing the closed-fragment classes per crank
stratum (prove side: `LaxND` + distribution instances; refute side:
`not_derivU_of_checkConf`).

* **`StableCore` CLOSED** (`stableCore_of_collapse`): promised-`⊥`
  region (`◯⊥ ∈ val Δ`) outright — fallible realisers on both sides,
  `◯⊥` transfers at crank 2 across the one-short link, `top` at the
  realiser's trace; `◯⊥`-free region has depth ≥ 2 (a depth-1 val is
  `cl \ {⊥}` ∋ `◯⊥`), so `4d−2 ≥ 6` and the collapse promotes the
  one-short link to every level — reflexive triple, no reservoir.
  Hence `mwitResidue_of_collapse`.
* **`CornerCoreW` CLOSED** (`wip/pcll1pv_stage2j.lean`,
  `cornerCoreW_of_collapse`): the kernel was RESTATED freed-`u`
  (conclusion `Rᵢ`-anchored at the corner witness, `Rₘ`-anchored at
  the base — both what `CornerTriple` actually consumes, via
  `sub_mi`/`trans_i`/`trans_m`).  The closure is `corner_descend`, a
  recursion on strictly decreasing canonical depth: promised-`⊥` →
  fallible close (join the seed by directedness, `hered_F` carries
  fallibility over the join); promise-stable → the ANCHORED witness
  clause (`agree_mwitN_anchored` — `confluent_char_match` now exposes
  its `Rᵢ`-seed anchor, latent in the directedness joins) +
  `trace_const_of_stable` + collapse-promotion, reflexive close at the
  current trace; unstable → `promise_realiser` (directedness fold)
  seeds `agree_mwit` with `⋀(promise set)`, the output strictly grows
  the trace, recurse.  `RmC` chains by `traceC_mforth`; the fallible
  clause-escapes are vacuous in the `◯⊥`-free region (they would put
  `◯⊥` in the trace).  Hence `amalgamConfluent_of_collapse`.
* **Supporting kit** (`wip/pcll1pv_stage2h.lean`): `PromiseStable`,
  `val_eq_of_stable_rmC` (RmC-successors are val-rigid at stable
  worlds), `trace_const_of_stable` (the K-side Rm-cone is
  trace-constant), `exists_broken_promise`.
* **A statement-level landmine fixed at the instantiation boundary**:
  strict `PPure` + `full_F` forces `F = ∅` — the "p-pure confluent
  class" was secretly the INFALLIBLE class (PICLL, not PCLL).  The
  chain now runs on weak purity `PPureF` (`V a ⊆ F` off `p`); `lvlB`'s
  atoms clause is re-proved through the fall-tie + `full_F`.

**Stage 3 (assembly + wrapper), COMPLETE:**

* `DerivU`-completeness verified at source: `derivU_iff_confluent_valid`
  (PLLConfluentComplete.lean) is over exactly the `ConstraintModel` +
  `MutuallyConfluent` + `force` types the chain uses; pin
  `[propext, Classical.choice, Quot.sound]`.
* **`oneVarConfluentAmalgamationW`** (`wip/pcll1pv_stage3.lean`),
  modulo `ClosedCollapse 6`: weakly p-pure mutually confluent `K`, `M`
  linked by closed agreement at budget `2·cl.card + 1` amalgamate into
  a CONFLUENT witness-form p-variant of `M` matching `K`'s `cl`-theory
  at the root and transferring every p-free formula.  The Thm 5.1
  semantic heart, entirely MBack-free.
* **The wrapper** (`wip/pcll1pv_stage3b.lean`): `IsSemExC` (the
  confluent semantic ∃p at 1 pv, variants ranged by `PBisimWit`);
  `pPurify` (purification functor: same frame, non-p atoms restricted
  to fallible worlds — confluence-, purity- and `{p}`-forcing-
  preserving); **`semExC_upper` and `semExC_adjunction` PROVED
  UNCONDITIONALLY**: any spec-satisfier `ψ` has `DerivU [φ] ψ` and,
  for every closed `χ`, `DerivU [φ] χ ↔ DerivU [ψ] χ` — a
  spec-satisfier IS the uniform post-interpolant over `DerivU`.
  Pins `[propext, choice, Quot.sound]`.
* **What remains OPEN, stated as such**: `SemExC1Definable`
  (existence of a spec-satisfier at 1 pv).  The amalgamation is the
  hard half; with the collapse, the candidate interpolant is
  `⋁ {bigAnd S : S a realised closed theory of a φ-realiser}` and the
  open step is exactly whether realised exact theories are up-closed
  (the forward direction needs a realiser with the SAME closed theory
  as the `ψ`-forcing world).  UI for full PCLL and for PLL remain
  OPEN.  And `ClosedCollapse 6` itself awaits the probe's
  certificates — if the collapse rank comes back > 6, the region
  arithmetic in stages 2(i)/2(j) recalibrates (the `◯⊥`-free region
  needs `4d−2 ≥ R₀`, so kernels reopen at depths `d < (R₀+2)/4` only).
