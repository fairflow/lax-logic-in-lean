# Belief-in-Lax-Logic: machine-checked results index

*Status 2026-07-16. Every mathematical claim the paper states as established is
backed by a `sorry`-free, axiom-audited Lean file on branch
`claude/belief-lax-logic-handover-f331bf` (worktree). Audit key: **clean** =
`[propext, Classical.choice, Quot.sound]`. Nothing is committed — the files are
untracked, for review.*

*Policy (Matthew, 2026-07-16): nothing in `wip/` is ever claimed as formally
proved; claimable results live in the `LaxLogic/` library. The belief files
below were promoted accordingly on 2026-07-16 (with `closedNucleus` /
`nucleus_eq_sup_bot` deduplicated into the shared base `BeliefCollapse`).*

| file | key results | audit | paper § |
|---|---|---|---|
| [`LaxLogic/BeliefCollapse.lean`](../LaxLogic/BeliefCollapse.lean) | `closedNucleus` (shared base); `nucleus_eq_sup_bot` (`j x = x ⊔ j⊥`); `eq_id_of_bot_eq_bot` (sceptic); `eq_top_of_bot_eq_top` (credulous) | clean | §2A / §3b-1 |
| [`LaxLogic/BeliefBooleanIso.lean`](../LaxLogic/BeliefBooleanIso.lean) | `nucleusOrderIsoBot : Nucleus B ≃o B` — the sharp `N(B) ≅ B` via `j ↦ j⊥` | clean | §2A / §3b-1 |
| [`LaxLogic/BeliefNormality.lean`](../LaxLogic/BeliefNormality.lean) | `nucleus_himp_le` (K axiom `◯(A→B)→(◯A→◯B)`); `nucleus_top` (`◯⊤=⊤`) | clean | §2 — `◯` is a *normal* modality (corrects the earlier "not normal") |
| [`LaxLogic/BeliefIdealisation.lean`](../LaxLogic/BeliefIdealisation.lean) | `belief_introspection` (`◯◯M⊣⊢◯M`); `belief_consequence` (`Γ⊢M ⟹ ◯Γ⊢◯M`, logical omniscience); `belief_necessitation`; `nucleus_listInf` (`⋀◯Γ=◯⋀Γ`) | clean | §2E |
| [`LaxLogic/BeliefOpenClosed.lean`](../LaxLogic/BeliefOpenClosed.lean) | `openNucleus`; `openNucleus_eq_closedNucleus` (BA: open = closed); `em_of_openNucleus_eq_closedNucleus` (open=closed ⇒ EM at `a`); `open_ne_closed_Fin3` (separation) | clean | §2B / §3b-2 |
| [`LaxLogic/BeliefFalsum.lean`](../LaxLogic/BeliefFalsum.lean) | `belief_no_D` (`⊬¬◯⊥`); `belief_bot_not_provable` (`⊬◯⊥`); `belief_credulous` (`◯⊥⊢◯M`) | clean | §2E / §3b-4 |
| [`LaxLogic/BeliefExamples.lean`](../LaxLogic/BeliefExamples.lean) | `chain3_card=4` (+ sceptic/credulous/closed/open exhibited, `chain3_open_ne_closed`); `chain4_card=8`; `boolean22_card=4` | 3-chain clean; `chain4_card`,`boolean22_card` add `ofReduceBool` (native_decide) | §5 / §3b-5 |

**Prior results reused** (from `main`, promoted to the library 2026-07-16):
`thm6` (context completeness — §6), `closed_lax_infinite` (infinite closed
fragment — §2B/§5), `thm2_boolean_algebra`, `corollary10` — now in
[`LaxLogic/PLLCtxCompleteness.lean`](../LaxLogic/PLLCtxCompleteness.lean) and
[`LaxLogic/PLLLaxInfinite.lean`](../LaxLogic/PLLLaxInfinite.lean).
Object-logic `◯`-laws cited: `somehowR`/`somehowM`/`somehowS`/`somehowFunctor`
(`PLLTheorems.lean`), `not_provable_not_somehow_false` (`PLLFrames.lean`).

**Literature sources** (prose, verified citations):
`docs/iel-justification-lit.md` — IEL⁻ / justification-logic positioning (§8);
`docs/realisability-modal-lit.md` — realisability model-theory direction (§9), incl.
the four-frameworks comparison, the metatheory-vs-object-theory verdict, and the
local-nucleus-stability analysis.

**Consolidation note — RESOLVED (2026-07-16).** The formerly duplicated
`closedNucleus`/`closedNucleus_apply` and `nucleus_eq_sup_bot` now live once, in
the shared base `BeliefCollapse`, imported by `BeliefBooleanIso` and
`BeliefOpenClosed`; all nine belief/Curry modules are imported by the library
root `LaxLogic.lean`, so `lake build` checks everything.
