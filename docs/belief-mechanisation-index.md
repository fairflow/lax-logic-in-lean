# Belief-in-Lax-Logic: machine-checked results index

*Status 2026-07-16. Every mathematical claim the paper states as established is
backed by a `sorry`-free, axiom-audited Lean file on branch
`claude/belief-lax-logic-handover-f331bf` (worktree). Audit key: **clean** =
`[propext, Classical.choice, Quot.sound]`. Nothing is committed — the files are
untracked, for review.*

| file | key results | audit | paper § |
|---|---|---|---|
| `wip/belief_boolean_collapse.lean` | `nucleus_eq_sup_bot` (`j x = x ⊔ j⊥`); `eq_id_of_bot_eq_bot` (sceptic); `eq_top_of_bot_eq_top` (credulous) | clean | §2A / §3b-1 |
| `wip/belief_boolean_iso.lean` | `nucleusOrderIsoBot : Nucleus B ≃o B` — the sharp `N(B) ≅ B` via `j ↦ j⊥` | clean | §2A / §3b-1 |
| `wip/belief_normality.lean` | `nucleus_himp_le` (K axiom `◯(A→B)→(◯A→◯B)`); `nucleus_top` (`◯⊤=⊤`) | clean | §2 — `◯` is a *normal* modality (corrects the earlier "not normal") |
| `wip/belief_idealisation.lean` | `belief_introspection` (`◯◯M⊣⊢◯M`); `belief_consequence` (`Γ⊢M ⟹ ◯Γ⊢◯M`, logical omniscience); `belief_necessitation`; `nucleus_listInf` (`⋀◯Γ=◯⋀Γ`) | clean | §2E |
| `wip/belief_open_closed.lean` | `openNucleus`,`closedNucleus`; `openNucleus_eq_closedNucleus` (BA: open = closed); `em_of_openNucleus_eq_closedNucleus` (open=closed ⇒ EM at `a`); `open_ne_closed_Fin3` (separation) | clean | §2B / §3b-2 |
| `wip/belief_falsum.lean` | `belief_no_D` (`⊬¬◯⊥`); `belief_bot_not_provable` (`⊬◯⊥`); `belief_credulous` (`◯⊥⊢◯M`) | clean | §2E / §3b-4 |
| `wip/belief_examples.lean` | `chain3_card=4` (+ sceptic/credulous/closed/open exhibited, `chain3_open_ne_closed`); `chain4_card=8`; `boolean22_card=4` | 3-chain clean; `chain4_card`,`boolean22_card` add `ofReduceBool` (native_decide) | §5 / §3b-5 |

**Prior results reused** (already on `main`): `thm6` (context completeness — §6),
`closed_lax_infinite` (infinite closed fragment — §2B/§5), `thm2_boolean_algebra`,
`corollary10` (in `wip/context_completeness.lean`, `wip/lax_infinite.lean`).
Object-logic `◯`-laws cited: `somehowR`/`somehowM`/`somehowS`/`somehowFunctor`
(`PLLTheorems.lean`), `not_provable_not_somehow_false` (`PLLFrames.lean`).

**Literature sources** (prose, verified citations):
`docs/iel-justification-lit.md` — IEL⁻ / justification-logic positioning (§8);
`docs/realisability-modal-lit.md` — realisability model-theory direction (§9), incl.
the four-frameworks comparison, the metatheory-vs-object-theory verdict, and the
local-nucleus-stability analysis.

**Consolidation note.** The `wip/belief_*.lean` files are self-contained, so
`closedNucleus` appears in both `belief_open_closed` and `belief_boolean_iso`, and
`nucleus_eq_sup_bot` in both `belief_boolean_collapse` and `belief_boolean_iso`.
When these move into the paper's Lean library, factor the shared `closedNucleus`
and the collapse into one base module and import it, to avoid duplicate `BeliefLax`
declarations.
