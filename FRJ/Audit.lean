/-
# Axiom audit

The standing guard.  Every pin below is `#guard_msgs`-checked, so a
regression is a BUILD FAILURE rather than something discovered months
later.  `collectAxioms` (i.e. `#print axioms`) is the only sound oracle;
`native_decide` would taint and is not used anywhere in `FRJ/`.

`Classical.choice` appears exactly once, in `frj_iff_not_IPL`, and for a
reason that is a property of the STATEMENT, not of the proof: passing
from "not every model validates `G`" to "some model refutes `G`" is not
constructively valid.  `frj_iff_countermodel` is the same theorem with
that step left to the caller, and it is choice-free.
-/
import FRJ.Minimal
import FRJ.Saturate
import FRJ.Erase

namespace FRJ

/-! ## The headline results -/

/-- info: 'FRJ.soundness' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms soundness

/-- info: 'FRJ.completeness' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms completeness

/-- info: 'FRJ.completenessData' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms completenessData

/-- info: 'FRJ.frj_iff_countermodel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms frj_iff_countermodel

-- The paper's statement, and the one place `Classical.choice` enters.
/-- info: 'FRJ.frj_iff_not_IPL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms frj_iff_not_IPL

/-! ## The machinery -/

/-- info: 'FRJ.minMod' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms minMod

/-- info: 'FRJ.visit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms visit

/-- info: 'FRJ.completeness_of_supply' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms completeness_of_supply

/-- info: 'FRJ.completeness_of_discrete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms completeness_of_discrete

/-- info: 'FRJ.completeness_of_allMet' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms completeness_of_allMet

/-- info: 'FRJ.frj_iff_root_countermodel_of_allMet' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms frj_iff_root_countermodel_of_allMet

/-- info: 'FRJ.completeness_via_closure' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms completeness_via_closure

/-- info: 'FRJ.provable_root_countermodel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms provable_root_countermodel

/-- info: 'FRJ.modR_countermodel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms modR_countermodel

/-- info: 'FRJ.lemma39R' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lemma39R

/-- info: 'FRJ.lemma39I' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lemma39I

/-- info: 'FRJ.lhs_clo_of_steps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lhs_clo_of_steps

/-- info: 'FRJ.minEta' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms minEta

/-! ## Where nothing at all is assumed -/

/-- info: 'FRJ.Kripke.decForce' does not depend on any axioms -/
#guard_msgs in
#print axioms Kripke.decForce

/-- info: 'FRJ.maxOn' does not depend on any axioms -/
#guard_msgs in
#print axioms maxOn

/-- info: 'FRJ.eq_nil_of_forall_not_mem' does not depend on any axioms -/
#guard_msgs in
#print axioms eq_nil_of_forall_not_mem

/-- info: 'FRJ.Kripke.force_mono' does not depend on any axioms -/
#guard_msgs in
#print axioms Kripke.force_mono

/-- info: 'FRJ.not_IPL_of_countermodel' does not depend on any axioms -/
#guard_msgs in
#print axioms not_IPL_of_countermodel

/-- info: 'FRJ.CtxEq' does not depend on any axioms -/
#guard_msgs in
#print axioms CtxEq

/-- info: 'FRJ.CtxEq.of_subset' does not depend on any axioms -/
#guard_msgs in
#print axioms CtxEq.of_subset

-- **Contexts are sets.**  The transport `Σ ≐ Σ' → Θ ≐ Θ' →
-- FRJi G Σ Θ C → FRJi G Σ' Θ' C` — declared FALSE for this family while
-- `Ax^I` pinned its own zone, a theorem since the deslime.
/-- info: 'FRJ.transportI' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms transportI

-- The regular half of the same statement: a derivation of `Γ ⇒ C` transports
-- to any `Γ'` with the same members.  The two context-sensitive side
-- conditions travel by monotonicity (`clo_mono`, `covers_mono`).
/-- info: 'FRJ.covers_mono' does not depend on any axioms -/
#guard_msgs in
#print axioms covers_mono

/-- info: 'FRJ.transportR' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms transportR

/-! ### The `◯`-corner kernel, closed on cone-grounded frames (2026-08-18)

`coneTrivial_of_corner` turns W4 §10 fact 3 from an observation into a
lemma: the kernel's own hypothesis pins the demanding world's modal cone
to itself, with NO assumption on the frame.  On a frame where
cone-triviality implies maximality — `Rm = ≤` in particular — the
generalised `Ax^I◯` then closes the kernel outright. -/

/-- info: 'FRJ.coneTrivial_of_corner' does not depend on any axioms -/
#guard_msgs in
#print axioms coneTrivial_of_corner

/-- info: 'FRJ.circSupply_of_coneGrounded' depends on axioms: [propext] -/
#guard_msgs in
#print axioms circSupply_of_coneGrounded

/-- info: 'FRJ.completeness_of_coneGrounded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms completeness_of_coneGrounded

/-- info: 'FRJ.completeness_of_rmFull' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms completeness_of_rmFull

-- The unconditional instance: no supply hypothesis, `◯` free on the right.
/-- info: 'FRJ.completeness_of_rmFull_of_circFreeL' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms completeness_of_rmFull_of_circFreeL

/-- info: 'FRJ.discrete_of_transparent_of_coneGrounded' does not depend on any axioms -/
#guard_msgs in
#print axioms discrete_of_transparent_of_coneGrounded

/-! ## W3 and the promise-join screen -/

/-- info: 'FRJ.Kripke.fal_force' does not depend on any axioms -/
#guard_msgs in
#print axioms Kripke.fal_force

/-- info: 'FRJ.Kripke.exists_common_witness' does not depend on any axioms -/
#guard_msgs in
#print axioms Kripke.exists_common_witness

/-- info: 'FRJ.Kripke.exists_common_witness_list' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Kripke.exists_common_witness_list

/-- info: 'FRJ.Kripke.circ_and' does not depend on any axioms -/
#guard_msgs in
#print axioms Kripke.circ_and

/-! ### Erasure transfer (FRJ/Erase.lean, 2026-08-17) -/

/-- info: 'FRJ.force_erase' does not depend on any axioms -/
#guard_msgs in
#print axioms force_erase

/-- info: 'FRJ.erase_hcf' depends on axioms: [propext] -/
#guard_msgs in
#print axioms erase_hcf

/-- info: 'FRJ.completeness_of_transparent_of_lift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms completeness_of_transparent_of_lift

/-- info: 'FRJ.circPart_lamStar_nil_of_transparent' depends on axioms: [propext] -/
#guard_msgs in
#print axioms circPart_lamStar_nil_of_transparent

/-- info: 'FRJ.completeness_of_transparent_of_circSupply' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms completeness_of_transparent_of_circSupply

/-- info: 'FRJ.clo_lift' depends on axioms: [propext] -/
#guard_msgs in
#print axioms clo_lift

end FRJ
