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

/-- info: 'FRJ.nf_ext' depends on axioms: [propext] -/
#guard_msgs in
#print axioms nf_ext

end FRJ
