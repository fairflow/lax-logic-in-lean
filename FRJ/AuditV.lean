/-
# Axiom audit — the repaired (RefAt) calculus

The standing guard for the `FRJV` stack (`docs/refat-plan.md`): every pin
`#guard_msgs`-checked, `collectAxioms` the only oracle, no
`native_decide` anywhere in the stack, no `Classical.choice`.

The trust story this file pins, end to end:

* the semantic kill lemma and the greedy chain certificate
  (`refAt_refutes`, `keptOf_ok`);
* the paper calculus embeds in the repaired one
  (`provableV_of_provable`);
* the repaired calculus is SOUND (`soundnessV`) — Lemma 3.9 and the
  pledge (`FRJ.V.lemma39R`, `FRJ.V.tag_cone`) over the new family;
* it DERIVES the two cells the paper calculus provably cannot
  (`wip/frjv_witness.lean`; the paper-side impossibility theorems are
  `wip/frj80_noprov.lean` / `wip/frj81_noprov.lean` — those files also
  pin themselves, and the witness/consequence pins live with them so the
  audit of `FRJ/` proper stays wip-free).
-/
import FRJ.RefAt
import FRJ.CalculusV
import FRJ.SoundV
import FRJ.BridgeV

namespace FRJ

/-! ## The RefAt layer -/

/-- info: 'FRJ.refAt_refutes' does not depend on any axioms -/
#guard_msgs in
#print axioms refAt_refutes

/-- info: 'FRJ.keptOf_ok' depends on axioms: [propext] -/
#guard_msgs in
#print axioms keptOf_ok

/-- info: 'FRJ.refAtB_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms refAtB_iff

/-! ## The embedding: paper ⊆ repaired -/

/-- info: 'FRJ.provableV_of_provable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms provableV_of_provable

/-! ## Soundness of the repaired calculus -/

/-- info: 'FRJ.V.lemma39R' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms V.lemma39R

/-- info: 'FRJ.V.tag_cone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms V.tag_cone

/-- info: 'FRJ.soundnessV' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms soundnessV

/-! ## The bridge -/

/-- info: 'FRJ.not_entails_of_provableV' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms not_entails_of_provableV

end FRJ
