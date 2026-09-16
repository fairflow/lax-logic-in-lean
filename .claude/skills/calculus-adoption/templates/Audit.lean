/-
# Axiom audit

The standing guard.  Every pin below is `#guard_msgs`-checked, so a
regression is a BUILD FAILURE rather than something discovered months
later.  `collectAxioms` (i.e. `#print axioms`) is the only sound oracle;
`native_decide` taints and must not appear.

Generate each block with `#axiom_pin <name>` (Meta/Audit.lean) and paste
it here.  Do not retype a pin: a transcription slip is a silent hole in
the machine-checked mandate.

If a pin carries `Classical.choice`, either fix it — `#choice_path <name>`
says where it enters — or state, here, why it belongs to the STATEMENT
rather than the proof, and give the choice-free variant beside it.
-/
import <YourLib>.<Main>

namespace <YourNamespace>

/-! ## The headline results -/

-- #axiom_pin soundness   ← run this, paste the result below

/-- info: 'X.soundness' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms soundness

/-! ## The machinery -/

/-! ## Where nothing at all is assumed -/

end <YourNamespace>
