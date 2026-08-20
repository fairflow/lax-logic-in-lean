import Core

/-!
# The standing axiom audit for the publishable core

`#print axioms` is the only sound oracle for what a theorem actually
rests on (`collectAxioms`); `native_decide` taints, and is not used
anywhere in the core.  Every pin below is `#guard_msgs`-checked, so an
axiom regression is a BUILD FAILURE rather than something discovered
months later.

Read an entry as: *this theorem is machine-checked, and these are the
only axioms it uses.*  What may legitimately appear:

* `propext` — propositional extensionality;
* `Quot.sound` — the quotient axiom;
* `Classical.choice` — where it appears, it is usually a property of the
  STATEMENT rather than a weakness of the proof: passing from "not every
  model validates φ" to "some model refutes φ" is not constructively
  valid.

What must never appear: `sorryAx` (an unproved claim) or
`Lean.ofReduceBool` (a `native_decide` result, trusting the compiled
evaluator rather than the kernel).

One campaign's terminal result is a REFUTATION rather than a theorem —
Iemhoff's `G4iLL` is incomplete for PLL — and it is pinned here on the
same footing, because a machine-checked counterexample is a result.

The section numbers match those of `Core.lean` and of `README.md`.
-/

namespace Core.Audit

/-! ## 1. `LaxND` — the reference system -/

/-- info: 'PLLND.conservativity_prop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.conservativity_prop

/-- info: 'PLLND.conservativity_IPL' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.conservativity_IPL
/-- info: 'PLLND.hd_iff_ND' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PLLND.hd_iff_ND

/-! ## 2. Constraint semantics -/

/-- info: 'PLLND.soundness' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PLLND.soundness

/-- info: 'PLLND.completeness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.completeness

/-- info: 'PLLND.finite_model_property' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.finite_model_property

/-- info: 'PLLND.SemUI.force_iff_of_bisim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.SemUI.force_iff_of_bisim

/-! ## 3. `SC` — cut elimination and the disjunction property -/

/-- info: 'PLLND.cutElimination' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.cutElimination

/-- info: 'PLLND.disjunction_property' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.disjunction_property

/-! ## 4. `G4iLL` REFUTED, and the repaired calculus `G4c` -/

/-- info: 'PLLG4Gap.cut_not_admissible' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PLLG4Gap.cut_not_admissible

/-- info: 'PLLG4Gap.contraction_not_admissible' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PLLG4Gap.contraction_not_admissible

/-- info: 'PLLND.G4c.cut' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.G4c.cut

/-- info: 'PLLND.G4c.contract' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.G4c.contract

/-- info: 'PLLND.G4c.completeness' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.G4c.completeness

/-- info: 'PLLND.G4c.equiv_sc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.G4c.equiv_sc

/-- info: 'PLLND.G4c.equiv_nd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.G4c.equiv_nd

/-- info: 'PLLND.G4c.equiv_tm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.G4c.equiv_tm

/-- info: 'PLLND.decidablePLL' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.decidablePLL

/-! ## 5. Strong normalisation -/

/-- info: 'PLLND.strong_normalisation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.strong_normalisation

/-! ## 6. Curry's problem (F&M, TYPES 2000) -/

/-- info: 'PLLND.Ctx.thm6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.Ctx.thm6

/-- info: 'PLLND.Ctx.corollary10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.Ctx.corollary10

/-! ## 7. PCLL and the infallible extension -/

/-- info: 'PLLND.ConfluentU.derivU_iff_confluent_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.ConfluentU.derivU_iff_confluent_valid

/-- info: 'PLLND.NoFall.derivUNoFall_iff_confluent_infallible_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.NoFall.derivUNoFall_iff_confluent_infallible_valid

/-- info: 'PLLND.NoFall.varfree_dichotomy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.NoFall.varfree_dichotomy

/-! ## 8. The closed fragment RN(◯,{}) -/

/-- info: 'PLLND.LaxInfinite.closed_lax_infinite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.LaxInfinite.closed_lax_infinite

/-! ## 9. Craig interpolation -/

/-- info: 'PLLND.craig_interpolation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.craig_interpolation

/-! ## 10. Certified countermodels -/

/-- info: 'PLLND.FinComp.emitter_completeness' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.FinComp.emitter_completeness

/-! ## 11. Timing analysis (Mendler, FMSD 2000) -/

/-- info: 'PLLND.circUp_rising' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.circUp_rising
/-- info: 'PLLND.falsePath_beats_topological' does not depend on any axioms -/
#guard_msgs in
#print axioms PLLND.falsePath_beats_topological

/-! ## 12. Belief, nuclei, and realisability -/

/-- info: 'BeliefLax.nucleus_himp_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeliefLax.nucleus_himp_le
/-- info: 'BeliefLax.nucleus_eq_sup_bot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeliefLax.nucleus_eq_sup_bot

/-- info: 'PLLND.BeliefReal.derivable_iff_no_realP_refutation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.BeliefReal.derivable_iff_no_realP_refutation

/-! ## 13. `FRJ(G)` for IPC -/

/-- info: 'FRJ.soundness' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms FRJ.soundness

/-- info: 'FRJ.completeness' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms FRJ.completeness

/-- info: 'FRJ.frj_iff_not_IPL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FRJ.frj_iff_not_IPL

/-! ## 14. `Reject` — refutation as positive derivation, for PLL -/

/-- info: 'Reject.built_iff_of_reduced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Reject.built_iff_of_reduced

/-- info: 'Reject.not_laxND_of_built' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Reject.not_laxND_of_built

end Core.Audit
