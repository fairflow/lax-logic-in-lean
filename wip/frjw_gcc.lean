/-
# W4 — the duality gap closes: an irregular FRJW disproof of `◯(◯p ⊃ p)`

Stage W4 of `docs/frjw-plan.md`.  The three machine-checked facts that
motivated `Lift` (plan §2):

* (a) FRJV has NO irregular disproof of `◯(◯Z ⊃ Z)` — for any `G`, `Z`,
  `Σ`, `Θ` (`FRJ.V.WCounter.no_irregular_circ_imp_self`);
* (b) Gbu◯ cannot prove `∅ →g ◯(◯p ⊃ p)`, and must not
  (`FRJ.Gbu.not_gbuIC_Gcc`);
* (c) a regular FRJV disproof of `◯(◯p ⊃ p)` exists
  (`FRJ.Gbu.provableV_Gcc`) but is unusable where an irregular one is
  required.

This file is the test the whole exercise was for: in FRJW the (a)/(b)
mismatch is gone —

    ∅ ; ∅ → ◯(◯p ⊃ p)      is an FRJW(Gcc) disproof,

by `lift` applied to the regular witness `GccWitness` (transported into
FRJW by W2's conservativity `toWr` — the transport this stage is what
licensed), with the retained context empty, so `lift`'s side condition
is vacuous.  `duality_closed` displays the closure as one statement:
the FRJW disproof exists at exactly the indices where the FRJV one is
provably impossible.
-/
import FRJ.SoundW
import wip.gbu_search_circ

namespace FRJ.W

open FRJ Form

/-- **The duality gap closes** (stage W4): `∅ ; ∅ → ◯(◯p ⊃ p)` in
`FRJW(Gcc)`.  `lift` turns the W2-transported regular witness into the
irregular disproof that FRJV provably lacks. -/
def gccIrregular : FRJWi Gbu.Gcc [] [] Gbu.Gcc :=
  .lift (toWr Gbu.GccWitness.2) (fun _ hX => absurd hX List.not_mem_nil)

/-- The same cell in `Nonempty` form, next to its FRJV impossibility. -/
theorem duality_closed :
    Nonempty (FRJWi Gbu.Gcc [] [] Gbu.Gcc) ∧
      (FRJVi Gbu.Gcc [] [] Gbu.Gcc → False) :=
  ⟨⟨gccIrregular⟩, fun d => V.WCounter.no_irregular_circ_imp_self
    (show FRJVi _ _ _ (.circ (.imp (.circ (.atom "p")) (.atom "p"))) from d)⟩

/-- Sanity: the lifted disproof still lives over a sound calculus — the
judgment's regular side already refutes `Gcc` in PLL (re-derived through
`soundnessW` rather than quoted from `not_pll_Gcc`). -/
example : ¬ PLL Gbu.Gcc :=
  soundnessW ⟨.barren, Gbu.GccWitness.1, ⟨toWr Gbu.GccWitness.2⟩⟩

/-! ## Axiom pins -/

/-- info: 'FRJ.W.gccIrregular' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms gccIrregular

/-- info: 'FRJ.W.duality_closed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms duality_closed

end FRJ.W
