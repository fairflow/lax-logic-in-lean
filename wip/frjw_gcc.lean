/-
# W4 — the duality gap closes: an irregular FRJW disproof of `◯(◯p ⊃ p)`

Stage W4 of `docs/frjw-plan.md`.  The three machine-checked facts that
motivated `Lift` (plan §2), as they stood on 2026-08-31:

* (a) FRJV had NO irregular disproof of `◯(◯Z ⊃ Z)`, for any `G`, `Z`,
  `Σ`, `Θ` (`FRJ.V.WCounter.no_irregular_circ_imp_self`, since withdrawn:
  (a) is REFUTED for the current `FRJVi`, see below);
* (b) Gbu◯ cannot prove `∅ →g ◯(◯p ⊃ p)`, and must not
  (`FRJ.Gbu.not_gbuIC_Gcc`);
* (c) a regular FRJV disproof of `◯(◯p ⊃ p)` exists
  (`FRJ.Gbu.provableV_Gcc`) but was unusable where an irregular one is
  required.

This file is the test the whole exercise was for: in FRJW the (a)/(b)
mismatch is gone,

    ∅ ; ∅ → ◯(◯p ⊃ p)      is an FRJW(Gcc) disproof,

by `lift` applied to the regular witness `GccWitness` (transported into
FRJW by W2's conservativity `toWr`, the transport this stage licensed),
with the retained context empty, so `lift`'s side condition is vacuous
(`gccIrregular`, and in `Nonempty` form `gccIrregular_nonempty`).

## The FRJV half is REFUTED for the current `FRJVi`

The file first displayed the closure as one conjunction, `duality_closed`,

    Nonempty (FRJWi Gcc [] [] Gcc) ∧ (FRJVi Gcc [] [] Gcc → False)

with the second conjunct taken from (a).  That conjunct held for `FRJVi`
before the constructor `liftI` (the rule `(Lift)`) was added to it
(993ea740, 2026-09-01), and it is REFUTED for the current `FRJVi`: `liftI`
applied to the same regular witness `GccWitness`, with the retained
context empty, is an irregular FRJV disproof of `Gcc`
(`not_frjvi_Gcc_impossible`),

    ¬ (FRJVi Gcc [] [] Gcc → False)

The positive result that supersedes (a) is
`FRJ.V.WCounter.irregular_circ_imp_self_lifts` (`wip/gbu_weakening.lean`):
every irregular FRJV disproof of `◯(◯Z ⊃ Z)` comes from a regular one,

    FRJVi G St Th (◯(◯Z ⊃ Z)) → ∃ t Γ, Nonempty (FRJVr G t Γ (◯(◯Z ⊃ Z)))

`duality_closed` was withdrawn on 2026-10-31
(`docs/nightly-fix-2026-10-31.md`); its first conjunct is
`gccIrregular_nonempty`.
-/
import FRJ.SoundW
import wip.gbu_search_circ
import Meta.Audit

namespace FRJ.W

open FRJ Form

/-- **The duality gap closes** (stage W4): `∅ ; ∅ → ◯(◯p ⊃ p)` in
`FRJW(Gcc)`.  `lift` turns the W2-transported regular witness into an
irregular disproof.  (Since `liftI` joined `FRJVi`, FRJV has one too:
`not_frjvi_Gcc_impossible`.) -/
def gccIrregular : FRJWi Gbu.Gcc [] [] Gbu.Gcc :=
  .lift (toWr Gbu.GccWitness.2) (fun _ hX => absurd hX List.not_mem_nil)

/-- The first conjunct of the withdrawn `duality_closed`: an irregular FRJW
disproof of `Gcc` with both contexts empty. -/
theorem gccIrregular_nonempty : Nonempty (FRJWi Gbu.Gcc [] [] Gbu.Gcc) :=
  ⟨gccIrregular⟩

/-- **The second conjunct of the withdrawn `duality_closed` is REFUTED** for
the current `FRJVi`: `(Lift)`, the constructor `liftI` added on 2026-09-01,
applied to the regular disproof `GccWitness` with the retained context empty,
is an irregular FRJV disproof of `Gcc`.  The conjunct held before `liftI`
(`no_irregular_circ_imp_self`, withdrawn); the superseding positive result is
`FRJ.V.WCounter.irregular_circ_imp_self_lifts`. -/
theorem not_frjvi_Gcc_impossible : ¬ (FRJVi Gbu.Gcc [] [] Gbu.Gcc → False) :=
  fun h => h (.liftI Gbu.GccWitness.2 (fun _ hX => absurd hX List.not_mem_nil))

/-- Sanity: the lifted disproof still lives over a sound calculus — the
judgment's regular side already refutes `Gcc` in PLL (re-derived through
`soundnessW` rather than quoted from `not_pll_Gcc`). -/
example : ¬ PLL Gbu.Gcc :=
  soundnessW ⟨.barren, Gbu.GccWitness.1, ⟨toWr Gbu.GccWitness.2⟩⟩

/-! ## Axiom pins -/

/-- info: 'FRJ.W.gccIrregular' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms gccIrregular

/-- info: 'FRJ.W.gccIrregular_nonempty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms gccIrregular_nonempty

/-- info: 'FRJ.W.not_frjvi_Gcc_impossible' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms not_frjvi_Gcc_impossible

end FRJ.W

#axioms_within FRJ.W.gccIrregular_nonempty [propext, Quot.sound]
#axioms_within FRJ.W.not_frjvi_Gcc_impossible [propext, Quot.sound]
