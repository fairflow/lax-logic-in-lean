/-
# Lean certify acceptance test (lean-certify `docs/outline.md` §9)

`FinCM.checkB` and `not_provable_of_check` (`CountermodelEmit.lean`, unchanged)
packaged as a `Certify.Certifier`; one refutation of `Certified/RhoRefutations.lean`
reproduced through `Certifier.verdict`; the axiom pin; the gate watched
rejecting corrupted models; the lints run on `checkB`, on the `WellFounded.fix`
decider `decideG4`, and on `decideFuel`. Every outcome is pinned with
`#guard_msgs`, so a change in any of them fails the build.
-/
import LaxLogic.PLL.Semantics.CountermodelEmit
import LaxLogic.PLL.G4.G4Dec
import LaxLogic.PLL.Search.Decide
import LaxLogic.RN.Rho
import LeanCertify

open PLLND PLLFormula Certify

/-- The project's configuration, read by the lints. -/
def Harness.config : Harness.Config := { kernelTimeFlagSec := 60 }

namespace CertifyAdoption

/-- Finite countermodels as a certifier: a specification is a sequent
`(Γ, C)`, a certificate a model with a world, the property `Γ ⊬ C`. -/
def countermodel :
    Certifier (List PLLFormula × PLLFormula) (FinCM × Nat) (fun s => s.1 ⊬ s.2) where
  check s c := FinCM.checkB c.1 c.2 s.1 s.2
  sound _ _ h := FinCM.not_provable_of_check h

/-! ## One ρ refutation, through the gate

`ρ1 ⊬ ρ4` (`rho_1_nle_4` in `Certified/RhoRefutations.lean`), on the same
three-world model `cm_rho_1_4`, transcribed from its `Tab` (`leT`, `rmT`
without the diagonal; `falT` as the fallible list; `atomsT` all empty). -/

def cm_rho_1_4 : FinCM :=
  { n := 3, ri := [(0, 1), (0, 2), (1, 2)], rm := [(1, 2)], fall := [2], val := [] }

theorem rho_1_nle_4 : [RhoOrder.rhoF 1] ⊬ RhoOrder.rhoF 4 :=
  countermodel.verdict ([RhoOrder.rhoF 1], RhoOrder.rhoF 4) (cm_rho_1_4, 0)

/-- info: 'CertifyAdoption.rho_1_nle_4' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms rho_1_nle_4

/-- info: R4 passes: rho_1_nle_4 depends on [propext, Quot.sound] ⊆ [propext, Quot.sound] -/
#guard_msgs in #certify_axioms rho_1_nle_4

/-! ## The gate watched failing

The ρ formulas are closed (no atoms), so the only valuation `cm_rho_1_4`
has is that of `⊥`, i.e. the fallible set. Corrupting it (world 2 no
longer fallible) makes `ρ4` forced at the root: `checkB` returns `false`,
and the gate rejects the certificate. -/

def cm_rho_1_4_bad : FinCM := { cm_rho_1_4 with fall := [] }

example : countermodel.check ([RhoOrder.rhoF 1], RhoOrder.rhoF 4) (cm_rho_1_4_bad, 0) = false := by
  decide +kernel

/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: Tactic `decide` proved that the proposition
  countermodel.check ([RhoOrder.rhoF 1], RhoOrder.rhoF 4) (cm_rho_1_4_bad, 0) = true
is false
-/
#guard_msgs in
example : [RhoOrder.rhoF 1] ⊬ RhoOrder.rhoF 4 :=
  countermodel.verdict ([RhoOrder.rhoF 1], RhoOrder.rhoF 4) (cm_rho_1_4_bad, 0)

/-! A model with an atom, so that the corruption is of the valuation proper:
`◯p ⊬ p` on two worlds, `p` true only at world 1. Making `p` true at the
root forces the conclusion, and the gate rejects it. -/

def cm_somehow : FinCM :=
  { n := 2, ri := [(0, 1)], rm := [(0, 1)], fall := [], val := [(1, "p")] }

theorem somehow_p_nle_p : [(prop "p").somehow] ⊬ prop "p" :=
  countermodel.verdict ([(prop "p").somehow], prop "p") (cm_somehow, 0)

def cm_somehow_bad : FinCM := { cm_somehow with val := [(0, "p"), (1, "p")] }

example : countermodel.check ([(prop "p").somehow], prop "p") (cm_somehow_bad, 0) = false := by
  decide +kernel

/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: Tactic `decide` proved that the proposition
  countermodel.check ([◯(prop "p")], prop "p") (cm_somehow_bad, 0) = true
is false
-/
#guard_msgs in
example : [(prop "p").somehow] ⊬ prop "p" :=
  countermodel.verdict ([(prop "p").somehow], prop "p") (cm_somehow_bad, 0)

/-! ## The lints -/

-- R3 on the checker: must pass.
/-- info: R3 passes: the evaluation path of FinCM.checkB is structural -/
#guard_msgs in #certify_structural FinCM.checkB

/-- info: R3 passes: the evaluation path of countermodel is structural -/
#guard_msgs in #certify_structural countermodel

-- R2 on the certifier: `Γ ⊬ C` mentions no budget.
/-- info: R2 passes: the property of countermodel mentions no budget -/
#guard_msgs in #certify_statement countermodel

-- R3 on the Iemhoff G4 decider defined by `WellFounded.fix`: must flag.
/--
error: R3 fails: the evaluation path of G4.decideG4 reaches 1 constant(s) R3 forbids:
• WellFounded.fix [Init.WF]: well-founded recursion (does not reduce in the kernel)
    via [PLLND.G4.decideG4, WellFounded.fix]
-/
#guard_msgs in #certify_structural G4.decideG4

-- R1 on `decideFuel`: must report (`Finset.card` of the enumerated space).
/--
warning: R1 reports: the evaluation path of decideFuel counts or builds a domain at run time (1 site(s)); pass a cheap bound instead:
• Finset.card [Mathlib.Data.Finset.Card]: materialises or counts a domain
    via [PLLND.decideFuel, Finset.card]
-/
#guard_msgs in #certify_domain decideFuel

-- R3 on `decideFuel`: R1 rejects, R3 passes, by design. `decideFuel` is
-- closed-form arithmetic, structural throughout; its cost is materialising
-- `enum` to count it (docs/demos.md §3), which is R1's rule, reported above.
/-- info: R3 passes: the evaluation path of decideFuel is structural -/
#guard_msgs in #certify_structural decideFuel

-- The lints read the project's configuration.
/-- info: kernelTimeFlagSec = 60 -/
#guard_msgs in
open Lean Elab Command in
#eval show CommandElabM Unit from do
  logInfo m!"kernelTimeFlagSec = {(← liftTermElabM Harness.readConfig).kernelTimeFlagSec}"

end CertifyAdoption
