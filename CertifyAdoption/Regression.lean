/-
Copyright (c) 2026 Matthew Fairtlough. All rights reserved.
-/
import CertifyAdoption.CheckDeriv
import Harness.Gates

/-!
# lean-certify: regression test for every use in this repository

Every use of lean-certify in lax-logic-in-lean is in `CertifyAdoption.lean`
(the countermodel certifier `countermodel`) and `CertifyAdoption/CheckDeriv.lean`
(the derivation certifiers `derivCertifier`, `laxNDCertifier` and the engine
`derivEngine`).  This module pins, with `#guard_msgs`, what lean-certify says
about each of them and about every theorem proved by evaluation through them,
and runs each checker once with its expected verdict.  A lean-certify release
that changes any of this fails the build here.

Pinned against v0.2.1 (2026-10-14), where R3 and R1 on a theorem walk the
computation its proof performs by evaluation (in v0.2.0 they walked nothing).
The two files it imports pin the lints on the declarations themselves (R2, R3,
and the R1/R3 verdicts on `decideFuel` and `G4.decideG4`); this module adds
R1 and R4 on the certifiers and R1, R3, R4 on the theorems.

Since 2026-10-27 (F0 plan step 4) it also pins the project decider's two
certifiers, `PLLDecider.fincmNo` and `PLLDecider.ljfoYes`
(`Harness/Tools.lean`), the theorems proved through them
(`Harness/Gates.lean`), and their producers' budgets; see the last section.

Build: `lake build CertifyAdoption.Regression`.  It needs the LJF◯ chain, so CI
builds it on pull requests that touch lean-certify's pin, `CertifyAdoption/` or
`LJF/`, and in the weekly full check.
-/

open PLLND PLLFormula LJFO Certify CertifyAdoption CertifyAdoption.CheckDeriv

namespace CertifyAdoption.Regression

/-! ## R1 and R4 on every certifier and engine -/

/-- info: R1: nothing to report on countermodel -/
#guard_msgs in #certify_domain countermodel

/-- info: R1: nothing to report on derivCertifier -/
#guard_msgs in #certify_domain derivCertifier

/-- info: R1: nothing to report on laxNDCertifier -/
#guard_msgs in #certify_domain laxNDCertifier

/-- info: R1: nothing to report on derivEngine -/
#guard_msgs in #certify_domain derivEngine

/-- info: R4 passes: countermodel depends on [propext, Quot.sound] ⊆ [propext, Quot.sound] -/
#guard_msgs in #certify_axioms countermodel

/-! ## R3, R1 and R4 on every theorem proved by evaluation through a certifier -/

/--
info: R3 passes: the evaluation path of rho_1_nle_4, walked from what its proof decides by evaluation:
  countermodel.check ([RhoOrder.rhoF 1], RhoOrder.rhoF 4) (cm_rho_1_4, 0) = true
is structural
-/
#guard_msgs in #certify_structural rho_1_nle_4

/--
info: R3 passes: the evaluation path of somehow_p_nle_p, walked from what its proof decides by evaluation:
  countermodel.check ([◯(prop "p")], prop "p") (cm_somehow, 0) = true
is structural
-/
#guard_msgs in #certify_structural somehow_p_nle_p

/--
info: R3 passes: the evaluation path of edge_rho3_rho4, walked from what its proof decides by evaluation:
  laxNDCertifier.check ([nOBot], nOBot ∨ oBot) treeEdge = true
is structural
-/
#guard_msgs in #certify_structural edge_rho3_rho4

/--
info: R3 passes: the evaluation path of probe_or_11_18, walked from what its proof decides by evaluation:
  laxNDCertifier.check ([RhoOrder.rhoF 15], RhoOrder.rhoF 11 ∨ RhoOrder.rhoF 18) treeOrBack = true
  laxNDCertifier.check ([RhoOrder.rhoF 11 ∨ RhoOrder.rhoF 18], RhoOrder.rhoF 15) treeOr = true
is structural
-/
#guard_msgs in #certify_structural probe_or_11_18

/--
info: R1: nothing to report on rho_1_nle_4, walked from what its proof decides by evaluation:
  countermodel.check ([RhoOrder.rhoF 1], RhoOrder.rhoF 4) (cm_rho_1_4, 0) = true
-/
#guard_msgs in #certify_domain rho_1_nle_4

/--
info: R1: nothing to report on edge_rho3_rho4, walked from what its proof decides by evaluation:
  laxNDCertifier.check ([nOBot], nOBot ∨ oBot) treeEdge = true
-/
#guard_msgs in #certify_domain edge_rho3_rho4

/-- info: R4 passes: somehow_p_nle_p depends on [propext, Quot.sound] ⊆ [propext, Quot.sound] -/
#guard_msgs in #certify_axioms somehow_p_nle_p

/-- info: R4 passes: edge_rho3_rho4 depends on [propext, Quot.sound] ⊆ [propext, Quot.sound] -/
#guard_msgs in #certify_axioms edge_rho3_rho4

/-- info: R4 passes: probe_or_11_18 depends on [propext, Quot.sound] ⊆ [propext, Quot.sound] -/
#guard_msgs in #certify_axioms probe_or_11_18

/-! ## One certified run per checker, with its expected verdict

Each in the kernel (`decide +kernel`), small: a two-world model, a short tree. -/

-- `countermodel` (checker `FinCM.checkB`): accepts the model of `◯p ⊬ p`, rejects its corruption.
example : countermodel.check ([(prop "p").somehow], prop "p") (cm_somehow, 0) = true := by
  decide +kernel
example : countermodel.check ([(prop "p").somehow], prop "p") (cm_somehow_bad, 0) = false := by
  decide +kernel

-- `laxNDCertifier`: accepts the tree for `[¬◯⊥] ⊢ ¬◯⊥ ∨ ◯⊥`, rejects a wrong rule index.
example : laxNDCertifier.check ([nOBot], .or nOBot oBot) treeEdge = true := by
  decide +kernel
example : laxNDCertifier.check ([nOBot], .or nOBot oBot) (badIndex treeEdge) = false := by
  decide +kernel

-- `derivCertifier` (checker `checkDeriv` on the LJF◯ sequent), same tree.
example : derivCertifier.check (decideSeq [nOBot] (.or nOBot oBot)) treeEdge = true := by
  decide +kernel
example : derivCertifier.check (decideSeq [nOBot] (.or nOBot oBot)) (badArity treeEdge) = false := by
  decide +kernel

-- `derivEngine`: the untrusted producer finds a tree for `p ↠ p` within budget 5,
-- and the certifier accepts it; with budget 0 it flags.
def verdictTag {C R : Type} : Verdict C R → String
  | .pass _ => "pass" | .fail _ => "fail" | .flag => "flag"

/-- info: "pass" -/
#guard_msgs in #eval verdictTag (derivEngine.produce (decideSeq [] (.ifThen (prop "p") (prop "p"))) 5)

/-- info: "flag" -/
#guard_msgs in #eval verdictTag (derivEngine.produce (decideSeq [] (.ifThen (prop "p") (prop "p"))) 0)

/-- info: true -/
#guard_msgs in #eval
  match derivEngine.produce (decideSeq [] (.ifThen (prop "p") (prop "p"))) 5 with
  | .pass t => derivCertifier.check (decideSeq [] (.ifThen (prop "p") (prop "p"))) t
  | _ => false

/-! ## The project decider's certifiers `fincm` and `ljfo` (2026-10-27)

`PLLDecider.fincmNo` and `PLLDecider.ljfoYes` (`Harness/Tools.lean`), at the
specification `PLLND.SubTab.Holds`; the theorems proved through them are the
exemplars of `Harness/Gates.lean`. -/

section Harness

open PLLDecider PLLDecider.Gates

/-- info: R1: nothing to report on fincmNo -/
#guard_msgs in #certify_domain fincmNo

/-- info: R1: nothing to report on ljfoYes -/
#guard_msgs in #certify_domain ljfoYes

/-- info: R4 passes: fincmNo depends on [propext, Quot.sound] ⊆ [propext, Quot.sound] -/
#guard_msgs in #certify_axioms fincmNo

/-- info: R4 passes: ljfoYes depends on [propext, Quot.sound] ⊆ [propext, Quot.sound] -/
#guard_msgs in #certify_axioms ljfoYes

/--
info: R3 passes: the evaluation path of not_peirce, walked from what its proof decides by evaluation:
  fincmNo.check Gates.peirce (cmPeirce, 0) = true
is structural
-/
#guard_msgs in #certify_structural not_peirce

/--
info: R3 passes: the evaluation path of not_somehowP, walked from what its proof decides by evaluation:
  fincmNo.check somehowP (cmSomehow, 0) = true
is structural
-/
#guard_msgs in #certify_structural not_somehowP

/--
info: R3 passes: the evaluation path of unit_p, walked from what its proof decides by evaluation:
  ljfoYes.check unitP treeUnit = true
is structural
-/
#guard_msgs in #certify_structural unit_p

/--
info: R3 passes: the evaluation path of gap, walked from what its proof decides by evaluation:
  ljfoYes.check gapCell treeGap = true
is structural
-/
#guard_msgs in #certify_structural gap

/--
info: R1: nothing to report on not_somehowP, walked from what its proof decides by evaluation:
  fincmNo.check somehowP (cmSomehow, 0) = true
-/
#guard_msgs in #certify_domain not_somehowP

/--
info: R1: nothing to report on gap, walked from what its proof decides by evaluation:
  ljfoYes.check gapCell treeGap = true
-/
#guard_msgs in #certify_domain gap

/-- info: R4 passes: not_peirce depends on [propext, Quot.sound] ⊆ [propext, Quot.sound] -/
#guard_msgs in #certify_axioms not_peirce

/-- info: R4 passes: not_somehowP depends on [propext, Quot.sound] ⊆ [propext, Quot.sound] -/
#guard_msgs in #certify_axioms not_somehowP

/-- info: R4 passes: unit_p depends on [propext, Quot.sound] ⊆ [propext, Quot.sound] -/
#guard_msgs in #certify_axioms unit_p

/-- info: R4 passes: gap depends on [propext, Quot.sound] ⊆ [propext, Quot.sound] -/
#guard_msgs in #certify_axioms gap

-- `fincmNo`: accepts the model of `⊬ ◯p ↠ p`, rejects its corruption.
example : fincmNo.check somehowP (cmSomehow, 0) = true := by decide +kernel
example : fincmNo.check somehowP (cmSomehowBad, 0) = false := by decide +kernel

-- `ljfoYes`: accepts the tree for `⊢ p ↠ ◯p`, rejects a wrong rule index.
example : ljfoYes.check unitP treeUnit = true := by decide +kernel
example : ljfoYes.check unitP (badIndex treeUnit) = false := by decide +kernel

-- The producers mean their budgets: at budget 1000 each finds a certificate
-- that its certifier accepts; at budget 0 neither does (`fincm`: the G4c
-- pre-check is cut off at once; `ljfo`: depth bound 0).

/-- info: true -/
#guard_msgs in #eval match fincmProduce somehowP 1000 with
  | some c => fincmNo.check somehowP c
  | none => false

/-- info: false -/
#guard_msgs in #eval (fincmProduce somehowP 0).isSome

/-- info: true -/
#guard_msgs in #eval match ljfoProduce unitP 1000 with
  | some t => ljfoYes.check unitP t
  | none => false

/-- info: false -/
#guard_msgs in #eval (ljfoProduce unitP 0).isSome

end Harness

end CertifyAdoption.Regression
