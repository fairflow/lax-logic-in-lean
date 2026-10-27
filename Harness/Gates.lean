import Harness.Tools

/-!
# Gates of the `fincm` and `ljfo` certifiers: exemplars and negative tests

2026-10-27, F0 re-implementation plan step 4 (`docs/f0-step4-STATUS.md`).
The certificates below were emitted by the untrusted producers of
`Harness/Tools.lean` at budget 1000 on the ◯-free and PLL smoke cells of
`docs/engine-adoption-statements.md` §6, and are judged here by the kernel
(`Certifier.verdict`, `decide +kernel`):

    ⊬ ((p ↠ q) ↠ p) ↠ p                     fincm, 2 worlds
    ⊬ ◯p ↠ p                                fincm, 2 worlds
    ⊢ p ↠ ◯p                                ljfo, a tree of 6 nodes
    ⊢ ◯((◯p ↠ r) ↠ ◯p) ↠ (◯p ↠ r) ↠ r       ljfo, a tree of 49 nodes (the G4iLL gap)

Negative tests: a tampered certificate of each kind is rejected by the
checker in the kernel, by `verdict` (pinned error), and by the decider's
run-time gate (`Prover.gate`, `Disprover.gate`: REJECTED, a tool defect).
Each negative test was watched failing on the untampered certificate
(`docs/f0-step4-STATUS.md`).
-/

open PLLND PLLFormula Certify

namespace PLLDecider.Gates

def p : PLLFormula := prop "p"
def q : PLLFormula := prop "q"
def r : PLLFormula := prop "r"

/-- `((p ↠ q) ↠ p) ↠ p`, Peirce's law (◯-free; not derivable). -/
def peirce : PLLFormula := ((p.ifThen q).ifThen p).ifThen p
/-- `p ↠ ◯p` (derivable). -/
def unitP : PLLFormula := p.ifThen p.somehow
/-- `◯p ↠ p` (not derivable). -/
def somehowP : PLLFormula := p.somehow.ifThen p
/-- `◯((◯p ↠ r) ↠ ◯p) ↠ (◯p ↠ r) ↠ r` (derivable; Iemhoff's G4iLL misses it). -/
def gapCell : PLLFormula :=
  (((p.somehow.ifThen r).ifThen p.somehow).somehow).ifThen ((p.somehow.ifThen r).ifThen r)

/-! ## `fincm` -/

/-- Worlds `0 ≤ 1`, `Rₘ` the identity, `p` true at 1 only: at 0,
`(p ↠ q) ↠ p` is forced (no world forces `p ↠ q`) and `p` is not. -/
def cmPeirce : FinCM :=
  { n := 2, ri := [(0, 0), (0, 1), (1, 1)], rm := [(0, 0), (1, 1)], fall := [],
    val := [(1, "p")] }

/-- Worlds `0 ≤ 1`, `Rₘ = Rᵢ`, `p` true at 1 only: at 0, `◯p` is forced
and `p` is not. -/
def cmSomehow : FinCM :=
  { n := 2, ri := [(0, 0), (0, 1), (1, 1)], rm := [(0, 0), (0, 1), (1, 1)], fall := [],
    val := [(1, "p")] }

theorem not_peirce : SubTab.Holds peirce → False := fincmNo.verdict peirce (cmPeirce, 0)

theorem not_somehowP : SubTab.Holds somehowP → False :=
  fincmNo.verdict somehowP (cmSomehow, 0)

/-- Tampered: `p` made true at the root, which then forces `◯p ↠ p`. -/
def cmSomehowBad : FinCM := { cmSomehow with val := [(0, "p"), (1, "p")] }

example : fincmNo.check somehowP (cmSomehowBad, 0) = false := by decide +kernel

/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: Tactic `decide` proved that the proposition
  fincmNo.check somehowP (cmSomehowBad, 0) = true
is false
-/
#guard_msgs in
example : SubTab.Holds somehowP → False := fincmNo.verdict somehowP (cmSomehowBad, 0)

/-- info: "fincm: certificate REJECTED by its certifier (a tool defect)" -/
#guard_msgs in
#eval match fincmDisprover.gate somehowP (some (cmSomehowBad, 0)) with
  | .inr msg => msg
  | .inl _ => "accepted"

/-! ## `ljfo` -/

def treeUnit : LJFO.DerivTree :=
  (.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [])])])])])])

def treeGap : LJFO.DerivTree :=
  (.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 2 [(.node 0 [(.node 0 [(.node 0 [
    (.node 0 [(.node 0 [(.node 1 [(.node 0 [(.node 0 [(.node 0 [(.node 1 [(.node 0 [(.node 0 [
    (.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 4 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [
    (.node 0 [(.node 1 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [])])])])])])])])])]),
    (.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [])])])])])])])])])])])]),
    (.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [])])])])])])])])])])])])])])]),
    (.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [])])])])])])])])])])])])

theorem unit_p : SubTab.Holds unitP := ljfoYes.verdict unitP treeUnit

theorem gap : SubTab.Holds gapCell := ljfoYes.verdict gapCell treeGap

open CertifyAdoption.CheckDeriv in
example : ljfoYes.check gapCell (badIndex treeGap) = false := by decide +kernel

open CertifyAdoption.CheckDeriv in
example : ljfoYes.check gapCell (swapKids treeGap) = false := by decide +kernel

open CertifyAdoption.CheckDeriv in
example : ljfoYes.check unitP (badArity treeUnit) = false := by decide +kernel

/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: Tactic `decide` proved that the proposition
  ljfoYes.check gapCell (CertifyAdoption.CheckDeriv.swapKids treeGap) = true
is false
-/
#guard_msgs in
example : SubTab.Holds gapCell :=
  ljfoYes.verdict gapCell (CertifyAdoption.CheckDeriv.swapKids treeGap)

/-- info: "ljfo: certificate REJECTED by its certifier (a tool defect)" -/
#guard_msgs in
#eval match ljfoProver.gate gapCell (some (CertifyAdoption.CheckDeriv.badIndex treeGap)) with
  | .inr msg => msg
  | .inl _ => "accepted"

end PLLDecider.Gates

/-! ## Axiom pins -/

#axioms_within PLLDecider.Gates.not_peirce [propext, Quot.sound]
#axioms_within PLLDecider.Gates.not_somehowP [propext, Quot.sound]
#axioms_within PLLDecider.Gates.unit_p [propext, Quot.sound]
#axioms_within PLLDecider.Gates.gap [propext, Quot.sound]
