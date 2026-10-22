import LaxLogic.PLL.SubTab.Complete
import tools.SubTab.Tableau

/-!
# The subframe tableau as a lean-certify engine

2026-10-15.  The untrusted producer (`SubTab.solve`,
`tools/SubTab/Tableau.lean`) with the two certifiers proved sound
(`LaxLogic/PLL/SubTab/Sound.lean`).  `complete`
(`LaxLogic/PLL/SubTab/Complete.lean`) proves that the search of the proof
terminates, by strong induction on the measure `meas`; the compiled producer
`SubTab.solve` is `partial`, and its termination is a paper argument.  The
budget is unused: `produce` returns `pass` or `fail`, never `flag`.

This module lives in `tools/`, not beside the certifiers, because the
producer's module imports `tools.Decide`, whose import closure reaches `wip/`.
-/

namespace PLLND
namespace SubTab

/-- The producer: a closed tableau or a finite subframe countermodel. -/
def produce (φ : PLLFormula) (_budget : Nat) : Certify.Verdict TCert SubCM :=
  match _root_.SubTab.solve φ with
  | .ok c => .pass c
  | .error m => .fail m

/-- **The subframe tableau engine.** -/
def engine : Certify.Engine PLLFormula TCert SubCM Holds where
  yes := yes
  no := no
  produce := produce

end SubTab
end PLLND

#certify_structural PLLND.SubTab.engine
#certify_statement PLLND.SubTab.engine
