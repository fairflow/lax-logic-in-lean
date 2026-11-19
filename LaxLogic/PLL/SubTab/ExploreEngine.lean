import LaxLogic.PLL.SubTab.Explore
import LaxLogic.PLL.SubTab.Tableau

/-!
# The subframe tableau engine, by scripts

2026-11-19.  The untrusted search of `Tableau.lean` (`SubTab.solve`) with
the yes side taken by scripts: its closed tableau is turned into a
derivation of the proof explorer (`ofCert`, `Explore.lean`) and that into a
script, which the certifier `yesScript` checks by running it.  The no side
is `no`, unchanged.  `complete_script` (`Explore.lean`) is the completeness
of this pair of certifiers; that the compiled search terminates is a paper
argument, as for `engine` (`Engine.lean`).

The search's closed tableau is checked before it is turned into a script;
if it did not check, the answer would be `flag` (a tool defect, never a
verdict).
-/

open ProofTools

namespace PLLND
namespace SubTab

/-- The producer of the engine by scripts: the search of `Tableau.lean`,
its closed tableau turned into a script. -/
def produceScript (φ : PLLFormula) (_budget : Nat) :
    Certify.Verdict (Explore.Script STab) SubCM :=
  match _root_.SubTab.solve φ with
  | .ok c =>
    if h : check ⟨false, [], [φ]⟩ c = true then .pass (scriptOf φ c h) else .flag
  | .error m => .fail m

/-- **The subframe tableau engine, by scripts.** -/
def engineScript : Certify.Engine PLLFormula (Explore.Script STab) SubCM Holds where
  yes := yesScript
  no := no
  produce := produceScript

end SubTab
end PLLND

#certify_structural PLLND.SubTab.engineScript
#certify_statement PLLND.SubTab.engineScript
