/- Challenge: `map_unNeg_negOf`.  Group: completeness.
   Replace the `sorry`.  Do not look for the original proof.

   Deliberately not stated here: where this comes from, how long the known
   proof is, or how hard it is.  Those were hints. -/
import LaxLogic.ToolkitTest.Punched.LJFComplete

namespace LJFIPC

open PLLND (LaxND SCh SC)

theorem map_unNeg_negOf {Γ : List PLLFormula} (h : ∀ ψ ∈ Γ, PLLND.isIPL ψ) :
    (Γ.map negOf).map unNeg = Γ := by
  sorry

end LJFIPC
