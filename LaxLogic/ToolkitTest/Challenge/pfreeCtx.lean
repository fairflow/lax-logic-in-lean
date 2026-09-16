/- Challenge: `pfreeCtx`.  Group: completeness.
   Replace the `sorry`.  Do not look for the original proof.

   Deliberately not stated here: where this comes from, how long the known
   proof is, or how hard it is.  Those were hints. -/
import LaxLogic.ToolkitTest.Punched.LJFComplete

namespace LJFIPC

open PLLND (LaxND SCh SC)

theorem pfreeCtx {p : String} {Δ : List PLLFormula}
    (h : ∀ ψ ∈ Δ, PFree p ψ) : LJF.PFreeCtx p (Δ.map negOf) := by
  sorry

end LJFIPC
