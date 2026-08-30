/- Challenge: `isIPL_erase`.  Group: nd-core.
   Replace the `sorry`.  Do not look for the original proof.

   Deliberately not stated here: where this comes from, how long the known
   proof is, or how hard it is.  Those were hints. -/
import LaxLogic.ToolkitTest.Punched.PLLNDCore

namespace PLLND

open PLLFormula

@[simp]
lemma isIPL_erase (φ : PLLFormula) : isIPL (erase φ) := by
  sorry

end PLLND
