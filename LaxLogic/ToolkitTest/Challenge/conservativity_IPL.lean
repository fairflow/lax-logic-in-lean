/- Challenge: `conservativity_IPL`.  Group: nd-core.
   Replace the `sorry`.  Do not look for the original proof.

   Deliberately not stated here: where this comes from, how long the known
   proof is, or how hard it is.  Those were hints. -/
import LaxLogic.ToolkitTest.Punched.PLLNDCore

namespace PLLND

open PLLFormula

/-- **Conservativity, classic form.**  If context and conclusion are already
IPL, a PLL derivation yields an IPL derivation of the same sequent. -/
theorem conservativity_IPL {Γ : List PLLFormula} {φ : PLLFormula}
    (hφ : isIPL φ) (hΓ : ∀ ψ ∈ Γ, isIPL ψ) (p : LaxND Γ φ) : IPLND Γ φ := by
  sorry

end PLLND
