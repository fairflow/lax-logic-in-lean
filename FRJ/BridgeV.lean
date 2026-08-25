/-
# The bridge for the repaired calculus

`FRJ/Bridge.lean`'s consequence wrappers, over `soundnessV`: a derivation
in the REPAIRED calculus refutes the original `LaxND` judgment.  Thin —
every proof is the paper wrapper with `soundness` replaced by
`soundnessV`.
-/
import FRJ.Bridge
import FRJ.SoundV

namespace FRJ

open PLLND

/-- A repaired-calculus derivation of `ofPLL φ` refutes `⊢ φ`. -/
theorem not_derivable_of_provableV {φ : PLLFormula} (h : ProvableV (ofPLL φ)) :
    ¬ Nonempty (LaxND [] φ) :=
  fun ⟨p⟩ => soundnessV h (valid_of_derivable p)

/-- The entailment form: a derivation of the implication refutes the
one-hypothesis judgment. -/
theorem not_entails_of_provableV {φ ψ : PLLFormula}
    (h : ProvableV (ofPLL (.ifThen φ ψ))) : ¬ Nonempty (LaxND [φ] ψ) :=
  fun ⟨p⟩ => not_derivable_of_provableV h ⟨.impIntro p⟩

end FRJ
