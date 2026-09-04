import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "FRJW: the campaign" =>

:::group "frjw"
FRJW is FRJV with one rule added and one deleted.  The campaign runs in six
stages, W1 to W6; W1 to W3 are machine-checked, W4 onward are open.
:::

# The rule and its motivation

:::definition "lift_rule" (parent := "frjw")
*Lift.*  A regular disproof becomes an irregular one over any retained
$`Ĝ`-context inside the closure of its own context:
$$`\frac{Γ ⇒ C \qquad Θ ⊆ Ĝ,\ Θ ⊆ \mathrm{Cl}(Γ)}{∅ ; Θ → C}`
Soundness is monotonicity of forcing: the component's root sits above $`w`
and refutes $`C`, so $`w` refutes $`C`.
The rule $`⊃∉` (`impNotIn`) is deleted, being Lift composed with $`⊃∈`;
$`◯∉` is kept, since its premise is a regular disproof of $`Z` rather than
of $`◯Z`, so it climbs the modality and Lift does not.
:::

:::theorem "duality_hole" (parent := "frjw") (tags := "proved, motivation")
FRJV has *no* irregular disproof of $`◯(◯Z ⊃ Z)`, for any $`G`, $`Z`,
$`Σ`, $`Θ`.  Only $`◯∉` and $`Ax^{I◯}` conclude a $`◯` goal; the former needs
a cleanly tagged regular disproof of $`◯Z ⊃ Z`, and the latter needs
`classForce` to reject a body of the form $`¬x ∨ x`.
:::

:::proof "duality_hole"
Machine-checked as `FRJ.V.WCounter.no_irregular_circ_imp_self`
(`wip/gbu_weakening.lean`), resting on
`FRJ.V.WCounter.not_clean_imp_self` for the $`◯∉` branch.
:::

:::theorem "gbu_gap" (parent := "frjw") (tags := "proved, motivation")
Gbu$`◯` cannot fill the hole: $`∅ →_g ◯(◯p ⊃ p)` is not derivable.
:::

:::proof "gbu_gap"
`FRJ.Gbu.not_gbuIC_Gcc` (`wip/gbu_search_circ.lean`).  `soundIC` gives the
irregular judgment the same reading as the regular one, and $`◯(◯p ⊃ p)` is
refuted by the model `GccWitness` extracts.
:::

:::theorem "provable_gcc" (parent := "frjw") (tags := "proved, motivation")
A *regular* FRJV disproof of $`◯(◯p ⊃ p)` does exist, by the barren
$`⋈^◯` join, but it cannot be used where an irregular disproof is required.
Together with {uses "duality_hole"}[] and {uses "gbu_gap"}[] this is the
mismatch {uses "lift_rule"}[] is designed to remove.
:::

:::proof "provable_gcc"
`FRJ.Gbu.provableV_Gcc` (`wip/gbu_search_circ.lean`), with the extracted
countermodel dumped as `countermodel_Gcc`.  The Lift clause of `lemma39I`
is separately checked as `FRJ.V.RBar.not_force_of_rootAbove`
(`wip/rbar.lean`), and was negative-tested: the same one-line proof does
not typecheck for a tagless $`◯∉`, so the gate discriminates.
:::

# Stages

:::theorem "w1_calculus" (parent := "frjw") (tags := "proved, stage-W1")
*W1, transcribe.*  The two FRJW families and the disprovability judgment
are defined: `FRJ.FRJWr`, `FRJ.FRJWi`, `FRJ.DisprovableW`, obtained from
FRJV by adding {uses "lift_rule"}[] and deleting $`⊃∉`.  The stage gate is
`#slime` reporting zero computed indices in the return type of every
constructor of both families.
:::

:::proof "w1_calculus"
`FRJ/CalculusW.lean`, 366 lines, sorry-free.
:::

:::theorem "w2_conservativity" (parent := "frjw") (tags := "proved, stage-W2")
*W2, conservativity.*  Every FRJV disproof is an FRJW disproof:
$$`\mathrm{FRJVr}\ G\ t\ Γ\ C → \mathrm{FRJWr}\ G\ t\ Γ\ C, \qquad
\mathrm{FRJVi}\ G\ Σ\ Θ\ C → \mathrm{FRJWi}\ G\ Σ\ Θ\ C`
The only non-trivial case is $`⊃∉`, reconstructed as
`lift (impIn d hA _) hTh`.  This is what licenses reusing the FRJV corpus,
so it is proved before soundness.
:::

:::proof "w2_conservativity"
`FRJ.disprovableW_of_provableV`, via `toWr` and `toWi`
(`FRJ/CalculusW.lean`).  Axioms pinned at `[propext, Quot.sound]` by a
`#guard_msgs`-checked `#print axioms`.
:::

:::theorem "w3_soundness" (parent := "frjw") (tags := "proved, stage-W3")
*W3, soundness.*  A disproof yields a refutation:
$$`\mathrm{DisprovableW}\ G → ¬\,\mathrm{PLL}\ G`
The Lift case of `lemma39I` was already available; the real obligation was
the joins', each of which must still discharge its `RootAbove` premise for
components now supplied by {uses "lift_rule"}[].
:::

:::proof "w3_soundness"
`FRJ.soundnessW` (`FRJ/SoundW.lean`, 1879 lines, sorry-free), through
`FRJ.W.lemma39R`, `FRJ.W.lemma39I` and `FRJ.W.modR_countermodel`, with
`RegIdx (lift d) := Unit` and `preI (lift d) _ := preR d`
(`FRJ/ExtractW.lean`).  The conclusion is against the wider fallible class,
because the fallible join builds a model with a fallible world.
:::

:::theorem "w4_duality_closes" (parent := "frjw") (tags := "open, stage-W4") (effort := "small") (priority := "high")
*W4, the duality gap closes.*  $`∅ ; ∅ → ◯(◯p ⊃ p)` is an FRJW disproof,
expected to be `lift GccWitness.2 (by simp)`.  This is the test the whole
exercise was for: it says the mismatch between {uses "duality_hole"}[] and
{uses "provable_gcc"}[] is gone.
:::

:::proof "w4_duality_closes"
Not yet written.  Depends on {uses "w3_soundness"}[] only for confidence,
not logically; the statement is a construction in the calculus of
{uses "w1_calculus"}[].
:::

:::theorem "w5_invertibility" (parent := "frjw") (tags := "open, stage-W5") (effort := "medium")
*W5, the two invertibility clauses.*
$$`(∨\text{-inv})\quad D ▷ (Ω ⇒_g C₁) ∧ D ▷ (Ω ⇒_g C₂) ⟹ D ▷ (Ω ⇒_g C₁ ∨ C₂)`
$$`(★)\quad D ▷ (Ω ⇒_g Z) ⟹ D ▷ (Ω ⇒_g ◯Z) \qquad (Ω ⊆ Ĝ_{at} ∪ Ĝ_{imp},\ Υ\text{ dead})`
Expected to be immediate: $`(∨\text{-inv})` by $`⋈^∨` on two `lift`
premises, $`(★)` by `lift` then `gbuSuccCirc`.  That these fall out is the
coherence check on the design, since neither was part of the motivation for
{uses "lift_rule"}[].
:::

:::proof "w5_invertibility"
Not yet written.  Follows {uses "w4_duality_closes"}[].
:::

:::theorem "w6_completeness" (parent := "frjw") (tags := "open, stage-W6, route-changed") (effort := "large")
*W6, completeness.*  Originally: rebuild the Gbu$`◯` search over FRJW, on
the invariant $`¬ D ▷ (Ω ⇒_g C)` that {uses "w5_invertibility"}[] makes
propagable.  Superseded 2026-08-31: completeness of Gbu$`◯(G)` is not to be
pursued directly but reached via LJF$`◯` focalisation, which is already
proved.  The database route is stood down, not deleted.
:::

:::proof "w6_completeness"
Open.  Two risks are to be screened extensionally before any proof is
scoped, per `METHOD.md`: termination of search rather than soundness, since
Lift makes `EvalI` at least as strong as `EvalR` over $`Ĝ`-contexts and so
sends far more traffic down the join branches; and the `RootAbove`
obligation at the joins over a `lift` premise.
:::
