import Verso
import VersoManual
import CLPPaper.Src
import CLPPaper.Cite
import SemPaper.Math
import SemPaper.Blocks

open Verso.Genre
open Verso.Genre.Manual
open CLPPaper CLPPaper.Cite PaperKit.Math PaperKit.Blocks
open PLLND PLLND.SemUI PLLND.LaxInfinite

set_option paperkit.notation "sem"

#doc (Manual) "Introduction" =>

Propositional lax logic (PLL) {pcite}`FairtloughMendler1997` extends
intuitionistic propositional logic by one modality $`\bigcirc`.  This paper
records what is machine-checked about two questions: in which models PLL is
complete, and how its provability is decided with certificates the Lean
kernel checks.  It ends with the algebra of the variable-free formulas,
whose order is the subject of the companion paper _The Order of F0: Covers,
Independence and the Rationals_.

# At a glance

:::f0table (widths := "0.5 0.1 0.31 0.05")
* * Result
  * Status
  * Axioms
  * §
* * PLL is sound and complete for constraint models
  * PROVED
  * {axiomsOf}`consequence_iff_derivable`
  * 3
* * Finite model property for constraint models
  * PROVED
  * {axiomsOf}`finite_model_property`
  * 3
* * Subframe and constraint models translate with the same forcing
  * PROVED
  * {axiomsOf}`SubframeModel.toConstraint_force ConstraintModel.toSubframe_force`
  * 4
* * PLL is sound and complete for subframe models
  * PROVED
  * {axiomsOf}`SubframeModel.derivable_iff_valid`
  * 4
* * … and for finite decidable subframe models, without choice
  * PROVED
  * {axiomsOf}`SubframeModel.CF.derivable_iff_valid`
  * 4
* * Every formula has a closed tableau or a finite subframe countermodel
  * PROVED
  * {axiomsOf}`SubTab.dichotomy`
  * 5
* * A closed tableau is a natural-deduction derivation
  * PROVED
  * {axiomsOf}`SubTab.termOf SubTab.deriveOf`
  * 5
* * A countermodel certificate refutes its formula
  * PROVED
  * {axiomsOf}`SubTab.SubCM.refutes_sound`
  * 5
* * Completeness for finite subframe models, from the tableau
  * PROVED
  * {axiomsOf}`SubTab.completeness_fin`
  * 5
* * G4c is equivalent to natural deduction
  * PROVED
  * {axiomsOf}`G4c.equiv_nd`
  * 6
* * PLL is decidable, through FRJW and $`\mathrm{Gbu}\bigcirc`
  * PROVED
  * {axiomsOf}`FRJ.Gbu.W.decideLaxND`
  * 6
* * $`F_0` is a Heyting algebra with a nucleus
  * PROVED
  * {axiomsOf}`F0Nuclear.instHeyting F0Nuclear.circNucleus`
  * 7
* * Esakia duality for Heyting algebras with a nucleus
  * OPEN
  * –
  * 8
:::

The axioms are computed by `collectAxioms` when the document is built.

# How to read the results

Each result is stated in words where the formula does not say it, displayed
as a formula generated from its Lean statement, and given beneath in small
type as the Lean statement with a link to its source line (in the HTML, a
panel that opens on click).  Supporting declarations are tabled at the end of
each section, with the axiom pins.  PROVED means kernel-checked and
sorry-free; anything not proved is OPEN or marked as a pen argument.  In
displays the meta-level connectives are written _and_, _or_; $`\vdash \varphi`
is provability without hypotheses; $`\Gamma \Rightarrow \Delta` is a signed
sequent of the tableau, $`\Rightarrow_{S}` at an $`S`-point;
$`\mathsf{FinDec}(M)` says that $`M` is finite, with decidable order, $`S` and
valuation.  The declarations are in the library (`LaxLogic/PLL`, `FRJ`)
except F0's Heyting algebra and nucleus (`wip/f0Nuclear.lean`); the figure is
drawn by `scripts/sem-figures.py` from data Lean computes.
