import Verso
import VersoManual
import CLPPaper.Src
import CLPPaper.Cite
import SemPaper.Math
import SemPaper.Blocks

open Verso.Genre
open Verso.Genre.Manual
open CLPPaper CLPPaper.Cite PaperKit.Math PaperKit.Blocks
open PLLND PLLND.SemUI

set_option paperkit.notation "sem"

#doc (Manual) "Constraint models" =>

A constraint model {pcite}`FairtloughMendler1997` has two preorders
$`R_m \subseteq R_i` on its worlds, a set $`F` of fallible worlds, upward
closed along $`R_i`, and a valuation hereditary along $`R_i` that makes every
atom true at a fallible world (the fields and conditions are tabled below).
Forcing is intuitionistic along $`R_i` for $`\land`, $`\lor`,
$`\twoheadrightarrow`; $`\bot` holds exactly at the fallible worlds; and
$`w \Vdash \bigcirc A` when every $`R_i`-successor of $`w` has an
$`R_m`-successor forcing $`A`.  $`\Gamma \models \varphi` is consequence over all
constraint models.

PLL is sound and complete for constraint models: soundness by induction on
derivations, completeness by a canonical model, which uses
`Classical.choice`.  PROVED.

{stmt}`consequence_iff_derivable`

{leanStmt consequence_iff_derivable}

It has the finite model property: a formula not provable fails at a world of
a finite constraint model (by filtration).  PROVED.

{stmt}`finite_model_property`

{leanStmt finite_model_property}

# Supporting declarations

{lemmaTable ConstraintModel ConstraintModel.force ConstraintModel.force_hered Consequence soundness completeness not_provable_iff_exists_finite_countermodel}

Pins (`collectAxioms`): {axiomsOf}`soundness` for `soundness`;
{axiomsOf}`completeness consequence_iff_derivable finite_model_property not_provable_iff_exists_finite_countermodel`
for `completeness`, `consequence_iff_derivable`, `finite_model_property` and
`not_provable_iff_exists_finite_countermodel`.
