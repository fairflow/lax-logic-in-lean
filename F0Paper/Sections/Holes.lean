import Verso
import VersoManual
import CLPPaper.Src
import CLPPaper.Cite
import F0Paper.Math
import F0Paper.Blocks

open Verso.Genre
open Verso.Genre.Manual
open CLPPaper CLPPaper.Cite PaperKit.Math PaperKit.Blocks
open PLLND PLLND.SemUI PLLND.F0 PLLND.RNEmbed
open PLLND.LaxInfinite (atomFree)

#doc (Manual) "A hole" =>

The gaps $`g_k`, $`k \ge 1`, have no greatest lower bound, among all formulas
or among the variable-free ones, so their infimum is a cut that $`F_0` does not
fill, and $`F_0` is not a complete lattice.  PROVED; `wip/floor.lean`.

{stmt}`gap_no_glb`

{leanStmt gap_no_glb}

The lower bounds include $`\bot` and every
$`W_b = (g_1 \land \cdots \land g_{b+1}) \land t_{2b+6}`, which holds at world
$`b + 3` of the lifted ladder; every lower bound of all the gaps fails at every
high enough world, since it fails where $`g_{m+1}` fails on the edged lift
$`\mathcal{E}_m` and the two models agree on it at world $`m + 3` past some
level.  A greatest lower bound would lie above every $`W_b`, so its truth set
would be unbounded: impossible.  A second unfilled cut is in Section 7;
Section 8 extends $`\bigcirc` to the completion.

# Supporting declarations

{lemmaTable Wit Wit_below_all_gaps L_no_greatest L_bounded}

Pins (`#print axioms` under `#guard_msgs`): `propext`, `Classical.choice`,
`Quot.sound` for all four and `gap_no_glb`, through the edged lifts and the
ladder's truth sets; whether choice is needed has not been examined.
