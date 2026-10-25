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
open F0Nuclear

set_option paperkit.notation "sem"

#doc (Manual) "The algebra" =>

A nucleus on a Heyting algebra $`H` is a map $`j : H \to H` with
$`a \le j(a)`, $`j(j(a)) \le j(a)` and $`j(a \land b) = j(a) \land j(b)`
{pcite}`Macnab1981`; a Heyting algebra with a nucleus is the algebraic
counterpart of PLL, with $`\bigcirc` as the nucleus.  The library builds this
structure on the variable-free formulas.  Write $`a \models b` when every
world of every constraint model that forces $`a` forces $`b`; by the
completeness of Section 3 this is derivability from the one hypothesis $`a`.
PROVED.

{stmt}`le_iff_nonempty`

{leanStmt le_iff_nonempty}

$`F_0` is the quotient of the variable-free formulas by $`\equiv`, the
equivalence of $`\models` both ways, ordered by $`\models`: the Lindenbaum
algebra of the variable-free fragment, an infinite bounded distributive
lattice.  Implication lifts from $`\twoheadrightarrow` and makes $`F_0` a Heyting
algebra (`instHeyting`).  PROVED.

{stmt}`le_himp_iff_rn`

{leanStmt le_himp_iff_rn}

$`\bigcirc` lifts to a nucleus on $`F_0` (`circNucleus`): it is inflationary,
idempotent and preserves meets.  PROVED.

{stmt}`le_box`

{leanStmt le_box}

{stmt}`box_box_le`

{leanStmt box_box_le}

{stmt}`box_inf`

{leanStmt box_inf}

The proofs are pointwise facts of the forcing clauses against $`\models`, with
no choice.  _Pen remark._  By the standard Lindenbaum argument $`F_0` is the
free Heyting algebra with a nucleus on no generators; this universal property
is not stated in Lean, nor is the Lindenbaum algebra on variables built.  The
order of $`F_0` (its covers, the independence of its
gaps, an embedding of the rationals and its completion) is the subject of the
companion paper _The Order of F0: Covers, Independence and the Rationals_.

# Supporting declarations

{lemmaTable LaxInfinite.Le LaxInfinite.LaxEquiv closed_lax_infinite F0Nuclear.himp instHeyting F0Nuclear.box circNucleus}

Pins (`collectAxioms`):
{axiomsOf}`le_iff_nonempty closed_lax_infinite` for `le_iff_nonempty` and
`closed_lax_infinite`, through completeness;
{axiomsOf}`instHeyting le_himp_iff_rn circNucleus le_box box_box_le box_inf`
for the Heyting algebra and the nucleus.
