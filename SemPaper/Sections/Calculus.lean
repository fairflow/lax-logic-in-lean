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

#doc (Manual) "PLL and natural deduction" =>

Formulas are built from atoms and $`\bot` by $`\land`, $`\lor`,
$`\twoheadrightarrow` and $`\bigcirc`; $`\lnot A` is $`A \twoheadrightarrow \bot`
and $`\top` is $`\bot \twoheadrightarrow \bot`.  The reference calculus is the
natural deduction system `LaxND`: the rules of intuitionistic natural
deduction, $`\bigcirc`-introduction from $`A` to $`\bigcirc A`, and
$`\bigcirc`-elimination, which from $`\bigcirc A` and a derivation of
$`\bigcirc B` from $`A` gives $`\bigcirc B` (the twelve rules are tabled
below).  A derivation is data; $`\Gamma \vdash \varphi` as a proposition says
that one exists.

The three axioms of Fairtlough and Mendler are derivable, so $`\bigcirc` is a
nucleus on provability: inflationary, idempotent, and preserving
conjunction.  Each is a derivation, built without axioms.

{stmt}`OI`

{leanStmt OI}

{stmt}`OM`

{leanStmt OM}

{stmt}`OSR`

{leanStmt OSR}

# Supporting declarations

{lemmaTable LaxND Deriv Interd}

Pins (`collectAxioms`): none for `LaxND`, `Deriv`, `Interd`, `OI`, `OM`,
`OSR`.
