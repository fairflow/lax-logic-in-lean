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

#doc (Manual) "Below the sixth rung" =>

The downsets $`{\downarrow}t_n` are finite for $`n \le 5` (Section 3).  For
$`n = 6, 7` and every $`n \ge 9` they are infinite: the conjecture that every
$`{\downarrow}t_n` is finite is REFUTED there, and OPEN at $`n = 8`.  No
`Classical.choice`; `wip/f0T6.lean`.

The sixth rung is double-negation elimination for $`\bigcirc\bot`, where the fifth,
$`t_3 \lor t_4`, is up to $`\dashv\vdash` weak excluded middle
$`\lnot\bigcirc\bot \lor \lnot\lnot\bigcirc\bot`, with a downset of six elements.
PROVED (a closed tableau checked by the kernel).

{stmt}`T6.t6_regular`

{leanStmt T6.t6_regular}

_The mechanism._  In the $`\bigcirc`-free instance the quotient by
$`\lnot\lnot p = p` has five elements (textbook, not mechanised), so an infinite
family below $`t_6` must use $`\bigcirc` beyond $`p := \bigcirc\bot`.  It does:
$`u = \bigcirc\lnot\bigcirc\bot` lies above $`t_3` (`t3_le_u`), and reading $`p`
as $`u` and $`\bot` as $`t_3` (`rel`) turns the Rieger–Nishimura rungs into a ladder
in $`[t_3, \top]`; Section 10 shows that it is the image of the rungs under
$`\sigma`.  The chain $`x_k = \mathrm{rel}(r_{2k+1}) \land t_6` is strictly
increasing below $`t_6`.  PROVED, on a countermodel: the Rieger–Nishimura ladder
under three top worlds, where $`u` holds on the ladder exactly at world $`0`, as
$`p` does (`rel_transfer`).

{stmt}`T6.t6_downset_infinite`

{leanStmt T6.t6_downset_infinite}

Since $`t_6 \vdash t_n` for $`n = 6, 7` and $`n \ge 9`, the chain lies below each.
At $`n = 8`, $`t_6 \nvdash t_8`, and the file records that $`t_8` fails on the
countermodel's ladder, where the chain holds.

{stmt}`T6.rung_downset_infinite`

{leanStmt T6.rung_downset_infinite}

# Supporting declarations

{lemmaTable T6.t6F T6.uF T6.t3_le_u T6.rel T6.xc T6.t6_chain T6.t6_le_rung}

Pins: every declaration here, the designed cells `cell_m6`, `cell_m9` and
`rel_transfer` within `propext`, `Quot.sound` (`#axioms_within`, confirmed by
`#print axioms`); the odd rungs' truth sets come from Section 4, choice-free.
