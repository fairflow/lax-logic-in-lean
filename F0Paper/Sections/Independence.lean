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

#doc (Manual) "Independence of the odd gaps" =>

No finite conjunction of odd gaps entails a finite disjunction of others
(with $`\bigwedge \emptyset = \top`, $`\bigvee \emptyset = \bot`).  PROVED,
without `Classical.choice`; `wip/f0Indep.lean`.

{stmt}`Indep`

{leanStmt indep}

This is the condition under which elements of a distributive lattice generate a
free distributive lattice {pcite}`Gratzer2011`; Section 7 proves that form
(`lpoly_deriv_iff`).

_The models._  The multi-edge lift $`\mathcal{M}_T` is the lifted
Rieger–Nishimura ladder (worlds $`0, 1, 2, \ldots`, $`x` sees $`x` and every
$`y \le x - 2`, one fallible world $`f` above all, a modal step from $`0` to
$`f`) with, for each $`j \in T`, a modal step from the edge world $`2j + 3` to
$`0`.  The root is $`2 \max T + 3`.

_The forcing lemma._  On $`\mathcal{M}_T` every odd gap with index outside
$`T` holds everywhere, and every odd gap with index in $`T` fails at the root.
PROVED.  The edges sit at worlds $`\ge 3`, so the rungs keep their ladder truth
sets and $`\bigcirc t_{2k+1}` holds at $`x` exactly when each world $`x` sees is
$`0`, an edge world or at most $`k`; an edge world $`2j + 3` with $`j \in T`
forces $`\bigcirc t_{4j+3}` and refutes $`t_{4j+3}`.  Independence follows by
soundness at the root.

{stmt}`MultiEdgeForcing`

{leanStmt multi_edge_forcing}

# Supporting declarations

{lemmaTable cmM IsEdge levels root cmM_chainF forced_off fails_on indep_of_forcing}

Pins: every declaration here is within `propext`, `Quot.sound`
(`#axioms_within`), and `#print axioms` reports exactly these.  The single-edge
lifts, whose frame law uses `Classical.byContradiction`, are not used, and the
odd rungs' truth sets are re-proved without choice (`sat_rn_odd_cf`).  The case
$`|T| = 1` (`odd_gaps_single`, `wip/f0OddGaps.lean`) is re-derived choice-free
as `odd_gaps_single_cf`.
