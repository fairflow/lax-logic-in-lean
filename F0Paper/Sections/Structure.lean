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

#doc (Manual) "Covers and threads together" =>

How the covers of Section 3 and the dyadic thread $`f` of Section 5 sit
together.  Files: `wip/f0Structure.lean`, `wip/f0Hole.lean`.

_The ladder under the thread._  Every rung up to $`t_{15}` lies below $`f(d)` for
every dyadic $`d > 0`; the bound is sharp, as $`t_{16} \nvdash f(1/2)`
(`t16_not_le_half`).  So, with the cover $`t_1 \lessdot t_4`, the thread sits
above a cover whose ends are formulas without $`\lor`.  PROVED.

{stmt}`ladder_le_formula`

{leanStmt ladder_le_formula}

_Boolean entailment._  Derivability between lattice polynomials in the odd gaps
is Boolean entailment, decided on the disjunctive normal form (`leCheck`): the
odd gaps generate a free distributive lattice.  PROVED.

{stmt}`lpoly_deriv_iff`

{leanStmt lpoly_deriv_iff}

_Pairwise incomparable threads._  For lattice polynomials $`p`, $`q` with
$`[\![ p ]\!] < [\![ q ]\!]`, the dyadic threads
$`e_k(d) = p \lor (q \land c_k(d))`, with $`c_k(d)` the polynomial of $`d` in a
fresh block of variables, satisfy $`e_k(0) \dashv\vdash [\![ p ]\!]`,
$`e_k(1) \dashv\vdash [\![ q ]\!]`, and $`e_k[(0, 1)] \parallel e_{k'}[(0, 1)]` for
$`k \ne k'`.  So the open interval of every pair in the odd-gap lattice contains
$`\aleph_0` threads, pairwise $`\parallel`.  PROVED.  Which other pairs have a
thread is OPEN (Section 11).

{stmt}`incomparable_copies`

{leanStmt incomparable_copies}

_The cover lemma._  If $`c` has a finite downset table whose order is decided
and $`c \nvdash a`, then $`a` has an upper cover $`b \vdash a \lor c`, as
$`y \mapsto y \land c` maps $`[a, a \lor c]` into the finite $`{\downarrow}c`.
PROVED (by excluded middle without the decision hypothesis, `cover_above_em`).

{stmt}`cover_above`

{leanStmt cover_above}

_A second cut._  The halves $`f(1/2^n)` descend, each a meet of fresh odd gaps
(`half_step`), are bounded below by $`t_{15}` and every $`W_b`, and have no
greatest lower bound.  PROVED.

{stmt}`halves_no_glb`

{leanStmt halves_no_glb}

# Supporting declarations

{lemmaTable t16_not_le_half leCheck lpoly_deriv_decide copyP copyF copy_zero copy_one cover_above_em half_step halves_no_glb_vf}

Pins (`#axioms_within`, confirmed by `#print axioms`): within `propext`,
`Quot.sound` for `ladder_le_formula`, `lpoly_deriv_iff`, `lpoly_deriv_decide`,
`incomparable_copies`, `copy_zero`, `copy_one`, `cover_above`, `half_step`;
`propext`, `Classical.choice`, `Quot.sound` for `cover_above_em`,
`t16_not_le_half`, `halves_no_glb`, `halves_no_glb_vf` (excluded middle, the
single-edge lifts, and the bounds $`W_b` of Section 6).
