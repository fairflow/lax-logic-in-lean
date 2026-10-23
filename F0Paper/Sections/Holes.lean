import Verso
import VersoManual
import CLPPaper.Src
import CLPPaper.Cite
import F0Paper.Math

open Verso.Genre
open Verso.Genre.Manual
open CLPPaper CLPPaper.Cite F0Paper.Math
open PLLND PLLND.SemUI PLLND.F0 PLLND.RNEmbed
open PLLND.LaxInfinite (atomFree)

#doc (Manual) "A hole" =>

This section records an earlier result about the gaps that bears on the order
of $`F_0`: the family $`\{g_k : k \ge 1\}` has no greatest lower bound.  So
$`F_0` is not a complete lattice, and the infimum of the gaps is a cut that
$`F_0` does not fill.  The results are in `wip/floor.lean`.

# The cut

Let $`L` be the set of variable-free lower bounds of the gaps,

$$`L = \{\chi \in \mathrm{Fm}_0 : \chi \vdash g_k \text{ for every } k \ge 1\}.`

$`L` is a downset of $`F_0` and is not empty: it contains $`\bot`, and, for every
$`b`, the formula $`W_b = (g_1 \land \cdots \land g_{b+1}) \land t_{2b+6}`.

{stmt}`Wit`

{docstring Wit +allowMissing}

{srcLink}`Wit`

{stmt}`Wit_below_all_gaps`

{docstring Wit_below_all_gaps +allowMissing}

{srcLink}`Wit_below_all_gaps`

An infimum of the gaps in $`F_0` would be a greatest element of $`L`.  There is
none: no formula, variable-free or not, is a greatest lower bound of the gaps,
and $`L` has no greatest element.  PROVED.

{stmt}`gap_no_glb`

{docstring gap_no_glb +allowMissing}

{srcLink}`gap_no_glb`

{stmt}`L_no_greatest`

{docstring L_no_greatest +allowMissing}

{srcLink}`L_no_greatest`

In order-theoretic terms, the pair consisting of $`L` and the set of upper
bounds of $`L` is a cut of $`F_0` with no element of $`F_0` at it: in the
Dedekind–MacNeille completion of $`F_0` the gaps have an infimum, and it is a
new element.  A second cut of this kind, below the copy of the dyadic
rationals, is in Section 7, and Section 8 extends $`\bigcirc` to the
completion.

# Why

Every gap holds at every world of the lifted ladder, while every lower bound
of all the gaps is refuted at every sufficiently high world of it.  PROVED.

{stmt}`L_bounded`

{docstring L_bounded +allowMissing}

{srcLink}`L_bounded`

The proof compares the lifted ladder with the edged lifts $`\mathcal{E}_m` of
Section 2.  The two agree at the worlds below $`m + 3`, and for each formula
$`\varphi` there is a level past which they agree on $`\varphi` at the world
$`m + 3` as well.  Since $`g_{m+1}` fails at world $`m + 3` of $`\mathcal{E}_m`,
a lower bound of all the gaps fails there too, for every $`m`, so it cannot
hold at all the high worlds of the lifted ladder; and a truth set on the
lifted ladder is either everything or bounded.  On the other hand $`W_b` holds
at world $`b + 3` of the lifted ladder.  A greatest element of $`L` would lie
above every $`W_b`, so its truth set would be unbounded, against `L_bounded`.

# Axioms

As recorded in the file (`#print axioms` under `#guard_msgs`): `gap_no_glb`,
`L_no_greatest`, `L_bounded` and `Wit_below_all_gaps` depend on `propext`,
`Classical.choice`, `Quot.sound`.  The proofs use the edged lifts and the
ladder's truth sets, which carry `Classical.choice` in their proofs (Sections
2 and 4); whether these results need it has not been examined.
