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

#doc (Manual) "Covers and copies together" =>

This section relates the two kinds of structure found so far: the covers at
the bottom of $`F_0` (Section 3) and the order-embedded copies of the dyadic
rationals (Section 5).  Apart from its bottom $`f(0) = \bot`, the copy sits
above the first sixteen rungs; between
any two comparable lattice polynomials in the odd gaps hang countably many
mutually incomparable copies; an element outside the downset of a table has an
upper cover; and the copy descends to a second cut that $`F_0` does not fill.
The results are in `wip/f0Structure.lean` and `wip/f0Hole.lean`.

# The ladder under the copy

Every rung up to $`t_{15}` lies below $`f(d)` for every dyadic $`d > 0`.
PROVED.  The variables of the polynomial $`F_n(m)` are indices $`2^{n} + m \ge 3`,
so $`f(d)` is a lattice polynomial in gaps $`g_k` with $`k \ge 7`; it is true at
the assignment that makes every variable true when $`d > 0`; and
$`t_{15} \vdash t_{2k+1} \vdash g_k` for $`k \ge 7`.

{stmt}`ladder_le_formula`

{docstring ladder_le_formula +allowMissing}

{srcLink}`ladder_le_formula`

The bound $`15` is sharp: $`f(1/2) \vdash g_7`, and $`t_{16} \nvdash g_7`.
PROVED.

{stmt}`t16_not_le_half`

{docstring t16_not_le_half +allowMissing}

{srcLink}`t16_not_le_half`

With the cover $`t_1 \lessdot t_4` of Section 3, that is
$`\bigcirc\bot \lessdot \lnot\lnot\bigcirc\bot` up to $`\dashv\vdash`, the dyadic
copy sits above a cover whose two ends are both formulas without $`\lor`.

# Derivability between lattice polynomials

Derivability between the interpretations of two lattice polynomials in the odd
gaps is Boolean entailment: $`[\![ q ]\!] \vdash [\![ p ]\!]` exactly when every
assignment that makes $`q` true makes $`p` true.  This is the lattice-theoretic
form of independence (Section 4): the odd gaps generate a free distributive
lattice.  The order is decided by a check on the disjunctive normal form of
$`q`: every monomial of it must make $`p` true.  PROVED.

{stmt}`lpoly_deriv_iff`

{docstring lpoly_deriv_iff +allowMissing}

{srcLink}`lpoly_deriv_iff`

{stmt}`leCheck`

{docstring leCheck +allowMissing}

{srcLink}`leCheck`

{stmt}`lpoly_deriv_decide`

{docstring lpoly_deriv_decide +allowMissing}

{srcLink}`lpoly_deriv_decide`

# Incomparable copies

Let $`p` and $`q` be lattice polynomials with $`[\![ p ]\!] \vdash [\![ q ]\!]` and
$`[\![ q ]\!] \nvdash [\![ p ]\!]`.  For each $`k \in \mathbb{N}`, the copy

$$`e_k(d) = p \lor (q \land c_k(d))`

uses $`c_k(d)`, the polynomial of $`d` with its variables renamed into a block of
fresh variables of its own, disjoint from those of $`p`, of $`q` and of every
other copy.

{stmt}`copyP`

{docstring copyP +allowMissing}

{srcLink}`copyP`

{stmt}`copyF`

{docstring copyF +allowMissing}

{srcLink}`copyF`

Each $`e_k` is an order embedding of the dyadic rationals in $`[0, 1]` into the
interval $`[[\![ p ]\!], [\![ q ]\!]]`, with $`e_k(0) \dashv\vdash [\![ p ]\!]` and
$`e_k(1) \dashv\vdash [\![ q ]\!]`, and for $`k \ne k'` the images of the open
interval $`(0, 1)` are pairwise incomparable.  PROVED.

{stmt}`incomparable_copies`

{docstring incomparable_copies +allowMissing}

{srcLink}`incomparable_copies`

{stmt}`copy_zero`

{docstring copy_zero +allowMissing}

{srcLink}`copy_zero`

{stmt}`copy_one`

{docstring copy_one +allowMissing}

{srcLink}`copy_one`

Since $`F_0` is countable, $`\aleph_0` is the largest possible number of such
copies; that remark is not a theorem of the library.  Whether every interval
$`[u, v]` of $`F_0` with $`u < v` and not a cover contains a copy is OPEN
(Section 9).

# The cover lemma

If $`c` has a finite downset table whose order is decided, and $`c \nvdash a`,
then $`a` has an upper cover $`b` with $`b \vdash a \lor c`.  By distributivity
$`y \mapsto y \land c` maps the interval $`[a, a \lor c]` into
$`{\downarrow}c`, which the table makes finite; a minimal member $`m` of the
table strictly above $`a \land c` gives $`b = a \lor m`.  PROVED; without the
hypothesis that the order on the table is decided, the same holds by excluded
middle.

{stmt}`cover_above`

{docstring cover_above +allowMissing}

{srcLink}`cover_above`

{stmt}`cover_above_em`

{docstring cover_above_em +allowMissing}

{srcLink}`cover_above_em`

# A second cut

The images $`h_n = f(1/2^n)` of the dyadics $`1/2^n` form a descending chain,
each a meet of fresh odd gaps: $`h_0 = \top` and
$`h_{n+1} \dashv\vdash h_n \land g_{2 x_{n+1,1} + 1}`, where $`x_{n,m} = 2^n + m`
is the variable of the dyadic $`m/2^n`.  PROVED.

{stmt}`half_step`

{docstring half_step +allowMissing}

{srcLink}`half_step`

The chain is bounded below by $`t_{15}` and by every $`W_b` of Section 6, and it
has no greatest lower bound, among all formulas or among the variable-free
ones.  PROVED.  So the copy of the dyadics descends towards $`0` through a cut
that $`F_0` does not fill.  The proof adapts that of Section 6: a lower bound of
the chain entails cofinally many gaps, which already bounds its truth set on
the lifted ladder.

{stmt}`halves_no_glb`

{docstring halves_no_glb +allowMissing}

{srcLink}`halves_no_glb`

{stmt}`halves_no_glb_vf`

{docstring halves_no_glb_vf +allowMissing}

{srcLink}`halves_no_glb_vf`

# Axioms

As recorded in the files (`#axioms_within`), and confirmed by `#print axioms`
on the build:

* within `propext`, `Quot.sound`: `ladder_le_formula`, `lpoly_deriv_iff`,
  `lpoly_deriv_decide`, `incomparable_copies`, `copy_zero`, `copy_one`,
  `cover_above`, `half_step` (`#print axioms` reports `propext` alone for
  `copy_one` and `cover_above`);
* `propext`, `Classical.choice`, `Quot.sound`: `cover_above_em` (excluded
  middle on the table), `t16_not_le_half` (through the single-edge lifts),
  `halves_no_glb` and `halves_no_glb_vf` (the dichotomy of plain-ladder truth
  sets, all or bounded, is proved by excluded middle, and the bounds $`W_b` are
  pinned with choice in Section 6).
