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

#doc (Manual) "Independence of the odd gaps" =>

This section proves that the odd gaps $`g_1, g_3, g_5, \ldots` are independent:
no finite conjunction of some of them entails a finite disjunction of others.
The proof is one family of constraint models, the ladder with several modal
edges at once, and is choice-free.  The results are in `wip/f0Indep.lean`.

# The statement

With $`\bigwedge \emptyset = \top` and $`\bigvee \emptyset = \bot`:

{stmt}`Indep`

{docstring Indep +allowMissing}

{srcLink}`Indep`

For elements $`x_i` of a distributive lattice, the condition
$`\bigwedge_{i \in S} x_i \not\le \bigvee_{j \in T} x_j` for all finite disjoint
$`S` and $`T` is the usual criterion for the bounded sublattice they generate
to be free distributive on them; see {cite}`Gratzer2011` on free distributive
lattices.  That restatement is not mechanised.  Section 5 uses `Indep` as it
stands.

# The multi-edge lift

Recall the lifted ladder of Section 2: the ladder's worlds $`0, 1, 2, \ldots`,
where $`x` sees itself and every $`y \le x - 2`, together with one fallible
world $`f` seen by every world, and a modal step $`0 \rightsquigarrow f`, so
that $`\bigcirc\bot` holds at $`0` and nowhere else on the ladder.  The edged
lift $`\mathcal{E}_m` of Section 2 adds one modal step $`m + 3 \rightsquigarrow 0`.
The multi-edge lift $`\mathcal{M}(\mathit{ms})` adds such a step for every
level $`m` in a list $`\mathit{ms}`; its edge worlds are the $`m + 3`, each with
steps to $`0` and to $`f`.

{stmt}`cmM`

{docstring cmM +allowMissing}

{srcLink}`cmM`

{stmt}`IsEdge`

{docstring IsEdge +allowMissing}

{srcLink}`IsEdge`

For a finite set $`T` of indices the levels are the $`2j`, $`j \in T`, so the
edge worlds are $`E_T = \{2j + 3 : j \in T\}`, and the root is the highest of
them, $`\mathrm{root}(T) = 2 \max T + 3`.  Write $`\mathcal{M}_T` for this model.
For $`T = \{0, 1\}`:

```
   f        the fallible world: every world sees it

   0   1   2   3   4   5   6   7  ...     x sees y  iff  y = x  or  y <= x - 2
   ^           |       |
   |           |       |                  modal steps:  0 ~> f,
   +-----------+-------+                  and e ~> 0, e ~> f for each edge e

   T = {0, 1}:   E_T = {3, 5},   root(T) = 5
```

{stmt}`levels`

{docstring levels +allowMissing}

{srcLink}`levels`

{stmt}`root`

{docstring root +allowMissing}

{srcLink}`root`

# The forcing lemma

On $`\mathcal{M}_T` every odd gap with index outside $`T` holds at every world,
and every odd gap with index in $`T` fails at the root.  The proof has four
steps, all on $`\mathcal{M}_T` directly.

_Step 1._  The edges sit at worlds $`\ge 3`, so on the ladder $`\bigcirc\bot`
still holds at $`0` alone, and the substituted rungs keep their ladder truth
sets; in particular $`t_{2k+1}` holds exactly on $`[0, k]`.

_Step 2._  Hence $`\bigcirc t_{2k+1}` holds at $`x` exactly when every world
seen from $`x` is $`0`, an edge world, or at most $`k`.  PROVED.

{stmt}`cmM_chainF`

{docstring cmM_chainF +allowMissing}

{srcLink}`cmM_chainF`

_Step 3, off $`T`._  A world refuting $`g_{2i+1}` would force
$`\bigcirc t_{4i+3}` and refute $`t_{4i+3}`, so it would be some $`y > 2i + 1`
all of whose successors are $`0`, edge worlds or at most $`2i + 1`.  Since $`y`
sees itself, it is an edge world $`2j + 3`; $`j = i` is excluded by
$`i \notin T`, and $`j < i` by $`y > 2i + 1`, so $`y \ge 2i + 5`, and then the
even world $`2i + 2`, which $`y` sees, is none of the three.  PROVED.

{stmt}`forced_off`

{docstring forced_off +allowMissing}

{srcLink}`forced_off`

_Step 4, on $`T`._  For $`j \in T` the edge world $`2j + 3` is seen from the
root, forces $`\bigcirc t_{4j+3}` (each of its successors is itself, an edge
world, or at most $`2j + 1`) and refutes $`t_{4j+3}`, whose truth set is
$`[0, 2j + 1]`.  So the root refutes $`g_{2j+1}`.  PROVED.

{stmt}`fails_on`

{docstring fails_on +allowMissing}

{srcLink}`fails_on`

The two halves together are the forcing lemma.  PROVED.

{stmt}`MultiEdgeForcing`

{docstring MultiEdgeForcing +allowMissing}

{srcLink}`MultiEdgeForcing`

{stmt}`multi_edge_forcing`

{docstring multi_edge_forcing +allowMissing}

{srcLink}`multi_edge_forcing`

Only odd indices are used because the edge at level $`m` refutes the gaps with
index in its window $`\{m+1, m+2\}`; with $`m = 2j` the window holds one odd
index, $`2j + 1`, and the other odd gaps are untouched.

# Independence

Suppose $`\bigwedge_{i \in S} g_{2i+1} \vdash \bigvee_{j \in T} g_{2j+1}` with
$`S` and $`T` disjoint.  At the root of $`\mathcal{M}_T` every conjunct holds,
because its index is not in $`T`, so by soundness some disjunct holds there,
against the forcing lemma.  PROVED.

{stmt}`indep_of_forcing`

{docstring indep_of_forcing +allowMissing}

{srcLink}`indep_of_forcing`

{stmt}`indep`

{docstring indep +allowMissing}

{srcLink}`indep`

The case $`|T| = 1` had been proved earlier with the single-edge lifts
(`odd_gaps_single`, `wip/f0OddGaps.lean`); `indep` re-derives it without
`Classical.choice` as `odd_gaps_single_cf`.

# Axioms

As recorded in the file (`#axioms_within`): every declaration of this section
is within `propext`, `Quot.sound`, and `#print axioms` on the build reports
exactly `propext`, `Quot.sound` for each.  No `Classical.choice`: the model
$`\mathcal{M}_T` is used directly and the single-edge lifts not at all (their
frame-law proof reaches `Classical.byContradiction`, as traced with
`#choice_path` in `wip/f0OddGaps.lean`), and the
odd rungs' truth sets on the ladder are re-proved choice-free
(`sat_rn_odd_cf`), by splitting the `omega` call on a biconditional that
reached `Classical.propDecidable` into two calls on implications and replacing
two `by_contra` steps by case splits on decidable arithmetic.
