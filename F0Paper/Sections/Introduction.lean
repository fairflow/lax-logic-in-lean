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

#doc (Manual) "Introduction" =>

This section states the question the document answers, summarises the
answers, and describes the layout.  It has no results of its own; every claim
in it is proved in a later section, which it names.

# The question

Propositional lax logic (PLL) {pcite}`FairtloughMendler1997` extends
intuitionistic propositional logic by one modality $`\bigcirc`.  A formula is
_variable-free_ when it contains no propositional variable: it is built from
$`\bot` by $`\land`, $`\lor`, $`\twoheadrightarrow` and $`\bigcirc`.  In
intuitionistic logic the variable-free formulas are, up to interderivability,
just $`\bot` and $`\top`.  In PLL they are not: $`\bigcirc\bot` is neither, and
the formulas $`\bigcirc\bot`, $`\lnot\bigcirc\bot`,
$`\bigcirc\bot \lor \lnot\bigcirc\bot`, … continue without end.

Write $`F_0` for the Lindenbaum algebra of the variable-free formulas: its
elements are the classes of variable-free formulas under $`\dashv\vdash`, and
it is ordered by $`\vdash`.  It is a Heyting algebra with a nucleus, the
initial one (Section 2), and it is infinite.  The question asked about it was:

* Is $`F_0` dense: for $`u < v`, is there always $`w` with $`u < w < v`?
* Does every interval $`[u, v]` with $`u < v` contain an order-embedded copy of
  $`\mathbb{Q}`?

# The answers

All of the following are PROVED: kernel-checked in Lean, sorry-free, with the
axiom sets stated in each section.

_Covers exist at the bottom._  With $`t_n` the $`n`-th Rieger–Nishimura rung
with $`\bigcirc\bot` for its variable (Section 2), so that $`t_0 = \bot`,
$`t_1 = \bigcirc\bot` and $`t_2 = \lnot\bigcirc\bot`, there are seven covers

$$`t_0 \lessdot t_1 \qquad t_0 \lessdot t_2 \qquad t_1 \lessdot t_3 \qquad t_2 \lessdot t_3 \qquad t_1 \lessdot t_4 \qquad t_3 \lessdot t_5 \qquad t_4 \lessdot t_5`

in $`F_0` (Section 3).  So $`F_0` is not dense, and the interval
$`[\bot, \bigcirc\bot]` has two elements: not every interval contains
$`\mathbb{Q}`.  The proof identifies the downset of each of $`t_1, \ldots, t_5`
exactly, using that a downset of $`F_0` is a quotient of $`F_0`.  A corollary is
a trichotomy: every variable-free $`x` satisfies $`\bigcirc\bot \vdash x`, or
$`x \dashv\vdash \bot`, or $`x \dashv\vdash \lnot\bigcirc\bot`.

_The odd gaps are independent._  The gaps are
$`g_k = \bigcirc t_{2k+1} \twoheadrightarrow t_{2k+1}`, and for all finite
disjoint $`S, T \subseteq \mathbb{N}`

$$`\bigwedge_{i \in S} g_{2i+1} \;\nvdash\; \bigvee_{j \in T} g_{2j+1}`

(Section 4).  This is the condition under which elements of a distributive
lattice generate a free distributive lattice.  The proof is one family of
constraint models: the Rieger–Nishimura ladder with one extra modal edge for
each index in $`T`.

_The rationals order-embed in $`F_0`._  Lattice polynomials in the odd gaps
give a map $`f` from the dyadic rationals in $`[0, 1]` to variable-free formulas
with $`f(0) = \bot`, $`f(1) = \top`, and

$$`d < d' \;\Longrightarrow\; f(d) \vdash f(d') \;\text{and}\; f(d') \nvdash f(d),`

an order embedding (Section 5).  Minkowski's question-mark function, composed
with an explicit order-isomorphism from $`\mathbb{Q}` onto
$`\mathbb{Q} \cap (0, 1)`, is an explicit order-isomorphism from $`\mathbb{Q}`
onto the dyadic rationals strictly between $`0` and $`1`; composing it with
$`f` gives an order embedding of $`\mathbb{Q}` in $`F_0`, without
`Classical.choice`.  A second route, through Cantor's theorem on countable
dense linear orders, gives an order embedding too, and carries
`Classical.choice`.

_A cut that $`F_0` does not fill._  The gaps $`g_k`, $`k \ge 1`, have no greatest
lower bound, among the variable-free formulas or among all formulas
(Section 6).

The answer to the first question is therefore no, and so is the answer to the
second as stated, while $`\mathbb{Q}` does order-embed in $`F_0` itself.
Section 7 will list the questions that remain, with their status.

# Layout

Section 2 fixes the logic, its models, $`F_0`, the rungs and the gaps.
Sections 3 to 6 prove the results above, one section each.  Section 7 is
reserved for the open questions, and Section 8 lists the references.

Each result is stated in words, then as a displayed formula generated from the
Lean statement when the document is built, then as the Lean declaration
printed from the compiled library, then as a link to its source line at the
commit that was built.  The declarations live in the repository's `wip/`
directory: `wip/f0Covers.lean`, `wip/f0Indep.lean`, `wip/f0Dyadic.lean`,
`wip/f0Minkowski.lean`, `wip/f0Rat.lean`, `wip/gapWidth.lean`,
`wip/embedNeg.lean`, `wip/floor.lean`
and the files they import.  In the displayed formulas the meta-level
conjunction and disjunction are written "and" and "or", so that they are not
confused with the connectives $`\land` and $`\lor` of PLL, and
$`x \in \mathrm{Fm}_0` says that $`x` is variable-free.
