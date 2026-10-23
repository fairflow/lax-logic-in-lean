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
* Does the open interval $`(u, v)` of every pair $`u < v` contain a _thread_,
  the image of an order embedding of $`\mathbb{Q}`?

Section 2 fixes this vocabulary: pairs, intervals, threads, the relation
$`A \parallel B` of sets no element of one of which is comparable with an
element of the other, and four levels of an interval: finite, containing a
thread, containing a free distributive lattice on countably many generators,
and containing a faithful copy of $`F_0`.

# The answers

All of the following are PROVED, kernel-checked in Lean and sorry-free, with
the axiom sets stated in each section, except where a statement is marked
REFUTED or OPEN.

_Covers exist at the bottom._  With $`t_n` the $`n`-th Rieger–Nishimura rung
with $`\bigcirc\bot` for its variable (Section 2), so that $`t_0 = \bot`,
$`t_1 = \bigcirc\bot` and $`t_2 = \lnot\bigcirc\bot`, there are seven covers

$$`t_0 \lessdot t_1 \qquad t_0 \lessdot t_2 \qquad t_1 \lessdot t_3 \qquad t_2 \lessdot t_3 \qquad t_1 \lessdot t_4 \qquad t_3 \lessdot t_5 \qquad t_4 \lessdot t_5`

in $`F_0` (Section 3).  So $`F_0` is not dense, and the open interval
$`(\bot, \bigcirc\bot)` is empty: not every pair has a thread.  The proof
identifies the downset of each of $`t_1, \ldots, t_5` exactly, using that a
downset of $`F_0` is a quotient of $`F_0`.  A corollary is a trichotomy: every
variable-free $`x` satisfies $`\bigcirc\bot \vdash x`, or $`x \dashv\vdash \bot`,
or $`x \dashv\vdash \lnot\bigcirc\bot`.

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
$`f` gives a thread in $`(\bot, \top)`, without `Classical.choice`.  A second
route, through Cantor's theorem on countable dense linear orders, gives an
order embedding too, and carries `Classical.choice`.

_Cuts that $`F_0` does not fill._  The gaps $`g_k`, $`k \ge 1`, have no greatest
lower bound, among the variable-free formulas or among all formulas
(Section 6), and neither has the descending chain $`f(1/2^n)` of the dyadic
thread (Section 7).

_Covers and threads together._  Apart from its bottom, the dyadic thread lies
above the rungs $`t_0, \ldots, t_{15}`, and not above $`t_{16}`.  Derivability
between lattice polynomials in the odd gaps is Boolean entailment, and for
every pair $`p < q` of them the open interval $`(p, q)` contains $`\aleph_0`
threads, pairwise $`\parallel`.  An element outside the downset of a finite
table has an upper cover (Section 7).

_The completion._  $`F_0` is a Heyting algebra with the nucleus $`\bigcirc`, and
$`\bigcirc` extends to its Dedekind–MacNeille completion as a nucleus, the
greatest monotone extension.  The extension theorem is Goldblatt's; the
extensions form an interval, and they are not unique in general: REFUTED by a
chain.  Uniqueness at $`F_0` is OPEN (Section 8).

_Below the sixth rung._  The conjecture that every downset $`{\downarrow}t_n` is
finite holds for $`n \le 5` (Section 3), and it is REFUTED for $`n = 6, 7` and
every $`n \ge 9`; for $`n = 8` it is OPEN.  The sixth rung is double-negation
elimination for $`\bigcirc\bot`,
$`t_6 \dashv\vdash \lnot\lnot\bigcirc\bot \twoheadrightarrow \bigcirc\bot`, and
below it the formula $`\bigcirc\lnot\bigcirc\bot` generates a Rieger–Nishimura
ladder relativised to the interval above $`t_3`, an infinite strictly
increasing chain.  The fifth rung, weak excluded middle for $`\bigcirc\bot`, has
a downset of six elements (Section 9).

_Self-similarity._  The substitution
$`\sigma(\varphi) = \varphi[\bot := \bigcirc\bot \lor \lnot\bigcirc\bot]`, which on
variable-free formulas is Friedman's A-translation, is an order embedding of
$`F_0` into the interval $`[t_3, \top]`.  It preserves derivability by
Friedman's lemma, and it reflects derivability for every formula, by a
choice-free argument from the subframe tableau.  Its iterates give an infinite
descending sequence of nested copies of $`F_0` inside $`F_0`, and the chain
below the sixth rung is the image under $`\sigma` of the Rieger–Nishimura ladder
(Section 10).

The answer to the first question is therefore no, and so is the answer to the
second as stated, while $`\mathbb{Q}` does order-embed in $`F_0` itself, and
every pair of lattice polynomials in the odd gaps has $`\aleph_0` threads.
Section 11 lists the questions that remain, with their status.

# Layout

Section 2 fixes the logic, its models, $`F_0`, the rungs, the gaps, and the
vocabulary of pairs and threads.  Sections 3 to 10 prove the results above, one
topic each, and Section 11 lists the open questions.  Section 12 lists the
references.

Each result is stated in words, then as a displayed formula generated from the
Lean statement when the document is built, then as the Lean declaration
printed from the compiled library, then as a link to its source line at the
commit that was built.  The declarations live in the repository's `wip/`
directory: `wip/f0Covers.lean`, `wip/f0Indep.lean`, `wip/f0Dyadic.lean`,
`wip/f0Minkowski.lean`, `wip/f0Rat.lean`, `wip/f0Structure.lean`,
`wip/f0Hole.lean`, `wip/f0Nuclear.lean`, `wip/f0MacNeille.lean`,
`wip/f0MacNeilleNonUnique.lean`, `wip/f0T6.lean`, `wip/f0SelfSim.lean`,
`wip/gapWidth.lean`, `wip/embedNeg.lean`, `wip/floor.lean` and the files they
import.  The subframe tableau used in Section 10 is in the library proper,
under `LaxLogic/PLL/SubTab`.  In the displayed formulas the meta-level conjunction and disjunction are written "and" and "or",
so that they are not confused with the connectives $`\land` and $`\lor` of PLL,
and $`x \in \mathrm{Fm}_0` says that $`x` is variable-free.
