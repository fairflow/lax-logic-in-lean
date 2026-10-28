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
open F0Nuclear MacNeille MacNeille.JoinDenseHeytingEmbedding

#doc (Manual) "Introduction" =>

Propositional lax logic (PLL) {pcite}`FairtloughMendler1997` extends
intuitionistic propositional logic by one modality $`\bigcirc`.  Its
variable-free formulas, built from $`\bot` by $`\land`, $`\lor`,
$`\twoheadrightarrow`, $`\bigcirc`, form under $`\dashv\vdash` an infinite
algebra $`F_0`, ordered by $`\vdash`; in intuitionistic logic there would be just
$`\bot` and $`\top`.  The question was whether $`F_0` is dense as an order, and
whether the open interval of every pair $`u < v` contains a _thread_, the image
of an order embedding of $`\mathbb{Q}` (Section 2 fixes this vocabulary).
Neither holds: there are covers.  But $`\mathbb{Q}` does embed, $`F_0` embeds in
a proper interval of itself, and much of its order is now known.

_New in v0.6._  Section 10: the free Heyting algebra on countably many
generators is a Heyting subalgebra of the interval $`[\sigma^{3}\bot, \top]`
of $`F_0`, so intuitionistic propositional logic embeds faithfully into the
variable-free formulas of PLL; with where the free structure stops below
$`\sigma^{3}\bot`, and why.  Sections 10 to 13 of v0.5 are now Sections 11
to 14.

_New in v0.5_ (in the present numbering).  Section 11 asks which filters $`[p, \top]` are isomorphic to
$`F_0`, and reduces the question to the filters above $`t_3`.  Section 12, on
the Dedekind–MacNeille completion $`F^{*}`, is rewritten: the construction by
cuts beside Dedekind's construction of $`\mathbb{R}`, where `Classical.choice`
enters, the extension of $`\bigcirc`, and the points of $`F^{*}`, with three new
theorems: $`F^{*}` has a point that is not principal,
$`|F^{*}| = 2^{\aleph_0}`, and $`F_0` has a filter that is not normal.
Section 13 tables what is established, with its
axioms, and Section 14 lists the open problems, with sketches where there are
any.  Sections 8 and 9 of v0.5 were Sections 9 and 10 of v0.4.1.

# At a glance

:::f0table (widths := "0.72 0.18 0.06")
* * Result
  * Status
  * §
* * Seven covers at the bottom; $`F_0` is not dense
  * PROVED
  * 3
* * $`F_0 = \{\bot, \lnot\bigcirc\bot\} \cup {\uparrow}\bigcirc\bot`
  * PROVED
  * 3
* * The odd gaps are independent
  * PROVED
  * 4
* * $`\mathbb{Q}` order-embeds in $`F_0`, explicitly and without choice
  * PROVED
  * 5
* * The gaps have no greatest lower bound
  * PROVED
  * 6
* * Pairs of the odd-gap lattice have $`\aleph_0` pairwise $`\parallel` threads
  * PROVED
  * 7
* * Outside a finite downset table there is an upper cover
  * PROVED
  * 7
* * Every $`{\downarrow}t_n` is finite
  * REFUTED
  * 8
* * $`{\downarrow}t_8` is finite
  * OPEN
  * 14
* * $`\sigma = [\bot := t_3]` embeds $`F_0` in $`[t_3, \top]`; the copies $`\sigma^{n}(F_0)` are strictly nested
  * PROVED
  * 9
* * $`\sigma` is onto $`[t_3, \top]`; $`[t_3, \top]` is order-isomorphic to $`F_0`
  * REFUTED
  * 9
* * IPC embeds faithfully in $`F_0`: $`H_\omega` and every $`H_n` lie in $`[\sigma^{3}\bot, \top]`, from one family of variable-free generators, and in every $`[\sigma^{m}\bot, \top]`, $`m \ge 3`
  * PROVED
  * 10
* * $`H_2` lies in $`[t_3, \top]`, with bottom $`t_3`
  * REFUTED
  * 10
* * $`H_3` lies in $`[\sigma^{2}\bot, \top]`; PLL embeds faithfully in $`F_0`
  * OPEN
  * 14
* * No proper filter is isomorphic to $`F_0` iff none above $`t_3` is
  * PROVED
  * 11
* * Some filter $`[p, \top]` with $`t_3 \le p` is order-isomorphic to $`F_0`
  * OPEN
  * 14
* * $`F^{*}` is a complete Heyting algebra with $`F_0` join- and meet-dense in it
  * PROVED
  * 12
* * $`\bigcirc` extends to $`F^{*}` as a nucleus, greatest among extensions
  * PROVED
  * 12
* * Nuclear extensions to the completion are unique
  * REFUTED
  * 12
* * … at $`F_0`
  * OPEN
  * 14
* * $`F^{*}` has a point that is not principal; $`|F^{*}| = 2^{\aleph_0}`
  * PROVED
  * 12
* * Some filter of $`F_0` is not normal ($`F_7`)
  * PROVED
  * 12
* * Some filter over a limit point of $`F^{*}` is not normal
  * OPEN
  * 14
* * $`F^{*}` can be built without `Classical.choice`
  * OPEN
  * 14
:::

# How to read the results

Each headline result is stated in words where the formula does not say it,
then displayed as a formula generated from its Lean statement, then given
beneath in small type as the Lean statement with a link to its source line (in
the HTML, a panel that opens on click).  That line is Lean's pretty-printing of
the compiled declaration: exactly the statement the kernel checked, but not the
source text, which the link gives.  Supporting declarations are tabled at the
end of each section, with the axiom pins; Section 13 gives the axioms of every
headline result, computed by `collectAxioms` when the document is built.
PROVED means kernel-checked and sorry-free; REFUTED, a kernel-checked
counterexample; a _pen argument_ is a proof on paper, not mechanised; anything
else is OPEN.  In displays the meta-level connectives are written “and”, “or”,
and $`x \in \mathrm{Fm}_0` says that $`x` is variable-free.  The declarations
are in the repository's `wip/` directory and in `LaxLogic/PLL/SubTab`; the
figures are drawn by `scripts/f0-figures.py` from data Lean computes.
