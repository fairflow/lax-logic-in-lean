import Verso
import VersoManual
import CLPPaper.Src
import CLPPaper.Cite
import F0Paper.Math
import F0Paper.Blocks

open Verso.Genre
open Verso.Genre.Manual
open CLPPaper CLPPaper.Cite F0Paper.Math F0Paper.Blocks
open PLLND PLLND.SemUI PLLND.F0 PLLND.RNEmbed
open PLLND.LaxInfinite (atomFree)
open F0Nuclear MacNeille MacNeille.JoinDenseHeytingEmbedding

#doc (Manual) "Introduction" =>

Propositional lax logic (PLL) {pcite}`FairtloughMendler1997` extends
intuitionistic propositional logic by one modality $`\bigcirc`.  Its
variable-free formulas, built from $`\bot` by $`\land`, $`\lor`,
$`\twoheadrightarrow`, $`\bigcirc`, form under $`\dashv\vdash` an infinite
algebra $`F_0`, ordered by $`\vdash`; in intuitionistic logic there would be just
$`\bot` and $`\top`.  The question was whether $`F_0` is dense, and whether the
open interval of every pair $`u < v` contains a _thread_, the image of an order
embedding of $`\mathbb{Q}` (Section 2 fixes this vocabulary).  Neither holds:
there are covers.  But $`\mathbb{Q}` does embed, $`F_0` embeds in a proper
interval of itself, and much of its order is now known.

# At a glance

:::f0table (widths := "0.44 0.1 0.38 0.05")
* * Result
  * Status
  * Axioms
  * §
* * Seven covers at the bottom; $`F_0` is not dense
  * PROVED
  * {axiomsOf}`cover_0_1 cover_0_2 cover_1_3 cover_2_3 cover_1_4 cover_3_5 cover_4_5`
  * 3
* * $`F_0 = \{\bot, \lnot\bigcirc\bot\} \cup {\uparrow}\bigcirc\bot`
  * PROVED
  * {axiomsOf}`low_trichotomy`
  * 3
* * The odd gaps are independent
  * PROVED
  * {axiomsOf}`indep`
  * 4
* * $`\mathbb{Q}` order-embeds in $`F_0`, explicitly
  * PROVED
  * {axiomsOf}`rat_embedding_cf`
  * 5
* * The gaps have no greatest lower bound
  * PROVED
  * {axiomsOf}`gap_no_glb`
  * 6
* * Pairs of the odd-gap lattice have $`\aleph_0` pairwise $`\parallel` threads
  * PROVED
  * {axiomsOf}`incomparable_copies lpoly_deriv_iff`
  * 7
* * Outside a finite downset table there is an upper cover
  * PROVED
  * {axiomsOf}`cover_above`
  * 7
* * $`\bigcirc` extends to $`\mathrm{DM}(F_0)`, greatest among extensions
  * PROVED
  * {axiomsOf}`circ_extends_to_DM`
  * 8
* * Nuclear extensions to the completion are unique
  * REFUTED
  * {axiomsOf}`MacNeilleNonUnique.nucleus_extension_not_unique`
  * 8
* * … at $`F_0`
  * OPEN
  * –
  * 11
* * Every $`{\downarrow}t_n` is finite
  * REFUTED
  * {axiomsOf}`T6.rung_downset_infinite`
  * 9
* * $`{\downarrow}t_8` is finite
  * OPEN
  * –
  * 11
* * $`\sigma = [\bot := t_3]` embeds $`F_0` in $`[t_3, \top]`
  * PROVED
  * {axiomsOf}`Sig.sigN_faithful`
  * 10
* * The copies $`\sigma^{n}(F_0)` are strictly nested
  * PROVED
  * {axiomsOf}`Sig.copies_strict`
  * 10
* * $`\sigma` is onto $`[t_3, \top]`
  * REFUTED
  * {axiomsOf}`SigOnto.sig_not_onto`
  * 10
* * $`[t_3, \top]` is order-isomorphic to $`F_0`
  * OPEN
  * –
  * 11
:::

The axioms are computed by `collectAxioms` when the document is built.

# How to read the results

Each headline result is stated in words where the formula does not say it,
then displayed as a formula generated from its Lean statement, then given
beneath in small type as the Lean statement with a link to its source line (in
the HTML, a panel that opens on click).  That line is Lean's pretty-printing of
the compiled declaration: exactly the statement the kernel checked, but not the
source text, which the link gives.  Supporting declarations are tabled at the
end of each section, with the axiom pins.  PROVED means kernel-checked and
sorry-free; REFUTED, a kernel-checked counterexample; anything else is OPEN, or
marked as a pen argument.  In displays the meta-level connectives are written
"and", "or", and $`x \in \mathrm{Fm}_0` says that $`x` is variable-free.  The
declarations are in the repository's `wip/` directory and in
`LaxLogic/PLL/SubTab`; the figures are drawn by `scripts/f0-figures.py` from
data Lean computes.
