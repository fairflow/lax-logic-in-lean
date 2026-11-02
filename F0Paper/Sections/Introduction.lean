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

_New in v0.8._  Section 9: a copy of $`F_0` strictly below $`\top`, in
$`[t_3, t_6]`; which bases $`a` give a faithful copy by $`\bot \mapsto a`
(a criterion: exactly those with $`\nvdash \bigcirc a \twoheadrightarrow a` and
$`\nvdash (\bigcirc a \twoheadrightarrow a) \twoheadrightarrow a`, closing an
open problem of v0.7); the tops over $`t_3`; the shells of the nested copies.
Section 10: $`H_\omega` in every non-degenerate interval of its copy, nested to
every depth (O'Connor's interval translation), and PLL in an interval of
itself, with a nested tower of such copies carried into $`F_0`.  Section 12:
the join of the bases $`\sigma^{n}\bot` in $`F^{*}` is $`\top` although they
are not cofinal, which corrects a sentence of v0.7, and the intervals of the
$`t_6` tower close on one point.  Pins are written with one key (below).

_New in v0.7._  The definitions that neither the text nor a displayed result
mentions, with the supporting lemmas whose statements use them, have moved
from the tables at the ends of the sections to Appendix A.

_New in v0.6._  Section 10: the free Heyting algebra on countably many
generators is a Heyting subalgebra of the interval $`[\sigma^{3}\bot, \top]`
of $`F_0`, so intuitionistic propositional logic embeds faithfully into the
variable-free formulas of PLL, and so does PLL itself; with where the free
structure stops below $`\sigma^{3}\bot`, and why.  Sections 10 to 13 of v0.5 are now Sections 11
to 14.

_New in v0.5_ (in the present numbering).  Section 11 asks which filters $`[p, \top]` are isomorphic to
$`F_0`, and reduces the question to the filters above $`t_3`.  Section 12, on
the Dedekind–MacNeille completion $`F^{*}`, is rewritten: the construction by
cuts beside Dedekind's construction of $`\mathbb{R}`, where choice
enters, the extension of $`\bigcirc`, and the points of $`F^{*}`, with three new
theorems: $`F^{*}` has a point that is not principal,
$`|F^{*}| = 2^{\aleph_0}`, and $`F_0` has a filter that is not normal.
Section 13 tables what is established, with its
pins, and Section 14 lists the open problems, with sketches where there are
any.  Sections 8 and 9 of v0.5 were Sections 9 and 10 of v0.4.1.

# At a glance

{pinKey}

:::f0table (widths := "0.59 0.11 0.14 0.06")
* * Result
  * Status
  * Pin
  * §
* * Seven covers at the bottom; $`F_0` is not dense
  * PROVED
  * {pinsOf}`cover_0_1 cover_0_2 cover_1_3 cover_2_3 cover_1_4 cover_3_5 cover_4_5`
  * 3
* * $`F_0 = \{\bot, \lnot\bigcirc\bot\} \cup {\uparrow}\bigcirc\bot`
  * PROVED
  * {pinsOf}`low_trichotomy`
  * 3
* * The odd gaps are independent
  * PROVED
  * {pinsOf}`indep multi_edge_forcing`
  * 4
* * $`\mathbb{Q}` order-embeds in $`F_0`, explicitly and without choice
  * PROVED
  * {pinsOf}`Mink.qm_lt Mink.qm_onto rat_embedding_cf`
  * 5
* * The gaps have no greatest lower bound
  * PROVED
  * {pinsOf}`gap_no_glb L_no_greatest`
  * 6
* * Pairs of the odd-gap lattice have $`\aleph_0` pairwise $`\parallel` threads
  * PROVED
  * {pinsOf}`incomparable_copies`
  * 7
* * Outside a finite downset table there is an upper cover
  * PROVED
  * {pinsOf}`cover_above`
  * 7
* * Every $`{\downarrow}t_n` is finite
  * REFUTED
  * {pinsOf}`T6.t6_downset_infinite T6.rung_downset_infinite`
  * 8
* * $`{\downarrow}t_8` is finite
  * OPEN
  * –
  * 14
* * $`\sigma = [\bot := t_3]` embeds $`F_0` in $`[t_3, \top]`; the copies $`\sigma^{n}(F_0)` are strictly nested
  * PROVED
  * {pinsOf}`Sig.sigN_faithful Sig.copies_strict`
  * 9
* * $`\sigma` is onto $`[t_3, \top]`; $`[t_3, \top]` is order-isomorphic to $`F_0`
  * REFUTED
  * {pinsOf}`SigOnto.sig_not_onto NotIso.t3_filter_not_iso`
  * 9
* * $`\tau(A) = \sigma(A) \land t_6` embeds $`F_0` in $`[t_3, t_6]`, strictly below $`\top`; its iterates give strictly nested intervals
  * PROVED
  * {pinsOf}`MovingTop.copyT3T6 MovingTop.w3`
  * 9
* * For variable-free $`a`: $`\bot \mapsto a` is faithful iff PLL embeds in $`[a, \top]` iff $`\nvdash \bigcirc a \twoheadrightarrow a` and $`\nvdash (\bigcirc a \twoheadrightarrow a) \twoheadrightarrow a`
  * PROVED
  * {pinsOf}`Endpoints.baseCriterion`
  * 9
* * The tops $`b` with $`F_0` in $`[t_3, b]` have a least element
  * REFUTED
  * {pinsOf}`Endpoints.noLeastTopT3`
  * 9
* * $`\sigma^{\omega}(F_0) = \{\top\}`; $`\sigma` maps each shell $`L_n` one-to-one onto $`L_{n+1}`
  * PROVED
  * {pinsOf}`InsideOut.lim_eq_top InsideOut.shell_shift`
  * 9
* * IPC embeds faithfully in $`F_0`: $`H_\omega` and every $`H_n` lie in $`[\sigma^{3}\bot, \top]`, from one family of variable-free generators, and in every $`[\sigma^{m}\bot, \top]`, $`m \ge 3`
  * PROVED
  * {pinsOf}`Base3.freeHAnAbove_base3 Base3.freeHAωAbove_base3 Base3.freeFamily3 AnyFamily.allAbove3 AnyFamily.allAbove3ω`
  * 10
* * $`H_2` lies in $`[t_3, \top]`, with bottom $`t_3`
  * REFUTED
  * {pinsOf}`FreeIPL.noFreeHA2`
  * 10
* * PLL embeds faithfully in $`F_0`, with $`\bigcirc \mapsto \bigcirc`
  * PROVED
  * {pinsOf}`FreePLL.freeReaders FreePLL.freePLLAbove_base3`
  * 10
* * $`H_\omega` lies in every non-degenerate interval of its copy in $`[\sigma^{3}\bot, \top]`, nested to every depth, with the interval operations of $`F_0`
  * PROVED
  * {pinsOf}`Interval.mainTheorem Interval.bridge3 Interval.nestAll Interval.hereditary_ops`
  * 10
* * PLL embeds faithfully in its own interval $`[t_3, t_6]`; a strictly nested tower of such copies, carried into $`F_0`
  * PROVED
  * {pinsOf}`MovingTop.pllSelf MovingTop.pllSelfTower MovingTop.pllTowerInF0`
  * 10
* * The readers give PLL in $`[\sigma^{3}\bot, t_6 \lor \sigma^{3}\bot]`; variable-free generators give PLL in some $`[t_3, b]`
  * REFUTED
  * {pinsOf}`MovingTop.not_pllBelowTop Endpoints.noClosedStepT3`
  * 10
* * $`H_3` lies in $`[\sigma^{2}\bot, \top]`
  * OPEN
  * –
  * 14
* * No proper filter is isomorphic to $`F_0` iff none above $`t_3` is
  * PROVED
  * {pinsOf}`FilterIso.filterIsoQ_iff_aboveResidue_t3`
  * 11
* * Some filter $`[p, \top]` with $`t_3 \le p` is order-isomorphic to $`F_0`
  * OPEN
  * –
  * 14
* * $`F^{*}` is a complete Heyting algebra with $`F_0` join- and meet-dense in it
  * PROVED
  * {pinsOf}`le_cutHimp_iff principal_himp sSup_principal_left sInf_principal_right`
  * 12
* * $`\bigcirc` extends to $`F^{*}` as a nucleus, greatest among extensions
  * PROVED
  * {pinsOf}`circ_extends_to_DM`
  * 12
* * Nuclear extensions to the completion are unique
  * REFUTED
  * {pinsOf}`MacNeilleNonUnique.nucleus_extension_not_unique`
  * 12
* * … at $`F_0`
  * OPEN
  * –
  * 14
* * $`F^{*}` has a point that is not principal; $`|F^{*}| = 2^{\aleph_0}`
  * PROVED
  * {pinsOf}`Points.gapCut_ne_principal Points.card_eq_continuum`
  * 12
* * Some filter of $`F_0` is not normal ($`F_7`)
  * PROVED
  * {pinsOf}`Normal.notAllNormal`
  * 12
* * The only upper bound of the bases $`\sigma^{n}\bot` is $`\top`, though they are not cofinal
  * PROVED
  * {pinsOf}`MovingTop.basesOnlyTop MovingTop.notCofinal`
  * 12
* * Some element of $`F_0` lies in every interval of the $`t_6` tower iff $`\tau` has a fixed point in $`F_0`, and there is at most one
  * PROVED
  * {pinsOf}`Endpoints.fixedIffInAll Endpoints.inAllUnique`
  * 12
* * $`\tau` has a fixed point in $`F_0`
  * OPEN
  * –
  * 14
* * $`F_0` in $`[a, b]` gives PLL in $`[a, b]` by the A-translation (PROVED at $`b = \top`)
  * OPEN
  * –
  * 14
* * The nested intervals of $`H_\omega` hold for PLL
  * OPEN
  * –
  * 14
* * Some filter over a limit point of $`F^{*}` is not normal
  * OPEN
  * –
  * 14
* * $`F^{*}` can be built without choice
  * OPEN
  * –
  * 14
:::

# How to read the results

Each headline result is stated in words where the formula does not say it,
then displayed as a formula generated from its Lean statement, then given
beneath in small type as the Lean statement with a link to its source line (in
the HTML, a panel that opens on click).  That line is Lean's pretty-printing of
the compiled declaration: exactly the statement the kernel checked, but not the
source text, which the link gives.  When the result is a proposition defined
by name, a second small line gives its definition.  Supporting declarations are
tabled at the end of each section, each row with its source line and its
pin; Section 13 gives the pin of every headline result.  Pins are computed by
`collectAxioms` when the document is built.  PROVED means kernel-checked and
sorry-free; REFUTED, a kernel-checked counterexample; a _pen argument_ is a
proof on paper, not mechanised; anything else is OPEN.  In displays the
meta-level connectives are written “and”, “or”, and $`x \in \mathrm{Fm}_0`
says that $`x` is variable-free.  The declarations are in the repository's
`wip/` directory and in `LaxLogic/PLL/SubTab`; the figures are drawn by
`scripts/f0-figures.py` from data Lean computes.
