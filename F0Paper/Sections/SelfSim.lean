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

set_option paperkit.pins true

#doc (Manual) "Self-similarity" =>

Substituting $`t_3` for $`\bot`,

$$`\sigma(\varphi) = \varphi[\bot := \bigcirc\bot \lor \lnot\bigcirc\bot],`

is Friedman's A-translation {pcite}`Friedman1978` with $`A = t_3`, restricted
to variable-free formulas.  It is an order embedding of $`F_0` into
$`[t_3, \top]`, and its iterates give an infinite descending sequence of nested
copies of $`F_0` inside $`F_0`.  A second translation moves the top as well
and gives a copy of $`F_0` strictly below $`\top`; the last subsections say
which bases and which tops admit a copy, and how the copies
$`\sigma^{n}(F_0)` divide $`F_0`.  No choice; `wip/f0SelfSim.lean`,
`wip/f0MovingTop.lean`, `wip/f0Endpoints.lean`, `wip/f0InsideOut.lean`.

:::f0Figure "selfsim"
Top: the rungs $`t_0, \ldots, t_5` (order decided by `rungCovers`, through
`rnSub_order`) and their images under $`\sigma` inside $`[t_3, \top]`, in the same
order (`sigN_faithful`), with $`\sigma(t_0) = t_3` and
$`\sigma(t_3) = \bigcirc t_3 \lor g_1` (`sig_t3`; both decided by Lean).  Below:
the copies $`\sigma^{n}(F_0)`, $`n = 0, 1, 2`, with their bases
$`\bot < t_3 < \sigma^{2}(\bot)`, where $`\sigma^{2}(\bot) = \sigma(t_3)`.  Each
copy is faithful (`sigN_faithful`) and lies in $`[\sigma^{n}(\bot), \top]`
(`sigN_bot_le`); the bases increase strictly (`sigN_bot_strict`), and
$`\sigma^{n}(\bot) \notin \sigma^{n+1}(F_0)` (`copies_strict`).  Schematic:
positions not to scale; every inclusion and every line drawn is a named
theorem.
:::

_Preservation_ is Friedman's lemma for PLL: derivations translate, and $`a`
entails every $`\varphi^{a}` (atoms $`p \mapsto p \lor a`, $`\bot \mapsto a`).
PROVED for every formula; on variable-free formulas $`\varphi^{a}` is
$`\varphi[\bot := a]` (`subBot_eq_aTr`).  The atom clause is needed:
$`t_3 \nvdash p` (`cell_corr`).

{stmt}`Sig.aTr_deriv`

{leanStmt Sig.aTr_deriv}

_Reflection_ holds for every formula: $`\vdash \sigma(\chi)` implies
$`\vdash \chi`.  The proof is choice-free.  The subframe tableau decides PLL
without choice (`SubTab.complete`): $`\chi` has a closed tableau, or
a finite subframe countermodel $`M, r \nVdash \chi` (an intuitionistic Kripke
model with a set $`S` of worlds, $`\bigcirc A` holding at $`x` when $`A` holds at
every world of $`S` above $`x`).  Completeness of PLL for finite models of
this kind is known: the finite model property is due to {cite}`Goldblatt1981`
and {cite}`FairtloughMendler1997`; the reading of $`\bigcirc` through a subset
$`S` rests on the correspondence between nuclei and subframes
{pcite}`BezhanishviliGhilardi2007`, and completeness for finite models with a
set $`S` is stated explicitly in Theorem 3.4.5 of {cite}`Melzer2020`; see also
{cite}`BezhanishviliBezhanishviliIlin2019`.  Add two top worlds above $`M`: $`n_T \in S`,
where $`\lnot\bigcirc\bot` holds, and $`e_T \notin S`, where $`\bigcirc\bot` holds.
Then $`t_3 = \sigma(\bot)` holds exactly at the tops, every $`\sigma(\psi)` holds
at both (`top_sig`), and at old worlds $`\sigma(\psi)` holds where $`\psi` does
(`orig_sig`); so $`\sigma(\chi)` fails at $`r`.  The statement was first tested
on five designed cells.  PROVED.

{stmt}`Sig.sigN_faithful`

{leanStmt Sig.sigN_faithful}

_Nested copies._  $`\sigma^{n}(F_0) \subseteq [\sigma^{n}(\bot), \top]`, the
bases increase strictly, and $`\sigma^{n}(\bot) \notin \sigma^{n+1}(F_0)`, so
the copies are strictly nested.  PROVED.  In the levels of Section 2 each
$`[\sigma^{n}(\bot), \top]` is at level 4 (with the pen identity
$`h_{\sigma^{n}(\bot), \top}(\varphi) \dashv\vdash \sigma^{n}(\varphi)`).

{stmt}`Sig.copies_strict`

{leanStmt Sig.copies_strict}

On the rungs, $`\sigma(t_n) \dashv\vdash \mathrm{rel}(r_n)`, so the chain below the
sixth rung (Section 8) is the image of the ladder under $`\sigma`.  PROVED.

{stmt}`Sig.sig_ladder`

{leanStmt Sig.sig_ladder}

# Not onto

The observation is Matthew Fairtlough's.  The embedding $`\sigma` preserves the
order but not covers, and it is not onto $`[t_3, \top]`.  In $`F_0`,
$`\bot \lessdot t_2` (Section 3), while

$$`\sigma(\bot) = t_3 < t_5 < g_1 = \sigma(t_2),`

where $`\sigma(t_2) = g_1` holds by `rfl` (`sig_t2`) and the four parts of
$`t_3 < t_5 < g_1` are kernel-checked (`t3_lt_t5_lt_g1`: $`t_3 \vdash t_5` by
$`\lor`-introduction, $`t_5 \nvdash t_3` as in Section 3, and $`t_5 \vdash g_1`,
$`g_1 \nvdash t_5` by the subframe tableau).  So $`t_5 \in [t_3, \top] \setminus \sigma(F_0)`.  Proof: if
$`\sigma(y) \dashv\vdash t_5`, then $`\sigma(y) \vdash \sigma(t_2)`, and reflection
gives $`y \vdash t_2`.  By `low_trichotomy`, either $`\bigcirc\bot \vdash y`,
impossible as $`\bigcirc\bot \nvdash \lnot\bigcirc\bot`; or $`y \dashv\vdash \bot`,
and then $`\sigma(y) \dashv\vdash t_3`, against $`t_5 \nvdash t_3`; or
$`y \dashv\vdash t_2`, and then $`\sigma(y) \dashv\vdash g_1`, against
$`g_1 \nvdash t_5`.  PROVED.

{stmt}`SigOnto.sig_not_onto`

{leanStmt SigOnto.sig_not_onto}

The same witness lies strictly between the images of the cover
$`\bot \lessdot t_2`.  PROVED.

{stmt}`SigOnto.sig_not_cover`

{leanStmt SigOnto.sig_not_cover}

Pen remark, not mechanised: $`F_0` is initial among Heyting algebras with a
nucleus, so $`\sigma` is the only homomorphism of Heyting algebras with a nucleus
from $`F_0` to $`[t_3, \top]` (with bottom $`t_3`); since $`\sigma` is not onto,
$`[t_3, \top]` is not isomorphic to $`F_0` in that structure.

Nor is $`[t_3, \top]` even order-isomorphic to $`F_0`.  Call two elements above
the bottom a _disjoint pair_ when their only common lower bound is the bottom.
In $`F_0` every disjoint pair contains $`\lnot\bigcirc\bot`
(`disjoint_pair_has_negOBot`, from `low_trichotomy`), while in $`[t_3, \top]`
the pairs $`(c_1, g_1)`, where $`c_1 = \bigcirc t_3`, and $`(t_5, t_6)` are
disjoint and share no member (`two_disjoint_pairs_above_t3`).  A member lying
in every disjoint pair (`HasCore`) is carried across an order isomorphism
(`hasCore_of_iso`); $`F_0` has one (`rnclass_core`), $`[t_3, \top]` has none
(`ici_no_core`).  PROVED, so the order isomorphism is REFUTED.  Section 11
asks the same question of the other filters.

{stmt}`NotIso.t3_filter_not_iso`

{leanStmt NotIso.t3_filter_not_iso}

# A copy of F0 strictly below ⊤

Every copy $`\sigma^{n}(F_0)` reaches $`\top`.  A copy below $`\top` needs a
translation that moves the top too.  The _interval translation_ for
$`[a, b]` with generators $`x` sends $`\bot` to $`a` and each variable $`p` to
$`x(p)`, keeps $`\land` and $`\lor`, and meets $`\twoheadrightarrow` and
$`\bigcirc` with $`b`; it is the device of {cite}`OConnor2007`, used again
in Section 10.

{stmt}`Interval.rel`

On variable-free formulas the generators are not read, and
$`\tau_{a,b}` is the translation with $`x(p) = a`.  _$`F_0` embeds in
$`[a, b]`_ (`CopyF0In`) when $`\tau_{a,b}` preserves and reflects $`\vdash`
between variable-free formulas.  For $`a \vdash b` the translation is a meet
with the top.  PROVED.

{stmt}`MovingTop.RelClosed`

{leanStmt MovingTop.relClosed}

{leanDef MovingTop.RelClosed}

So a copy in $`[a, b]` exists exactly when $`b` proves $`C[\bot := a]` only for
theorems $`C` (`TopAvoid`).  PROVED.

{stmt}`MovingTop.CopyIffTopAvoid`

{leanStmt MovingTop.copyIffTopAvoid}

{leanDef MovingTop.CopyIffTopAvoid}

At $`a = t_3` the top $`t_6 = t_5 \twoheadrightarrow t_3` serves:
$`t_3 \vdash t_6` and $`\nvdash t_6` (`t3_t6`, `nd_t6`), and $`t_6 \vdash \sigma(C)` only for theorems $`C`, for every formula $`C` (`SigAvoidT6`, `sigAvoidT6`): in
the model of reflection, $`M` with the two top worlds, $`t_6` holds at every
world (`t6_ext`).  So $`\tau(A) \dashv\vdash \sigma(A) \land t_6`, with
$`\tau = \tau_{t_3, t_6}`, embeds $`F_0` faithfully in $`[t_3, t_6]`, an
interval strictly below $`\top`.  PROVED.

{stmt}`MovingTop.CopyT3T6`

{leanStmt MovingTop.copyT3T6}

{leanDef MovingTop.CopyT3T6}

The top $`t_5` fails: $`t_5 \vdash \sigma(t_3) = \sigma^{2}(\bot)`, by a closed
tableau (`t5_sig2_imp`), while $`\nvdash t_3` (`nd_t3`); so $`F_0` does not embed
in $`[t_3, t_5]` this way.  REFUTED (`CopyT3T5`, `not_copyT3T5`).

The iterates $`\tau^{d}` are interval translations again,
$`\tau^{d}(A) \dashv\vdash \tau_{\tau^{d}(\bot), \tau^{d}(\top)}(A)` (`W2`, `w2`),
and the intervals $`[\tau^{d}(\bot), \tau^{d}(\top)]` are strictly nested at
both ends.  PROVED, with the general form `StrictNestOf` (`strictNestOf`).  Where they close is
the subject of Section 12.

{stmt}`MovingTop.StrictNest`

{leanStmt MovingTop.w3}

{leanDef MovingTop.W3}

# Which bases

For a variable-free $`a`, when is $`\varphi \mapsto \varphi[\bot := a]`
faithful on $`F_0`?  At $`b = \top` the interval translation is this map
(`RelClosed`), so the question is $`\mathit{CopyStep}(a, \top)`, with
`CopyStep` the name of `CopyF0In` in `wip/f0Endpoints.lean`.  Since $`\lnot\bigcirc\bot` and
$`\lnot\lnot\bigcirc\bot` are no theorems, neither
$`(\lnot\bigcirc\bot)[\bot := a] = \bigcirc a \twoheadrightarrow a` nor
$`(\lnot\lnot\bigcirc\bot)[\bot := a] = (\bigcirc a \twoheadrightarrow a) \twoheadrightarrow a`
may be one.  These two conditions are also sufficient, and then even PLL
embeds in $`[a, \top]`, by the A-translation of Friedman's lemma meeting with
the top: $`\mathit{SelfStep}(a, b)` (`SelfStep`) says that $`\alpha_{a,b}(A) = A^{s_{a,b}}_{[a,b]}`, with $`s_{a,b}(p) = (p \lor a) \land b`, preserves and
reflects $`\vdash` between all formulas, $`\bigcirc` included.  PROVED.

{stmt}`Endpoints.BaseCriterion`

{leanStmt Endpoints.baseCriterion}

{leanDef Endpoints.BaseCriterion}

Proof of sufficiency (`ts_realizes`).  From countermodels of the two formulas
take two worlds refuting $`a` whose strict successors all force $`a`, one in
$`S` and one with no world of $`S` in its cluster (`sidesOfNd`).  Above every
world of a finite countermodel $`M` that sees $`S` put the strict successors
of the first, above every world that sees a world with no world of $`S` above
it those of the second (`TS`).  Each terminal cluster of $`M` is bisimilar to
the matching side (`isBisimIn`, `isBisimOut`), so $`a` fails exactly at the
worlds of $`M`, and the induction of reflection reads $`M` off the image
(`realize`).  Necessity holds for every top $`b`: the four instances
$`C = \bot, \bigcirc\bot, \lnot\bigcirc\bot, \lnot\lnot\bigcirc\bot` of
$`b \nvdash C[\bot := a]`.  PROVED.

{stmt}`Endpoints.NecCells`

{leanStmt Endpoints.necCells}

{leanDef Endpoints.NecCells}

So $`\bigcirc a \vdash a` excludes a copy for every top (`NecBox`, `necBox`; the case
$`\bigcirc a \dashv\vdash a`, $`b = \top` is `box_fixed_not_injective`), and
so does $`b \vdash T^{n}(a)` for any $`n`, where $`T^{n}(a) = \sigma^{n}(\bot)[\bot := a]` (`NecPow`, `necPow`).  The base cells, one designed
countermodel or derivation each (`BaseNo`, `BaseYes`):

:::f0table (widths := "0.2 0.38 0.38")
* * Base $`a`
  * Copy of $`F_0` in $`[a, \top]`
  * Declarations
* * $`t_1`, $`t_4`, $`t_6`, $`\bigcirc t_3`
  * no: $`\vdash \bigcirc a \twoheadrightarrow a`
  * `baseNo_e`, `baseNo_t4`, `baseNo_t6`, `baseNo_c1`
* * $`t_2`
  * no: $`\vdash (\bigcirc a \twoheadrightarrow a) \twoheadrightarrow a`
  * `baseNo_ne`
* * $`t_3`, $`t_5`, $`\sigma^{2}\bot`, $`a_K = t_6 \land g_1`
  * yes, and PLL in $`[a, \top]`
  * `baseYes_t3`, `baseYes_t5`, `baseYes_s2`, `baseYes_aK`; `selfStep_t5`, `selfStep_s2`, `selfStep_aK`
:::

Every $`\sigma^{n}(\bot)`, $`n \ge 1`, is a base, by `sigN_faithful`; $`t_6`
is not, as $`\bigcirc t_6 \vdash t_6`, but it is a top.

# Tops over t3

Which tops $`b` admit a copy of $`F_0` in $`[t_3, b]`?  The model of
reflection adds two top worlds, $`M \mapsto \widehat{M}`; the variable-free
formulas true at every world of every $`\widehat{M}` are exactly those above
$`t_6`.  So $`t_6` is the least top that this construction allows.  PROVED.

{stmt}`Endpoints.ExtTops`

{leanStmt Endpoints.extTops}

{leanDef Endpoints.ExtTops}

Another construction, a top world outside $`S` above every world and one in
$`S` above the worlds that see a world with no world of $`S` above it
(`MinR`), gives a second top, $`b' = g_1 \twoheadrightarrow t_5 = (\bigcirc t_3 \twoheadrightarrow t_3) \twoheadrightarrow t_5`, incomparable
with $`t_6`; with it even PLL embeds by the A-translation.  PROVED.

{stmt}`Endpoints.TopT3Alt`

{leanStmt Endpoints.topT3Alt}

{leanDef Endpoints.TopT3Alt}

The meet $`t_6 \land b'` is not a top: it proves $`\sigma(\lnot\lnot\bigcirc\bot) = g_1 \twoheadrightarrow t_3` (`meet_sig_nne`), and $`\nvdash \lnot\lnot\bigcirc\bot` (`MeetNotTop`, `meetNotTop`).  So the tops over $`t_3` are not closed
under $`\land` (`TopsT3NotMeet`, `topsT3NotMeet`) and have no least element.  PROVED.

{stmt}`Endpoints.NoLeastTopT3`

{leanStmt Endpoints.noLeastTopT3}

{leanDef Endpoints.NoLeastTopT3}

Over the base $`t_5` the top $`t_5 \lor t_6` serves for PLL, and its iterates
$`\alpha^{d}` give a strictly nested tower of copies of PLL
(`selfStep_t5_t56`, `tower_t5`, in the form `SelfTowerAt` of Section 10).
PROVED.

# The shells

Write $`L_n = \sigma^{n}(F_0) \setminus \sigma^{n+1}(F_0)` for the $`n`-th
shell of the nested copies.  Then $`\sigma` maps $`L_n` one-to-one onto
$`L_{n+1}`.  PROVED.

{stmt}`InsideOut.Stmt.ShellShift`

{leanStmt InsideOut.shell_shift}

{leanDef InsideOut.Stmt.ShellShift}

Only $`\top` lies in every copy: $`\sigma^{\omega}(F_0) = \bigcap_n \sigma^{n}(F_0) = \{\top\}`.  In a finite subframe countermodel the truth sets
of $`\sigma^{n}(\bot)` stabilise at some set $`U`, and
$`\sigma^{n+1}(\bot) = \bigcirc\sigma^{n}(\bot) \lor (\bigcirc\sigma^{n}(\bot) \twoheadrightarrow \sigma^{n}(\bot))` forces $`U` to be every world
(`bot_everywhere`, `cm_eventually`).  PROVED.  So $`F_0 \setminus \{\top\}` is
the disjoint union of the shells (pen, from the definitions).

{stmt}`InsideOut.Stmt.LimEqTop`

{leanStmt InsideOut.lim_eq_top}

{leanDef InsideOut.Stmt.LimEqTop}

By the same argument every orbit $`\sigma^{n}(a)` leaves the downset of every
$`x \ne \top`.  PROVED.

{stmt}`InsideOut.Stmt.OrbitOrderLimit`

{leanStmt InsideOut.orbit_order_limit}

{leanDef InsideOut.Stmt.OrbitOrderLimit}

# Supporting declarations

{lemmaTable Sig.aTr Sig.subBot Sig.sig Sig.sigN Sig.aTr_top Sig.subBot_deriv Sig.subBot_top Sig.cell_corr Sig.sig_reflects Sig.sig_reflects_ctx Sig.sigN_reflects Sig.sigN_bot_le Sig.sigN_bot_strict Sig.sig_t3 Sig.box_fixed_not_injective SubTab.complete Sig.top_sig Sig.orig_sig SigOnto.sig_t2 SigOnto.t3_lt_t5_lt_g1 NotIso.disjoint_pair_has_negOBot NotIso.two_disjoint_pairs_above_t3 NotIso.Disj NotIso.Core NotIso.HasCore NotIso.hasCore_of_iso NotIso.rnclass_core NotIso.ici_no_core MovingTop.relC MovingTop.CopyF0In MovingTop.TopAvoid Interval.FreeInPLL MovingTop.t3_t6 MovingTop.nd_t6 MovingTop.SigAvoidT6 MovingTop.sigAvoidT6 MovingTop.t6_ext MovingTop.t5_sig2_imp MovingTop.nd_t3 MovingTop.CopyT3T5 MovingTop.not_copyT3T5 MovingTop.tauN MovingTop.W2 MovingTop.w2 MovingTop.StrictNestOf MovingTop.strictNestOf Endpoints.CopyStep Endpoints.selfGen Endpoints.tauS Endpoints.SelfStep Endpoints.NecBox Endpoints.necBox Endpoints.Tpow Endpoints.NecPow Endpoints.necPow Endpoints.BaseNo Endpoints.BaseYes Endpoints.baseNo_e Endpoints.baseNo_ne Endpoints.baseNo_t4 Endpoints.baseNo_t6 Endpoints.baseNo_c1 Endpoints.baseYes_t3 Endpoints.baseYes_t5 Endpoints.baseYes_s2 Endpoints.g1 Endpoints.aK Endpoints.baseYes_aK Endpoints.selfStep_t5 Endpoints.selfStep_s2 Endpoints.selfStep_aK Endpoints.ExtTop Endpoints.bP Endpoints.t3_bP Endpoints.nd_bP_t6 Endpoints.nd_t6_bP Endpoints.meet_sig_nne Endpoints.MeetNotTop Endpoints.meetNotTop Endpoints.TopsT3NotMeet Endpoints.topsT3NotMeet Endpoints.tauSN Endpoints.SelfTowerAt Endpoints.selfStep_t5_t56 Endpoints.tower_t5 InsideOut.inSig InsideOut.inLim InsideOut.shell}

Pins: each row's pin is computed when the document is built.  The modules
bound them by `#axioms_within`: every declaration of `wip/f0SelfSim.lean`,
`wip/f0SigOnto.lean`, `wip/f0NotIso.lean`, `wip/f0MovingTop.lean` and
`wip/f0Endpoints.lean` here within \[pext,Q\], confirmed by `#print axioms`
(`t3_filter_not_iso` included; `sig_t3` holds by `rfl` and uses no axioms),
and the F0 part of `wip/f0InsideOut.lean` within \[pext,Q\];
`SubTab.complete` and subframe soundness are pinned to \[pext,Q\] in the
library.
