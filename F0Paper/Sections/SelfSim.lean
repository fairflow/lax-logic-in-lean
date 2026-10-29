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

#doc (Manual) "Self-similarity" =>

Substituting $`t_3` for $`\bot`,

$$`\sigma(\varphi) = \varphi[\bot := \bigcirc\bot \lor \lnot\bigcirc\bot],`

is Friedman's A-translation {pcite}`Friedman1978` with $`A = t_3`, restricted
to variable-free formulas.  It is an order embedding of $`F_0` into
$`[t_3, \top]`, and its iterates give an infinite descending sequence of nested
copies of $`F_0` inside $`F_0`.  No `Classical.choice`; `wip/f0SelfSim.lean`.

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
without `Classical.choice` (`SubTab.complete`): $`\chi` has a closed tableau, or
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

_The base._  If $`\bigcirc a \dashv\vdash a`, then $`\bot \mapsto a` identifies
$`\bigcirc\bot` with $`\bot`, so $`\bigcirc a \ne a` is necessary for a faithful
copy (`box_fixed_not_injective`; $`a = \bigcirc\bot` fails).  Which bases work is
OPEN.

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

# Supporting declarations

{lemmaTable Sig.aTr Sig.subBot Sig.sig Sig.sigN Sig.aTr_top Sig.subBot_deriv Sig.subBot_top Sig.cell_corr Sig.sig_reflects Sig.sig_reflects_ctx Sig.sigN_reflects Sig.sigN_bot_le Sig.sigN_bot_strict Sig.sig_t3 Sig.box_fixed_not_injective SubTab.complete Sig.top_sig Sig.orig_sig SigOnto.sig_t2 SigOnto.t3_lt_t5_lt_g1 NotIso.disjoint_pair_has_negOBot NotIso.two_disjoint_pairs_above_t3 NotIso.Disj NotIso.Core NotIso.HasCore NotIso.hasCore_of_iso NotIso.rnclass_core NotIso.ici_no_core}

Pins: every declaration of `wip/f0SelfSim.lean`, `wip/f0SigOnto.lean` and
`wip/f0NotIso.lean` here within `propext`, `Quot.sound` (`#axioms_within`,
confirmed by `#print axioms`; `t3_filter_not_iso` included);
`sig_t3` holds by `rfl` and uses no axioms (no pin recorded); `SubTab.complete`
and subframe soundness are pinned to `propext`, `Quot.sound` in the library.
