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

#doc (Manual) "Self-similarity" =>

Substituting $`t_3` for $`\bot`,

$$`\sigma(\varphi) = \varphi[\bot := \bigcirc\bot \lor \lnot\bigcirc\bot],`

is Friedman's A-translation {pcite}`Friedman1978` with $`A = t_3`, restricted
to variable-free formulas.  It is an order embedding of $`F_0` into
$`[t_3, \top]`, and its iterates give an infinite descending sequence of nested
copies of $`F_0` inside $`F_0`.  No `Classical.choice`; `wip/f0SelfSim.lean`.

:::f0Figure "selfsim" (width := "1.0")
Left: the rungs $`t_0, \ldots, t_7` (order decided by `rungCovers`, through
`rnSub_order`) and their images under $`\sigma` inside $`[t_3, \top]`, in the same
order (`sigN_faithful`), with $`\sigma(t_0) = t_3` and
$`\sigma(t_3) = \bigcirc t_3 \lor g_1` (`sig_t3`; both decided by Lean).  Right:
the copies $`\sigma^{n}(F_0)` with their bases
$`\bot < t_3 < \sigma(t_3) < \sigma^{3}(\bot)`, each region labelled, and the
theorems behind them in the key.  Schematic: positions not to
scale; every inclusion and every line drawn is a named theorem.
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
every world of $`S` above $`x`).  Add two top worlds above $`M`: $`n_T \in S`,
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
$`h_{\sigma^{n}(\bot), \top}(\varphi) \dashv\vdash \sigma^{n}(\varphi)`).  But
$`[t_3, \top]` may contain elements outside $`\sigma(F_0)`, so a cover inside the
copy need not be a cover in $`F_0`.

{stmt}`Sig.copies_strict`

{leanStmt Sig.copies_strict}

On the rungs, $`\sigma(t_n) \dashv\vdash \mathrm{rel}(r_n)`, so the chain below the
sixth rung (Section 9) is the image of the ladder under $`\sigma`.  PROVED.

{stmt}`Sig.sig_ladder`

{leanStmt Sig.sig_ladder}

_The base._  If $`\bigcirc a \dashv\vdash a`, then $`\bot \mapsto a` identifies
$`\bigcirc\bot` with $`\bot`, so $`\bigcirc a \ne a` is necessary for a faithful
copy (`box_fixed_not_injective`; $`a = \bigcirc\bot` fails).  Which bases work is
OPEN.

# Supporting declarations

{lemmaTable Sig.aTr Sig.subBot Sig.sig Sig.sigN Sig.aTr_top Sig.subBot_deriv Sig.subBot_top Sig.cell_corr Sig.sig_reflects Sig.sig_reflects_ctx Sig.sigN_reflects Sig.sigN_bot_le Sig.sigN_bot_strict Sig.sig_t3 Sig.box_fixed_not_injective SubTab.complete Sig.top_sig Sig.orig_sig}

Pins: every declaration of `wip/f0SelfSim.lean` here within `propext`,
`Quot.sound` (`#axioms_within`, confirmed by `#print axioms`); `sig_t3` holds by
`rfl` and uses no axioms (no pin recorded); `SubTab.complete` and subframe
soundness are pinned to `propext`, `Quot.sound` in the library.
