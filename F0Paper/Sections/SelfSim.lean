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

#doc (Manual) "Self-similarity" =>

Substituting $`t_3 = \bigcirc\bot \lor \lnot\bigcirc\bot` for $`\bot` maps
$`F_0` into itself:

$$`\sigma(\varphi) = \varphi[\bot := \bigcirc\bot \lor \lnot\bigcirc\bot].`

On variable-free formulas $`\sigma` is Friedman's A-translation
{pcite}`Friedman1978` with $`A = t_3`, restricted to variable-free formulas.
This section proves that $`\sigma` is an order embedding of $`F_0` into the
interval $`[t_3, \top]`, so that its iterates give an infinite descending
sequence of nested copies of $`F_0` inside $`F_0`, and that the chain of
Section 9 is the image under $`\sigma` of the Rieger–Nishimura ladder.  The
results are in `wip/f0SelfSim.lean`, and none of them uses `Classical.choice`.

# The translations

For a formula $`a`, the A-translation $`\varphi^{a}` and the substitution
$`\varphi[\bot := a]` are

$$`p^{a} = p \lor a, \qquad \bot^{a} = a, \qquad (\bigcirc A)^{a} = \bigcirc A^{a},`

$$`(A \circ B)^{a} = A^{a} \circ B^{a} \quad \text{for } \circ \in \{\land, \lor, \twoheadrightarrow\},`

and $`\varphi[\bot := a]` is the same with the atoms left fixed.  On
variable-free formulas the two coincide (`subBot_eq_aTr`).  The iterates are
$`\sigma^{0}(\varphi) = \varphi` and
$`\sigma^{n+1}(\varphi) = \sigma^{n}(\sigma(\varphi))`.

{stmt}`Sig.aTr`

{docstring Sig.aTr +allowMissing}

{srcLink}`Sig.aTr`

{stmt}`Sig.subBot`

{docstring Sig.subBot +allowMissing}

{srcLink}`Sig.subBot`

{stmt}`Sig.sig`

{docstring Sig.sig +allowMissing}

{srcLink}`Sig.sig`

{stmt}`Sig.sigN`

{docstring Sig.sigN +allowMissing}

{srcLink}`Sig.sigN`

# Preservation

Friedman's lemma holds for PLL: the A-translation preserves derivations, and
$`a` entails every $`\varphi^{a}`.  PROVED, for every formula and every $`a`,
closed or not; the modal rules translate to themselves.

{stmt}`Sig.aTr_deriv`

{docstring Sig.aTr_deriv +allowMissing}

{srcLink}`Sig.aTr_deriv`

{stmt}`Sig.aTr_top`

{docstring Sig.aTr_top +allowMissing}

{srcLink}`Sig.aTr_top`

For variable-free formulas, therefore, $`\bot \mapsto a` preserves derivability
and lands above $`a`.  PROVED.

{stmt}`Sig.subBot_deriv`

{docstring Sig.subBot_deriv +allowMissing}

{srcLink}`Sig.subBot_deriv`

{stmt}`Sig.subBot_top`

{docstring Sig.subBot_top +allowMissing}

{srcLink}`Sig.subBot_top`

The atom clause $`p \mapsto p \lor a` is needed: $`a \vdash \varphi[\bot := a]`
fails for formulas with atoms, since $`\bot \vdash p` but $`t_3 \nvdash p`.
REFUTED, by a countermodel of two worlds from the subframe tableau, checked by
the kernel.

{stmt}`Sig.cell_corr`

{docstring Sig.cell_corr +allowMissing}

{srcLink}`Sig.cell_corr`

# Reflection

The converse holds for every formula, with no hypothesis of variable-freeness:

$$`\vdash \sigma(\chi) \Longrightarrow\ \vdash \chi, \qquad \sigma(\varphi) \vdash \sigma(\psi) \Longrightarrow \varphi \vdash \psi.`

PROVED.  Before the proof was built, the statement was tested on five designed
cells: $`\nvdash \sigma(\chi)` for
$`\chi \in \{\bigcirc\bot, t_3, t_5, g_1, \bigcirc t_3 \lor g_1\}`, each by a
countermodel from the subframe tableau checked by the kernel (`cellS_e`,
`cellS_t3`, `cellS_t5`, `cellS_g1`, `cellS_c1g1`).

{stmt}`Sig.sig_reflects`

{docstring Sig.sig_reflects +allowMissing}

{srcLink}`Sig.sig_reflects`

{stmt}`Sig.sig_reflects_ctx`

{docstring Sig.sig_reflects_ctx +allowMissing}

{srcLink}`Sig.sig_reflects_ctx`

_The proof._  It runs in subframe models: an intuitionistic Kripke model
$`(W, \le, V)` with a set $`S \subseteq W`, in which $`\bigcirc A` holds at
$`x` when $`A` holds at every $`y \ge x` with $`y \in S`; there are no
fallible worlds.  PLL is sound and complete for them
(`LaxLogic/PLL/Semantics/Subframe.lean`), and the subframe tableau of the
library decides PLL without `Classical.choice`: every formula has a closed
tableau, accepted by the checker `yes`, or a finite subframe countermodel,
accepted by the checker `no`.

{stmt}`SubTab.complete`

{docstring SubTab.complete +allowMissing}

{srcLink}`SubTab.complete`

If $`\chi` has a closed tableau, $`\vdash \chi`.  Otherwise let
$`M, r \nVdash \chi` be the countermodel, and extend $`M` to $`\widehat{M}` by
two maximal worlds above every old world: $`n_T \in S`, so that $`\bigcirc\bot`
fails at $`n_T` and $`\lnot\bigcirc\bot` holds there, and $`e_T \notin S`, so
that $`\bigcirc\bot` holds at $`e_T`; every atom is true at both.  Then
$`t_3 = \sigma(\bot)` fails at every old world and holds at both tops; every
$`\sigma(\psi)` holds at both tops, which play the part that fallible worlds
play in constraint models; and at the old worlds $`\sigma(\psi)` holds exactly
where $`\psi` holds in $`M`, by induction on $`\psi`.

{stmt}`Sig.top_sig`

{docstring Sig.top_sig +allowMissing}

{srcLink}`Sig.top_sig`

{stmt}`Sig.orig_sig`

{docstring Sig.orig_sig +allowMissing}

{srcLink}`Sig.orig_sig`

So $`\widehat{M}, r \nVdash \sigma(\chi)`, and $`\vdash \sigma(\chi)` would
contradict soundness.  The case split is on the output of the decision
procedure, not on excluded middle, and the proof is choice-free: its axioms are
`propext` and `Quot.sound`.  The countermodel $`\mathcal{U}` of Section 9 is the
instance in which $`M` is the Rieger–Nishimura ladder.

By induction on $`n`, the iterates reflect derivability too, and $`\sigma^{n}`
is an order embedding of $`F_0` into itself.  PROVED.

{stmt}`Sig.sigN_reflects`

{docstring Sig.sigN_reflects +allowMissing}

{srcLink}`Sig.sigN_reflects`

{stmt}`Sig.sigN_faithful`

{docstring Sig.sigN_faithful +allowMissing}

{srcLink}`Sig.sigN_faithful`

# Nested copies

The copy $`\sigma^{n}(F_0)` lies in $`[\sigma^{n}(\bot), \top]`; the bases
$`\sigma^{n}(\bot)` are strictly increasing; and $`\sigma^{n}(\bot)` is not in
$`\sigma^{n+1}(F_0)`.  As $`\sigma^{n+1}(\varphi) = \sigma^{n}(\sigma(\varphi))`
by definition, the copies are nested,
$`\sigma^{n+1}(F_0) \subseteq \sigma^{n}(F_0)`, and strictly decreasing: an
infinite descending sequence of faithful copies of $`F_0` inside $`F_0`.  PROVED.
In the classification of Section 2 every interval $`[\sigma^{n}(\bot), \top]` is
therefore at level 4, through the identification
$`h_{\sigma^{n}(\bot), \top}(\varphi) \dashv\vdash \sigma^{n}(\varphi)`, which is a pen
argument.

{stmt}`Sig.sigN_bot_le`

{docstring Sig.sigN_bot_le +allowMissing}

{srcLink}`Sig.sigN_bot_le`

{stmt}`Sig.sigN_bot_strict`

{docstring Sig.sigN_bot_strict +allowMissing}

{srcLink}`Sig.sigN_bot_strict`

{stmt}`Sig.copies_strict`

{docstring Sig.copies_strict +allowMissing}

{srcLink}`Sig.copies_strict`

_A caution._  $`\sigma(F_0) \subseteq [t_3, \top]`, but $`[t_3, \top]` may contain
elements outside $`\sigma(F_0)`.  So a cover inside the copy, $`\sigma(x)` below
$`\sigma(y)` with no element of $`\sigma(F_0)` strictly between, need not be a
cover in $`F_0`.  Whether $`\sigma` is onto $`[t_3, \top]` is OPEN (Section 11).

The second base is $`\sigma^{2}(\bot) = \sigma(t_3) = c_1 \lor g_1`, with
$`c_1 = \bigcirc t_3` and $`g_1 = c_1 \twoheadrightarrow t_3`: excluded middle for
$`c_1` over $`t_3`.  It is one of the classes of the frontier (the 22 classes of
$`F_0` catalogued in the project as of 2026-10-22), where it carries that name.
The identity holds by definition.

{stmt}`Sig.sig_t3`

{docstring Sig.sig_t3 +allowMissing}

{srcLink}`Sig.sig_t3`

# The chain below the sixth rung is the image of the ladder

On variable-free formulas $`\sigma` is the relativisation $`\mathrm{rel}` of
Section 9 (`rel_eq_sig`), and on the ladder
$`\sigma(t_n) \dashv\vdash \mathrm{rel}(r_n)`, through
$`\sigma(\bigcirc\bot) = \bigcirc t_3 \dashv\vdash \bigcirc\lnot\bigcirc\bot = u`
(`sig_e_interd_u`).  PROVED.  So the chain $`x_k` of Section 9 is, up to
$`\dashv\vdash`, the image under $`\sigma` of the odd rungs, met with $`t_6`.

{stmt}`Sig.sig_ladder`

{docstring Sig.sig_ladder +allowMissing}

{srcLink}`Sig.sig_ladder`

# A necessary condition on the base

Replace $`t_3` by another base $`a`.  If $`\bigcirc a \dashv\vdash a`, then
$`\bot \mapsto a` sends $`\bigcirc\bot` and $`\bot` to interderivable formulas,
while $`\bigcirc\bot \nvdash \bot`; so the map is not one-to-one on $`F_0`.
PROVED.  Hence $`\bigcirc a \ne a` in $`F_0` is necessary for a faithful copy;
for instance $`a = \bigcirc\bot` fails, as $`\bigcirc\bigcirc\bot \dashv\vdash \bigcirc\bot`
(`control_oBot`).  Which bases give a faithful copy is OPEN (Section 11).

{stmt}`Sig.box_fixed_not_injective`

{docstring Sig.box_fixed_not_injective +allowMissing}

{srcLink}`Sig.box_fixed_not_injective`

# Axioms

As recorded in the file (`#axioms_within`), and confirmed by `#print axioms` on
the build: `propext`, `Quot.sound` for `aTr_top`, `aTr_deriv`, `subBot_eq_aTr`,
`subBot_deriv`, `subBot_top`, `rel_eq_sig`, `sig_e_interd_u`, `sig_ladder`,
`box_fixed_not_injective`, `control_oBot`, the six cells, `orig_sig`,
`sig_reflects`, `sig_reflects_ctx`, `sigN_reflects`, `sigN_faithful`,
`sigN_bot_le`, `sigN_bot_strict` and `copies_strict`.  `sig_t3` holds by
definition and depends on no axioms (no pin recorded).  In the library files:
`SubTab.complete` is pinned to `propext`, `Quot.sound`, and the soundness of
PLL for subframe models (`SubframeModel.CF.soundness`) to the same, with
`#print axioms` reporting `propext` alone.  No `Classical.choice` anywhere in
the section.
