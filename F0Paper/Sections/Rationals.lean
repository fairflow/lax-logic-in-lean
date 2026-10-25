import Verso
import VersoManual
import CLPPaper.Src
import CLPPaper.Cite
import F0Paper.Math
import F0Paper.Blocks

open Verso.Genre
open Verso.Genre.Manual
open CLPPaper CLPPaper.Cite PaperKit.Math PaperKit.Blocks
open PLLND PLLND.SemUI PLLND.F0 PLLND.F0.Mink PLLND.RNEmbed
open PLLND.LaxInfinite (atomFree)

#doc (Manual) "The rationals" =>

The dyadic rationals in $`[0, 1]` order-embed in $`F_0` through lattice
polynomials in the odd gaps, and $`\mathbb{Q}` follows through an explicit
order-isomorphism built from Minkowski's question-mark function, all without
`Classical.choice`; a second route through Cantor's theorem carries it.  Files:
`wip/f0Dyadic.lean`, `wip/f0Minkowski.lean`, `wip/f0Rat.lean`.

# The dyadic thread

In a free distributive lattice, if $`a < b` and the generator $`x` occurs in
neither, then $`a < a \lor (b \land x) < b`, as an assignment separating $`b`
from $`a` extends by $`x = 1` or $`x = 0` {pcite}`Gratzer2011`.  Inserting a
fresh odd gap between neighbours, level by level, gives the polynomials

$$`F_0(0) = \bot,\qquad F_0(1) = \top,\qquad F_{n+1}(2k) = F_n(k),\qquad F_{n+1}(2k+1) = F_n(k) \lor \bigl(F_n(k+1) \land x_{2^{n+1} + 2k + 1}\bigr),`

the variable $`x_v` read as the gap $`g_{2v+1}`.  Strictness comes from
`indep` through threshold assignments.  Writing $`f(m/2^n)` for the
interpretation of $`F_n(m)`: $`f` is an order embedding of the dyadic rationals
in $`[0, 1]` into $`F_0`, with $`f(0) = \bot`, $`f(1) = \top`, every value
variable-free.  PROVED.

{stmt}`dyadic_embedding`

{leanStmt dyadic_embedding}

# An explicit order embedding of the rationals

Minkowski's $`\mathord{?}` {pcite}`Minkowski1904` maps the Stern–Brocot tree of
$`\mathbb{Q} \cap (0, 1)` onto the tree of dyadic midpoints, path for path:

$$`\mathord{?}\Bigl(\frac{a}{b}\Bigr) = \begin{cases} 1/2 & \text{if } 2a = b,\\[2pt] \tfrac{1}{2}\, \mathord{?}\bigl(\tfrac{a}{b-a}\bigr) & \text{if } 2a < b,\\[2pt] \tfrac{1}{2}\bigl(1 + \mathord{?}\bigl(\tfrac{2a-b}{a}\bigr)\bigr) & \text{if } 2a > b, \end{cases}`

with fuel $`b`, on pairs never reduced.  Composed with
$`\sigma(x) = \bigl(1 + x/(1 + |x|)\bigr)/2`, an order-isomorphism of
$`\mathbb{Q}` onto $`\mathbb{Q} \cap (0, 1)`, it gives
$`\mathit{qm} = \mathord{?} \circ \sigma`, an explicit order-isomorphism from
$`\mathbb{Q}` onto the dyadic rationals in $`(0, 1)` (checked against values
from the continued-fraction formula, e.g. $`\mathord{?}(3/7) = 7/16`).  It
preserves $`<` and nothing else.  PROVED.

{stmt}`qm_lt`

{leanStmt qm_lt}

{stmt}`qm_onto`

{leanStmt qm_onto}

So $`f'(q) = f(\mathit{qm}(q))` is a thread in $`(\bot, \top)`: an order embedding
of $`\mathbb{Q}` into $`F_0`.  PROVED, without `Classical.choice`.

{stmt}`rat_embedding_cf`

{leanStmt rat_embedding_cf}

_Choice in core's rationals._  Core Lean's `Rat.normalize` and `Rat.mul`
(behind `/`) carry `Classical.choice` through `Classical.propDecidable`; the
order `Rat.blt` does not.  `wip/f0Minkowski.lean` works with numerators,
denominators and `Rat.blt` only; the one declaration with choice, `rq_bridge`,
identifies its structures with core's literals $`1/2`, $`1/3`, $`2/3`, $`2/5`.

# A second route: Cantor's theorem

Any two countable dense linear orders without endpoints are order-isomorphic
{pcite}`Cantor1895`, by the back-and-forth argument {pcite}`Rosenstein1982`
(Mathlib's `Order.iso_of_countable_dense`, {pcite}`MathlibCommunity2020`).  The
isomorphism with the dyadics in $`(0, 1)` preserves $`<` only and depends on the
enumerations.  It gives an order embedding $`f_{\mathbb{Q}}` too.  PROVED, with
`Classical.choice`.

{stmt}`rat_embedding`

{leanStmt rat_embedding}

# Supporting declarations

{lemmaTable LPoly LPoly.den true_entails false_entails separate F0.F F_mono thr F_eval F_sep Dy Dy.lt Dy.formula formula_zero formula_one dyadic_vf qmF mink cell_third cell_five_eighths cell_three_sevenths mink_lt mink_onto Mink.sq qm qm_eq_mink qm_inj ratFormulaCF rat_vf_cf DyQ ratIso ratFormula rat_vf}

Pins, as recorded (`#axioms_within`) and confirmed by `#print axioms`:
`propext`, `Quot.sound` (or `propext` alone) for the dyadic construction and
for every declaration of `wip/f0Minkowski.lean` used here; `propext`,
`Classical.choice`, `Quot.sound` for `rq_bridge` and for the Cantor route
(`ratIso` takes the isomorphism out of `Nonempty`; `toDy` chooses a
representation $`m / 2^n` by `Classical.choose`).
