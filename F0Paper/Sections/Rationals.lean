import Verso
import VersoManual
import CLPPaper.Src
import CLPPaper.Cite
import F0Paper.Math

open Verso.Genre
open Verso.Genre.Manual
open CLPPaper CLPPaper.Cite F0Paper.Math
open PLLND PLLND.SemUI PLLND.F0 PLLND.F0.Mink PLLND.RNEmbed
open PLLND.LaxInfinite (atomFree)

#doc (Manual) "The rationals" =>

This section builds an order embedding of the dyadic rationals in $`[0, 1]`
into $`F_0`, from lattice polynomials in the odd gaps, and composes it with an
explicit order-isomorphism from $`\mathbb{Q}` onto the dyadic rationals in
$`(0, 1)`, built from Minkowski's question-mark function, to obtain an order
embedding of $`\mathbb{Q}`.  Everything in that route is choice-free.  A second
route, through Cantor's theorem, carries `Classical.choice` and is given at the
end.  The results are in `wip/f0Dyadic.lean`, `wip/f0Minkowski.lean` and
`wip/f0Rat.lean`.

# The free distributive lattice argument

In a free distributive lattice, let $`a < b` and let $`x` be a generator that
occurs in neither.  Then

$$`a \;<\; a \lor (b \land x) \;<\; b.`

The two inequalities $`\le` hold in any lattice, since $`a \le b`.  For
strictness, recall that in a free distributive lattice $`u \le v` holds exactly
when every assignment of $`0` and $`1` to the generators that sends $`u` to $`1`
sends $`v` to $`1` {pcite}`Gratzer2011`.  Since $`b \not\le a` there is an
assignment $`\sigma` with $`\sigma(b) = 1` and $`\sigma(a) = 0`; it does not
mention $`x`.  Setting $`x` to $`1` sends $`a \lor (b \land x)` to $`1` and $`a`
to $`0`; setting $`x` to $`0` sends $`b` to $`1` and $`a \lor (b \land x)` to $`0`.
Starting from $`\bot < \top` and inserting a fresh generator between each pair
of neighbours, level by level, gives a chain of the order type of the dyadic
rationals in $`[0, 1]`.

The lattice-theoretic restatement of Section 4 (that the odd gaps generate a
free distributive lattice) is not mechanised, so the argument is carried out
on lattice polynomials directly: derivability between their interpretations
is proved by lattice reasoning in PLL, and underivability by assignments,
through `indep`.

# Lattice polynomials

Lattice polynomials have variables in $`\mathbb{N}`, constants $`\bot` and
$`\top`, and $`\land`, $`\lor`.  The interpretation $`[\![ p ]\!]` of a polynomial
reads the variable $`n` as the odd gap $`g_{2n+1}`.

{stmt}`LPoly`

{docstring LPoly +allowMissing}

{srcLink}`LPoly`

{stmt}`LPoly.den`

{docstring LPoly.den +allowMissing}

{srcLink}`LPoly.den`

A polynomial true under an assignment $`\sigma` is entailed by the conjunction
of the gaps of its true variables, and a polynomial false under $`\sigma`
entails the disjunction of the gaps of its false variables.  Both PROVED, by
induction on the polynomial.

{stmt}`true_entails`

{docstring true_entails +allowMissing}

{srcLink}`true_entails`

{stmt}`false_entails`

{docstring false_entails +allowMissing}

{srcLink}`false_entails`

Together with independence they separate: if one assignment makes $`p` true
and $`q` false, then $`[\![ p ]\!] \nvdash [\![ q ]\!]`.  For a derivation would
give $`\bigwedge_{i \in S} g_{2i+1} \vdash \bigvee_{j \in T} g_{2j+1}`, with $`S`
the true and $`T` the false variables of $`p` and $`q`, which are disjoint.
PROVED.

{stmt}`separate`

{docstring separate +allowMissing}

{srcLink}`separate`

# The dyadic construction

The dyadic rational $`m / 2^n` gets the polynomial $`F_n(m)`:

$$`F_0(0) = \bot,\qquad F_0(1) = \top,\qquad F_{n+1}(2k) = F_n(k),\qquad F_{n+1}(2k+1) = F_n(k) \lor \bigl(F_n(k+1) \land x_{2^{n+1} + 2k + 1}\bigr).`

The variable $`2^{n+1} + 2k + 1` is used for the dyadic $`(2k+1)/2^{n+1}` and
nowhere else: $`(n, m) \mapsto 2^n + m` is injective on the pairs with
$`m < 2^n`, and is decoded by the binary logarithm.  This is $`a \lor (b \land x)` above, with $`a` and $`b` the
two neighbours $`k/2^n` and $`(k+1)/2^n`.

{stmt}`F0.F`

{docstring F0.F +allowMissing}

{srcLink}`F0.F`

Monotonicity is lattice reasoning on the recursion.  PROVED.

{stmt}`F_mono`

{docstring F_mono +allowMissing}

{srcLink}`F_mono`

Strictness uses the threshold assignment $`\theta_{C,N}`, which makes the
variable of $`m/2^n` true exactly when $`m / 2^n \ge C / 2^N`.  By induction on
the level, $`F_n(m)` is then true exactly when $`m / 2^n \ge C / 2^N`.  PROVED.

{stmt}`thr`

{docstring thr +allowMissing}

{srcLink}`thr`

{stmt}`F_eval`

{docstring F_eval +allowMissing}

{srcLink}`F_eval`

For $`m < m' \le 2^N` the threshold $`m' / 2^N` makes $`F_N(m')` true and
$`F_N(m)` false, and `separate` applies.  PROVED.

{stmt}`F_sep`

{docstring F_sep +allowMissing}

{srcLink}`F_sep`

# The dyadic embedding

A dyadic rational in $`[0, 1]` is a pair $`(m, n)` with $`m \le 2^n`, read as
$`m / 2^n`, ordered by the value; $`f(d)` is the interpretation of its
polynomial.

{stmt}`Dy`

{docstring Dy +allowMissing}

{srcLink}`Dy`

{stmt}`Dy.lt`

{docstring Dy.lt +allowMissing}

{srcLink}`Dy.lt`

{stmt}`Dy.formula`

{docstring Dy.formula +allowMissing}

{srcLink}`Dy.formula`

Two dyadics are compared at a common level, where a dyadic has the same
polynomial at every finer level; monotonicity and strictness then give the
embedding.  PROVED: $`f` is an order embedding of the dyadic rationals in
$`[0, 1]` into $`F_0`, with $`f(0) = \bot` and $`f(1) = \top`, and every $`f(d)`
is variable-free.

{stmt}`dyadic_embedding`

{docstring dyadic_embedding +allowMissing}

{srcLink}`dyadic_embedding`

{stmt}`formula_zero`

{docstring formula_zero +allowMissing}

{srcLink}`formula_zero`

{stmt}`formula_one`

{docstring formula_one +allowMissing}

{srcLink}`formula_one`

{stmt}`dyadic_vf`

{docstring dyadic_vf +allowMissing}

{srcLink}`dyadic_vf`

# An explicit order embedding of the rationals

Minkowski's question-mark function $`\mathord{?}` {pcite}`Minkowski1904` is a
strictly increasing bijection from $`\mathbb{Q} \cap [0, 1]` onto the dyadic
rationals in $`[0, 1]`.  It sends the Stern–Brocot tree of the rationals in
$`(0, 1)`, in which each node is the mediant of its two neighbours, to the tree
of the dyadic rationals in $`(0, 1)`, in which each node is the midpoint, path
for path.  On a pair $`a/b` with $`0 < a < b`, the test at the root and the two
subtree maps give the recursion

$$`\mathord{?}\Bigl(\frac{a}{b}\Bigr) = \begin{cases} 1/2 & \text{if } 2a = b,\\[2pt] \tfrac{1}{2}\, \mathord{?}\bigl(\tfrac{a}{b-a}\bigr) & \text{if } 2a < b,\\[2pt] \tfrac{1}{2}\bigl(1 + \mathord{?}\bigl(\tfrac{2a-b}{a}\bigr)\bigr) & \text{if } 2a > b. \end{cases}`

Each step lowers $`b`, so $`b` steps of fuel suffice, and the recursion is
invariant under scaling $`a/b \mapsto ka/kb`, so lowest terms are never needed.
On $`\mathbb{Q}`, $`\mathord{?}` is extended by $`0` below $`0` and $`1` above $`1`.

{stmt}`qmF`

{docstring qmF +allowMissing}

{srcLink}`qmF`

{stmt}`mink`

{docstring mink +allowMissing}

{srcLink}`mink`

The definition is checked against known values, each cell closed by `rfl`: $`\mathord{?}(1/3) = 1/4`, $`\mathord{?}(2/3) = 3/4` and
$`\mathord{?}(2/5) = 3/8` (`cell_third`, `cell_two_thirds`, `cell_two_fifths`),
and two values computed independently from the continued-fraction formula
$`\mathord{?}([0; a_1, a_2, \ldots]) = 2 \sum_{k \ge 1} (-1)^{k+1} 2^{-(a_1 + \cdots + a_k)}`:
$`\mathord{?}(5/8) = 11/16` and $`\mathord{?}(3/7) = 7/16`.  In the displays a
dyadic is printed as $`m/2^{n}`.  PROVED.

{stmt}`cell_third`

{docstring cell_third +allowMissing}

{srcLink}`cell_third`

{stmt}`cell_five_eighths`

{docstring cell_five_eighths +allowMissing}

{srcLink}`cell_five_eighths`

{stmt}`cell_three_sevenths`

{docstring cell_three_sevenths +allowMissing}

{srcLink}`cell_three_sevenths`

On $`[0, 1]`, $`\mathord{?}` is strictly increasing, and it is onto the dyadic
rationals in $`(0, 1)`; $`\equiv` below is equality of the values $`m/2^n`.
Both PROVED.

{stmt}`mink_lt`

{docstring mink_lt +allowMissing}

{srcLink}`mink_lt`

{stmt}`mink_onto`

{docstring mink_onto +allowMissing}

{srcLink}`mink_onto`

The map $`\sigma(x) = \bigl(1 + x/(1 + |x|)\bigr)/2` is an order-isomorphism
from $`\mathbb{Q}` onto $`\mathbb{Q} \cap (0, 1)`; it is computed on the
numerator and denominator, as a pair that is not reduced.  The composite
$`\mathit{qm} = \mathord{?} \circ \sigma` is then an explicit, computable map
from $`\mathbb{Q}` to the dyadic rationals in $`(0, 1)`.

{stmt}`sq`

{docstring sq +allowMissing}

{srcLink}`sq`

{stmt}`qm`

{docstring qm +allowMissing}

{srcLink}`qm`

{stmt}`qm_eq_mink`

{docstring qm_eq_mink +allowMissing}

{srcLink}`qm_eq_mink`

$`\mathit{qm}` is strictly increasing, injective on values, and onto the dyadic
rationals in $`(0, 1)`: an order-isomorphism from $`\mathbb{Q}` onto them.  It
preserves $`<` and nothing else; no arithmetic is carried over.  PROVED.

{stmt}`qm_lt`

{docstring qm_lt +allowMissing}

{srcLink}`qm_lt`

{stmt}`qm_inj`

{docstring qm_inj +allowMissing}

{srcLink}`qm_inj`

{stmt}`qm_onto`

{docstring qm_onto +allowMissing}

{srcLink}`qm_onto`

Composed with the dyadic embedding, it gives the order embedding of
$`\mathbb{Q}` into $`F_0`: $`f'(q) = f(\mathit{qm}(q))`.  PROVED, without
`Classical.choice`.

{stmt}`ratFormulaCF`

{docstring ratFormulaCF +allowMissing}

{srcLink}`ratFormulaCF`

{stmt}`rat_embedding_cf`

{docstring rat_embedding_cf +allowMissing}

{srcLink}`rat_embedding_cf`

{stmt}`rat_vf_cf`

{docstring rat_vf_cf +allowMissing}

{srcLink}`rat_vf_cf`

_Remark (choice in core's rationals)._  Core Lean's normalisation and division
of rationals carry `Classical.choice`, through `Classical.propDecidable`:
`Rat.normalize` proves its reducedness field through `Int.natAbs_ediv`, and
`Rat.mul`, behind `/`, through a chain of lemmas ending at `Nat.right_eq_add`.
So core's `Rat.lt_iff`, and any literal such as $`1/3` written with `/`, carry
it.  The order itself, `Rat.blt`, does not.  `wip/f0Minkowski.lean` therefore
works with the numerator, the denominator and `Rat.blt` directly: the order is
characterised from its definition (`rat_lt_iff`), and rationals are built as
structures (`rq`), never normalised.  The one declaration pinned with
`Classical.choice`, `rq_bridge`, only identifies such structures with core's
literals $`1/2`, $`1/3`, $`2/3` and $`2/5`.  Two core lemmas on `Nat`,
`Nat.mul_lt_mul_left` and `Nat.lt_of_mul_lt_mul_left`, carry choice too and are
avoided.

# A second route: Cantor's theorem

Cantor's theorem {pcite}`Cantor1895`: any two countable dense linear orders
without endpoints are order-isomorphic.  The usual proof is the back-and-forth
argument {pcite}`Rosenstein1982`, which builds the isomorphism from
enumerations of the two orders; Mathlib's `Order.iso_of_countable_dense`
{pcite}`MathlibCommunity2020` is such a proof.  The dyadic rationals strictly
between $`0` and $`1` form a countable dense linear order without endpoints, so
they are order-isomorphic to $`\mathbb{Q}`.  The isomorphism preserves $`<`
only, not the arithmetic, and it depends on the enumerations chosen.  This
route was mechanised first; it carries `Classical.choice`.

{stmt}`DyQ`

{docstring DyQ +allowMissing}

{srcLink}`DyQ`

{stmt}`ratIso`

{docstring ratIso +allowMissing}

{srcLink}`ratIso`

Composing the isomorphism with a chosen representation $`m / 2^n` of each
dyadic and with $`f` gives $`f_{\mathbb{Q}}`, an order embedding of $`\mathbb{Q}`
into $`F_0` whose values are variable-free.  PROVED.

{stmt}`ratFormula`

{docstring ratFormula +allowMissing}

{srcLink}`ratFormula`

{stmt}`rat_embedding`

{docstring rat_embedding +allowMissing}

{srcLink}`rat_embedding`

{stmt}`rat_vf`

{docstring rat_vf +allowMissing}

{srcLink}`rat_vf`

# Axioms

As recorded in the files (`#axioms_within`), and confirmed by `#print axioms`
on the build:

* within `propext`, `Quot.sound`: `true_entails`, `false_entails`,
  `separate`, `F_mono`, `F_eval`, `F_sep`, `dyadic_embedding`,
  `formula_zero`, `formula_one`, `dyadic_vf` (`#print axioms` reports
  `propext`, `Quot.sound` for the first seven and `propext` alone for the last
  three); and every declaration of `wip/f0Minkowski.lean` shown above,
  `mink_lt`, `mink_onto`, the three cells, `qm_eq_mink`, `qm_lt`, `qm_inj`,
  `qm_onto`, `rat_embedding_cf` and `rat_vf_cf`, each reported as `propext`,
  `Quot.sound`.
* `propext`, `Classical.choice`, `Quot.sound`: `rq_bridge`, which only
  identifies literals; and the Cantor route, `rat_embedding` and `rat_vf`.
  There `Classical.choice` enters twice, through Cantor's theorem (`ratIso`
  takes the isomorphism out of `Nonempty` with `Classical.choice`) and through
  the chosen representation $`m / 2^n` of each dyadic (`toDy`, by
  `Classical.choose`).
