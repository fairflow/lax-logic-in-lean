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

#doc (Manual) "The rationals" =>

This section builds an order embedding of the dyadic rationals in $`[0, 1]`
into $`F_0`, from lattice polynomials in the odd gaps, and composes it with an
order-isomorphism to obtain an order embedding of $`\mathbb{Q}`.  The dyadic
embedding is choice-free; the last step is not.  The results are in
`wip/f0Dyadic.lean` and `wip/f0Rat.lean`.

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

# An order embedding of the rationals

Cantor's theorem {pcite}`Cantor1895`: any two countable dense linear orders
without endpoints are order-isomorphic.  The usual proof is the back-and-forth
argument {pcite}`Rosenstein1982`, which builds the isomorphism from
enumerations of the two orders; Mathlib's `Order.iso_of_countable_dense`
{pcite}`MathlibCommunity2020` is such a proof.  The dyadic rationals strictly
between $`0` and $`1` form a countable dense linear order without endpoints, so
they are order-isomorphic to $`\mathbb{Q}`.  The isomorphism preserves $`<`
only, not the arithmetic, and it depends on the enumerations chosen.

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

_Remark (an explicit isomorphism)._  Minkowski's question-mark function
$`?` {pcite}`Minkowski1904` is a strictly increasing bijection from
$`\mathbb{Q} \cap [0, 1]` onto the dyadic rationals in $`[0, 1]`, with
$`?(1/3) = 1/4`, $`?(1/2) = 1/2` and $`?(2/3) = 3/4`.  The map
$`x \mapsto x / (1 + |x|)` is an order-isomorphism from $`\mathbb{Q}` onto
$`\mathbb{Q} \cap (-1, 1)`; followed by $`y \mapsto (1 + y)/2` and by $`?`, it
gives an explicit order-isomorphism from $`\mathbb{Q}` onto the dyadic
rationals in $`(0, 1)`.  Mechanising it would remove `Classical.choice` from
`rat_embedding`.  This is not done.

# Axioms

As recorded in the files (`#axioms_within`):

* within `propext`, `Quot.sound`: `true_entails`, `false_entails`,
  `separate`, `F_mono`, `F_eval`, `F_sep`, `dyadic_embedding`,
  `formula_zero`, `formula_one`, `dyadic_vf`.  `#print axioms` on the build
  reports `propext`, `Quot.sound` for the first seven and `propext` alone for
  the last three.
* `propext`, `Classical.choice`, `Quot.sound`: `rat_embedding`, `rat_vf`.
  `Classical.choice` enters twice, through Cantor's theorem (`ratIso` takes
  the isomorphism out of `Nonempty` with `Classical.choice`) and through the
  chosen representation $`m / 2^n` of each dyadic (`toDy`, by
  `Classical.choose`).
