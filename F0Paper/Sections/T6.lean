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

#doc (Manual) "Below the sixth rung" =>

Section 3 found the downsets $`{\downarrow}t_n` finite for $`n \le 5`, as
explicit tables.  This section shows that $`{\downarrow}t_6` is infinite, and
with it $`{\downarrow}t_n` for $`n = 6, 7` and every $`n \ge 9`.  The conjecture
that $`{\downarrow}t_n` is finite for every $`n` is therefore REFUTED for
$`n = 6, 7` and every $`n \ge 9`; it holds for $`n \le 5` (Section 3); for
$`n = 8` it is OPEN.  The results are in `wip/f0T6.lean`, and none of them uses
`Classical.choice`.

For a variable-free $`a`, $`{\downarrow}a` is the set of classes below $`a`; it
is a PLL algebra under $`\land`, $`\lor`, $`(x \twoheadrightarrow y) \land a` and
$`\bigcirc x \land a`, the quotient of $`F_0` by the principal filter of $`a`.

# Double negation for the modal bottom

The sixth rung is $`t_6 = t_5 \twoheadrightarrow t_3`, and it is double-negation
elimination for $`\bigcirc\bot`:

$$`t_6 \dashv\vdash \lnot\lnot\bigcirc\bot \twoheadrightarrow \bigcirc\bot`

PROVED, by a closed tableau checked by the kernel.  So $`{\downarrow}t_6` is
variable-free PLL in which $`\bigcirc\bot` is regular.

{stmt}`T6.t6F`

{docstring T6.t6F +allowMissing}

{srcLink}`T6.t6F`

{stmt}`T6.t6_regular`

{docstring T6.t6_regular +allowMissing}

{srcLink}`T6.t6_regular`

The contrast is with the fifth rung.  Up to $`\dashv\vdash`,
$`t_4 = t_3 \twoheadrightarrow \bigcirc\bot` is $`\lnot\lnot\bigcirc\bot` and
$`t_5 = t_3 \lor t_4` is $`\lnot\bigcirc\bot \lor \lnot\lnot\bigcirc\bot`, weak
excluded middle for $`\bigcirc\bot` (elementary intuitionistic steps, not stated
separately in the library).  Weak excluded middle for $`\bigcirc\bot` leaves a
downset of six elements, $`{\downarrow}t_5 = \{t_0, \ldots, t_5\}` (Section 3);
double-negation elimination for $`\bigcirc\bot` leaves an infinite one.

# The modality-free instance first

In the $`\bigcirc`-free instance the Rieger–Nishimura algebra of one variable
$`p`, divided by $`\lnot\lnot p = p`, has five elements, $`\bot`, $`p`,
$`\lnot p`, $`p \lor \lnot p` and $`\top`; equivalently
$`{\downarrow}r_6 = \{r_0, r_1, r_2, r_3, r_6\}`.  This is textbook, and it is
not mechanised here.  So an infinite family below $`t_6` must use $`\bigcirc`
beyond the substitution $`p := \bigcirc\bot`.

# The mechanism

The formula

$$`u = \bigcirc\lnot\bigcirc\bot = \bigcirc t_2`

lies above $`t_3`: $`\bigcirc\bot \vdash \bigcirc\lnot\bigcirc\bot` by
monotonicity of $`\bigcirc`, and $`\lnot\bigcirc\bot \vdash \bigcirc\lnot\bigcirc\bot`
by the unit.  PROVED.

{stmt}`T6.uF`

{docstring T6.uF +allowMissing}

{srcLink}`T6.uF`

{stmt}`T6.t3_le_u`

{docstring T6.t3_le_u +allowMissing}

{srcLink}`T6.t3_le_u`

So $`u` lives in the interval $`[t_3, \top]`, a Heyting algebra with bottom
$`t_3`, the same $`\land`, $`\lor`, $`\twoheadrightarrow`, and the relative
negation $`x \mapsto x \twoheadrightarrow t_3`.  The relativisation
$`\mathrm{rel}` reads $`p` as $`u`, and $`\bot` and every other atom as $`t_3`;
on the rungs it gives

$$`\mathrm{rel}(r_1) = u, \qquad \mathrm{rel}(r_2) = u \twoheadrightarrow t_3,`

$$`\mathrm{rel}(r_{2k+3}) = \mathrm{rel}(r_{2k+1}) \lor \mathrm{rel}(r_{2k+2}), \qquad \mathrm{rel}(r_{2k+4}) = \mathrm{rel}(r_{2k+3}) \twoheadrightarrow \mathrm{rel}(r_{2k+1}).`

So $`u` generates a Rieger–Nishimura ladder over $`t_3`, relativised.  Several
classes that an untrusted generator found below $`t_6` are, up to
$`\dashv\vdash`, such rungs met with $`t_6`; two of these identifications are
designed cells checked by the kernel (`cell_m6`, `cell_m9`).  The chain of the
theorem takes the odd rungs:

{stmt}`T6.rel`

{docstring T6.rel +allowMissing}

{srcLink}`T6.rel`

{stmt}`T6.xc`

{docstring T6.xc +allowMissing}

{srcLink}`T6.xc`

# The downset is infinite

The $`x_k` form an infinite strictly increasing chain of variable-free formulas
below $`t_6`, so $`{\downarrow}t_6` is infinite.  PROVED.

{stmt}`T6.t6_chain`

{docstring T6.t6_chain +allowMissing}

{srcLink}`T6.t6_chain`

{stmt}`T6.t6_downset_infinite`

{docstring T6.t6_downset_infinite +allowMissing}

{srcLink}`T6.t6_downset_infinite`

The countermodel $`\mathcal{U}` (`cmU`) is the Rieger–Nishimura ladder under
three top worlds: $`n_E`, where $`\lnot\bigcirc\bot` holds; $`o_E`, where
$`\bigcirc\bot` holds, with a modal edge to the fallible world $`f`; and $`f`
itself.  The only other modal edge is from the bottom ladder world $`0` to
$`n_E`.  Then $`\bigcirc\bot` holds on $`\{o_E, f\}`, $`\lnot\bigcirc\bot` on
$`\{n_E, f\}`, $`t_3` on all three tops, $`t_6` everywhere, and $`u` holds on
the ladder exactly at $`0`, as $`p` does on the Rieger–Nishimura ladder.  Every
$`\mathrm{rel}(A)` with $`A` free of $`\bigcirc` holds at the three tops, so an
implication evaluated at a ladder world sees only the ladder, and
(`rel_transfer`)

$$`\mathcal{U}, x \Vdash \mathrm{rel}(A) \iff \mathcal{L}, x \Vdash A`

for every ladder world $`x`.  With the choice-free truth sets of the odd rungs
(`sat_rnP_cf`, Section 4), $`x_k` holds at the ladder world $`x` exactly when
$`x \le k`, which separates the chain.

# Every rung above the sixth

$`t_6 \vdash t_n` for $`n = 6, 7` and every $`n \ge 9`, by the rung order through
the substitution, so the chain lies below each of these rungs.  PROVED.

{stmt}`T6.t6_le_rung`

{docstring T6.t6_le_rung +allowMissing}

{srcLink}`T6.t6_le_rung`

{stmt}`T6.rung_downset_infinite`

{docstring T6.rung_downset_infinite +allowMissing}

{srcLink}`T6.rung_downset_infinite`

The construction says nothing about $`t_8`: $`t_6 \nvdash t_8` by the rung order
(`rnSub_deriv_iff`, Section 2), and the file records that $`t_8` fails on the
ladder of $`\mathcal{U}`, where the chain holds.  Whether $`{\downarrow}t_8` is
finite is OPEN (Section 11).

# Axioms

As recorded in the file (`#axioms_within`), and confirmed by `#print axioms` on
the build: `propext`, `Quot.sound` for `t6_regular`, `t3_le_u`, `cell_m6`,
`cell_m9`, `rel_transfer`, `t6_chain`, `t6_downset_infinite`, `t6_le_rung` and
`rung_downset_infinite`.  No `Classical.choice`: the cells are closed tableaux
checked by `decide`, and the countermodel argument uses the choice-free truth
sets of Section 4.
