import Verso
import VersoManual
import LaxLogic.QLL
import CLPPaper.Src
import CLPPaper.Decl
import CLPPaper.Math
import CLPPaper.Layout

open Verso.Genre
open Verso.Genre.Manual
open CLPPaper CLPPaper.Math
open LaxLogic.QLL LaxLogic.QLL.SLD
open LaxLogic.QLL.CLPExamples

#doc (Manual) "Examples" =>

This section works the examples of the 1997 report, Examples 9.5, 6.1 and 2.1
(the last is the CLP(R) mortgage program), and adds new ones.  The theorems of
the earlier sections hold for every program; the examples show them at work
on particular programs, and exercise the engine and the certified solver of
Section 8 at sizes where trusting an unchecked answer would matter.  They are
grouped by constraint domain and by the technique that solves them, and each
is given in enough detail that its numbers can be recomputed by hand.

:::wtable (widths := "0.10 0.30 0.28 0.32") +header
*
  * Group
  * Domain
  * Solved by
  * Checked by
*
  * A
  * uninterpreted constraint atoms
  * nothing
  * the kernel
*
  * B
  * linear $`\mathbb{Q}`, difference form
  * elimination, longest paths
  * the kernel (Example 6.1); compiled checkers
*
  * C
  * linear $`\mathbb{Q}`, general coefficients
  * elimination, entailment
  * compiled checkers
*
  * D
  * as B and C
  * Wolfram, through the bridge
  * compiled checkers
:::

# A. Uninterpreted constraints: Example 9.5

This is the running example of Sections 4 to 7: its program is displayed in
Section 4.4, its Table 2 run and proof tree in Section 5.3, its abstraction
and extracted constraint in Section 6.3, and its runs in SLD and SLD◯ in
Section 7.6.  Two results complete it.

*Corollary 9.8 on Example 9.5.*  The answer of the six steps implies the
query: $`\Theta \vdash (\top \land c_1) \land c_3 \twoheadrightarrow \top \land (Q \land \top)`
(in the display the query $`Q` is $`\mathit{goal}_{95}` and $`c_i` is $`c(i)`).

{stmt}`CLPExamples.cor95`

{leanDecl CLPExamples.cor95}

*Theorem 9.7 on Example 9.5.*  There is a concrete proof tree of $`Q` whose
abstract image proves $`\bigcirc Q` from the abstract program, and the
constraint extracted from it is $`\dashv\vdash (\top \land c_1) \land c_3`,
the answer of the six steps.

{stmt}`CLPExamples.thm97_95`

{leanDecl CLPExamples.thm97_95}

# B. Difference constraints: Example 6.1

The program is

$$`\theta_0 = \forall s.\, s \ge 5 \twoheadrightarrow A_1(s), \qquad \theta_1 = \forall s.\, s \ge 9 \twoheadrightarrow A_2(s),`

$$`\theta_2 = \forall t.\, \bigl(\exists s.\, A_1(s) \land A_2(s) \land t \ge s + 35\bigr) \twoheadrightarrow B(t),`

and the query is $`B(z)`.  The engine resolves with $`\theta_2` at
$`t := z`, opens the existential at a fresh variable $`u`, splits the
conjunction, and resolves $`A_1(u)` and $`A_2(u)` with $`\theta_0` and
$`\theta_1`, moving three constraints into the store:

$$`[0]\;\; -u + 5 \le 0 \qquad\quad [1]\;\; -u + 9 \le 0 \qquad\quad [2]\;\; u - z + 35 \le 0`

_Elimination._  $`z` occurs only in $`[2]`, negatively, and $`u` occurs only
negatively in $`[0]` and $`[1]`; nothing new is created and no contradiction
arises.  _Back-substitution._  $`u` has lower bounds $`5` and $`9`, so
$`u = 9`; $`z` has lower bound $`u + 35 = 44`.  The witness is
$`(z, u) = (44, 9)`.  _Least value._  Longest paths give $`u = 9` through
$`[1]` and $`z = 44` through $`[2]`.  The critical path $`[2], [1]` gives
multipliers $`(0, 1, 1)`, and with multiplier $`1` on $`z - 44 < 0` the
combination $`(-u + 9) + (u - z + 35) + (z - 44) = 0`, which uses a strict
constraint, is a contradiction.  _Projection._  $`z` has coefficient $`-1` in
its only constraint, so the answer is upward closed in $`z`.

*The kernel runs the engine on Example 6.1 and accepts its tree.*

{stmt}`CLPExamples.check61`

{leanDecl CLPExamples.check61}

*The 1997 report's answer $`z \ge 44`.*  A value $`r` for $`z` extends to a solution
of the answer constraint if and only if $`44 \le r`.

{stmt}`CLPExamples.ex61_answer`

{leanDecl CLPExamples.ex61_answer}

*The $`\bigcirc` pass on Example 6.1.*  It extracts

$$`(((\top \land u \ge 5) \land (((\top \land u \ge 9) \land (\top \land \top)) \land \top)) \land \top) \land (\top \land (\top \land z \ge u + 35)),`

which is the 1997 report's expression, and this is $`\dashv\vdash` the total
constraint.

{stmt}`CLPExamples.ext61`

{leanDecl CLPExamples.ext61}

*Corollary 9.8 by the 1997 report's route, on Example 6.1.*

{stmt}`CLPExamples.cor61`

{leanDecl CLPExamples.cor61}

# B, continued: scheduling and adders

A scheduling program has four tasks, precedences, a release time, and one
shared machine encoded by a two-clause predicate $`\mathit{disjoint}`.  With
eager pruning it gives earliest ends $`12` on the first machine order and
$`11` on the second.  With deadline $`10` both branches are refuted, by Farkas
certificates whose multipliers are $`1` on the critical path and on the
deadline constraint.

Ripple-carry adders are generated with gate delays $`3` for exclusive-or gates
and $`2` for conjunction and disjunction gates.  Each gate is a clause

$$`\mathit{out}(t) \leftarrow \exists s.\, \mathit{in}_1(s) \land \mathit{in}_2(s) \land t \ge s + d,`

and the carry-out of $`n` bits settles at $`4n + 3`, certified from both sides
for $`n` up to $`64` ($`449` clauses, a proof tree of $`1794` nodes,
$`513` constraints) and for all $`33` outputs of a $`32`-bit adder at once
($`15330` nodes, $`4385` constraints), in tens of milliseconds compiled.  For
$`n = 2` the seventeen constraints and the critical path of six are listed in
the write-up `docs/qll-clp-writeup.md`.

# C. General coefficients: the mortgage program

Example 2.1 of the 1997 report, over $`\mathbb{Q}`:

$$`\mathit{mortgage}(P, D, I, M, B) \leftarrow D \le 1 \land B + M = P \cdot (I + 1),`

$$`\mathit{mortgage}(P, D, I, M, B) \leftarrow 1 < D \land \mathit{mortgage}(P \cdot (I + 1) - M,\; D - 1,\; I,\; M,\; B),`

with principal $`P`, duration $`D`, interest rate $`I`, monthly payment
$`M` and balance $`B`.  With $`r = 1 + I` and $`B = 0` the balances satisfy
$`P \cdot r^{D} = M \cdot (1 + r + \cdots + r^{D-1})`.

* For $`D = 2` and $`I = 1/100` the constraints are $`1 < 2`, $`2 - 1 \le 1`
  and $`0 + M = (P \cdot (1/100 + 1) - M) \cdot (1/100 + 1)`, read as
  $`(201/100) \cdot M = (10201/10000) \cdot P`, and the relation is certified as
  an entailment in both directions.
* For $`D = 120`, $`I = 1/100` and $`M = 1721.65` the answer has $`121`
  constraints, and $`P` is determined as the exact rational
  $`M \cdot \sum_k r^{-k}`, with a 246-digit numerator over a 241-digit
  denominator, $`119999.9037\ldots`.
* For $`D = 5` the certified coefficients are
  $`M = (10510100501/51010050100) \cdot P` at $`I = 1/100` and
  $`M = (161051/610510) \cdot P` at $`I = 1/10`.  The 1997 report's printed figure
  $`0.263797522` belongs to the second rate, and its $`P = 120000` is the first
  answer rounded.

# D. Wolfram

The systems above were also sent to Wolfram through the bridge, and every
answer passed the Lean checks: Example 6.1 satisfiable with least value $`44`;
the mortgage query satisfiable; the schedule with deadline $`10`
unsatisfiable, with a Farkas certificate; the adders satisfiable with least
value $`4n + 3`, in $`0.26` to $`4.9` seconds against under a millisecond for
elimination.  On the designed system $`\pm x_i \pm x_j \le 1` over five
variables ($`40` constraints) elimination grows the rows
$`40 \to 88 \to 411 \to 10211` and stops at the cap, while Wolfram answers
satisfiable at $`x = 0`; with $`\sum_i x_i \ge 5` added, Wolfram answers
unsatisfiable with multipliers $`1/5, 1/5, 2/5, 1/5, 2/5`, whose combination
is $`1 > 0`.
