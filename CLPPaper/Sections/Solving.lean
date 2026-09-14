import Verso
import VersoManual
import LaxLogic.QLL

open Verso.Genre
open Verso.Genre.Manual

#doc (Manual) "Solving constraints with certificates" =>

How an answer constraint over the rationals is solved, and why nothing that
solves it has to be trusted: every verdict carries a certificate — an
assignment, Farkas multipliers, or a least value with both — checked by a
function proved sound.

# From atoms to linear constraints

A term is read as a linear expression: variables, numerals `n`, `-n`, `n/d`
parsed from the function symbol, `add`, `sub`, `neg`, and `mul` when one side
is constant.  An atom `leq`, `lt`, `geq`, `gt` or `eq` between two such terms
becomes $`e \le 0`, `e < 0` or `e = 0`.  A conjunction of atoms becomes a list of
constraints, or fails if any atom is not linear.

# Certificates

A witness is an assignment; a Farkas certificate is a list of multipliers, one
per constraint, non-negative except on equations.  The combination is
computed and normalised; the certificate is valid when every variable's
coefficient is `0` and the constant is `> 0`, or $`\ge 0` with a positive
multiplier on some strict constraint.  Validity refutes the system.

A checked witness satisfies every constraint.

{docstring LaxLogic.QLL.LinQ.checkWitness_sound +allowMissing}

A checked Farkas certificate shows the system unsatisfiable.

{docstring LaxLogic.QLL.LinQ.checkFarkas_unsat +allowMissing}

Fourier–Motzkin elimination, untrusted.  Each constraint becomes a row with
its multiplier vector; while variables remain, the variable with the fewest
positive-negative pairs is eliminated, with a cap on the number of new rows;
a contradiction row's multipliers are the Farkas certificate, and otherwise
back-substitution builds a witness.

{docstring LaxLogic.QLL.LinQ.fm +allowMissing}

A verdict `sat w` that passes certification has `w` a solution.

{docstring LaxLogic.QLL.LinQ.certifyVerdict_sat +allowMissing}

A verdict `unsat λ̃` that passes certification has the system unsatisfiable.
Any solver may produce the verdict, and none has to be trusted.

{docstring LaxLogic.QLL.LinQ.certifyVerdict_unsat +allowMissing}

# Entailment, least values, projection

Entailment $`\mathit{cs} \models e \le 0` is established by refuting $`\mathit{cs} \land −e < 0`, and an
equation by both inequalities; this is how the mortgage program's answers are
certified.  Timing programs produce constraints $`x \ge y + d` and $`x \ge d`, whose
least solution is given by longest paths, and the path attaining the value of
`z` — the critical path — gives multipliers `1` on its constraints and on
`z − z* < 0`, a telescoping Farkas certificate.

Certified entailment by refutation.

{docstring LaxLogic.QLL.Engine.entailsLe_sound +allowMissing}

A checked lower-bound certificate gives $`z* \le \sigma (z)` for every solution `σ`;
with a witness attaining `z*`, the least value is certified from both sides.

{docstring LaxLogic.QLL.Engine.lowerBoundCert_sound +allowMissing}

If `z` has a non-positive coefficient in every inequality, raising `z`
preserves solutions, so the projection onto `z` is exactly $`z \ge z*`.

{docstring LaxLogic.QLL.Engine.upClosed_sound +allowMissing}

# The engine

Depth-first, leftmost selection, in continuation-passing style; existentials
get fresh variables from a counter; clauses are indexed by head.  With
`eager` set, the whole store is read and passed to the certified solver after
each constraint, and an `unsat` verdict fails the branch — the `→s`
transition.  Every answer carries its proof tree.

The search, as a strategy over the rules of Table 2.

{docstring LaxLogic.QLL.Engine.solveK +allowMissing}

An answer whose tree checks satisfies $`\Theta \vdash \mathit{constraint} \supset G`.

{docstring LaxLogic.QLL.Engine.answer_sound +allowMissing}

# Wolfram as an untrusted oracle

Through the Lean–Wolfram bridge one kernel is kept alive and three kinds of
command are sent: `FindInstance` over the reals for a witness; `FindInstance`
over multipliers for the Farkas conditions, normalised; and `Minimize` for a
least value, followed by a Farkas request for the strict bound.  Every answer
goes through the same checkers as the in-Lean solver's.  On sparse timing
systems Fourier–Motzkin answers in under a millisecond and Wolfram in
hundreds of milliseconds; on a system designed to defeat elimination —
all $`±x_i ± x_j \le 1` over five variables — elimination gives up at the row cap
and Wolfram answers, with certificates that check.
