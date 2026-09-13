import Verso
import VersoManual
import VersoBlueprint
import LaxLogic.QLL

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Solving constraints with certificates" =>

How an answer constraint over the rationals is solved, and why nothing that
solves it has to be trusted: every verdict carries a certificate — an
assignment, Farkas multipliers, or a least value with both — checked by a
function proved sound.

# From atoms to linear constraints

A term is read as a linear expression: variables, numerals `n`, `-n`, `n/d`
parsed from the function symbol, `add`, `sub`, `neg`, and `mul` when one side
is constant.  An atom `leq`, `lt`, `geq`, `gt` or `eq` between two such terms
becomes `e ≤ 0`, `e < 0` or `e = 0`.  A conjunction of atoms becomes a list of
constraints, or fails if any atom is not linear.

# Certificates

A witness is an assignment; a Farkas certificate is a list of multipliers, one
per constraint, non-negative except on equations.  The combination is
computed and normalised; the certificate is valid when every variable's
coefficient is `0` and the constant is `> 0`, or `≥ 0` with a positive
multiplier on some strict constraint.  Validity refutes the system.

:::group "solve"
The certified solver.
:::

:::theorem "solve_witness" (parent := "solve") (lean := "LaxLogic.QLL.LinQ.checkWitness_sound")
A checked witness satisfies every constraint.
:::

:::theorem "solve_farkas" (parent := "solve") (lean := "LaxLogic.QLL.LinQ.checkFarkas_unsat")
A checked Farkas certificate shows the system unsatisfiable.
:::

:::definition "solve_fm" (parent := "solve") (lean := "LaxLogic.QLL.LinQ.fm")
Fourier–Motzkin elimination, untrusted.  Each constraint becomes a row with
its multiplier vector; while variables remain, the variable with the fewest
positive-negative pairs is eliminated, with a cap on the number of new rows;
a contradiction row's multipliers are the Farkas certificate, and otherwise
back-substitution builds a witness.
:::

:::theorem "solve_sat" (parent := "solve") (uses := "solve_witness") (lean := "LaxLogic.QLL.LinQ.certifyVerdict_sat")
A verdict `sat w` that passes certification has `w` a solution.
:::

:::theorem "solve_unsat" (parent := "solve") (uses := "solve_farkas") (lean := "LaxLogic.QLL.LinQ.certifyVerdict_unsat")
A verdict `unsat λ̃` that passes certification has the system unsatisfiable.
Any solver may produce the verdict, and none has to be trusted.
:::

# Entailment, least values, projection

Entailment `cs ⊨ e ≤ 0` is established by refuting `cs ∧ −e < 0`, and an
equation by both inequalities; this is how the mortgage program's answers are
certified.  Timing programs produce constraints `x ≥ y + d` and `x ≥ d`, whose
least solution is given by longest paths, and the path attaining the value of
`z` — the critical path — gives multipliers `1` on its constraints and on
`z − z* < 0`, a telescoping Farkas certificate.

:::theorem "solve_entails" (parent := "solve") (uses := "solve_unsat") (lean := "LaxLogic.QLL.Engine.entailsLe_sound")
Certified entailment by refutation.
:::

:::theorem "solve_lower" (parent := "solve") (uses := "solve_farkas") (lean := "LaxLogic.QLL.Engine.lowerBoundCert_sound")
A checked lower-bound certificate gives `z* ≤ σ(z)` for every solution `σ`;
with a witness attaining `z*`, the least value is certified from both sides.
:::

:::theorem "solve_up" (parent := "solve") (lean := "LaxLogic.QLL.Engine.upClosed_sound")
If `z` has a non-positive coefficient in every inequality, raising `z`
preserves solutions, so the projection onto `z` is exactly `z ≥ z*`.
:::

# The engine

Depth-first, leftmost selection, in continuation-passing style; existentials
get fresh variables from a counter; clauses are indexed by head.  With
`eager` set, the whole store is read and passed to the certified solver after
each constraint, and an `unsat` verdict fails the branch — the `→s`
transition.  Every answer carries its proof tree.

:::definition "solve_engine" (parent := "solve") (uses := "trees_cproof") (lean := "LaxLogic.QLL.Engine.solveK")
The search, as a strategy over the rules of Table 2.
:::

:::theorem "solve_answer" (parent := "solve") (uses := "solve_engine, trees_checkC, trees_prv_total") (lean := "LaxLogic.QLL.Engine.answer_sound")
An answer whose tree checks satisfies `Θ ⊢ constraint ⊃ G`.
:::

# Wolfram as an untrusted oracle

Through the Lean–Wolfram bridge one kernel is kept alive and three kinds of
command are sent: `FindInstance` over the reals for a witness; `FindInstance`
over multipliers for the Farkas conditions, normalised; and `Minimize` for a
least value, followed by a Farkas request for the strict bound.  Every answer
goes through the same checkers as the in-Lean solver's.  On sparse timing
systems Fourier–Motzkin answers in under a millisecond and Wolfram in
hundreds of milliseconds; on a system designed to defeat elimination —
all `±xᵢ ± xⱼ ≤ 1` over five variables — elimination gives up at the row cap
and Wolfram answers, with certificates that check.
