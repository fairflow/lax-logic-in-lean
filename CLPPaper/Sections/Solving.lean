import Verso
import VersoManual
import LaxLogic.QLL
import CLPPaper.Src
import CLPPaper.Decl
import CLPPaper.Math

open Verso.Genre
open Verso.Genre.Manual
open CLPPaper CLPPaper.Math
open LaxLogic.QLL LaxLogic.QLL.SLD
open LaxLogic.QLL.LinQ LaxLogic.QLL.Engine

#doc (Manual) "Solving constraints with certificates" =>

This section is new; the 1997 report has no counterpart.  Sections 5 to 7
leave the constraint atoms uninterpreted: an answer is a formula, and whether
it can be satisfied is not their concern.  A program is run for its answers,
so that question has to be settled, and settled without enlarging what must
be trusted.  This section says how an answer constraint over the
rationals is solved, and why nothing that solves it has to be trusted: every
verdict carries a certificate (an assignment, Farkas multipliers, or a least
value with both) which is checked by a function proved sound.  It also
describes the engine that produces answers and proves its answers sound.
These results use `Classical.choice`, through Mathlib's rationals.

# From atoms to linear constraints

A term is read as a linear expression: variables; numerals $`n`, $`-n` and
$`n/d`, parsed from the function symbol; and $`\mathit{add}`,
$`\mathit{sub}`, $`\mathit{neg}`, and $`\mathit{mul}` when one side is
constant.  An atom $`\mathit{leq}`, $`\mathit{lt}`, $`\mathit{geq}`,
$`\mathit{gt}` or $`\mathit{eq}` between two such terms becomes a constraint
$`e \le 0`, $`e < 0` or $`e = 0`.  A conjunction of atoms becomes a list of
constraints, or fails if some atom is not linear.

# Certificates

A _witness_ is an assignment of rationals to the variables.  A _Farkas
certificate_ is a list of multipliers, one per constraint, non-negative except
on equations.  The certificate's combination of the constraints is computed and
normalised; the certificate is valid when every variable's coefficient is
$`0` and the constant is $`> 0`, or the constant is $`\ge 0` and some strict
constraint has a positive multiplier.  A valid certificate refutes the
system.

*A checked witness satisfies every constraint.*

{stmt}`LinQ.checkWitness_sound`

{leanDecl LinQ.checkWitness_sound}

*A checked Farkas certificate shows the system unsatisfiable.*

{stmt}`LinQ.checkFarkas_unsat`

{leanDecl LinQ.checkFarkas_unsat}

*Fourier–Motzkin elimination, untrusted.*  Each constraint becomes a row with
its multiplier vector.  While variables remain, the variable with the fewest
pairs of positive and negative occurrences is eliminated, with a cap on the
number of new rows.  A contradiction row's multipliers are the Farkas
certificate; otherwise back-substitution builds a witness.  This is a
definition, so no statement is displayed.

{stmt}`LinQ.fm`

{leanDecl LinQ.fm}

*Certified satisfiability.*  A verdict $`\mathit{sat}(w)` that passes
certification has $`w` a solution.

{stmt}`LinQ.certifyVerdict_sat`

{leanDecl LinQ.certifyVerdict_sat}

*Certified unsatisfiability.*  A verdict $`\mathit{unsat}(\tilde{\lambda})`
that passes certification has the system unsatisfiable.  Any solver may
produce the verdict, and none has to be trusted.

{stmt}`LinQ.certifyVerdict_unsat`

{leanDecl LinQ.certifyVerdict_unsat}

# Entailment, least values, projection

An entailment $`\mathit{cs} \models e \le 0` is established by refuting
$`\mathit{cs} \land -e < 0`, and an equation by both inequalities; this is how
the answers of the mortgage program (Section 9) are certified.  Timing
programs produce constraints $`x \ge y + d` and $`x \ge d`, whose least
solution is given by longest paths.  The path attaining the value of
$`z`, the _critical path_, gives multipliers $`1` on its constraints and on
$`z - z^{*} < 0`: a telescoping Farkas certificate.

*Certified entailment, by refutation.*

{stmt}`Engine.entailsLe_sound`

{leanDecl Engine.entailsLe_sound}

*Certified lower bound.*  A checked lower-bound certificate gives
$`z^{*} \le \sigma(z)` for every solution $`\sigma`; with a witness that
attains $`z^{*}`, the least value is certified from both sides.

{stmt}`Engine.lowerBoundCert_sound`

{leanDecl Engine.lowerBoundCert_sound}

*Upward closure, a projection.*  If $`z` has a non-positive coefficient in
every inequality, raising $`z` preserves solutions, so the projection of the
solution set onto $`z` is exactly $`z \ge z^{*}`.

{stmt}`Engine.upClosed_sound`

{leanDecl Engine.upClosed_sound}

# The engine

The engine is depth-first with leftmost selection, written in
continuation-passing style.  Existentials get fresh variables from a counter,
and clauses are indexed by head.  With the flag `eager` set, the whole store is
read and passed to the certified solver after each constraint, and an
$`\mathit{unsat}` verdict fails the branch (the transition
$`\rightarrow_s`).  Every answer carries its proof tree.

*The search,* a strategy over the rules of Table 2.  This is a definition, so
no statement is displayed.

{stmt}`Engine.solveK`

{leanDecl Engine.solveK}

*Answer soundness.*  An answer whose proof tree passes the checker satisfies
$`\Theta \vdash \mathit{constraint} \twoheadrightarrow G`.

{stmt}`Engine.answer_sound`

{leanDecl Engine.answer_sound}

# Wolfram as an untrusted oracle

Through the Lean–Wolfram bridge one kernel is kept alive and three kinds of
command are sent: `FindInstance` over the reals for a witness; `FindInstance`
over the multipliers for the Farkas conditions, normalised; and `Minimize`
for a least value, followed by a Farkas request for the strict bound.  Every
answer goes through the same checkers as the in-Lean solver's.  On sparse
timing systems Fourier–Motzkin answers in under a millisecond and Wolfram in
hundreds of milliseconds.  On a system designed to defeat elimination, all
$`\pm x_i \pm x_j \le 1` over five variables, elimination gives up at the row
cap and Wolfram answers, with certificates that check (Section 9).
