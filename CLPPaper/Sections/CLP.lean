import Verso
import VersoManual
import LaxLogic.QLL
import CLPPaper.Src
import CLPPaper.Math
import CLPPaper.Layout

open Verso.Genre
open Verso.Genre.Manual
open CLPPaper CLPPaper.Math
open LaxLogic.QLL LaxLogic.QLL.SLD

#doc (Manual) "Constraint logic programming" =>

This section is new; the 1997 report has no counterpart.  It recalls the
conventional account of CLP and says where each of its parts reappears in
this document.  The lax reading reformulates a scheme that is well
understood, and can be judged only against it: each construction of the later
sections takes over the role of some part of the conventional account, and
the table below says which, and which parts have no counterpart.  The section
has no results of its own; a reader who knows the survey of Jaffar and Maher
can use it as an index to the rest.

# The scheme

The CLP scheme (Jaffar and Lassez, POPL 1987) parametrises logic programming
by a _constraint domain_, a structure together with a language of constraints
over it, and by a _solver_ for those constraints.  The standard operational
account is the transition system of Jaffar and Maher's survey (J. Logic
Programming 19/20, 1994, §5).  A state is a triple $`\langle A, C, S\rangle` of
goals $`A`, active constraints $`C` and passive constraints $`S`.  There are
four transitions:

* $`\rightarrow_r` resolves an atom $`a` with a renamed clause $`h \leftarrow B`
  and adds the equations $`a = h` to the store;
* $`\rightarrow_c` moves a constraint from the goals into the store;
* $`\rightarrow_i` infers active constraints from passive ones;
* $`\rightarrow_s` continues if $`\mathit{consistent}(C)` and fails otherwise.

The consistency test may be incomplete: it must accept every satisfiable store
and may accept some unsatisfiable ones.  A successful derivation ends with no
goals, and its store is the _answer constraint_.

The survey's Theorem 6.1 relates this to the logical semantics.  The success
set coincides with the least model over the domain (item 1).  An answer
constraint $`c` of a goal $`G` satisfies $`P, T \models c \to G`, where $`T` is
the theory of the constraint domain (item 2, soundness).  If
$`P, T \models c \to G`, then finitely many answers together cover $`c`
(item 4); unlike plain logic programming, a disjunction of answers may be
needed.  _Answer projection_, which eliminates the local variables so that
only the query's remain, is a separate step: quantifier elimination over the
domain (Jaffar, Maher, Stuckey and Yap, New Generation Computing 11, 1993).
Table 2 of the 1997 report follows Argenius and Voronkov (LNAI 1050, 1996).

# The correspondence

The table sets each part of the conventional account beside the construction
that plays its part here, with the section where it appears.

:::wtable (widths := "0.30 0.70") +header
*
  * Conventional CLP
  * This document
*
  * constraint domain
  * Constraint predicates are those named by a classifier $`\mathit{isC}`.
    Semantically they are interpreted by relations $`R` over the Herbrand
    universe (world 2 of the canonical model, Section 6); computationally, by
    linear arithmetic over $`\mathbb{Q}` (Section 8).
*
  * goal $`\langle A, C\rangle`
  * A goal $`c \mathrel{\square} \varphi_1, \ldots, \varphi_n`: a store $`c`
    and a list of formulas (Table 2, Section 5); in the machine of Section 7,
    a store and a forest of partial proof trees.
*
  * $`\rightarrow_r`, with equations $`a = h`
  * Rule 5 of Table 2, the rule $`\mathit{clause}` of the machine.  Clause
    heads are $`P(x_1, \ldots, x_m)` with distinct variables (Definition 5.1),
    so $`a = h` is solved by substituting the arguments: resolution is
    matching, and every other relation between terms is an explicit
    constraint.
*
  * $`\rightarrow_c`
  * Rule 1 of Table 2, the rule $`\mathit{cstr}` of the machine.
*
  * $`\rightarrow_s` and $`\mathit{consistent}`
  * The parameter $`\mathit{ok}` of Rule 1.  In the engine (Section 8) it is
    the certified solver run on the whole store, which is conservative.
*
  * $`\rightarrow_i`, passive constraints
  * None: a nonlinear store is left untested.
*
  * answer constraint
  * The store $`c'` at the end of a run; equivalently, up to $`\dashv\vdash`,
    the conjunction of the constraint leaves of the run's proof tree
    (Theorem 9.4, Section 5).
*
  * Theorem 6.1(2), soundness
  * $`\Theta \vdash c' \twoheadrightarrow c \land G`, provable in intuitionistic
    QLL with no constraint theory (Corollary 9.8 and the engine's answer
    soundness, Sections 5 and 8).
*
  * Theorem 6.1(1), the least model
  * The least Herbrand model and its fixpoint characterisations (Section 4).
*
  * completeness for closed queries
  * A closed query is true in the least model over $`R` if and only if some
    proof tree's total constraint is true in $`R` (Section 5).
*
  * answer projection
  * For particular shapes only: the least value of one variable of a
    difference system, and single equalities by two entailments (Section 8).
:::

# What is different

Derivations become proof trees: first-class objects that are checked,
extracted from, and translated.  Soundness is proof-theoretic: the answer
constraint implies the query in QLL with the constraint atoms uninterpreted.
The domain enters only semantically, through the relations of world 2, and
computationally, through the solver.  The solver is outside the trusted base,
because every verdict carries a certificate that is checked in Lean.  And the
lax modality separates a program's logic from its constraints, which is the
abstraction-and-refinement reading of the $`\bigcirc` pass.

Two rows of the table have no real counterpart here: inference of active
constraints from passive ones, and passive constraints themselves.  They mark
the two computational shortcuts this development takes.  The projection row
marks the one place where the domain's own theory is needed; only special
cases are built.
