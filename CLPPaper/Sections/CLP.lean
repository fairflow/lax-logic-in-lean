import Verso
import VersoManual
import LaxLogic.QLL
import CLPPaper.Src
import CLPPaper.Math

open Verso.Genre
open Verso.Genre.Manual
open CLPPaper CLPPaper.Math

#doc (Manual) "Constraint logic programming" =>

The conventional account, and where each of its parts reappears here.  A
reader who knows the Jaffar–Maher survey can use this section as an index to
the rest.

# The scheme

The CLP scheme (Jaffar and Lassez, POPL 1987) parametrises logic programming
by a constraint domain — a structure together with a language of constraints
over it — and a solver.  The standard operational account is the transition
system of Jaffar and Maher's survey (J. Logic Programming 19/20, 1994, §5).
A state is `⟨A, C, S⟩`: the goals `A`, the active constraints `C` and the
passive ones `S`.  The transitions are `→r`, resolving an atom `a` with a
renamed clause `h ← B` and adding the equations `a = h` to the store; `→c`,
moving a constraint from the goals into the store; `→i`, inferring active
constraints from passive ones; and `→s`, continuing if `consistent(C)` and
failing otherwise.  The consistency test may be incomplete: it must accept
every satisfiable store and may accept some unsatisfiable ones.  A successful
derivation ends with no goals, and its store is the answer constraint.

The survey's Theorem 6.1 relates this to the logical semantics.  The success
set coincides with the least model over the domain (item 1).  An answer
constraint `c` of a goal `G` satisfies $`P, T \models c \to G`, with `T` the constraint
theory (item 2, soundness).  If $`P, T \models c \to G` then finitely many answers
cover `c` (item 4): in general a disjunction of answers is needed, unlike in
plain logic programming.  Answer projection — eliminating the local variables
so that only the query's remain — is a separate step, quantifier elimination
over the domain (Jaffar, Maher, Stuckey and Yap, New Generation Computing 11,
1993).  The draft's Table 2 follows Argenius and Voronkov (LNAI 1050, 1996).

# The correspondence

```
conventional CLP                    this development
──────────────────────────────────  ─────────────────────────────────────────────────
constraint domain                   constraint predicates isC; over the Herbrand
                                    universe, relations R (world 2); for computation,
                                    linear arithmetic over ℚ (LinQ)
goal ⟨A, C⟩                         Goal = c □ φ₁,…,φₙ; the machine state (store, forest)
→r, with equations a = h            Rule 5 / clause.  Heads are P(x₁,…,xₘ) with distinct
                                    variables (Def 5.1), so a = h is solved by
                                    substituting the arguments: resolution is matching,
                                    and every other relation between terms is an
                                    explicit constraint
→c                                  Rule 1 / cstr
→s, consistent                      the parameter ok of Rule 1; in the engine satOK, the
                                    certified solver on the whole store, conservative
infer, passive constraints          none: a nonlinear store is left untested
answer constraint                   c' at the end of a run; equivalently total(p) of the
                                    proof tree (Theorem 9.4)
Theorem 6.1(2), soundness           steps_sound, answer_sound: Θ ⊢ c' ⊃ c ∧ G, provable
                                    in intuitionistic QLL with no constraint theory
Theorem 6.1(1), the least model     LHM and its fixpoint characterisations
completeness for closed queries     world2_free: true in the least model iff some proof
                                    tree's total constraint is true in R
answer projection                   for specific shapes only: least value of one
                                    variable of a difference system, and single
                                    equalities by two entailments
```

# What is different

Derivations become proof trees: first-class objects that are checked,
extracted from, and translated.  Soundness is proof-theoretic — the answer
constraint implies the query in QLL with the constraint atoms uninterpreted;
the domain enters only semantically, through the relations of world 2, and
computationally, through the solver.  The solver is outside the trusted base:
every verdict carries a certificate checked in Lean.  And the lax modality
separates the program's logic from its constraints, which is the
abstraction-and-refinement reading of the $`\bigcirc` pass.

The correspondence above is the map from Jaffar–Maher's transition system to
the constructions of this document; the two rows that have no counterpart
(`infer`, passive constraints) mark the two computational shortcuts taken
here, and the projection row marks the one place where the domain's own
theory is needed and only special cases are built.

