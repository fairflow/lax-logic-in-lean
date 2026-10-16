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

#doc (Manual) "Status, simplification, and what is not built" =>

This section records the axioms the printed results use, the check that the
inductive definitions carry no computed indices, why the extracted constraints
come out unsimplified and how they could be simplified, what is not built, and
the references.

# Axioms

Of the 112 declarations printed in this document, 14 use no axiom at all (most
of them are definitions), 34 use `propext` only, and 43 use `propext` and
`Quot.sound`.  The remaining 21 also use `Classical.choice`:

* through Mathlib's rationals: the arithmetic certificates and the engine
  (Section 8), and the examples that evaluate them (Example 6.1 and the
  kernel-run instance of Section 10);
* through `OrderHom.lfp`: the least-fixpoint form of the least model
  (Section 4);
* avoidably, through a lemma about list lengths: the three run theorems of the
  machine (Section 7);
* through the canonical model: completeness of QLL (Section 3);
* through a classical argument: the validity of
  $`(\bigcirc A \twoheadrightarrow \bigcirc B) \twoheadrightarrow \bigcirc (A \twoheadrightarrow B)`
  in models with $`R_\exists = R_i` (Section 3).

No printed declaration depends on `sorryAx`.  The library pins the axiom sets
of its main results with `#guard_msgs`, so a change in them fails the build.

# Inductive definitions without computed indices

An index of an inductive family that is computed by a function (green slime,
in McBride's term) cannot be inverted by the unifier, so case analysis on the
family either fails or survives only by substituting into whatever stands
opposite, and statements tend to bend to fit.  Every indexed family of the
library was checked with the command `#slime`.  Fourteen of the 23 carried
computed indices: the instance $`A[t/0]` in the conclusion of
$`(\forall E)`, the instantiated head in every clause rule, the goal list
$`\tilde{\varphi} \mathbin{+\!\!+} [\varphi] \mathbin{+\!\!+} \tilde{\psi}` in
every rule of Table 2 and in the machine's steps, and a leaf position computed
by addition.  Each computed index was replaced by a variable and an equation
premise, with the proofs changed only by `rfl` at constructions and `subst` in
case analyses; no theorem statement changed, and the axioms of all 112 printed
declarations are the same before and after.  The census is recorded in the
repository as `docs/qll-slime-census-2026-10-15.md`.

# Why the constraints come out unsimplified

The examples show $`\top` units, ground constraints kept after being checked,
unevaluated arithmetic, unmerged linear forms, duplicated constraints,
re-derived shared subgoals, and local variables that are never projected
away.  Each has a cause, and a remedy that costs nothing certified:

:::wtable (widths := "0.24 0.40 0.36") +header
*
  * Redundancy
  * Cause
  * Remedy
*
  * $`\top` units
  * $`\mathit{val}` contributes $`\top` and $`\mathit{bind}` a $`\land`; the
    monad laws hold only up to $`\dashv\vdash`
  * a normalising conjunction that drops $`\top`, one lemma
*
  * ground constraints kept
  * resolution substitutes without evaluating; the store is tested, never
    rewritten
  * decide ground atoms on entry
*
  * unevaluated arithmetic
  * Herbrand terms; variable heads force nothing
  * fold constants, or a fresh variable per compound argument
*
  * unmerged linear forms
  * normalisation happens only inside the solver
  * normalise when reading an atom
*
  * duplicated constraints
  * shared inputs are read twice
  * the store as a set
*
  * shared subgoals re-derived
  * tree-shaped search
  * tabling, justified by answer soundness plus projection
*
  * dead local variables
  * no answer projection
  * project as variables become unreachable, two entailments each
:::

The $`\top` units are precisely the syntactic residue of the writer monad's
$`\mathit{val}`, and Section 10 explains why they cannot simply be removed by
regrouping: the grouping is information.

# Not built

The following are not built, and nothing in the library asserts them:

* the Gentzen system of the draft's Fig. 1;
* Definition 6.5's refined clauses as formulas (they are used through their
  instances);
* constraints beyond linear arithmetic, in particular a Herbrand equality
  solver;
* the converse simulation from SLD◯ to SLD, the completeness of the machines,
  and the corresponding results for the Herbrand models;
* the switching lemma under an incomplete consistency test;
* the placements of Section 10 that are stated with designed cells only;
* the simplifications above.

# References

* Jaffar and Lassez, _Constraint logic programming_, POPL 1987.
* Jaffar and Maher, _Constraint logic programming: a survey_, J. Logic
  Programming 19/20 (1994) 503–581.
* Jaffar, Maher, Marriott and Stuckey, _The semantics of constraint logic
  programs_, J. Logic Programming 37 (1998) 1–46.
* Jaffar, Maher, Stuckey and Yap, _Projecting CLP(R) constraints_, New
  Generation Computing 11 (1993) 449–469.
* Argenius and Voronkov, _Semantics of constraint logic programs with bounded
  quantifiers_, LNAI 1050 (1996).
* Lloyd, _Foundations of Logic Programming_, 2nd ed., 1987.
* Van Emden and Kowalski, _The semantics of predicate logic as a programming
  language_, J. ACM 23 (1976).
* Fairtlough and Mendler, _Propositional lax logic_, Information and
  Computation 137 (1997).
* Fairtlough, Mendler and Cheng, _Abstraction and refinement in higher order
  logic_, TPHOLs 2001, LNCS 2152.
* Moggi, _Notions of computation and monads_, Information and Computation 93
  (1991).
* Maher, _Logic semantics for a class of committed-choice programs_, ICLP 1987.
* Saraswat, _Concurrent Constraint Programming_, MIT Press 1993.
* Haridi and Janson, _Kernel Andorra Prolog and its computation model_, ICLP
  1990.
* Franzén, _Logical aspects of the Andorra Kernel Language_, SICS R91:12
  (1991).
* Naish, _Pruning in logic programming_, TR 95/16, Melbourne (1995).
* Andrews, _The witness properties and the semantics of the Prolog cut_, TPLP
  3(1) (2003).
* Piróg and Staton, _Backtracking with cut via a distributive law and
  left-zero monoids_, JFP 27 (2017).
* Van Hentenryck, _Constraint Satisfaction in Logic Programming_, MIT Press
  1989.
* Frühwirth, _Theory and practice of Constraint Handling Rules_, J. Logic
  Programming 37 (1998).
* Schrijvers, Stuckey and Wadler, _Monadic constraint programming_, JFP 19
  (2009).
* Gocht, McCreesh and Nordström, _An auditable constraint programming solver_,
  CP 2022.
