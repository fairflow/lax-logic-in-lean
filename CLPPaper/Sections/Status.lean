import Verso
import VersoManual
import LaxLogic.QLL
import CLPPaper.Src

open Verso.Genre
open Verso.Genre.Manual
open CLPPaper

#doc (Manual) "Status, simplification, and what is not built" =>

Where every result stands, why the constraints come out unsimplified and how
they could be simplified en route, what is not built, and the references.

# Axioms

`propext` and `Quot.sound` are the axioms of the logical results; `Classical.choice`
enters only through Mathlib's rationals — the arithmetic certificates and
everything that evaluates them — through `OrderHom.lfp`, and, avoidably,
through a list-length lemma in the machine's run theorems.  The status of
every node is computed by the compiler and shown in the summary below.

# Why the constraints come out unsimplified

The examples show $`\top` units, ground constraints kept after being checked,
unevaluated arithmetic, unmerged linear forms, duplicated constraints,
re-derived shared subgoals, and unprojected local variables.  Each has a
cause and a remedy that costs nothing certified:

```
redundancy                       cause                                   remedy
⊤ units                          val contributes ⊤, bind an ∧; laws       normalising ∧ dropping ⊤,
                                 hold only up to ⊣⊢                       one lemma
ground constraints kept          resolution substitutes unevaluated;      decide ground atoms on entry
                                 the store is tested, never rewritten
unevaluated arithmetic           Herbrand terms; variable heads force      fold constants, or a fresh
                                 nothing                                  variable per compound argument
unmerged linear forms            normalisation only inside the solver     normalise when reading an atom
duplicated constraints           shared inputs read twice                 the store as a set
shared subgoals re-derived       tree-shaped search                       tabling, justified by answer
                                                                          soundness plus projection
dead local variables             no answer projection                     project as variables become
                                                                          unreachable, two entailments each
```

The $`\top` units are precisely the syntactic residue of the writer monad's
`val`, and the realiser section explains why they cannot simply be removed
by regrouping: the grouping is information.

# Not built

Fig. 1's Gentzen system; Definition 6.5's refined clauses as formulas
(they are used through their instances); constraints beyond linear
arithmetic, in particular a Herbrand equality solver; the converse
simulation SLD◯ to SLD and the completeness of the machines, with the
Herbrand corollaries; the switching lemma under an incomplete test; the
placements of the last section that are stated with cells; the
simplifications above.  None of these is asserted anywhere.

# References

Jaffar and Lassez, *Constraint logic programming*, POPL 1987.  Jaffar and
Maher, *Constraint logic programming: a survey*, J. Logic Programming 19/20
(1994) 503–581.  Jaffar, Maher, Marriott and Stuckey, *The semantics of
constraint logic programs*, J. Logic Programming 37 (1998) 1–46.  Jaffar,
Maher, Stuckey and Yap, *Projecting CLP(R) constraints*, New Generation
Computing 11 (1993) 449–469.  Argenius and Voronkov, *Semantics of constraint
logic programs with bounded quantifiers*, LNAI 1050 (1996).  Lloyd,
*Foundations of Logic Programming*, 2nd ed., 1987.  Van Emden and Kowalski,
*The semantics of predicate logic as a programming language*, J. ACM 23
(1976).  Fairtlough and Mendler, *Propositional lax logic*, Information and
Computation 137 (1997).  Fairtlough, Mendler and Cheng, *Abstraction and
refinement in higher order logic*, TPHOLs 2001, LNCS 2152.  Moggi, *Notions
of computation and monads*, Information and Computation 93 (1991).  Maher,
*Logic semantics for a class of committed-choice programs*, ICLP 1987.
Saraswat, *Concurrent Constraint Programming*, MIT Press 1993.  Haridi and
Janson, *Kernel Andorra Prolog and its computation model*, ICLP 1990.
Franzén, *Logical aspects of the Andorra Kernel Language*, SICS R91:12
(1991).  Naish, *Pruning in logic programming*, TR 95/16, Melbourne (1995).
Andrews, *The witness properties and the semantics of the Prolog cut*, TPLP
3(1) (2003).  Piróg and Staton, *Backtracking with cut via a distributive law
and left-zero monoids*, JFP 27 (2017).  Van Hentenryck, *Constraint
Satisfaction in Logic Programming*, MIT Press 1989.  Frühwirth, *Theory and
practice of Constraint Handling Rules*, J. Logic Programming 37 (1998).
Schrijvers, Stuckey and Wadler, *Monadic constraint programming*, JFP 19
(2009).  Gocht, McCreesh and Nordström, *An auditable constraint programming
solver*, CP 2022.
