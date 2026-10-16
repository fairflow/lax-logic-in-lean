import Verso
import VersoManual
import LaxLogic.QLL
import CLPPaper.Src
import CLPPaper.Math

open Verso.Genre
open Verso.Genre.Manual
open CLPPaper CLPPaper.Math
open LaxLogic.QLL LaxLogic.QLL.SLD

#doc (Manual) "Introduction" =>

This section says what the 1997 draft proposed, which three questions the
mechanisation was asked to answer, what it found, and how the rest of the
document is laid out.

# The proposal

Constraint logic programming (CLP), in the scheme of Jaffar and Lassez,
replaces unification by constraint solving over a domain: a clause body may
contain constraints, resolution collects them into a store, and an answer is a
constraint rather than a substitution.  The 1997 draft observes that the
separation between the logical part of a program and its constraints is what
the lax modality $`\bigcirc` of Fairtlough and Mendler expresses.  A clause

$$`\forall \tilde{x}.\; S \twoheadrightarrow \bigcirc P(\tilde{x})`

says that $`P(\tilde{x})` follows from $`S` _up to a constraint that is not
stated_, and a query $`\bigcirc G` asks for the constraint under which $`G`
holds.

The draft develops this in two passes.  The first is ordinary CLP: built-in
constraint atoms, proof trees with constraint leaves, the goal reduction of its
Table 2, and the soundness theorems that connect them.  The second is the
$`\bigcirc` pass: abstract the constraints out of the program, prove the
abstract program in lax logic, and extract the constraint from the abstract
proof by a writer monad.  The draft's Theorem 9.7 says that the two passes
compute the same answer.

# Three questions

The mechanisation was asked to settle three things.

* What does the lax reading add to the theory of CLP?
* Can it be implemented efficiently and with certificates, using an external
  solver where that helps?
* Is there a significant program to show for it?

# What was found

_Theory._  Every result of the draft that is a theorem is now a theorem in
Lean, in both passes, with two exceptions that are false as stated: the second
half of Proposition 6.6, and the equivalence of a clause body with its
$`\bigcirc`-decorated variant when the head is plain.  Both are refuted by
kernel-checked countermodels (Sections 6 and 10).  Three things were added that
the draft does not have.

* One operational semantics on partial proof trees serves both passes.  Table 2
  is its projection, Theorem 9.4 becomes a step invariant, and the switching
  lemma and the exact effect of pruning are proved for it (Section 7).
* A study of _where_ the modality may be placed, with the realiser type of each
  placement, shows which placements are redundant, which are unsound, and which
  are new; and that provable equivalence is the wrong notion for a
  computational reading, because two provably equivalent formulas can have
  different realisers (Section 10).
* An inclusion lemma orders derivations by the table entries they use.  It is
  what makes derivations comparable at the abstract level, before any
  constraint is solved (Section 10).

_Implementation._  The engine is depth-first resolution in which every answer
carries a proof tree, checked by a checker proved sound.  Constraints over the
rationals are solved by an untrusted Fourier–Motzkin procedure whose verdicts
carry witnesses or Farkas multipliers that are checked in Lean.  Timing
problems get least values certified from both sides.  Wolfram's `FindInstance`
and `Minimize` are used as untrusted oracles through a bridge, and their
answers are re-checked by the same checkers (Section 8).

_Programs._  The examples run from the draft's own to ripple-carry adders of
sixty-four bits with every output certified, the CLP(R) mortgage program with
exact rational answers, and a scheduling problem with disjunctive resource
constraints (Section 9).

# How to read this document

Sections are in dependence order.  Section 2 sets the conventional account of
CLP beside the constructions of this document, so that a reader who knows the
survey of Jaffar and Maher can place each construction before meeting it.
Sections 3 to 6 follow the draft; Sections 7, 8, 10 and 11 are new; Section 9
works the examples; Section 12 records what is and is not built.

Results carry the draft's numbers where the draft has them; results the draft
does not have are named, not numbered.  Each result is given three times:

* in words, saying what it states and why it is there;
* as a displayed formula, generated when the document is built from the type
  of the Lean declaration, so that it cannot drift from the code (variables are
  quantified at the front, hypotheses are listed one per line before
  $`\Longrightarrow`, and the conclusion comes last);
* as the Lean declaration itself, in small type with a rule on its left, with
  the implicit arguments omitted (they are the free letters of the statement)
  and a link to the line of the source at the commit that was built.

*Status.*  PROVED means that the declaration is checked by the Lean kernel and
contains no `sorry`; the axioms each one uses are listed in Section 12.
REFUTED means that a kernel-checked countermodel of the statement as written
exists; the refuting declaration is printed.  OPEN means neither: the
statement is fixed and nothing asserts it.  Every displayed result in this
document is PROVED unless the text says otherwise.
