import Verso
import VersoManual
import LaxLogic.QLL
import CLPPaper.Src
import CLPPaper.Cite
import CLPPaper.Math

open Verso.Genre
open Verso.Genre.Manual
open CLPPaper CLPPaper.Math CLPPaper.Cite
open LaxLogic.QLL LaxLogic.QLL.SLD

#doc (Manual) "Introduction" =>

This section introduces the 1997 report that the document mechanises, the
three questions the mechanisation was asked to answer, what it found, and how
the rest of the document is laid out.  It has no results of its own.

# The proposal

The document mechanises the report

> M. Fairtlough, M. Mendler and M. Walton, _First-order Lax Logic as a framework for Constraint Logic Programming_, draft of 10 September 1997.

It is cited from here on as the 1997 report, and its numbered results keep
their numbers: Theorem 9.4 below is Theorem 9.4 of the report.  The draft is
the version mechanised; the references list the University of Passau
technical report of the same title {pcite}`FairtloughMendlerWalton1997`.

Constraint logic programming (CLP), in the scheme of {cite}`JaffarLassez1987`,
replaces unification by constraint solving over a domain: a clause body may
contain constraints, resolution collects them into a store, and an answer is a
constraint rather than a substitution.  The 1997 report observes that the
separation between the logical part of a program and its constraints is what
the lax modality $`\bigcirc` of {cite}`FairtloughMendler1997` expresses.  A clause

$$`\forall \tilde{x}.\; S \twoheadrightarrow \bigcirc P(\tilde{x})`

says that $`P(\tilde{x})` follows from $`S` _up to a constraint that is not
stated_, and a query $`\bigcirc G` asks for the constraint under which $`G`
holds.

The report develops this in two passes.  The first is ordinary CLP: built-in
constraint atoms, proof trees with constraint leaves, the goal reduction of its
Table 2, and the soundness theorems that connect them.  The second is the
$`\bigcirc` pass: abstract the constraints out of the program, prove the
abstract program in lax logic, and extract the constraint from the abstract
proof by a writer monad.  Its Theorem 9.7 says that the two passes compute
the same answer.

# Three questions

The mechanisation was asked to settle three things.

* What does the lax reading add to the theory of CLP?
* Can it be implemented efficiently and with certificates, using an external
  solver where that helps?
* Is there a significant program to show for it?

# What was found

_Theory._  Every result of the 1997 report that is a theorem is now a theorem in
Lean, in both passes, with two exceptions that are false as stated: the second
half of Proposition 6.6, and the equivalence of a clause body with its
$`\bigcirc`-decorated variant when the head is plain.  Both are refuted by
kernel-checked countermodels (Sections 6 and 10).  Three things were added that
the report does not have.

* The rules of proof trees, applied at the open leaves of partial trees, give
  one operational semantics for both passes.  Table 2 is this semantics with
  the tree forgotten, Theorem 9.4 becomes a step invariant, the $`\bigcirc`
  pass gets an operational reading, and the switching lemma and the exact
  effect of pruning are proved for it (Section 7).
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

_Programs._  The examples run from the 1997 report's own to ripple-carry adders of
sixty-four bits with every output certified, the CLP(R) mortgage program with
exact rational answers, and a scheduling problem with disjunctive resource
constraints (Section 9).

# How to read this document

Sections are in dependence order.  Section 2 sets the conventional account of
CLP beside the constructions of this document, so that a reader who knows the
survey of {cite}`JaffarMaher1994` can place each construction before meeting
it.  Sections 3 to 6 mechanise the 1997 report; Sections 2, 7, 8, 10, 11 and
12 are new; Section 9 works the report's examples and new ones; Section 12
compares the engine with SWI-Prolog on a standard CLP program; Section 13
records what is and is not built; Section 14 lists the references.  Each
section opens by saying which of these it is, and which problem it solves.

One example runs through Sections 4 to 7: Example 9.5 of the 1997 report,
three clauses with four constraint atoms.  Section 4 gives the program,
Section 5 its Table 2 run and its proof tree, Section 6 its abstraction and
the constraint extracted from it, which agrees with the Table 2 answer
(Theorem 9.7), and Section 7 the same run in both machines.  Every state,
tree and constraint shown for it is a statement checked by the Lean kernel in
`LaxLogic/QLL/CLPExamples.lean`; the text links to the checking declaration
instead of printing it, since its statement is the display.

Results carry the 1997 report's numbers where the report has them; results it
does not have are named, not numbered.  Each result is given three times:

* in words, saying what it states and why it is there;
* as a displayed formula, generated when the document is built from the type
  of the Lean declaration, so that it cannot drift from the code (variables are
  quantified at the front, hypotheses are listed one per line before
  $`\Longrightarrow`, and the conclusion comes last);
* as the Lean declaration itself, in small type with a rule on its left, with
  the implicit arguments omitted (they are the free letters of the statement)
  and a link to the line of the source at the commit that was built.

*Status.*  The proofs are written in Lean 4 {pcite}`DeMouraUllrich2021` with
Mathlib {pcite}`MathlibCommunity2020`.  PROVED means that the declaration is
checked by the Lean kernel and contains no `sorry`; the axioms each one uses
are listed in Section 13.
REFUTED means that a kernel-checked countermodel of the statement as written
exists; the refuting declaration is printed.  OPEN means neither: the
statement is fixed and nothing asserts it.  Every displayed result in this
document is PROVED unless the text says otherwise.
