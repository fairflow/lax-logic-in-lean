import Verso
import VersoManual
import LaxLogic.QLL
import CLPPaper.Src
import CLPPaper.Math

open Verso.Genre
open Verso.Genre.Manual
open CLPPaper CLPPaper.Math

#doc (Manual) "Introduction" =>

What the draft proposed, the three questions the mechanisation was asked to
answer, and what it found.

# The proposal

Constraint logic programming, in the scheme of Jaffar and Lassez, replaces
unification by constraint solving over a domain: a clause body may contain
constraints, resolution collects them into a store, and an answer is a
constraint rather than a substitution.  The 1997 draft observes that the
separation between the logical part of a program and its constraints is
exactly what the lax modality of Fairtlough and Mendler expresses.  A clause
$`\forall \tilde{x}. S \supset \bigcirc P(\tilde{x})` says that `P` follows from `S` *up to a constraint left
unstated*; a query $`\bigcirc G` asks for the constraint under which `G` holds.  The
draft develops this in two passes.  First, ordinary CLP with built-in
constraint atoms, proof trees with constraint leaves, and the operational
semantics of Table 2 with its soundness theorems.  Second, the $`\bigcirc` pass:
abstract the constraints out of the program, prove the abstract program in
lax logic, and extract the constraint from the abstract proof by a writer
monad.  Its Theorem 9.7 says the two passes compute the same answer.

# Three questions

The mechanisation was asked to settle three things.  What does the lax
reading add to CLP theory?  Can it be implemented efficiently and with
certificates, using an external solver where that helps?  And is there a
significant program to show for it?

# What was found

On the theory, everything in the draft that is a theorem is now a theorem in
Lean, in both passes, with two exceptions that turned out to be false as
stated (Proposition 6.6's second half, and the equivalence of a body with its
$`\bigcirc`-decorated variant when the head is plain) and are refuted by kernel-checked
countermodels.  Three things were added that the draft does not have.  A
single operational semantics on partial proof trees serves both passes; Table
2 is its projection, Theorem 9.4 becomes a step invariant, and the switching
lemma and the exact effect of pruning are proved for it.  A study of *where*
the modality may be placed, with the realiser types of each placement, shows
which placements are redundant, which are unsound, and which are new — and
that logical equivalence is the wrong notion for a computational reading: two
provably equivalent formulas can have different realisers.  And an inclusion
lemma orders derivations by the table entries they summon, which is what makes
comparison between derivations possible at the abstract level, before any
constraint is solved.

On implementation, the engine is depth-first resolution whose every answer
carries a proof tree checked by a checker proved sound; constraints over the
rationals are solved by an untrusted Fourier–Motzkin procedure whose verdicts
carry witnesses or Farkas multipliers checked in Lean; timing problems get
least values certified from both sides; and Wolfram's `FindInstance` and
`Minimize` are used as untrusted oracles through a bridge, their answers
re-checked by the same checkers.

On programs, the examples run from the draft's own to ripple-carry adders of
sixty-four bits with every output certified, the CLP(R) mortgage program with
exact rational answers, and a scheduling problem with disjunctive resource
constraints.

# How to read this

Sections are in dependence order.  The correspondence with the conventional
account comes first, so a reader who knows Jaffar–Maher can place every
construction before meeting it.  Each
theorem node names its Lean declaration; the graph at the end shows what
depends on what, and the summary the count of nodes by status.

PROVED means kernel-checked, `sorry`-free, with the axiom set recorded; every
node in this document carries a declaration and the compiler assigns its
status.  REFUTED means a kernel-checked countermodel of the statement as
written.  OPEN means neither: the statement is fixed and nothing asserts it.

