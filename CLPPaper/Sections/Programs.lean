import Verso
import VersoManual
import LaxLogic.QLL
import CLPPaper.Src
import CLPPaper.Cite
import CLPPaper.Decl
import CLPPaper.Math

open Verso.Genre
open Verso.Genre.Manual
open CLPPaper CLPPaper.Math CLPPaper.Cite
open LaxLogic.QLL LaxLogic.QLL.SLD
open LaxLogic.QLL.Form (openAt instAll)

#doc (Manual) "Lax logic programs and their least models" =>

This section mechanises Definition 5.1, the indices of §6.2 and the two-world
model of §7 of the 1997 report; the least-model theory between them is
that of {cite}`Lloyd1987`, proved here for the Horn programs that result.  It answers two
questions that come before any constraint is solved.  What does a program
mean?  Its least Herbrand model; that needs Horn clauses, so a clause with a
disjunctive body is first split by the report's indices.  And can that
meaning tell “$`S` holds” from “$`S` holds up to a constraint”?  Not in one
world, where $`\bigcirc` collapses; the report's two-world model can
(Theorem 7.5 at worlds 0 and 1).  The section ends with the program of the
example that runs through Sections 4 to 7.

# Clauses

A $`\Sigma`-formula is built by the grammar
$`S ::= \top \mid P(\tilde{t}) \mid S \land S \mid S \lor S \mid \exists x.\, S`;
there is no $`\bigcirc` and no $`\twoheadrightarrow` in a body.  A program
clause (Definition 5.1) is

$$`\forall x_1 \ldots x_m.\; S \twoheadrightarrow H, \qquad H = P(x_1, \ldots, x_m) \;\text{ or }\; H = \bigcirc_q P(x_1, \ldots, x_m).`

The head's arguments are distinct bound variables, so resolution against a
clause is instantiation.  A program $`\Theta` is a list of clauses.  In Lean a
clause records its arity, its body with a proof that the body is a
Σ-formula, the head predicate, and whether the head is modal (and with which
$`q`).

{stmt}`Clause`

{leanDecl Clause}

The 1997 report's indices $`\mathit{ind}(S)` choose one disjunct at every
$`\lor` of $`S`, and $`\mathit{sel}(S, g)` is $`S` with every disjunction
replaced by the side that $`g` chooses.  A clause is provably equivalent to
the Horn clauses obtained by replacing its body by $`\mathit{sel}(S, g)`, one
for each $`g \in \mathit{ind}(S)`.  The next three results give the two
directions for bodies and the consequence for clauses.

*Selection is sound.*  A proof of one selected disjunct proves the body.

{stmt}`Prv.of_sel`

{leanDecl Prv.of_sel}

*Selection is exhaustive.*  A proof of the body proves the disjunction of its
selections.

{stmt}`Prv.disj_sel`

{leanDecl Prv.disj_sel}

*A clause follows from its Horn clauses.*

{stmt}`Clause.prv_of_toHorn`

{leanDecl Clause.prv_of_toHorn}

# The least Herbrand model

Fix relations $`R` on closed terms, the _built-in_ relations, and a list
$`P` of Horn clauses.  The least model is defined inductively: the atoms of
$`R` hold, $`\top` holds, a conjunction holds if both conjuncts do, an
existential holds if it holds of some closed witness, and a clause fires when
its body holds of an instance.  $`\mathit{LHM}(R, P)` is the set of atoms that
hold, and $`\mathit{Tp}(R, P)` is the immediate consequence operator.

{stmt}`LHM`

{leanDecl LHM}

_Standing hypotheses for the rest of this subsection._  The built-in relations
hold only of closed terms (the hypothesis named `hR` in Lean), and every Horn
clause of $`P` is closed: its body and head arguments mention only its own
bound variables (`hP`).  They appear in the displays below as the first
premises.

*The least model is a fixpoint* of $`\mathit{Tp}`.

{stmt}`Tp_LHM`

{leanDecl Tp_LHM}

*It is the least pre-fixpoint:* every $`I` with $`\mathit{Tp}(I) \subseteq I`
contains it.

{stmt}`LHM_least`

{leanDecl LHM_least}

*It is the union of the finite iterates* $`\mathit{Tp}^n(\emptyset)`.

{stmt}`LHM_iff_Tpow`

{leanDecl LHM_iff_Tpow}

*It is the least fixpoint* in the sense of `OrderHom.lfp` from Mathlib
{pcite}`MathlibCommunity2020`.  This is
the one result of the section that uses `Classical.choice`, through Mathlib's
complete lattices.

{stmt}`LHM_eq_lfp`

{leanDecl LHM_eq_lfp}

*Pre-fixpoints are models.*  $`\mathit{Tp}(I) \subseteq I` holds if and only
if $`I` contains $`R` and satisfies every clause of $`P`.

{stmt}`prefixpoint_iff_model`

{leanDecl prefixpoint_iff_model}

*So the least model is the intersection of the models.*

{stmt}`LHM_iff_all_models`

{leanDecl LHM_iff_all_models}

Lloyd's theorems follow for non-modal Horn programs with no built-in
relations ($`R` empty, written `RNone`) and closed Σ-queries.

*Lloyd's theorem, proof-theoretic form.*  $`P \vdash S` if and only if $`S`
is true in the least model.

{stmt}`lloyd_prv_iff`

{leanDecl lloyd_prv_iff}

*Consequence and provability coincide* on these programs and queries.

{stmt}`lloyd_consequence_iff`

{leanDecl lloyd_consequence_iff}

*Van Emden and Kowalski* {pcite}`VanEmdenKowalski1976`.  A closed atom is in
the least model if and only if
it is a consequence of the program.

{stmt}`vanEmden_Kowalski`

{leanDecl vanEmden_Kowalski}

Two designed cells mark the limits of the method.  First, least models are
intuitionistic: $`P \lor (P \twoheadrightarrow \bot)` is not provable, refuted
by a two-world Herbrand model.

{stmt}`lem_not_prv`

{leanDecl lem_not_prv}

Second, a disjunction has no least Herbrand model: no interpretation that
makes $`P \lor Q` true is contained in every other.  This is why bodies are
split into Horn clauses first.

{stmt}`or_no_least_model`

{leanDecl or_no_least_model}

# Why two worlds

Lloyd's theory uses one world, and in one world $`\bigcirc` collapses: in a
one-world Herbrand model $`\bigcirc_q A` holds if and only if $`A` holds.

{stmt}`HTrue_circ`

{leanDecl HTrue_circ}

So a one-world model cannot tell “$`S` holds” from “$`S` holds up to a
constraint”, which is the distinction lax logic programming exists to make.
The least structure that separates them has two worlds $`0 \le 1`, with the
arrow modal, so that $`0 \models \bigcirc S` if and only if $`1 \models S`.
Each world is a least Herbrand model of a variant of the program.  World 0
carries $`M(\Pi^0)`, where $`\Pi^0` is the program with its modal clauses
deleted: the pessimistic reading, under which a modal clause says nothing.
World 1 carries $`M(\Pi^1)`, where $`\Pi^1` is the program with $`\bigcirc`
erased: the optimistic reading, in which every constraint is assumed
solvable.  The inclusion $`M(\Pi^0) \subseteq M(\Pi^1)` makes the
interpretation monotone.  In Lean the two worlds are `false` (world 0) and
`true` (world 1) of the model `llpModel`, every clause of $`\Theta` is assumed
closed, and for world 1 every modal clause carries the same $`q`.

*Theorem 7.5 at world 0.*  For a closed Σ-formula $`S`, $`\Theta \vdash S` if
and only if $`S` is forced at world 0.

{stmt}`thm_7_5_world0`

{leanDecl thm_7_5_world0}

*Theorem 7.5 at world 1.*  $`\Theta \vdash \bigcirc_q S` if and only if
$`S` is forced at world 1.

{stmt}`thm_7_5_world1`

{leanDecl thm_7_5_world1}

Solvability needs two more worlds, and they appear with the $`\bigcirc` pass
(Section 6): world 2 carries the least model of the concrete program over the
constraint relations, and above it a fallible world 3, through which
$`\bigcirc` imposes nothing at world 2.  Without world 3, forcing the
abstract clauses at world 0 would demand that every constraint be solvable.

# The running example

Example 9.5 of the 1997 report is followed through this section and the next
three.  Four predicate symbols are constraints, $`c_1, \ldots, c_4` (the
classifier $`\mathit{isC}_{95}` says so), and the program $`\mathit{ex}_{95}`
has three clauses $`\theta_1, \theta_2, \theta_3` of arity zero.  As formulas
({srcLink}`CLPExamples.run95_program`):

{stmt}`CLPExamples.run95_program`

The query is $`Q`.  The body of $`\theta_3` is a disjunction, so $`\theta_3`
has two indices, and splitting it gives one Horn clause per disjunct
($`\mathit{toHorn}` splits a clause and $`\mathit{form}` reads a Horn clause as
a formula; {srcLink}`CLPExamples.run95_horn`):

{stmt}`CLPExamples.run95_horn`

The engine of Section 8 finds two answers for $`Q`, $`c_1 \land c_3` and
$`c_2 \land c_4`, one for each disjunct
({srcLink}`CLPExamples.all95`).  The next three sections compute the first of
them in each of the ways the theory provides: Section 5 by Table 2, recorded
as a proof tree; Section 6 by the $`\bigcirc` pass; Section 7 by both
machines.  In the trees, $`\mathit{clause}_w` applies the clause at
position $`w` of the program, counting from $`0`, so $`\theta_3` is applied by
$`\mathit{clause}_2`.
