import Verso
import VersoManual
import LaxLogic.QLL
import CLPPaper.Src
import CLPPaper.Cite
import CLPPaper.Math
import CLPPaper.Layout

open Verso.Genre
open Verso.Genre.Manual
open CLPPaper CLPPaper.Math CLPPaper.Cite
open LaxLogic.QLL LaxLogic.QLL.SLD

#doc (Manual) "Pruning and Prolog's cut" =>

This section is new; the 1997 report has no counterpart, and the section has
no results of its own.  Pruning by a consistency test is the one place where
the machine of Section 7 discards part of the search, which raises the
question of how it compares with Prolog's cut, the best-known pruning
operator.  The section asks whether there is a published correlation between
constraint pruning in CLP and Prolog's cut, says what it is, and relates it to
the switching lemma and the pruning theorem of Section 7.

# What is published

The link runs through committed choice with constraint guards.

* The logical semantics of the ALPS class {pcite}`Maher1987` governs
  commitment by constraint entailment.
* Concurrent constraint programming {pcite}`Saraswat1993` makes _ask_ (block
  until the store entails the guard) and _tell_ its primitives.
* The Andorra Kernel Language {pcite}`HaridiJanson1990` has a conditional
  choice, which is Prolog's if-then-else guarded by entailment; a committed
  choice; and a nondeterminate choice that waits.  Its logical account
  {pcite}`Franzen1991` restricts pruning to _quiet_ guards, entailed by the
  store rather than merely consistent with it, because quiet pruning is
  insensitive to execution order.
* A survey of pruning operators {pcite}`Naish1995` records that they are
  typically not declarative and cost completeness or soundness.
  {cite}`Andrews2003` shows that Prolog with negation as failure and cut lacks
  the witness properties, and gives a restriction that keeps cut's
  first-solution behaviour with them.  {cite}`PirogStaton2017` show that cut
  makes backtracking the monad of free left-zero monoids.

On the CLP side, failure pruning is the transition $`\rightarrow_s` of
{cite}`JaffarMaher1994`; branch and bound {pcite}`VanHentenryck1989` prunes by
bounds and is sound for optimal answers only; Constraint Handling Rules
{pcite}`Fruhwirth1998` are committed-choice guarded rules that simplify the
store; monadic constraint programming {pcite}`SCHRIJVERSSTUCKEYWADLER2009`
treats search strategies and pruning as composable transformers of a search
tree; and {cite}`GochtMcCreeshNordstrom2022` log every pruning step of a
constraint solver as a checkable cutting-planes proof.

# How it lines up

:::wtable (widths := "0.15 0.32 0.20 0.33") +header
*
  * Pruning
  * Condition
  * Order dependence
  * Certificate here
*
  * failure
  * the store is unsatisfiable
  * none
  * Farkas multipliers (Section 8)
*
  * quiet commit
  * the guard is entailed by the store
  * little
  * entailment by refutation (Section 8)
*
  * bound
  * the branch cannot beat the incumbent
  * none, for optima
  * a lower-bound certificate (Section 8)
*
  * cut
  * first success in textual order
  * essential
  * none possible
:::

Failure pruning is the zero of the constraint monoid:
$`\bot \land c \dashv\vdash \bot \dashv\vdash c \land \bot`, a two-sided zero.
That is why it commutes with everything, and why Theorem 9.4 holds for any
$`\mathit{ok}`.  Cut is a left zero and is not commutative.  Selection
independence rests on the commutativity of the store's conjunction (Section 6),
so cut cannot live in the constraint monoid: it lives in the search, and its
left-zero law is the precise point where commutativity fails.  Quiet commit
sits between the two: its pruning is justified by an entailment, so it can be
checked.

# What the machine adds

The switching lemma and the pruning theorem of Section 7 make this exact for
the failure case.  Without pruning the search is confluent under switching;
with an exact satisfiability test, the pruned runs are precisely the unpruned
runs whose final store is satisfiable, so failure pruning is independent of
order and invisible to answers.  Cut has no such theorem, and the reason is
visible in the same place: it is not a function of the store.

The pruning theorem can be read as the formal content of “failure pruning is
green”: it changes the prefixes explored, not the trees reachable with an
acceptable store.

Three directions would build on this, each to start with a statement and
designed cells: a certified pruning log (unsatisfiable, dominated, or not
selected under a quiet commit, each with its certificate); quiet commit in lax
logic programs, with answer soundness as the first target; and the cut of
{cite}`PirogStaton2017` added to the extraction monad, with the failure of selection
independence as a designed countermodel, which would be a formal version,
inside the lax framework, of “cut is non-logical”.
