import Verso
import VersoManual
import LaxLogic.QLL
import CLPPaper.Src
import CLPPaper.Decl
import CLPPaper.Math
import CLPPaper.Layout

open Verso.Genre
open Verso.Genre.Manual
open CLPPaper CLPPaper.Math
open LaxLogic.QLL LaxLogic.QLL.SLD
open LaxLogic.QLL.Form (openAt instAll strip)

#doc (Manual) "SLD and SLD◯: one machine for both passes" =>

This section is not in the draft.  Table 2 rewrites a flat goal list and
forgets the derivation; Fig. 3 is a proof-tree calculus and does no rewriting.
Here both passes are given the same operational form.  A state is a _partial
proof tree_, a proof tree with open leaves, and a step expands one open leaf
by one rule.  Table 2's goal list is the list of open leaves of the tree, and
the proof tree of Theorem 9.4 is the tree itself once no leaf is open.  The
section proves that the machine and Table 2 are the same relation on single
goals, restates Theorem 9.4 as an invariant of the machine, proves both
machines sound, simulates the concrete machine in the abstract one, and proves
the switching lemma and the exact effect of pruning.

# The rules, in one format

An open leaf labelled $`S` is replaced by a node whose open leaves are the new
goals.  Brackets $`[A]` mark an open leaf.

:::wtable (widths := "0.12 0.20 0.38 0.30") +header
*
  * Rule
  * Open leaf
  * New node
  * Store (SLD only)
*
  * $`\mathit{top}`
  * $`\top`
  * $`\top`
  * unchanged
*
  * $`\mathit{cstr}`
  * $`B(\tilde{t})`, $`B` a constraint
  * the leaf $`B(\tilde{t})`
  * $`c \land B(\tilde{t})`, if $`\mathit{ok}`
*
  * $`\mathit{and}`
  * $`A \land B`
  * $`{\land}I\;[A]\;[B]`
  * unchanged
*
  * $`\mathit{orL}`, $`\mathit{orR}`
  * $`A \lor B`
  * $`{\lor}I_1\;[A]`, respectively $`{\lor}I_2\;[B]`
  * unchanged
*
  * $`\mathit{ex}`
  * $`\exists x.\, A`
  * $`{\exists}I\;t\;[A[t/x]]`, $`t` closed
  * unchanged
*
  * $`\mathit{clause}`
  * $`P(\tilde{t})`
  * $`\mathit{clause}\;w\;\tilde{t}\;[S_w[\tilde{t}]]`
  * unchanged
:::

SLD runs on a concrete program and threads a store.  SLD◯ runs on the
abstract program, whose clause heads are all modal and whose bodies have
$`\top` where the constraints were, so $`\mathit{cstr}` has become
$`\mathit{top}` and there is no store: the constraint is extracted from the
finished tree.  Every judgement of SLD◯ is lax, so $`\bigcirc` appears in no
rule; it appears in the QLL derivation that justifies each rule, and these
derivations are the cases of the proof that abstract proofs are proofs
(Section 6):

:::wtable (widths := "0.25 0.75") +header
*
  * Rule of SLD◯
  * Justifying QLL derivation
*
  * $`\mathit{top}`
  * $`(\bigcirc I)` after $`(\top I)`
*
  * $`\mathit{and}`
  * $`(\bigcirc E)`, $`(\bigcirc E)`, then $`(\bigcirc I)` after $`({\land}I)`
*
  * $`\mathit{orL}`, $`\mathit{orR}`
  * $`(\bigcirc E)`, then $`(\bigcirc I)` after $`({\lor}I_1)` or $`({\lor}I_2)`
*
  * $`\mathit{ex}`
  * $`(\bigcirc E)`, then $`(\bigcirc I)` after $`({\exists}I)`
*
  * $`\mathit{clause}`
  * $`({\forall}E)` on $`\forall \tilde{x}.\, S^\sharp \twoheadrightarrow \bigcirc P(\tilde{x})`, $`(\bigcirc E)` on the body's $`\bigcirc S^\sharp`, $`({\twoheadrightarrow}E)`
:::

A partial tree has the constructors of a proof tree and one more, an open
leaf $`\mathit{hole}(S)`.  The function $`\mathit{opens}` lists the open
leaves from left to right, $`\mathit{store}` conjoins the constraint leaves
reached so far, and $`\mathit{close}` returns the proof tree when no leaf is
open.

{stmt}`SLD.PTree`

{leanDecl SLD.PTree}

$`\mathsf{Expand}(\mathit{isC}, \Theta, \mathit{ok}, c, p, p', c')`: one SLD
rule applied at one open leaf of $`p`, taking the store $`c` to $`c'`.
Congruence rules pass through every node, so the position of the leaf is
free.

{stmt}`SLD.Expand`

{leanDecl SLD.Expand}

$`\mathsf{ExpandA}(\Theta, q, a, a')`: the same rules on abstract partial
trees, with $`\mathit{cstr}` gone and no store.

{stmt}`SLD.ExpandA`

{leanDecl SLD.ExpandA}

# The projection to Table 2, and lifting

A machine state is a store and a forest of partial trees, one per initial
goal; its _goal_ is the store with the open leaves of the forest.

*Projection.*  Every SLD step is a Table 2 step between the goals.

{stmt}`SLD.SLDStep.goal_step`

{leanDecl SLD.SLDStep.goal_step}

*Lifting a rule.*  A rule of Table 2 applied at a given open leaf of a tree
(located by splitting $`\mathit{opens}(p)` as $`l_1 \mathbin{+\!\!+} [S] \mathbin{+\!\!+} r_1`)
is an expansion of the tree.

{stmt}`SLD.PTree.lift`

{leanDecl SLD.PTree.lift}

*Lifting a step.*  A Table 2 step from a tree's goal list is an expansion of
that tree.

{stmt}`Step.lift`

{leanDecl Step.lift}

*Lifting a run.*  A Table 2 run from one goal is an SLD run on one tree.

{stmt}`Steps.lift`

{leanDecl Steps.lift}

*Projecting a run.*  With the previous result, Table 2 and the machine are
the same relation on single goals, in both directions.

{stmt}`SLD.SLDSteps.goal`

{leanDecl SLD.SLDSteps.goal}

# Soundness, and Theorem 9.4 as an invariant

Typing is preserved by every step, a closed typed tree is a proof tree, and
the store is $`c_0 \land \mathit{store}` throughout a run.

*Theorem 9.4, machine form.*  A run from $`c_0 \mathrel{\square} [S]` that
closes its tree to $`q` has $`q` a proof tree of $`S` and
$`c \dashv\vdash c_0 \land \mathit{total}(q)`.

{stmt}`SLD.SLDSteps.store`

{leanDecl SLD.SLDSteps.store}

*Soundness of SLD with respect to QLL.*  The finished tree proves
$`\mathit{total}(q) \twoheadrightarrow S`.

{stmt}`SLD.SLDSteps.prv`

{leanDecl SLD.SLDSteps.prv}

*Soundness of SLD◯ with respect to QLL.*  A run from $`[S]` that closes its
tree gives an abstract proof, hence $`\Theta^\sharp \vdash \bigcirc S`.

{stmt}`SLD.SLDCSteps.prv`

{leanDecl SLD.SLDCSteps.prv}

These three results use `Classical.choice`, through a lemma about list
lengths that could be avoided (Section 12).

# The simulation under abstraction

*Simulation of a step.*  If no clause head is a constraint, every SLD step on
$`\Theta` is an SLD◯ step on $`\Theta^\sharp` at the image leaf:
$`\mathit{cstr}` becomes $`\mathit{top}`, and every other rule is itself.

{stmt}`SLD.Expand.toA`

{leanDecl SLD.Expand.toA}

*Simulation of a run.*

{stmt}`SLD.SLDSteps.toA`

{leanDecl SLD.SLDSteps.toA}

The converse simulation, from SLD◯ to SLD, holds only when $`\mathit{ok}`
accepts every store; under pruning it fails at $`\mathit{cstr}`, and that
failure is the exact content of pruning.  The converse is stated and not yet
built (OPEN).

# The switching lemma, and pruning put back

Expansions at two different leaves of the same tree commute.  The statement
needs the position of the leaf, so $`\mathsf{ExpandAt}` is
$`\mathsf{Expand}` indexed by the position of the expanded leaf in
$`\mathit{opens}`.  The lemma is stated without pruning, for a reason that is
itself the point: two constraint leaves, each consistent with the store, need
not be jointly consistent, so under $`\mathit{ok} = \text{satisfiable}` each
single step is allowed and neither can be completed after the other.

{stmt}`SLD.ExpandAt`

{leanDecl SLD.ExpandAt}

*The switching lemma.*  Without pruning, expansions at leaves $`i \ne j` have
a common successor, reached either way, with stores equal up to
$`\dashv\vdash`.

{stmt}`SLD.ExpandAt.diamond`

{leanDecl SLD.ExpandAt.diamond}

*Pruning is invisible to answers.*  If $`\mathit{ok}` is closed under provable
weakening, as satisfiability is, and the initial store passes $`\mathit{ok}`,
then the pruned runs are exactly the unpruned runs whose final store passes
$`\mathit{ok}`.  Pruning changes which prefixes are explored, never which trees
are reachable with an acceptable store.

{stmt}`SLD.SLDSteps.noPrune_iff`

{leanDecl SLD.SLDSteps.noPrune_iff}

The test the engine implements, `satOK`, is not closed under weakening,
because it accepts nonlinear stores it cannot decide; so strategy independence
holds for the ideal test and can fail for the engine's.  What is proved about
strategies is therefore this: answers are independent of the selection order
(Theorem 9.4 is position-free, and so is its machine form); the unpruned
search space is confluent under switching; and pruning by an exact test
changes neither.  Completeness of the machines (every typed tree is the log of
some run) and the corollaries for the Herbrand models through Section 5's
completeness at world 2 and Theorem 7.5 remain OPEN.
