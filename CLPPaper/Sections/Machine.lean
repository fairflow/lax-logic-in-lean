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

This section is new; the 1997 report has no counterpart.  It adds no rules.
SLD is the rule set of $`\mathsf{CTyped}` (Section 5.1) applied at an open
leaf of a _partial proof tree_, a proof tree with open leaves; SLD◯ is the
rule set of $`\mathsf{ATyped}` (Section 6.1) applied in the same way; and
Table 2 is SLD with the tree forgotten (the map at the start of Section 5).
What is new is that the tree is kept during the run: Table 2 rewrites a flat
goal list and forgets the derivation, and Fig. 3 describes finished
derivations and does not run.  Keeping the tree gives four things.

* _Theorem 9.4 becomes an invariant._  Section 5.2 proves it by reconstructing
  proof trees from a finished Table 2 run (`steps_forest`).  Here the tree is
  part of the state, and after every step the store is the initial store
  conjoined with the constraint leaves reached so far
  (`SLD.SLDSteps.store`, Section 7.3).
* _The $`\bigcirc` pass gets an operational semantics,_ which the 1997 report
  does not give: Fig. 3 says which abstract proofs exist, not how one is
  built.  A run of SLD◯ builds an abstract proof one rule at a time, and is
  sound for QLL (`SLD.SLDCSteps.prv`, Section 7.3).
* _The two passes can be compared step by step._  Every SLD step on
  $`\Theta` is an SLD◯ step on $`\Theta^\sharp` at the image leaf
  (`SLD.Expand.toA` and `SLD.SLDSteps.toA`, Section 7.4).  This is the
  operational counterpart of Theorem 9.7, which compares only finished
  computations.  The converse simulation is OPEN.
* _The switching lemma and the pruning theorem can be stated._  Both are about
  derivations.  The switching lemma says that expansions at two different
  leaves of a tree commute and reach the same tree; the pruning theorem says
  which trees remain reachable under pruning.  A Table 2 state records the
  open goals but not the derivation they belong to, and different derivations
  can reach the same goal list, so in Table 2 neither statement could say that
  the same proof tree is reached.  Both are in Section 7.5, as
  `SLD.ExpandAt.diamond` and `SLD.SLDSteps.noPrune_iff`.

Table 2 keeps its role.  The 1997 report's theorems are stated for it, and
Section 7.2 proves that Table 2 and SLD are the same relation on single goals,
so every result of this section can be read back in Table 2.  Section 7.6
runs the example of Sections 4 to 6 in both machines.

# The rules, in one format

An open leaf labelled $`S` is replaced by a node whose open leaves are the new
goals.  An open leaf labelled $`A` is written $`\langle A \rangle`, and the
other nodes with the names of their rules, as in the displays.

:::wtable (widths := "0.12 0.20 0.38 0.30") +header
*
  * Rule
  * Open leaf
  * New node
  * Store (SLD only)
*
  * $`\mathit{top}`
  * $`\top`
  * $`{\top}\mathrm{I}`
  * unchanged
*
  * $`\mathit{cstr}`
  * $`B(\tilde{t})`, $`B` a constraint
  * the leaf $`B(\tilde{t})`
  * $`c \land B(\tilde{t})`, if $`\mathit{ok}`
*
  * $`\mathit{and}`
  * $`A \land B`
  * $`{\land}\mathrm{I}(\langle A \rangle,\, \langle B \rangle)`
  * unchanged
*
  * $`\mathit{orL}`, $`\mathit{orR}`
  * $`A \lor B`
  * $`{\lor}\mathrm{I}_1(\langle A \rangle)`, respectively $`{\lor}\mathrm{I}_2(\langle B \rangle)`
  * unchanged
*
  * $`\mathit{ex}`
  * $`\exists x.\, A`
  * $`{\exists}\mathrm{I}_t(\langle A[t/x] \rangle)`, $`t` closed
  * unchanged
*
  * $`\mathit{clause}`
  * $`P(\tilde{t})`
  * $`\mathit{clause}_w^{\tilde{t}}(\langle S_w[\tilde{t}] \rangle)`
  * unchanged
:::

SLD runs on a concrete program and threads a store.  SLD◯ runs on the
abstract program, whose clause heads are all modal and whose bodies have
$`\top` where the constraints were, so $`\mathit{cstr}` has become
$`\mathit{top}` and there is no store: the constraint is extracted from the
finished tree.  The nodes it builds are those of Fig. 3: $`\mathit{val}`,
$`{\land}{\bigcirc}`, $`{\lor}{\bigcirc}_1`, $`{\lor}{\bigcirc}_2`,
$`{\exists}{\bigcirc}_t` and $`{\twoheadrightarrow}{\bigcirc}_w`.  Every
judgement of SLD◯ is lax, so $`\bigcirc` appears in no
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
leaf $`\langle S \rangle` (`hole S` in Lean).  The function $`\mathit{opens}` lists the open
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

# The running example in SLD and SLD◯

The Table 2 run of Section 5.3, replayed on partial trees: each step expands
one open leaf, by the rule that Table 2 applies to the corresponding goal
({srcLink}`CLPExamples.run95_sld`).

{stmt}`CLPExamples.run95_sld`

The goal of each state, its store with its open leaves read from left to
right, is the Table 2 state in the same row ({srcLink}`CLPExamples.run95_goals`);
this is the projection of Section 7.2 on this run.  The last tree has no open
leaf, and closes to the proof tree of Section 5.3, as Theorem 9.4 in machine
form requires ({srcLink}`CLPExamples.run95_close`):

{stmt}`CLPExamples.run95_close`

The same six rules on the abstract program of Section 6.3 make an SLD◯ run.
The constraint goals $`c_1` and $`c_3` have become $`\top`, closed by
$`\mathit{top}` instead of $`\mathit{cstr}`, and there is no store
({srcLink}`CLPExamples.run95_sldc`):

{stmt}`CLPExamples.run95_sldc`

Each tree of this run is the image under $`\mathit{toA}` of the SLD tree in
the same row ({srcLink}`CLPExamples.run95_toA`), which is the simulation of
Section 7.4 on this run.  The last tree closes to the abstract proof of
Section 6.3, from which extraction recovers the answer of the Table 2 run
(Theorem 9.7; {srcLink}`CLPExamples.run95_closeA`):

{stmt}`CLPExamples.run95_closeA`
