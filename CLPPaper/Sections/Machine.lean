import Verso
import VersoManual
import VersoBlueprint
import LaxLogic.QLL

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "SLD and SLD◯: one machine for both passes" =>

Table 2 rewrites a flat goal list and forgets the derivation; Fig. 3 is a
proof-tree calculus and does no rewriting.  This section gives both passes
the same operational form.  A state is a partial proof tree — a proof tree
with open leaves — and a step expands one open leaf by one rule.  Table 2's
goal list is the projection of the tree onto its open leaves, and the proof
tree of Theorem 9.4 is the tree itself once no leaf is open.

# The rules, in one format

An open leaf `S` is replaced by a node whose open leaves are the new goals:

```
rule     open leaf S           new node                     store (SLD only)
top      ⊤                     ⊤                            —
cstr     B(t̃), isC B           B(t̃) leaf                    c ∧ B(t̃), if ok
and      A ∧ B                 ∧I [A] [B]                   —
orL/orR  A ∨ B                 ∨I₁ [A]  /  ∨I₂ [B]          —
ex       ∃x.A                  ∃I t [A[t]],  t closed       —
clause   P(t̃)                  clause w t̃ [S_w[t̃]]          —
```

SLD runs on a concrete program and threads a store.  SLD◯ runs on the
abstract program, whose clause heads are all modal and whose bodies have `⊤`
where the constraints were, so `cstr` has become `top` and there is no store:
the constraint is extracted from the finished tree.  Every judgement of SLD◯
is lax, so `◯` appears in no rule; it appears in the QLL derivation that
justifies each — `◯I ⊤I` for `top`; `◯E, ◯E, ◯I ∧I` for `and`; `◯E, ◯I ∨I` for
the disjunction rules; `◯E, ◯I ∃I` for `ex`; and `∀E` on `∀x̃. S♯ ⊃ ◯P(x̃)`,
`◯E` on the body's `◯S♯`, `⊃E` for `clause`.  These are the cases of the
soundness proof of the abstract calculus.

:::group "machine"
Partial proof trees and the two expansion relations.
:::

:::definition "mach_ptree" (parent := "machine") (uses := "trees_cproof") (lean := "LaxLogic.QLL.SLD.PTree")
A `CProof` with open leaves; `opens` lists them left to right, `store`
conjoins the constraint leaves reached so far, `close` gives the `CProof` when
no leaf is open.
:::

:::definition "mach_expand" (parent := "machine") (uses := "mach_ptree, prog_clause") (lean := "LaxLogic.QLL.SLD.Expand")
SLD: one rule at one open leaf, store `c` to `c'`, with congruence rules
through every node so the position is free.
:::

:::definition "mach_expandA" (parent := "machine") (uses := "abs_aproof") (lean := "LaxLogic.QLL.SLD.ExpandA")
SLD◯: the same rules on abstract partial trees, `cstr` gone, no store.
:::

# The projection to Table 2, and lifting

:::theorem "mach_goal_step" (parent := "machine") (uses := "mach_expand, trees_step") (lean := "LaxLogic.QLL.SLD.SLDStep.goal_step")
Every SLD step is a Table 2 step on the projections.
:::

:::theorem "mach_lift_tree" (parent := "machine") (uses := "mach_expand") (lean := "LaxLogic.QLL.SLD.PTree.lift")
A rule shape applied at a given open leaf of a tree — located by a split of
`opens` — is an expansion of the tree.
:::

:::theorem "mach_lift" (parent := "machine") (uses := "mach_lift_tree, trees_step") (lean := "LaxLogic.QLL.Step.lift")
Lifting: a Table 2 step from a tree's goal list is an expansion of that tree.
:::

:::theorem "mach_lift_run" (parent := "machine") (uses := "mach_lift") (lean := "LaxLogic.QLL.Steps.lift")
Runs lift: a Table 2 run from one goal is an SLD run on one tree.
:::

:::theorem "mach_goal_run" (parent := "machine") (uses := "mach_goal_step") (lean := "LaxLogic.QLL.SLD.SLDSteps.goal")
Runs project.  With the previous node, Table 2 and the machine are the same
relation on single goals, in both directions.
:::

# Soundness, and Theorem 9.4 as an invariant

Typing is preserved by every step, and a closed typed tree is a proof tree;
the store is `c₀ ∧ store` throughout the run.

:::theorem "mach_store" (parent := "machine") (uses := "mach_expand, trees_ctyped") (lean := "LaxLogic.QLL.SLD.SLDSteps.store")
A run from `c₀ □ [S]` that closes its tree to `q` has `q` a proof tree of `S`
and `c ⊣⊢ c₀ ∧ total q`.  Theorem 9.4 in machine form.
:::

:::theorem "mach_prv" (parent := "machine") (uses := "mach_store, trees_prv_total") (lean := "LaxLogic.QLL.SLD.SLDSteps.prv")
Soundness of SLD with respect to QLL: the finished tree proves `total q ⊃ S`.
:::

:::theorem "mach_prvC" (parent := "machine") (uses := "mach_expandA, abs_prv") (lean := "LaxLogic.QLL.SLD.SLDCSteps.prv")
Soundness of SLD◯ with respect to QLL: a run from `[S]` that closes its tree
gives an abstract proof, hence `Θ♯ ⊢ ◯S`.
:::

# The simulation under `toA`

:::theorem "mach_toA" (parent := "machine") (uses := "mach_expand, mach_expandA, abs_toA") (lean := "LaxLogic.QLL.SLD.Expand.toA")
Every SLD step on `Θ` is an SLD◯ step on `Θ♯` at the image leaf: `cstr`
becomes `top`, every other rule is itself.  Heads must not be constraints.
:::

:::theorem "mach_toA_run" (parent := "machine") (uses := "mach_toA") (lean := "LaxLogic.QLL.SLD.SLDSteps.toA")
The simulation on runs.
:::

The converse simulation holds only when `ok` accepts every store; under
pruning it fails at `cstr`, and that failure is the exact content of pruning.
It is stated and not yet built.

# The switching lemma, and pruning put back

Expansions at two different leaves of the same tree commute.  The statement
needs the leaf's position, so `ExpandAt` is `Expand` indexed by the position
of the expanded leaf in `opens`.  It is stated without pruning for a reason
that is itself the point: two constraint leaves each consistent with the
store need not be jointly consistent, so under `ok = satisfiable` each single
step is allowed and neither can be completed.

:::definition "mach_expandAt" (parent := "machine") (uses := "mach_expand") (lean := "LaxLogic.QLL.SLD.ExpandAt")
`Expand` with the index of the expanded leaf.
:::

:::theorem "mach_diamond" (parent := "machine") (uses := "mach_expandAt") (lean := "LaxLogic.QLL.SLD.ExpandAt.diamond")
The switching lemma: without pruning, expansions at leaves `i ≠ j` have a
common successor reached either way, with stores equal up to `⊣⊢`.
:::

:::theorem "mach_noprune" (parent := "machine") (uses := "mach_expand") (lean := "LaxLogic.QLL.SLD.SLDSteps.noPrune_iff")
Pruning is invisible to answers.  For `ok` closed under provable weakening —
satisfiability is — and an acceptable initial store, the pruned runs are
exactly the unpruned runs whose final store passes `ok`.  So pruning changes
which prefixes are explored, never which trees are reachable with an
acceptable store.
:::

The implemented test `satOK` is not closed under weakening, because it
accepts nonlinear stores it cannot decide; so strategy independence holds for
the ideal test and can fail for the engine's.  What is proved about
strategies is therefore: answers are independent of the selection order
(Theorem 9.4 is position-free, and so is its machine form); the unpruned
search space is confluent under switching; and pruning by an exact test
changes neither.  Completeness of the machines — that every typed tree is the
log of some run — and the Herbrand corollaries through `world2_free` and
Theorem 7.5 remain OPEN.
