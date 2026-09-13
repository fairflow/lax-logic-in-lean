import Verso
import VersoManual
import VersoBlueprint
import LaxLogic.QLL

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Proof trees and Table 2" =>

The first pass: constraint logic programs with built-in constraint atoms,
their proof trees, the goal reduction of Table 2, and the soundness theorems
that connect them, all before `◯` enters.

# Proof trees

A proof tree records a derivation as data: constraint leaves, the connectives,
the witness of each existential, and each clause application with its
instance.  The typing relation says which trees prove which goals from which
program; the engine produces trees, a decision procedure checks them, and only
the checker's soundness is trusted.

```
inductive CProof where
  | top
  | cstr (B : String) (ts : List Tm)             -- a constraint leaf
  | andI (p q : CProof)
  | orL (p : CProof) | orR (p : CProof)
  | exI (t : Tm) (p : CProof)                    -- the witness term
  | clause (w : Nat) (ts : List Tm) (p : CProof) -- clause w at instance t̃
```

:::group "trees"
Proof trees, their constraints, and Table 2.
:::

:::definition "trees_cproof" (parent := "trees") (lean := "LaxLogic.QLL.CProof")
Proof trees with constraint leaves.
:::

:::definition "trees_ctyped" (parent := "trees") (uses := "trees_cproof, prog_clause") (lean := "LaxLogic.QLL.CTyped")
`CTyped isC Θ S p`: the tree `p` proves the Σ-goal `S` from `Θ`, constraint
atoms (`isC`) as leaves, clause applications instantiating a clause's bound
variables by the recorded terms.
:::

Definition 8.1 splits the constraint leaves into the active ones, not under a
clause application, and the latent ones, under one; `total` is all of them.

:::theorem "trees_total" (parent := "trees") (uses := "trees_cproof") (lean := "LaxLogic.QLL.CProof.total_equiv")
`total(p) ⊣⊢ latent(p) ∧ active(p)`.
:::

:::theorem "trees_prv_total" (parent := "trees") (uses := "trees_ctyped, logic_prv") (lean := "LaxLogic.QLL.CTyped.prv_total")
Answer soundness for trees: `CTyped Θ S p` gives `Θ ⊢ total(p) ⊃ S`.
:::

:::theorem "trees_checkC" (parent := "trees") (uses := "trees_ctyped") (lean := "LaxLogic.QLL.checkC_sound")
The checker is sound: `checkC Θ S p = true` gives `CTyped Θ S p`.
:::

# Table 2

A goal is `c □ φ₁,…,φₙ`, a store and a list of formulas.  A step applies one
rule at any position: Rule 1 moves a constraint atom into the store, guarded
by a parameter `ok`; Rule 2 chooses a disjunct; Rule 3 splits a conjunction;
Rule 4 opens an existential with a term; Rule 5 resolves an atom with a
clause.  Nothing in the rules fixes the order in which subgoals are selected.

:::definition "trees_step" (parent := "trees") (uses := "prog_clause") (lean := "LaxLogic.QLL.Step")
One step of Table 2, at any position of the goal list.
:::

:::theorem "trees_94" (parent := "trees") (uses := "trees_step, trees_ctyped") (lean := "LaxLogic.QLL.steps_forest")
Theorem 9.4.  A run `c □ φ̃ ⇝* c' □ ε` yields trees `p₁,…,pₙ` with `pᵢ`
proving `φᵢ` and `c' ⊣⊢ c ∧ total(p₁) ∧ … ∧ total(pₙ)`.  The parameter `ok`
plays no part: pruning restricts the search and never the soundness.
:::

:::theorem "trees_98" (parent := "trees") (uses := "trees_94, trees_prv_total") (lean := "LaxLogic.QLL.steps_sound")
Corollary 9.8.  `c □ φ̃ ⇝* c' □ ε` gives `Θ ⊢ c' ⊃ c ∧ φ₁ ∧ … ∧ φₙ`.
:::

# World 2 without `◯`

With `R` interpreting the constraint predicates and `Θ` non-modal and well
formed, for a closed Σ-goal:

:::theorem "trees_world2" (parent := "trees") (uses := "trees_ctyped, prog_lhm") (lean := "LaxLogic.QLL.world2_free")
`S` is true in the least model over `R` iff some tree proves `S` with
`total(p)` true in `R`.  This is the completeness half of the conventional
Theorem 6.1 in tree form.
:::
