import Verso
import VersoManual
import LaxLogic.QLL
import CLPPaper.Src

open Verso.Genre
open Verso.Genre.Manual
open CLPPaper

#doc (Manual) "Proof trees and Table 2" =>

The first pass: constraint logic programs with built-in constraint atoms,
their proof trees, the goal reduction of Table 2, and the soundness theorems
that connect them, all before $`\bigcirc` enters.

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

Proof trees with constraint leaves.

{docstring LaxLogic.QLL.CProof +allowMissing}

{srcLink}`LaxLogic.QLL.CProof`

`CTyped isC Θ S p`: the tree `p` proves the Σ-goal `S` from `Θ`, constraint
atoms (`isC`) as leaves, clause applications instantiating a clause's bound
variables by the recorded terms.

{docstring LaxLogic.QLL.CTyped +allowMissing}

{srcLink}`LaxLogic.QLL.CTyped`

Definition 8.1 splits the constraint leaves into the active ones, not under a
clause application, and the latent ones, under one; `total` is all of them.

$$`\mathit{total}(p) \dashv\vdash \mathit{latent}(p) \land \mathit{active}(p)`

{docstring LaxLogic.QLL.CProof.total_equiv +allowMissing}

{srcLink}`LaxLogic.QLL.CProof.total_equiv`

Answer soundness for trees: `CTyped Θ S p` gives $`\Theta \vdash \mathit{total}(p) \supset S`.

{docstring LaxLogic.QLL.CTyped.prv_total +allowMissing}

{srcLink}`LaxLogic.QLL.CTyped.prv_total`

The checker is sound: `checkC Θ S p = true` gives `CTyped Θ S p`.

{docstring LaxLogic.QLL.checkC_sound +allowMissing}

{srcLink}`LaxLogic.QLL.checkC_sound`

# Table 2

A goal is `c □ φ₁,…,φₙ`, a store and a list of formulas.  A step applies one
rule at any position: Rule 1 moves a constraint atom into the store, guarded
by a parameter `ok`; Rule 2 chooses a disjunct; Rule 3 splits a conjunction;
Rule 4 opens an existential with a term; Rule 5 resolves an atom with a
clause.  Nothing in the rules fixes the order in which subgoals are selected.

One step of Table 2, at any position of the goal list.

{docstring LaxLogic.QLL.Step +allowMissing}

{srcLink}`LaxLogic.QLL.Step`

Theorem 9.4.  A run $`c \square \tilde{\varphi } \rightsquigarrow * c' \square \varepsilon` yields trees `p₁,…,pₙ` with `pᵢ`
proving `φᵢ` and $`c' \dashv\vdash c \land \mathit{total}(p_1) \land … \land \mathit{total}(p_n)`.  The parameter `ok`
plays no part: pruning restricts the search and never the soundness.

{docstring LaxLogic.QLL.steps_forest +allowMissing}

{srcLink}`LaxLogic.QLL.steps_forest`

Corollary 9.8.  $`c \square \tilde{\varphi } \rightsquigarrow * c' \square \varepsilon` gives $`\Theta \vdash c' \supset c \land \varphi _1 \land … \land \varphi _n`.

{docstring LaxLogic.QLL.steps_sound +allowMissing}

{srcLink}`LaxLogic.QLL.steps_sound`

# World 2 without `◯`

With `R` interpreting the constraint predicates and `Θ` non-modal and well
formed, for a closed Σ-goal:

`S` is true in the least model over `R` iff some tree proves `S` with
`total(p)` true in `R`.  This is the completeness half of the conventional
Theorem 6.1 in tree form.

{docstring LaxLogic.QLL.world2_free +allowMissing}

{srcLink}`LaxLogic.QLL.world2_free`

