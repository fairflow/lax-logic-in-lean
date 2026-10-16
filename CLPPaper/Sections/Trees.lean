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
open LaxLogic.QLL.Form (openAt instAll)

#doc (Manual) "Proof trees and Table 2" =>

This section is the first pass of the draft, before $`\bigcirc` enters:
constraint logic programs with built-in constraint atoms, their proof trees
with the draft's split of constraint leaves into active and latent ones
(Definition 8.1), the goal reduction of Table 2, and the soundness theorems
that connect them (Theorem 9.4 and Corollary 9.8).  It ends with the
completeness of proof trees for the least model over the constraint relations.

Throughout, $`\Theta` is a program and $`\mathit{isC}` says which predicate
symbols are constraints.

# Proof trees

A proof tree records a derivation as data: constraint leaves, the connectives,
the witness of each existential, and each clause application with the clause's
position $`w` in the program and the terms $`\tilde{t}` at which it is
instantiated.  The engine of Section 8 produces trees, a decision procedure
checks them, and only the checker's soundness is trusted.

{stmt}`CProof`

{leanDecl CProof}

$`\mathsf{CTyped}(\mathit{isC}, \Theta, S, p)` says that the tree $`p` proves
the Σ-goal $`S` from $`\Theta`.  A constraint atom is a leaf.  The clause rule
applies clause $`w` of $`\Theta`, which must be non-modal, at closed terms
$`\tilde{t}` of the right number: from a proof of the instantiated body it
concludes the instantiated head.  In Lean the conclusion is an atom
$`P(\tilde{u})`, with premises saying that $`P` is the clause's head predicate
and that $`\tilde{u}` is its head variables instantiated at $`\tilde{t}`.

{stmt}`CTyped`

{leanDecl CTyped}

Definition 8.1 splits the constraint leaves of a tree into the _active_ ones,
not under a clause application, and the _latent_ ones, under one.
$`\mathit{total}(p)` is the conjunction of all of them.

*Definition 8.1, checked.*  $`\mathit{total}(p) \dashv\vdash \mathit{latent}(p) \land \mathit{active}(p)`.

{stmt}`CProof.total_equiv`

{leanDecl CProof.total_equiv}

*Answer soundness for trees.*  If $`p` proves $`S` from $`\Theta`, then
$`\Theta \vdash \mathit{total}(p) \twoheadrightarrow S`.  The constraint atoms
are uninterpreted: no constraint theory is used.

{stmt}`CTyped.prv_total`

{leanDecl CTyped.prv_total}

*The checker is sound.*  A tree that the Boolean function `checkC` accepts is
a proof tree of the goal.  This is the only part of answer checking that has
to be trusted, and it is proved.

{stmt}`checkC_sound`

{leanDecl checkC_sound}

# Table 2

A goal $`c \mathrel{\square} \varphi_1, \ldots, \varphi_n` is a store $`c` and
a list of formulas.  A step applies one rule to one formula of the list,
wherever it stands; in the table, $`\tilde{\varphi}` and $`\tilde{\psi}` are
the formulas before and after it.  Nothing in the rules fixes the order in
which subgoals are selected.

:::wtable (widths := "0.12 0.50 0.38") +header
*
  * Rule
  * Step
  * Condition
*
  * 1
  * $`c \mathrel{\square} \tilde{\varphi}, B(\tilde{t}), \tilde{\psi} \;\rightsquigarrow\; c \land B(\tilde{t}) \mathrel{\square} \tilde{\varphi}, \tilde{\psi}`
  * $`B` is a constraint predicate and $`\mathit{ok}(c \land B(\tilde{t}))`
*
  * 2
  * $`c \mathrel{\square} \tilde{\varphi}, A_1 \lor A_2, \tilde{\psi} \;\rightsquigarrow\; c \mathrel{\square} \tilde{\varphi}, A_i, \tilde{\psi}`
  * $`i = 1, 2`
*
  * 3
  * $`c \mathrel{\square} \tilde{\varphi}, A \land B, \tilde{\psi} \;\rightsquigarrow\; c \mathrel{\square} \tilde{\varphi}, A, B, \tilde{\psi}`
  * —
*
  * 4
  * $`c \mathrel{\square} \tilde{\varphi}, \exists x.\, A, \tilde{\psi} \;\rightsquigarrow\; c \mathrel{\square} \tilde{\varphi}, A[t/x], \tilde{\psi}`
  * $`t` closed
*
  * 5
  * $`c \mathrel{\square} \tilde{\varphi}, P(\tilde{t}), \tilde{\psi} \;\rightsquigarrow\; c \mathrel{\square} \tilde{\varphi}, S[\tilde{t}/\tilde{x}], \tilde{\psi}`
  * $`\forall \tilde{x}.\, S \twoheadrightarrow P(\tilde{x})` a non-modal clause of $`\Theta`, $`\tilde{t}` closed
*
  * $`\top`
  * $`c \mathrel{\square} \tilde{\varphi}, \top, \tilde{\psi} \;\rightsquigarrow\; c \mathrel{\square} \tilde{\varphi}, \tilde{\psi}`
  * —
:::

The parameter $`\mathit{ok}` is the consistency test: pruning by it restricts
the search.  In Lean the goal lists before and after a step are carried as
equations $`\mathit{gs} = \tilde{\varphi} \mathbin{+\!\!+} [\varphi] \mathbin{+\!\!+} \tilde{\psi}`
rather than computed in the indices (Section 12).

{stmt}`Step`

{leanDecl Step}

*Theorem 9.4.*  A successful run
$`c \mathrel{\square} \tilde{\varphi} \rightsquigarrow^{*} c' \mathrel{\square} \varepsilon`
yields proof trees $`p_1, \ldots, p_n`, with $`p_i` proving $`\varphi_i`, such
that $`c' \dashv\vdash c \land \mathit{total}(p_1) \land \cdots \land \mathit{total}(p_n)`.
The parameter $`\mathit{ok}` plays no part: pruning restricts the search,
never the soundness.

{stmt}`steps_forest`

{leanDecl steps_forest}

*Corollary 9.8.*  A successful run
$`c \mathrel{\square} \tilde{\varphi} \rightsquigarrow^{*} c' \mathrel{\square} \varepsilon`
gives $`\Theta \vdash c' \twoheadrightarrow c \land \varphi_1 \land \cdots \land \varphi_n`.

{stmt}`steps_sound`

{leanDecl steps_sound}

# Completeness at world 2, without the modality

Let $`R` interpret the constraint predicates (it holds only of constraint
predicates and of closed terms) and let $`\Theta` be non-modal with closed
clauses.  For a closed Σ-goal $`S`: $`S` is true in the least model of
$`\Theta` over $`R` if and only if some proof tree of $`S` has its total
constraint true in $`R`.  This is the completeness half of the conventional
Theorem 6.1, in the form of proof trees.

{stmt}`world2_free`

{leanDecl world2_free}
