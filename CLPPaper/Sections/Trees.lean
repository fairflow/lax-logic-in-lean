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

This section mechanises the first pass of the 1997 report, before
$`\bigcirc` enters: proof trees for programs with built-in constraint atoms,
the report's split of their constraint leaves into active and latent ones
(Definition 8.1), the goal reduction of its Table 2, and the soundness
theorems that connect them (Theorem 9.4 and Corollary 9.8).  It ends with the
completeness of proof trees for the least model over the constraint
relations.  The answer of a CLP computation is a constraint, and what must be
proved about it is soundness: the answer implies the query.  Table 2 computes
answers but keeps no record of why each one is an answer.  A proof tree is
that record, and with it soundness becomes a property of an object that can
be checked, so that neither the search nor the solver has to be trusted.

This section and the next two use four relations on two programs, the
concrete program $`\Theta` and its abstraction $`\Theta^\sharp`
(Section 6).  A _static_ relation types a finished tree; a _dynamic_ one takes
a computation one step.

:::wtable (widths := "0.22 0.36 0.42") +header
*
  * Program
  * Static
  * Dynamic
*
  * concrete, $`\Theta`
  * $`\mathsf{CTyped}` (Section 5.1, the 1997 report's proof trees)
  * $`\mathsf{Step}`, Table 2 (Section 5.2, the report's); $`\mathsf{Expand}`, SLD (Section 7, new)
*
  * abstract, $`\Theta^\sharp`
  * $`\mathsf{ATyped}` (Section 6.1, the report's Fig. 3)
  * $`\mathsf{ExpandA}`, SLD◯ (Section 7, new)
:::

The four are one rule set, read statically and dynamically, on the concrete
and on the abstract program.  The local rules of $`\mathsf{Expand}` are the
rules of $`\mathsf{CTyped}` one for one ($`\mathit{top}`, $`\mathit{cstr}`,
$`\mathit{and}`, $`\mathit{orL}`, $`\mathit{orR}`, $`\mathit{ex}` and
$`\mathit{clause}`), each applied at an open leaf of a partial tree instead of
at the root of a finished one, and congruence rules carry a step down to the
leaf it applies at.  $`\mathsf{ExpandA}` stands to $`\mathsf{ATyped}` in the
same way.  Table 2 is the dynamic reading with the tree discarded: a Table 2
state keeps only the store and the list of open leaves, and Section 7.2
proves that Table 2 and SLD are the same relation on single goals.  The 1997
report's results are stated for Table 2 and for proof trees, and are proved
here in that form; Section 7 says what keeping the tree during a run adds.

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

In displays a tree is written with the names of its rules: $`{\top}\mathrm{I}`,
a constraint leaf as its atom $`B(\tilde{t})`,
$`{\land}\mathrm{I}(p,\, q)`, $`{\lor}\mathrm{I}_1(p)`,
$`{\lor}\mathrm{I}_2(p)`, $`{\exists}\mathrm{I}_t(p)`, and
$`\mathit{clause}_w^{\tilde{t}}(p)`, with the superscript omitted when the
instance $`\tilde{t}` is empty.

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
rather than computed in the indices (Section 13).

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

# The running example in Table 2

The 1997 report runs Example 9.5 (Section 4.4) in six steps of Table 2:
Rule 5 with $`\theta_3`, Rule 2, Rule 3, Rule 5 with $`\theta_1`, and Rule 1
twice.  Each row below is a state and each arrow one step of
$`\mathsf{Step}`, with the consistency test $`\mathit{NoPrune}` that accepts
every store ({srcLink}`CLPExamples.run95_table2`):

{stmt}`CLPExamples.run95_table2`

The answer is the final store, $`(\top \land c_1) \land c_3`, and by
Corollary 9.8 it implies the query (`cor95`, Section 9.1).  The engine of
Section 8, run by the kernel on the query $`Q`, returns the proof tree
$`\mathit{proof}_{95}` ({srcLink}`CLPExamples.run95_tree`):

{stmt}`CLPExamples.run95_tree`

Read from the root: $`\theta_3` is applied, the left disjunct of its body is
chosen, and of the two conjuncts $`P_1` is proved by $`\theta_1` from the
constraint leaf $`c_1`, while $`c_3` is itself a constraint leaf.  These are
the six steps of the run, one node each.  The total constraint is the
conjunction of the two leaves ({srcLink}`CLPExamples.total95`):

{stmt}`CLPExamples.total95`

Theorem 9.4 relates this total to the answer: the answer of a run is, up to
$`\dashv\vdash`, its initial store conjoined with the totals of some proof
trees of its goals.  Section 7.6 shows that for this run the tree is the one
above, built by the run itself.

# Completeness at world 2, without the modality

Let $`R` interpret the constraint predicates (it holds only of constraint
predicates and of closed terms) and let $`\Theta` be non-modal with closed
clauses.  For a closed Σ-goal $`S`: $`S` is true in the least model of
$`\Theta` over $`R` if and only if some proof tree of $`S` has its total
constraint true in $`R`.  This is the completeness half of the conventional
Theorem 6.1, in the form of proof trees.

{stmt}`world2_free`

{leanDecl world2_free}
