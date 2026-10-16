import Verso
import VersoManual
import LaxLogic.QLL
import CLPPaper.Src
import CLPPaper.Decl
import CLPPaper.Math

open Verso.Genre
open Verso.Genre.Manual
open CLPPaper CLPPaper.Math
open LaxLogic.QLL LaxLogic.QLL.SLD
open LaxLogic.QLL.Form (openAt openWith)

#doc (Manual) "Quantified lax logic" =>

This section fixes the logic in which everything is stated: intuitionistic
first-order logic with two lax modalities (QLL), its natural deduction
calculus, its Kripke models, and soundness and completeness.  The draft takes
the logic from Fairtlough and Mendler; the rules below are those of Fig. 5 of
Fairtlough, Mendler and Cheng (TPHOLs 2001), stated on formula contexts.  The
section ends with a warning about the modal relation of a model, which matters
for the Herbrand models of Section 4.

# Syntax and proofs

Formulas are built from $`\top`, $`\bot` and atoms $`P(t_1, \ldots, t_n)` by
$`\land`, $`\lor`, $`\twoheadrightarrow`, $`\forall`, $`\exists` and two
modalities $`\bigcirc_q A`, one for each $`q \in \{\forall, \exists\}`.  The
draft's single modality $`\bigcirc` is $`\bigcirc_\exists`; every proof below
is stated for a general $`q`.  Terms and formulas are locally nameless: bound
variables are de Bruijn indices, free ones are names, and $`A[t/0]` replaces
the outermost bound variable of $`\forall A` or $`\exists A` by the term $`t`.

Provability $`\Gamma \vdash A`, for a list $`\Gamma` of formulas, is natural
deduction.  The propositional rules are the intuitionistic ones, with
$`\bot`-elimination.  The modal rules are

$$`\dfrac{\Gamma \vdash A}{\Gamma \vdash \bigcirc_q A}\;(\bigcirc I) \qquad\qquad \dfrac{\Gamma \vdash \bigcirc_q A \qquad A, \Gamma \vdash \bigcirc_q B}{\Gamma \vdash \bigcirc_q B}\;(\bigcirc E)`

so $`\bigcirc_q` is a monad: $`(\bigcirc I)` is its unit and $`(\bigcirc E)`
its bind.  The quantifier rules use cofinite quantification over the fresh
name $`a`: a premise must hold for every name outside some finite list $`L`,

$$`\dfrac{\Gamma \vdash A[a/0] \;\text{ for all } a \notin L}{\Gamma \vdash \forall A}\;(\forall I) \qquad\qquad \dfrac{\Gamma \vdash \forall A}{\Gamma \vdash A[t/0]}\;(\forall E)`

$$`\dfrac{\Gamma \vdash A[t/0]}{\Gamma \vdash \exists A}\;(\exists I) \qquad\qquad \dfrac{\Gamma \vdash \exists A \qquad A[a/0], \Gamma \vdash K \;\text{ for all } a \notin L}{\Gamma \vdash K}\;(\exists E)`

where in $`(\forall E)` and $`(\exists I)` the term $`t` is closed.  In the
Lean definition the conclusion of $`(\forall E)` is a variable $`B` with the
equation $`B = A[t/0]` as a further premise, so that every index of the
inductive family is a variable (the green-slime check of Section 12).

{stmt}`Prv`

{leanDecl Prv}

# Models

A Kripke model has a preorder $`R_i` of states with increasing domains of
individuals; a set of _fallible_ states, closed upwards, at which every atom
and $`\bot` hold; two modal relations $`R_\forall, R_\exists \subseteq R_i`,
each reflexive and transitive; rigid function symbols; and predicates whose
extension is hereditary along $`R_i`.  Implication and the universal
quantifier are interpreted along $`R_i` in the usual intuitionistic way, and
the modality by

$$`s \models \bigcirc_q A \iff \text{for every } v \text{ with } s \mathrel{R_i} v \text{ there is } u \text{ with } v \mathrel{R_q} u \text{ and } u \models A.`

Consequence $`\Gamma \models A` means: at every state of every model, under
every assignment, if every formula of $`\Gamma` is forced then $`A` is forced.
The Lean structure below extends the frame structure, whose fields are the
relations just listed; only the fields it adds are printed.

{stmt}`KModel`

{leanDecl KModel}

*Soundness.*  Every provable sequent is a consequence.  The proof uses no
choice.

{stmt}`Prv.sound`

{leanDecl Prv.sound}

*Completeness.*  For contexts and formulas without loose bound variables,
provability and consequence coincide.  The canonical model construction uses
`Classical.choice`.

{stmt}`prv_iff_consequence`

{leanDecl prv_iff_consequence}

# The modal relation is a parameter

When building Herbrand models it is tempting to take the modal relation to be
the intuitionistic order, $`R_\exists = R_i`.  That is not harmless.  With no
fallible states, $`\bigcirc` is then forced exactly where $`\lnot\lnot` is, and
such models validate a formula that QLL does not prove.  The two results below
are a designed pair: the first shows that every model with
$`R_\exists = R_i` forces the formula

$$`(\bigcirc A \twoheadrightarrow \bigcirc B) \twoheadrightarrow \bigcirc (A \twoheadrightarrow B),`

at every state and under every assignment, by a classical argument; the second
shows that QLL does not prove it.

{stmt}`circ_imp_of_rm_eq_ri`

{leanDecl circ_imp_of_rm_eq_ri}

*REFUTED: $`R_\exists = R_i` is a free choice.*  The countermodel has three
states $`r \le s \le f` with $`f` fallible, and the modal relation is the
identity together with $`s \mathrel{R_\exists} f`.

{stmt}`not_prv_circ_imp`

{leanDecl not_prv_circ_imp}

The Herbrand frames used later therefore carry their own modal preorder
$`m \subseteq R_i`.  Where the draft takes $`m = R_i`, it does so on a frame
whose fallible world keeps $`\bigcirc` from collapsing (Section 6).
