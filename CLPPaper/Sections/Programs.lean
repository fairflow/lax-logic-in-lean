import Verso
import VersoManual
import LaxLogic.QLL

open Verso.Genre
open Verso.Genre.Manual

#doc (Manual) "Lax logic programs and their least models" =>

Clauses, the splitting of disjunctive bodies into Horn clauses, Lloyd's least
Herbrand model with its fixpoint characterisations, and the two-world model
that separates "holds" from "holds up to a constraint".

# Clauses

Σ-formulas are `S ::= ⊤ | P(t̃) | S ∧ S | S ∨ S | ∃x.S`; there is no $`\bigcirc` and
no $`\supset` in a body.  A program clause is $`\forall x_1…x_m. S \supset H` with `H = P(x̃)` or
$`\bigcirc _q P(\tilde{x})`; the head's arguments are distinct bound variables, so resolution
is instantiation.  A program `Θ` is a list of clauses.

Definition 5.1's clauses: a Σ-body, a head predicate applied to the bound
variables, and a flag for a modal head.

{docstring LaxLogic.QLL.Clause +allowMissing}

The draft's indices `ind(S)` choose one disjunct at every $`\lor`, and `sel S g`
is `S` at index `g`; a clause is provably equivalent to its Horn clauses, one
per index.

$`g \in \mathit{ind} S` and $`\Gamma \vdash \mathit{sel} S g` give $`\Gamma \vdash S`.

{docstring LaxLogic.QLL.Prv.of_sel +allowMissing}

$`\Gamma \vdash S` gives $`\Gamma \vdash \bigvee \mathit{sel} S g` over $`g \in \mathit{ind} S`.

{docstring LaxLogic.QLL.Prv.disj_sel +allowMissing}

A clause follows from its Horn clauses.

{docstring LaxLogic.QLL.Clause.prv_of_toHorn +allowMissing}

# The least Herbrand model

Relative to built-in relations `R`, `Holds R Θ φ` is the inductive least
model — atoms of `R`, $`\top`, $`\land`, $`\exists` with a closed witness, and clause firing
— and `LHM R Θ` is its atomic part.  `Tp` is the immediate consequence
operator.

The least Herbrand model relative to built-ins.

{docstring LaxLogic.QLL.LHM +allowMissing}

`Tp(LHM) = LHM`.

{docstring LaxLogic.QLL.Tp_LHM +allowMissing}

$`\mathit{Tp}(I) \subseteq I` implies $`\mathit{LHM} \subseteq I`.

{docstring LaxLogic.QLL.LHM_least +allowMissing}

`LHM = ⋃ₙ Tpⁿ(∅)`.

{docstring LaxLogic.QLL.LHM_iff_Tpow +allowMissing}

`LHM = lfp Tp` in the sense of `OrderHom.lfp`; this is the one result that
uses `Classical.choice`, through Mathlib's lattice.

{docstring LaxLogic.QLL.LHM_eq_lfp +allowMissing}

$`\mathit{Tp}(I) \subseteq I` iff $`R \subseteq I` and $`I \models \Theta`.

{docstring LaxLogic.QLL.prefixpoint_iff_model +allowMissing}

$$`\mathit{LHM} = \bigcap \{ I | R \subseteq I, I \models \Theta \}`

{docstring LaxLogic.QLL.LHM_iff_all_models +allowMissing}

Lloyd's theorems for non-modal Horn programs and closed Σ-queries follow.

$`\Theta \vdash S` iff `S` is true in the least model.

{docstring LaxLogic.QLL.lloyd_prv_iff +allowMissing}

$`\Theta \vdash S` iff $`\Theta \Vdash S`.

{docstring LaxLogic.QLL.lloyd_consequence_iff +allowMissing}

Van Emden and Kowalski: `M_P(p, ũ)` iff $`P \Vdash p(\tilde{u} )`.

{docstring LaxLogic.QLL.vanEmden_Kowalski +allowMissing}

Two designed cells mark the limits of the method.

$`\nvdash P \lor \lnot P`, refuted by a two-world Herbrand model: least models are
intuitionistic.

{docstring LaxLogic.QLL.lem_not_prv +allowMissing}

A disjunction has no least Herbrand model, which is why bodies are split into
Horn clauses first.

{docstring LaxLogic.QLL.or_no_least_model +allowMissing}

# Why two worlds

Lloyd's theory uses one world.  In one world $`\bigcirc` collapses:

In a one-world Herbrand model, $`\bigcirc A` holds iff `A` does.

{docstring LaxLogic.QLL.HTrue_circ +allowMissing}

So a one-world model cannot tell "`S` holds" from "`S` holds up to a
constraint", which is the distinction lax logic programming exists to make.
The least structure that separates them has two worlds $`0 \le 1` with the arrow
modal: $`0 \models \bigcirc S` iff $`1 \models S`.  Each world is a least Herbrand model of a
variant of the program.  World 0 carries `Π⁰`, the program with its modal
clauses deleted — the pessimistic reading, under which a modal clause says
nothing.  World 1 carries `Π¹`, the program with $`\bigcirc` erased — the optimistic
reading, all constraints assumed solvable.  $`M(\Pi ^0) \subseteq M(\Pi ^1)` makes the
interpretation monotone.

Theorem 7.5 at world 0: $`\Theta \vdash S` iff $`0 \models S`.

{docstring LaxLogic.QLL.thm_7_5_world0 +allowMissing}

Theorem 7.5 at world 1: $`\Theta \vdash \bigcirc _q S` iff $`1 \models S`.

{docstring LaxLogic.QLL.thm_7_5_world1 +allowMissing}

Solvability needs two more worlds, and they appear with the $`\bigcirc` pass: world 2
carries the least model of the concrete program over the constraint
relations, and above it a fallible world 3 through which $`\bigcirc` imposes nothing
at world 2 — without it, forcing the abstract clauses at world 0 would demand
that every constraint be solvable.
