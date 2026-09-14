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

Σ-formulas are `S ::= ⊤ | P(t̃) | S ∧ S | S ∨ S | ∃x.S`; there is no `◯` and
no `⊃` in a body.  A program clause is `∀x₁…xₘ. S ⊃ H` with `H = P(x̃)` or
`◯_q P(x̃)`; the head's arguments are distinct bound variables, so resolution
is instantiation.  A program `Θ` is a list of clauses.

Definition 5.1's clauses: a Σ-body, a head predicate applied to the bound
variables, and a flag for a modal head.

{docstring LaxLogic.QLL.Clause +allowMissing}

The draft's indices `ind(S)` choose one disjunct at every `∨`, and `sel S g`
is `S` at index `g`; a clause is provably equivalent to its Horn clauses, one
per index.

`g ∈ ind S` and `Γ ⊢ sel S g` give `Γ ⊢ S`.

{docstring LaxLogic.QLL.Prv.of_sel +allowMissing}

`Γ ⊢ S` gives `Γ ⊢ ⋁ sel S g` over `g ∈ ind S`.

{docstring LaxLogic.QLL.Prv.disj_sel +allowMissing}

A clause follows from its Horn clauses.

{docstring LaxLogic.QLL.Clause.prv_of_toHorn +allowMissing}

# The least Herbrand model

Relative to built-in relations `R`, `Holds R Θ φ` is the inductive least
model — atoms of `R`, `⊤`, `∧`, `∃` with a closed witness, and clause firing
— and `LHM R Θ` is its atomic part.  `Tp` is the immediate consequence
operator.

The least Herbrand model relative to built-ins.

{docstring LaxLogic.QLL.LHM +allowMissing}

`Tp(LHM) = LHM`.

{docstring LaxLogic.QLL.Tp_LHM +allowMissing}

`Tp(I) ⊆ I` implies `LHM ⊆ I`.

{docstring LaxLogic.QLL.LHM_least +allowMissing}

`LHM = ⋃ₙ Tpⁿ(∅)`.

{docstring LaxLogic.QLL.LHM_iff_Tpow +allowMissing}

`LHM = lfp Tp` in the sense of `OrderHom.lfp`; this is the one result that
uses `Classical.choice`, through Mathlib's lattice.

{docstring LaxLogic.QLL.LHM_eq_lfp +allowMissing}

`Tp(I) ⊆ I` iff `R ⊆ I` and `I ⊨ Θ`.

{docstring LaxLogic.QLL.prefixpoint_iff_model +allowMissing}

`LHM = ⋂ { I | R ⊆ I, I ⊨ Θ }`.

{docstring LaxLogic.QLL.LHM_iff_all_models +allowMissing}

Lloyd's theorems for non-modal Horn programs and closed Σ-queries follow.

`Θ ⊢ S` iff `S` is true in the least model.

{docstring LaxLogic.QLL.lloyd_prv_iff +allowMissing}

`Θ ⊢ S` iff `Θ ⊫ S`.

{docstring LaxLogic.QLL.lloyd_consequence_iff +allowMissing}

Van Emden and Kowalski: `M_P(p, ũ)` iff `P ⊫ p(ũ)`.

{docstring LaxLogic.QLL.vanEmden_Kowalski +allowMissing}

Two designed cells mark the limits of the method.

`⊬ P ∨ ¬P`, refuted by a two-world Herbrand model: least models are
intuitionistic.

{docstring LaxLogic.QLL.lem_not_prv +allowMissing}

A disjunction has no least Herbrand model, which is why bodies are split into
Horn clauses first.

{docstring LaxLogic.QLL.or_no_least_model +allowMissing}

# Why two worlds

Lloyd's theory uses one world.  In one world `◯` collapses:

In a one-world Herbrand model, `◯A` holds iff `A` does.

{docstring LaxLogic.QLL.HTrue_circ +allowMissing}

So a one-world model cannot tell "`S` holds" from "`S` holds up to a
constraint", which is the distinction lax logic programming exists to make.
The least structure that separates them has two worlds `0 ≤ 1` with the arrow
modal: `0 ⊨ ◯S` iff `1 ⊨ S`.  Each world is a least Herbrand model of a
variant of the program.  World 0 carries `Π⁰`, the program with its modal
clauses deleted — the pessimistic reading, under which a modal clause says
nothing.  World 1 carries `Π¹`, the program with `◯` erased — the optimistic
reading, all constraints assumed solvable.  `M(Π⁰) ⊆ M(Π¹)` makes the
interpretation monotone.

Theorem 7.5 at world 0: `Θ ⊢ S` iff `0 ⊨ S`.

{docstring LaxLogic.QLL.thm_7_5_world0 +allowMissing}

Theorem 7.5 at world 1: `Θ ⊢ ◯_q S` iff `1 ⊨ S`.

{docstring LaxLogic.QLL.thm_7_5_world1 +allowMissing}

Solvability needs two more worlds, and they appear with the `◯` pass: world 2
carries the least model of the concrete program over the constraint
relations, and above it a fallible world 3 through which `◯` imposes nothing
at world 2 — without it, forcing the abstract clauses at world 0 would demand
that every constraint be solvable.
