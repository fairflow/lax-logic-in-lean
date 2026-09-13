import Verso
import VersoManual
import VersoBlueprint
import LaxLogic.QLL

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Lax logic programs and their least models" =>

Clauses, the splitting of disjunctive bodies into Horn clauses, Lloyd's least
Herbrand model with its fixpoint characterisations, and the two-world model
that separates "holds" from "holds up to a constraint".

# Clauses

Σ-formulas are `S ::= ⊤ | P(t̃) | S ∧ S | S ∨ S | ∃x.S`; there is no `◯` and
no `⊃` in a body.  A program clause is `∀x₁…xₘ. S ⊃ H` with `H = P(x̃)` or
`◯_q P(x̃)`; the head's arguments are distinct bound variables, so resolution
is instantiation.  A program `Θ` is a list of clauses.

:::group "prog"
Programs and their models.
:::

:::definition "prog_clause" (parent := "prog") (lean := "LaxLogic.QLL.Clause")
Definition 5.1's clauses: a Σ-body, a head predicate applied to the bound
variables, and a flag for a modal head.
:::

The draft's indices `ind(S)` choose one disjunct at every `∨`, and `sel S g`
is `S` at index `g`; a clause is provably equivalent to its Horn clauses, one
per index.

:::theorem "prog_of_sel" (parent := "prog") (lean := "LaxLogic.QLL.Prv.of_sel")
`g ∈ ind S` and `Γ ⊢ sel S g` give `Γ ⊢ S`.
:::

:::theorem "prog_disj_sel" (parent := "prog") (lean := "LaxLogic.QLL.Prv.disj_sel")
`Γ ⊢ S` gives `Γ ⊢ ⋁ sel S g` over `g ∈ ind S`.
:::

:::theorem "prog_horn" (parent := "prog") (uses := "prog_of_sel, prog_disj_sel") (lean := "LaxLogic.QLL.Clause.prv_of_toHorn")
A clause follows from its Horn clauses.
:::

# The least Herbrand model

Relative to built-in relations `R`, `Holds R Θ φ` is the inductive least
model — atoms of `R`, `⊤`, `∧`, `∃` with a closed witness, and clause firing
— and `LHM R Θ` is its atomic part.  `Tp` is the immediate consequence
operator.

:::definition "prog_lhm" (parent := "prog") (lean := "LaxLogic.QLL.LHM")
The least Herbrand model relative to built-ins.
:::

:::theorem "prog_tp_lhm" (parent := "prog") (uses := "prog_lhm") (lean := "LaxLogic.QLL.Tp_LHM")
`Tp(LHM) = LHM`.
:::

:::theorem "prog_lhm_least" (parent := "prog") (uses := "prog_lhm") (lean := "LaxLogic.QLL.LHM_least")
`Tp(I) ⊆ I` implies `LHM ⊆ I`.
:::

:::theorem "prog_lhm_tpow" (parent := "prog") (uses := "prog_tp_lhm, prog_lhm_least") (lean := "LaxLogic.QLL.LHM_iff_Tpow")
`LHM = ⋃ₙ Tpⁿ(∅)`.
:::

:::theorem "prog_lhm_lfp" (parent := "prog") (uses := "prog_lhm_tpow") (lean := "LaxLogic.QLL.LHM_eq_lfp")
`LHM = lfp Tp` in the sense of `OrderHom.lfp`; this is the one result that
uses `Classical.choice`, through Mathlib's lattice.
:::

:::theorem "prog_prefix" (parent := "prog") (uses := "prog_lhm") (lean := "LaxLogic.QLL.prefixpoint_iff_model")
`Tp(I) ⊆ I` iff `R ⊆ I` and `I ⊨ Θ`.
:::

:::theorem "prog_lhm_all" (parent := "prog") (uses := "prog_prefix, prog_lhm_least") (lean := "LaxLogic.QLL.LHM_iff_all_models")
`LHM = ⋂ { I | R ⊆ I, I ⊨ Θ }`.
:::

Lloyd's theorems for non-modal Horn programs and closed Σ-queries follow.

:::theorem "prog_lloyd" (parent := "prog") (uses := "prog_lhm, logic_sound") (lean := "LaxLogic.QLL.lloyd_prv_iff")
`Θ ⊢ S` iff `S` is true in the least model.
:::

:::theorem "prog_lloyd_conseq" (parent := "prog") (uses := "prog_lloyd") (lean := "LaxLogic.QLL.lloyd_consequence_iff")
`Θ ⊢ S` iff `Θ ⊫ S`.
:::

:::theorem "prog_vek" (parent := "prog") (uses := "prog_lloyd_conseq") (lean := "LaxLogic.QLL.vanEmden_Kowalski")
Van Emden and Kowalski: `M_P(p, ũ)` iff `P ⊫ p(ũ)`.
:::

Two designed cells mark the limits of the method.

:::theorem "prog_lem" (parent := "prog") (uses := "logic_sound") (lean := "LaxLogic.QLL.lem_not_prv")
`⊬ P ∨ ¬P`, refuted by a two-world Herbrand model: least models are
intuitionistic.
:::

:::theorem "prog_or" (parent := "prog") (uses := "prog_lhm") (lean := "LaxLogic.QLL.or_no_least_model")
A disjunction has no least Herbrand model, which is why bodies are split into
Horn clauses first.
:::

# Why two worlds

Lloyd's theory uses one world.  In one world `◯` collapses:

:::theorem "prog_htrue" (parent := "prog") (uses := "logic_kmodel") (lean := "LaxLogic.QLL.HTrue_circ")
In a one-world Herbrand model, `◯A` holds iff `A` does.
:::

So a one-world model cannot tell "`S` holds" from "`S` holds up to a
constraint", which is the distinction lax logic programming exists to make.
The least structure that separates them has two worlds `0 ≤ 1` with the arrow
modal: `0 ⊨ ◯S` iff `1 ⊨ S`.  Each world is a least Herbrand model of a
variant of the program.  World 0 carries `Π⁰`, the program with its modal
clauses deleted — the pessimistic reading, under which a modal clause says
nothing.  World 1 carries `Π¹`, the program with `◯` erased — the optimistic
reading, all constraints assumed solvable.  `M(Π⁰) ⊆ M(Π¹)` makes the
interpretation monotone.

:::theorem "prog_75_0" (parent := "prog") (uses := "prog_lloyd, prog_htrue") (lean := "LaxLogic.QLL.thm_7_5_world0")
Theorem 7.5 at world 0: `Θ ⊢ S` iff `0 ⊨ S`.
:::

:::theorem "prog_75_1" (parent := "prog") (uses := "prog_lloyd, prog_htrue") (lean := "LaxLogic.QLL.thm_7_5_world1")
Theorem 7.5 at world 1: `Θ ⊢ ◯_q S` iff `1 ⊨ S`.
:::

Solvability needs two more worlds, and they appear with the `◯` pass: world 2
carries the least model of the concrete program over the constraint
relations, and above it a fallible world 3 through which `◯` imposes nothing
at world 2 — without it, forcing the abstract clauses at world 0 would demand
that every constraint be solvable.
