import Verso
import VersoManual
import VersoBlueprint
import LaxLogic.QLL

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Abstraction, extraction and refinement" =>

The second pass: delete the constraints from the program, prove the abstract
program in lax logic, extract the constraint from the abstract proof, and
recombine.  This is the pattern of Fairtlough, Mendler and Cheng's
abstraction-and-refinement method (TPHOLs 2001) applied to CLP, and its
theorems say that each step is sound and that the composite computes the
conventional answer constraint.

# Abstraction

`S♯` replaces each constraint atom by `⊤`; the clause `∀x̃. S ⊃ P(x̃)` becomes
`∀x̃. S♯ ⊃ ◯_q P(x̃)`.  Abstract proof trees are the derivations of Fig. 3,
whose judgement is always `◯S`: `val` at `⊤`, `∧◯`, `∨◯`, `∃◯`, and `⊃◯`, the
application of a modal-headed clause.

```
inductive AProof where
  | val | andC (p r : AProof) | orL (p : AProof) | orR (p : AProof)
  | exC (t : Tm) (p : AProof) | impC (w : Nat) (ts : List Tm) (p : AProof)
```

:::group "abs"
The `◯` pass.
:::

:::definition "abs_aproof" (parent := "abs") (lean := "LaxLogic.QLL.AProof")
Abstract proof trees, Fig. 3's derivations as data.
:::

:::definition "abs_atyped" (parent := "abs") (uses := "abs_aproof, prog_clause") (lean := "LaxLogic.QLL.ATyped")
`ATyped Θ♯ q S a`: `a` proves `◯_q S`; the clause rule demands a modal head
of polarity `q`.
:::

:::theorem "abs_prv" (parent := "abs") (uses := "abs_atyped") (lean := "LaxLogic.QLL.ATyped.prv")
Abstract proofs are proofs: `ATyped Θ♯ q S a` gives `Θ♯ ⊢ ◯_q S`.  Its cases
are the QLL derivations that justify each rule of Fig. 3.
:::

:::theorem "abs_toA" (parent := "abs") (uses := "trees_ctyped, abs_atyped") (lean := "LaxLogic.QLL.CTyped.toA")
Theorem 6.3, at the level of terms: if no clause head is a constraint, a
concrete tree for `S` maps to an abstract tree for `S♯` against `Θ♯`.
:::

:::theorem "abs_prv_abs" (parent := "abs") (uses := "abs_toA, abs_prv") (lean := "LaxLogic.QLL.CTyped.prv_abs")
Theorem 6.3: `Θ ⊢ S` gives `Θ♯ ⊢ ◯_q S♯`.
:::

# Extraction

The writer monad `WM α = C × α` with `val a = (⊤, a)` and `bind (c, a) f =
(c ∧ π₁(f a), π₂(f a))` satisfies the monad laws up to `⊣⊢`, and is
commutative.  Witnesses are the values of the refinement types of
Σ-formulas: unit, pairs, injections, packs with a term.  A table `T w t̃ z`
gives the constraint of clause `w` at instance `t̃` and body witness `z` —
the draft's `θ♯₁`.  Extraction reads an abstract proof against a table,
clause by clause of Fig. 3.

:::definition "abs_ext" (parent := "abs") (uses := "abs_aproof") (lean := "LaxLogic.QLL.AProof.ext")
Extraction: an abstract proof and a table give a constraint and a witness.
:::

:::theorem "abs_comm" (parent := "abs") (lean := "LaxLogic.QLL.WM.bind_comm")
Commutativity of the writer monad up to `⊣⊢`: what selection-order
independence rests on.  The monad laws the draft asks for do not include it.
:::

:::theorem "abs_83" (parent := "abs") (uses := "trees_ctyped") (lean := "LaxLogic.QLL.CTyped.ctable_wit")
Lemma 8.3: the concrete program's table entry at a tree's witness is the
tree's active constraint.
:::

:::theorem "abs_84" (parent := "abs") (uses := "abs_83, abs_ext") (lean := "LaxLogic.QLL.CTyped.ext_toA")
Lemma 8.4: the witness of `toA p` is `p`'s witness, and the extracted
constraint is `⊣⊢` the latent constraint.
:::

:::theorem "abs_ext_total" (parent := "abs") (uses := "abs_84, trees_total") (lean := "LaxLogic.QLL.CTyped.ext_total")
Extracted constraint and active constraint together are the total constraint,
up to `⊣⊢`.
:::

:::theorem "abs_97" (parent := "abs") (uses := "trees_94, abs_toA, abs_ext_total") (lean := "LaxLogic.QLL.thm_9_7")
Theorem 9.7.  For a pure query `φ`, a run `⊤ □ φ ⇝* c □ ε` yields a concrete
tree `p` whose abstract image types against `Θ♯` and whose extracted
constraint is `⊣⊢ c`: the two passes compute the same answer.
:::

# Refinement

Definition 6.5 recombines a table with an abstract clause into a concrete one.
It is used through its instances: `RefinedBy Δ Θ♯ T` says that `Δ` proves
`T w t̃ z ∧ (S_w[t̃] @ z) ⊃ P_w(t̃)` for every clause, instance and witness,
where `S @ z` is the disjunct of `S` that `z` selects with its existential
witnesses substituted.  Then, for any table:

:::theorem "abs_68" (parent := "abs") (uses := "abs_atyped, abs_ext") (lean := "LaxLogic.QLL.thm_6_8")
Theorem 6.8: `RefinedBy Δ Θ♯ T` and `ATyped Θ♯ q S a` give `Δ ⊢ π₁|a| ⊃ S`.
Uniform in the table.
:::

:::theorem "abs_66a" (parent := "abs") (uses := "abs_83") (lean := "LaxLogic.QLL.refinedBy_abs")
Proposition 6.6, first half: a non-modal program refines its own abstraction
through its own table.
:::

:::theorem "abs_98abs" (parent := "abs") (uses := "abs_68, abs_66a") (lean := "LaxLogic.QLL.cor_9_8_abs")
Corollary 9.8 by the draft's route: an abstract proof of `◯S`, refined with
the concrete program's table, yields a constraint that implies `S` in the
concrete program.
:::

The second half of Proposition 6.6, that a modal clause follows from its
refinement, is false as stated.

:::theorem "abs_66b_refuted" (parent := "abs") (uses := "logic_sound") (lean := "LaxLogic.QLL.p66_refuted")
REFUTED: `∀x.(A x ∧ B x) ⊃ P x` does not prove `∀x. A x ⊃ ◯P x`.  One-world
countermodel: `A` everywhere, `B` and `P` nowhere.
:::

:::theorem "abs_66b_lax" (parent := "abs") (uses := "abs_66b_refuted") (lean := "LaxLogic.QLL.p66_with_lax")
Repaired: with the table's constraints lax-true, `∀x. ◯B x`, the clause does
follow.
:::

# The canonical constraint model

The draft's frame is `0 → 1`, `0 → 2 → 3`, world 3 fallible, every arrow
modal.  For the abstraction of a well-formed non-modal program and constraint
relations `R`: world 0 carries `M(Π⁰)`, world 1 `M(Π¹)`, world 2 the least
model of `Θ` over `R`, world 3 everything.

:::theorem "abs_72" (parent := "abs") (uses := "prog_lhm") (lean := "LaxLogic.QLL.canon_clause")
Lemma 7.2: world 0 forces every clause of `Θ♯`.
:::

:::theorem "abs_73" (parent := "abs") (uses := "prog_lhm") (lean := "LaxLogic.QLL.canon_hered")
Lemma 7.3: the interpretation is monotone along the frame.
:::

:::theorem "abs_w2circ" (parent := "abs") (lean := "LaxLogic.QLL.canon_circ_w2")
World 2 forces `◯S` for every `S`, through the fallible world 3: solvability
is recorded in world 2's atoms only, and `◯⊥` holds there.
:::

:::theorem "abs_75_0" (parent := "abs") (uses := "abs_72, abs_73") (lean := "LaxLogic.QLL.thm_7_5_canon0")
Theorem 7.5 at world 0: `Θ♯ ⊢ S` iff `0 ⊨ S`.
:::

:::theorem "abs_75_1" (parent := "abs") (uses := "abs_72, abs_73") (lean := "LaxLogic.QLL.thm_7_5_canon1")
Theorem 7.5 at world 1: `Θ♯ ⊢ ◯_q S` iff `1 ⊨ S`.
:::

:::theorem "abs_75_2" (parent := "abs") (uses := "abs_72, abs_73, abs_ext") (lean := "LaxLogic.QLL.thm_7_5_canon2")
Theorem 7.5 at world 2: for a pure `S`, some abstract proof of `◯S` extracts
a constraint true in `R` iff `2 ⊨ S`.  The draft asks for a solvable
constraint; with the witness terms chosen to be the solution, that is the
same.
:::

Worlds 1 and 2 agree on derivability and differ exactly on solvability.  That
is the formal statement that no argument at the abstract level can see
whether a constraint is solvable — the reason the two passes must be two.
