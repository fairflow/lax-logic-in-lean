import Verso
import VersoManual
import LaxLogic.QLL
import CLPPaper.Src

open Verso.Genre
open Verso.Genre.Manual
open CLPPaper

#doc (Manual) "Abstraction, extraction and refinement" =>

The second pass: delete the constraints from the program, prove the abstract
program in lax logic, extract the constraint from the abstract proof, and
recombine.  This is the pattern of Fairtlough, Mendler and Cheng's
abstraction-and-refinement method (TPHOLs 2001) applied to CLP, and its
theorems say that each step is sound and that the composite computes the
conventional answer constraint.

# Abstraction

`S♯` replaces each constraint atom by $`\top`; the clause $`\forall \tilde{x}. S \supset P(\tilde{x})` becomes
$`\forall \tilde{x}. S^\sharp \supset \bigcirc _q P(\tilde{x})`.  Abstract proof trees are the derivations of Fig. 3,
whose judgement is always $`\bigcirc S`: `val` at $`\top`, $`\land \bigcirc`, $`\lor \bigcirc`, $`\exists \bigcirc`, and $`\supset \bigcirc`, the
application of a modal-headed clause.

```
inductive AProof where
  | val | andC (p r : AProof) | orL (p : AProof) | orR (p : AProof)
  | exC (t : Tm) (p : AProof) | impC (w : Nat) (ts : List Tm) (p : AProof)
```

Abstract proof trees, Fig. 3's derivations as data.

{docstring LaxLogic.QLL.AProof +allowMissing}

{srcLink}`LaxLogic.QLL.AProof`

`ATyped Θ♯ q S a`: `a` proves $`\bigcirc _q S`; the clause rule demands a modal head
of polarity `q`.

{docstring LaxLogic.QLL.ATyped +allowMissing}

{srcLink}`LaxLogic.QLL.ATyped`

Abstract proofs are proofs: `ATyped Θ♯ q S a` gives $`\Theta ^\sharp \vdash \bigcirc _q S`.  Its cases
are the QLL derivations that justify each rule of Fig. 3.

{docstring LaxLogic.QLL.ATyped.prv +allowMissing}

{srcLink}`LaxLogic.QLL.ATyped.prv`

Theorem 6.3, at the level of terms: if no clause head is a constraint, a
concrete tree for `S` maps to an abstract tree for `S♯` against `Θ♯`.

{docstring LaxLogic.QLL.CTyped.toA +allowMissing}

{srcLink}`LaxLogic.QLL.CTyped.toA`

Theorem 6.3: $`\Theta \vdash S` gives $`\Theta ^\sharp \vdash \bigcirc _q S^\sharp`.

{docstring LaxLogic.QLL.CTyped.prv_abs +allowMissing}

{srcLink}`LaxLogic.QLL.CTyped.prv_abs`

# Extraction

The writer monad $`\mathit{WM} \alpha = C \times \alpha` with $`\mathit{val} a = (\top, a)` and `bind (c, a) f =
(c ∧ π₁(f a), π₂(f a))` satisfies the monad laws up to `⊣⊢`, and is
commutative.  Witnesses are the values of the refinement types of
Σ-formulas: unit, pairs, injections, packs with a term.  A table `T w t̃ z`
gives the constraint of clause `w` at instance `t̃` and body witness `z` —
the draft's `θ♯₁`.  Extraction reads an abstract proof against a table,
clause by clause of Fig. 3.

Extraction: an abstract proof and a table give a constraint and a witness.

{docstring LaxLogic.QLL.AProof.ext +allowMissing}

{srcLink}`LaxLogic.QLL.AProof.ext`

Commutativity of the writer monad up to $`\dashv\vdash`: what selection-order
independence rests on.  The monad laws the draft asks for do not include it.

{docstring LaxLogic.QLL.WM.bind_comm +allowMissing}

{srcLink}`LaxLogic.QLL.WM.bind_comm`

Lemma 8.3: the concrete program's table entry at a tree's witness is the
tree's active constraint.

{docstring LaxLogic.QLL.CTyped.ctable_wit +allowMissing}

{srcLink}`LaxLogic.QLL.CTyped.ctable_wit`

Lemma 8.4: the witness of `toA p` is `p`'s witness, and the extracted
constraint is $`\dashv\vdash` the latent constraint.

{docstring LaxLogic.QLL.CTyped.ext_toA +allowMissing}

{srcLink}`LaxLogic.QLL.CTyped.ext_toA`

Extracted constraint and active constraint together are the total constraint,
up to $`\dashv\vdash`.

{docstring LaxLogic.QLL.CTyped.ext_total +allowMissing}

{srcLink}`LaxLogic.QLL.CTyped.ext_total`

Theorem 9.7.  For a pure query `φ`, a run $`\top \square \varphi \rightsquigarrow * c \square \varepsilon` yields a concrete
tree `p` whose abstract image types against `Θ♯` and whose extracted
constraint is $`\dashv\vdash c`: the two passes compute the same answer.

{docstring LaxLogic.QLL.thm_9_7 +allowMissing}

{srcLink}`LaxLogic.QLL.thm_9_7`

# Refinement

Definition 6.5 recombines a table with an abstract clause into a concrete one.
It is used through its instances: `RefinedBy Δ Θ♯ T` says that `Δ` proves
$`T w \tilde{t} z \land (S_w[\tilde{t}] @ z) \supset P_w(\tilde{t})` for every clause, instance and witness,
where `S @ z` is the disjunct of `S` that `z` selects with its existential
witnesses substituted.  Then, for any table:

Theorem 6.8: `RefinedBy Δ Θ♯ T` and `ATyped Θ♯ q S a` give $`\Delta \vdash \pi _1|a| \supset S`.
Uniform in the table.

{docstring LaxLogic.QLL.thm_6_8 +allowMissing}

{srcLink}`LaxLogic.QLL.thm_6_8`

Proposition 6.6, first half: a non-modal program refines its own abstraction
through its own table.

{docstring LaxLogic.QLL.refinedBy_abs +allowMissing}

{srcLink}`LaxLogic.QLL.refinedBy_abs`

Corollary 9.8 by the draft's route: an abstract proof of $`\bigcirc S`, refined with
the concrete program's table, yields a constraint that implies `S` in the
concrete program.

{docstring LaxLogic.QLL.cor_9_8_abs +allowMissing}

{srcLink}`LaxLogic.QLL.cor_9_8_abs`

The second half of Proposition 6.6, that a modal clause follows from its
refinement, is false as stated.

REFUTED: $`\forall x.(A x \land B x) \supset P x` does not prove $`\forall x. A x \supset \bigcirc P x`.  One-world
countermodel: `A` everywhere, `B` and `P` nowhere.

{docstring LaxLogic.QLL.p66_refuted +allowMissing}

{srcLink}`LaxLogic.QLL.p66_refuted`

Repaired: with the table's constraints lax-true, $`\forall x. \bigcirc B x`, the clause does
follow.

{docstring LaxLogic.QLL.p66_with_lax +allowMissing}

{srcLink}`LaxLogic.QLL.p66_with_lax`

# The canonical constraint model

The draft's frame is `0 → 1`, `0 → 2 → 3`, world 3 fallible, every arrow
modal.  For the abstraction of a well-formed non-modal program and constraint
relations `R`: world 0 carries `M(Π⁰)`, world 1 `M(Π¹)`, world 2 the least
model of `Θ` over `R`, world 3 everything.

Lemma 7.2: world 0 forces every clause of `Θ♯`.

{docstring LaxLogic.QLL.canon_clause +allowMissing}

{srcLink}`LaxLogic.QLL.canon_clause`

Lemma 7.3: the interpretation is monotone along the frame.

{docstring LaxLogic.QLL.canon_hered +allowMissing}

{srcLink}`LaxLogic.QLL.canon_hered`

World 2 forces $`\bigcirc S` for every `S`, through the fallible world 3: solvability
is recorded in world 2's atoms only, and $`\bigcirc \bot` holds there.

{docstring LaxLogic.QLL.canon_circ_w2 +allowMissing}

{srcLink}`LaxLogic.QLL.canon_circ_w2`

Theorem 7.5 at world 0: $`\Theta ^\sharp \vdash S` iff $`0 \models S`.

{docstring LaxLogic.QLL.thm_7_5_canon0 +allowMissing}

{srcLink}`LaxLogic.QLL.thm_7_5_canon0`

Theorem 7.5 at world 1: $`\Theta ^\sharp \vdash \bigcirc _q S` iff $`1 \models S`.

{docstring LaxLogic.QLL.thm_7_5_canon1 +allowMissing}

{srcLink}`LaxLogic.QLL.thm_7_5_canon1`

Theorem 7.5 at world 2: for a pure `S`, some abstract proof of $`\bigcirc S` extracts
a constraint true in `R` iff $`2 \models S`.  The draft asks for a solvable
constraint; with the witness terms chosen to be the solution, that is the
same.

{docstring LaxLogic.QLL.thm_7_5_canon2 +allowMissing}

{srcLink}`LaxLogic.QLL.thm_7_5_canon2`

Worlds 1 and 2 agree on derivability and differ exactly on solvability.  That
is the formal statement that no argument at the abstract level can see
whether a constraint is solvable — the reason the two passes must be two.
