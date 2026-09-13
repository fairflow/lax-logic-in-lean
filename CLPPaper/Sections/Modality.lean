import Verso
import VersoManual
import VersoBlueprint
import LaxLogic.QLL

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "What the modality buys: placements and realisers" =>

The draft places `◯` in one position, the clause head.  This section asks
what the other positions would do, and finds that the right notion for
answering is not provability but the realiser: two provably equivalent
formulas can have different realisers, and then a program is not the same
program after rewriting one to the other.

# `◯` in a clause body

Bodies are Σ-formulas, so `◯` cannot occur in them.  What would it do?  The
answer turns on the head.

:::group "mod"
Placements of the modality.
:::

:::theorem "mod_body_plain" (parent := "mod") (lean := "LaxLogic.QLL.BodyCirc.body_circ_to_plain")
With a plain head, a body `◯` implies the same clause with the `◯` deleted:
`(A ∧ ◯B) ⊃ P ⊢ (A ∧ B) ⊃ P`.
:::

:::theorem "mod_body_plain_refuted" (parent := "mod") (uses := "logic_sound") (lean := "LaxLogic.QLL.BodyCirc.not_prv_plain_to_body_circ")
REFUTED converse: `(A ∧ B) ⊃ P` does not prove `(A ∧ ◯B) ⊃ P`.  Two worlds
`w0 ≤ w1`, every arrow modal, nothing fallible, `A` everywhere, `B` and `P`
at `w1` only.  So with a plain head a body `◯` is strictly stronger: it lets a
lax premise justify a non-lax conclusion — it *discharges* a constraint,
which is exactly the fault of Proposition 6.6's second half, sound only under
`⊢ ◯c`.  Read positively, `◯B ⊃ P` says "if `B` is derivable in the
abstraction, conclude `P` concretely": abstract derivability as a guard, a
two-level program whose least-model theorem is OPEN.
:::

:::theorem "mod_body_modal" (parent := "mod") (lean := "LaxLogic.QLL.BodyCirc.clause4")
With a modal head the two forms are interderivable, because `◯E` absorbs the
body's `◯`: `(A ∧ B) ⊃ ◯P ⊢ (A ∧ ◯B) ⊃ ◯P`, and conversely.
:::

:::theorem "mod_body_modal_ex" (parent := "mod") (uses := "mod_body_modal") (lean := "LaxLogic.QLL.BodyCirc.fo_ex_II_to_I")
The same with the `◯` under an existential, the shape a body actually has:
`∀t. (∃s. B s ∧ C s t) ⊃ ◯P t ⊢ ∀t. (∃s. ◯B s ∧ C s t) ⊃ ◯P t`, and
conversely.  So in an abstract program, whose heads are all modal, a body `◯`
adds nothing: it is `val`.
:::

:::theorem "mod_idem" (parent := "mod") (lean := "LaxLogic.QLL.BodyCirc.circ_circ_iff")
`◯◯A ⊣⊢ ◯A`: nesting one modality on itself is not a layering device.  But
`◯` under `⊃` and `⊥` does create structure — the variable-free fragment of
intuitionistic logic has two classes and gains infinitely many when `◯` is
added — so layers are to be sought in negative positions, not in depth.
:::

# `◯` over a conjunction: interderivable, not the same realisers

`◯(A ∧ B) ⊣⊢ ◯A ∧ ◯B` in QLL.  Under extraction the two sides have different
types, `C × (|A| × |B|)` against `(C × |A|) × (C × |B|)`: on the left one
constraint may relate both witnesses, on the right each constraint sees only
its own.  The two directions of the equivalence are the double strength
`dstr ((c₁,z₁),(c₂,z₂)) = (c₁ ∧ c₂, (z₁,z₂))` and the duplication
`dup (c,(z₁,z₂)) = ((c,z₁),(c,z₂))`.

:::theorem "mod_split" (parent := "mod") (lean := "LaxLogic.QLL.circ_and_split")
`◯(A ∧ B) ⊢ ◯A ∧ ◯B`.
:::

:::theorem "mod_join" (parent := "mod") (lean := "LaxLogic.QLL.circ_and_join")
`◯A ∧ ◯B ⊢ ◯(A ∧ B)`.
:::

:::theorem "mod_dstr_dup" (parent := "mod") (lean := "LaxLogic.QLL.dstr_dup")
`dstr ∘ dup` is the identity up to `⊣⊢`.
:::

:::theorem "mod_not_dup_dstr" (parent := "mod") (uses := "logic_sound") (lean := "LaxLogic.QLL.not_dup_dstr")
REFUTED: `dup ∘ dstr` is not; `((⊤,⋆),(⊥,⋆))` comes back with first
component `(⊤ ∧ ⊥, ⋆)`.  A clause body cannot be regrouped this way without
changing what is extracted.
:::

:::theorem "mod_andC" (parent := "mod") (uses := "abs_ext") (lean := "LaxLogic.QLL.AProof.ext_andC")
Fig. 3's `∧◯` is `dstr`: the second subgoal's constraint never sees the
first's witness.  A constraint relating two subgoals' witnesses can live only
in the table entry of the enclosing clause — a design property of the draft,
now visible.
:::

# The inclusion lemma

Two derivations of one `◯S` can differ in the clause applications they make,
and only there: the monad laws identify everything else.  The entries
`(w, t̃, z)` a derivation summons fix its constraint parametrically in the
table, and inclusion of entries gives entailment for every table.

:::definition "mod_entries" (parent := "mod") (uses := "abs_aproof") (lean := "LaxLogic.QLL.AProof.entries")
The table entries a derivation summons.
:::

:::theorem "mod_incl" (parent := "mod") (uses := "mod_entries, abs_ext") (lean := "LaxLogic.QLL.AProof.ext_prv_of_entries_subset")
If every entry `a` summons is summoned by `a'`, then `a'`'s extracted
constraint entails `a`'s, for every table.  Depends on `propext` only.
:::

:::theorem "mod_incl_eq" (parent := "mod") (uses := "mod_incl") (lean := "LaxLogic.QLL.AProof.ext_peq_of_entries_eq")
Equal entry sets give `⊣⊢`.
:::

This is what lets derivations be compared at the abstract level, before any
constraint is looked at: prefer the derivation that summons fewer entries.
Derivations differing only up to the monad laws are the same; derivations
with incomparable entry sets cannot be ranked without the domain, and the
two-world model says no abstract argument could rank them.

# Variable-only heads

Definition 5.1 forbids constructors in heads.  Nothing is lost, given the
equality axioms a constraint theory supplies — this is the first step of
Clark's completed definition — and the same two axioms suffice under a modal
head.

:::theorem "mod_flat1" (parent := "mod") (lean := "LaxLogic.QLL.HeadFlatten.flat_to_orig")
`∀x. (∃y. x = f y ∧ S y) ⊃ P x` with `∀x. x = x` proves `∀y. S y ⊃ P(f y)`.
:::

:::theorem "mod_flat2" (parent := "mod") (lean := "LaxLogic.QLL.HeadFlatten.orig_to_flat")
`∀y. S y ⊃ P(f y)` with `∀x y. x = y ⊃ P y ⊃ P x` proves the flattening.
:::

:::theorem "mod_flat_circ" (parent := "mod") (uses := "mod_flat2") (lean := "LaxLogic.QLL.HeadFlatten.orig_to_flat_circ")
The same with a `◯P(f y)` head and the same plain substitutivity axiom:
`◯E` lifts it.  So the fact is native to the `◯`-free fragment and unchanged
by `◯`; what the constraint framework contributes is that `=` is a constraint
solved in the domain rather than an algorithm wired into resolution.  This
development has no Herbrand equality solver, so constructor heads are
logically available and computationally not; the recommended design is
constructor heads as surface syntax elaborated to variable heads and `=`
constraints, with unification an untrusted oracle whose certificate is the
substitution.
:::

# Decorating a disjunct

A goal may be a disjunction, and one disjunct may carry the modality while the
other does not: `A ∨ ◯B`, "either `A` outright, or `B` up to a constraint".
Under an outer `◯` the decoration collapses; as a plain goal it is a genuine
weakening.

:::theorem "mod_disj_collapse" (parent := "mod") (lean := "LaxLogic.QLL.circ_or_circ_collapse")
`◯(A ∨ ◯B) ⊢ ◯(A ∨ B)`.
:::

:::theorem "mod_disj_expand" (parent := "mod") (lean := "LaxLogic.QLL.circ_or_circ_expand")
`◯(A ∨ B) ⊢ ◯(A ∨ ◯B)`: under `◯` the two goals are the same.
:::

:::theorem "mod_disj_weaker" (parent := "mod") (lean := "LaxLogic.QLL.or_to_or_circ")
`A ∨ B ⊢ A ∨ ◯B`.
:::

:::theorem "mod_disj_refuted" (parent := "mod") (uses := "logic_sound") (lean := "LaxLogic.QLL.BodyCirc.not_prv_or_circ_to_or")
REFUTED converse: `P ∨ ◯B` does not prove `P ∨ B`; in the two-world model the
lax branch is the only one open.  So a plain decorated goal accepts the
constraint-only route where the undecorated one does not.
:::

Under extraction a disjunction is a sum and each branch's constraint sits
inside its injection: the realiser of `A ∨ ◯B` is `|A| + (C × |B|)`, one
branch free and one costing a constraint.  What makes a branch free is not
that it applies no clauses but that every clause it applies has a `⊤` table
entry.

:::theorem "mod_disj_sum" (parent := "mod") (uses := "abs_ext") (lean := "LaxLogic.QLL.AProof.ext_orL")
`|∨◯ p| = (π₁|p| ∧ ⊤, inl π₂|p|)`: the branch's constraint travels with the
injection.
:::

:::theorem "mod_disj_top" (parent := "mod") (uses := "mod_entries") (lean := "LaxLogic.QLL.AProof.ext_top_of_pure")
A derivation whose summoned entries all have table value `⊤` extracts `⊤`.
:::

:::theorem "mod_disj_once" (parent := "mod") (uses := "mod_disj_top") (lean := "LaxLogic.QLL.AProof.once_of_pure")
A sound `once`: every other derivation's answer entails such a derivation's.
Succeed on the free branch and no other branch can be more general — what
Prolog's cut does by fiat and Andorra's quiet guards by entailment, obtained
here from the type.
:::

:::theorem "mod_disj_ex" (parent := "mod") (uses := "mod_disj_once, trees_checkC") (lean := "LaxLogic.QLL.BodyCirc.extD_top")
Kernel-run instance: `Q(t) ⊂ R(t) ∨ ∃s. B(s) ∧ t ≥ s + 2` with `R`
constraint-free.  The engine's first answer for `Q(z)` is `⊤` and its second
is `B`'s constraint `s ≥ 5 ∧ z ≥ s + 2`; the free branch extracts `⊤` under
the `◯` pass, and every other derivation's answer entails it.
:::

# Placements not yet built

A clause under the modality, `◯(∧Γ ⊃ M)`, carries a constraint independent of
the body witness; between it and the LLP clause lies a three-level hierarchy
by where the constraint may depend, and such a clause fires only against a
modal goal, which constrains clause order.  Negative occurrences, `¬◯B`, read
as negation as failure in the two-world model and are trivialised by the
fallible world in the four-world one — so solvability and negation as failure
are one frame parameter seen from two sides.  Both are stated with their
cells and not built.
