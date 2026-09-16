import Verso
import VersoManual
import LaxLogic.QLL
import CLPPaper.Src
import CLPPaper.Math

open Verso.Genre
open Verso.Genre.Manual
open CLPPaper CLPPaper.Math

#doc (Manual) "What the modality buys: placements and realisers" =>

The draft places $`\bigcirc` in one position, the clause head.  This section asks
what the other positions would do, and finds that the right notion for
answering is not provability but the realiser: two provably equivalent
formulas can have different realisers, and then a program is not the same
program after rewriting one to the other.

# `◯` in a clause body

Bodies are Σ-formulas, so $`\bigcirc` cannot occur in them.  What would it do?  The
answer turns on the head.

With a plain head, a body $`\bigcirc` implies the same clause with the $`\bigcirc` deleted:
{stmt}`LaxLogic.QLL.BodyCirc.body_circ_to_plain`

{docstring LaxLogic.QLL.BodyCirc.body_circ_to_plain +allowMissing}

{srcLink}`LaxLogic.QLL.BodyCirc.body_circ_to_plain`

REFUTED converse: $`(A \land B) \supset P` does not prove $`(A \land \bigcirc B) \supset P`.  Two worlds
$`w_0 \le w_1`, every arrow modal, nothing fallible, `A` everywhere, `B` and `P`
at `w1` only.  So with a plain head a body $`\bigcirc` is strictly stronger: it lets a
lax premise justify a non-lax conclusion — it *discharges* a constraint,
which is exactly the fault of Proposition 6.6's second half, sound only under
$`\vdash \bigcirc c`.  Read positively, $`\bigcirc B \supset P` says "if `B` is derivable in the
abstraction, conclude `P` concretely": abstract derivability as a guard, a
two-level program whose least-model theorem is OPEN.

{stmt}`LaxLogic.QLL.BodyCirc.not_prv_plain_to_body_circ`

{docstring LaxLogic.QLL.BodyCirc.not_prv_plain_to_body_circ +allowMissing}

{srcLink}`LaxLogic.QLL.BodyCirc.not_prv_plain_to_body_circ`

With a modal head the two forms are interderivable, because $`\bigcirc E` absorbs the
body's $`\bigcirc`: $`(A \land B) \supset \bigcirc P \vdash (A \land \bigcirc B) \supset \bigcirc P`, and conversely.

{stmt}`LaxLogic.QLL.BodyCirc.clause4`

{docstring LaxLogic.QLL.BodyCirc.clause4 +allowMissing}

{srcLink}`LaxLogic.QLL.BodyCirc.clause4`

The same with the $`\bigcirc` under an existential, the shape a body actually has:
$`\forall t. (\exists s. B s \land C s t) \supset \bigcirc P t \vdash \forall t. (\exists s. \bigcirc B s \land C s t) \supset \bigcirc P t`, and
conversely.  So in an abstract program, whose heads are all modal, a body $`\bigcirc`
adds nothing: it is `val`.

{stmt}`LaxLogic.QLL.BodyCirc.fo_ex_II_to_I`

{docstring LaxLogic.QLL.BodyCirc.fo_ex_II_to_I +allowMissing}

{srcLink}`LaxLogic.QLL.BodyCirc.fo_ex_II_to_I`

$`\bigcirc \bigcirc A \dashv\vdash \bigcirc A`: nesting one modality on itself is not a layering device.  But
$`\bigcirc` under $`\supset` and $`\bot` does create structure — the variable-free fragment of
intuitionistic logic has two classes and gains infinitely many when $`\bigcirc` is
added — so layers are to be sought in negative positions, not in depth.

{stmt}`LaxLogic.QLL.BodyCirc.circ_circ_iff`

{docstring LaxLogic.QLL.BodyCirc.circ_circ_iff +allowMissing}

{srcLink}`LaxLogic.QLL.BodyCirc.circ_circ_iff`

# `◯` over a conjunction: interderivable, not the same realisers

$`\bigcirc (A \land B) \dashv\vdash \bigcirc A \land \bigcirc B` in QLL.  Under extraction the two sides have different
types, $`C \times (|A| \times |B|)` against $`(C \times |A|) \times (C \times |B|)`: on the left one
constraint may relate both witnesses, on the right each constraint sees only
its own.  The two directions of the equivalence are the double strength
$`\mathit{dstr} ((c_1,z_1),(c_2,z_2)) = (c_1 \land c_2, (z_1,z_2))` and the duplication
`dup (c,(z₁,z₂)) = ((c,z₁),(c,z₂))`.

{stmt}`LaxLogic.QLL.circ_and_split`

{docstring LaxLogic.QLL.circ_and_split +allowMissing}

{srcLink}`LaxLogic.QLL.circ_and_split`

{stmt}`LaxLogic.QLL.circ_and_join`

{docstring LaxLogic.QLL.circ_and_join +allowMissing}

{srcLink}`LaxLogic.QLL.circ_and_join`

$`\mathit{dstr} \circ \mathit{dup}` is the identity up to $`\dashv\vdash`.

{stmt}`LaxLogic.QLL.dstr_dup`

{docstring LaxLogic.QLL.dstr_dup +allowMissing}

{srcLink}`LaxLogic.QLL.dstr_dup`

REFUTED: $`\mathit{dup} \circ \mathit{dstr}` is not; $`((\top,\star),(\bot,\star))` comes back with first
component $`(\top \land \bot, \star)`.  A clause body cannot be regrouped this way without
changing what is extracted.

{stmt}`LaxLogic.QLL.not_dup_dstr`

{docstring LaxLogic.QLL.not_dup_dstr +allowMissing}

{srcLink}`LaxLogic.QLL.not_dup_dstr`

Fig. 3's $`\land \bigcirc` is `dstr`: the second subgoal's constraint never sees the
first's witness.  A constraint relating two subgoals' witnesses can live only
in the table entry of the enclosing clause — a design property of the draft,
now visible.

{stmt}`LaxLogic.QLL.AProof.ext_andC`

{docstring LaxLogic.QLL.AProof.ext_andC +allowMissing}

{srcLink}`LaxLogic.QLL.AProof.ext_andC`

# The inclusion lemma

Two derivations of one $`\bigcirc S` can differ in the clause applications they make,
and only there: the monad laws identify everything else.  The entries
`(w, t̃, z)` a derivation summons fix its constraint parametrically in the
table, and inclusion of entries gives entailment for every table.

The table entries a derivation summons.

{stmt}`LaxLogic.QLL.AProof.entries`

{docstring LaxLogic.QLL.AProof.entries +allowMissing}

{srcLink}`LaxLogic.QLL.AProof.entries`

If every entry `a` summons is summoned by `a'`, then `a'`'s extracted
constraint entails `a`'s, for every table.  Depends on `propext` only.

{stmt}`LaxLogic.QLL.AProof.ext_prv_of_entries_subset`

{docstring LaxLogic.QLL.AProof.ext_prv_of_entries_subset +allowMissing}

{srcLink}`LaxLogic.QLL.AProof.ext_prv_of_entries_subset`

Equal entry sets give $`\dashv\vdash`.

{stmt}`LaxLogic.QLL.AProof.ext_peq_of_entries_eq`

{docstring LaxLogic.QLL.AProof.ext_peq_of_entries_eq +allowMissing}

{srcLink}`LaxLogic.QLL.AProof.ext_peq_of_entries_eq`

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

$`\forall x. (\exists y. x = f y \land S y) \supset P x` with $`\forall x. x = x` proves $`\forall y. S y \supset P(f y)`.

{stmt}`LaxLogic.QLL.HeadFlatten.flat_to_orig`

{docstring LaxLogic.QLL.HeadFlatten.flat_to_orig +allowMissing}

{srcLink}`LaxLogic.QLL.HeadFlatten.flat_to_orig`

$`\forall y. S y \supset P(f y)` with $`\forall x y. x = y \supset P y \supset P x` proves the flattening.

{stmt}`LaxLogic.QLL.HeadFlatten.orig_to_flat`

{docstring LaxLogic.QLL.HeadFlatten.orig_to_flat +allowMissing}

{srcLink}`LaxLogic.QLL.HeadFlatten.orig_to_flat`

The same with a $`\bigcirc P(f y)` head and the same plain substitutivity axiom:
$`\bigcirc E` lifts it.  So the fact is native to the $`\bigcirc`-free fragment and unchanged
by $`\bigcirc`; what the constraint framework contributes is that `=` is a constraint
solved in the domain rather than an algorithm wired into resolution.  This
development has no Herbrand equality solver, so constructor heads are
logically available and computationally not; the recommended design is
constructor heads as surface syntax elaborated to variable heads and `=`
constraints, with unification an untrusted oracle whose certificate is the
substitution.

{stmt}`LaxLogic.QLL.HeadFlatten.orig_to_flat_circ`

{docstring LaxLogic.QLL.HeadFlatten.orig_to_flat_circ +allowMissing}

{srcLink}`LaxLogic.QLL.HeadFlatten.orig_to_flat_circ`

# Decorating a disjunct

A goal may be a disjunction, and one disjunct may carry the modality while the
other does not: $`A \lor \bigcirc B`, "either `A` outright, or `B` up to a constraint".
Under an outer $`\bigcirc` the decoration collapses; as a plain goal it is a genuine
weakening.

{stmt}`LaxLogic.QLL.circ_or_circ_collapse`

{docstring LaxLogic.QLL.circ_or_circ_collapse +allowMissing}

{srcLink}`LaxLogic.QLL.circ_or_circ_collapse`

$`\bigcirc (A \lor B) \vdash \bigcirc (A \lor \bigcirc B)`: under $`\bigcirc` the two goals are the same.

{stmt}`LaxLogic.QLL.circ_or_circ_expand`

{docstring LaxLogic.QLL.circ_or_circ_expand +allowMissing}

{srcLink}`LaxLogic.QLL.circ_or_circ_expand`

{stmt}`LaxLogic.QLL.or_to_or_circ`

{docstring LaxLogic.QLL.or_to_or_circ +allowMissing}

{srcLink}`LaxLogic.QLL.or_to_or_circ`

REFUTED converse: $`P \lor \bigcirc B` does not prove $`P \lor B`; in the two-world model the
lax branch is the only one open.  So a plain decorated goal accepts the
constraint-only route where the undecorated one does not.

{stmt}`LaxLogic.QLL.BodyCirc.not_prv_or_circ_to_or`

{docstring LaxLogic.QLL.BodyCirc.not_prv_or_circ_to_or +allowMissing}

{srcLink}`LaxLogic.QLL.BodyCirc.not_prv_or_circ_to_or`

Under extraction a disjunction is a sum and each branch's constraint sits
inside its injection: the realiser of $`A \lor \bigcirc B` is $`|A| + (C \times |B|)`, one
branch free and one costing a constraint.  What makes a branch free is not
that it applies no clauses but that every clause it applies has a $`\top` table
entry.

$`|\lor \bigcirc p| = (\pi _1|p| \land \top, \mathit{inl} \pi _2|p|)`: the branch's constraint travels with the
injection.

{stmt}`LaxLogic.QLL.AProof.ext_orL`

{docstring LaxLogic.QLL.AProof.ext_orL +allowMissing}

{srcLink}`LaxLogic.QLL.AProof.ext_orL`

A derivation whose summoned entries all have table value $`\top` extracts $`\top`.

{stmt}`LaxLogic.QLL.AProof.ext_top_of_pure`

{docstring LaxLogic.QLL.AProof.ext_top_of_pure +allowMissing}

{srcLink}`LaxLogic.QLL.AProof.ext_top_of_pure`

A sound `once`: every other derivation's answer entails such a derivation's.
Succeed on the free branch and no other branch can be more general — what
Prolog's cut does by fiat and Andorra's quiet guards by entailment, obtained
here from the type.

{stmt}`LaxLogic.QLL.AProof.once_of_pure`

{docstring LaxLogic.QLL.AProof.once_of_pure +allowMissing}

{srcLink}`LaxLogic.QLL.AProof.once_of_pure`

Kernel-run instance: $`Q(t) \subset R(t) \lor \exists s. B(s) \land t \ge s + 2` with `R`
constraint-free.  The engine's first answer for `Q(z)` is $`\top` and its second
is `B`'s constraint $`s \ge 5 \land z \ge s + 2`; the free branch extracts $`\top` under
the $`\bigcirc` pass, and every other derivation's answer entails it.

{stmt}`LaxLogic.QLL.BodyCirc.extD_top`

{docstring LaxLogic.QLL.BodyCirc.extD_top +allowMissing}

{srcLink}`LaxLogic.QLL.BodyCirc.extD_top`

# Placements not yet built

A clause under the modality, $`\bigcirc (\land \Gamma \supset M)`, carries a constraint independent of
the body witness; between it and the LLP clause lies a three-level hierarchy
by where the constraint may depend, and such a clause fires only against a
modal goal, which constrains clause order.  Negative occurrences, $`\lnot \bigcirc B`, read
as negation as failure in the two-world model and are trivialised by the
fallible world in the four-world one — so solvability and negation as failure
are one frame parameter seen from two sides.  Both are stated with their
cells and not built.
