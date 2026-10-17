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
open LaxLogic.QLL.BodyCirc LaxLogic.QLL.HeadFlatten

#doc (Manual) "What the modality buys: placements and realisers" =>

This section is new; the 1997 report has no counterpart.  The report places
$`\bigcirc` in one position, the clause head, and a framework built on a
modality invites the question whether its other positions mean anything, and
whether they add to what programs can say or only repeat it.  Here the other
positions are examined: in a clause
body, over a conjunction, on one disjunct of a goal, and with constructors in
the head.  The finding is that the right notion for these questions is not
provability but the _realiser_, the value that extraction (Section 6) assigns:
two provably equivalent formulas can have different realisers, and then a
program is not the same program after one is rewritten into the other.  The
section also proves the inclusion lemma, which compares derivations by the
table entries they use.

# The modality in a clause body

Bodies are Σ-formulas, so $`\bigcirc` cannot occur in them.  What would it do?
The answer depends on the head.

*With a plain head, a body $`\bigcirc` can be deleted:*
$`(A \land \bigcirc_q B) \twoheadrightarrow P \vdash (A \land B) \twoheadrightarrow P`.

{stmt}`BodyCirc.body_circ_to_plain`

{leanDecl BodyCirc.body_circ_to_plain}

*REFUTED: the converse.*  $`(A \land B) \twoheadrightarrow P` does not prove
$`(A \land \bigcirc B) \twoheadrightarrow P`.  The countermodel has two worlds
$`w_0 \le w_1`, every arrow modal, nothing fallible, with $`A` true at both
worlds and $`B` and $`P` at $`w_1` only.

{stmt}`BodyCirc.not_prv_plain_to_body_circ`

{leanDecl BodyCirc.not_prv_plain_to_body_circ}

So with a plain head a body $`\bigcirc` is strictly stronger.  It lets a lax
premise justify a non-lax conclusion: it _discharges_ a constraint, which is
exactly the fault of the second half of Proposition 6.6 (Section 6), sound
only under $`\vdash \bigcirc c`.  Read positively,
$`\bigcirc B \twoheadrightarrow P` says “if $`B` is derivable in the
abstraction, conclude $`P` concretely”: abstract derivability as a guard, in a
two-level program whose least-model theorem is OPEN.

*With a modal head the two forms are interderivable,* because
$`(\bigcirc E)` absorbs the body's $`\bigcirc`:
$`(A \land B) \twoheadrightarrow \bigcirc_q P \vdash (A \land \bigcirc_q B) \twoheadrightarrow \bigcirc_q P`.
The converse is `clause3` in the library.

{stmt}`BodyCirc.clause4`

{leanDecl BodyCirc.clause4}

*The same, with the $`\bigcirc` under an existential,* the shape a body
actually has:

$$`\forall t.\, \bigl(\exists s.\, B(s) \land C(s, t)\bigr) \twoheadrightarrow \bigcirc_q P(t) \;\;\vdash\;\; \forall t.\, \bigl(\exists s.\, \bigcirc_q B(s) \land C(s, t)\bigr) \twoheadrightarrow \bigcirc_q P(t),`

the two clauses being `clEII` and `clEI` in Lean; the converse is
`fo_ex_I_to_II`.  So in an abstract program, whose heads are all modal, a body
$`\bigcirc` adds nothing: its realiser is $`\mathit{val}`.

{stmt}`BodyCirc.fo_ex_II_to_I`

{leanDecl BodyCirc.fo_ex_II_to_I}

*Nesting does not layer:* $`\bigcirc_q \bigcirc_q A` and $`\bigcirc_q A` are
interderivable from any context.  But $`\bigcirc` under $`\twoheadrightarrow`
and $`\bot` does create structure (the variable-free fragment of intuitionistic
logic has two classes up to provable equivalence and gains infinitely many when
$`\bigcirc` is added), so layers are to be sought in negative positions, not
in depth.

{stmt}`BodyCirc.circ_circ_iff`

{leanDecl BodyCirc.circ_circ_iff}

# The modality over a conjunction: interderivable, not the same realisers

$`\bigcirc (A \land B) \dashv\vdash \bigcirc A \land \bigcirc B` in QLL.  Under
extraction the two sides have different types,

$$`C \times (|A| \times |B|) \qquad\text{against}\qquad (C \times |A|) \times (C \times |B|):`

on the left one constraint may relate both witnesses, on the right each
constraint sees only its own.  The two directions of the equivalence are
realised by the double strength and the duplication,

$$`\mathit{dstr}\,((c_1, z_1), (c_2, z_2)) = (c_1 \land c_2, (z_1, z_2)), \qquad \mathit{dup}\,(c, (z_1, z_2)) = ((c, z_1), (c, z_2)).`

*Splitting:* $`\bigcirc_q (A \land B) \vdash \bigcirc_q A \land \bigcirc_q B`.

{stmt}`circ_and_split`

{leanDecl circ_and_split}

*Joining:* $`\bigcirc_q A \land \bigcirc_q B \vdash \bigcirc_q (A \land B)`.

{stmt}`circ_and_join`

{leanDecl circ_and_join}

*One composite is the identity:* $`\mathit{dstr} \circ \mathit{dup}` is the
identity up to $`\mathit{WEq}`.

{stmt}`dstr_dup`

{leanDecl dstr_dup}

*REFUTED: the other composite is the identity.*
$`\mathit{dup} \circ \mathit{dstr}` sends $`((\top, \star), (\bot, \star))` to a
pair whose first component is $`(\top \land \bot, \star)`, not
$`(\top, \star)` up to $`\mathit{WEq}`.  So a clause body cannot be regrouped
this way without changing what is extracted.

{stmt}`not_dup_dstr`

{leanDecl not_dup_dstr}

*Fig. 3's $`\land\bigcirc` is $`\mathit{dstr}`:* the second subgoal's
constraint never sees the first subgoal's witness.  A constraint relating two
subgoals' witnesses can therefore live only in the table entry of the
enclosing clause.  This is a design property of the 1997 report, made visible here.

{stmt}`AProof.ext_andC`

{leanDecl AProof.ext_andC}

# The inclusion lemma

Two derivations of one $`\bigcirc S` can differ in the clause applications they
make, and only there: the monad laws identify everything else.  The _entries_
$`(w, \tilde{t}, z)` that a derivation uses (clause $`w` at instance
$`\tilde{t}` with body witness $`z`) fix its extracted constraint
parametrically in the table, and inclusion of entries gives entailment for
every table.

*The table entries a derivation uses.*  This is a definition, so no statement
is displayed.

{stmt}`AProof.entries`

{leanDecl AProof.entries}

*The inclusion lemma.*  If every entry used by $`a` is used by $`a'`, then the
constraint extracted from $`a'` entails the one extracted from $`a`, for every
table $`T`.  It depends on `propext` only.

{stmt}`AProof.ext_prv_of_entries_subset`

{leanDecl AProof.ext_prv_of_entries_subset}

*Equal entry sets give $`\dashv\vdash`.*

{stmt}`AProof.ext_peq_of_entries_eq`

{leanDecl AProof.ext_peq_of_entries_eq}

This is what lets derivations be compared at the abstract level, before any
constraint is looked at: prefer the derivation that uses fewer entries.
Derivations that differ only up to the monad laws are the same; derivations
with incomparable entry sets cannot be ranked without the domain, and the
two-world model says that no abstract argument could rank them.

# Variable-only heads

Definition 5.1 forbids constructors in heads.  Nothing is lost, given the
equality axioms a constraint theory supplies; this is the first step of
Clark's completed definition, and the same two axioms suffice under a modal
head.  Write

$$`\mathit{orig} = \forall y.\, S(y) \twoheadrightarrow P(f(y)), \qquad \mathit{flat} = \forall x.\, \bigl(\exists y.\, x = f(y) \land S(y)\bigr) \twoheadrightarrow P(x),`

$$`\mathit{eqRefl} = \forall x.\, x = x, \qquad \mathit{eqSubst} = \forall x\, y.\, x = y \twoheadrightarrow P(y) \twoheadrightarrow P(x),`

where $`=` is an ordinary predicate symbol.

*The flattened clause and reflexivity prove the original.*

{stmt}`HeadFlatten.flat_to_orig`

{leanDecl HeadFlatten.flat_to_orig}

*The original clause and substitutivity prove the flattened one.*

{stmt}`HeadFlatten.orig_to_flat`

{leanDecl HeadFlatten.orig_to_flat}

*The same with a modal head*
$`\mathit{orig}_q = \forall y.\, S(y) \twoheadrightarrow \bigcirc_q P(f(y))` and
$`\mathit{flat}_q = \forall x.\, (\exists y.\, x = f(y) \land S(y)) \twoheadrightarrow \bigcirc_q P(x)`,
and the same plain substitutivity axiom: $`(\bigcirc E)` lifts it.

{stmt}`HeadFlatten.orig_to_flat_circ`

{leanDecl HeadFlatten.orig_to_flat_circ}

So the fact is native to the $`\bigcirc`-free fragment and unchanged by
$`\bigcirc`.  What the constraint framework contributes is that $`=` is a
constraint solved in the domain rather than an algorithm wired into
resolution.  This development has no Herbrand equality solver, so constructor
heads are logically available and computationally not.  The recommended
design is constructor heads as surface syntax, elaborated to variable heads
and $`=` constraints, with unification an untrusted oracle whose certificate
is the substitution.

# Decorating a disjunct

A goal may be a disjunction one of whose disjuncts carries the modality:
$`A \lor \bigcirc B`, “either $`A` outright, or $`B` up to a constraint”.
Under an outer $`\bigcirc` the decoration collapses; as a plain goal it is a
genuine weakening.

*Collapse:* $`\bigcirc_q (A \lor \bigcirc_q B) \vdash \bigcirc_q (A \lor B)`.

{stmt}`circ_or_circ_collapse`

{leanDecl circ_or_circ_collapse}

*Expansion:* $`\bigcirc_q (A \lor B) \vdash \bigcirc_q (A \lor \bigcirc_q B)`.
Under $`\bigcirc` the two goals are the same.

{stmt}`circ_or_circ_expand`

{leanDecl circ_or_circ_expand}

*Weakening:* $`A \lor B \vdash A \lor \bigcirc_q B`.

{stmt}`or_to_or_circ`

{leanDecl or_to_or_circ}

*REFUTED: the converse of weakening.*  $`P \lor \bigcirc B` does not prove
$`P \lor B`: in the two-world model the lax branch is the only one open.  So a
plain decorated goal accepts the constraint-only route where the undecorated
one does not.

{stmt}`BodyCirc.not_prv_or_circ_to_or`

{leanDecl BodyCirc.not_prv_or_circ_to_or}

Under extraction a disjunction is a sum, and each branch's constraint sits
inside its injection: the realiser of $`A \lor \bigcirc B` has type
$`|A| + (C \times |B|)`, one branch free and one costing a constraint.  What
makes a branch free is not that it applies no clauses but that every clause it
applies has the table entry $`\top`.

*Extraction at a left injection:*
$`|{\lor}\bigcirc\, p| = (\pi_1|p| \land \top,\; \mathit{inl}\; \pi_2|p|)`; the
branch's constraint travels with the injection.

{stmt}`AProof.ext_orL`

{leanDecl AProof.ext_orL}

*A derivation whose entries all have table value $`\top` extracts $`\top`.*

{stmt}`AProof.ext_top_of_pure`

{leanDecl AProof.ext_top_of_pure}

*A sound “once”.*  Every other derivation's answer entails such a derivation's
answer.  Succeed on the free branch, and no other branch can be more general:
what Prolog's cut does by fiat, and the quiet guards of the Andorra Kernel
Language do by entailment, is obtained here from the type.

{stmt}`AProof.once_of_pure`

{leanDecl AProof.once_of_pure}

*A kernel-run instance.*  Take the program
$`Q(t) \leftarrow R(t) \lor \exists s.\, B(s) \land t \ge s + 2`, with $`R`
constraint-free and $`B(s) \leftarrow s \ge 5` (`exD` in Lean).  The engine's
first answer for $`Q(z)` is $`\top`, and its second is $`B`'s constraint,
$`s \ge 5 \land z \ge s + 2`.  The free branch extracts $`\top` under the
$`\bigcirc` pass, and every other derivation's answer entails it.

{stmt}`BodyCirc.extD_top`

{leanDecl BodyCirc.extD_top}

# Placements not yet built

A clause under the modality, $`\bigcirc (\bigwedge \Gamma \twoheadrightarrow M)`,
carries a constraint independent of the body witness.  Between it and the
clause of a lax logic program lies a three-level hierarchy according to what
the constraint may depend on, and such a clause fires only against a modal
goal, which constrains clause order.  Negative occurrences,
$`\lnot \bigcirc B`, read as negation as failure in the two-world model and are
trivialised by the fallible world in the four-world one, so solvability and
negation as failure are one frame parameter seen from two sides.  Both are
stated with their designed cells and not built (OPEN).
