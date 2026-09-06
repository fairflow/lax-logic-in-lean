import Verso
import VersoManual
import VersoBlueprint
import LaxLogic.Obligation

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "The machinery" =>

# The two modalities

The original paper's Fig. 4 defines the meaning of a constraint/formula pair
`p : M` by recursion on `M`.  Two of its nine clauses are the modal ones:

```
(p : ◯∃M) = ∃z :: |M|. p z ∧ (z : M)
(p : ◯∀M) = ∀z :: |M|. p z ⊃ (z : M)
```

In Lean these are two definitions over a constraint type and are the whole of
the modal apparatus.  A _constraint_ and a _refined formula_ are both predicates
on the witness type; the two modalities quantify over the witness in the two
possible ways.

:::group "mach_modal"
The modalities and their rules.
:::

:::definition "laxall" (parent := "mach_modal") (lean := "LaxLogic.Obligation.LaxAll")
The weakening modality: the claim holds at every witness the constraint admits.
:::

:::definition "laxex" (parent := "mach_modal") (lean := "LaxLogic.Obligation.LaxEx")
The strengthening modality: some admitted witness carries the claim.
:::

Notation `◯∀[p] M` and `◯∃[p] M` is used throughout.  The rules the original
paper derives from Fig. 4 are here ordinary theorems, and the two that do the
work in every example are the conjunction and implication rules.

:::theorem "laxall_meet" (parent := "mach_modal") (uses := "laxall") (lean := "LaxLogic.Obligation.laxAll_meet")
The rule `◯∧`: constraints on a shared witness combine by conjunction.
:::

:::theorem "laxall_image" (parent := "mach_modal") (uses := "laxall") (lean := "LaxLogic.Obligation.laxAll_image")
The rule `◯⊃`: a constraint propagates through a component along the direct
image of the component's refinement part.
:::

:::theorem "laxall_mono" (parent := "mach_modal") (uses := "laxall") (lean := "LaxLogic.Obligation.laxAll_mono")
`◯∀` is antitone in the constraint.  Every synthesised constraint in the case
studies below arises as the side condition of one application of this rule: the
offset between what a stage delivers and what the next demands.
:::

The one-witness case is the one the tactic machinery uses.

:::definition "debt" (parent := "mach_modal") (uses := "laxall") (lean := "LaxLogic.Obligation.Debt")
`Debt C A` is `A` modulo the outstanding constraint `C`.
:::

Read epistemically, `Debt C A` is the open nucleus of the repository's belief
development, and this holds by `rfl` rather than by analogy.

:::theorem "debt_nucleus" (parent := "mach_modal") (uses := "debt") (lean := "LaxLogic.Obligation.debt_eq_openNucleus")
An obligation is a hypothetical belief: if the constraint were known, the belief
in the claim would convert to knowledge; if the constraint is false, the belief
is vacuous.
:::

That vacuity is not decoration.  `Debt False A` holds for every `A`, so a
modality with no admissible class of constraints says nothing at all — which is
why the models of the next section fix one.

# A hole that records instead of asserting

Lean's `sorry` elaborates to `sorryAx`, which inhabits the goal.  A declaration
containing one _asserts_ its statement on no evidence, and `#print axioms`
reports only that something is missing, not what.

`postpone` closes a goal differently.  It reverts the part of the local context
the goal reaches, records the resulting closed proposition as a named
obligation, and discharges the goal from a hypothesis that the enclosing
`postponing theorem` command then abstracts into the statement.  What reaches
the environment is

```
theorem foo : foo.obligation1 → … → foo.obligationN → <the intended goal>
```

a complete, sorry-free theorem about a weaker statement, whose axioms are those
of its finished parts.  In Mendler's notation from his thesis this is
`weak [γₙ, …, γ₁] φ`, the constraint applied by iterated implication.

:::definition "postpone" (parent := "mach_tactic") (uses := "debt") (lean := "LaxLogic.Obligation.postponeCore")
The whole of `postpone`, on an explicit goal.  Factored out so that `lax_apply`
can reuse it rather than reimplement it.
:::

:::group "mach_tactic"
The tactic and the ledger.
:::

:::definition "weak" (parent := "mach_tactic") (uses := "debt") (lean := "LaxLogic.Obligation.weak")
Mendler's `weak`: a constraint is a list of propositions, applied by iterated
implication.  The unit is the empty list and composition is append.
:::

:::theorem "weak_append" (parent := "mach_tactic") (uses := "weak") (lean := "LaxLogic.Obligation.weak_append")
The monoid law of Mendler's triple.  This is why obligations from different
holes, and from different modules, combine by concatenating ledgers.
:::

Three design points were forced by getting them wrong first.

**Obligations must not re-quantify the declaration's own binders.**  An
obligation that did would be a statement about all parameters rather than the
ones at hand, and no assumption about the actual parameters could discharge it.
Obligations are therefore predicates over the binders, applied to them in the
finished statement.

**A non-`Prop` goal must be refused.**  It would produce an ill-typed obligation
definition, the kernel would reject it, and `addDecl`'s `addAsAxiom` fallback
would then add the obligation _as an axiom_, silently.  This was observed before
it was guarded.

**The reverted context must be the part the goal reaches, not all of it.**
Reverting everything is sound — a stronger obligation still implies the goal —
but it produces obligations no one can read.

# The ledger, and checking that nothing was smuggled in

Recorded obligations live in a persistent environment extension, so a theorem in
one module can be built from holed theorems in another and the whole
accumulated debt is reportable.  `#obligations` prints it; `#obligations_json`
prints the same for tooling, which is the hook an automated loop would use: the
obligations are the goals to attack, they are named constants so a proof can be
stated against them elsewhere, and the count is a progress measure that a binary
sorry-or-not cannot provide.

The mechanism must not be able to introduce an axiom, and this is checked rather
than assumed.  (Only that: the definitions and rules of the previous section add
nothing to Lean's logic, being ordinary definitions and theorems, so the
question of conservativity does not arise for them.  It is the metaprogramming
that has to be watched.)  `#obligations_audit` verifies, for every declaration in the
ledger, that it is a theorem and not an axiom, that each of its obligations is a
definition, that no `sorryAx` occurs, and that nothing depends on a constant the
mechanism itself introduced.  It throws rather than reporting, so it fails a
build.

Both directions of that gate have been watched.  Injecting `Classical.choice`
into a case-study lemma reddens the audit line and two axiom pins; replacing a
`postpone` by `sorry` does something more informative — the obligation constant
is then **not in the environment at all**, and every downstream reference fails
with `Unknown constant`.  That is the difference the library exists for.
