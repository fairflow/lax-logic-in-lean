import Verso
import VersoManual
import VersoBlueprint
import LaxLogic.Obligation

open Verso.Genre
open Verso.Genre.Manual
open Informal
open LaxLogic.Obligation

#doc (Manual) "Introduction" =>

# The problem

A verification that uses abstraction accumulates side conditions, and it
accumulates them in the wrong direction.  Fairtlough, Mendler and Cheng put it
this way:

> A fundamental obstacle to the sound use of abstraction techniques is that the
> associated constraints accumulate in the opposite direction to the proof
> effort, whether forward or goal-directed proof methods are used.  Thus a
> situation typically arises where it is not known at the outset what exactly
> needs to be proved.

For a circuit this is not a nuisance but the whole difficulty.  The timing
constraints under which a latch holds its state are not an input to the
verification; they are what the verification is for.  Herbert's proofs of the
basic memory devices were, as the same authors observe, "the result of several
iterations which were needed to discover the exact timing constraints necessary
to prove them".

Their answer is to split a theory along two dimensions: an _abstract_ dimension
carrying functional content, and a _constraint_ dimension carrying the offset
between the abstract model and the concrete one.  Reasoning proceeds abstractly;
the constraint is computed alongside as a lambda term; and a _refinement_ step
recombines the two into a concrete-level theorem of the form "the device behaves
as specified, provided the following constraints hold".  The constraints are
therefore _synthesised_, not guessed.

# What this development is

This paper describes a Lean 4 library, `LaxLogic.Obligation`, that carries that
method out inside a dependently typed proof assistant, together with the tactics
and commands that make it run without a person supplying the answers.

The mathematical content is a reformulation, not a port: the Isabelle/HOL
development the original paper describes was not consulted, and dependent types
change what has to be built.  Where the original must introduce refinement types
`|M|` by a separate mapping because HOL cannot compute them, Lean computes them;
where the original must define a fresh set of connectives because the abstract
ones do not have the expected HOL types, most of the corresponding equations
here hold by `rfl`.

What is new is the other half.  A method that computes constraints is only
usable if the machine computes them, and in the original the constraint
reductions are performed on paper — the step from equation (8) to equation (9)
of the latch analysis is justified by the sentence "given such reasoning is
built into constraint reductions".  Here it is built in.

# Contributions

The library provides, in order of dependence:

1. The two lax modalities `◯∀` and `◯∃` with the abstraction and refinement
   equations of the original Fig. 4, and the timing correspondence they were
   invented for.
2. `postpone`, a proof hole that **records** a goal as a named obligation rather
   than asserting it, and `postponing theorem`, which folds the recorded
   obligations into the finished statement.  A declaration built this way is
   sorry-free and its axioms are those of its finished parts.
3. `lax_apply`, which lets a theorem that is _itself_ holed be used as an
   abstract lemma: the borrowed obligations move into the caller's ledger.  This
   is what makes the method modular, and it is Mendler's monoid law on
   constraint lists as an operation rather than a theorem.
4. A solver for the `(max, +)` fragment that **computes** each obligation's
   reduced form and the single implication `C ⊃ ◯φ` over the whole constraint
   set.  It runs automatically as each declaration is recorded.  The normaliser
   is not verified and does not need to be: it proposes, and `omega` certifies
   against the kernel.
5. Two constraint models, timing and resource budgets, and four worked circuits:
   the introductory example of the original paper, its RS latch, this
   repository's ripple-carry and carry-lookahead adders, and a three-stage
   datapath assembled modularly from them.

Everything stated here is machine-checked with pinned axioms.  Where a
dependency on `Classical.choice` enters — it enters in exactly one place, and
for a reason to do with the certifying tactic rather than the mathematics — it
is pinned and explained rather than absorbed.

# A note on "conservative"

The original paper's Theorem 1 states that the `p : M` construction is a
conservative extension of HOL, and describes its Isabelle implementation as a
purely definitional one.  That result belongs to a setting where `p : M` is new
syntax in the object logic.  Nothing of the kind is added here: the modalities,
`Debt` and `weak` are ordinary Lean definitions, the Fig. 4 equations are
ordinary theorems — several of them `rfl` — and the modal notation is notation.
The extension is definitional, or merely surface-syntactic, so conservativity is
not the right notion for it: there is nothing for it to be conservative over.

The property that does need checking is different and weaker.  The obligation
mechanism *does* add declarations to the environment, by metaprogramming, and
what must be ruled out is that it adds an axiom.  That is checked by a command,
`#obligations_audit`, rather than by inspection.

:::definition "intro_debt" (parent := "intro") (lean := "Debt")
The one-witness case of the weakening modality, and the object the whole
library is about: a claim held modulo an outstanding constraint.
:::

:::group "intro"
Orientation.
:::
