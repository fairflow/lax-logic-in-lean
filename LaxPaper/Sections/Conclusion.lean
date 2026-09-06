import Verso
import VersoManual
import VersoBlueprint
import LaxLogic.Obligation

open Verso.Genre
open Verso.Genre.Manual
open Informal
open LaxLogic.Obligation

#doc (Manual) "Conclusion" =>

# What runs

The method of Fairtlough, Mendler and Cheng runs in Lean, and the step their
paper leaves to the reader — the reduction of a synthesised constraint to a
readable one — runs too.  Concretely, for a declaration written with `postpone`
in place of its side conditions, the following happen with nothing supplied by
the author: the obligations are recorded and named; obligations borrowed from
other holed theorems are carried along and remain the callee's own constants;
each obligation in the `(max, +)` fragment is reduced to a conjunction of linear
inequalities, one per path; the whole set is folded into a single implication
`C ⊃ ◯φ`; and at a constraint model the set is closed by one call to `omega`,
yielding the concrete theorem.

Four circuits go through it: the original paper's introductory example, its RS
latch — recovering equations (8) and (9) — and this repository's ripple-carry
and carry-lookahead adders, with a three-stage datapath assembled modularly from
the last of them.  Two constraint models are carried side by side, timing and
resource budgets, differing in how constraints combine and sharing every tactic.

# On "conservative"

The original paper's Theorem 1 states that the `p : M` construction is a
conservative extension of HOL, and its implementation is described as a purely
definitional one.  That result belongs to a setting where `p : M` is new syntax
in the object logic.  Nothing of the kind happens here: `◯∀`, `◯∃`, `Debt` and
`weak` are ordinary Lean definitions, the Fig. 4 equations are ordinary
theorems — several of them `rfl` — and `◯∀[p] M` is notation.  The extension is
definitional, or merely surface-syntactic, so **conservativity is not the right
notion**: there is nothing for it to be conservative over.

What does need checking is a different and weaker property: that the obligation
_mechanism_ — which does add declarations to the environment, by
metaprogramming — introduces no axiom of its own.  That is checked by
`#obligations_audit` rather than by inspection, and both directions of the gate
have been watched.  The module implementing it is currently called
`Conservativity.lean`, which overstates what it does; the name is owed a
correction.

# Limitations

The following are known and none is hidden by the gates.

* **One constraint reduction is still hand-written.**  The latch's internal
  memory constraint has the quantified time on both sides of its bound, which is
  outside the `(max, +)` fragment.  The solver reports this and leaves the
  obligation unreduced.
* **`max` costs `Classical.choice`.**  `omega` normalises `max` classically, so
  a constraint arising from a parallel join is certified with it and one that is
  not stays at `propext` and `Quot.sound`.  This is the certifying tactic, not
  the mathematics; `Nat.max_le` is `[propext]`.
* **Obligations are deduplicated syntactically**, so two goals equal only up to
  unfolding produce two constants.
* **`postponing theorem` reimplements only part of `theorem`**: a doc comment,
  binders, a type and a body.  Attributes, `private`, mutual blocks and the
  equation compiler are not supported.
* **`lax_apply` needs the lemma's non-obligation arguments given explicitly**,
  since unification cannot recover them from the conclusion alone.
* **The examples are illustrative, not sign-off.**  The delay figures are
  nominal, and none of this is static timing analysis on a real netlist.

# Future work

**Certificates without `Classical.choice`.**  The normaliser already knows which
branch of the `max` tree each summand came from, so it could emit a proof built
from `Nat.le_max_left` and `Nat.add_le_add_right` instead of calling `omega`.
That would make every synthesised constraint clean, and would turn the solver
from a proposer into a certifying compiler.

**A wider fragment.**  Subtraction with truncation, `min` on the right of `≤`,
and bounds mentioning the quantified variable on both sides all occur in
practice; the latch already produces one of them.  Each is a decidable
extension, and the fragment boundary should be reported as data rather than as a
warning string.

**Schedules as first-class objects.**  The earliest-schedule instantiation is
done by hand in one example.  Computing the earliest schedule from the ledger,
and reporting the residual single inequality, is the step that would make the
output look like what a timing tool prints.

**The remaining memory devices.**  The original paper's own future work was the
other two devices Herbert verified, and formal microprocessor design.  The first
of those is now a reasonable target, and would be the real test of whether the
induction principle generalises or whether each device needs its own.

**Mendler's incrementor.**  The paper's other worked example is a cascade of
half-adders whose overflow constraint is built by a recursion mirroring the
circuit's, and which is equivalent to a flattened bound.  It is the natural test
of a solver over a non-arithmetic constraint domain, since the interesting
property there is that the recursive form can evaluate to a trivial constraint
in context where the flattened form would have to be proved trivial.

**An automated loop.**  `#obligations_json` exists for this: the outstanding
obligations are named constants with printable statements, so an external prover
can be handed them one at a time and its results linked back as ordinary
theorems.  The count is a progress measure that a binary sorry-or-not cannot
give, and the residual constraint order — a stronger obligation is lower — is a
measure along which such a loop could be said to converge.
