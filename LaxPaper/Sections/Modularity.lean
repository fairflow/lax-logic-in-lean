import Verso
import VersoManual
import VersoBlueprint
import LaxLogic.Obligation

open Verso.Genre
open Verso.Genre.Manual
open Informal
open LaxLogic.Obligation

#doc (Manual) "Modularity: borrowing a constraint" =>

# The gap

`postponing theorem` produces `C₁ ⊃ ⋯ ⊃ Cₙ ⊃ φ`.  That is the fold-back, and it
is automatic.  It is not yet modular reasoning, because a theorem produced this
way could not be _used_ while its constraint was outstanding: applying it left
the obligation as an ordinary goal, to be proved on the spot.  That defeats the
purpose.  The reason to abstract a constraint is to go on reasoning while it is
unresolved, and a method that forces resolution at the first use is a method
that has to be applied to one monolithic proof.

This is the non-compositionality the original paper identifies as pervasive and
rarely named, quoting Eveking: in the general case one has to reanalyse a
network completely even if the fragments were proved correct.

# `lax_apply`

`lax_apply h` behaves as `apply h`, except that any resulting goal whose head is
a registered obligation constant is recorded by `postpone` rather than returned.
The borrowed debt lands in the caller's ledger and is abstracted into the
caller's statement.  Goals that are not obligations are left to prove, exactly
as `apply` leaves them; a `lax_apply` that borrows nothing warns rather than
passing itself off as `apply`.

Operationally this is `weak_append`: the ledger of a proof assembled from holed
components is the concatenation of their ledgers.

# It is verbatim, and it is transitive

The interesting property is that the borrowed obligation is not re-derived.  The
caller's ledger records the callee's own obligation constant, applied to the
caller's binders — so the following hold by `rfl` and depend on **no axioms**.

:::group "mod_borrow"
Borrowing.
:::

:::theorem "borrowed_is_bal" (parent := "mod_borrow") (uses := "postpone, weak_append, bal_meets_cycle") (lean := "Modular.borrowed_is_bal")
The datapath's first obligation *is* the adder block's own obligation.
:::

:::theorem "borrowed_is_datapath" (parent := "mod_borrow") (uses := "borrowed_is_bal, datapath") (lean := "Modular.borrowed_is_datapath")
And the pipeline's first obligation is the datapath's first, which is the
block's: borrowing composes transitively.
:::

The three-stage example of a later section owes 1, 2 and 3 obligations
respectively, the increments being one borrowed set plus one new constraint at
each stage.  What `#obligations` prints makes the structure visible:

```
Adder.bal_meets_cycle owes 1:
    …obligation1 : fun Gp δ k T hm hleaf =>
  ∀ (z : ℕ), T ≤ z → from_ (k * δ) z

Modular.datapath_meets_clock owes 2:
    …obligation1 : fun Gp Pb Sum δ δsum T tp Tclk k hm hleaf hpb hxor =>
  Adder.bal_meets_cycle.obligation1 Gp δ k T hm hleaf
    …obligation2 : fun Gp Pb Sum δ δsum T tp Tclk k hm hleaf hpb hxor =>
  ∀ (z : ℕ), Tclk ≤ z → from_ (max T tp + δsum) z

Modular.pipeline_meets_clock owes 3:
    …obligation1 : … => datapath_meets_clock.obligation1 …
    …obligation2 : … => datapath_meets_clock.obligation2 …
    …obligation3 : … => ∀ (z : ℕ), Tout ≤ z → from_ (Tclk + δbuf) z

total outstanding: 7 across 4 declaration(s)
```

# The control test

A tactic that claims to do something should be shown not to be redundant.
Replacing the single `lax_apply` in the datapath proof by a plain `apply`
produces, in one build: the datapath owing **one** obligation instead of two,
with an unsolved goal where the borrowed one should be; both `rfl` theorems
above failing with `Not a definitional equality`; and the pipeline owing two
instead of three.  Restoring `lax_apply` restores 2 and 3.

# The cost

`lax_apply` makes it possible to write a proof that owes something it should
have proved.  That is the point of abstraction and not a defect, but it does
mean the ledger, rather than the build's success, is the measure of what is
finished.  A green build with seven outstanding obligations is a green build
with seven outstanding obligations, and `#obligations` is how a development
built this way is read.
