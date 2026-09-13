import Verso
import VersoManual
import VersoBlueprint
import LaxLogic.QLL

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Pruning and Prolog's cut" =>

Whether there is a published correlation between constraint pruning in CLP
and Prolog's cut, what it is, and how the results above bear on it.

# What is published

The link runs through committed choice with constraint guards.  Maher's
logical semantics for the ALPS class (ICLP 1987) governs commitment by
constraint entailment; Saraswat's concurrent constraint programming makes
`ask` — block until the store entails the guard — and `tell` the primitives;
the Andorra Kernel Language (Haridi and Janson, ICLP 1990) has a conditional
choice that is Prolog's if-then-else guarded by entailment, a committed
choice, and a nondeterminate choice that waits, and Franzén's logical account
restricts pruning to *quiet* guards, entailed by the store rather than merely
consistent with it, because quiet pruning is insensitive to execution order.
Naish's survey of pruning operators (1995) records that they are typically
not declarative and cost completeness or soundness; Andrews (TPLP 2003) shows
that Prolog with negation as failure and cut lacks the witness properties and
gives a restriction that keeps cut's first-solution behaviour with them;
Piróg and Staton (JFP 2017) show that cut makes backtracking the monad of
free left-zero monoids.  On the CLP side, failure pruning is Jaffar–Maher's
`→s`, branch and bound (Van Hentenryck 1989) prunes by bounds and is sound
for optimal answers only, and Gocht, McCreesh and Nordström (CP 2022) log
every pruning step of a constraint solver as a checkable cutting-planes
proof.

# How it lines up

```
pruning         condition                      order dependence   certificate here
failure         store unsatisfiable            none               Farkas multipliers
quiet commit    guard entailed by the store    little             entailment by refutation
bound           branch cannot beat incumbent   none for optima    lowerBoundCert
cut             first success in text order    essential          none possible
```

Failure pruning is the constraint monoid's zero, `⊥ ∧ c ⊣⊢ ⊥ ⊣⊢ c ∧ ⊥`, a
two-sided zero; that is why it commutes with everything and why Theorem 9.4
holds for any `ok`.  Cut is a left zero, non-commutative; the commutativity
of `⊗` is what selection independence rests on, so cut cannot live in the
constraint monoid — it lives in the search, and its left-zero law is the
precise point where commutativity fails.  Quiet commit sits between: its
pruning is justified by an entailment, so it can be checked.

# What the machine adds

The switching lemma and the pruning theorem of the machine section make this
exact for the failure case.  Without pruning the search is confluent under
switching; with an exact satisfiability test, the pruned runs are precisely
the unpruned runs whose final store is satisfiable, so failure pruning is
order-independent and answer-invisible.  Cut has no such theorem, and the
reason is visible in the same place: it is not a function of the store.

:::group "prune"
The connection to the machine.
:::

:::theorem "prune_noprune" (parent := "prune") (uses := "mach_noprune, mach_diamond") (lean := "LaxLogic.QLL.SLD.SLDSteps.noPrune_iff")
The pruning theorem, read as the formal content of "failure pruning is
green": it changes the prefixes explored, not the trees reachable with an
acceptable store.
:::

Directions that would build on this, each to start with a statement and
designed cells: a certified pruning log (unsatisfiable, dominated, or not
selected under a quiet commit, each with its certificate); quiet commit in
lax logic programs, with answer soundness as the first target; and
Piróg–Staton's cut added to the extraction monad, with the failure of
selection independence as a designed countermodel — a formal version, inside
the lax framework, of "cut is non-logical".
