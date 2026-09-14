import Verso
import VersoManual
import LaxLogic.QLL

open Verso.Genre
open Verso.Genre.Manual

#doc (Manual) "Quantified lax logic" =>

The logic in which everything is stated: intuitionistic first-order logic with
two lax modalities, its natural deduction system, and its Kripke models, in
which the modal relation is a parameter that must not be fixed carelessly.

# Syntax and proofs

Formulas are `⊤`, `⊥`, atoms `P(t̃)`, `∧`, `∨`, `⊃`, `∀`, `∃` and `◯_q A` for
`q ∈ {∀, ∃}`; the draft's `◯` is `◯_∃`, and every proof below is stated for a
general `q`.  Terms and formulas are locally nameless.  Provability
`Γ ⊢ A` is natural deduction with cofinite binders; the modal rules are

```
Γ ⊢ A                     Γ ⊢ ◯_q A     A, Γ ⊢ ◯_q B
──────────── (◯I)         ─────────────────────────── (◯E)
Γ ⊢ ◯_q A                         Γ ⊢ ◯_q B
```

so `◯` is a monad: `◯I` is the unit and `◯E` the bind.

Natural deduction for QLL with cofinite quantifier rules.

{docstring LaxLogic.QLL.Prv +allowMissing}

# Models

A Kripke model is a preorder of worlds with increasing domains, hereditary
fallible worlds at which every atom holds, and two modal relations
`R_∀, R_∃ ⊆ Ri`.  The modal clause is

```
w ⊨ ◯_q A   iff   for every v with w Ri v there is u with v R_q u and u ⊨ A.
```

Kripke models with fallible worlds and two modal relations.

{docstring LaxLogic.QLL.KModel +allowMissing}

Soundness: `Γ ⊢ A` implies `Γ ⊫ A`.  Proved without choice.

{docstring LaxLogic.QLL.Prv.sound +allowMissing}

Completeness on the fragment used here; the canonical model construction uses
`Classical.choice`.

{docstring LaxLogic.QLL.prv_iff_consequence +allowMissing}

# The modal relation is a parameter

It is tempting, when building Herbrand models, to take the modal relation to
be the intuitionistic order.  That is not harmless.  With no fallible worlds,
`◯` is then forced exactly where `¬¬` is, and such models validate a formula
QLL does not prove.

With `R_∃ = Ri`, the formula `(◯A ⊃ ◯B) ⊃ ◯(A ⊃ B)` is forced at every world.

{docstring LaxLogic.QLL.circ_imp_of_rm_eq_ri +allowMissing}

QLL does not prove `(◯P ⊃ ◯Q) ⊃ ◯(P ⊃ Q)`.  The countermodel has three worlds
`r ≤ s ≤ f`, `f` fallible, and the modal relation the identity together with
`s → f`.  REFUTED cell for the claim that `R_m = Ri` is a free choice.

{docstring LaxLogic.QLL.not_prv_circ_imp +allowMissing}

The Herbrand frames used later therefore carry their own modal preorder `m ⊆
le`, and the draft's choice `m = le` is made deliberately, on frames whose
fallible world keeps `◯` from collapsing.
