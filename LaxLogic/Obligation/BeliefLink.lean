/-
# Proof obligations are hypothetical belief

The belief development in this repository reads the lax modality epistemically:
`BeliefOpenClosed.lean` defines the **open nucleus**

    u_a(x) = a ⇨ x

and glosses it *"I would believe `x` given `a`"* — hypothetical belief. The
obligation library reads the same modality proof-theoretically: `Debt C A` is
"`A`, modulo the outstanding obligation `C`".

They are the same operator, and this file says so in the only way that counts.
Every identity below holds by `rfl`.

* `debt_eq_openNucleus` — `Debt C A = u_C(A)` in the Heyting algebra `Prop`.
  A recorded proof obligation *is* a hypothetical belief; discharging it is
  turning hypothetical belief into belief.
* `laxAll_iff_le` — `◯∀[p] M ↔ p ≤ M` in the pointwise Heyting algebra
  `γ → Prop`. So the weakening modality is entailment, and "the residual
  shrinks" is literally movement down that order.
* `laxAll_iff_openNucleus` — the two readings agree pointwise.

## What the belief side then says about obligations

`BeliefLax.openNucleus_eq_closedNucleus` proves that on a **Boolean** algebra
the open nucleus collapses to the closed one, `a ⇨ x = x ⊔ aᶜ`, and
`em_of_openNucleus_eq_closedNucleus` proves the converse at a point. Read on the
obligation side that says: **classically, "`A` modulo `C`" is just "`A` or not
`C`"**, and the distinction the whole library rests on disappears. Tracking a
debt is only informative in a setting where `C ∨ ¬C` is not free — which is the
setting Lean's `Prop` actually provides, and the reason the obligations in
`LatchSynth.lean` carry content rather than evaporating.

This is a statement of identity, not a new theorem; its value is that two
threads of the development turn out to be one, so results proved on either side
are available to the other.
-/

import LaxLogic.Obligation.Modality
import LaxLogic.BeliefOpenClosed

universe u

namespace LaxLogic.Obligation

open BeliefLax

/-- **A proof obligation is a hypothetical belief.** In the Heyting algebra
`Prop`, `Debt C A` is the open nucleus `u_C` applied to `A`. -/
theorem debt_eq_openNucleus (C A : Prop) : Debt C A = openNucleus C A := rfl

/-- **`◯∀` is entailment.** In the pointwise Heyting algebra `γ → Prop`,
`◯∀[p] M` says exactly that the constraint entails the claim.

This is the order the residual measure of an automated loop should move along:
a *stronger* constraint is lower, and progress is `p' ≤ p`. -/
theorem laxAll_iff_le {γ : Type u} (p M : Constraint γ) :
    ◯∀[p] M ↔ p ≤ M := Iff.rfl

/-- The two readings agree pointwise: `◯∀[p] M` is the open nucleus holding at
every witness. -/
theorem laxAll_iff_openNucleus {γ : Type u} (p M : Constraint γ) :
    ◯∀[p] M ↔ ∀ z, openNucleus (p z) (M z) := Iff.rfl

/-- The one-witness case, for completeness. -/
theorem debt_iff_le (C A : Prop) : Debt C A ↔ C ≤ A := Iff.rfl

end LaxLogic.Obligation
