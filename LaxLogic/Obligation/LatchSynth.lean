/-
# Synthesising the latch's timing constraint, instead of assuming it

`Latch.lean` proves the paper's result with the two timing constraints supplied
as hypotheses. That is the ordinary way to write the theorem, and it hides what
the paper's method is actually for: the constraints are not *inputs* to the
verification, they are its *output*.

Here the same derivation is written with `postpone` at the two arithmetic side
conditions of the induction step, and nothing else changes. The library then
computes what those holes owe, and what comes back is

    obligation1 : ∀ t₁, ta + D₁ ≤ t₁ → sa + d₁ + d₂ + d₁ ≤ t₁
    obligation2 : ∀ t₁, ta + D₁ ≤ t₁ → t₁ < t₁ + D₂ + D₁

which is the paper's equation **(8)**, in the form it appears there, before any
reduction. The paper then says of exactly this step:

> the condition `∀t₁ ≥ t_a + D₁. ∃m₁₁ ≥ s_a. m₁₁ + 2d₁ + d₂ ≤ t₁` is logically
> equivalent to `t_a + D₁ ≥ s_a + 2d₁ + d₂`. Given such reasoning is built into
> constraint reductions, we are looking at the solution form …

and prints its equation **(9)**. `obligation1_iff` and `obligation2_iff` below
are that reduction, machine-checked, and `omega` performs it. So the whole
pipeline of Fig. 9 — abstract, derive, reduce, refine — runs here with the
reduction step discharged automatically.

## How to organise a proof effort this way

1. State the theorem **without** its side conditions.
2. Prove it, and `postpone` every goal that is a side condition rather than
   part of the argument.
3. Read `#obligations`. Those are the conditions under which the theorem holds,
   derived rather than guessed.
4. Reduce them (`omega` here), and state the reduced form as the theorem's
   hypotheses if you want the conventional presentation.

Step 3 is the one that is not available with `sorry`: a `sorry`ed side condition
records nothing, so the constraint has to be known in advance — which, for a
circuit, is precisely the thing the verification was supposed to discover.
-/

import LaxLogic.Obligation.Latch
import LaxLogic.Obligation.Postpone
import LaxLogic.Obligation.Conservativity

namespace LaxLogic.Obligation.Latch

open LaxLogic.Obligation

/-- The latch derivation with its two side conditions postponed. Identical to
`latch_resets` except that `hold` and `inertia` are absent from the statement
and the two `omega` calls that used them are `postpone`. -/
postponing theorem latch_synth
    (rin sin qout qbar : Nat → Prop) (d₁ d₂ D₁ D₂ sa ta : Nat)
    (h1 : Θ₁ rin qout d₁ D₁) (h2 : Θ₂ sin qout qbar d₂ D₂)
    (h3 : Θ₃ qout qbar d₁ D₁)
    (hp1 : Θₚ₁ rin sa ta) (hp2 : Θₚ₂ sin sa) :
    ∀ t, sa + d₁ ≤ t → During (Low qout) (sa + d₁, t) := by
  have base : During (Low qout) (sa + d₁, ta + D₁) := h1 sa ta hp1
  have hR : ∀ x : Interval, During (Low qout) x → ∀ y : Interval,
      (sa ≤ x.1 ∧ y.1 = x.1 + d₂ + d₁ ∧ y.2 = x.2 + D₂ + D₁) →
      During (Low qout) y := by
    rintro ⟨x₁, x₂⟩ hx ⟨y₁, y₂⟩ ⟨hsa, rfl, rfl⟩
    exact loop sin qout qbar d₁ d₂ D₁ D₂ sa h2 h3 hp2 hsa hx
  have hprog : Prog
      (fun x y => sa ≤ x.1 ∧ y.1 = x.1 + d₂ + d₁ ∧ y.2 = x.2 + D₂ + D₁)
      (sa + d₁, ta + D₁) := by
    intro t₁ ht₁
    refine ⟨sa + d₁ + d₂ + d₁, t₁ + D₂ + D₁, by omega, ?_, ?_, by omega, rfl, rfl⟩
    · postpone   -- becomes the EXTERNAL HOLD constraint
    · postpone   -- becomes the INTERNAL MEMORY constraint
  intro t ht
  exact ind_aux (During (Low qout))
    (fun h hb => During.restrict h hb) (fun h₁ h₂ hc => During.union h₁ h₂ hc)
    base hR hprog t ht

section Reduce

variable (rin sin qout qbar : Nat → Prop) (d₁ d₂ D₁ D₂ sa ta : Nat)
variable (h1 : Θ₁ rin qout d₁ D₁) (h2 : Θ₂ sin qout qbar d₂ D₂)
variable (h3 : Θ₃ qout qbar d₁ D₁) (hp1 : Θₚ₁ rin sa ta) (hp2 : Θₚ₂ sin sa)

/-- **The paper's (8) → (9) reduction for the first constraint, machine-checked.**

The synthesised obligation is *equivalent* to the external hold constraint, not
merely implied by it: the latch resets exactly when `r_in` is held high for
`2d₁ + d₂` beyond the propagation allowance. -/
theorem obligation1_iff :
    latch_synth.obligation1 rin sin qout qbar d₁ d₂ D₁ D₂ sa ta h1 h2 h3 hp1 hp2
      ↔ sa + 2 * d₁ + d₂ ≤ ta + D₁ := by
  constructor
  · intro h; have := h (ta + D₁) (Nat.le_refl _); omega
  · intro h t₁ ht₁; omega

/-- The same for the second constraint: the **internal memory constraint**, that
at least one of the two gates has non-zero inertia. -/
theorem obligation2_iff :
    latch_synth.obligation2 rin sin qout qbar d₁ d₂ D₁ D₂ sa ta h1 h2 h3 hp1 hp2
      ↔ 0 < D₂ + D₁ := by
  constructor
  · intro h; have := h (ta + D₁) (Nat.le_refl _); omega
  · intro h t₁ _; omega

end Reduce

/-- Discharging the synthesised obligations gives back the paper's result, so
the two routes agree: the constraint that was *derived* is the constraint the
conventional statement *assumes*. -/
theorem latch_resets_synth
    (rin sin qout qbar : Nat → Prop) (d₁ d₂ D₁ D₂ sa ta : Nat)
    (h1 : Θ₁ rin qout d₁ D₁) (h2 : Θ₂ sin qout qbar d₂ D₂)
    (h3 : Θ₃ qout qbar d₁ D₁) (hp1 : Θₚ₁ rin sa ta) (hp2 : Θₚ₂ sin sa)
    (hold : sa + 2 * d₁ + d₂ ≤ ta + D₁) (inertia : 0 < D₂ + D₁) :
    ∀ t, sa + d₁ ≤ t → During (Low qout) (sa + d₁, t) :=
  latch_synth rin sin qout qbar d₁ d₂ D₁ D₂ sa ta h1 h2 h3 hp1 hp2
    ((obligation1_iff rin sin qout qbar d₁ d₂ D₁ D₂ sa ta h1 h2 h3 hp1 hp2).mpr hold)
    ((obligation2_iff rin sin qout qbar d₁ d₂ D₁ D₂ sa ta h1 h2 h3 hp1 hp2).mpr inertia)

/-! ## Gates

The synthesised route is conservative and rests on the ordinary baseline: the
constraint was *derived*, and nothing was assumed to derive it. -/

/--
info: conservativity audit passed for 1 declaration(s); base-theory axioms only:
  LaxLogic.Obligation.Latch.latch_synth — [propext, Quot.sound]
-/
#guard_msgs in
#obligations_audit

/-- info: 'LaxLogic.Obligation.Latch.latch_resets_synth' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms latch_resets_synth

/-- info: 'LaxLogic.Obligation.Latch.latch_synth' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms latch_synth

end LaxLogic.Obligation.Latch
