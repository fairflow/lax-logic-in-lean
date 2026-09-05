/-
# The timing interpretation of `◯`

The original reading of the lax modality, and the one the case study of
Fairtlough–Mendler–Cheng (TPHOLs 2001, §3) is built on: the witness type is a
clock, and a constraint is a **lower bound** saying when a signal has settled.
`◯∀[a ≤ ·] P` then reads "`P` holds from time `a` onwards".

Everything in this file is a check on the correspondence rather than new
mathematics. What it establishes is that the two operations of the constraint
calculus specialise, on lower bounds, to the two operations of timing analysis:

| constraint calculus                | timing                    |
| ---------------------------------- | ------------------------- |
| `meet` — conjunction of demands    | `max` — parallel join     |
| `image (· + d)` — propagation      | `+ d` — sequential delay  |

`meet_lowerBound` and `image_delay` are those two rows. `pipeline` is the shape
of the paper's introductory example: two components available from times `a` and
`b` feeding a third with delay `d`, giving `max a b + d`.

The reason the parallel rule is `max` and not `min` is that the constraints are
*lower* bounds and they are conjoined: to have both signals you must wait for
the later one. On the implication side of Fig. 4 this is the ordinary
conjunction of antecedents, which is why the two readings agree.

Nothing here needs Mathlib; `omega` decides all of it.
-/

import LaxLogic.Obligation.Modality

namespace LaxLogic.Obligation.Timing

open LaxLogic.Obligation

/-- Availability from time `a` onwards: the constraint carried by a signal that
has settled by `a`. -/
abbrev from_ (a : Nat) : Constraint Nat := fun s => a ≤ s

/-- **Parallel composition is `max`.** Conjoining two availability constraints
on a shared clock gives availability from the later of the two times.

This is the timing content of `LaxLogic.Obligation.meet`, and the reason the
paper's parallel rule `(◯A ∧ ◯B) ⊃ ◯(A ∧ B)` computes a maximum. -/
theorem meet_lowerBound (a b s : Nat) :
    meet (from_ a) (from_ b) s ↔ from_ (max a b) s := by
  simp only [meet, from_]
  omega

/-- **Sequential composition adds the delay.** Propagating an availability
constraint through a component with delay `d` — the direct image along `· + d`,
which is the paper's `⊃_◯` — shifts the bound by `d`.

The `∃` in `image` is what makes this a genuine computation rather than a
rewrite: the existential is eliminated, and a bound in the form `a + d ≤ ·`
comes out. -/
theorem image_delay (a d z : Nat) :
    image (· + d) (from_ a) z ↔ from_ (a + d) z := by
  simp only [image, from_]
  constructor
  · rintro ⟨m, hm, rfl⟩
    omega
  · intro hz
    exact ⟨z - d, by omega, by omega⟩

/-- The two rules together, as a single constraint computation: combine in
parallel, then delay. -/
theorem meet_then_delay (a b d z : Nat) :
    image (· + d) (meet (from_ a) (from_ b)) z ↔ from_ (max a b + d) z := by
  simp only [image, meet, from_]
  constructor
  · rintro ⟨m, ⟨ha, hb⟩, rfl⟩
    omega
  · intro hz
    exact ⟨z - d, ⟨by omega, by omega⟩, by omega⟩

/-- **The paper's introductory example, in general form.**

Two components whose outputs are available from times `a` and `b` feed a third
which needs both and adds a delay `d`. The derived availability of the result is
`max a b + d`, and it is *computed* from the two component constraints rather
than assumed.

This is the whole method of Fig. 9 in miniature: the functional facts (`h₁`,
`h₂`, `hQ`) are proved without reference to time, and the timing constraint is
synthesised from the derivation. In the paper's own instance the component
bounds are `s ≥ 5` and `s ≥ 9 - y`, and the delay is 35 units. -/
theorem pipeline {P₁ P₂ Q : Refined Nat} {a b d : Nat}
    (h₁ : ◯∀[from_ a] P₁)
    (h₂ : ◯∀[from_ b] P₂)
    (hQ : ∀ t, (∃ s, s + d ≤ t ∧ P₁ s ∧ P₂ s) → Q t) :
    ◯∀[from_ (max a b + d)] Q := by
  intro t ht
  simp only [from_] at ht
  exact hQ t ⟨max a b, by omega, h₁ _ (by simp only [from_]; omega),
    h₂ _ (by simp only [from_]; omega)⟩

/-- The paper's own numbers, as a sanity check on `pipeline`: components at 5
and 9 time units, a 35-unit delay, giving 44. -/
example {P₁ P₂ Q : Refined Nat}
    (h₁ : ◯∀[from_ 5] P₁) (h₂ : ◯∀[from_ 9] P₂)
    (hQ : ∀ t, (∃ s, s + 35 ≤ t ∧ P₁ s ∧ P₂ s) → Q t) :
    ◯∀[from_ 44] Q := by
  have := pipeline h₁ h₂ hQ
  simpa using this

/-! ### Why the obligation reading is the degenerate case of this one

A proof obligation is a timing constraint on a one-point clock: there is nothing
to schedule, so the constraint is simply a proposition, and `max` degenerates to
conjunction. That is `LaxLogic.Obligation.Debt`, and it is why the same two
rules — combine, and propagate — do all the work in the tactic. -/

/-- On a one-point clock, parallel composition is conjunction. -/
theorem meet_unit (C D : Prop) (z : Unit) :
    meet (fun _ : Unit => C) (fun _ : Unit => D) z ↔ (C ∧ D) :=
  Iff.rfl

end LaxLogic.Obligation.Timing
