/-
# A second constraint model: resource budgets

`Timing.lean` reads a constraint as a lower bound on a clock, and finds that
combining constraints is `max` and propagating one through a component is `+`.
Nothing in the modality forced that. This module instantiates the *same*
machinery at a different monoid — a resource budget, where two components drawn
from separate pools cost the **sum** and two sharing one pool cost the **max** —
and runs the same pipeline over it: `postponing theorem` synthesises the
constraint, the solver reduces it, and it discharges at a model.

The point of having two models in the repository is that everything between
them is shared. `carry_cell` and `combine` below are different theorems, but
`postpone`, `lax_apply`, `reduce_obligation`, `discharge_obligation`, the
ledger, the audit and the `(max, +)` solver are the same code, and neither
model was anticipated by any of it.

## The two ways to combine

| situation | constraint | which Fig. 4 rule |
| --- | --- | --- |
| separate pools (two sub-circuits on one die) | `a + b` | `pair` then `image (+)` |
| one shared pool (peak current, a register file port) | `max a b` | `meet` |

The first is the interesting one, because it is the case the timing reading
never produces: in `Timing.lean` every combination is a `meet`, so every
constraint contains a `max`. Here the additive constraints are `max`-free,
which the axiom pins below make visible — `omega` normalises `max` classically,
so a `max`-free constraint is certified without `Classical.choice`.
-/

import LaxLogic.Obligation.Solve
import LaxLogic.Obligation.Tactics

namespace LaxLogic.Obligation.Budget

open LaxLogic.Obligation

/-- A resource budget: `atLeast c` holds of a budget `b` when `b` covers `c`.

Formally identical to `Timing.from_`, and deliberately so — what differs is not
the shape of a single constraint but how two of them combine. -/
abbrev atLeast (c : Nat) : Constraint Nat := fun b => c ≤ b

/-! ## Separate pools: cost adds -/

/-- **Two components on separate budgets cost the sum.**

This is the paper's `⊃_◯` at the direct image along `(x, y) ↦ x + y`, applied
after `laxAll_pair`; spelling it out as one rule keeps the case studies
readable. -/
theorem combine {M N K : Refined Nat} {a b : Nat}
    (hM : ◯∀[atLeast a] M) (hN : ◯∀[atLeast b] N)
    (hK : ∀ t, (∃ x y, x + y ≤ t ∧ M x ∧ N y) → K t) :
    ◯∀[atLeast (a + b)] K := by
  intro t ht
  exact hK t ⟨a, b, by simpa only [atLeast] using ht,
    hM a (Nat.le_refl a), hN b (Nat.le_refl b)⟩

/-- **Two components sharing one budget cost the max.** The same rule as
`Timing.pipeline` with a zero delay, which is the sense in which the timing
model is the shared-resource case. -/
theorem share {M N K : Refined Nat} {a b : Nat}
    (hM : ◯∀[atLeast a] M) (hN : ◯∀[atLeast b] N)
    (hK : ∀ t, (∃ s, s ≤ t ∧ M s ∧ N s) → K t) :
    ◯∀[atLeast (max a b)] K := by
  intro t ht
  simp only [atLeast] at ht
  exact hK t ⟨max a b, ht,
    hM _ (by simp only [atLeast]; omega), hN _ (by simp only [atLeast]; omega)⟩

/-! ## The prefix tree's gate count

`Adder.lean` compares a ripple chain and a balanced prefix fold on *delay*. The
same two networks differ in **area**, and the balanced one is the more expensive
per unit depth: a depth-`k` tree has `2ᵏ - 1` merge cells, all of which the
ripple chain also has, but the ripple chain of the same leaf count is a line.
This is the constraint the delay comparison of `Adder.lean` does not see. -/

/-- Merge cells in a balanced prefix tree of depth `k`: two subtrees and a root.
-/
def treeGates : Nat → Nat
  | 0 => 0
  | k + 1 => 2 * treeGates k + 1

/-- `treeGates k = 2ᵏ - 1`. Deliberately proved rather than taken as the
definition, so that the recursion mirrors the tree the delay argument folds
over. -/
theorem treeGates_eq : ∀ k, treeGates k = 2 ^ k - 1
  | 0 => rfl
  | k + 1 => by
      have ih := treeGates_eq k
      have hp : 2 ^ (k + 1) = 2 ^ k * 2 := Nat.pow_succ ..
      have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
      simp only [treeGates, ih]
      omega

/-- **The area obligation.** The statement carries no area hypothesis; the
hypothesis is what comes out. -/
postponing theorem tree_within_budget
    (Tree : Refined Nat) (k A : Nat)
    (hbuild : ◯∀[atLeast (treeGates k)] Tree) :
    ◯∀[atLeast A] Tree := by
  refine laxAll_mono (fun z (hz : A ≤ z) => ?_) hbuild
  postpone   -- becomes the AREA constraint

/-! ## Discharging at an area model

A 32-bit block is a depth-5 tree, `treeGates 5 = 31` merge cells. -/

/-- Thirty-one cells fit a forty-cell budget. -/
theorem tree32_fits (Tree : Refined Nat) (hbuild : ◯∀[atLeast (treeGates 5)] Tree) :
    ◯∀[atLeast 40] Tree :=
  tree_within_budget_debt Tree 5 40 hbuild (by simp only [tree_within_budget.obligation1]; decide)

/-- And they do not fit a thirty-cell budget: **refuted**, not unproved. -/
theorem tree32_too_big (Tree : Refined Nat) (hbuild : ◯∀[atLeast (treeGates 5)] Tree) :
    ¬ tree_within_budget.obligation1 Tree 5 30 hbuild := by
  simp only [tree_within_budget.obligation1]
  decide

/-- Cost adds across separate pools: two 32-bit blocks are 62 cells, and the
constraint is computed by `combine`, not asserted. -/
theorem two_blocks {M N K : Refined Nat}
    (hM : ◯∀[atLeast (treeGates 5)] M) (hN : ◯∀[atLeast (treeGates 5)] N)
    (hK : ∀ t, (∃ x y, x + y ≤ t ∧ M x ∧ N y) → K t) :
    ◯∀[atLeast 62] K := by
  have h := combine hM hN hK
  simpa only [show treeGates 5 + treeGates 5 = 62 from by decide] using h

/-! ## Gates

The area constraints are `max`-free, so unlike the timing ones they are
certified without `Classical.choice`. That contrast is the reason both models
are in the repository. -/

/--
info: 'LaxLogic.Obligation.Budget.tree_within_budget_debt' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms tree_within_budget_debt

/-- info: 'LaxLogic.Obligation.Budget.tree32_fits' depends on axioms: [propext] -/
#guard_msgs in
#print axioms tree32_fits

/-- info: 'LaxLogic.Obligation.Budget.combine' does not depend on any axioms -/
#guard_msgs in
#print axioms combine

/-- info: 'LaxLogic.Obligation.Budget.treeGates_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms treeGates_eq

end LaxLogic.Obligation.Budget
