/-
# Worked examples, and the gate

This file is documentation and test at once. Every claim the library makes about
axioms is pinned here with `#guard_msgs`, so a change that silently reintroduces
`sorryAx` — or that trips the `addAsAxiom` fallback described in
`LaxLogic.Obligation.Postpone` — breaks the build rather than passing quietly.

The negative case is included deliberately: §5 shows what `sorry` does to the
same proof, so the pin is watched failing as well as passing. Its statement is
true but unproved, so nothing false enters the environment.
-/

import LaxLogic.Obligation.Postpone
import LaxLogic.Obligation.Conservativity

namespace LaxLogic.Obligation.Examples

/-! ## 1. A hole records a debt instead of asserting the goal -/

#guard_msgs (drop info) in
/-- Half of this is proved; the other half becomes an obligation. -/
postponing theorem split (n : Nat) : n + 0 = n ∧ n * 1 = n := by
  refine ⟨?_, ?_⟩
  · rfl
  · postpone

-- The debt is in the type.
/-- info: LaxLogic.Obligation.Examples.split (n : Nat) (obl1 : split.obligation1 n) : n + 0 = n ∧ n * 1 = n -/
#guard_msgs in
#check split

-- And the theorem rests on nothing at all: the hole contributed no axiom.
/-- info: 'LaxLogic.Obligation.Examples.split' does not depend on any axioms -/
#guard_msgs in
#print axioms split

/-! ## 2. Discharging the obligation recovers the intended theorem

`split.obligation1` is reducible, so a proof of the underlying statement is
accepted directly. -/

theorem split' (n : Nat) : n + 0 = n ∧ n * 1 = n :=
  split n (Nat.mul_one n)

/-- info: 'LaxLogic.Obligation.Examples.split'' does not depend on any axioms -/
#guard_msgs in
#print axioms split'

/-! ## 3. A false obligation is carried safely

This is the property that distinguishes the mechanism from `sorry`. The
obligation below is false, and the theorem is still true, kernel-accepted and
axiom-free — because it asserts nothing about its conclusion. -/

#guard_msgs (drop info) in
postponing theorem bogus : (0 : Nat) = 1 := by
  postpone

/-- info: 'LaxLogic.Obligation.Examples.bogus' does not depend on any axioms -/
#guard_msgs in
#print axioms bogus

-- Nothing false has entered the environment: `bogus` is the identity on a
-- false proposition, which is a tautology.
example : bogus.obligation1 → (0 : Nat) = 1 := bogus

/-! ## 4. Obligations combine, and duplicates are merged

Two holes with the same goal contribute one obligation, not two. -/

#guard_msgs (drop info) in
postponing theorem twice : ((0 : Nat) = 1) ∧ ((0 : Nat) = 1) := by
  refine ⟨?_, ?_⟩
  · postpone
  · postpone

/-- info: LaxLogic.Obligation.Examples.twice (obl1 : twice.obligation1) : 0 = 1 ∧ 0 = 1 -/
#guard_msgs in
#check twice

/-! A theorem built from two holed theorems accumulates both debts. This is
`Debt.and` at work, and it is what makes a hole deep in a development surface at
the top as a single list of outstanding goals. -/

#guard_msgs (drop info) in
postponing theorem combined :
    (∀ n : Nat, n + 0 = n ∧ n * 1 = n) ∧ ((0 : Nat) = 1) := by
  exact ⟨fun n => split n (by postpone), bogus (by postpone)⟩

/--
info: LaxLogic.Obligation.Examples.combined (obl1 : combined.obligation1) (obl2 : combined.obligation2) :
  (∀ (n : Nat), n + 0 = n ∧ n * 1 = n) ∧ 0 = 1
-/
#guard_msgs in
#check combined

/-- info: 'LaxLogic.Obligation.Examples.combined' does not depend on any axioms -/
#guard_msgs in
#print axioms combined

/-! ## 5. The contrast with `sorry`, watched rather than asserted

The same shape of proof, closed with `sorry` instead. The statement is true, so
nothing unsound is added; what changes is the axiom set — and it propagates to
anything built on top. -/

/-- warning: declaration uses `sorry` -/
#guard_msgs in
theorem sorried (n : Nat) : n + 0 = n ∧ n * 1 = n := by
  refine ⟨rfl, ?_⟩
  sorry

/-- info: 'LaxLogic.Obligation.Examples.sorried' depends on axioms: [sorryAx] -/
#guard_msgs in
#print axioms sorried

theorem downstream (n : Nat) : n * 1 = n := (sorried n).2

/-- info: 'LaxLogic.Obligation.Examples.downstream' depends on axioms: [sorryAx] -/
#guard_msgs in
#print axioms downstream

/-! ## 6. The conservativity audit

Matthew's ruling on the paper's Theorem 1: conservative over the logic
underlying Lean — higher-order dependent type theory, with `propext` and
`Quot.sound` if wanted, which come free as with any axiomatic extension. For the
theory half that is true by construction. For the *tactic* half it has to be
checked, because `addDecl` can add a name as an axiom when the kernel rejects
it. This is that check, and it is a gate: it throws rather than reports. -/

/--
info: conservativity audit passed for 4 declaration(s); base-theory axioms only:
  LaxLogic.Obligation.Examples.split — no axioms
  LaxLogic.Obligation.Examples.bogus — no axioms
  LaxLogic.Obligation.Examples.twice — no axioms
  LaxLogic.Obligation.Examples.combined — no axioms
-/
#guard_msgs in
#obligations_audit

/-! `sorried` and `downstream` both carry `sorryAx`, while `split` and
`combined` carry nothing — with the *same* amount actually proved. That
difference is the whole point of the library. -/

end LaxLogic.Obligation.Examples
