import wip.f0FreePLL
import wip.f0FreeAnyFamily
import Meta.Audit

/-!
# Promoted F0 facts for the Belief paper

The Belief paper's policy (2026-07-16) is that nothing cited there as proved
lives only in `wip/`.  This module promotes the headline facts of the F0
free-algebra development — the faithful embedding of IPC into the closed
fragment F0, and the faithful self-embedding of PLL — as restatements whose
proofs are the `wip/` theorems (`wip/f0FreeBase3.lean`, `wip/f0FreePLL.lean`,
`wip/f0FreeAnyFamily.lean`, definitions in `wip/f0FreeHAn.lean`).  The
originals stay in place: the paper "The Order of F0" cites them by source
line, and its open revision must not be disturbed.  This module is built by
default through the `BeliefF0` library (lakefile), on the pattern of `SubTab`
and `FRJGbu`: the `LaxLogic` root module does not import it, keeping the root
import closure free of `wip/`.

Vocabulary (from `wip/f0FreeHAn.lean`): `base m = σᵐ⊥`, where
`σ(φ) = φ[⊥ := ◯⊥ ∨ ¬◯⊥]`; `FreeHAnAbove b n` says the free Heyting algebra
on `n` generators embeds as a Heyting subalgebra of the interval `[b, ⊤]` of
F0, stated as preservation and reflection of derivability under a
substitution of variable-free formulas for the variables and `b` for `⊥`;
`FreeHAωAbove b` is the ω-generator form; `FreePLLAbove b` drops the ◯-free
restriction: all PLL formulas, with `◯ ↦ ◯`.
-/

namespace BeliefLax.F0

open PLLND.F0 FreeHAn

/-- IPC embeds faithfully into F0: for every `n`, the free Heyting algebra on
`n` generators is a Heyting subalgebra of `[σ³⊥, ⊤]`, from one generator
family.  Proof: `wip/f0FreeBase3.lean`. -/
theorem freeHAnAbove_base3 (n : Nat) : FreeHAnAbove (base 3) n :=
  Base3.freeHAnAbove_base3 n

/-- The ω-generator form: `H_ω` is a Heyting subalgebra of `[σ³⊥, ⊤]`, so
intuitionistic propositional logic in countably many variables embeds
faithfully into the variable-free formulas of PLL. -/
theorem freeHAωAbove_base3 : FreeHAωAbove (base 3) :=
  Base3.freeHAωAbove_base3

/-- The conjecture of the F0 development, proved with `m = 3`:
for every `n` there is an `m` with `H_n` a Heyting subalgebra of
`[σᵐ⊥, ⊤]`. -/
theorem conjecture : Conjecture :=
  Base3.conjecture

/-- Every base `σᵐ⊥` with `m ≥ 3` carries the free Heyting algebra on every
finite number of generators.  Proof: `wip/f0FreeAnyFamily.lean` (the
σ-shift). -/
theorem allAbove3 : AnyFamily.AllAbove3 :=
  AnyFamily.allAbove3

/-- The ω-generator form over every base `σᵐ⊥`, `m ≥ 3`. -/
theorem allAbove3ω : AnyFamily.AllAbove3ω :=
  AnyFamily.allAbove3ω

/-- PLL embeds faithfully into its own closed fragment: substituting reader
formulas for the variables and `σ³⊥` for `⊥`, with `◯ ↦ ◯`, preserves and
reflects derivability for ALL formulas.  Proof: `wip/f0FreePLL.lean`. -/
theorem freePLLAbove_base3 : FreePLL.FreePLLAbove (base 3) :=
  FreePLL.freePLLAbove_base3

/-- The underlying faithfulness statement of the PLL self-embedding, with the
explicit reader generators. -/
theorem freeReaders : FreePLL.FreeReaders :=
  FreePLL.freeReaders

end BeliefLax.F0

/-- info: 'BeliefLax.F0.freeHAnAbove_base3' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms BeliefLax.F0.freeHAnAbove_base3

/-- info: 'BeliefLax.F0.freeHAωAbove_base3' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms BeliefLax.F0.freeHAωAbove_base3

/-- info: 'BeliefLax.F0.conjecture' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms BeliefLax.F0.conjecture

/-- info: 'BeliefLax.F0.allAbove3' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms BeliefLax.F0.allAbove3

/-- info: 'BeliefLax.F0.allAbove3ω' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms BeliefLax.F0.allAbove3ω

/-- info: 'BeliefLax.F0.freePLLAbove_base3' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms BeliefLax.F0.freePLLAbove_base3

/-- info: 'BeliefLax.F0.freeReaders' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms BeliefLax.F0.freeReaders
