/-
# `LaxLogic.Obligation` — lax modalities, and proof holes that record a debt

A small library with two halves that meet in the middle.

**The theory** (`Modality`, `Timing`) is a Lean reformulation of the
abstraction/refinement apparatus of

> M. Fairtlough, M. Mendler and X. Cheng, *Abstraction and refinement in higher
> order logic*, TPHOLs 2001, LNCS 2152, 201–216.

It defines the paper's two lax modalities `◯∀` (weakening) and `◯∃`
(strengthening) by their Fig. 4 clauses, and proves the rules `◯∧` and `◯⊃`
that combine and propagate constraints. `Timing` checks the correspondence the
modality was invented for: on lower bounds over a clock, combining constraints
is `max` and propagating one through a delay is `+`.

**The tactic** (`Ledger`, `Postpone`) applies the one-witness case. `postpone`
closes a goal by recording it as an obligation rather than by asserting it, and
`postponing theorem` abstracts the accumulated obligations into the statement.
The result is a complete, `sorry`-free theorem about a weaker proposition, where
`sorry` would have given a tainted theorem about the intended one.

**The case studies** are two circuits, each run both ways. `Latch`/`LatchSynth`
take the paper's own RS latch (its Figs. 7–8), first with the timing constraints
assumed and then with them synthesised, recovering its equation (8) and reducing
it to (9). `Adder` does the same for the repository's ripple-carry and
carry-lookahead adders (`PLLTimingRipple`, `PLLTimingLookahead`), which were
built on the `◯∃` writer reading; the `◯∀` rerun derives the same bounds
(`ripple_is_extracted`, `bal_is_extracted`), synthesises the cycle-time
constraint, **refutes** it for a 32-bit ripple in a 1 ns cycle, and discharges
it after re-associating the fold — the loop of the paper's Fig. 9, closed.

`Examples` is documentation and gate at once: every axiom claim is pinned with
`#guard_msgs`, including the negative case showing what `sorry` does to the same
proof.

## Quick start

```lean
import LaxLogic.Obligation

postponing theorem split (n : Nat) : n + 0 = n ∧ n * 1 = n := by
  refine ⟨?_, ?_⟩
  · rfl
  · postpone
-- split : split.obligation1 → ∀ (n : Nat), n + 0 = n ∧ n * 1 = n
-- and '#print axioms split' reports none

theorem split' (n : Nat) : n + 0 = n ∧ n * 1 = n :=
  split (fun m => Nat.mul_one m) n

#obligations        -- what the development still owes
#obligations_json   -- the same, for tooling
```

## What this is not

The paper's Theorem 1, conservativity of the `p : M` extension over HOL, is a
meta-theoretical result about a different base logic and is deliberately left
for later work. Nothing here depends on it: the definitions are ordinary Lean
definitions and the rules are ordinary Lean theorems.

Nor is this a port. The Isabelle/HOL development the paper describes was not
consulted; the constructions were reformulated for dependent type theory, where
the refinement type `|M|` of Fig. 3 becomes an ordinary index type and much of
Fig. 4 becomes definitional.
-/

import LaxLogic.Obligation.Modality
import LaxLogic.Obligation.Connectives
import LaxLogic.Obligation.Mendler
import LaxLogic.Obligation.Tactics
import LaxLogic.Obligation.Timing
import LaxLogic.Obligation.Latch
import LaxLogic.Obligation.LatchSynth
import LaxLogic.Obligation.Adder
import LaxLogic.Obligation.BeliefLink
import LaxLogic.Obligation.PLLBridge
import LaxLogic.Obligation.StdCtxBridge
import LaxLogic.Obligation.Ledger
import LaxLogic.Obligation.Postpone
import LaxLogic.Obligation.Conservativity
import LaxLogic.Obligation.Examples
