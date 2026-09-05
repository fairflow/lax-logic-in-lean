# `LaxLogic.Obligation`

Lax modalities, and proof holes that record a debt instead of asserting the goal.

Lean's `sorry` elaborates to `sorryAx`, which inhabits the goal outright: a
declaration containing one *asserts* its statement on no evidence, and
`#print axioms` reports only that something is missing, not what. `postpone`
closes a goal by recording it as an **obligation** and discharging it from a
hypothesis, so what enters the environment is

```
theorem foo : foo.obligation1 → … → foo.obligationN → <the intended goal>
```

a complete, `sorry`-free theorem about a weaker statement. Its axioms are
whatever the finished parts of the proof used; the holes contribute none.

The theory behind it is the abstraction/refinement apparatus of Fairtlough,
Mendler and Cheng, *Abstraction and refinement in higher order logic*, TPHOLs
2001, LNCS 2152, 201–216 — reformulated for Lean, not ported. The paper's
Theorem 1 (conservativity over HOL) is deliberately left for later work.

## Files

| module | what is in it |
| --- | --- |
| `Modality.lean` | `LaxAll` (`◯∀`) and `LaxEx` (`◯∃`) by their Fig. 4 clauses; the rules `◯∧` and `◯⊃`; functoriality, monotonicity, strength; the one-witness case `Debt`; the two degeneracies that constrain any tool built on this. No imports. |
| `Timing.lean` | The reading the modality was invented for: on lower bounds over a clock, combining constraints is `max` and propagating one through a delay is `+`. Includes the paper's introductory example in general form. |
| `Ledger.lean` | The persistent environment extension. Separate module because `initialize` cannot be consumed where it is declared. |
| `Postpone.lean` | The `postpone` tactic, the `postponing theorem` command, and the `#obligations` / `#obligations_json` reports. |
| `Examples.lean` | Documentation and gate: every axiom claim pinned with `#guard_msgs`, including the negative case showing what `sorry` does to the same proof. |

## Quick start

```lean
import LaxLogic.Obligation

postponing theorem split (n : Nat) : n + 0 = n ∧ n * 1 = n := by
  refine ⟨?_, ?_⟩
  · rfl
  · postpone
-- split : split.obligation1 → ∀ (n : Nat), n + 0 = n ∧ n * 1 = n
-- #print axioms split  →  does not depend on any axioms

theorem split' (n : Nat) : n + 0 = n ∧ n * 1 = n :=
  split (fun m => Nat.mul_one m) n
```

Obligation constants are reducible, so a proof of the underlying statement is
accepted directly with no unfolding step.

## Using it in an automated proving loop

The mechanism was built with this in mind, and three properties matter.

**Every attempt produces a checked artefact.** A run that closes nothing still
yields `foo : foo.obligation1 → G`, kernel-accepted and axiom-free. Nothing is
discarded, and nothing false is banked.

**Progress is measurable.** `#obligations_json` emits one object per
declaration, so a loop can record how the outstanding count and the obligation
statements change between iterations, instead of a pass/fail bit.

```bash
# one JSON object per declaration that owes something
lake env lean <file-that-imports-your-module> 2>&1 | grep '^{'
```

**Attempts compose.** An obligation is a named constant, so an obligation left
by one iteration is the goal of the next:

```lean
postponing theorem foo.obligation1_proof : foo.obligation1 := by
  …            -- may itself use `postpone`, and the debt chains
```

and a `postponing theorem` built from holed theorems in other modules
accumulates their obligations alongside its own. The ledger survives `import`.

### The one thing a loop must not do

`Debt.trivial : Debt A A` is provable: taking the goal as its own obligation is
always possible and achieves nothing. It is a fixed point of the calculus and it
is exactly what `sorry` does. A loop that treats "obligation recorded" as
progress is therefore measuring nothing, and a search driven by obligation size
will find this exploit immediately. An independent residual measure and a guard
against it are needed before any of this is used as a reward signal. That work
is not done here.

## Limits of this first cut

- `postpone` reverts the **whole** local context. Safe — a hypothesis absent
  from the goal may still be needed to prove it — but it makes obligations
  larger than necessary. Simplification and context hoisting are not done.
- Obligations are deduplicated by syntactic equality only.
- `postponing theorem` re-implements only what it needs of `theorem`: a doc
  comment, binders, a type and a body. Attributes, `private`/`protected`,
  mutual blocks and the equation compiler are not supported.
- `Prop` goals only. A hole standing for data would make the obligation
  computational, which is a different design; `postpone` refuses such a goal
  rather than producing an ill-typed obligation.
