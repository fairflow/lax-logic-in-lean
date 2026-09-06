/-
# The adder, rerun through the obligation library

`Latch.lean`/`LatchSynth.lean` take the TPHOLs paper's RS latch through the
library. This file does the same for the repository's own adders — the
`n`-bit ripple carry of `PLLTimingRipple.lean` and the balanced prefix fold of
`PLLTimingLookahead.lean`, the example that carries the belief reading
("`◯gp` is *the group carry is believed ready*").

Those two files run the **`◯∃`** side of Fig. 4: `Tm.eval` is a writer monad
over `(ℕ, +, 0)` with `σ = max`, so evaluating the proof term *returns* a delay
alongside the value. This file runs the same two circuits through the **`◯∀`**
side: the delay is not returned, it is the constraint the claim is weakened by.
The point of doing both is that the answers must agree, and `ripple_is_extracted`
/ `bal_is_extracted` below say they do — the number the extractor computes off
the proof term is the bound in the obligation.

## What the rerun adds

Three things the writer reading cannot express.

* **One cell, two shapes, one theorem.** `carry_cell` is `Timing.pipeline`: two
  signals available from `a` and `b` feeding a cell of delay `δ`, giving
  `max a b + δ`. The ripple chain and the balanced fold are the *same*
  induction over that cell (`chain_ready`, `bal_ready`) — as in the object logic,
  where `linFold` and `balFold` inhabit one sequent `Γ ⊢ ◯gp` and differ only in
  associativity.

* **The cycle-time question is an obligation, not a hypothesis.** "Does this
  adder make the clock?" is the constraint synthesised by `postpone` when the
  derived availability `◯∀[from_ (n·δ)]` is weakened to the demanded
  `◯∀[from_ T]`:

      obligation1 : ∀ z, T ≤ z → n * δ ≤ z

  which is the same shape as the latch's equation (8), reduced by the same
  tactic (`reduce_obligation`) to the same kind of answer, `n * δ ≤ T`.

* **The loop of Fig. 9 actually closes.** At 32 bits and a 1 ns cycle the
  synthesised obligation is **false**, kernel-checked
  (`ripple32_obligation_false`) — not "unproved", refuted. Re-associating the
  fold into a balanced tree, which `Lookahead.balGP_eq_linGP` licenses because
  it computes the same group pair, replaces the obligation by one that
  discharges (`lookahead32_obligation_holds`). Synthesise, refute, restructure,
  discharge: the constraint drove a design decision.

  Replacing either `postpone` by `sorry` does not merely taint the proof: it
  produces *no* `obligation1` constant at all, so §7 and §8 fail to elaborate
  with `Unknown constant`. That is the difference the library exists for, and
  it was watched happening before these gates were pinned.

## Which constraint is the easier one

`Stronger p q` is `∀ z, p z → q z`, and `◯∀` is *antitone* in it
(`laxAll_mono`). A later availability is a *stronger* demand, so the ripple's
constraint entails the lookahead's and not conversely
(`lookahead_strictly_weaker`). "The design got faster" is literally movement up
that order — the same order `BeliefLink.laxAll_iff_le` identifies with
entailment in the Heyting algebra `ℕ → Prop`.
-/

import LaxLogic.Obligation.Timing
import LaxLogic.Obligation.Postpone
import LaxLogic.Obligation.Conservativity
import LaxLogic.Obligation.Tactics
import LaxLogic.Obligation.Solve
import LaxLogic.PLLTimingLookahead

namespace LaxLogic.Obligation.Adder

open LaxLogic.Obligation LaxLogic.Obligation.Timing

/-! ## 1. The carry cell

A combinational cell with two inputs and delay `δ`, specified functionally: if
both inputs held at some `s` with `s + δ ≤ t`, the output holds at `t`. This is
the hypothesis shape of `Timing.pipeline`, and it is the `◯∀` reading of the
object-logic netlist hypothesis `◯c ⊃ ◯p ⊃ ◯c`. -/

/-- The specification of a two-input cell of delay `δ`: functional behaviour
only, with no availability times mentioned. -/
def CellSpec (In₁ In₂ Out : Refined Nat) (δ : Nat) : Prop :=
  ∀ t, (∃ s, s + δ ≤ t ∧ In₁ s ∧ In₂ s) → Out t

/-- **The cell rule.** Availability composes as `max` then `+ δ` — the two rows
of `Timing.lean`'s table, applied once. Everything below is this by induction. -/
theorem carry_cell {In₁ In₂ Out : Refined Nat} {a b δ : Nat}
    (h₁ : ◯∀[from_ a] In₁) (h₂ : ◯∀[from_ b] In₂)
    (hcell : CellSpec In₁ In₂ Out δ) :
    ◯∀[from_ (max a b + δ)] Out :=
  pipeline h₁ h₂ hcell

/-! ## 2. The ripple carry chain

`PLLTimingRipple.lean`'s netlist is one reusable carry cell `◯c ⊃ ◯p ⊃ ◯c`, a
propagate line and a carry-in, and the width-`n` carry-out is that cell applied
`n` times. Here the same chain, with the carries as a family of refined
formulas over the clock. -/

/-- The width-independent netlist: at every stage, the previous carry and the
propagate line drive the next carry through a cell of delay `δ`. -/
def RippleNet (Cy : Nat → Refined Nat) (Pr : Refined Nat) (δ : Nat) : Prop :=
  ∀ i, CellSpec (Cy i) Pr (Cy (i + 1)) δ

/-- **Linear carry delay in the `◯∀` reading**, by induction on the width — the
same induction as `RippleN.ready_bound`, one carry cell per step. With carry-in
and propagate available from `0`, the width-`n` carry-out is available from
`n·δ`. -/
theorem chain_ready {Cy : Nat → Refined Nat} {Pr : Refined Nat} {δ : Nat}
    (hnet : RippleNet Cy Pr δ)
    (hcin : ◯∀[from_ 0] (Cy 0)) (hp : ◯∀[from_ 0] Pr) :
    ∀ n, ◯∀[from_ (n * δ)] (Cy n) := by
  intro n
  induction n with
  | zero => simpa using hcin
  | succ n ih =>
      have h := carry_cell ih hp (hnet n)
      have he : max (n * δ) 0 + δ = (n + 1) * δ := by rw [add_one_mul]; omega
      rwa [he] at h

/-! ## 3. The balanced fold

`PLLTimingLookahead.lean` abstracts a `(generate, propagate)` pair as one lax
signal `◯gp` and the prefix operator as one reusable merge cell
`◯gp ⊃ ◯gp ⊃ ◯gp`. Both its folds inhabit that single sequent; only the tree
shape differs. In the `◯∀` reading the merge cell is `CellSpec Gp Gp Gp δ`, and
the two folds are the *same* theorem read at two depths. -/

/-- The prefix-merge netlist: one cell of delay `δ` combining two group pairs
into a group pair. -/
def MergeNet (Gp : Refined Nat) (δ : Nat) : Prop := CellSpec Gp Gp Gp δ

/-- **Depth-`k` availability of the merged group pair.** Each level merges two
subtrees of equal availability — `max` of equal times — and pays one cell
delay, so depth `k` costs `k·δ` whatever the leaf count. This is
`Lookahead.balReady_bound`, and at `k := 2ᵏ - 1` it is `Lookahead.linReady_bound`:
the ripple-shaped fold of `2ᵏ` leaves has depth `2ᵏ - 1`, the balanced fold of
the same leaves has depth `k`. -/
theorem bal_ready {Gp : Refined Nat} {δ : Nat}
    (hm : MergeNet Gp δ) (hleaf : ◯∀[from_ 0] Gp) :
    ∀ k, ◯∀[from_ (k * δ)] Gp := by
  intro k
  induction k with
  | zero => simpa using hleaf
  | succ k ih =>
      have h := carry_cell ih ih hm
      have he : max (k * δ) (k * δ) + δ = (k + 1) * δ := by rw [add_one_mul]; omega
      rwa [he] at h

/-! ## 4. Which availability constraint is easier to meet -/

/-- `k + 1 < 2ᵏ` for `k ≥ 2`. `Lookahead.lt_two_pow_pred` says the same thing but
goes through Mathlib's `Nat.le_induction` and `norm_num`, which drag in
`Classical.choice`; this development's axiom discipline is worth the six lines. -/
private theorem succ_lt_two_pow : ∀ k, 2 ≤ k → k + 1 < 2 ^ k
  | 0, h => absurd h (by omega)
  | 1, h => absurd h (by omega)
  | 2, _ => by decide
  | (n + 3), _ => by
      have ih := succ_lt_two_pow (n + 2) (by omega)
      have hp : 2 ^ (n + 3) = 2 ^ (n + 2) * 2 := Nat.pow_succ ..
      omega

/-- The balanced depth is strictly below the ripple length, `Classical.choice`-free. -/
private theorem lt_two_pow_pred' (k : Nat) (hk : 2 ≤ k) : k < 2 ^ k - 1 := by
  have := succ_lt_two_pow k hk
  omega

/-- Availability later is a stronger demand. -/
theorem stronger_of_le {a b : Nat} (h : b ≤ a) : Stronger (from_ a) (from_ b) :=
  fun _ hz => Nat.le_trans h hz

/-- **The lookahead's constraint is strictly weaker than the ripple's.** The
ripple's availability entails the lookahead's — so anything provable under the
lookahead bound is provable under the ripple bound — and the converse fails, by
the same arithmetic that makes `Lookahead.lookahead_beats_ripple` true.

`◯∀` being antitone (`laxAll_mono`), this is exactly the statement that the
balanced design is the easier obligation. -/
theorem lookahead_strictly_weaker (δ k : Nat) (hδ : 0 < δ) (hk : 2 ≤ k) :
    Stronger (from_ ((2 ^ k - 1) * δ)) (from_ (k * δ)) ∧
      ¬ Stronger (from_ (k * δ)) (from_ ((2 ^ k - 1) * δ)) := by
  have hlt : k * δ < (2 ^ k - 1) * δ :=
    Nat.mul_lt_mul_of_lt_of_le (lt_two_pow_pred' k hk) (Nat.le_refl δ) hδ
  refine ⟨stronger_of_le (Nat.le_of_lt hlt), fun hcon => ?_⟩
  exact absurd (hcon (k * δ) (Nat.le_refl _)) (by omega)

/-! ## 5. The two readings agree

The bound in the `◯∀` statement is the number the `◯∃` extractor computes off
the proof term. Nothing forces this: `chain_ready` is an induction in the
weakening reading and `RippleN.ready_bound` an evaluation in the writer reading,
and they meet only because both are the same recurrence
`rₙ₊₁ = max rₙ tp + δ`. -/

/-- The ripple's obligation bound **is** `RippleN.ready`, the delay extracted
from the object-logic proof term `RippleN.ripple n`. -/
theorem ripple_is_extracted {Cy : Nat → Refined Nat} {Pr : Refined Nat} {δ : Nat}
    (hnet : RippleNet Cy Pr δ)
    (hcin : ◯∀[from_ 0] (Cy 0)) (hp : ◯∀[from_ 0] Pr) (n : Nat) :
    ◯∀[from_ (PLLND.RippleN.ready δ 0 0 n)] (Cy n) := by
  rw [PLLND.RippleN.ready_bound]
  exact chain_ready hnet hcin hp n

/-- The balanced fold's obligation bound **is** `Lookahead.balReady`, the delay
extracted from `Lookahead.balFold k`. -/
theorem bal_is_extracted {Gp : Refined Nat} {δ : Nat}
    (hm : MergeNet Gp δ) (hleaf : ◯∀[from_ 0] Gp) (k : Nat) :
    ◯∀[from_ (PLLND.Lookahead.balReady δ k)] Gp := by
  rw [PLLND.Lookahead.balReady_bound]
  exact bal_ready hm hleaf k

/-! ## 6. Synthesising the cycle-time constraint

The design question is not "what is the delay" — the sections above answer that
— but "does the carry make the sampling edge at `T`". Written as a theorem, that
is `◯∀[from_ T] (Cy n)`: the carry-out holds from `T` onwards. Deriving it from
`chain_ready` needs exactly one step, `laxAll_mono`, and its side condition is
the timing constraint. `postpone` records it instead of demanding it. -/

/-- **The ripple adder meets the cycle — modulo one recorded obligation.** The
statement carries no timing hypothesis; the timing hypothesis is what comes
out. -/
postponing theorem ripple_meets_cycle
    (Cy : Nat → Refined Nat) (Pr : Refined Nat) (δ n T : Nat)
    (hnet : RippleNet Cy Pr δ)
    (hcin : ◯∀[from_ 0] (Cy 0)) (hp : ◯∀[from_ 0] Pr) :
    ◯∀[from_ T] (Cy n) := by
  refine laxAll_mono (fun z (hz : T ≤ z) => ?_) (chain_ready hnet hcin hp n)
  postpone   -- becomes the CYCLE-TIME constraint

/-- **The balanced fold meets the cycle — modulo one recorded obligation.** The
same derivation over the same cell; only the depth differs. -/
postponing theorem bal_meets_cycle
    (Gp : Refined Nat) (δ k T : Nat)
    (hm : MergeNet Gp δ) (hleaf : ◯∀[from_ 0] Gp) :
    ◯∀[from_ T] Gp := by
  refine laxAll_mono (fun z (hz : T ≤ z) => ?_) (bal_ready hm hleaf k)
  postpone   -- becomes the CYCLE-TIME constraint

/-! ## 7. The synthesised constraints are already reduced

Nothing below states what the constraints reduce to, and nothing reduces them
either: `postpone` solved each one **as it recorded it**, so what the ledger
holds and what the statements quantify over is

    ripple_meets_cycle.obligation1 … = (n * δ ≤ T)
    bal_meets_cycle.obligation1 …    = (k * δ ≤ T)

That is why the refutation below needs no equivalence to rewrite through: it
unfolds the obligation constant and decides. The constant has to be *named* —
being `@[reducible]` is enough for `whnfR` but not for `simp` or `decide` — but
its right-hand side never is. `postponing theorem` also emitted
`ripple_meets_cycle_debt` and `bal_meets_cycle_debt`, the `C ⊃ φ` forms. -/

/-- Discharging the ripple's obligation recovers the conventional statement, in
which the timing constraint is a hypothesis. The derived and the assumed
constraint agree — the adder analogue of `latch_resets_synth`. Note that the
proof is just the generated `Debt`: `n * δ ≤ T` was never typed here. -/
theorem ripple_meets_cycle_of
    (Cy : Nat → Refined Nat) (Pr : Refined Nat) (δ n T : Nat)
    (hnet : RippleNet Cy Pr δ)
    (hcin : ◯∀[from_ 0] (Cy 0)) (hp : ◯∀[from_ 0] Pr)
    (hfit : n * δ ≤ T) :
    ◯∀[from_ T] (Cy n) :=
  ripple_meets_cycle_debt Cy Pr δ n T hnet hcin hp hfit

@[inherit_doc ripple_meets_cycle_of]
theorem bal_meets_cycle_of
    (Gp : Refined Nat) (δ k T : Nat)
    (hm : MergeNet Gp δ) (hleaf : ◯∀[from_ 0] Gp)
    (hfit : k * δ ≤ T) :
    ◯∀[from_ T] Gp :=
  bal_meets_cycle_debt Gp δ k T hm hleaf hfit

/-! ## 8. The loop of Fig. 9, closed

Nominal sky130 numbers, as in `PLLTimingRipple.lean` and
`PLLTimingLookahead.lean`: carry cell and prefix merge both `120 ps`. Target: a
32-bit add in a `1 ns` cycle.

The three steps below are the method. The obligation is synthesised; it is
**refuted**, not merely left unproved; the design is restructured; the
obligation is **discharged**. -/

/-- **Step 1 — the synthesised obligation is false.** A 32-bit ripple carry at
`120 ps` per cell cannot make a `1 ns` cycle: `32 · 120 = 3840 > 1000`. This is
a refutation, and it holds for *every* instantiation of the functional layer,
because the reduced constraint mentions none of it. -/
theorem ripple32_obligation_false
    (Cy : Nat → Refined Nat) (Pr : Refined Nat)
    (hnet : RippleNet Cy Pr PLLND.dCARRY)
    (hcin : ◯∀[from_ 0] (Cy 0)) (hp : ◯∀[from_ 0] Pr) :
    ¬ ripple_meets_cycle.obligation1 Cy Pr PLLND.dCARRY 32 1000 hnet hcin hp := by
  simp only [ripple_meets_cycle.obligation1]
  decide

/-- **Step 2 — restructure.** The balanced fold over the same `2⁵ = 32` leaves
uses the same `31` merge cells re-associated, and
`Lookahead.balGP_eq_linGP` proves the two folds compute the same group
`(generate, propagate)` pair, so the re-association is sound rather than a
change of specification.

**Step 3 — the obligation now discharges.** Depth `5` at `120 ps` is `600 ps`,
inside the `1 ns` cycle. -/
theorem lookahead32_obligation_holds
    (Gp : Refined Nat) (hm : MergeNet Gp PLLND.Lookahead.dMERGE)
    (hleaf : ◯∀[from_ 0] Gp) :
    bal_meets_cycle.obligation1 Gp PLLND.Lookahead.dMERGE 5 1000 hm hleaf := by
  simp only [bal_meets_cycle.obligation1]
  decide

/-- **The design decision, kernel-checked.** At 32 bits in a 1 ns cycle the
ripple's obligation is refutable and the balanced fold's discharges, delivering
the availability the specification asked for. The constraint chose the
architecture. -/
theorem restructuring_closes_the_loop
    (Gp : Refined Nat) (hm : MergeNet Gp PLLND.Lookahead.dMERGE)
    (hleaf : ◯∀[from_ 0] Gp) :
    (∀ (Cy : Nat → Refined Nat) (Pr : Refined Nat)
        (hnet : RippleNet Cy Pr PLLND.dCARRY)
        (hcin : ◯∀[from_ 0] (Cy 0)) (hp : ◯∀[from_ 0] Pr),
        ¬ ripple_meets_cycle.obligation1 Cy Pr PLLND.dCARRY 32 1000 hnet hcin hp)
      ∧ ◯∀[from_ 1000] Gp :=
  ⟨ripple32_obligation_false,
    bal_meets_cycle_of Gp PLLND.Lookahead.dMERGE 5 1000 hm hleaf (by decide)⟩

/-! ## Gates

The synthesised route is conservative: both adders are derived in the base
theory with nothing assumed, and the constraints came out rather than in. -/

/--
info: conservativity audit passed for 2 declaration(s); base-theory axioms only:
  LaxLogic.Obligation.Adder.ripple_meets_cycle — [propext, Quot.sound]
  LaxLogic.Obligation.Adder.bal_meets_cycle — [propext, Quot.sound]
-/
#guard_msgs in
#obligations_audit

/-- info: 'LaxLogic.Obligation.Adder.chain_ready' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms chain_ready

/-- info: 'LaxLogic.Obligation.Adder.bal_ready' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms bal_ready

/-- info: 'LaxLogic.Obligation.Adder.ripple_is_extracted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ripple_is_extracted

/-- info: 'LaxLogic.Obligation.Adder.bal_is_extracted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms bal_is_extracted

/-- info: 'LaxLogic.Obligation.Adder.lookahead_strictly_weaker' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lookahead_strictly_weaker

/--
info: 'LaxLogic.Obligation.Adder.restructuring_closes_the_loop' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms restructuring_closes_the_loop


end LaxLogic.Obligation.Adder
