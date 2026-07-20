import LaxLogic.PLLTimingRipple

/-!
# Carry-lookahead vs ripple: proof restructuring is circuit speed-up

`PLLTimingRipple.lean` shows the ripple carry has delay `n·δ` — linear in the
width, and *tight* (extraction equals the topological path).  The engineering
fix is the carry-**lookahead** adder, whose delay is `O(log n)`.  This file
mechanises the contrast and pins down what, logically, the speed-up *is*.

## The lookahead principle: an associative fold

The carry-lookahead insight (Brent–Kung and every prefix adder) is that the
block carry is the fold of the per-bit *(generate, propagate)* pairs under the
associative prefix operator

  `(g, p) ∘ (g', p') = (g ∨ (p ∧ g'), p ∧ p')`.

We abstract a `(g, p)` pair as one lax signal `◯gp` (ready when the pair is
stable) and the operator as **one reusable merge cell**

  `∘ : ◯gp ⊃ ◯gp ⊃ ◯gp`,

exactly the shape of the ripple's carry cell.  Because `∘` is associative, the
*same* group pair can be folded in *any* tree shape — and the shape is the only
thing that differs between ripple and lookahead:

* `linFold n`  — the **ripple-shaped** left fold: `∘` nested `n` deep, delay
  `n·δ` (`linReady_bound`, by induction — the same argument as
  `RippleN.ready_bound`);
* `balFold k`  — the **balanced** fold over `2ᵏ` leaves: `∘` in a perfect
  binary tree of *depth* `k`, delay `k·δ` (`balReady_bound`, by induction).

Both are proof terms of the **same sequent** `Γ ⊢ ◯gp` (`Γ = [∘, leaf]`), and
`balFold k` and `linFold (2ᵏ - 1)` use the **same `2ᵏ - 1` merge gates** — the
balanced tree merely re-associates them.  Yet:

  `lookahead_beats_ripple : balReady δ k  <  linReady δ (2ᵏ - 1)`   (`0 < δ`, `2 ≤ k`)

i.e. `k·δ < (2ᵏ - 1)·δ` — the delay drops from linear to logarithmic in the leaf
count with **no extra hardware**.  So *restructuring the derivation to reduce
its `◯`-nesting depth — re-associating the fold into a balanced tree — is the
circuit speed-up.*  Ripple is the maximally-mediated (deepest) proof of the
group carry; lookahead is a shallow proof of the very same `◯gp`.

## Belief reading

`◯gp` is "the group carry is believed ready".  The ripple believes it through a
chain of `2ᵏ - 1` mediated inferences; the lookahead believes the *same* fact
through a depth-`k` argument over the same premises.  Evidential depth is what
`◯`'s sequential `+` charges for, and re-associating a proof of equal size into
a shallower one is exactly how the cost is cut.
-/

open PLLFormula

namespace PLLND
namespace Lookahead

/-! ## The associative merge cell and its two fold shapes -/

/-- A `(generate, propagate)` group pair, abstracted as one lax signal:
`◯gp` is ready when the pair is stable. -/
abbrev Ogp := somehow (prop "gp")

/-- The netlist: one reusable prefix-merge cell `∘ : ◯gp ⊃ ◯gp ⊃ ◯gp` and a
leaf pair `◯gp`.  Independent of how deep we fold. -/
abbrev Γ : List PLLFormula := [Ogp.ifThen (Ogp.ifThen Ogp), Ogp]

/-- **The ripple-shaped (linear) fold**: `∘` nested `n` deep to the left.  Same
shape as `RippleN.ripple`; `linFold n : Γ ⊢ ◯gp`. -/
def linFold : ℕ → Tm Γ Ogp
  | 0     => .var (.there .here)                                 -- leaf
  | n + 1 => .app (.app (.var .here) (linFold n)) (.var (.there .here))  -- ∘ (linFold n) leaf

/-- **The balanced (lookahead) fold** over `2ᵏ` leaves: `∘` in a perfect binary
tree of depth `k`.  `balFold k : Γ ⊢ ◯gp` — the *same sequent* as `linFold`. -/
def balFold : ℕ → Tm Γ Ogp
  | 0     => .var (.there .here)                                 -- leaf
  | k + 1 => .app (.app (.var .here) (balFold k)) (balFold k)    -- ∘ (balFold k) (balFold k)

/-- Curry–Howard: both folds are genuine PLL derivations of `◯gp`. -/
example (n : ℕ) : Nonempty (LaxND Γ Ogp) := ⟨(linFold n).toND⟩
example (k : ℕ) : Nonempty (LaxND Γ Ogp) := ⟨(balFold k).toND⟩

/-- The environment: merge cell delay `δ` (a 2-input gate, `σ = max`), leaf pair
ready at `0`. -/
def env (δ : ℕ) : Env (M := ℕ) B Γ :=
  (gate2 δ, ((0, ()), PUnit.unit))

/-- Extracted ready-time of the linear (ripple-shaped) fold. -/
abbrev linReady (δ n : ℕ) : ℕ := (Tm.eval (· + ·) 0 B (linFold n) (env δ)).1

/-- Extracted ready-time of the balanced (lookahead) fold. -/
abbrev balReady (δ k : ℕ) : ℕ := (Tm.eval (· + ·) 0 B (balFold k) (env δ)).1

/-! ## Linear fold: delay `n·δ` (the ripple shape again) -/

theorem linReady_zero (δ : ℕ) : linReady δ 0 = 0 := rfl

theorem linReady_succ (δ n : ℕ) : linReady δ (n + 1) = max (linReady δ n) 0 + δ := rfl

/-- The ripple-shaped fold has delay `n·δ` — linear in the fold depth. -/
theorem linReady_bound (δ n : ℕ) : linReady δ n = n * δ := by
  induction n with
  | zero => simp [linReady_zero]
  | succ n ih => rw [linReady_succ, ih, add_one_mul]; omega

/-! ## Balanced fold: delay `k·δ` (logarithmic in the leaf count) -/

theorem balReady_zero (δ : ℕ) : balReady δ 0 = 0 := rfl

/-- Each level of the balanced tree merges two identical subtrees — `σ = max`
of equal ready-times — and pays one cell delay: `balₖ₊₁ = max balₖ balₖ + δ`. -/
theorem balReady_succ (δ k : ℕ) :
    balReady δ (k + 1) = max (balReady δ k) (balReady δ k) + δ := rfl

/-- **The balanced fold has delay `k·δ`** — depth `k` over `2ᵏ` leaves, so
logarithmic in the leaf count.  By induction on the depth. -/
theorem balReady_bound (δ k : ℕ) : balReady δ k = k * δ := by
  induction k with
  | zero => simp [balReady_zero]
  | succ k ih => rw [balReady_succ, ih, add_one_mul]; omega

/-! ## The speed-up: same gates, re-associated, exponentially less delay -/

/-- `k < 2ᵏ - 1` for `k ≥ 2`: the balanced depth is below the linear length. -/
theorem lt_two_pow_pred (k : ℕ) (hk : 2 ≤ k) : k < 2 ^ k - 1 := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
      have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
      have hpos : 0 < 2 ^ k := pow_pos (by norm_num) k
      omega

/-- **Carry-lookahead beats ripple: proof restructuring is speed-up.**  The
balanced fold `balFold k` and the ripple-shaped fold `linFold (2ᵏ - 1)` derive
the *same* `◯gp` from the *same* `2ᵏ - 1` merge cells — the balanced tree only
re-associates them — yet the balanced delay `k·δ` is strictly below the linear
`(2ᵏ - 1)·δ`.  Delay is `◯`-nesting depth; the lookahead is the shallow proof. -/
theorem lookahead_beats_ripple (δ k : ℕ) (hδ : 0 < δ) (hk : 2 ≤ k) :
    balReady δ k < linReady δ (2 ^ k - 1) := by
  rw [balReady_bound, linReady_bound]
  exact mul_lt_mul_of_pos_right (lt_two_pow_pred k hk) hδ

/-! ### Concrete numbers — nominal merge delay `dMERGE = 120 ps`

The prefix merge is a generate/propagate combine of delay comparable to the
full-adder carry cell (`dMERGE = dCARRY = 120 ps`, nominal sky130; illustrative,
not sign-off STA — same discipline as `PLLTiming`). -/

/-- Nominal prefix-merge delay (ps), taken equal to the carry cell. -/
def dMERGE : ℕ := 120

/-- A 32-bit block (`2⁵` leaves) folded the **ripple** way: `31` merges in a
line, `31·120 = 3720 ps`. -/
example : linReady dMERGE (2 ^ 5 - 1) = 3720 := by rw [linReady_bound]; decide

/-- The **same** 32-bit block folded the **lookahead** way: a depth-`5` balanced
tree of the same `31` merges, `5·120 = 600 ps`. -/
example : balReady dMERGE 5 = 600 := by rw [balReady_bound]; decide

/-- The lookahead is `6.2×` faster than the ripple on a 32-bit block, using the
same hardware — kernel-checked. -/
example : balReady dMERGE 5 < linReady dMERGE (2 ^ 5 - 1) :=
  lookahead_beats_ripple dMERGE 5 (by decide) (by norm_num)

/-! ## Axiom audits — measured and pinned on creation (2026-07-20)

The `_zero`/`_succ` recurrences are `rfl` (the extractor reads the delay off the
proof term), hence axiom-free.  The linear/balanced bounds go through
`omega`/`Nat` lemmas (`propext, Quot.sound`); the depth inequality and the
speed-up theorem use `Nat.le_induction` and ordered-algebra lemmas, so also draw
`Classical.choice` — the clean-classical tier, still sound. -/

/-- info: 'PLLND.Lookahead.linReady_zero' does not depend on any axioms -/
#guard_msgs in
#print axioms linReady_zero

/-- info: 'PLLND.Lookahead.linReady_succ' does not depend on any axioms -/
#guard_msgs in
#print axioms linReady_succ

/-- info: 'PLLND.Lookahead.linReady_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms linReady_bound

/-- info: 'PLLND.Lookahead.balReady_zero' does not depend on any axioms -/
#guard_msgs in
#print axioms balReady_zero

/-- info: 'PLLND.Lookahead.balReady_succ' does not depend on any axioms -/
#guard_msgs in
#print axioms balReady_succ

/-- info: 'PLLND.Lookahead.balReady_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms balReady_bound

/--
info: 'PLLND.Lookahead.lt_two_pow_pred' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms lt_two_pow_pred

/--
info: 'PLLND.Lookahead.lookahead_beats_ripple' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms lookahead_beats_ripple

end Lookahead
end PLLND
