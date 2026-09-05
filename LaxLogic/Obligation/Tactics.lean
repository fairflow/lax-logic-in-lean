/-
# `lax_abstract`, `lax_refine`, `reduce_obligation`

Three tactics, closing the two arrows of Fig. 9 that the library could state but
not *perform*, and the reduction step Mendler says is "built into constraint
reductions".

* **`lax_abstract`** is Fig. 4 read right to left: it recognises a base-logic
  goal of the shape `∀ z, C z → P z` (or `∃ z, C z ∧ P z`) and presents it as
  the abstract pair `◯∀[C] P` (resp. `◯∃[C] P`), so that the modal rules apply
  to it. The two are definitionally equal — the work the tactic does is
  *finding* `C` and `P`, which is the abstraction step.

* **`lax_refine`** is Fig. 4 read left to right: it unfolds every abstract
  formula and constraint constructor back into base logic, "zipping" the pair
  into an ordinary proposition. Use it when a modal goal is easier to finish
  concretely than by the rules.

* **`reduce_obligation`** proves `obligation ↔ <simpler form>` for the shape
  that keeps arising: a constraint universally quantified over a time, with a
  lower bound as its hypothesis. The move is to instantiate the universal at
  that bound — which unification finds by itself from `Nat.le_refl _` — and let
  `omega` finish. This is exactly the step the TPHOLs paper performs between its
  equations (8) and (9), and it is what turns a synthesised constraint into a
  readable one.

## Why the names

`refine` is a core Lean tactic, so the pair is `lax_abstract` / `lax_refine`
rather than the paper's bare *abstraction* and *refinement*.
-/

import Lean
import LaxLogic.Obligation.Connectives

namespace LaxLogic.Obligation

open Lean Meta Elab Tactic

/-- Present a base-logic goal as an abstract formula under a constraint.

`∀ z, C z → P z` becomes `◯∀[C] P`, and `∃ z, C z ∧ P z` becomes `◯∃[C] P`.
Fails if the goal has neither shape, or if the implication is dependent (a
genuine `Π`, where there is no constraint/formula split to make). -/
syntax (name := laxAbstractTac) "lax_abstract" : tactic

@[tactic laxAbstractTac]
def elabLaxAbstract : Tactic := fun _ => do
  let g ← getMainGoal
  let tgt ← instantiateMVars (← whnf (← g.getType))
  let mk (γ : Expr) (n : Name) (a b : Expr) (which : Name) : TacticM Unit := do
    -- `a` lives under `z`; `b` lives under `z` and the anonymous witness.
    if b.hasLooseBVar 0 then
      throwError "lax_abstract: the goal is a dependent Π, so it has no \
        constraint/formula split"
    let C := Expr.lam n γ a .default
    let P := Expr.lam n γ (b.lowerLooseBVars 1 1) .default
    let target ← mkAppM which #[C, P]
    let g' ← g.change target
    replaceMainGoal [g']
  match tgt with
  | .forallE n γ body _ =>
      match body with
      | .forallE _ a b _ => mk γ n a b ``LaxAll
      | _ => throwError "lax_abstract: expected `∀ z, C z → P z`"
  | _ =>
      -- `∃ z, C z ∧ P z`
      match tgt.getAppFnArgs with
      | (``Exists, #[γ, .lam n _ body _]) =>
          match body.getAppFnArgs with
          | (``And, #[a, b]) =>
              -- both `a` and `b` live under `z`; re-wrap for the shared shape
              let C := Expr.lam n γ a .default
              let P := Expr.lam n γ b .default
              let target ← mkAppM ``LaxEx #[C, P]
              let g' ← g.change target
              replaceMainGoal [g']
          | _ => throwError "lax_abstract: expected `∃ z, C z ∧ P z`"
      | _ => throwError "lax_abstract: expected `∀ z, C z → P z` or `∃ z, C z ∧ P z`"

/-- Unfold abstract formulas and constraints into base logic — Fig. 4 left to
right. `lax_refine` works on the goal, `lax_refine at h` on a hypothesis. -/
syntax (name := laxRefineTac) "lax_refine" (Lean.Parser.Tactic.location)? : tactic

macro_rules
  | `(tactic| lax_refine $[$loc]?) =>
    `(tactic| simp only [LaxAll, LaxEx, Debt, val, pair, meet, image, Stronger,
        sum, either, inl, toFun, piC, sigC,
        Refined.tt, Refined.ff, Refined.and, Refined.or, Refined.imp,
        Refined.all, Refined.ex, Refined.boxAll, Refined.boxEx] $[$loc]?)

/-- Prove `obligation ↔ <simpler form>` for a constraint of the shape
`∀ t, bound ≤ t → …`.

The forward direction instantiates the universal at the bound — `Nat.le_refl _`
makes unification choose it — and the backward direction reintroduces it; both
finish with `omega`. This is the TPHOLs paper's (8) → (9) step, and Mendler's
"constraint reduction". -/
syntax (name := reduceObligationTac) "reduce_obligation" : tactic

macro_rules
  | `(tactic| reduce_obligation) =>
    `(tactic|
        refine Iff.intro (fun h => ?_) (fun h => ?_) <;>
          first
            | omega
            | (have := h _ (Nat.le_refl _); omega)
            | (have := h _ _ (Nat.le_refl _); omega)
            | (intros; omega))

/-- Discharge an obligation **at a constraint model**: the parameters are
concrete, so the constraint is decidable arithmetic.

This is the last step of the loop. `reduce_obligation` turns a synthesised
constraint into a readable one for a human; `discharge_obligation` closes it
outright once the delays and the clock period are fixed, so the concrete
theorem is derived from the abstract one by evaluation rather than by a new
proof. -/
syntax (name := dischargeObligationTac) "discharge_obligation" : tactic

macro_rules
  | `(tactic| discharge_obligation) =>
    `(tactic| first | omega | (intros; omega) | decide | (intros; decide))

/-! ## Worked examples, which double as the tests -/

section Examples

/-- `lax_abstract` finds the constraint/formula split, and the modal rules then
apply to a goal that was stated in base logic. -/
example (P Q : Nat → Prop) (hP : ∀ s, 5 ≤ s → P s) (hQ : ∀ s, 9 ≤ s → Q s) :
    ∀ s, (5 ≤ s ∧ 9 ≤ s) → (P s ∧ Q s) := by
  lax_abstract
  exact laxAll_meet hP hQ

@[inherit_doc laxAbstractTac]
example (P : Nat → Prop) (h : ∃ s, 5 ≤ s ∧ P s) : ∃ s, 5 ≤ s ∧ P s := by
  lax_abstract
  exact h

/-- `lax_refine` goes the other way, on the goal … -/
example (p M : Constraint Nat) (h : ∀ z, p z → M z) : ◯∀[p] M := by
  lax_refine
  exact h

/-- … or on a hypothesis. -/
example (p M : Constraint Nat) (h : ◯∀[p] M) : ∀ z, p z → M z := by
  lax_refine at h
  exact h

/-- `reduce_obligation` on the two shapes the latch produced. The first is the
external hold constraint, the second the internal memory constraint. -/
example (a f : Nat) : (∀ t, a ≤ t → f ≤ t) ↔ f ≤ a := by reduce_obligation

@[inherit_doc reduceObligationTac]
example (a D : Nat) : (∀ t, a ≤ t → t < t + D) ↔ 0 < D := by reduce_obligation

/-- `discharge_obligation` at a constraint model: the same shape, but with the
delays fixed there is nothing left to state. -/
example : ∀ t, 1000 ≤ t → 5 * 120 + 60 ≤ t := by discharge_obligation

end Examples

end LaxLogic.Obligation
