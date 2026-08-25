/-
CERTIFIED REWRITING for PLL — turning banked (in)equations into a
simplifier.

Matthew's observation (2026-08-14): every certified interderivability
in this repo is not only a result but a potential SIMPLIFIER, and most
especially inside subformulas.  Search currently re-derives everything
from scratch; only cheap SYNTACTIC folding is reused (`nfc` in
wip/closed_frag.lean), and the SEMANTIC corpus — the closed-fragment
catalogue, the rung classification, the dictionary — is never used to
shrink a goal.

The enabler is already in the tree: `Interd` is a full congruence
(`Interd.and_congr`, `or_congr`, `imp_congr`, **`box_congr`**,
LaxLogic/PLLSemUIFrag.lean), so rewriting a SUBFORMULA by a certified
interderivability preserves interderivability.  This file makes that
mechanical.

DESIGN NOTES.

* **Fuel, not a measure.**  Normalisation is fuel-bounded rather than
  well-founded on a complexity measure.  The payoff is that
  correctness is UNCONDITIONAL: every step preserves `Interd`, so
  `norm_interd` holds for any fuel and any rule list, however badly
  oriented — no termination obligation, no confluence obligation.
  Orientation and confluence then become questions of EFFECTIVENESS,
  screenable, never of soundness.
* **Orientation.**  Rules should be oriented big-to-small by `crank`
  (the repo's own measure: ⊃ costs 1, ◯ costs 2, ∧/∨ take the max),
  which is exactly the "reduce ⊃/◯ nesting" instinct.  `crankOriented`
  below checks a rule list, and is a SCREEN, not a hypothesis.
* **Stratify by logic.**  A PCLL-only equation (e.g. the four
  distribution merges of the catalogue) must NOT sit in a PLL rule
  list, or PLL goals would be silently simplified by non-PLL facts.
  `RwRule` carries a `Interd` proof, so this is enforced by TYPE: a
  PCLL-only merge simply cannot be given one.
-/
import LaxLogic.PLLSemUIFrag
import LaxLogic.PLLSemUILayered

namespace Rewrite

open PLLND PLLND.SemUI

/-- A rewrite rule: a certified interderivability, oriented. -/
structure RwRule where
  lhs : PLLFormula
  rhs : PLLFormula
  ok : Interd lhs rhs

/-- Fire the first rule whose left-hand side matches at the top. -/
def rwStep (rs : List RwRule) (φ : PLLFormula) : PLLFormula :=
  match rs.find? (fun r => decide (r.lhs = φ)) with
  | some r => r.rhs
  | none => φ

theorem rwStep_interd (rs : List RwRule) (φ : PLLFormula) :
    Interd φ (rwStep rs φ) := by
  unfold rwStep
  cases h : rs.find? (fun r => decide (r.lhs = φ)) with
  | none => exact Interd.refl φ
  | some r =>
      have hm : r.lhs = φ := by
        have := List.find?_some h
        simpa using this
      exact hm ▸ r.ok

/-- **Normalise**: rewrite subformulas first, then at the top.  Fuel
bounds the number of passes. -/
def norm (rs : List RwRule) : Nat → PLLFormula → PLLFormula
  | 0, φ => φ
  | n + 1, φ =>
      rwStep rs <|
        match φ with
        | .and a b => .and (norm rs n a) (norm rs n b)
        | .or a b => .or (norm rs n a) (norm rs n b)
        | .ifThen a b => .ifThen (norm rs n a) (norm rs n b)
        | .somehow a => .somehow (norm rs n a)
        | x => x

/-- **CORRECTNESS, unconditional**: the normal form is interderivable
with the input, for ANY fuel and ANY rule list.  No termination or
confluence obligation — orientation is an effectiveness question. -/
theorem norm_interd (rs : List RwRule) :
    ∀ (n : Nat) (φ : PLLFormula), Interd φ (norm rs n φ) := by
  intro n
  induction n with
  | zero => intro φ; exact Interd.refl φ
  | succ n ih =>
      intro φ
      refine Interd.trans ?_ (rwStep_interd rs _)
      cases φ with
      | prop a => exact Interd.refl _
      | falsePLL => exact Interd.refl _
      | and a b => exact Interd.and_congr (ih a) (ih b)
      | or a b => exact Interd.or_congr (ih a) (ih b)
      | ifThen a b => exact Interd.imp_congr (ih a) (ih b)
      | somehow a => exact Interd.box_congr (ih a)

/-- **The goal-level reduction.**  Normalising both sides of a
sequent is sound BOTH WAYS: `φ ⊢ ψ` iff `norm φ ⊢ norm ψ`. -/
theorem deriv_iff_norm (rs : List RwRule) (n : Nat) (φ ψ : PLLFormula) :
    Nonempty (LaxND [φ] ψ) ↔
      Nonempty (LaxND [norm rs n φ] (norm rs n ψ)) := by
  constructor
  · rintro ⟨d⟩
    obtain ⟨-, ⟨back⟩⟩ := norm_interd rs n φ
    obtain ⟨⟨fwd⟩, -⟩ := norm_interd rs n ψ
    exact ⟨.impElim (.impIntro (fwd.rename (by
        intro χ hχ
        rcases List.mem_cons.mp hχ with rfl | hχ
        · exact .head _
        · exact absurd hχ (by simp))))
      (.impElim (.impIntro (d.rename (by
        intro χ hχ
        rcases List.mem_cons.mp hχ with rfl | hχ
        · exact .head _
        · exact absurd hχ (by simp))))
        (back.rename (by intro χ hχ; exact hχ)))⟩
  · rintro ⟨d⟩
    obtain ⟨⟨fwd⟩, -⟩ := norm_interd rs n φ
    obtain ⟨-, ⟨back⟩⟩ := norm_interd rs n ψ
    exact ⟨.impElim (.impIntro (back.rename (by
        intro χ hχ
        rcases List.mem_cons.mp hχ with rfl | hχ
        · exact .head _
        · exact absurd hχ (by simp))))
      (.impElim (.impIntro (d.rename (by
        intro χ hχ
        rcases List.mem_cons.mp hχ with rfl | hχ
        · exact .head _
        · exact absurd hχ (by simp))))
        (fwd.rename (by intro χ hχ; exact hχ)))⟩

/-! ## Orientation screen -/

/-- A rule is crank-oriented when it does not increase `crank`. -/
def crankOriented (r : RwRule) : Bool := decide (crank r.rhs ≤ crank r.lhs)

/-- Screen a rule list.  A FALSE here is a warning about
effectiveness, never about soundness (`norm_interd` is
unconditional). -/
def allOriented (rs : List RwRule) : Bool := rs.all crankOriented

/-! ## Pins -/

/--
info: 'Rewrite.norm_interd' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms norm_interd

/--
info: 'Rewrite.deriv_iff_norm' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms deriv_iff_norm

end Rewrite
