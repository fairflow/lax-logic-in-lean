/- Challenge: `isIPL_erase`.  Group: nd-core.
   Replace the `sorry`.  Do not look for the original proof.

   Deliberately not stated here: where this comes from, how long the known
   proof is, or how hard it is.  Those were hints. -/
import LaxLogic.PLLFormula

/-!
# A slime-free core ND system for PLL, with conservativity over IPL

This file is the "canonical system" produced by the transport-problem audit
(see `transport-problem-brief.md` §6).  Design rules applied:

* Contexts are `List PLLFormula`, extended only by `φ :: Γ` — every index in a
  constructor return type is a variable or a constructor form (no `++`, no
  `∪`, no `map`): McBride's no-green-slime rule.
* The identity rule takes a membership hypothesis `φ ∈ Γ` instead of pinning
  `φ` at a position in the context.  Exchange, weakening and contraction are
  then *admissible* (`LaxND.rename`) rather than structural rules, so the
  `move`/exchange rule of `LaxNDList` is derivable (`LaxND.move`) and no cast
  is ever needed.
* `orElim` carries its major premise `Γ ⊢ φ ∨ ψ` (missing from the other
  systems in this repo, which makes them derive everything — see the audit).

Consequences: the erasure translation `LaxND.erased` and both conservativity
theorems below are entirely cast-free — no `▸`, no `cast`, no `HEq`.
-/

open PLLFormula

namespace PLLND

/-- Erase the lax modality: `◯φ ↦ φ` recursively.  (Same function as
`eraseSomehow`/`zapSomehow` elsewhere in this repo, kept local so this file
only depends on `PLLFormula`.) -/
@[simp]
def erase : PLLFormula → PLLFormula
  | .prop a     => .prop a
  | .falsePLL   => .falsePLL
  | .ifThen φ ψ => .ifThen (erase φ) (erase ψ)
  | .and φ ψ    => .and (erase φ) (erase ψ)
  | .or φ ψ     => .or (erase φ) (erase ψ)
  | .somehow φ  => erase φ

/-- A formula is an IPL formula iff it contains no `somehow`. -/
@[simp]
def isIPL : PLLFormula → Prop
  | .prop _     => True
  | .falsePLL   => True
  | .ifThen φ ψ => isIPL φ ∧ isIPL ψ
  | .and φ ψ    => isIPL φ ∧ isIPL ψ
  | .or φ ψ     => isIPL φ ∧ isIPL ψ
  | .somehow _  => False

@[simp]
lemma isIPL_erase (φ : PLLFormula) : isIPL (erase φ) := by
  sorry
