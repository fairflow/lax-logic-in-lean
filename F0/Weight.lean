import LaxLogic.PLL.Syntax.Formula
import Meta.Audit

/-!
# Formula weights for the RN(◯,∅) explorer

2026-10-22, at Matthew's direction: every weight the explorer data relies on
is a Lean definition over `PLLFormula`; scripts may only read, report and
render.

* `size φ`: the node count (`⊤ = ⊥ ↠ ⊥` has size 3, `¬A = A ↠ ⊥` has size
  `size A + 2`).  It agrees with `PLLND.fsize` (`F0.size_eq_fsize`, in
  `F0/WeightGates.lean`, which may import the heavier module defining
  `fsize`).
* `boxDepth φ`: the maximum nesting of `◯`.
* `boxScope φ`: the sum, over the `◯` nodes of `φ`, of the size of the
  formula under that `◯`.
* `weight φ = (boxDepth φ, size φ, boxScope φ)`, ordered lexicographically
  (`lexLt`, `weightLt`, both decidable).
* `pickRep incumbent members`: the member of least weight; a tie with the
  incumbent keeps the incumbent; remaining ties go to the least in the
  syntactic order `synCmp`.

The last tie-break is the syntactic order `synCmp` (constructor rank
`⊥ < ∧ < ∨ < ↠ < ◯ < atoms`, then the children left to right), not
`PLLFormula.toString`: the latter reaches `Classical.choice` through the
core `String` library (`String.extract`), and these definitions are
choice-free.  `synCmp` does not compare atom names (F0 is closed); two
members that differ only in atom names tie, and the earlier one is kept.

The ρ-indices are historical labels in order of discovery, not a
systematic numbering; nothing here depends on them.

Structural recursion only; no imports beyond the formula type and the
axiom-audit command.  Pins and gates: `F0/WeightGates.lean`.
-/

namespace F0

/-- The node count. -/
def size : PLLFormula → Nat
  | .prop _ => 1
  | .falsePLL => 1
  | .and A B => size A + size B + 1
  | .or A B => size A + size B + 1
  | .ifThen A B => size A + size B + 1
  | .somehow A => size A + 1

/-- The maximum nesting of `◯`. -/
def boxDepth : PLLFormula → Nat
  | .prop _ => 0
  | .falsePLL => 0
  | .and A B => max (boxDepth A) (boxDepth B)
  | .or A B => max (boxDepth A) (boxDepth B)
  | .ifThen A B => max (boxDepth A) (boxDepth B)
  | .somehow A => boxDepth A + 1

/-- The `◯`-scope: the sum, over the `◯` nodes, of the size of the formula
under that `◯`. -/
def boxScope : PLLFormula → Nat
  | .prop _ => 0
  | .falsePLL => 0
  | .and A B => boxScope A + boxScope B
  | .or A B => boxScope A + boxScope B
  | .ifThen A B => boxScope A + boxScope B
  | .somehow A => boxScope A + size A

/-- The weight: `(◯-depth, size, ◯-scope)`. -/
def weight (φ : PLLFormula) : Nat × Nat × Nat := (boxDepth φ, size φ, boxScope φ)

/-- The lexicographic order on weights. -/
def lexLt (a b : Nat × Nat × Nat) : Prop :=
  a.1 < b.1 ∨ (a.1 = b.1 ∧ (a.2.1 < b.2.1 ∨ (a.2.1 = b.2.1 ∧ a.2.2 < b.2.2)))

instance (a b : Nat × Nat × Nat) : Decidable (lexLt a b) :=
  inferInstanceAs (Decidable (_ ∨ (_ ∧ (_ ∨ (_ ∧ _)))))

/-- `φ` weighs strictly less than `ψ`. -/
def weightLt (φ ψ : PLLFormula) : Prop := lexLt (weight φ) (weight ψ)

instance (φ ψ : PLLFormula) : Decidable (weightLt φ ψ) :=
  inferInstanceAs (Decidable (lexLt _ _))

/-- Constructor rank for the syntactic order. -/
def rank : PLLFormula → Nat
  | .falsePLL => 0
  | .and _ _ => 1
  | .or _ _ => 2
  | .ifThen _ _ => 3
  | .somehow _ => 4
  | .prop _ => 5

/-- The syntactic order: constructor rank, then the children left to right
(atom names are not compared). -/
def synCmp : PLLFormula → PLLFormula → Ordering
  | .and a b, .and c d => (synCmp a c).then (synCmp b d)
  | .or a b, .or c d => (synCmp a c).then (synCmp b d)
  | .ifThen a b, .ifThen c d => (synCmp a c).then (synCmp b d)
  | .somehow a, .somehow c => synCmp a c
  | φ, ψ => compare (rank φ) (rank ψ)

/-- `φ` comes strictly before `ψ` in the syntactic order. -/
def synBefore (φ ψ : PLLFormula) : Bool := synCmp φ ψ == .lt

/-- The representative: the member of least weight.  A tie with the
incumbent keeps the incumbent; remaining ties go to the least in the
syntactic order `synCmp`, then to the earlier member. -/
def pickRep (incumbent : PLLFormula) (members : List PLLFormula) : PLLFormula :=
  members.foldl (fun best m =>
    if weightLt m best then m
    else if weight m = weight best ∧ best ≠ incumbent ∧ synBefore m best = true then m
    else best) incumbent

/-- No `∨` anywhere in the formula. -/
def orFree : PLLFormula → Bool
  | .prop _ => true
  | .falsePLL => true
  | .and A B => orFree A && orFree B
  | .or _ _ => false
  | .ifThen A B => orFree A && orFree B
  | .somehow A => orFree A

end F0

#axioms_within F0.size [propext, Quot.sound]
#axioms_within F0.boxDepth [propext, Quot.sound]
#axioms_within F0.boxScope [propext, Quot.sound]
#axioms_within F0.weight [propext, Quot.sound]
#axioms_within F0.weightLt [propext, Quot.sound]
#axioms_within F0.synCmp [propext, Quot.sound]
#axioms_within F0.pickRep [propext, Quot.sound]
#axioms_within F0.orFree [propext, Quot.sound]
