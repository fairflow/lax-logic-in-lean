/-
# The two constraint calculi meet in `Debt`

`PLLBridge.lean` reads `◯` as `Debt C` for a single fixed `C`, which collapses
iterated modalities and is therefore the easy half. The two real constraint
calculi in play let the constraint vary:

* **Mendler's** `(Ω*, [], @)` (PhD §3.2): a list of propositions, applied by
  iterated implication, `weak [γ₁,…,γₙ] φ = γ₁ ⊃ ⋯ ⊃ γₙ ⊃ φ`.
* **Fairtlough–Mendler's standard constraints** (`StdCtx` in
  `PLLCtxCompleteness.lean`, the Curry's-problem paper): a list of *pairs*,
  applied as a **conjunction over the list itself**:

      applyC [(K₁,L₁), …, (Kₙ,Lₙ)] x  =  ⋀ᵢ₌₁ⁿ (Kᵢ ⊃ (x ∨ Lᵢ))

  so the `C` on the left is exactly the list whose entries index the
  conjunction on the right. At `n = 0` it is the empty conjunction `⊤`, at
  `n = 1` a single clause, and only for `n > 1` is it a conjunction in the
  ordinary sense.

These are not the same construction, and the difference is not cosmetic: their
units sit at opposite ends. `weak [] φ = φ` is *no* weakening; `applyC [] x = ⊤`
is *total* weakening. Nor is the composition the same — Mendler appends demands
that must **all** hold, F&M conjoins clauses each of which is discharged by
**one** of the preconditions.

What this file shows is that both are `Debt` at a combination of the atomic
constraints, and it is the combination that differs:

    weak c φ                     ↔  Debt (allOf c) φ        -- conjunction
    applyC [(K₁,⊥),…,(Kₙ,⊥)] x   ↔  Debt (anyOf [K₁,…,Kₙ]) x -- disjunction

The two `[]` conventions then agree with the two ends of `Debt`: `allOf [] =
True` and `Debt True φ ≡ φ`, while `anyOf [] = False` and `Debt False x` is
vacuous, which is F&M's `⊤[x] ≡ true`. Their bottom `[(true,false)]` gives
`Debt True x ≡ x`. So the apparent clash of conventions is one interval seen
from its two ends.

This is what connects the obligation library to Theorem 6: PLL provability is
equivalent to IPL provability of `φ^C` for *every* standard constraint, and
every standard constraint of the `L = ⊥` fragment is a `Debt`.
-/

import LaxLogic.PLLCtxCompleteness
import LaxLogic.Obligation.PLLBridge

namespace LaxLogic.Obligation.StdCtxBridge

open PLLFormula PLLND PLLND.Ctx LaxLogic.Obligation LaxLogic.Obligation.PLLBridge

/-! ### Combining a list of propositions -/

/-- The conjunction of a list — how **Mendler's** demands combine. -/
def allOf : List Prop → Prop
  | [] => True
  | γ :: rest => γ ∧ allOf rest

/-- The disjunction of a list — how **F&M's** preconditions combine. -/
def anyOf : List Prop → Prop
  | [] => False
  | γ :: rest => γ ∨ anyOf rest

/-- **Mendler's constraint is `Debt` at the conjunction.** Iterated implication
curries into a single obligation. -/
theorem weak_iff_debt_allOf (c : List Prop) (φ : Prop) :
    weak c φ ↔ Debt (allOf c) φ := by
  induction c with
  | nil => exact ⟨fun h _ => h, fun h => h trivial⟩
  | cons γ rest ih =>
      constructor
      · rintro h ⟨hγ, hrest⟩; exact ih.mp (h hγ) hrest
      · intro h hγ; exact ih.mpr (fun hrest => h ⟨hγ, hrest⟩)

/-! ### F&M's standard constraints, at the level of propositions -/

/-- `basic K L x = K ⊃ (x ∨ L)`, as a proposition. -/
def basicP (K L x : Prop) : Prop := K → (x ∨ L)

/-- `applyC`, as a proposition: the conjunction of the clauses. -/
def applyP : List (Prop × Prop) → Prop → Prop
  | [], _ => True
  | (K, L) :: rest, x => basicP K L x ∧ applyP rest x

/-- **F&M's constraint, with every escape `⊥`, is `Debt` at the disjunction.**

A conjunction of clauses `Kᵢ ⊃ x` is discharged by any one of the `Kᵢ`, so the
obligation is their disjunction — where Mendler's is a conjunction. -/
theorem applyP_bot_iff (ks : List Prop) (x : Prop) :
    applyP (ks.map (fun K => (K, False))) x ↔ Debt (anyOf ks) x := by
  induction ks with
  | nil => exact ⟨fun _ h => h.elim, fun _ => trivial⟩
  | cons K rest ih =>
      constructor
      · rintro ⟨hK, hrest⟩ (h | h)
        · exact (hK h).elim id False.elim
        · exact ih.mp hrest h
      · intro h
        refine ⟨fun hK => Or.inl (h (Or.inl hK)), ih.mpr fun hr => h (Or.inr hr)⟩

/-! ### And the object-level `applyC` is `applyP` under the interpretation -/

/-- The `◯∀` interpretation takes F&M's `applyC` to `applyP`, clause by clause.
This is the step that makes the two previous theorems say something about the
repository's own `StdCtx` rather than about a look-alike. -/
theorem interp_applyC (Cc : Prop) (v : String → Prop) :
    ∀ (Cs : StdCtx) (x : PLLFormula),
      interp Cc v (applyC Cs x) ↔
        applyP (Cs.map (fun p => (interp Cc v p.1, interp Cc v p.2))) (interp Cc v x)
  | [], _ => ⟨fun _ => trivial, fun _ h => h.elim⟩
  | (K, L) :: rest, x => by
      constructor
      · rintro ⟨h₁, h₂⟩
        exact ⟨h₁, (interp_applyC Cc v rest x).mp h₂⟩
      · rintro ⟨h₁, h₂⟩
        exact ⟨h₁, (interp_applyC Cc v rest x).mpr h₂⟩

/-- **The connection, assembled.** A standard constraint whose escapes are all
`⊥` interprets as an obligation: the disjunction of its preconditions. -/
theorem interp_applyC_bot (Cc : Prop) (v : String → Prop)
    (Ks : List PLLFormula) (x : PLLFormula) :
    interp Cc v (applyC (Ks.map (fun K => (K, .falsePLL))) x) ↔
      Debt (anyOf (Ks.map (interp Cc v))) (interp Cc v x) := by
  have h := interp_applyC Cc v (Ks.map (fun K => (K, .falsePLL))) x
  have hlist :
      (Ks.map (fun K => ((K : PLLFormula), (PLLFormula.falsePLL)))).map
        (fun p => (interp Cc v p.1, interp Cc v p.2))
      = (Ks.map (interp Cc v)).map (fun K => (K, False)) := by
    simp [List.map_map, Function.comp_def, interp]
  rw [h, hlist]
  exact applyP_bot_iff _ _

/-! ### The two units, at the two ends of `Debt` -/

/-- F&M's top `⊤ = []`: `⊤[x] ≡ true`, which is `Debt False x` — vacuous. -/
theorem applyP_nil (x : Prop) : applyP [] x ↔ Debt False x :=
  ⟨fun _ h => h.elim, fun _ => trivial⟩

/-- F&M's bottom `⊥ = [(true,false)]`: `⊥[x] ≡ x`, which is `Debt True x`. -/
theorem applyP_bottom (x : Prop) : applyP [(True, False)] x ↔ Debt True x :=
  ⟨fun h _ => (h.1 trivial).elim id False.elim, fun h => ⟨fun _ => Or.inl (h trivial), trivial⟩⟩

/-- Mendler's unit `[]`: no weakening at all, `Debt True φ ≡ φ`. -/
theorem weak_nil_iff (φ : Prop) : weak [] φ ↔ Debt True φ :=
  ⟨fun h _ => h, fun h => h trivial⟩

end LaxLogic.Obligation.StdCtxBridge
