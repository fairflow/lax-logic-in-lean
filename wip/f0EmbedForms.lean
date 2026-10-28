import wip.f0FreePair
import Mathlib.Order.Heyting.Basic
import Meta.Audit

/-!
# Three forms of a copy of a Heyting algebra in F0

Matthew, 2026-10-28.  A framework for describing a copy of a Heyting algebra
`H` inside F0 by a map `e : H → F0`:

    (H) Heyting embedding into [b, ⊤]:  F0's ∧ ∨ ↠ preserved, ⊥ ↦ b, order reflected
    (L) lattice embedding:              F0's ∧ ∨ preserved, order reflected,
                                        → computed in the image
    (O) order embedding:                order preserved and reflected,
                                        all operations computed in the image

    (H) ⟹ (L) ⟹ (O);   (H) with bottom b ⟹ (O) with any bottom b' ≤ b (the shift).

`FreeHAnAbove b n` (`wip/f0FreeHAn.lean`) is (H): `relB b x` is a substitution,
so it preserves the operations by definition, and
`[A] ⊢ B ⟺ [relB b x A] ⊢ relB b x B` is preservation (⟹) plus order
reflection (⟸).

## Statements (committed before any proof, METHOD.md §1)

* `PairwiseHimp` (Lemma 1, abstract): for Heyting algebras `H`, `K` and
  `e : H → K` reflecting and preserving the order and preserving `⊓`,

      e (a ⇨ c) ≤ e a ⇨ e c,
      e a ⇨ e c = e (a ⇨ c)  ⟺  ∃ d, e d = e a ⇨ e c.

  So an (L)-copy whose image is closed under `↠` preserves `↠` at every pair:
  (L) and (H) agree pairwise.
* `Shift` (abstract): an order embedding `e` of a bounded-below partial order
  `H`, and `b' ≤ e ⊥`; then `x ↦ if x = ⊥ then b' else e x` is again an order
  embedding.
* `ShiftH2` (Lemma 2, the shift for `H₂` with bottom `⊥`), with
  `h = relB σ²⊥ xs` of `wip/f0FreePair.lean`: for ◯-free `A`, `B` in `p`, `pp`,

      (i)   [A] ⊬ ⊥ → [B] ⊬ ⊥ → ([A] ⊢ B ⟺ [h A] ⊢ h B)
      (ii)  [A] ⊬ ⊥ → [h A] ⊬ ⊥
      (iii) [⊥] ⊢ h B

  so sending the class of `⊥` to `⊥` and every other class `A` to `h A` is an
  order embedding of `H₂` into F0, stated without a decision procedure.
* `ShiftOrderEmb`: the same as one statement, over the relation
  `ShiftVal A φ := ([A] ⊢ ⊥ ∧ φ = ⊥) ∨ ([A] ⊬ ⊥ ∧ φ = h A)`:

      ShiftVal A φ → ShiftVal B ψ → ([A] ⊢ B ⟺ [φ] ⊢ ψ).

* `ShiftMeetFails`: the shift does not preserve `∧`: `[p ∧ ¬p] ⊢ ⊥`, `p` and
  `¬p` are not `⊥`, and `[h p ∧ h ¬p] ⊬ ⊥`.
-/

open PLLFormula

namespace PLLND
namespace F0
namespace EmbedForms

open SemUI FreeHAn Pair

/-! ## The abstract statements -/

/-- **Lemma 1 (the pairwise lemma)**: for `e : H → K` between Heyting algebras,
reflecting and preserving the order and preserving `⊓`,

    e (a ⇨ c) ≤ e a ⇨ e c,     e a ⇨ e c = e (a ⇨ c) ⟺ ∃ d, e d = e a ⇨ e c. -/
def PairwiseHimp : Prop :=
  ∀ (H K : Type) [HeytingAlgebra H] [HeytingAlgebra K] (e : H → K),
    (∀ x y, e x ≤ e y ↔ x ≤ y) → (∀ x y, e (x ⊓ y) = e x ⊓ e y) →
    ∀ a c : H, e (a ⇨ c) ≤ e a ⇨ e c ∧ (e a ⇨ e c = e (a ⇨ c) ↔ ∃ d, e d = e a ⇨ e c)

/-- **The shift**: an order embedding `e` with `b' ≤ e ⊥` stays an order
embedding when `⊥` is sent to `b'` instead:

    (∀ x y, e x ≤ e y ↔ x ≤ y) → b' ≤ e ⊥ →
      ∀ x y, e' x ≤ e' y ↔ x ≤ y,     e' x = if x = ⊥ then b' else e x. -/
def Shift : Prop :=
  ∀ (H K : Type) [PartialOrder H] [OrderBot H] [DecidableEq H] [Preorder K] (e : H → K),
    (∀ x y, e x ≤ e y ↔ x ≤ y) → ∀ b' : K, b' ≤ e (⊥ : H) →
    ∀ x y : H, ((if x = (⊥ : H) then b' else e x) ≤ (if y = (⊥ : H) then b' else e y) ↔ x ≤ y)

/-! ## The shift for `H₂` with bottom `⊥` -/

/-- **Lemma 2**: with `h = relB σ²⊥ xs`, for ◯-free `A`, `B` in `p`, `pp`,

    (i)   [A] ⊬ ⊥ → [B] ⊬ ⊥ → ([A] ⊢ B ⟺ [h A] ⊢ h B)
    (ii)  [A] ⊬ ⊥ → [h A] ⊬ ⊥
    (iii) [⊥] ⊢ h B. -/
def ShiftH2 : Prop :=
  ∀ A B : PLLFormula, boxFree A = true → boxFree B = true →
    varsBelow 2 A = true → varsBelow 2 B = true →
    (¬ Deriv [A] .falsePLL → ¬ Deriv [B] .falsePLL →
        (Deriv [A] B ↔ Deriv [relB b2 xs A] (relB b2 xs B))) ∧
    (¬ Deriv [A] .falsePLL → ¬ Deriv [relB b2 xs A] .falsePLL) ∧
    Deriv [.falsePLL] (relB b2 xs B)

/-- The value of the shifted map at `A`: `⊥` if `[A] ⊢ ⊥`, else `h A`. -/
def ShiftVal (A φ : PLLFormula) : Prop :=
  (Deriv [A] .falsePLL ∧ φ = .falsePLL) ∨ (¬ Deriv [A] .falsePLL ∧ φ = relB b2 xs A)

/-- **The shifted map is an order embedding of `H₂` into F0**:

    ShiftVal A φ → ShiftVal B ψ → ([A] ⊢ B ⟺ [φ] ⊢ ψ). -/
def ShiftOrderEmb : Prop :=
  ∀ A B φ ψ : PLLFormula, boxFree A = true → boxFree B = true →
    varsBelow 2 A = true → varsBelow 2 B = true →
    ShiftVal A φ → ShiftVal B ψ → (Deriv [A] B ↔ Deriv [φ] ψ)

/-- **The shift does not preserve `∧`**: `[p ∧ ¬p] ⊢ ⊥`, `[p] ⊬ ⊥`, `[¬p] ⊬ ⊥`,
and `[h p ∧ h ¬p] ⊬ ⊥`. -/
def ShiftMeetFails : Prop :=
  Deriv [pP.and (negF pP)] .falsePLL ∧ ¬ Deriv [pP] .falsePLL ∧
    ¬ Deriv [negF pP] .falsePLL ∧
    ¬ Deriv [(relB b2 xs pP).and (relB b2 xs (negF pP))] .falsePLL

end EmbedForms
end F0
end PLLND
