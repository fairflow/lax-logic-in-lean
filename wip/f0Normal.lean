import wip.f0T6
import LaxLogic.ClosedFragmentLattice
import LaxLogic.PLL.SubTab.Semantics
import Meta.Audit

/-!
# A filter of F0 that is not normal

F0 = `RNClass` is the Lindenbaum algebra of the variable-free PLL formulas,
ordered by entailment (`Le`: truth at every world of every constraint model).
`t n = rnSub n` are the substituted Rieger–Nishimura rungs and
`ρ k = rel (rn (2k+1))` the relativised odd rungs of `wip/f0T6.lean`
(`p ↦ u = ◯¬◯⊥`, `⊥ ↦ t3`).

A **filter** `F` of F0 is a nonempty, upward closed set closed under `⊓`.  It
is **normal** when it is the set of upper bounds of its lower bounds,

    F = Fˡᵘ := upperBounds (lowerBounds F)

(Mathlib: `Order.IsIntent (· ≤ ·) F`).  Every principal filter `↑a` is normal,
since `(↑a)ˡ = ↓a` and `(↓a)ᵘ = ↑a`.  A non-principal filter whose meet `m`
exists in F0 is never normal: `Fˡ = ↓m`, so `Fˡᵘ = ↑m ∋ m ∉ F`.

## The designed witness `F₇`

    d k := ρ k ↠ t7,          F₇ := ⋃_{k ≥ 2} ↑(d k) = { y | ∃ k, d (k+2) ≤ y }.

(a) `d (k+1) ≤ d k`                                   (`d_anti`)
(b) `¬ d k ≤ d (k+1)` for `k ≥ 2`                      (`d_not_le`, the model `M k`)
(c) `t7 ≤ d k`                                        (`t7_le_d`)
(d) `(∀ k, y ≤ d (k+2)) → y ≤ t7`                     (`le_t7_of_le_d`)
(e) `F₇` is a filter, non-principal, `IsGLB F₇ t7`, and so

    upperBounds (lowerBounds F₇) = ↑t7 ≠ F₇          (`F7_not_normal`, `notAllNormal`).

## (★) and the two joins

    (★)  in every finite subframe model every world forces some ρ k.

Induction on the number of proper successors of the world: if every proper
successor of `w` forces `ρ J` (one `J` for all of them, the rungs being
increasing) then `w ⊩ ρ (J+2) = ρ (J+1) ∨ (ρ (J+1) ↠ ρ J)`: either `w ⊩ ρ (J+1)`,
or every successor forcing `ρ (J+1)` is proper (persistence) and forces `ρ J`.
The same induction with `p ↦ ◯⊥` gives it for the odd rungs `t (2k+1)`.  Hence

    ⋁_k ρ k = ⊤   and   ⋁_k t (2k+1) = ⊤   in F0        (`supRho`, `supOddRungs`),

and (d): a lower bound `y` of the `d k` is `≤ t7`, since at a world forcing
`y` of a finite subframe model some `ρ k` holds, and `y ≤ d k` puts `t7` there;
`SubframeModel.CF.completeness_imp` (choice-free) turns this into `y ≤ t7`.
(★) fails in infinite models: a world above the whole `u`-ladder forces no
`ρ k`, hence every `d k` and not `t7`; the meet is reached only in the algebra.

## The countermodel `M k` for (b)

`T6.cmU` (the ladder `lad n` under the tops `nE`, `oE`, `fl`) with two new
worlds: `z ≤ oE, fl` and `x ≤ z, lad 0, …, lad (k−1), nE, oE, fl`, no new
modal edges.  Forcing at the old worlds is unchanged (`force_base`).  `z` is a
dead end of relative type 1 (`z ⊩ ρ 1`, `z ⊮ u`); `x` forces no `ρ j`, `j ≤ k`,
and forces `ρ (k+1)` when `k ≥ 2` (its proper successors in the relativised
model have types `0, …, k−1` and `1`); `x ⊩ d k`, `x ⊮ t7`.  So `[d k] ⊬ d (k+1)`.
At `k = 1` the same model FAILS (`x` has type 3, not 2): the gate watched in
`_out/f0Normal_gate.lean`.

Pins: `[propext, Quot.sound]` throughout.
-/

open PLLFormula

namespace PLLND
namespace F0
namespace Normal

open SemUI
open RNEmbed (rnP embed rnSub)
open PLLND.LaxInfinite (atomFree Le Closed closedSetoid)
open T6 (rel uF t6F cmU UW RiU RmU isTop)
open SubframeModel.CF (FinDec)

/-! ## The formulas -/

/-- `ρ k = rel (rn (2k+1))`, the relativised odd rungs (`wip/f0T6.lean`). -/
def ρF (k : Nat) : PLLFormula := rel (rnP k).1

/-- `t7 = t5 ∨ t6`. -/
def t7F : PLLFormula := rnSub 7

theorem t7F_eq : t7F = .or t5 t6F := rfl

/-- `d k = ρ k ↠ t7`. -/
def dF (k : Nat) : PLLFormula := .ifThen (ρF k) t7F

/-- The odd rungs `t (2k+1) = rn (2k+1) [p := ◯⊥]`. -/
def oddF (k : Nat) : PLLFormula := embed (rnP k).1

theorem oddF_eq (k : Nat) : oddF k = rnSub (2 * k + 1) := (rnSub_odd_embed k).symm

/-! ## Their classes in F0 -/

/-- The class of a variable-free formula. -/
def cls (φ : PLLFormula) (h : atomFree φ = true) : RNClass :=
  Quotient.mk closedSetoid (Closed.mk φ h)

theorem ρF_vf (k : Nat) : atomFree (ρF k) = true := T6.rel_vf _

theorem t7F_vf : atomFree t7F = true := rfl

theorem dF_vf (k : Nat) : atomFree (dF k) = true := by
  show (atomFree (ρF k) && atomFree t7F) = true
  rw [ρF_vf]
  rfl

theorem embed_rnP_vf : ∀ k, atomFree (embed (rnP k).1) = true ∧ atomFree (embed (rnP k).2) = true
  | 0 => ⟨rfl, rfl⟩
  | k + 1 => by
      obtain ⟨h1, h2⟩ := embed_rnP_vf k
      constructor
      · show (atomFree (embed (rnP k).1) && atomFree (embed (rnP k).2)) = true
        rw [h1, h2]
        rfl
      · show ((atomFree (embed (rnP k).1) && atomFree (embed (rnP k).2))
            && atomFree (embed (rnP k).1)) = true
        rw [h1, h2]
        rfl

theorem oddF_vf (k : Nat) : atomFree (oddF k) = true := (embed_rnP_vf k).1

/-- `ρ k ∈ F0`. -/
def ρ (k : Nat) : RNClass := cls (ρF k) (ρF_vf k)
/-- `t7 ∈ F0`. -/
def t7 : RNClass := cls t7F t7F_vf
/-- `d k = ρ k ↠ t7 ∈ F0`. -/
def d (k : Nat) : RNClass := cls (dF k) (dF_vf k)
/-- `t (2k+1) ∈ F0`. -/
def odd (k : Nat) : RNClass := cls (oddF k) (oddF_vf k)

/-- `F₇ = ⋃_{k ≥ 2} ↑(d k)`. -/
def F7 : Set RNClass := {y | ∃ k, d (k + 2) ≤ y}

/-! ## The statements -/

/-- A filter: nonempty, upward closed, closed under binary meets. -/
def IsFilter (F : Set RNClass) : Prop :=
  F.Nonempty ∧ (∀ x y, x ∈ F → x ≤ y → y ∈ F) ∧ (∀ x y, x ∈ F → y ∈ F → x ⊓ y ∈ F)

/-- A filter is **normal** when it is the set of upper bounds of its lower
bounds (`Order.IsIntent (· ≤ ·) F` in Mathlib). -/
def IsNormal (F : Set RNClass) : Prop := upperBounds (lowerBounds F) = F

/-- **F0 has a filter that is not normal.** -/
def NotAllNormal : Prop :=
  ∃ F : Set RNClass, IsFilter F ∧ upperBounds (lowerBounds F) ≠ F

/-- (★): in every finite subframe model every world forces some `ρ k`. -/
def Star : Prop :=
  ∀ (M : SubframeModel) [FinDec M] (w : M.W), ∃ k, M.force w (ρF k)

/-- (★) for the odd rungs `t (2k+1)`. -/
def StarOdd : Prop :=
  ∀ (M : SubframeModel) [FinDec M] (w : M.W), ∃ k, M.force w (oddF k)

/-- `⋁_k ρ k = ⊤` in F0. -/
def SupRho : Prop := IsLUB (Set.range ρ) ⊤

/-- `⋁_k t (2k+1) = ⊤` in F0. -/
def SupOddRungs : Prop := IsLUB (Set.range odd) ⊤

/-- (a) the `d k` descend. -/
def Descending : Prop := ∀ k, d (k + 1) ≤ d k

/-- (b) strictly, from `k = 2` on. -/
def StrictlyDescending : Prop := ∀ k, 2 ≤ k → ¬ d k ≤ d (k + 1)

/-- (c) `t7` is a lower bound. -/
def LowerBound : Prop := ∀ k, t7 ≤ d k

/-- (d) every common lower bound of the `d k` is below `t7`. -/
def GreatestLowerBound : Prop := ∀ y : RNClass, (∀ k, y ≤ d (k + 2)) → y ≤ t7

/-- `F₇` is a filter. -/
def F7IsFilter : Prop := IsFilter F7

/-- The meet of `F₇` is `t7`. -/
def F7Meet : Prop := IsGLB F7 t7

/-- `F₇` is not principal. -/
def F7NonPrincipal : Prop := ∀ m : RNClass, F7 ≠ Set.Ici m

/-- `F₇` is not normal. -/
def F7NotNormal : Prop := upperBounds (lowerBounds F7) ≠ F7

end Normal
end F0
end PLLND
