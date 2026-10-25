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



/-! ## Monotonicity of the rungs, in every constraint model -/

/-- `ρ j ≤ ρ (j+1)`: `ρ (j+1) = ρ j ∨ rel (rn (2j+2))`. -/
theorem force_ρF_succ (C : ConstraintModel) {w : C.W} {j : Nat} (h : C.force w (ρF j)) :
    C.force w (ρF (j + 1)) :=
  show C.force w (ρF j) ∨ C.force w (rel (rnP j).2) from Or.inl h

theorem force_ρF_mono (C : ConstraintModel) {w : C.W} {i j : Nat} (hij : i ≤ j)
    (h : C.force w (ρF i)) : C.force w (ρF j) := by
  induction hij with
  | refl => exact h
  | step _ ih => exact force_ρF_succ C ih

/-! ## The countermodel `M k`

`cmU` with two new worlds `z` and `x`:

    z ≤ z, oE, fl            x ≤ x, z, lad 0, …, lad (k−1), nE, oE, fl

and no new modal edges (`z ⇝ z`, `x ⇝ x`). -/

/-- Worlds: those of `cmU`, and two new worlds `z`, `x`. -/
inductive VW where
  | base (w : UW)
  | z
  | x

/-- `Rᵢ`: the old order on the old worlds; `z ≤ z, oE, fl`;
`x ≤ x, z, lad i (i < k), nE, oE, fl`. -/
def RiV (k : Nat) : VW → VW → Prop
  | .base w, .base v => RiU w v
  | .z, .z => True
  | .z, .base .oE => True
  | .z, .base .fl => True
  | .x, .x => True
  | .x, .z => True
  | .x, .base (.lad i) => i < k
  | .x, .base .nE => True
  | .x, .base .oE => True
  | .x, .base .fl => True
  | _, _ => False

/-- `Rₘ`: the old relation on the old worlds; `z ⇝ z`, `x ⇝ x`. -/
def RmV : VW → VW → Prop
  | .base w, .base v => RmU w v
  | .z, .z => True
  | .x, .x => True
  | _, _ => False

theorem riu_lad {i j : Nat} (h : RiU (.lad i) (.lad j)) : j = i ∨ j + 2 ≤ i := h

/-! ### Successors -/

theorem succ_z {k : Nat} : ∀ {b : VW}, RiV k .z b → b = .z ∨ b = .base .oE ∨ b = .base .fl := by
  intro b h
  rcases b with ⟨v⟩ | _ | _
  · cases v with
    | lad n => exact False.elim h
    | nE => exact False.elim h
    | oE => exact Or.inr (Or.inl rfl)
    | fl => exact Or.inr (Or.inr rfl)
  · exact Or.inl rfl
  · exact False.elim h

theorem succ_x {k : Nat} : ∀ {b : VW}, RiV k .x b →
    b = .x ∨ b = .z ∨ (∃ i, i < k ∧ b = .base (.lad i)) ∨ (∃ w, isTop w ∧ b = .base w) := by
  intro b h
  rcases b with ⟨v⟩ | _ | _
  · cases v with
    | lad i => exact Or.inr (Or.inr (Or.inl ⟨i, h, rfl⟩))
    | nE => exact Or.inr (Or.inr (Or.inr ⟨UW.nE, trivial, rfl⟩))
    | oE => exact Or.inr (Or.inr (Or.inr ⟨UW.oE, trivial, rfl⟩))
    | fl => exact Or.inr (Or.inr (Or.inr ⟨UW.fl, trivial, rfl⟩))
  · exact Or.inr (Or.inl rfl)
  · exact Or.inl rfl

theorem rm_z : ∀ {b : VW}, RmV .z b → b = .z := by
  intro b h
  rcases b with ⟨v⟩ | _ | _
  · exact False.elim h
  · rfl
  · exact False.elim h

theorem rm_x : ∀ {b : VW}, RmV .x b → b = .x := by
  intro b h
  rcases b with ⟨v⟩ | _ | _
  · exact False.elim h
  · exact False.elim h
  · rfl

/-- The only successor of `fl` is `fl`. -/
theorem flV_up {k : Nat} : ∀ {a b : VW}, RiV k a b → a = .base .fl → b = .base .fl := by
  intro a b h ha
  subst ha
  rcases b with ⟨v⟩ | _ | _
  · exact congrArg VW.base (T6.fl_up h rfl)
  · exact False.elim h
  · exact False.elim h

/-! ### The frame conditions -/

theorem RiV_refl (k : Nat) : ∀ a : VW, RiV k a a
  | .base w => T6.RiU_refl w
  | .z => trivial
  | .x => trivial

theorem RiV_trans {k : Nat} : ∀ {a b c : VW}, RiV k a b → RiV k b c → RiV k a c := by
  intro a b c h1 h2
  rcases a with ⟨w⟩ | _ | _
  · -- old worlds see only old worlds
    rcases b with ⟨v⟩ | _ | _
    · rcases c with ⟨u⟩ | _ | _
      · exact T6.RiU_trans h1 h2
      · exact False.elim h2
      · exact False.elim h2
    · exact False.elim h1
    · exact False.elim h1
  · -- z sees z, oE, fl
    rcases succ_z h1 with rfl | rfl | rfl
    · exact h2
    · rcases c with ⟨u⟩ | _ | _
      · cases u with
        | lad n => exact False.elim h2
        | nE => exact False.elim h2
        | oE => trivial
        | fl => trivial
      · exact False.elim h2
      · exact False.elim h2
    · have hc := flV_up h2 rfl
      subst hc
      trivial
  · -- x sees x, z, lad i (i < k), the tops
    rcases succ_x h1 with rfl | rfl | ⟨i, hi, rfl⟩ | ⟨v, hv, rfl⟩
    · exact h2
    · rcases succ_z h2 with rfl | rfl | rfl <;> trivial
    · rcases c with ⟨u⟩ | _ | _
      · cases u with
        | lad j =>
            have h2' := riu_lad h2
            show j < k
            omega
        | nE => trivial
        | oE => trivial
        | fl => trivial
      · exact False.elim h2
      · exact False.elim h2
    · rcases c with ⟨u⟩ | _ | _
      · have hu := T6.top_up hv h2
        cases u with
        | lad n => exact False.elim hu
        | nE => trivial
        | oE => trivial
        | fl => trivial
      · exact False.elim h2
      · exact False.elim h2

theorem RmV_refl : ∀ a : VW, RmV a a
  | .base w => T6.RmU_refl w
  | .z => trivial
  | .x => trivial

theorem RmV_trans : ∀ {a b c : VW}, RmV a b → RmV b c → RmV a c := by
  intro a b c h1 h2
  rcases a with ⟨w⟩ | _ | _ <;> rcases b with ⟨v⟩ | _ | _ <;> rcases c with ⟨u⟩ | _ | _ <;>
    first
    | exact trivial
    | exact T6.RmU_trans h1 h2
    | exact False.elim h1
    | exact False.elim h2

theorem RmV_sub {k : Nat} : ∀ {a b : VW}, RmV a b → RiV k a b := by
  intro a b h
  rcases a with ⟨w⟩ | _ | _ <;> rcases b with ⟨v⟩ | _ | _ <;>
    first
    | exact trivial
    | exact T6.RmU_sub h
    | exact False.elim h

/-- **The model** `M k`: `cmU` with `z` and `x`; `F = {fl}`. -/
@[reducible] def M (k : Nat) : ConstraintModel where
  W := VW
  Ri := RiV k
  Rm := RmV
  F := {a | a = .base .fl}
  V _ := {a | a = .base .fl}
  refl_i := RiV_refl k
  trans_i := RiV_trans
  refl_m := RmV_refl
  trans_m := RmV_trans
  sub_mi := RmV_sub
  hered_F := fun h ha => flV_up h ha
  hered_V := fun h ha => flV_up h ha
  full_F := fun ha => ha

/-! ### Forcing at the old worlds is unchanged -/

/-- The old worlds see only old worlds, along `Rᵢ` and along `Rₘ`, so forcing
there is as in `cmU`. -/
theorem force_base (k : Nat) :
    ∀ (φ : PLLFormula) (w : UW), (M k).force (.base w) φ ↔ cmU.force w φ := by
  intro φ
  induction φ with
  | prop a =>
      intro w
      exact ⟨fun h => VW.base.inj (show VW.base w = VW.base UW.fl from h),
        fun h => congrArg VW.base (show w = UW.fl from h)⟩
  | falsePLL =>
      intro w
      exact ⟨fun h => VW.base.inj (show VW.base w = VW.base UW.fl from h),
        fun h => congrArg VW.base (show w = UW.fl from h)⟩
  | and φ ψ ihφ ihψ => intro w; exact and_congr (ihφ w) (ihψ w)
  | or φ ψ ihφ ihψ => intro w; exact or_congr (ihφ w) (ihψ w)
  | ifThen φ ψ ihφ ihψ =>
      intro w
      constructor
      · intro h v hv hφ
        exact (ihψ v).mp (h (.base v) hv ((ihφ v).mpr hφ))
      · intro h b hb hφ
        rcases b with ⟨v⟩ | _ | _
        · exact (ihψ v).mpr (h v hb ((ihφ v).mp hφ))
        · exact False.elim hb
        · exact False.elim hb
  | somehow φ ih =>
      intro w
      constructor
      · intro h v hv
        obtain ⟨b, hb, hbφ⟩ := h (.base v) hv
        rcases b with ⟨u⟩ | _ | _
        · exact ⟨u, hb, (ih u).mp hbφ⟩
        · exact False.elim hb
        · exact False.elim hb
      · intro h b hb
        rcases b with ⟨v⟩ | _ | _
        · obtain ⟨u, hu, huφ⟩ := h v hb
          exact ⟨.base u, hu, (ih u).mpr huφ⟩
        · exact False.elim hb
        · exact False.elim hb

theorem force_e_oE {k : Nat} : (M k).force (.base .oE) e :=
  (force_base k e _).mpr ((T6.force_e _).mpr (Or.inl rfl))

theorem force_t3_top {k : Nat} {w : UW} (hw : isTop w) : (M k).force (.base w) t3 :=
  (force_base k t3 w).mpr ((T6.force_t3 w).mpr hw)

/-- `t7` holds at every old world (`t6` does, `T6.force_t6`). -/
theorem force_t7_base {k : Nat} (w : UW) : (M k).force (.base w) t7F :=
  (force_base k t7F w).mpr (show cmU.force w (.or t5 t6F) from Or.inr (T6.force_t6 w))

/-! ### The new world `z`: relative type 1, `t4`, `t7`, not `t3`, not `u` -/

theorem not_force_e_z {k : Nat} : ¬ (M k).force .z e := fun h => by
  obtain ⟨b, hb, hbF⟩ := h .z trivial
  have hbz := rm_z hb
  subst hbz
  exact VW.noConfusion (show VW.z = VW.base UW.fl from hbF)

theorem not_force_ne_z {k : Nat} : ¬ (M k).force .z ne := fun h => by
  have h' : VW.base UW.oE = VW.base UW.fl := h (.base .oE) trivial force_e_oE
  cases VW.base.inj h'

theorem not_force_t3_z {k : Nat} : ¬ (M k).force .z t3 := fun h =>
  (show (M k).force .z e ∨ (M k).force .z ne from h).elim not_force_e_z not_force_ne_z

theorem force_t4_z {k : Nat} : (M k).force .z t4 := by
  intro b hb h3
  rcases succ_z hb with rfl | rfl | rfl
  · exact absurd h3 not_force_t3_z
  · exact force_e_oE
  · exact (M k).force_of_fallible rfl

theorem force_t5_z {k : Nat} : (M k).force .z t5 :=
  show (M k).force .z t3 ∨ (M k).force .z t4 from Or.inr force_t4_z

theorem force_t7_z {k : Nat} : (M k).force .z t7F :=
  show (M k).force .z t5 ∨ (M k).force .z t6F from Or.inl force_t5_z

theorem not_force_u_z {k : Nat} : ¬ (M k).force .z uF := fun h => by
  obtain ⟨b, hb, hbn⟩ := h .z trivial
  have hbz := rm_z hb
  subst hbz
  exact not_force_ne_z hbn

/-- `z ⊩ ρ 1 = u ∨ (u ↠ t3)`: the successors of `z` forcing `u` are the tops. -/
theorem force_ρ1_z {k : Nat} : (M k).force .z (ρF 1) := by
  show (M k).force .z uF ∨ (M k).force .z (.ifThen uF t3)
  refine Or.inr (fun b hb hu => ?_)
  rcases succ_z hb with rfl | rfl | rfl
  · exact absurd hu not_force_u_z
  · exact force_t3_top trivial
  · exact (M k).force_of_fallible rfl

theorem force_ρ_z {k j : Nat} (hj : 1 ≤ j) : (M k).force .z (ρF j) :=
  force_ρF_mono _ hj force_ρ1_z

/-! ### The new world `x`: forces `d k`, not `t7`, no `ρ j` with `j ≤ k` -/

theorem not_force_e_x {k : Nat} : ¬ (M k).force .x e := fun h => by
  obtain ⟨b, hb, hbF⟩ := h .x trivial
  have hbx := rm_x hb
  subst hbx
  exact VW.noConfusion (show VW.x = VW.base UW.fl from hbF)

theorem not_force_ne_x {k : Nat} : ¬ (M k).force .x ne := fun h => by
  have h' : VW.base UW.oE = VW.base UW.fl := h (.base .oE) trivial force_e_oE
  cases VW.base.inj h'

theorem not_force_t3_x {k : Nat} : ¬ (M k).force .x t3 := fun h =>
  (show (M k).force .x e ∨ (M k).force .x ne from h).elim not_force_e_x not_force_ne_x

/-- `x ⊮ t4`: `x` sees `nE`, where `t3` holds and `◯⊥` fails. -/
theorem not_force_t4_x {k : Nat} : ¬ (M k).force .x t4 := fun h => by
  have h' := (force_base k e _).mp (h (.base .nE) trivial (force_t3_top trivial))
  rcases (T6.force_e _).mp h' with h'' | h'' <;> cases h''

theorem not_force_t5_x {k : Nat} : ¬ (M k).force .x t5 := fun h =>
  (show (M k).force .x t3 ∨ (M k).force .x t4 from h).elim not_force_t3_x not_force_t4_x

/-- `x ⊮ t6`: `x` sees `z`, where `t5` holds and `t3` fails. -/
theorem not_force_t6_x {k : Nat} : ¬ (M k).force .x t6F := fun h =>
  not_force_t3_z (h .z trivial force_t5_z)

theorem not_force_t7_x {k : Nat} : ¬ (M k).force .x t7F := fun h =>
  (show (M k).force .x t5 ∨ (M k).force .x t6F from h).elim not_force_t5_x not_force_t6_x

theorem not_force_u_x {k : Nat} : ¬ (M k).force .x uF := fun h => by
  obtain ⟨b, hb, hbn⟩ := h .x trivial
  have hbx := rm_x hb
  subst hbx
  exact not_force_ne_x hbn

/-- `lad j ⊮ rel (rn (2j+2))`: the ladder world of type `j` forces `ρ j` and
not its consequent (`t3` for `j = 0`, `ρ (j−1)` for `j ≥ 1`). -/
theorem lad_not_rnP2 (j : Nat) : ¬ cmU.force (.lad j) (rel (rnP j).2) := by
  cases j with
  | zero =>
      intro h
      exact (T6.force_t3 (UW.lad 0)).mp
        (h (UW.lad 0) (T6.RiU_refl (UW.lad 0)) ((T6.force_u_lad 0).mpr rfl))
  | succ j =>
      intro h
      have h1 := h (UW.lad (j + 1)) (T6.RiU_refl (UW.lad (j + 1)))
        ((T6.rel_odd (j + 1) (j + 1)).mpr (Nat.le_refl _))
      have h2 := (T6.rel_odd j (j + 1)).mp h1
      omega

/-- `x ⊮ ρ j` for `j ≤ k`: `x` sees `lad j`. -/
theorem not_force_ρ_x {k : Nat} : ∀ {j : Nat}, j ≤ k → ¬ (M k).force .x (ρF j) := by
  intro j
  induction j with
  | zero => exact fun _ => not_force_u_x
  | succ j ih =>
      intro hj h
      rcases (show (M k).force .x (ρF j) ∨ (M k).force .x (rel (rnP j).2) from h) with h | h
      · exact ih (Nat.le_of_succ_le hj) h
      · exact lad_not_rnP2 j ((force_base k _ _).mp
          ((M k).force_hered (show RiV k .x (.base (.lad j)) from hj) h))

/-- `x ⊩ d k = ρ k ↠ t7`: the successors of `x` forcing `ρ k` are `z` and old
worlds, where `t7` holds. -/
theorem force_d_x {k : Nat} : (M k).force .x (dF k) := by
  intro b hb hρ
  rcases succ_x hb with rfl | rfl | ⟨i, _, rfl⟩ | ⟨w, _, rfl⟩
  · exact absurd hρ (not_force_ρ_x (Nat.le_refl k))
  · exact force_t7_z
  · exact force_t7_base _
  · exact force_t7_base _


/-! ### The type of `x` is `k+1` when `k ≥ 2` -/

/-- `x ⊩ ρ (k+1)` for `k ≥ 2`: `ρ (k+1) = ρ k ∨ (ρ k ↠ ρ (k−1))`, and every
successor of `x` forcing `ρ k` (`z`, the `lad i` with `i < k`, the tops) forces
`ρ (k−1)`; `z` does because `k − 1 ≥ 1`.  (At `k = 1` this FAILS at `z`:
`_out/f0Normal_gate.lean`.) -/
theorem force_ρ_succ_x {k : Nat} (hk : 2 ≤ k) : (M k).force .x (ρF (k + 1)) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  show (M (k' + 1)).force .x (ρF (k' + 1)) ∨
    (M (k' + 1)).force .x (.ifThen (ρF (k' + 1)) (ρF k'))
  refine Or.inr (fun b hb hρ => ?_)
  rcases succ_x hb with rfl | rfl | ⟨i, hi, rfl⟩ | ⟨w, hw, rfl⟩
  · exact absurd hρ (not_force_ρ_x (Nat.le_refl _))
  · exact force_ρ_z (by omega)
  · exact (force_base _ _ _).mpr ((T6.rel_odd k' i).mpr (by omega))
  · exact (force_base _ _ _).mpr ((T6.rel_transfer (RNEmbed.rnP_boxFree k').1).2 w hw)

theorem not_force_d_succ_x {k : Nat} (hk : 2 ≤ k) : ¬ (M k).force .x (dF (k + 1)) := fun h =>
  not_force_t7_x (h .x trivial (force_ρ_succ_x hk))

/-! ## (a), (b), (c): the chain `d k` in F0 -/

/-- (a) `d (k+1) ≤ d k`: `↠` is antitone in its antecedent and `ρ k ≤ ρ (k+1)`. -/
theorem d_anti (k : Nat) : d (k + 1) ≤ d k := by
  show Le (dF (k + 1)) (dF k)
  intro C w h v hv hρ
  exact h v hv (force_ρF_succ C hρ)

theorem d_le_of_le {i j : Nat} (hij : i ≤ j) : d j ≤ d i := by
  induction hij with
  | refl => exact le_refl _
  | step _ ih => exact le_trans (d_anti _) ih

/-- (c) `t7 ≤ d k`: `b ≤ a ↠ b`. -/
theorem t7_le_d (k : Nat) : t7 ≤ d k := by
  show Le t7F (dF k)
  intro C w h v hv _
  exact C.force_hered hv h

/-- (b) `¬ d k ≤ d (k+1)` for `k ≥ 2`: the world `x` of `M k` forces `d k` and
not `d (k+1)`. -/
theorem d_not_le {k : Nat} (hk : 2 ≤ k) : ¬ d k ≤ d (k + 1) := fun h =>
  not_force_d_succ_x hk (h (M k) .x force_d_x)

/-! ## (★): every world of a finite subframe model forces some rung

By descent on the number of proper successors: if every proper successor of
`w` forces `σ J` then `w ⊩ σ (J+2) = σ (J+1) ∨ (σ (J+1) ↠ σ J)`, since a
successor forcing `σ (J+1)` is proper (else `w` would force it, by persistence)
and so forces `σ J`.  Stated for any sequence with the Rieger–Nishimura
recursion `σ (j+1) = σ j ∨ τ j`, `τ (j+1) = σ (j+1) ↠ σ j`. -/

theorem sforce_or_inl (M : SubframeModel) {w : M.W} {φ ψ : PLLFormula} (h : M.force w φ) :
    M.force w (φ.or ψ) :=
  show M.force w φ ∨ M.force w ψ from Or.inl h

section Star

open SubframeModel.CF

variable (M : SubframeModel) [FinDec M]

/-- The number of proper successors of `w`. -/
def nProper (w : M.W) : Nat :=
  (FinDec.elems (M := M)).countP (fun v => decide (M.le w v ∧ ¬ M.le v w))

theorem nProper_lt {w v : M.W} (h1 : M.le w v) (h2 : ¬ M.le v w) :
    nProper M v < nProper M w :=
  FRJ.countP_lt_countP
    (fun u _ hu => by
      have hu' := of_decide_eq_true hu
      exact decide_eq_true ⟨M.trans h1 hu'.1, fun h => hu'.2 (M.trans h h1)⟩)
    (FinDec.complete v) (decide_eq_true ⟨h1, h2⟩)
    (decide_eq_false (fun h => h.2 (M.refl v)))

/-- One index bounding the rungs forced at all proper successors in a list. -/
theorem bound_list (σ : Nat → PLLFormula)
    (hmono : ∀ {i j : Nat} {v : M.W}, i ≤ j → M.force v (σ i) → M.force v (σ j))
    (w : M.W) :
    ∀ L : List M.W, (∀ v ∈ L, M.le w v → ¬ M.le v w → ∃ k, M.force v (σ k)) →
      ∃ J, ∀ v ∈ L, M.le w v → ¬ M.le v w → M.force v (σ J)
  | [], _ => ⟨0, fun v hv => absurd hv List.not_mem_nil⟩
  | v :: L, h => by
      obtain ⟨J, hJ⟩ := bound_list σ hmono w L (fun u hu => h u (List.mem_cons_of_mem v hu))
      rcases Decidable.em (M.le w v ∧ ¬ M.le v w) with hv | hv
      · obtain ⟨k, hk⟩ := h v (List.mem_cons_self ..) hv.1 hv.2
        refine ⟨max J k, fun u hu h1 h2 => ?_⟩
        rcases List.mem_cons.mp hu with rfl | hu
        · exact hmono (Nat.le_max_right J k) hk
        · exact hmono (Nat.le_max_left J k) (hJ u hu h1 h2)
      · refine ⟨J, fun u hu h1 h2 => ?_⟩
        rcases List.mem_cons.mp hu with rfl | hu
        · exact absurd ⟨h1, h2⟩ hv
        · exact hJ u hu h1 h2

/-- The step: from `σ J` at every proper successor to `σ (J+2)` at `w`. -/
theorem step_two (σ τ : Nat → PLLFormula)
    (hσ : ∀ j, σ (j + 1) = (σ j).or (τ j))
    (hτ : ∀ j, τ (j + 1) = (σ (j + 1)).ifThen (σ j))
    (w : M.W) (J : Nat) (hJ : ∀ v, M.le w v → ¬ M.le v w → M.force v (σ J)) :
    M.force w (σ (J + 1 + 1)) := by
  rw [hσ (J + 1), hτ J]
  show M.force w (σ (J + 1)) ∨ M.force w ((σ (J + 1)).ifThen (σ J))
  rcases Decidable.em (M.force w (σ (J + 1))) with h | h
  · exact Or.inl h
  · refine Or.inr (fun v hwv hv => ?_)
    rcases Decidable.em (M.le v w) with hvw | hvw
    · exact absurd (SubframeModel.force_mono M _ hvw hv) h
    · exact hJ v hwv hvw

theorem exists_force_aux (σ τ : Nat → PLLFormula)
    (hσ : ∀ j, σ (j + 1) = (σ j).or (τ j))
    (hτ : ∀ j, τ (j + 1) = (σ (j + 1)).ifThen (σ j)) :
    ∀ (n : Nat) (w : M.W), nProper M w ≤ n → ∃ k, M.force w (σ k) := by
  have hmono : ∀ {i j : Nat} {v : M.W}, i ≤ j → M.force v (σ i) → M.force v (σ j) := by
    intro i j v hij h
    induction hij with
    | refl => exact h
    | step _ ih =>
        rw [hσ]
        exact sforce_or_inl M ih
  intro n
  induction n with
  | zero =>
      intro w hw
      refine ⟨0 + 1 + 1, step_two M σ τ hσ hτ w 0 (fun v h1 h2 => ?_)⟩
      exact absurd (Nat.lt_of_lt_of_le (nProper_lt M h1 h2) hw) (Nat.not_lt_zero _)
  | succ n ih =>
      intro w hw
      obtain ⟨J, hJ⟩ := bound_list M σ hmono w (FinDec.elems (M := M)) (fun v _ h1 h2 =>
        ih v (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (nProper_lt M h1 h2) hw)))
      exact ⟨J + 1 + 1, step_two M σ τ hσ hτ w J (fun v h1 h2 => hJ v (FinDec.complete v) h1 h2)⟩

/-- **(★), generically.** -/
theorem exists_force_chain (σ τ : Nat → PLLFormula)
    (hσ : ∀ j, σ (j + 1) = (σ j).or (τ j))
    (hτ : ∀ j, τ (j + 1) = (σ (j + 1)).ifThen (σ j)) (w : M.W) :
    ∃ k, M.force w (σ k) :=
  exists_force_aux M σ τ hσ hτ _ w (Nat.le_refl _)

end Star

/-- **(★)**: every world of every finite subframe model forces some `ρ k`. -/
theorem star : Star := fun M _ w =>
  exists_force_chain M ρF (fun k => rel (rnP k).2) (fun _ => rfl) (fun _ => rfl) w

/-- (★) for the odd rungs `t (2k+1)`. -/
theorem starOdd : StarOdd := fun M _ w =>
  exists_force_chain M oddF (fun k => embed (rnP k).2) (fun _ => rfl) (fun _ => rfl) w

/-! ## From constraint models to finite subframe models, without choice -/

section Transfer

open SubframeModel.CF

/-- `SubframeModel.toConstraint_force` for a `FinDec` model: its one case
split, on membership in `S`, is decidable there, so no choice enters. -/
theorem toConstraint_force_fd (M : SubframeModel) [FinDec M] :
    ∀ (φ : PLLFormula) (x : M.W),
      ((SubframeModel.toConstraint M).force (some x) φ ↔ M.force x φ) := by
  intro φ
  induction φ with
  | prop a => intro x; exact Iff.rfl
  | falsePLL =>
      intro x
      constructor
      · intro h
        cases (show (some x : Option M.W) = none from h)
      · intro h
        exact h.elim
  | and φ ψ ihφ ihψ => intro x; exact and_congr (ihφ x) (ihψ x)
  | or φ ψ ihφ ihψ => intro x; exact or_congr (ihφ x) (ihψ x)
  | ifThen φ ψ ihφ ihψ =>
      intro x
      constructor
      · intro h v hxv hφ
        exact (ihψ v).mp (h (some v) hxv ((ihφ v).mpr hφ))
      · intro h b hxb hφ
        cases b with
        | none => exact (SubframeModel.toConstraint M).force_of_fallible rfl
        | some v => exact (ihψ v).mpr (h v hxb ((ihφ v).mp hφ))
  | somehow φ ih =>
      intro x
      constructor
      · intro h v hxv hvS
        obtain ⟨u, hvu, hu⟩ := h (some v) hxv
        cases u with
        | none => exact absurd hvS hvu
        | some u' =>
            have hvu' : v = u' := hvu
            subst hvu'
            exact (ih v).mp hu
      · intro h b hxb
        cases b with
        | none => exact ⟨none, trivial, (SubframeModel.toConstraint M).force_of_fallible rfl⟩
        | some v =>
            rcases Decidable.em (v ∈ M.S) with hvS | hvS
            · exact ⟨some v, rfl, (ih v).mpr (h v hxb hvS)⟩
            · exact ⟨none, hvS, (SubframeModel.toConstraint M).force_of_fallible rfl⟩

end Transfer

/-- `ρ j ≤ ρ (j+1)` in a subframe model. -/
theorem sforce_ρF_succ (M : SubframeModel) {x : M.W} {j : Nat} (h : M.force x (ρF j)) :
    M.force x (ρF (j + 1)) :=
  sforce_or_inl M h

/-! ## (d): the greatest lower bound, through the choice-free completeness -/

/-- (d) A common lower bound `y` of the `d (k+2)` is `≤ t7`.  At a world of a
finite subframe model forcing `y` some `ρ k` holds (★), hence `ρ (k+2)`, and
`y ≤ d (k+2)` puts `t7` there; `completeness_imp` and `soundness` close. -/
theorem le_t7_of_le_d : GreatestLowerBound := by
  intro y
  induction y using Quotient.ind
  rename_i a
  intro hy
  show Le a.1 t7F
  have hnd : Nonempty (LaxND [] (a.1 ↠ t7F)) :=
    SubframeModel.CF.completeness_imp (fun M _ x hx => by
      obtain ⟨k, hk⟩ := star M x
      have hk2 : M.force x (ρF (k + 2)) := sforce_ρF_succ M (sforce_ρF_succ M hk)
      have hd : M.force x (dF (k + 2)) :=
        (toConstraint_force_fd M _ x).mp
          (hy k (SubframeModel.toConstraint M) (some x) ((toConstraint_force_fd M _ x).mpr hx))
      exact hd x (M.refl x) hk2)
  obtain ⟨p⟩ := hnd
  intro C w hw
  exact PLLND.soundness p C w (fun _ hχ => absurd hχ List.not_mem_nil) w (C.refl_i w) hw

/-! ## The two joins -/

/-- `⋁_k ρ k = ⊤`: an upper bound of all `ρ k` holds at every world of every
finite subframe model, by (★). -/
theorem supRho : SupRho := by
  refine ⟨fun y _ => le_top, fun y hy => ?_⟩
  induction y using Quotient.ind
  rename_i a
  show Le (.ifThen .falsePLL .falsePLL) a.1
  have hnd : Nonempty (LaxND [] a.1) :=
    SubframeModel.CF.completeness (fun M _ x => by
      obtain ⟨k, hk⟩ := star M x
      exact (toConstraint_force_fd M _ x).mp
        (hy (Set.mem_range_self k) (SubframeModel.toConstraint M) (some x)
          ((toConstraint_force_fd M _ x).mpr hk)))
  obtain ⟨p⟩ := hnd
  intro C w _
  exact PLLND.soundness p C w (fun _ hχ => absurd hχ List.not_mem_nil)

/-- `⋁_k t (2k+1) = ⊤`. -/
theorem supOddRungs : SupOddRungs := by
  refine ⟨fun y _ => le_top, fun y hy => ?_⟩
  induction y using Quotient.ind
  rename_i a
  show Le (.ifThen .falsePLL .falsePLL) a.1
  have hnd : Nonempty (LaxND [] a.1) :=
    SubframeModel.CF.completeness (fun M _ x => by
      obtain ⟨k, hk⟩ := starOdd M x
      exact (toConstraint_force_fd M _ x).mp
        (hy (Set.mem_range_self k) (SubframeModel.toConstraint M) (some x)
          ((toConstraint_force_fd M _ x).mpr hk)))
  obtain ⟨p⟩ := hnd
  intro C w _
  exact PLLND.soundness p C w (fun _ hχ => absurd hχ List.not_mem_nil)

/-! ## (e): `F₇` -/

theorem d_mem_F7 (k : Nat) : d (k + 2) ∈ F7 := ⟨k, le_refl _⟩

/-- `F₇` is a filter: the union of the chain of principal filters `↑(d (k+2))`. -/
theorem F7_isFilter : F7IsFilter := by
  refine ⟨⟨d 2, d_mem_F7 0⟩, fun x y ⟨k, hk⟩ hxy => ⟨k, le_trans hk hxy⟩, ?_⟩
  rintro x y ⟨k₁, h₁⟩ ⟨k₂, h₂⟩
  refine ⟨max k₁ k₂, le_inf ?_ ?_⟩
  · exact le_trans (d_le_of_le (Nat.add_le_add_right (Nat.le_max_left k₁ k₂) 2)) h₁
  · exact le_trans (d_le_of_le (Nat.add_le_add_right (Nat.le_max_right k₁ k₂) 2)) h₂

theorem t7_mem_lowerBounds_F7 : t7 ∈ lowerBounds F7 :=
  fun _ ⟨_, hk⟩ => le_trans (t7_le_d _) hk

/-- `F₇ˡ = ↓t7`. -/
theorem lowerBounds_F7 : lowerBounds F7 = Set.Iic t7 := by
  ext y
  constructor
  · intro hy
    exact le_t7_of_le_d y (fun k => hy (d_mem_F7 k))
  · intro hy z hz
    obtain ⟨k, hk⟩ := hz
    exact le_trans hy (le_trans (t7_le_d _) hk)

/-- The meet of `F₇` is `t7`. -/
theorem F7_meet : F7Meet :=
  ⟨t7_mem_lowerBounds_F7, fun y hy => le_t7_of_le_d y (fun k => hy (d_mem_F7 k))⟩

/-- `t7 ∉ F₇`: else `d (k+2) ≤ t7 ≤ d (k+3)`, against (b). -/
theorem t7_not_mem_F7 : t7 ∉ F7 := fun ⟨k, hk⟩ =>
  d_not_le (k := k + 2) (by omega) (le_trans hk (t7_le_d (k + 3)))

/-- `F₇` is a proper filter. -/
theorem bot_not_mem_F7 : (⊥ : RNClass) ∉ F7 := fun h =>
  t7_not_mem_F7 (F7_isFilter.2.1 _ _ h bot_le)

/-- `F₇ˡᵘ = ↑t7`. -/
theorem upperBounds_lowerBounds_F7 : upperBounds (lowerBounds F7) = Set.Ici t7 := by
  rw [lowerBounds_F7]
  ext y
  constructor
  · intro hy
    exact hy (Set.mem_Iic.mpr (le_refl t7))
  · intro hy z hz
    exact le_trans (Set.mem_Iic.mp hz) hy

/-- **`F₇` is not normal**: `t7 ∈ F₇ˡᵘ`, `t7 ∉ F₇`. -/
theorem F7_not_normal : F7NotNormal := by
  intro h
  have ht : t7 ∈ F7 := by
    rw [← h, upperBounds_lowerBounds_F7]
    exact Set.self_mem_Ici
  exact t7_not_mem_F7 ht

/-- `F₇` is not principal: a least element would be some `d (k+2)`, but
`d (k+3) ∈ F₇` lies strictly below it. -/
theorem F7_nonPrincipal : F7NonPrincipal := by
  intro m hm
  have hm_mem : m ∈ F7 := by
    rw [hm]
    exact Set.self_mem_Ici
  obtain ⟨k, hk⟩ := hm_mem
  have h3 : d (k + 3) ∈ F7 := d_mem_F7 (k + 1)
  rw [hm] at h3
  exact d_not_le (k := k + 2) (by omega) (le_trans hk h3)

/-! ## The theorems, under their statement names -/

/-- **F0 has a filter that is not normal.** -/
theorem notAllNormal : NotAllNormal := ⟨F7, F7_isFilter, F7_not_normal⟩

theorem descending : Descending := d_anti
theorem strictlyDescending : StrictlyDescending := fun _ hk => d_not_le hk
theorem lowerBound : LowerBound := t7_le_d
theorem greatestLowerBound : GreatestLowerBound := le_t7_of_le_d

end Normal
end F0
end PLLND

/-! ## Axiom pins -/

#axioms_within PLLND.F0.Normal.force_d_x [propext, Quot.sound]
#axioms_within PLLND.F0.Normal.force_ρ_succ_x [propext, Quot.sound]
#axioms_within PLLND.F0.Normal.star [propext, Quot.sound]
#axioms_within PLLND.F0.Normal.starOdd [propext, Quot.sound]
#axioms_within PLLND.F0.Normal.toConstraint_force_fd [propext, Quot.sound]
#axioms_within PLLND.F0.Normal.supRho [propext, Quot.sound]
#axioms_within PLLND.F0.Normal.supOddRungs [propext, Quot.sound]
#axioms_within PLLND.F0.Normal.descending [propext, Quot.sound]
#axioms_within PLLND.F0.Normal.strictlyDescending [propext, Quot.sound]
#axioms_within PLLND.F0.Normal.lowerBound [propext, Quot.sound]
#axioms_within PLLND.F0.Normal.greatestLowerBound [propext, Quot.sound]
#axioms_within PLLND.F0.Normal.F7_isFilter [propext, Quot.sound]
#axioms_within PLLND.F0.Normal.F7_meet [propext, Quot.sound]
#axioms_within PLLND.F0.Normal.F7_nonPrincipal [propext, Quot.sound]
#axioms_within PLLND.F0.Normal.bot_not_mem_F7 [propext, Quot.sound]
#axioms_within PLLND.F0.Normal.F7_not_normal [propext, Quot.sound]
#axioms_within PLLND.F0.Normal.notAllNormal [propext, Quot.sound]
