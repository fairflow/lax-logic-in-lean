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

end Normal
end F0
end PLLND
