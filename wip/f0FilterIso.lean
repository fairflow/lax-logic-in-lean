import wip.f0NotIso
import wip.f0Nuclear
import Meta.Audit

/-!
# Is a proper filter of F0 order-isomorphic to F0?

Paper III, open question 1.  The question, as a proposition (`FilterIsoQ`):

    ∀ p : RNClass,  p ≠ ⊥  →  ¬ Nonempty (Set.Ici p ≃o RNClass)

## The reduction to the dense filters (PROVED)

`F0 = {⊥, t1, t2, t4} ∪ ↑t3` (`classify_low`, from `low_trichotomy` and the
tables `D3`, `D4` of `wip/f0Covers.lean`).  The three non-dense `p ≠ ⊥` are
refuted, each by its own order invariant:

* `p = t2 = ¬◯⊥` and `p = t4`: `[t2, ⊤] = {t2} ∪ ↑t3` and `[t4, ⊤] = {t4} ∪ ↑t5`
  have no disjoint pair; F0 has one, `(t1, t2)` (`HasDisjPair`).
* `p = t1 = ◯⊥`: F0 has exactly one *big atom* (an atom `a` with
  `F0 = {⊥, d} ∪ ↑a` for some `d`), namely `t1` (`bigAtom_rn`); in `[t1, ⊤]`
  the element `t3` is one (`[t1, ⊤] = {t1, t4} ∪ ↑t3`).  An isomorphism
  `[t1, ⊤] ≅ F0` therefore sends `t3` to `t1` and restricts to
  `[t3, ⊤] ≅ [t1, ⊤] ≅ F0`, against `NotIso.t3_filter_not_iso`.

  In the ◯-free instance (the Rieger–Nishimura lattice, `◯⊥` read as the
  generator `p`) the corresponding filter IS isomorphic to the whole lattice,
  by the shift `tₙ ↦ tₙ₊₂` (pen); the descent breaks at `t3` because `◯t3 ≠ t3`
  creates the second disjoint pair `(◯t3, ◯t3 ↠ t3)` above `t3`.

So the question is equivalent to its dense residue (`filterIsoQ_iff_dense`):

    ∀ p : RNClass,  t3 ≤ p  →  ¬ Nonempty (Set.Ici p ≃o RNClass)

## The σ-bases (PROVED)

`σⁿ(t3) = σⁿ⁺¹(⊥)`, the bases of the nested copies of `wip/f0SelfSim.lean`:
`[σⁿ(t3), ⊤]` has the two disjoint pairs `σⁿ(c1, g1)`, `σⁿ(t5, t6)`
(`sigN_filter_not_iso`).  `σ` preserves `∧` and derivability; it reflects
refutation on constraint models with decidable fallibility (`refutes_sig`:
add the tops `nT`, `eT`, and a fallible `fT` above `eT`), so the eight
countermodels of `wip/f0NotIso.lean` serve every `n`; no completeness theorem.

## A dense cell off the σ-bases (PROVED)

`p = c1 = ◯t3 = σ(t1)`, `◯`-fixed like `t1`: `[c1, ⊤]` has three pairwise
disjoint elements (`c1_filter_not_iso`).

## What remains (OPEN)

`DenseResidue` for the other dense `p`.  The proposed next statement is
`ObstructionA` (§8, a `Prop`, not proved here): if `d` covers `p` and is
meet-prime, then `◯d ⊢ d` or `◯(d ↠ p) ⊢ d ↠ p`.

Pins: `[propext, Quot.sound]` for the cells and the reduction; tighter where
the declaration needs less (each pin watched failing at a tighter set).
-/

open PLLFormula

namespace PLLND
namespace F0
namespace FilterIso

open SemUI RNEmbed
open PLLND.LaxInfinite (atomFree)
open NotIso (cls le_of_deriv not_le_of_check Disj Core HasCore hasCore_of_iso T3)

/-! ## 0. The question -/

/-- **The question** (Paper III, OPEN): no proper principal filter of F0 is
order-isomorphic to F0. -/
def FilterIsoQ : Prop :=
  ∀ p : RNClass, p ≠ ⊥ → ¬ Nonempty (Set.Ici p ≃o RNClass)

/-- **The dense residue**: the same for the filters above `t3`. -/
def DenseResidue : Prop :=
  ∀ p : RNClass, T3 ≤ p → ¬ Nonempty (Set.Ici p ≃o RNClass)

/-! ## 1. Order-theoretic tools -/

/-- `P` has a disjoint pair of non-least elements. -/
def HasDisjPair (P : Type) [LE P] : Prop :=
  ∃ x y : P, ¬ IsBot x ∧ ¬ IsBot y ∧ Disj x y

/-- **A disjoint pair transfers along an order isomorphism.** -/
theorem hasDisjPair_of_iso {P Q : Type} [Preorder P] [Preorder Q] (f : P ≃o Q)
    (h : HasDisjPair Q) : HasDisjPair P := by
  obtain ⟨x, y, hx, hy, hxy⟩ := h
  refine ⟨f.symm x, f.symm y, fun hb => hx fun w => f.symm.le_iff_le.mp (hb (f.symm w)),
    fun hb => hy fun w => f.symm.le_iff_le.mp (hb (f.symm w)), fun z hzx hzy => ?_⟩
  have hb := hxy (f z) (f.le_symm_apply.mp hzx) (f.le_symm_apply.mp hzy)
  exact fun w => f.le_iff_le.mp (hb (f w))

/-- `a` is a **big atom**: not least, and everything except the bottom and
one further element `d` lies above it. -/
def BigAtom {P : Type} [LE P] (a : P) : Prop :=
  ¬ IsBot a ∧ ∃ d : P, ∀ x : P, a ≤ x ∨ IsBot x ∨ x = d

/-- **Big atoms transfer along an order isomorphism.** -/
theorem bigAtom_of_iso {P Q : Type} [Preorder P] [Preorder Q] (f : P ≃o Q) {a : P}
    (h : BigAtom a) : BigAtom (f a) := by
  obtain ⟨ha, d, hd⟩ := h
  refine ⟨fun hb => ha fun w => f.le_iff_le.mp (hb (f w)), f d, fun x => ?_⟩
  rcases hd (f.symm x) with h | h | h
  · exact Or.inl (f.le_symm_apply.mp h)
  · exact Or.inr (Or.inl fun w => f.symm.le_iff_le.mp (h (f.symm w)))
  · refine Or.inr (Or.inr ?_)
    rw [← h]
    exact (f.apply_symm_apply x).symm

/-- An order isomorphism restricts to the principal filters. -/
def iciIso {P Q : Type} [Preorder P] [Preorder Q] (f : P ≃o Q) (x : P) :
    Set.Ici x ≃o Set.Ici (f x) where
  toFun y := ⟨f y.1, f.monotone y.2⟩
  invFun z := ⟨f.symm z.1, f.le_symm_apply.mpr z.2⟩
  left_inv y := Subtype.ext (f.symm_apply_apply y.1)
  right_inv z := Subtype.ext (f.apply_symm_apply z.1)
  map_rel_iff' := f.le_iff_le

/-- The filter of `x` inside `[p, ⊤]` is the filter of `x`. -/
def iciIci {α : Type} [Preorder α] (p : α) (x : Set.Ici p) :
    Set.Ici x ≃o Set.Ici (x : α) where
  toFun y := ⟨y.1.1, y.2⟩
  invFun z := ⟨⟨z.1, le_trans x.2 z.2⟩, z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-! ## 2. The classes below `t3` and the low classification -/

/-- `⟦◯⊥⟧ = t1`. -/
def E : RNClass := cls e rfl
/-- `⟦¬◯⊥⟧ = t2`. -/
def NE : RNClass := cls ne rfl
/-- `⟦t4⟧`. -/
def T4c : RNClass := cls t4 rfl
/-- `⟦t5⟧`. -/
def T5c : RNClass := cls t5 rfl

/-! The non-entailments, on the four-world model `M3` of `wip/f0Covers.lean`
(the worlds of the cells `nd_*` there), stated for the semantic order. -/

theorem nle_e_bot : ¬ LaxInfinite.Le e .falsePLL := not_le_of_check (M := M3) (w := 0) (by decide)
theorem nle_ne_bot : ¬ LaxInfinite.Le ne .falsePLL :=
  not_le_of_check (M := M3) (w := 1) (by decide)
theorem nle_t3_bot : ¬ LaxInfinite.Le t3 .falsePLL :=
  not_le_of_check (M := M3) (w := 0) (by decide)
theorem nle_t4_bot : ¬ LaxInfinite.Le t4 .falsePLL :=
  not_le_of_check (M := M3) (w := 0) (by decide)
theorem nle_e_ne : ¬ LaxInfinite.Le e ne := not_le_of_check (M := M3) (w := 0) (by decide)
theorem nle_ne_e : ¬ LaxInfinite.Le ne e := not_le_of_check (M := M3) (w := 1) (by decide)
theorem nle_ne_t4 : ¬ LaxInfinite.Le ne t4 := not_le_of_check (M := M3) (w := 1) (by decide)
theorem nle_t3_e : ¬ LaxInfinite.Le t3 e := not_le_of_check (M := M3) (w := 1) (by decide)
theorem nle_t3_ne : ¬ LaxInfinite.Le t3 ne := not_le_of_check (M := M3) (w := 0) (by decide)
theorem nle_t4_e : ¬ LaxInfinite.Le t4 e := not_le_of_check (M := M3) (w := 2) (by decide)
theorem nle_t4_ne : ¬ LaxInfinite.Le t4 ne := not_le_of_check (M := M3) (w := 0) (by decide)
theorem nle_t5_t4 : ¬ LaxInfinite.Le t5 t4 := not_le_of_check (M := M3) (w := 1) (by decide)

/-- **`F0 = {⊥, t1, t2, t4} ∪ ↑t3`.**  Every class is above `t3` or is one of
`⊥`, `◯⊥`, `¬◯⊥`, `t4`.  Constructive: `low_trichotomy`, then the tables for
`↓t3` and `↓t4`. -/
theorem classify_low (x : RNClass) : T3 ≤ x ∨ x = ⊥ ∨ x = E ∨ x = NE ∨ x = T4c := by
  induction x using Quotient.ind
  rename_i c
  rcases low_trichotomy c.1 c.2 with hec | hcb | hcn
  · obtain ⟨l, hl, i⟩ := D3_table.classify c.1 c.2
    have hec3 : Deriv [e] (c.1.and t3) := Deriv.andIntro hec D3_below_1
    rcases List.mem_cons.mp hl with rfl | hl
    · exact absurd (Deriv.cutHead hec3 i.1) nd_e_bot
    rcases List.mem_cons.mp hl with rfl | hl
    · have hc4 : Deriv [c.1] t4 :=
        Deriv.impIntro (Deriv.cutHead
          (Deriv.andIntro (Deriv.iden (.tail _ (.head _))) (Deriv.iden (.head _))) i.1)
      obtain ⟨l', hl', i'⟩ := D4_table.classify_below c.2 hc4
      rcases List.mem_cons.mp hl' with rfl | hl'
      · exact absurd (Deriv.cutHead hec i'.1) nd_e_bot
      rcases List.mem_cons.mp hl' with rfl | hl'
      · exact Or.inr (Or.inr (Or.inl (Quotient.sound ⟨le_of_deriv i'.1, le_of_deriv i'.2⟩)))
      rcases List.mem_cons.mp hl' with rfl | hl'
      · exact Or.inr (Or.inr (Or.inr (Or.inr
          (Quotient.sound ⟨le_of_deriv i'.1, le_of_deriv i'.2⟩))))
      · simp at hl'
    rcases List.mem_cons.mp hl with rfl | hl
    · exact absurd (Deriv.cutHead hec3 i.1) nd_e_ne
    rcases List.mem_cons.mp hl with rfl | hl
    · exact Or.inl (le_of_deriv (Deriv.andElim1 i.2))
    · simp at hl
  · exact Or.inr (Or.inl (Quotient.sound ⟨le_of_deriv hcb.1, le_of_deriv hcb.2⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      (Quotient.sound ⟨le_of_deriv hcn.1, le_of_deriv hcn.2⟩))))

/-! ## 3. The cells `t2`, `t4`: no disjoint pair -/

/-- **F0 has a disjoint pair**: `◯⊥ ∧ ¬◯⊥ ⊢ ⊥`. -/
theorem rn_hasDisjPair : HasDisjPair RNClass := by
  refine ⟨E, NE, fun h => nle_e_bot (h ⊥), fun h => nle_ne_bot (h ⊥), fun z hzE hzN => ?_⟩
  induction z using Quotient.ind
  rename_i c
  have hc : LaxInfinite.Le c.1 .falsePLL := fun M w h =>
    le_of_deriv D3_and_1_2.1 M w ⟨(hzE : LaxInfinite.Le c.1 e) M w h,
      (hzN : LaxInfinite.Le c.1 ne) M w h⟩
  exact fun w => le_trans (hc : (Quotient.mk _ c : RNClass) ≤ ⊥) bot_le

/-- Above `¬◯⊥`, every element other than `¬◯⊥` lies above `t3`. -/
theorem above_t3_of_ici_ne (x : Set.Ici NE) (hx : ¬ IsBot x) : T3 ≤ x.1 := by
  have h2 : NE ≤ x.1 := x.2
  rcases classify_low x.1 with h | h | h | h | h
  · exact h
  · rw [h] at h2
    exact absurd h2 nle_ne_bot
  · rw [h] at h2
    exact absurd h2 nle_ne_e
  · exfalso
    apply hx
    intro w
    show x.1 ≤ w.1
    rw [h]
    exact w.2
  · rw [h] at h2
    exact absurd h2 nle_ne_t4

theorem ne_ici_no_disjPair : ¬ HasDisjPair (Set.Ici NE) := by
  rintro ⟨x, y, hx, hy, hxy⟩
  have hz := hxy ⟨T3, (le_of_deriv D3_below_2 : NE ≤ T3)⟩
    (above_t3_of_ici_ne x hx) (above_t3_of_ici_ne y hy)
  exact nle_t3_ne (hz ⟨NE, le_refl NE⟩)

/-- **Cell `t2`: `[¬◯⊥, ⊤] ≇ F0`.** -/
theorem ne_filter_not_iso : ¬ Nonempty (Set.Ici NE ≃o RNClass) :=
  fun ⟨f⟩ => ne_ici_no_disjPair (hasDisjPair_of_iso f rn_hasDisjPair)

/-- Above `t4`, every element other than `t4` lies above `t3`. -/
theorem above_t3_of_ici_t4 (x : Set.Ici T4c) (hx : ¬ IsBot x) : T3 ≤ x.1 := by
  have h2 : T4c ≤ x.1 := x.2
  rcases classify_low x.1 with h | h | h | h | h
  · exact h
  · rw [h] at h2
    exact absurd h2 nle_t4_bot
  · rw [h] at h2
    exact absurd h2 nle_t4_e
  · rw [h] at h2
    exact absurd h2 nle_t4_ne
  · exfalso
    apply hx
    intro w
    show x.1 ≤ w.1
    rw [h]
    exact w.2

theorem t5_le_of {x : RNClass} (h3 : T3 ≤ x) (h4 : T4c ≤ x) : T5c ≤ x := by
  induction x using Quotient.ind
  exact fun M w h => h.elim (fun h' => (h3 : LaxInfinite.Le t3 _) M w h')
    (fun h' => (h4 : LaxInfinite.Le t4 _) M w h')

theorem t4_ici_no_disjPair : ¬ HasDisjPair (Set.Ici T4c) := by
  rintro ⟨x, y, hx, hy, hxy⟩
  have hz := hxy ⟨T5c, (le_of_deriv D5_below_4 : T4c ≤ T5c)⟩
    (t5_le_of (above_t3_of_ici_t4 x hx) x.2) (t5_le_of (above_t3_of_ici_t4 y hy) y.2)
  exact nle_t5_t4 (hz ⟨T4c, le_refl T4c⟩)

/-- **Cell `t4`: `[t4, ⊤] ≇ F0`.** -/
theorem t4_filter_not_iso : ¬ Nonempty (Set.Ici T4c ≃o RNClass) :=
  fun ⟨f⟩ => t4_ici_no_disjPair (hasDisjPair_of_iso f rn_hasDisjPair)

/-! ## 4. The cell `t1`: descent to `t3` -/

/-- **`◯⊥` is the only big atom of F0.** -/
theorem bigAtom_rn {a : RNClass} (h : BigAtom a) : a = E := by
  obtain ⟨ha, d, hd⟩ := h
  have nbE : ¬ IsBot E := fun hb => nle_e_bot (hb ⊥)
  have nbNE : ¬ IsBot NE := fun hb => nle_ne_bot (hb ⊥)
  have nbT4 : ¬ IsBot T4c := fun hb => nle_t4_bot (hb ⊥)
  rcases classify_low a with h | h | h | h | h
  · rcases hd E with h1 | h1 | h1
    · exact absurd (le_trans h h1) nle_t3_e
    · exact absurd h1 nbE
    rcases hd NE with h2 | h2 | h2
    · exact absurd (le_trans h h2) nle_t3_ne
    · exact absurd h2 nbNE
    exact absurd (le_of_eq (h2.trans h1.symm)) nle_ne_e
  · exfalso
    apply ha
    rw [h]
    exact fun b => bot_le
  · exact h
  · subst h
    rcases hd E with h1 | h1 | h1
    · exact absurd h1 nle_ne_e
    · exact absurd h1 nbE
    rcases hd T4c with h2 | h2 | h2
    · exact absurd h2 nle_ne_t4
    · exact absurd h2 nbT4
    exact absurd (le_of_eq (h2.trans h1.symm)) nle_t4_e
  · subst h
    rcases hd E with h1 | h1 | h1
    · exact absurd h1 nle_t4_e
    · exact absurd h1 nbE
    rcases hd NE with h2 | h2 | h2
    · exact absurd h2 nle_t4_ne
    · exact absurd h2 nbNE
    exact absurd (le_of_eq (h2.trans h1.symm)) nle_ne_e

theorem E_le_T3 : E ≤ T3 := le_of_deriv D3_below_1

/-- **`t3` is a big atom of `[◯⊥, ⊤]`**, with `t4` the exceptional element:
`[t1, ⊤] = {t1, t4} ∪ ↑t3`. -/
theorem bigAtom_ici_e : BigAtom (⟨T3, E_le_T3⟩ : Set.Ici E) := by
  refine ⟨fun hb => nle_t3_e (hb ⟨E, le_refl E⟩),
    ⟨T4c, (le_of_deriv D4_below_1 : E ≤ T4c)⟩, fun x => ?_⟩
  have h2 : E ≤ x.1 := x.2
  rcases classify_low x.1 with h | h | h | h | h
  · exact Or.inl h
  · rw [h] at h2
    exact absurd h2 nle_e_bot
  · refine Or.inr (Or.inl ?_)
    intro w
    show x.1 ≤ w.1
    rw [h]
    exact w.2
  · rw [h] at h2
    exact absurd h2 nle_e_ne
  · exact Or.inr (Or.inr (Subtype.ext h))

/-- **Cell `t1`: `[◯⊥, ⊤] ≇ F0`.**  An isomorphism sends the big atom `t3` of
`[◯⊥, ⊤]` to the big atom `◯⊥` of F0, so it restricts to
`[t3, ⊤] ≅ [◯⊥, ⊤]`, and `[t3, ⊤] ≅ F0` is refuted (`t3_filter_not_iso`). -/
theorem e_filter_not_iso : ¬ Nonempty (Set.Ici E ≃o RNClass) := by
  rintro ⟨g⟩
  have hg : g ⟨T3, E_le_T3⟩ = E := bigAtom_rn (bigAtom_of_iso g bigAtom_ici_e)
  exact NotIso.t3_filter_not_iso
    ⟨((iciIci E ⟨T3, E_le_T3⟩).symm.trans (iciIso g ⟨T3, E_le_T3⟩)).trans
      ((OrderIso.setCongr _ _ (by rw [hg])).trans g)⟩

/-! ## 5. The reduction -/

/-- **Every non-dense `p ≠ ⊥` is refuted.** -/
theorem nondense_filter_not_iso (p : RNClass) (hp : p ≠ ⊥) (hd : ¬ T3 ≤ p) :
    ¬ Nonempty (Set.Ici p ≃o RNClass) := by
  rcases classify_low p with h | h | h | h | h
  · exact absurd h hd
  · exact absurd h hp
  · subst h
    exact e_filter_not_iso
  · subst h
    exact ne_filter_not_iso
  · subst h
    exact t4_filter_not_iso

/-- **The question is equivalent to its dense residue.** -/
theorem filterIsoQ_iff_dense : FilterIsoQ ↔ DenseResidue := by
  constructor
  · intro h p hp
    refine h p fun h0 => ?_
    rw [h0] at hp
    exact nle_t3_bot hp
  · intro h p hp
    rcases classify_low p with h3 | h0 | h1 | h2 | h4
    · exact h p h3
    · exact absurd h0 hp
    · subst h1
      exact e_filter_not_iso
    · subst h2
      exact ne_filter_not_iso
    · subst h4
      exact t4_filter_not_iso

/-! ## 6. The σ-bases -/

namespace SigC

/-- Worlds of the σ-extension of a constraint model: the old worlds, the tops
`nT` (no fallible `Rₘ`-successor, so `¬◯⊥` holds) and `eT`, and a fallible
world `fT` above `eT` (so `◯⊥` holds at `eT`).  Only the non-fallible old
worlds see the tops. -/
inductive CW (W : Type) where
  | orig (x : W)
  | nT
  | eT
  | fT

variable (M : ConstraintModel)

def ri : CW M.W → CW M.W → Prop
  | .orig x, .orig y => M.Ri x y
  | .orig x, .nT => x ∉ M.F
  | .orig x, .eT => x ∉ M.F
  | .orig x, .fT => x ∉ M.F
  | .nT, .nT => True
  | .eT, .eT => True
  | .eT, .fT => True
  | .fT, .fT => True
  | _, _ => False

def rm : CW M.W → CW M.W → Prop
  | .orig x, .orig y => M.Rm x y
  | .nT, .nT => True
  | .eT, .eT => True
  | .eT, .fT => True
  | .fT, .fT => True
  | _, _ => False

def fl : CW M.W → Prop
  | .orig x => x ∈ M.F
  | .fT => True
  | _ => False

def vl (a : String) : CW M.W → Prop
  | .orig x => x ∈ M.V a
  | _ => True

theorem ri_refl : ∀ w : CW M.W, ri M w w
  | .orig x => M.refl_i x
  | .nT => trivial
  | .eT => trivial
  | .fT => trivial

theorem rm_refl : ∀ w : CW M.W, rm M w w
  | .orig x => M.refl_m x
  | .nT => trivial
  | .eT => trivial
  | .fT => trivial

theorem ri_trans {u v w : CW M.W} (h1 : ri M u v) (h2 : ri M v w) : ri M u w := by
  cases u <;> cases v <;> cases w <;>
    first
    | exact trivial
    | exact M.trans_i h1 h2
    | exact fun hx => h2 (M.hered_F h1 hx)
    | exact h1
    | exact False.elim h1
    | exact False.elim h2

theorem rm_trans {u v w : CW M.W} (h1 : rm M u v) (h2 : rm M v w) : rm M u w := by
  cases u <;> cases v <;> cases w <;>
    first
    | exact trivial
    | exact M.trans_m h1 h2
    | exact False.elim h1
    | exact False.elim h2

theorem rm_sub {u v : CW M.W} (h : rm M u v) : ri M u v := by
  cases u <;> cases v <;>
    first
    | exact trivial
    | exact M.sub_mi h
    | exact False.elim h

theorem fl_hered {u v : CW M.W} (h : ri M u v) (hu : fl M u) : fl M v := by
  cases u <;> cases v <;>
    first
    | exact trivial
    | exact M.hered_F h hu
    | exact False.elim (h hu)
    | exact False.elim h
    | exact False.elim hu

theorem vl_hered {a : String} {u v : CW M.W} (h : ri M u v) (hu : vl M a u) : vl M a v := by
  cases u <;> cases v <;>
    first
    | exact trivial
    | exact M.hered_V h hu
    | exact False.elim h

theorem vl_full {a : String} {w : CW M.W} (hw : fl M w) : vl M a w := by
  cases w with
  | orig x => exact M.full_F hw
  | nT => exact trivial
  | eT => exact trivial
  | fT => exact trivial

/-- **The σ-extension**, a constraint model. -/
def ext : ConstraintModel where
  W := CW M.W
  Ri := ri M
  Rm := rm M
  F := {w | fl M w}
  V a := {w | vl M a w}
  refl_i := ri_refl M
  trans_i := ri_trans M
  refl_m := rm_refl M
  trans_m := rm_trans M
  sub_mi := rm_sub M
  hered_F := fun h hu => fl_hered M h hu
  hered_V := fun h hu => vl_hered M h hu
  full_F := fun hw => vl_full M hw

theorem decF (hF : ∀ x : M.W, x ∈ M.F ∨ x ∉ M.F) :
    ∀ w : CW M.W, w ∈ (ext M).F ∨ w ∉ (ext M).F
  | .orig x => hF x
  | .nT => Or.inr fun h => h
  | .eT => Or.inr fun h => h
  | .fT => Or.inl trivial

theorem not_e_nT : ¬ (ext M).force CW.nT e := by
  intro h
  obtain ⟨u, hu, hf⟩ := h CW.nT trivial
  cases u with
  | orig _ => exact hu
  | nT => exact hf
  | eT => exact hu
  | fT => exact hu

theorem e_eT : (ext M).force CW.eT e := by
  show ∀ v, (ext M).Ri CW.eT v → ∃ u, (ext M).Rm v u ∧ (ext M).force u .falsePLL
  intro v hv
  cases v with
  | orig _ => exact False.elim hv
  | nT => exact False.elim hv
  | eT => exact ⟨CW.fT, trivial, trivial⟩
  | fT => exact ⟨CW.fT, trivial, trivial⟩

theorem fT_force (φ : PLLFormula) : (ext M).force CW.fT φ :=
  (ext M).force_of_fallible (show CW.fT ∈ (ext M).F from trivial)

def isTop : CW M.W → Prop
  | .orig _ => False
  | _ => True

theorem top_up {u v : CW M.W} (hu : isTop M u) (h : ri M u v) : isTop M v := by
  cases u <;> cases v <;> first | exact trivial | exact False.elim hu | exact False.elim h

theorem t3_top : ∀ w : CW M.W, isTop M w → (ext M).force w t3
  | .orig _, hw => False.elim hw
  | .nT, _ => by
      show (ext M).force CW.nT e ∨ (ext M).force CW.nT ne
      refine Or.inr ?_
      show ∀ v, (ext M).Ri CW.nT v → (ext M).force v e → (ext M).force v .falsePLL
      intro v hv hve
      cases v with
      | orig _ => exact False.elim hv
      | nT => exact False.elim (not_e_nT M hve)
      | eT => exact False.elim hv
      | fT => exact False.elim hv
  | .eT, _ => Or.inl (e_eT M)
  | .fT, _ => fT_force M t3

theorem t3_orig {x : M.W} (hx : x ∉ M.F) : ¬ (ext M).force (CW.orig x) t3 := by
  intro h
  rcases (h : (ext M).force (CW.orig x) e ∨ (ext M).force (CW.orig x) ne) with h | h
  · exact not_e_nT M ((ext M).force_hered (show (ext M).Ri (CW.orig x) CW.nT from hx) h)
  · exact h CW.eT hx (e_eT M)

/-- **The tops force every `σ`-formula.** -/
theorem top_sig : ∀ (ψ : PLLFormula) (w : CW M.W), isTop M w → (ext M).force w (Sig.sig ψ)
  | .prop _, w, hw => by
      cases w with
      | orig _ => exact False.elim hw
      | nT => exact trivial
      | eT => exact trivial
      | fT => exact trivial
  | .falsePLL, w, hw => t3_top M w hw
  | .and A B, w, hw => ⟨top_sig A w hw, top_sig B w hw⟩
  | .or A _, w, hw => Or.inl (top_sig A w hw)
  | .ifThen _ B, w, hw => fun v hv _ => top_sig B v (top_up M hw hv)
  | .somehow A, w, hw => fun v hv => ⟨v, rm_refl M v, top_sig A v (top_up M hw hv)⟩

/-- **At old worlds `σ ψ` holds exactly where `ψ` holds**, when fallibility
is decidable in `M`. -/
theorem orig_sig (hF : ∀ x : M.W, x ∈ M.F ∨ x ∉ M.F) :
    ∀ (ψ : PLLFormula) (x : M.W), (ext M).force (CW.orig x) (Sig.sig ψ) ↔ M.force x ψ
  | .prop _, _ => Iff.rfl
  | .falsePLL, x => ⟨fun h => (hF x).elim id (fun hx => False.elim (t3_orig M hx h)),
      fun h => (ext M).force_of_fallible (show CW.orig x ∈ (ext M).F from h)⟩
  | .and A B, x => and_congr (orig_sig hF A x) (orig_sig hF B x)
  | .or A B, x => or_congr (orig_sig hF A x) (orig_sig hF B x)
  | .ifThen A B, x =>
      ⟨fun h y hxy hA => (orig_sig hF B y).mp (h (CW.orig y) hxy ((orig_sig hF A y).mpr hA)),
       fun h v hv hA => by
        cases v with
        | orig y => exact (orig_sig hF B y).mpr (h y hv ((orig_sig hF A y).mp hA))
        | nT => exact top_sig M B CW.nT trivial
        | eT => exact top_sig M B CW.eT trivial
        | fT => exact fT_force M _⟩
  | .somehow A, x =>
      ⟨fun h y hxy => by
        obtain ⟨u, hu, hA⟩ := h (CW.orig y) hxy
        cases u with
        | orig z => exact ⟨z, hu, (orig_sig hF A z).mp hA⟩
        | nT => exact False.elim hu
        | eT => exact False.elim hu
        | fT => exact False.elim hu,
       fun h v hv => by
        cases v with
        | orig y =>
            obtain ⟨z, hz, hA⟩ := h y hv
            exact ⟨CW.orig z, hz, (orig_sig hF A z).mpr hA⟩
        | nT => exact ⟨CW.nT, trivial, top_sig M A CW.nT trivial⟩
        | eT => exact ⟨CW.eT, trivial, top_sig M A CW.eT trivial⟩
        | fT => exact ⟨CW.fT, trivial, fT_force M _⟩⟩

end SigC

/-- A refutation of `a ⊢ b` on a constraint model with decidable fallibility. -/
def Refutes (a b : PLLFormula) : Prop :=
  ∃ M : ConstraintModel, (∀ x : M.W, x ∈ M.F ∨ x ∉ M.F) ∧
    ∃ w : M.W, M.force w a ∧ ¬ M.force w b

theorem not_le_of_refutes {a b : PLLFormula} (h : Refutes a b) : ¬ LaxInfinite.Le a b := by
  intro hle
  obtain ⟨M, _, w, ha, hb⟩ := h
  exact hb (hle M w ha)

/-- **`σ` carries refutations** (semantic reflection, no completeness). -/
theorem refutes_sig {a b : PLLFormula} (h : Refutes a b) :
    Refutes (Sig.sig a) (Sig.sig b) := by
  obtain ⟨M, hF, w, ha, hb⟩ := h
  exact ⟨SigC.ext M, SigC.decF M hF, SigC.CW.orig w, (SigC.orig_sig M hF a w).mpr ha,
    fun h => hb ((SigC.orig_sig M hF b w).mp h)⟩

theorem refutes_sigN : ∀ (n : Nat) {a b : PLLFormula}, Refutes a b →
    Refutes (Sig.sigN n a) (Sig.sigN n b)
  | 0, _, _, h => h
  | n + 1, _, _, h => refutes_sigN n (refutes_sig h)

/-- A checked finite countermodel is a refutation with decidable fallibility. -/
theorem refutes_of_check {M : FinCM} {w : Nat} {a b : PLLFormula}
    (h : FinCM.checkB M w [a] b = true) : Refutes a b := by
  simp only [FinCM.checkB, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨hwb, hlt⟩, hΓ⟩, hC⟩ := h
  have hwf := FinCM.wellFormed_of_wellB hwb
  refine ⟨M.toModel hwf, fun x => ?_, ⟨w, hlt⟩,
    (M.force_iff hwf a ⟨w, hlt⟩).mpr (hΓ a (List.mem_singleton_self a)), fun hf => ?_⟩
  · show M.fallB x.1 = true ∨ ¬ M.fallB x.1 = true
    cases M.fallB x.1 with
    | true => exact Or.inl rfl
    | false => exact Or.inr Bool.false_ne_true
  · rw [M.force_iff hwf b ⟨w, hlt⟩, hC] at hf
    exact Bool.false_ne_true hf

/-- Two disjoint pairs `(a1, b1)`, `(a2, b2)` of `[q, ⊤]` with no member in
common: the positive facts are derivations, the negative ones refutations. -/
structure TwoPairs (q a1 b1 a2 b2 : PLLFormula) : Prop where
  la1 : Deriv [q] a1
  lb1 : Deriv [q] b1
  la2 : Deriv [q] a2
  lb2 : Deriv [q] b2
  m1 : Deriv [a1.and b1] q
  m2 : Deriv [a2.and b2] q
  na1 : Refutes a1 q
  nb1 : Refutes b1 q
  na2 : Refutes a2 q
  nb2 : Refutes b2 q
  x11 : Refutes a1 a2 ∨ Refutes a2 a1
  x12 : Refutes a1 b2 ∨ Refutes b2 a1
  x21 : Refutes b1 a2 ∨ Refutes a2 b1
  x22 : Refutes b1 b2 ∨ Refutes b2 b1

theorem sigN_and : ∀ (n : Nat) (φ ψ : PLLFormula),
    Sig.sigN n (φ.and ψ) = (Sig.sigN n φ).and (Sig.sigN n ψ)
  | 0, _, _ => rfl
  | n + 1, φ, ψ => sigN_and n (Sig.sig φ) (Sig.sig ψ)

theorem refutes_or_sigN (n : Nat) {a b : PLLFormula} (h : Refutes a b ∨ Refutes b a) :
    Refutes (Sig.sigN n a) (Sig.sigN n b) ∨ Refutes (Sig.sigN n b) (Sig.sigN n a) :=
  h.elim (fun h => Or.inl (refutes_sigN n h)) (fun h => Or.inr (refutes_sigN n h))

/-- **`σⁿ` carries two disjoint pairs.** -/
theorem twoPairs_sigN (n : Nat) {q a1 b1 a2 b2 : PLLFormula}
    (hq : atomFree q = true) (ha1 : atomFree a1 = true) (hb1 : atomFree b1 = true)
    (ha2 : atomFree a2 = true) (hb2 : atomFree b2 = true)
    (h : TwoPairs q a1 b1 a2 b2) :
    TwoPairs (Sig.sigN n q) (Sig.sigN n a1) (Sig.sigN n b1) (Sig.sigN n a2)
      (Sig.sigN n b2) where
  la1 := Sig.sigN_mono n hq ha1 h.la1
  lb1 := Sig.sigN_mono n hq hb1 h.lb1
  la2 := Sig.sigN_mono n hq ha2 h.la2
  lb2 := Sig.sigN_mono n hq hb2 h.lb2
  m1 := by
    have := Sig.sigN_mono n (φ := a1.and b1) (by simp [atomFree, ha1, hb1]) hq h.m1
    rwa [sigN_and] at this
  m2 := by
    have := Sig.sigN_mono n (φ := a2.and b2) (by simp [atomFree, ha2, hb2]) hq h.m2
    rwa [sigN_and] at this
  na1 := refutes_sigN n h.na1
  nb1 := refutes_sigN n h.nb1
  na2 := refutes_sigN n h.na2
  nb2 := refutes_sigN n h.nb2
  x11 := refutes_or_sigN n h.x11
  x12 := refutes_or_sigN n h.x12
  x21 := refutes_or_sigN n h.x21
  x22 := refutes_or_sigN n h.x22

/-- A point of `[⟦q⟧, ⊤]`. -/
def ptq (q : PLLFormula) (hq : atomFree q = true) (φ : PLLFormula) (h : atomFree φ = true)
    (hle : Deriv [q] φ) : Set.Ici (cls q hq) :=
  ⟨cls φ h, le_of_deriv hle⟩

theorem ptq_not_bot {q φ : PLLFormula} {hq : atomFree q = true} {h : atomFree φ = true}
    {hle : Deriv [q] φ} (hn : ¬ LaxInfinite.Le φ q) : ¬ IsBot (ptq q hq φ h hle) :=
  fun hb => hn (hb ⟨cls q hq, Set.self_mem_Ici⟩)

theorem ptq_disj {q a b : PLLFormula} {hq : atomFree q = true} {ha : atomFree a = true}
    {hb : atomFree b = true} {hla : Deriv [q] a} {hlb : Deriv [q] b}
    (hab : Deriv [a.and b] q) : Disj (ptq q hq a ha hla) (ptq q hq b hb hlb) := by
  intro z hza hzb
  obtain ⟨zq, hzq⟩ := z
  induction zq using Quotient.ind
  rename_i c
  have hct : LaxInfinite.Le c.1 q := fun M w hc =>
    le_of_deriv hab M w ⟨(hza : LaxInfinite.Le c.1 a) M w hc, (hzb : LaxInfinite.Le c.1 b) M w hc⟩
  intro w
  show (Quotient.mk LaxInfinite.closedSetoid c : RNClass) ≤ w.1
  exact le_trans (hct : (Quotient.mk LaxInfinite.closedSetoid c : RNClass) ≤ cls q hq)
    (Set.mem_Ici.mp w.2)

theorem ptq_ne {q a b : PLLFormula} {hq : atomFree q = true} {ha : atomFree a = true}
    {hb : atomFree b = true} {hla : Deriv [q] a} {hlb : Deriv [q] b}
    (hne : Refutes a b ∨ Refutes b a) : ptq q hq a ha hla ≠ ptq q hq b hb hlb := fun h => by
  have he : LaxInfinite.LaxEquiv a b := Quotient.exact (congrArg Subtype.val h)
  rcases hne with hn | hn
  · exact not_le_of_refutes hn he.1
  · exact not_le_of_refutes hn he.2

/-- **Two disjoint pairs with no member in common: `[q, ⊤]` has no core.** -/
theorem ici_no_core_of_twoPairs {q a1 b1 a2 b2 : PLLFormula} (hq : atomFree q = true)
    (ha1 : atomFree a1 = true) (hb1 : atomFree b1 = true)
    (ha2 : atomFree a2 = true) (hb2 : atomFree b2 = true)
    (h : TwoPairs q a1 b1 a2 b2) : ¬ HasCore (Set.Ici (cls q hq)) := by
  rintro ⟨d, hd⟩
  have hC := hd (ptq q hq a1 ha1 h.la1) (ptq q hq b1 hb1 h.lb1)
    (ptq_not_bot (not_le_of_refutes h.na1)) (ptq_not_bot (not_le_of_refutes h.nb1))
    (ptq_disj h.m1)
  have hT := hd (ptq q hq a2 ha2 h.la2) (ptq q hq b2 hb2 h.lb2)
    (ptq_not_bot (not_le_of_refutes h.na2)) (ptq_not_bot (not_le_of_refutes h.nb2))
    (ptq_disj h.m2)
  rcases hC with h1 | h1 <;> rcases hT with h2 | h2
  · exact ptq_ne h.x11 (h1.trans h2.symm)
  · exact ptq_ne h.x12 (h1.trans h2.symm)
  · exact ptq_ne h.x21 (h1.trans h2.symm)
  · exact ptq_ne h.x22 (h1.trans h2.symm)

/-! The eight countermodels of `wip/f0NotIso.lean`, as refutations. -/

theorem rf_c1_t3 : Refutes NotIso.c1F t3 :=
  refutes_of_check (M := NotIso.K_c1_t3) (w := 0) (by decide)
theorem rf_g1_t3 : Refutes NotIso.g1F t3 :=
  refutes_of_check (M := NotIso.K_g1_t3) (w := 0) (by decide)
theorem rf_t5_t3 : Refutes t5 t3 :=
  refutes_of_check (M := NotIso.K_t5_t3) (w := 0) (by decide)
theorem rf_t6_t3 : Refutes NotIso.t6F t3 :=
  refutes_of_check (M := NotIso.K_t6_t3) (w := 0) (by decide)
theorem rf_c1_t5 : Refutes NotIso.c1F t5 :=
  refutes_of_check (M := NotIso.K_c1_t5_lr) (w := 0) (by decide)
theorem rf_t6_c1 : Refutes NotIso.t6F NotIso.c1F :=
  refutes_of_check (M := NotIso.K_c1_t6_rl) (w := 0) (by decide)
theorem rf_g1_t5 : Refutes NotIso.g1F t5 :=
  refutes_of_check (M := NotIso.K_g1_t5_lr) (w := 0) (by decide)
theorem rf_g1_t6 : Refutes NotIso.g1F NotIso.t6F :=
  refutes_of_check (M := NotIso.K_g1_t6_lr) (w := 0) (by decide)

/-- **The two disjoint pairs above `t3`** (`wip/f0NotIso.lean`), as data. -/
theorem twoPairs_t3 : TwoPairs t3 NotIso.c1F NotIso.g1F t5 NotIso.t6F where
  la1 := NotIso.t3_le_c1
  lb1 := NotIso.t3_le_g1
  la2 := NotIso.t3_le_t5
  lb2 := NotIso.t3_le_t6
  m1 := NotIso.c1g1_le_t3
  m2 := NotIso.t5t6_le_t3
  na1 := rf_c1_t3
  nb1 := rf_g1_t3
  na2 := rf_t5_t3
  nb2 := rf_t6_t3
  x11 := Or.inl rf_c1_t5
  x12 := Or.inr rf_t6_c1
  x21 := Or.inl rf_g1_t5
  x22 := Or.inl rf_g1_t6

/-- **Cell `σⁿ⁺¹(⊥) = σⁿ(t3)`, every `n`: `[σⁿ(t3), ⊤] ≇ F0`.**  `n = 0` is
`t3_filter_not_iso`; `n = 1` is the base `σ²(⊥) = ◯t3 ∨ g1` of the second copy. -/
theorem sigN_filter_not_iso (n : Nat) :
    ¬ Nonempty (Set.Ici (cls (Sig.sigN n t3) (Sig.sigN_vf n rfl)) ≃o RNClass) := by
  rintro ⟨f⟩
  have h := twoPairs_sigN n (q := t3) (a1 := NotIso.c1F) (b1 := NotIso.g1F) (a2 := t5)
    (b2 := NotIso.t6F) rfl rfl rfl rfl rfl twoPairs_t3
  exact ici_no_core_of_twoPairs (Sig.sigN_vf n (φ := t3) rfl)
    (Sig.sigN_vf n (φ := NotIso.c1F) rfl) (Sig.sigN_vf n (φ := NotIso.g1F) rfl)
    (Sig.sigN_vf n (φ := t5) rfl) (Sig.sigN_vf n (φ := NotIso.t6F) rfl) h
    (hasCore_of_iso f NotIso.rnclass_core)

/-- The second base, `σ²(⊥) = σ(t3)`, explicitly. -/
theorem sig2_filter_not_iso :
    ¬ Nonempty (Set.Ici (cls (Sig.sig t3) (Sig.sig_vf rfl)) ≃o RNClass) :=
  sigN_filter_not_iso 1

/-! ## 7. A dense cell off the σ-bases: `c1 = ◯t3 = σ(t1)`

The dense analogue of the cell `t1`: `◯`-fixed (`◯c1 ⊣⊢ c1`) and the σ-image
of `t1`, but not a σ-base.  `[c1, ⊤]` has three pairwise disjoint elements
above `c1`,

    α = c1 ∨ t4,    β = c1 ∨ (g1 ∧ t6),    γ = c1 ∨ (t6 ∧ (g1 ↠ c1)),

so no element lies in every disjoint pair.  The meets are semantic one-liners
(`t4 ∧ t6 ⊢ ◯⊥ ⊢ c1`, and modus ponens); the three non-entailments
`α, β, γ ⊬ c1` are hand-built constraint models on 3, 4 and 5 worlds (the
points `(∈S, {e})`, `(∈S, {n, e})` and `(∈S, {(∉S, {n, e})})` under a fallible
top), checked by the kernel. -/

/-- Three pairwise disjoint non-least elements: no core. -/
theorem no_core_of_three {P : Type} [Preorder P] {x y z : P}
    (hx : ¬ IsBot x) (hy : ¬ IsBot y) (hz : ¬ IsBot z)
    (hxy : Disj x y) (hxz : Disj x z) (hyz : Disj y z) : ¬ HasCore P := by
  have dne : ∀ {u v : P}, ¬ IsBot u → Disj u v → u ≠ v :=
    fun hu h e => hu (h _ le_rfl (le_of_eq e))
  rintro ⟨d, hd⟩
  rcases hd x y hx hy hxy with h1 | h1
  · rcases hd y z hy hz hyz with h3 | h3
    · exact dne hx hxy (h1.trans h3.symm)
    · exact dne hx hxz (h1.trans h3.symm)
  · rcases hd x z hx hz hxz with h2 | h2
    · exact dne hx hxy (h2.trans h1.symm)
    · exact dne hy hyz (h1.trans h2.symm)

/-- `ptq_disj` from the semantic order. -/
theorem ptq_disj_le {q a b : PLLFormula} {hq : atomFree q = true} {ha : atomFree a = true}
    {hb : atomFree b = true} {hla : Deriv [q] a} {hlb : Deriv [q] b}
    (hab : LaxInfinite.Le (a.and b) q) : Disj (ptq q hq a ha hla) (ptq q hq b hb hlb) := by
  intro z hza hzb
  obtain ⟨zq, hzq⟩ := z
  induction zq using Quotient.ind
  rename_i c
  have hct : LaxInfinite.Le c.1 q := fun M w hc =>
    hab M w ⟨(hza : LaxInfinite.Le c.1 a) M w hc, (hzb : LaxInfinite.Le c.1 b) M w hc⟩
  intro w
  show (Quotient.mk LaxInfinite.closedSetoid c : RNClass) ≤ w.1
  exact le_trans (hct : (Quotient.mk LaxInfinite.closedSetoid c : RNClass) ≤ cls q hq)
    (Set.mem_Ici.mp w.2)

/-- `α = c1 ∨ t4`. -/
def alF : PLLFormula := NotIso.c1F.or t4
/-- `β = c1 ∨ (g1 ∧ t6)`. -/
def beF : PLLFormula := NotIso.c1F.or (NotIso.g1F.and NotIso.t6F)
/-- `γ = c1 ∨ (t6 ∧ (g1 ↠ c1))`. -/
def gaF : PLLFormula := NotIso.c1F.or (NotIso.t6F.and (NotIso.g1F.ifThen NotIso.c1F))

theorem e_le_c1 : Deriv [e] NotIso.c1F :=
  Deriv.somehowMono (Deriv.falsoElim _ (Deriv.iden (.head _)))

/-- `t4 ∧ t6 ⊢ c1`, semantically: `t4 ⊢ t5`, so `t6 = t5 ↠ t3` gives `t3`, and
`t3 ∧ t4 ⊣⊢ ◯⊥ ⊢ c1`. -/
theorem key46 {M : ConstraintModel} {w : M.W} (h4 : M.force w t4)
    (h6 : M.force w NotIso.t6F) : M.force w NotIso.c1F := by
  have h5 : M.force w t5 := Or.inr h4
  have h3 : M.force w t3 := h6 w (M.refl_i w) h5
  exact le_of_deriv e_le_c1 M w (le_of_deriv D5_and_3_4.1 M w ⟨h3, h4⟩)

theorem meet_al_be : LaxInfinite.Le (alF.and beF) NotIso.c1F := fun _ _ h =>
  h.1.elim id fun h4 => h.2.elim id fun hgt => key46 h4 hgt.2

theorem meet_al_ga : LaxInfinite.Le (alF.and gaF) NotIso.c1F := fun _ _ h =>
  h.1.elim id fun h4 => h.2.elim id fun hti => key46 h4 hti.1

theorem meet_be_ga : LaxInfinite.Le (beF.and gaF) NotIso.c1F := fun M w h =>
  h.1.elim id fun hgt => h.2.elim id fun hti => hti.2 w (M.refl_i w) hgt.1

/-- `(∈S, {e})` under a fallible top: `α ⊬ c1` at world 0. -/
def K_al : FinCM := ⟨3, [(0, 1), (0, 2), (1, 2)], [(1, 2)], [2], []⟩
/-- `(∈S, {n, e})` under a fallible top: `β ⊬ c1` at world 0. -/
def K_be : FinCM := ⟨4, [(0, 1), (0, 2), (0, 3), (2, 3)], [(2, 3)], [3], []⟩
/-- `(∈S, {(∉S, {n, e})})` under a fallible top: `γ ⊬ c1` at world 0. -/
def K_ga : FinCM :=
  ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (3, 4)], [(1, 4), (3, 4)], [4], []⟩

theorem nle_al_c1 : ¬ LaxInfinite.Le alF NotIso.c1F :=
  not_le_of_check (M := K_al) (w := 0) (by decide)
theorem nle_be_c1 : ¬ LaxInfinite.Le beF NotIso.c1F :=
  not_le_of_check (M := K_be) (w := 0) (by decide)
theorem nle_ga_c1 : ¬ LaxInfinite.Le gaF NotIso.c1F :=
  not_le_of_check (M := K_ga) (w := 0) (by decide)

/-- `⟦◯t3⟧`. -/
def C1 : RNClass := cls NotIso.c1F rfl

/-- **`[◯t3, ⊤]` has no core.** -/
theorem c1_ici_no_core : ¬ HasCore (Set.Ici C1) :=
  no_core_of_three
    (ptq_not_bot (q := NotIso.c1F) (hq := rfl) (h := rfl)
      (hle := Deriv.orIntro1 (Deriv.iden (.head _))) nle_al_c1)
    (ptq_not_bot (q := NotIso.c1F) (hq := rfl) (h := rfl)
      (hle := Deriv.orIntro1 (Deriv.iden (.head _))) nle_be_c1)
    (ptq_not_bot (q := NotIso.c1F) (hq := rfl) (h := rfl)
      (hle := Deriv.orIntro1 (Deriv.iden (.head _))) nle_ga_c1)
    (ptq_disj_le meet_al_be) (ptq_disj_le meet_al_ga) (ptq_disj_le meet_be_ga)

/-- **Cell `c1 = ◯t3`: `[◯t3, ⊤] ≇ F0`.** -/
theorem c1_filter_not_iso : ¬ Nonempty (Set.Ici C1 ≃o RNClass) :=
  fun ⟨f⟩ => c1_ici_no_core (hasCore_of_iso f NotIso.rnclass_core)

/-! ## 8. The proposed next statement (OPEN, not proved here)

If `[p, ⊤] ≅ F0` by `f`, put `a = f(◯⊥)`, `d = f(¬◯⊥)`, `d₄ = f(t4) = d ↠ p`.
Transported from F0: `[p, ⊤] = {p, d} ∪ ↑a`, so `d` covers `p` and is
meet-prime (two elements not below `d` join with `p` above `a`).  The
statement below then gives `◯d ⊢ d` or `◯d₄ ⊢ d₄`.  In F0 itself (`p = ⊥`)
the second holds: `◯¬¬◯⊥ ⊢ ¬¬◯⊥` (`pen_nn_closed`), and `◯¬◯⊥ ⊬ ¬◯⊥`. -/

/-- **Obstruction A** (OPEN; proposed).  For `d` covering `p`, meet-prime
(stated negatively, as it is obtained), with `d₄ = d ↠ p`:

    ¬ (◯d ⊢ d)  and  ¬ (◯d₄ ⊢ d₄)   is impossible.

Planned proof, one model construction: for `w ⊨ d`, add a root `r` below `w`
whose only `Rₘ`-successor is itself.  Then `r ⊨ ◯d ↠ d`; meet-primality puts
`◯d ↠ d` below `d`, so `r ⊨ d`; covering gives `d ⊢ p ∨ ◯d₄`, so
`r ⊨ p ∨ d₄`, hence `w ⊨ d ∧ d₄ ⊢ p`; so `d ⊢ p`, a contradiction. -/
def ObstructionA : Prop :=
  ∀ p d : PLLFormula, atomFree p = true → atomFree d = true →
    LaxInfinite.Le p d → ¬ LaxInfinite.Le d p →
    (∀ x : PLLFormula, atomFree x = true → LaxInfinite.Le p x → LaxInfinite.Le x d →
      ¬ LaxInfinite.Le x p → LaxInfinite.Le d x) →
    (∀ x y : PLLFormula, atomFree x = true → atomFree y = true →
      ¬ LaxInfinite.Le x d → ¬ LaxInfinite.Le y d → ¬ LaxInfinite.Le (x.and y) d) →
    ¬ LaxInfinite.Le (.somehow d) d →
    ¬ LaxInfinite.Le (.somehow (d.ifThen p)) (d.ifThen p) → False

/-- **Consistency check of `ObstructionA` against F0 itself** (`p = ⊥`,
`d = ¬◯⊥`, `d ↠ ⊥ = ¬¬◯⊥`): the first alternative fails, the second holds,
as it must, since `F0 ≅ F0`. -/
theorem obstructionA_F0_case :
    ¬ LaxInfinite.Le (.somehow ne) ne ∧
      LaxInfinite.Le (.somehow (ne.ifThen .falsePLL)) (ne.ifThen .falsePLL) :=
  ⟨fun h => nle_t3_ne (LaxInfinite.Le.trans (le_of_deriv T6.t3_le_u) h),
   le_of_deriv pen_nn_closed⟩

/-! ## 9. Transport of the bottom of F0 along `F0 ≅ [p, ⊤]`

For `f : F0 ≃o [p, ⊤]` the images `a = f(◯⊥)`, `d = f(¬◯⊥)`, `d₄ = f(t4)`,
`a₃ = f(t3)` carry the bottom of F0 into `[p, ⊤]`:

    [p, ⊤] = {p, d} ∪ ↑a,     ↑a = {a, d₄} ∪ ↑a₃,     d₄ = d ⇨ p,     d = d₄ ⇨ p,

so `d` covers `p` and is meet-prime.  Order-only arguments: an order
isomorphism preserves `⊥` and the Heyting implication, both being order-defined. -/

open F0Nuclear (box le_box)

/-- `F0 = {⊥, ¬◯⊥} ∪ ↑◯⊥`. -/
theorem f0_split (y : RNClass) : y = ⊥ ∨ y = NE ∨ E ≤ y := by
  rcases classify_low y with h | h | h | h | h
  · exact Or.inr (Or.inr (le_trans E_le_T3 h))
  · exact Or.inl h
  · exact Or.inr (Or.inr (le_of_eq h.symm))
  · exact Or.inr (Or.inl h)
  · refine Or.inr (Or.inr ?_)
    rw [h]
    exact le_of_deriv D4_below_1

/-- `↑◯⊥ = {◯⊥, t4} ∪ ↑t3`. -/
theorem f0_split_e {y : RNClass} (hy : E ≤ y) : y = E ∨ y = T4c ∨ T3 ≤ y := by
  rcases classify_low y with h | h | h | h | h
  · exact Or.inr (Or.inr h)
  · rw [h] at hy
    exact absurd hy nle_e_bot
  · exact Or.inl h
  · rw [h] at hy
    exact absurd hy nle_e_ne
  · exact Or.inr (Or.inl h)

/-- `¬¬¬◯⊥ ⊣⊢ ¬◯⊥` read as `¬t2 = t4`: `t2 ⇨ ⊥ = t4`. -/
theorem ne_himp_bot : NE ⇨ ⊥ = T4c := by
  show F0Nuclear.himp NE ⊥ = T4c
  exact Quotient.sound (show LaxInfinite.LaxEquiv (ne.ifThen .falsePLL) t4 from
    ⟨fun M _ h v hv h3 => h3.elim id fun hn => M.force_of_fallible (h v hv hn),
     fun M _ h v hv hn => hn v (M.refl_i v) (h v hv (Or.inr hn))⟩)

/-- `t4 ⇨ ⊥ = t2`. -/
theorem t4_himp_bot : T4c ⇨ ⊥ = NE := by
  show F0Nuclear.himp T4c ⊥ = NE
  exact Quotient.sound (show LaxInfinite.LaxEquiv (t4.ifThen .falsePLL) ne from
    ⟨fun M _ h v hv he => h v hv (fun u hu _ => M.force_hered hu he),
     fun M _ h v hv h4 => h v hv (h4 v (M.refl_i v)
       (Or.inr fun u hu he => h u (M.trans_i hv hu) he))⟩)

section Transport

variable {p : RNClass} (f : RNClass ≃o Set.Ici p)

/-- The least element of `[p, ⊤]`. -/
def botI (p : RNClass) : Set.Ici p := ⟨p, Set.self_mem_Ici⟩

theorem iso_bot : f ⊥ = botI p :=
  le_antisymm (f.le_symm_apply.mp bot_le) (f ⊥).2

theorem iso_le {x y : RNClass} : (f x).1 ≤ (f y).1 ↔ x ≤ y := f.le_iff_le

/-- **An order isomorphism onto `[p, ⊤]` carries the Heyting implication.** -/
theorem iso_himp (x y : RNClass) : (f (x ⇨ y)).1 = (f x).1 ⇨ (f y).1 := by
  apply le_antisymm
  · rw [le_himp_iff]
    have hW : p ≤ (f (x ⇨ y)).1 ⊓ (f x).1 := le_inf (f (x ⇨ y)).2 (f x).2
    have h1 : (⟨_, hW⟩ : Set.Ici p) ≤ f (x ⇨ y) := by
      show _ ≤ (f (x ⇨ y)).1
      exact inf_le_left
    have h2 : (⟨_, hW⟩ : Set.Ici p) ≤ f x := by
      show _ ≤ (f x).1
      exact inf_le_right
    have h3 : f.symm ⟨_, hW⟩ ≤ y :=
      le_trans (le_inf (f.symm_apply_le.mpr h1) (f.symm_apply_le.mpr h2)) himp_inf_le
    exact f.symm_apply_le.mp h3
  · have hZ : p ≤ (f x).1 ⇨ (f y).1 := le_trans (f y).2 le_himp
    have hfz : f (f.symm ⟨_, hZ⟩) = ⟨_, hZ⟩ := f.apply_symm_apply _
    have hzx : f.symm ⟨_, hZ⟩ ⊓ x ≤ y := by
      apply f.le_iff_le.mp
      have ha : (f (f.symm ⟨_, hZ⟩ ⊓ x)).1 ≤ (f x).1 ⇨ (f y).1 := by
        have := f.monotone (inf_le_left : f.symm ⟨_, hZ⟩ ⊓ x ≤ f.symm ⟨_, hZ⟩)
        rw [hfz] at this
        exact this
      have hb : (f (f.symm ⟨_, hZ⟩ ⊓ x)).1 ≤ (f x).1 := f.monotone inf_le_right
      show (f (f.symm ⟨_, hZ⟩ ⊓ x)).1 ≤ (f y).1
      exact le_trans (le_inf ha hb) himp_inf_le
    have h7 := f.monotone (le_himp_iff.mpr hzx)
    rw [hfz] at h7
    exact h7

/-- **`[p, ⊤] = {p, d} ∪ ↑a`.** -/
theorem iso_split (X : RNClass) (hX : p ≤ X) : X = p ∨ X = (f NE).1 ∨ (f E).1 ≤ X := by
  have hfx : f (f.symm ⟨X, hX⟩) = ⟨X, hX⟩ := f.apply_symm_apply _
  rcases f0_split (f.symm ⟨X, hX⟩) with h | h | h
  · left
    have := congrArg Subtype.val hfx
    rw [h, iso_bot f] at this
    exact this.symm
  · right
    left
    have := congrArg Subtype.val hfx
    rw [h] at this
    exact this.symm
  · right
    right
    have := f.monotone h
    rw [hfx] at this
    exact this

/-- **`↑a = {a, d₄} ∪ ↑a₃`.** -/
theorem iso_split_a (X : RNClass) (hX : (f E).1 ≤ X) :
    X = (f E).1 ∨ X = (f T4c).1 ∨ (f T3).1 ≤ X := by
  have hX' : p ≤ X := le_trans (f E).2 hX
  have hfx : f (f.symm ⟨X, hX'⟩) = ⟨X, hX'⟩ := f.apply_symm_apply _
  have hE : E ≤ f.symm ⟨X, hX'⟩ := f.le_symm_apply.mpr hX
  rcases f0_split_e hE with h | h | h
  · left
    have := congrArg Subtype.val hfx
    rw [h] at this
    exact this.symm
  · right
    left
    have := congrArg Subtype.val hfx
    rw [h] at this
    exact this.symm
  · right
    right
    have := f.monotone h
    rw [hfx] at this
    exact this

theorem Ai_nle_Di : ¬ (f E).1 ≤ (f NE).1 := fun h => nle_e_ne ((iso_le f).mp h)
theorem Di_nle_D4i : ¬ (f NE).1 ≤ (f T4c).1 := fun h => nle_ne_t4 ((iso_le f).mp h)
theorem D4i_nle_Ai : ¬ (f T4c).1 ≤ (f E).1 := fun h => nle_t4_e ((iso_le f).mp h)
theorem Ai_le_D4i : (f E).1 ≤ (f T4c).1 := (iso_le f).mpr (le_of_deriv D4_below_1)
theorem Ai_le_A3i : (f E).1 ≤ (f T3).1 := (iso_le f).mpr E_le_T3
theorem Di_le_A3i : (f NE).1 ≤ (f T3).1 := (iso_le f).mpr (le_of_deriv D3_below_2)

theorem Di_nle_p : ¬ (f NE).1 ≤ p := fun h => by
  have h' : (f NE).1 ≤ (f ⊥).1 := by
    rw [iso_bot f]
    exact h
  exact nle_ne_bot ((iso_le f).mp h')

/-- **`d` covers `p`.** -/
theorem iso_cover (X : RNClass) (h1 : p ≤ X) (h2 : X ≤ (f NE).1) : X = p ∨ X = (f NE).1 := by
  rcases iso_split f X h1 with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd (le_trans h h2) (Ai_nle_Di f)

/-- **`d` is meet-prime** (negative form). -/
theorem iso_prime (Z1 Z2 : RNClass) (h1 : ¬ Z1 ≤ (f NE).1) (h2 : ¬ Z2 ≤ (f NE).1) :
    ¬ Z1 ⊓ Z2 ≤ (f NE).1 := by
  have k : ∀ Z : RNClass, ¬ Z ≤ (f NE).1 → (f E).1 ≤ p ⊔ Z := fun Z hZ => by
    rcases iso_split f (p ⊔ Z) le_sup_left with h | h | h
    · exact absurd (le_trans (le_trans le_sup_right (le_of_eq h)) (f NE).2) hZ
    · exact absurd (le_trans le_sup_right (le_of_eq h)) hZ
    · exact h
  intro h12
  apply Ai_nle_Di f
  calc (f E).1 ≤ (p ⊔ Z1) ⊓ (p ⊔ Z2) := le_inf (k Z1 h1) (k Z2 h2)
    _ = p ⊔ Z1 ⊓ Z2 := (sup_inf_left p Z1 Z2).symm
    _ ≤ (f NE).1 := sup_le (f NE).2 h12

/-- **`d₄ = d ⇨ p`.** -/
theorem Di_himp : (f NE).1 ⇨ p = (f T4c).1 := by
  have h := iso_himp f NE ⊥
  rw [ne_himp_bot, iso_bot f] at h
  exact h.symm

/-- **`d = d₄ ⇨ p`.** -/
theorem D4i_himp : (f T4c).1 ⇨ p = (f NE).1 := by
  have h := iso_himp f T4c ⊥
  rw [t4_himp_bot, iso_bot f] at h
  exact h.symm

end Transport

/-! ## 10. `ObstructionA` PROVED: a new root below a `d`-world

The root `r` sees `w` and everything above it; its only `Rₘ`-successor is
itself, so `r ⊨ ◯φ` gives `r ⊨ φ`.  The old worlds keep their forcing. -/

namespace RootExt

variable (M : ConstraintModel) (w : M.W)

def ri : Option M.W → Option M.W → Prop
  | none, none => True
  | none, some v => M.Ri w v
  | some u, some v => M.Ri u v
  | some _, none => False

def rm : Option M.W → Option M.W → Prop
  | none, none => True
  | some u, some v => M.Rm u v
  | _, _ => False

def fl : Option M.W → Prop
  | none => False
  | some u => u ∈ M.F

def vl (a : String) : Option M.W → Prop
  | none => False
  | some u => u ∈ M.V a

theorem ri_refl : ∀ x : Option M.W, ri M w x x
  | none => trivial
  | some u => M.refl_i u

theorem rm_refl : ∀ x : Option M.W, rm M x x
  | none => trivial
  | some u => M.refl_m u

theorem ri_trans {x y z : Option M.W} (h1 : ri M w x y) (h2 : ri M w y z) : ri M w x z := by
  cases x <;> cases y <;> cases z <;>
    first
    | exact trivial
    | exact M.trans_i h1 h2
    | exact h2
    | exact False.elim h1

theorem rm_trans {x y z : Option M.W} (h1 : rm M x y) (h2 : rm M y z) : rm M x z := by
  cases x <;> cases y <;> cases z <;>
    first
    | exact trivial
    | exact M.trans_m h1 h2
    | exact False.elim h1
    | exact False.elim h2

theorem rm_sub {x y : Option M.W} (h : rm M x y) : ri M w x y := by
  cases x <;> cases y <;>
    first
    | exact trivial
    | exact M.sub_mi h
    | exact False.elim h

theorem fl_hered {x y : Option M.W} (h : ri M w x y) (hx : fl M x) : fl M y := by
  cases x <;> cases y <;>
    first
    | exact M.hered_F h hx
    | exact False.elim hx
    | exact False.elim h

theorem vl_hered {a : String} {x y : Option M.W} (h : ri M w x y) (hx : vl M a x) :
    vl M a y := by
  cases x <;> cases y <;>
    first
    | exact M.hered_V h hx
    | exact False.elim hx
    | exact False.elim h

theorem vl_full {a : String} {x : Option M.W} (hx : fl M x) : vl M a x := by
  cases x with
  | none => exact False.elim hx
  | some u => exact M.full_F hx

/-- The extension by a root below `w`. -/
def ext : ConstraintModel where
  W := Option M.W
  Ri := ri M w
  Rm := rm M
  F := {x | fl M x}
  V a := {x | vl M a x}
  refl_i := ri_refl M w
  trans_i := ri_trans M w
  refl_m := rm_refl M
  trans_m := rm_trans M
  sub_mi := rm_sub M w
  hered_F := fun h hx => fl_hered M w h hx
  hered_V := fun h hx => vl_hered M w h hx
  full_F := fun hx => vl_full M hx

/-- The old worlds keep their forcing. -/
theorem old_force : ∀ (φ : PLLFormula) (u : M.W), (ext M w).force (some u) φ ↔ M.force u φ
  | .prop _, _ => Iff.rfl
  | .falsePLL, _ => Iff.rfl
  | .and A B, u => and_congr (old_force A u) (old_force B u)
  | .or A B, u => or_congr (old_force A u) (old_force B u)
  | .ifThen A B, u =>
      ⟨fun h v huv hA => (old_force B v).mp (h (some v) huv ((old_force A v).mpr hA)),
       fun h y hy hA => by
        cases y with
        | none => exact False.elim hy
        | some v => exact (old_force B v).mpr (h v hy ((old_force A v).mp hA))⟩
  | .somehow A, u =>
      ⟨fun h v huv => by
        obtain ⟨y, hy, hA⟩ := h (some v) huv
        cases y with
        | none => exact False.elim hy
        | some u' => exact ⟨u', hy, (old_force A u').mp hA⟩,
       fun h y hy => by
        cases y with
        | none => exact False.elim hy
        | some v =>
            obtain ⟨u', hu', hA⟩ := h v hy
            exact ⟨some u', hu', (old_force A u').mpr hA⟩⟩

theorem root_box {φ : PLLFormula} (h : (ext M w).force none (.somehow φ)) :
    (ext M w).force none φ := by
  obtain ⟨y, hy, hφ⟩ := h none trivial
  cases y with
  | none => exact hφ
  | some _ => exact False.elim hy

theorem root_hered {φ : PLLFormula} (h : (ext M w).force none φ) : M.force w φ :=
  (old_force M w φ w).mp
    ((ext M w).force_hered (show (ext M w).Ri none (some w) from M.refl_i w) h)

theorem root_imp_box {d : PLLFormula} (hw : M.force w d) :
    (ext M w).force none ((PLLFormula.somehow d).ifThen d) := by
  show ∀ y, (ext M w).Ri none y → (ext M w).force y (.somehow d) → (ext M w).force y d
  intro y hy hb
  cases y with
  | none => exact root_box M w hb
  | some v => exact (old_force M w d v).mpr (M.force_hered hy hw)

end RootExt

/-- **`ObstructionA` PROVED.** -/
theorem obstructionA : ObstructionA := by
  unfold ObstructionA
  intro p d hp hd hpd hdp hcov hprime h1 h2
  have hz : ¬ ¬ LaxInfinite.Le ((PLLFormula.somehow d).ifThen d) d := fun hn =>
    hprime ((PLLFormula.somehow d).ifThen d) (PLLFormula.somehow d)
      (by simp [atomFree, hd]) (by simp [atomFree, hd]) hn h1
      (fun M w h => h.1 w (M.refl_i w) h.2)
  have hc : ¬ ¬ LaxInfinite.Le d (p.or (.somehow (d.ifThen p))) := fun hn => by
    have hxp : ¬ LaxInfinite.Le (d.and (p.or (.somehow (d.ifThen p)))) p := fun hle =>
      h2 (fun M w hb v hwv hdv => hle M v ⟨hdv, Or.inr (M.force_hered hwv hb)⟩)
    have hpx : LaxInfinite.Le p (d.and (p.or (.somehow (d.ifThen p)))) :=
      fun M w hpw => ⟨hpd M w hpw, Or.inl hpw⟩
    have hxd : LaxInfinite.Le (d.and (p.or (.somehow (d.ifThen p)))) d := fun _ _ h => h.1
    have hdx := hcov (d.and (p.or (.somehow (d.ifThen p)))) (by simp [atomFree, hp, hd])
      hpx hxd hxp
    exact hn (fun M w hdw => (hdx M w hdw).2)
  apply hz
  intro hz'
  apply hc
  intro hc'
  apply hdp
  intro M w hw
  have hr : (RootExt.ext M w).force none d :=
    hz' (RootExt.ext M w) none (RootExt.root_imp_box M w hw)
  rcases hc' (RootExt.ext M w) none hr with hp' | hb
  · exact RootExt.root_hered M w hp'
  · have h4 : M.force w (d.ifThen p) := RootExt.root_hered M w (RootExt.root_box M w hb)
    exact h4 w (M.refl_i w) hw

/-! ## 11. The case analysis at an isomorphism -/

theorem box_mono {x y : RNClass} (h : x ≤ y) : box x ≤ box y := by
  induction x using Quotient.ind
  induction y using Quotient.ind
  exact fun M _ hb v hv => (hb v hv).imp fun _ hu => ⟨hu.1, h M _ hu.2⟩

/-- `x` is meet-prime (negative form). -/
def MeetPrime (x : RNClass) : Prop := ∀ y z : RNClass, ¬ y ≤ x → ¬ z ≤ x → ¬ y ⊓ z ≤ x

/-- `v` covers `u`. -/
def CoversC (u v : RNClass) : Prop := u < v ∧ ∀ x : RNClass, u ≤ x → x ≤ v → x = u ∨ x = v

section Cases

variable {p : RNClass} (f : RNClass ≃o Set.Ici p)

/-- **`ObstructionA` at an isomorphism**: not both `◯d ⊬ d` and `◯d₄ ⊬ d₄`. -/
theorem iso_obstruction (h1 : ¬ box (f NE).1 ≤ (f NE).1)
    (h2 : ¬ box (f T4c).1 ≤ (f T4c).1) : False := by
  obtain ⟨p0, rfl⟩ := Quotient.exists_rep p
  obtain ⟨d0, hd0⟩ := Quotient.exists_rep (f NE).1
  have hpd : (Quotient.mk _ p0 : RNClass) ≤ Quotient.mk _ d0 := by
    rw [hd0]
    exact (f NE).2
  have hdp : ¬ (Quotient.mk _ d0 : RNClass) ≤ Quotient.mk _ p0 := by
    rw [hd0]
    exact Di_nle_p f
  refine obstructionA p0.1 d0.1 p0.2 d0.2 hpd hdp ?_ ?_ ?_ ?_
  · intro x hx hx1 hx2 hx3
    have h2' : cls x hx ≤ (f NE).1 := by
      have : cls x hx ≤ Quotient.mk _ d0 := hx2
      rwa [hd0] at this
    rcases iso_cover f (cls x hx) hx1 h2' with h | h
    · exact absurd (le_of_eq h) hx3
    · have : (Quotient.mk _ d0 : RNClass) ≤ cls x hx := by
        rw [hd0, h]
      exact this
  · intro x y hx hy hx1 hy1 hxy
    have hx1' : ¬ cls x hx ≤ (f NE).1 := by
      have : ¬ cls x hx ≤ Quotient.mk _ d0 := hx1
      rwa [hd0] at this
    have hy1' : ¬ cls y hy ≤ (f NE).1 := by
      have : ¬ cls y hy ≤ Quotient.mk _ d0 := hy1
      rwa [hd0] at this
    apply iso_prime f (cls x hx) (cls y hy) hx1' hy1'
    have : cls x hx ⊓ cls y hy ≤ Quotient.mk _ d0 := hxy
    rwa [hd0] at this
  · have : ¬ box (Quotient.mk _ d0) ≤ Quotient.mk _ d0 := by
      rw [hd0]
      exact h1
    exact this
  · have : ¬ box (Quotient.mk _ d0 ⇨ Quotient.mk _ p0) ≤ Quotient.mk _ d0 ⇨ Quotient.mk _ p0 := by
      rw [hd0, Di_himp f]
      exact h2
    exact this

/-- **The case analysis** (every `p`, no density used).  With `a = f(◯⊥)`,
`d = f(¬◯⊥)`, `d₄ = f(t4)`:

    ◯p = p  ∨  ◯p = d  ∨  ◯p = d₄  ∨  (◯p = a ∧ ◯d₄ = d₄).

The remaining possibility `a₃ ≤ ◯p` is excluded by `ObstructionA`.  F0
itself (`p = ⊥`, `◯⊥ = t1`, `◯t4 = t4`) is in the last case. -/
theorem iso_cases :
    box p = p ∨ box p = (f NE).1 ∨ box p = (f T4c).1 ∨
      (box p = (f E).1 ∧ box (f T4c).1 = (f T4c).1) := by
  have hpD : p ≤ (f NE).1 := (f NE).2
  have hpD4 : p ≤ (f T4c).1 := (f T4c).2
  rcases iso_split f (box p) (le_box p) with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · rcases iso_split_a f (box p) h with h' | h' | h'
    · refine Or.inr (Or.inr (Or.inr ⟨h', ?_⟩))
      have hd1 : ¬ box (f NE).1 ≤ (f NE).1 := fun hb =>
        Ai_nle_Di f (le_trans h (le_trans (box_mono hpD) hb))
      rcases iso_split_a f (box (f T4c).1) (le_trans (Ai_le_D4i f) (le_box _)) with k | k | k
      · exfalso
        apply D4i_nle_Ai f
        rw [← k]
        exact le_box _
      · exact k
      · exfalso
        exact iso_obstruction f hd1
          (fun hb => Di_nle_D4i f (le_trans (Di_le_A3i f) (le_trans k hb)))
    · exact Or.inr (Or.inr (Or.inl h'))
    · exfalso
      exact iso_obstruction f
        (fun hb => Ai_nle_Di f (le_trans (Ai_le_A3i f)
          (le_trans h' (le_trans (box_mono hpD) hb))))
        (fun hb => Di_nle_D4i f (le_trans (Di_le_A3i f)
          (le_trans h' (le_trans (box_mono hpD4) hb))))

/-- **Case `◯p = d`**: then `◯p` covers `p` and is meet-prime. -/
theorem case_d_shape (h : box p = (f NE).1) : CoversC p (box p) ∧ MeetPrime (box p) := by
  rw [h]
  refine ⟨⟨lt_of_le_not_ge (f NE).2 (Di_nle_p f), fun x h1 h2 => iso_cover f x h1 h2⟩,
    fun y z hy hz => iso_prime f y z hy hz⟩

/-- **Case `◯p = d₄`**: then the gap `◯p ⇨ p` (which is `d`) covers `p`. -/
theorem case_d4_shape (h : box p = (f T4c).1) : CoversC p (box p ⇨ p) := by
  rw [h, D4i_himp f]
  exact ⟨lt_of_le_not_ge (f NE).2 (Di_nle_p f), fun x h1 h2 => iso_cover f x h1 h2⟩

/-- **Case `◯p = a`**: then `◯p` is a big atom of `[p, ⊤]`. -/
theorem case_a_shape (h : box p = (f E).1) : BigAtom (⟨box p, le_box p⟩ : Set.Ici p) := by
  refine ⟨fun hb => ?_, ⟨(f NE).1, (f NE).2⟩, fun x => ?_⟩
  · have h1 : (f E).1 ≤ (f ⊥).1 := by
      rw [← h, iso_bot f]
      exact hb (botI p)
    exact nle_e_bot ((iso_le f).mp h1)
  · rcases iso_split f x.1 x.2 with k | k | k
    · refine Or.inr (Or.inl fun w => ?_)
      show x.1 ≤ w.1
      rw [k]
      exact w.2
    · exact Or.inr (Or.inr (Subtype.ext k))
    · refine Or.inl ?_
      show box p ≤ x.1
      rw [h]
      exact k

end Cases

/-! ## 12. Cells for the four cases

`iso_cases` leaves four shapes for a counterexample `p`, each a property of
`◯p` (`case_d_shape`, `case_d4_shape`, `case_a_shape`):

* (i)   `◯p = p`;
* (ii)  `◯p = d`: `◯p` covers `p` and is meet-prime;
* (iii) `◯p = d₄`: the gap `◯p ⇨ p` covers `p`;
* (iv)  `◯p = a`, `◯d₄ = d₄`: `◯p` is a big atom of `[p, ⊤]` (F0 itself, `p = ⊥`).

The cells: (i) is realised by the dense, `◯`-fixed `σⁿ(c1)`, every `n`, and
each is still refuted (three pairwise disjoint elements); (ii)–(iv) fail
at the designed dense cells `t3` and `t5` for the stated local reason; `t5`
is refuted outright as well. -/

/-! ### The A-translation is monotone on the semantic order -/

namespace RelF

variable (M : ConstraintModel) (q : PLLFormula)

/-- `M` with the `q`-worlds made fallible. -/
def ext : ConstraintModel where
  W := M.W
  Ri := M.Ri
  Rm := M.Rm
  F := {w | M.force w q}
  V a := {w | w ∈ M.V a ∨ M.force w q}
  refl_i := M.refl_i
  trans_i := M.trans_i
  refl_m := M.refl_m
  trans_m := M.trans_m
  sub_mi := M.sub_mi
  hered_F := fun h hw => M.force_hered h hw
  hered_V := fun h hw =>
    hw.elim (fun h' => Or.inl (M.hered_V h h')) (fun h' => Or.inr (M.force_hered h h'))
  full_F := fun hw => Or.inr hw

/-- On closed formulas, forcing in `ext M q` is forcing of `φ[⊥ := q]` in `M`. -/
theorem force_ext : ∀ (φ : PLLFormula), atomFree φ = true → ∀ w : M.W,
    (ext M q).force w φ ↔ M.force w (Sig.subBot q φ)
  | .prop _, h, _ => nomatch h
  | .falsePLL, _, _ => Iff.rfl
  | .and A B, h, w => by
      have h' : (atomFree A && atomFree B) = true := h
      obtain ⟨hA, hB⟩ := (Bool.and_eq_true _ _).mp h'
      exact and_congr (force_ext A hA w) (force_ext B hB w)
  | .or A B, h, w => by
      have h' : (atomFree A && atomFree B) = true := h
      obtain ⟨hA, hB⟩ := (Bool.and_eq_true _ _).mp h'
      exact or_congr (force_ext A hA w) (force_ext B hB w)
  | .ifThen A B, h, w => by
      have h' : (atomFree A && atomFree B) = true := h
      obtain ⟨hA, hB⟩ := (Bool.and_eq_true _ _).mp h'
      exact ⟨fun k v hv ha => (force_ext B hB v).mp (k v hv ((force_ext A hA v).mpr ha)),
        fun k v hv ha => (force_ext B hB v).mpr (k v hv ((force_ext A hA v).mp ha))⟩
  | .somehow A, h, w =>
      ⟨fun k v hv => (k v hv).imp fun u hu => ⟨hu.1, (force_ext A h u).mp hu.2⟩,
       fun k v hv => (k v hv).imp fun u hu => ⟨hu.1, (force_ext A h u).mpr hu.2⟩⟩

end RelF

/-- **`φ ↦ φ[⊥ := q]` is monotone on the semantic order** of closed formulas. -/
theorem subBot_le (q : PLLFormula) {a b : PLLFormula} (ha : atomFree a = true)
    (hb : atomFree b = true) (h : LaxInfinite.Le a b) :
    LaxInfinite.Le (Sig.subBot q a) (Sig.subBot q b) := fun M w hw =>
  (RelF.force_ext M q b hb w).mp (h (RelF.ext M q) w ((RelF.force_ext M q a ha w).mpr hw))

theorem sigN_le : ∀ (n : Nat) {a b : PLLFormula}, atomFree a = true → atomFree b = true →
    LaxInfinite.Le a b → LaxInfinite.Le (Sig.sigN n a) (Sig.sigN n b)
  | 0, _, _, _, _, h => h
  | n + 1, _, _, ha, hb, h =>
      sigN_le n (Sig.sig_vf ha) (Sig.sig_vf hb) (subBot_le t3 ha hb h)

theorem sigN_somehow : ∀ (n : Nat) (φ : PLLFormula),
    Sig.sigN n (.somehow φ) = .somehow (Sig.sigN n φ)
  | 0, _ => rfl
  | n + 1, φ => sigN_somehow n (Sig.sig φ)

/-! ### Case (i), `◯p = p`: realised by `σⁿ(c1)`, refuted -/

theorem rf_al_c1 : Refutes alF NotIso.c1F :=
  refutes_of_check (M := K_al) (w := 0) (by decide)
theorem rf_be_c1 : Refutes beF NotIso.c1F :=
  refutes_of_check (M := K_be) (w := 0) (by decide)
theorem rf_ga_c1 : Refutes gaF NotIso.c1F :=
  refutes_of_check (M := K_ga) (w := 0) (by decide)

/-- `⟦σⁿ(c1)⟧`. -/
def C1n (n : Nat) : RNClass := cls (Sig.sigN n NotIso.c1F) (Sig.sigN_vf n rfl)

/-- `σⁿ(c1)` is `◯`-fixed. -/
theorem C1n_box (n : Nat) : box (C1n n) = C1n n := by
  refine le_antisymm ?_ (le_box _)
  show LaxInfinite.Le (.somehow (Sig.sigN n (.somehow t3))) (Sig.sigN n (.somehow t3))
  rw [sigN_somehow]
  intro M w h v hv
  obtain ⟨u, hvu, hu⟩ := h v hv
  obtain ⟨u', huu', hu'⟩ := hu u (M.refl_i u)
  exact ⟨u', M.trans_m hvu huu', hu'⟩

theorem t3_le_sigN_bot : ∀ n : Nat, Deriv [t3] (Sig.sigN (n + 1) .falsePLL)
  | 0 => Deriv.iden (.head _)
  | n + 1 => Deriv.cutHead (t3_le_sigN_bot n) (Sig.sigN_bot_strict (n + 1)).1

/-- `σⁿ(c1)` is dense. -/
theorem C1n_dense : ∀ n : Nat, T3 ≤ C1n n
  | 0 => le_of_deriv NotIso.t3_le_c1
  | n + 1 => le_of_deriv (Deriv.cutHead (t3_le_sigN_bot n) (Sig.sigN_bot_le (n + 1) NotIso.c1F rfl))

theorem C1n_ici_no_core (n : Nat) : ¬ HasCore (Set.Ici (C1n n)) := by
  have hm : ∀ a b : PLLFormula, atomFree a = true → atomFree b = true →
      LaxInfinite.Le (a.and b) NotIso.c1F →
      LaxInfinite.Le ((Sig.sigN n a).and (Sig.sigN n b)) (Sig.sigN n NotIso.c1F) :=
    fun a b ha hb h => by
      have := sigN_le n (a := a.and b) (by simp [atomFree, ha, hb]) rfl h
      rwa [sigN_and] at this
  have hl : ∀ φ : PLLFormula, atomFree φ = true → Deriv [NotIso.c1F] φ →
      Deriv [Sig.sigN n NotIso.c1F] (Sig.sigN n φ) := fun φ hφ h => Sig.sigN_mono n rfl hφ h
  have i1 : Deriv [NotIso.c1F] alF := Deriv.orIntro1 (Deriv.iden (.head _))
  have i2 : Deriv [NotIso.c1F] beF := Deriv.orIntro1 (Deriv.iden (.head _))
  have i3 : Deriv [NotIso.c1F] gaF := Deriv.orIntro1 (Deriv.iden (.head _))
  exact no_core_of_three
    (ptq_not_bot (q := Sig.sigN n NotIso.c1F) (hq := Sig.sigN_vf n rfl)
      (h := Sig.sigN_vf n (φ := alF) rfl) (hle := hl alF rfl i1)
      (not_le_of_refutes (refutes_sigN n rf_al_c1)))
    (ptq_not_bot (q := Sig.sigN n NotIso.c1F) (hq := Sig.sigN_vf n rfl)
      (h := Sig.sigN_vf n (φ := beF) rfl) (hle := hl beF rfl i2)
      (not_le_of_refutes (refutes_sigN n rf_be_c1)))
    (ptq_not_bot (q := Sig.sigN n NotIso.c1F) (hq := Sig.sigN_vf n rfl)
      (h := Sig.sigN_vf n (φ := gaF) rfl) (hle := hl gaF rfl i3)
      (not_le_of_refutes (refutes_sigN n rf_ga_c1)))
    (ptq_disj_le (hm alF beF rfl rfl meet_al_be))
    (ptq_disj_le (hm alF gaF rfl rfl meet_al_ga))
    (ptq_disj_le (hm beF gaF rfl rfl meet_be_ga))

/-- **Case (i) cell, every `n`: `[σⁿ(c1), ⊤] ≇ F0`**, though `σⁿ(c1)` is
dense and `◯`-fixed (`C1n_dense`, `C1n_box`). -/
theorem C1n_filter_not_iso (n : Nat) : ¬ Nonempty (Set.Ici (C1n n) ≃o RNClass) :=
  fun ⟨f⟩ => C1n_ici_no_core n (hasCore_of_iso f NotIso.rnclass_core)

/-! ### The cell `t5`: three pairwise disjoint elements

`t5` covers `t3` (`cover_3_5`).  Above `t5`:

    α₅ = t5 ∨ c1,    β₅ = t5 ∨ (g1 ∧ t6),    γ₅ = t8 = (t5 ∨ t6) ↠ t5.

The meets use `c1 ⊢ t6` (from `c1 ∧ t4 ⊢ ◯⊥`, PROVED here semantically). -/

/-- `t7 = t5 ∨ t6`. -/
def t7F : PLLFormula := t5.or NotIso.t6F
/-- `t8 = t7 ↠ t5`. -/
def t8F : PLLFormula := t7F.ifThen t5
def al5F : PLLFormula := t5.or NotIso.c1F
def be5F : PLLFormula := t5.or (NotIso.g1F.and NotIso.t6F)

/-- `c1 ∧ t4 ⊢ ◯⊥`. -/
theorem c1_t4_e {M : ConstraintModel} {w : M.W} (hc : M.force w NotIso.c1F)
    (h4 : M.force w t4) : M.force w e := by
  intro v hv
  obtain ⟨u, hvu, h3⟩ := hc v hv
  have h4u : M.force u t4 := M.force_hered (M.trans_i hv (M.sub_mi hvu)) h4
  obtain ⟨u', huu', hf⟩ := h4u u (M.refl_i u) h3 u (M.refl_i u)
  exact ⟨u', M.trans_m hvu huu', hf⟩

/-- `c1 ⊢ t6`. -/
theorem c1_t6 {M : ConstraintModel} {w : M.W} (hc : M.force w NotIso.c1F) :
    M.force w NotIso.t6F := fun _ hv h5 =>
  h5.elim id fun h4 => Or.inl (c1_t4_e (M.force_hered hv hc) h4)

theorem meet_al5_be5 : LaxInfinite.Le (al5F.and be5F) t5 := fun M w h =>
  h.1.elim id fun hc => h.2.elim id fun hgt => Or.inl (hgt.1 w (M.refl_i w) hc)

theorem meet_al5_ga5 : LaxInfinite.Le (al5F.and t8F) t5 := fun M w h =>
  h.1.elim id fun hc => h.2 w (M.refl_i w) (Or.inr (c1_t6 hc))

theorem meet_be5_ga5 : LaxInfinite.Le (be5F.and t8F) t5 := fun M w h =>
  h.1.elim id fun hgt => h.2 w (M.refl_i w) (Or.inr hgt.2)

/-- `(∉S, {(∈S, {e}), n})` under a fallible top. -/
def K_F : FinCM :=
  ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 4), (2, 4)], [(0, 4), (2, 4)], [4], []⟩

theorem nle_gt_t5 : ¬ LaxInfinite.Le (NotIso.g1F.and NotIso.t6F) t5 :=
  not_le_of_check (M := K_be) (w := 0) (by decide)
theorem nle_t8_t5 : ¬ LaxInfinite.Le t8F t5 := not_le_of_check (M := K_F) (w := 0) (by decide)
theorem nle_bt5_al5 : ¬ LaxInfinite.Le (.somehow t5) al5F :=
  not_le_of_check (M := K_F) (w := 0) (by decide)
theorem nle_bt5_be5 : ¬ LaxInfinite.Le (.somehow t5) be5F :=
  not_le_of_check (M := K_F) (w := 0) (by decide)

theorem nle_al5_t5 : ¬ LaxInfinite.Le al5F t5 := fun h =>
  NotIso.nle_c1_t5 fun M w hc => h M w (Or.inr hc)
theorem nle_be5_t5 : ¬ LaxInfinite.Le be5F t5 := fun h =>
  nle_gt_t5 fun M w hg => h M w (Or.inr hg)

theorem t5_ici_no_core : ¬ HasCore (Set.Ici T5c) :=
  no_core_of_three
    (ptq_not_bot (q := t5) (hq := rfl) (h := rfl)
      (hle := Deriv.orIntro1 (Deriv.iden (.head _))) nle_al5_t5)
    (ptq_not_bot (q := t5) (hq := rfl) (h := rfl)
      (hle := Deriv.orIntro1 (Deriv.iden (.head _))) nle_be5_t5)
    (ptq_not_bot (q := t5) (hq := rfl) (h := rfl)
      (hle := Deriv.impIntro (Deriv.iden (.tail _ (.head _)))) nle_t8_t5)
    (ptq_disj_le meet_al5_be5) (ptq_disj_le meet_al5_ga5) (ptq_disj_le meet_be5_ga5)

/-- **Cell `t5`: `[t5, ⊤] ≇ F0`.** -/
theorem t5_filter_not_iso : ¬ Nonempty (Set.Ici T5c ≃o RNClass) :=
  fun ⟨f⟩ => t5_ici_no_core (hasCore_of_iso f NotIso.rnclass_core)

/-! ### Case (ii), `◯p` a meet-prime cover of `p`: fails at `t3` and at `t5` -/

/-- **`◯t3 = c1` is not meet-prime**: `α, β ⊬ c1`, `α ∧ β ⊢ c1`. -/
theorem box_t3_not_meetPrime : ¬ MeetPrime (box T3) := fun h =>
  h (cls alF rfl) (cls beF rfl) nle_al_c1 nle_be_c1 meet_al_be

theorem T3_le_T5c : T3 ≤ T5c := le_of_deriv D5_below_3

/-- **`◯t5` does not cover `t5`**: `t5 < t5 ∨ c1 < ◯t5`. -/
theorem box_t5_not_cover : ¬ CoversC T5c (box T5c) := by
  rintro ⟨_, h⟩
  rcases h (T5c ⊔ box T3) le_sup_left (sup_le (le_box _) (box_mono T3_le_T5c)) with k | k
  · exact NotIso.nle_c1_t5 (le_trans le_sup_right (le_of_eq k))
  · exact nle_bt5_al5 (le_of_eq k.symm)

/-! ### Case (iii), the gap `◯p ⇨ p` covers `p`: fails at `t3` -/

/-- **`g1 = ◯t3 ⇨ t3` does not cover `t3`**: `t3 < t5 < g1` (`t3_lt_t5_lt_g1`). -/
theorem gap_t3_not_cover : ¬ CoversC T3 (box T3 ⇨ T3) := by
  rintro ⟨_, h⟩
  rcases h T5c T3_le_T5c (le_of_deriv SigOnto.t5_le_g1F) with k | k
  · exact NotIso.nle_t5_t3 (le_of_eq k)
  · exact NotIso.nle_g1_t5 (le_of_eq k.symm)

/-! ### Case (iv), `◯p` a big atom of `[p, ⊤]`: fails at `t3` and at `t5` -/

theorem dne_of_disj {P : Type} [Preorder P] {u v : P} (hu : ¬ IsBot u) (h : Disj u v) :
    u ≠ v := fun e => hu (h _ le_rfl (le_of_eq e))

/-- **`◯t3 = c1` is not a big atom of `[t3, ⊤]`**: `t5` and `g1` are distinct,
non-least, and not above `c1`. -/
theorem box_t3_not_bigAtom :
    ¬ BigAtom (⟨box T3, le_box T3⟩ : Set.Ici T3) := by
  rintro ⟨_, d, hd⟩
  rcases hd ⟨T5c, T3_le_T5c⟩ with h | h | h1
  · exact NotIso.nle_c1_t5 h
  · exact NotIso.nle_t5_t3 (h ⟨T3, le_refl T3⟩)
  rcases hd ⟨cls NotIso.g1F rfl, le_of_deriv NotIso.t3_le_g1⟩ with h | h | h2
  · exact NotIso.nle_c1_t3 (fun M w hc => (h : LaxInfinite.Le NotIso.c1F NotIso.g1F) M w hc w
      (M.refl_i w) hc)
  · exact NotIso.nle_g1_t3 (h ⟨T3, le_refl T3⟩)
  · exact NotIso.nle_g1_t5 (le_of_eq (congrArg Subtype.val (h2.trans h1.symm)))

/-- **`◯t5` is not a big atom of `[t5, ⊤]`**: `α₅` and `β₅` are distinct,
non-least, and not above `◯t5`. -/
theorem box_t5_not_bigAtom :
    ¬ BigAtom (⟨box T5c, le_box T5c⟩ : Set.Ici T5c) := by
  rintro ⟨_, d, hd⟩
  have hna : ¬ IsBot (ptq t5 rfl al5F rfl (Deriv.orIntro1 (Deriv.iden (.head _)))) :=
    ptq_not_bot nle_al5_t5
  have hnb : ¬ IsBot (ptq t5 rfl be5F rfl (Deriv.orIntro1 (Deriv.iden (.head _)))) :=
    ptq_not_bot nle_be5_t5
  rcases hd (ptq t5 rfl al5F rfl (Deriv.orIntro1 (Deriv.iden (.head _)))) with h | h | h1
  · exact nle_bt5_al5 h
  · exact hna h
  rcases hd (ptq t5 rfl be5F rfl (Deriv.orIntro1 (Deriv.iden (.head _)))) with h | h | h2
  · exact nle_bt5_be5 h
  · exact hnb h
  exact dne_of_disj hna (ptq_disj_le meet_al5_be5) (h1.trans h2.symm)

end FilterIso
end F0
end PLLND

/-! ## Axiom pins -/

#axioms_within PLLND.F0.FilterIso.hasDisjPair_of_iso [propext, Quot.sound]
#axioms_within PLLND.F0.FilterIso.bigAtom_of_iso [propext, Quot.sound]
#axioms_within PLLND.F0.FilterIso.classify_low [propext, Quot.sound]
#axioms_within PLLND.F0.FilterIso.rn_hasDisjPair [propext, Quot.sound]
#axioms_within PLLND.F0.FilterIso.ne_filter_not_iso [propext, Quot.sound]
#axioms_within PLLND.F0.FilterIso.t4_filter_not_iso [propext, Quot.sound]
#axioms_within PLLND.F0.FilterIso.bigAtom_rn [propext, Quot.sound]
#axioms_within PLLND.F0.FilterIso.bigAtom_ici_e [propext, Quot.sound]
#axioms_within PLLND.F0.FilterIso.e_filter_not_iso [propext, Quot.sound]
#axioms_within PLLND.F0.FilterIso.nondense_filter_not_iso [propext, Quot.sound]
#axioms_within PLLND.F0.FilterIso.filterIsoQ_iff_dense [propext, Quot.sound]
#axioms_within PLLND.F0.FilterIso.SigC.orig_sig [propext]
#axioms_within PLLND.F0.FilterIso.refutes_sig [propext]
#axioms_within PLLND.F0.FilterIso.refutes_sigN [propext]
#axioms_within PLLND.F0.FilterIso.refutes_of_check [propext, Quot.sound]
#axioms_within PLLND.F0.FilterIso.twoPairs_sigN [propext, Quot.sound]
#axioms_within PLLND.F0.FilterIso.ici_no_core_of_twoPairs [propext, Quot.sound]
#axioms_within PLLND.F0.FilterIso.twoPairs_t3 [propext, Quot.sound]
#axioms_within PLLND.F0.FilterIso.sigN_filter_not_iso [propext, Quot.sound]
#axioms_within PLLND.F0.FilterIso.sig2_filter_not_iso [propext, Quot.sound]
#axioms_within PLLND.F0.FilterIso.no_core_of_three []
#axioms_within PLLND.F0.FilterIso.meet_al_be [propext]
#axioms_within PLLND.F0.FilterIso.c1_ici_no_core [propext, Quot.sound]
#axioms_within PLLND.F0.FilterIso.c1_filter_not_iso [propext, Quot.sound]
#axioms_within PLLND.F0.FilterIso.obstructionA_F0_case [propext, Quot.sound]
#axioms_within PLLND.F0.FilterIso.ne_himp_bot [propext, Quot.sound]
#axioms_within PLLND.F0.FilterIso.t4_himp_bot [propext, Quot.sound]
#axioms_within PLLND.F0.FilterIso.iso_himp [propext, Quot.sound]
#axioms_within PLLND.F0.FilterIso.iso_split [propext, Quot.sound]
#axioms_within PLLND.F0.FilterIso.iso_split_a [propext, Quot.sound]
#axioms_within PLLND.F0.FilterIso.iso_cover [propext, Quot.sound]
#axioms_within PLLND.F0.FilterIso.iso_prime [propext, Quot.sound]
#axioms_within PLLND.F0.FilterIso.Di_himp [propext, Quot.sound]
#axioms_within PLLND.F0.FilterIso.D4i_himp [propext, Quot.sound]
#axioms_within PLLND.F0.FilterIso.RootExt.old_force [propext]
#axioms_within PLLND.F0.FilterIso.obstructionA [propext]
#axioms_within PLLND.F0.FilterIso.iso_obstruction [propext, Quot.sound]
#axioms_within PLLND.F0.FilterIso.iso_cases [propext, Quot.sound]
#axioms_within PLLND.F0.FilterIso.case_d_shape [propext, Quot.sound]
#axioms_within PLLND.F0.FilterIso.case_d4_shape [propext, Quot.sound]
#axioms_within PLLND.F0.FilterIso.case_a_shape [propext, Quot.sound]
#axioms_within PLLND.F0.FilterIso.RelF.force_ext [propext]
#axioms_within PLLND.F0.FilterIso.subBot_le [propext]
#axioms_within PLLND.F0.FilterIso.sigN_le [propext]
#axioms_within PLLND.F0.FilterIso.C1n_box [propext, Quot.sound]
#axioms_within PLLND.F0.FilterIso.C1n_dense [propext, Quot.sound]
#axioms_within PLLND.F0.FilterIso.C1n_filter_not_iso [propext, Quot.sound]
#axioms_within PLLND.F0.FilterIso.c1_t6 []
#axioms_within PLLND.F0.FilterIso.t5_filter_not_iso [propext, Quot.sound]
#axioms_within PLLND.F0.FilterIso.box_t3_not_meetPrime [propext, Quot.sound]
#axioms_within PLLND.F0.FilterIso.box_t5_not_cover [propext, Quot.sound]
#axioms_within PLLND.F0.FilterIso.gap_t3_not_cover [propext, Quot.sound]
#axioms_within PLLND.F0.FilterIso.box_t3_not_bigAtom [propext, Quot.sound]
#axioms_within PLLND.F0.FilterIso.box_t5_not_bigAtom [propext, Quot.sound]
