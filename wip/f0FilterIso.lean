import wip.f0NotIso
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

Pins `[propext, Quot.sound]` throughout.
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
