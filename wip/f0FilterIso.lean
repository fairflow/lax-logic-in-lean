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

-- PART2

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
