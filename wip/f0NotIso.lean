import wip.f0SigOnto
import LaxLogic.ClosedFragmentLattice
import Meta.Audit

/-!
# `[t3, ⊤]` is not order-isomorphic to F0

**REFUTED**: `[t3, ⊤] ≅ F0` as posets, hence also as lattices
(`t3_filter_not_iso`, over `RNClass`, the closed-fragment quotient of
`LaxLogic/ClosedFragmentLattice.lean`).

## The invariant

Call `x, y` a *disjoint pair* when both are above the bottom and their only
common lower bounds are the bottom.  In F0 every disjoint pair contains
`¬◯⊥` (`disjoint_pair_has_negOBot`):

    atomFree x, y,   x ⊬ ⊥,   y ⊬ ⊥,   x ∧ y ⊢ ⊥   ⟹   x ⊣⊢ ¬◯⊥  ∨  y ⊣⊢ ¬◯⊥

By `low_trichotomy` each of `x`, `y` is `⊣⊢ ¬◯⊥` or lies above `◯⊥`; if both
lie above `◯⊥` then `◯⊥ ⊢ x ∧ y ⊢ ⊥`, against `◯⊥ ⊬ ⊥`.

In `[t3, ⊤]` (bottom `t3`) there are two disjoint pairs with no member in
common up to `⊣⊢` (`two_disjoint_pairs_above_t3`):

    c1 ∧ g1 ⊢ t3     (c1 = ◯t3,  g1 = c1 ↠ t3,  t3 ⊢ c1,  t3 ⊢ g1)
    t5 ∧ t6 ⊢ t3     (t6 = t5 ↠ t3,  t3 ⊢ t5,  t3 ⊢ t6)

with `c1, g1, t5, t6 ⊬ t3` and `c1, g1 ≢ t5, t6` (four non-equivalences;
`[c1] ⊢ t6` holds, so that pair is separated by `t6 ⊬ c1`).

The invariant is order-theoretic (`HasCore`: some `d` lies in every disjoint
pair, with "disjoint" read through lower bounds), so it transfers along an
order isomorphism (`hasCore_of_iso`).  `RNClass` has a core (`¬◯⊥`,
`rnclass_core`); `Set.Ici ⟦t3⟧` has none (`ici_no_core`).

## What remains

**OPEN**: is any proper principal filter `[p, ⊤]`, `p ≠ ⊥`, order-isomorphic
to F0?  This argument gives a necessary condition: `[p, ⊤]` must have a
member `d` lying in every disjoint pair.

The cells: positive ones by hand derivations; the eight non-entailments by
finite constraint countermodels (`FinCM`, from the subframe tableau through a
fallible top, `_out/gen9.lean`, untrusted producer), checked by
`FinCM.checkB` in the kernel.  They refute the semantic order `Le` of
`RNClass` directly (`not_le_of_check`), so no completeness theorem is used.
Pins `[propext, Quot.sound]` throughout, `t3_filter_not_iso` included
(Mathlib's `OrderIso` API brings no choice here).
-/

open PLLFormula

namespace PLLND
namespace F0
namespace NotIso

open SemUI RNEmbed
open PLLND.LaxInfinite (atomFree)

/-! ## The formulas -/

/-- `c1 = ◯t3`. -/
def c1F : PLLFormula := .somehow t3

/-- `g1 = c1 ↠ t3`. -/
def g1F : PLLFormula := .ifThen c1F t3

/-- `t6 = t5 ↠ t3`. -/
abbrev t6F : PLLFormula := T6.t6F

/-! ## Semantic order and derivability -/

/-- Derivability gives the semantic order (soundness). -/
theorem le_of_deriv {a b : PLLFormula} (h : Deriv [a] b) : LaxInfinite.Le a b :=
  fun M w ha => by
    obtain ⟨d⟩ := h
    exact soundness d M w (fun ψ hψ => by rw [List.mem_singleton.mp hψ]; exact ha)

/-- A checked finite constraint countermodel refutes the semantic order. -/
theorem not_le_of_check {M : FinCM} {w : Nat} {a b : PLLFormula}
    (h : FinCM.checkB M w [a] b = true) : ¬ LaxInfinite.Le a b := by
  simp only [FinCM.checkB, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨hwb, hlt⟩, hΓ⟩, hC⟩ := h
  have hwf := FinCM.wellFormed_of_wellB hwb
  intro hle
  have hval := hle (M.toModel hwf) ⟨w, hlt⟩
    ((M.force_iff hwf a ⟨w, hlt⟩).mpr (hΓ a (List.mem_singleton_self a)))
  rw [M.force_iff hwf b ⟨w, hlt⟩, hC] at hval
  exact Bool.false_ne_true hval

theorem nd_of_nle {a b : PLLFormula} (h : ¬ LaxInfinite.Le a b) : [a] ⊬ b :=
  fun d => h (le_of_deriv d)

/-! ## The countermodels -/

-- c1_t3: [a] ⊬ b, 5 worlds, refuting world 0
def K_c1_t3 : FinCM :=
  ⟨5, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (0, 4), (1, 4), (2, 4), (3, 4)],
    [(0, 4), (1, 4), (3, 4)], [4], []⟩

-- g1_t3: [a] ⊬ b, 7 worlds, refuting world 0
def K_g1_t3 : FinCM :=
  ⟨7, [(0, 1),
 (0, 2),
 (0, 3),
 (0, 4),
 (0, 5),
 (1, 2),
 (1, 3),
 (1, 4),
 (1, 5),
 (4, 5),
 (0, 6),
 (1, 6),
 (2, 6),
 (3, 6),
 (4, 6),
 (5, 6)],
    [(0, 6), (1, 6), (3, 6), (5, 6)], [6], []⟩

-- t5_t3: [a] ⊬ b, 6 worlds, refuting world 0
def K_t5_t3 : FinCM :=
  ⟨6, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3), (0, 5), (1, 5), (2, 5), (3, 5), (4, 5)],
    [(0, 5), (1, 5), (3, 5), (4, 5)], [5], []⟩

-- t6_t3: [a] ⊬ b, 7 worlds, refuting world 0
def K_t6_t3 : FinCM :=
  ⟨7, [(0, 1),
 (0, 2),
 (0, 3),
 (0, 4),
 (0, 5),
 (1, 2),
 (1, 3),
 (1, 4),
 (1, 5),
 (4, 5),
 (0, 6),
 (1, 6),
 (2, 6),
 (3, 6),
 (4, 6),
 (5, 6)],
    [(0, 6), (1, 6), (3, 6), (4, 6)], [6], []⟩

-- c1_t5_lr: [a] ⊬ b, 7 worlds, refuting world 0
def K_c1_t5_lr : FinCM :=
  ⟨7, [(0, 1),
 (0, 2),
 (0, 3),
 (0, 4),
 (0, 5),
 (1, 2),
 (1, 3),
 (1, 4),
 (1, 5),
 (4, 5),
 (0, 6),
 (1, 6),
 (2, 6),
 (3, 6),
 (4, 6),
 (5, 6)],
    [(0, 6), (1, 6), (3, 6), (4, 6)], [6], []⟩

-- c1_t6_lr: no countermodel ([c1] ⊢ t6 holds); the other direction is refuted
-- c1_t6_rl: [a] ⊬ b, 11 worlds, refuting world 0
def K_c1_t6_rl : FinCM :=
  ⟨11, [(0, 1),
 (0, 2),
 (0, 3),
 (0, 4),
 (0, 5),
 (0, 6),
 (0, 7),
 (0, 8),
 (0, 9),
 (1, 2),
 (1, 3),
 (1, 4),
 (1, 5),
 (1, 6),
 (1, 7),
 (1, 8),
 (1, 9),
 (4, 5),
 (6, 7),
 (6, 8),
 (6, 9),
 (8, 9),
 (0, 10),
 (1, 10),
 (2, 10),
 (3, 10),
 (4, 10),
 (5, 10),
 (6, 10),
 (7, 10),
 (8, 10),
 (9, 10)],
    [(0, 10), (1, 10), (3, 10), (4, 10), (7, 10), (8, 10)], [10], []⟩

-- g1_t5_lr: [a] ⊬ b, 9 worlds, refuting world 0
def K_g1_t5_lr : FinCM :=
  ⟨9, [(0, 1),
 (0, 2),
 (0, 3),
 (0, 4),
 (0, 5),
 (0, 6),
 (0, 7),
 (1, 2),
 (1, 3),
 (1, 4),
 (1, 5),
 (1, 6),
 (1, 7),
 (4, 5),
 (6, 7),
 (0, 8),
 (1, 8),
 (2, 8),
 (3, 8),
 (4, 8),
 (5, 8),
 (6, 8),
 (7, 8)],
    [(0, 8), (1, 8), (3, 8), (5, 8), (6, 8)], [8], []⟩

-- g1_t6_lr: [a] ⊬ b, 11 worlds, refuting world 0
def K_g1_t6_lr : FinCM :=
  ⟨11, [(0, 1),
 (0, 2),
 (0, 3),
 (0, 4),
 (0, 5),
 (0, 6),
 (0, 7),
 (0, 8),
 (0, 9),
 (1, 2),
 (1, 3),
 (1, 4),
 (1, 5),
 (1, 6),
 (1, 7),
 (1, 8),
 (1, 9),
 (2, 3),
 (4, 5),
 (4, 6),
 (4, 7),
 (4, 8),
 (4, 9),
 (5, 6),
 (8, 9),
 (0, 10),
 (1, 10),
 (2, 10),
 (3, 10),
 (4, 10),
 (5, 10),
 (6, 10),
 (7, 10),
 (8, 10),
 (9, 10)],
    [(0, 10), (1, 10), (3, 10), (4, 10), (6, 10), (7, 10), (9, 10)], [10], []⟩


theorem nle_c1_t3 : ¬ LaxInfinite.Le c1F t3 := not_le_of_check (M := K_c1_t3) (w := 0) (by decide)
theorem nle_g1_t3 : ¬ LaxInfinite.Le g1F t3 := not_le_of_check (M := K_g1_t3) (w := 0) (by decide)
theorem nle_t5_t3 : ¬ LaxInfinite.Le t5 t3 := not_le_of_check (M := K_t5_t3) (w := 0) (by decide)
theorem nle_t6_t3 : ¬ LaxInfinite.Le t6F t3 := not_le_of_check (M := K_t6_t3) (w := 0) (by decide)
theorem nle_c1_t5 : ¬ LaxInfinite.Le c1F t5 :=
  not_le_of_check (M := K_c1_t5_lr) (w := 0) (by decide)
theorem nle_t6_c1 : ¬ LaxInfinite.Le t6F c1F :=
  not_le_of_check (M := K_c1_t6_rl) (w := 0) (by decide)
theorem nle_g1_t5 : ¬ LaxInfinite.Le g1F t5 :=
  not_le_of_check (M := K_g1_t5_lr) (w := 0) (by decide)
theorem nle_g1_t6 : ¬ LaxInfinite.Le g1F t6F :=
  not_le_of_check (M := K_g1_t6_lr) (w := 0) (by decide)
/-- `◯⊥ ⊬ ⊥`, semantically (the model `M3` of `wip/f0Covers.lean`). -/
theorem nle_e_bot : ¬ LaxInfinite.Le e .falsePLL :=
  not_le_of_check (M := M3) (w := 0) (by decide)

/-! ## The invariant in F0 -/

/-- **Every disjoint pair of F0 contains `¬◯⊥`.** -/
theorem disjoint_pair_has_negOBot {x y : PLLFormula} (hx : atomFree x = true)
    (hy : atomFree y = true) (hx0 : [x] ⊬ .falsePLL) (hy0 : [y] ⊬ .falsePLL)
    (hxy : Deriv [x.and y] .falsePLL) : Interd x notOBot ∨ Interd y notOBot := by
  rcases low_trichotomy x hx with hex | hxb | hxn
  · rcases low_trichotomy y hy with hey | hyb | hyn
    · exact absurd (Deriv.cutHead (Deriv.andIntro hex hey) hxy) nd_e_bot
    · exact absurd hyb.1 hy0
    · exact Or.inr hyn
  · exact absurd hxb.1 hx0
  · exact Or.inl hxn

/-! ## Two disjoint pairs above `t3` -/

theorem t3_le_c1 : Deriv [t3] c1F := ⟨.laxIntro (.iden (.head _))⟩
theorem t3_le_g1 : Deriv [t3] g1F := Deriv.impIntro (Deriv.iden (.tail _ (.head _)))
theorem c1g1_le_t3 : Deriv [c1F.and g1F] t3 :=
  Deriv.impElim (Deriv.andElim2 (Deriv.iden (.head _))) (Deriv.andElim1 (Deriv.iden (.head _)))
theorem t3_le_t5 : Deriv [t3] t5 := Deriv.orIntro1 (Deriv.iden (.head _))
theorem t3_le_t6 : Deriv [t3] t6F := Deriv.impIntro (Deriv.iden (.tail _ (.head _)))
theorem t5t6_le_t3 : Deriv [t5.and t6F] t3 :=
  Deriv.impElim (Deriv.andElim2 (Deriv.iden (.head _))) (Deriv.andElim1 (Deriv.iden (.head _)))

/-- **Two disjoint pairs above `t3`, with no member in common.** -/
theorem two_disjoint_pairs_above_t3 :
    (Deriv [t3] c1F ∧ Deriv [t3] g1F ∧ Deriv [c1F.and g1F] t3 ∧
      ([c1F] ⊬ t3) ∧ ([g1F] ⊬ t3)) ∧
    (Deriv [t3] t5 ∧ Deriv [t3] t6F ∧ Deriv [t5.and t6F] t3 ∧
      ([t5] ⊬ t3) ∧ ([t6F] ⊬ t3)) ∧
    (¬ Interd c1F t5 ∧ ¬ Interd c1F t6F ∧ ¬ Interd g1F t5 ∧ ¬ Interd g1F t6F) :=
  ⟨⟨t3_le_c1, t3_le_g1, c1g1_le_t3, nd_of_nle nle_c1_t3, nd_of_nle nle_g1_t3⟩,
   ⟨t3_le_t5, t3_le_t6, t5t6_le_t3, nd_of_nle nle_t5_t3, nd_of_nle nle_t6_t3⟩,
   ⟨fun hi => nle_c1_t5 (le_of_deriv hi.1), fun hi => nle_t6_c1 (le_of_deriv hi.2),
    fun hi => nle_g1_t5 (le_of_deriv hi.1), fun hi => nle_g1_t6 (le_of_deriv hi.1)⟩⟩

/-! ## The order-theoretic invariant -/

/-- `x`, `y` are disjoint: their common lower bounds are least elements. -/
def Disj {P : Type} [LE P] (x y : P) : Prop := ∀ z, z ≤ x → z ≤ y → IsBot z

/-- `d` lies in every disjoint pair of non-least elements. -/
def Core {P : Type} [LE P] (d : P) : Prop :=
  ∀ x y : P, ¬ IsBot x → ¬ IsBot y → Disj x y → x = d ∨ y = d

def HasCore (P : Type) [LE P] : Prop := ∃ d : P, Core d

/-- **The invariant transfers along an order isomorphism.** -/
theorem hasCore_of_iso {P Q : Type} [Preorder P] [Preorder Q] (f : P ≃o Q)
    (h : HasCore Q) : HasCore P := by
  obtain ⟨d, hd⟩ := h
  refine ⟨f.symm d, fun x y hx hy hxy => ?_⟩
  have hbot : ∀ u : P, IsBot (f u) → IsBot u := fun u hu w => f.le_iff_le.mp (hu (f w))
  have hbot' : ∀ v : Q, IsBot (f.symm v) → IsBot v := fun v hv w =>
    f.symm.le_iff_le.mp (hv (f.symm w))
  have hdisj : Disj (f x) (f y) := fun z hzx hzy => by
    apply hbot' z
    apply hxy
    · have h1 := f.symm.le_iff_le.mpr hzx
      rwa [f.symm_apply_apply] at h1
    · have h1 := f.symm.le_iff_le.mpr hzy
      rwa [f.symm_apply_apply] at h1
  rcases hd (f x) (f y) (fun h => hx (hbot x h)) (fun h => hy (hbot y h)) hdisj with h | h
  · left
    rw [← h, f.symm_apply_apply]
  · right
    rw [← h, f.symm_apply_apply]

/-! ## `RNClass` has a core: `¬◯⊥` -/

/-- The class of a closed formula. -/
def cls (φ : PLLFormula) (h : atomFree φ = true) : RNClass :=
  Quotient.mk _ (Closed.mk φ h)

theorem rnclass_core : HasCore RNClass := by
  refine ⟨cls notOBot rfl, fun x y hx hy hxy => ?_⟩
  induction x using Quotient.ind
  induction y using Quotient.ind
  rename_i a b
  -- each side is `¬◯⊥`, or above `◯⊥`, or `⊥`
  have side : ∀ c : LaxInfinite.Closed, ¬ IsBot (Quotient.mk LaxInfinite.closedSetoid c) →
      (cls oBot rfl ≤ Quotient.mk LaxInfinite.closedSetoid c) ∨
        Quotient.mk LaxInfinite.closedSetoid c = cls notOBot rfl := by
    intro c hc
    rcases low_trichotomy c.1 c.2 with hec | hcb | hcn
    · exact Or.inl (le_of_deriv hec)
    · exact absurd (fun w => le_trans (le_of_deriv hcb.1 :
        (Quotient.mk LaxInfinite.closedSetoid c : RNClass) ≤ (⊥ : RNClass)) bot_le) hc
    · exact Or.inr (Quotient.sound ⟨le_of_deriv hcn.1, le_of_deriv hcn.2⟩)
  rcases side a hx with ha | ha
  · rcases side b hy with hb | hb
    · exact absurd ((hxy _ ha hb) (⊥ : RNClass) : cls oBot rfl ≤ (⊥ : RNClass)) nle_e_bot
    · exact Or.inr hb
  · exact Or.inl ha

/-! ## `[t3, ⊤]` has no core -/

/-- `⟦t3⟧`. -/
def T3 : RNClass := cls t3 rfl

/-- A point of `[t3, ⊤]`. -/
def pt (φ : PLLFormula) (h : atomFree φ = true) (hle : Deriv [t3] φ) : Set.Ici T3 :=
  ⟨cls φ h, le_of_deriv hle⟩

theorem pt_not_bot {φ : PLLFormula} {h : atomFree φ = true} {hle : Deriv [t3] φ}
    (hn : ¬ LaxInfinite.Le φ t3) : ¬ IsBot (pt φ h hle) :=
  fun hb => hn (hb ⟨T3, le_refl T3⟩)

theorem pt_disj {a b : PLLFormula} {ha : atomFree a = true} {hb : atomFree b = true}
    {hla : Deriv [t3] a} {hlb : Deriv [t3] b} (hab : Deriv [a.and b] t3) :
    Disj (pt a ha hla) (pt b hb hlb) := by
  intro z hza hzb
  obtain ⟨zq, hzq⟩ := z
  induction zq using Quotient.ind
  rename_i c
  have hct : LaxInfinite.Le c.1 t3 := fun M w hc =>
    le_of_deriv hab M w ⟨(hza : LaxInfinite.Le c.1 a) M w hc, (hzb : LaxInfinite.Le c.1 b) M w hc⟩
  intro w
  show (Quotient.mk LaxInfinite.closedSetoid c : RNClass) ≤ w.1
  exact le_trans (hct : (Quotient.mk LaxInfinite.closedSetoid c : RNClass) ≤ T3)
    (Set.mem_Ici.mp w.2)

theorem pt_ne {a b : PLLFormula} {ha : atomFree a = true} {hb : atomFree b = true}
    {hla : Deriv [t3] a} {hlb : Deriv [t3] b} (hne : ¬ LaxInfinite.Le a b ∨ ¬ LaxInfinite.Le b a) :
    pt a ha hla ≠ pt b hb hlb := fun h => by
  have he : LaxInfinite.LaxEquiv a b := Quotient.exact (congrArg Subtype.val h)
  rcases hne with hn | hn
  · exact hn he.1
  · exact hn he.2

theorem ici_no_core : ¬ HasCore (Set.Ici T3) := by
  rintro ⟨d, hd⟩
  have hC := hd (pt c1F rfl t3_le_c1) (pt g1F rfl t3_le_g1) (pt_not_bot nle_c1_t3)
    (pt_not_bot nle_g1_t3) (pt_disj c1g1_le_t3)
  have hT := hd (pt t5 rfl t3_le_t5) (pt t6F rfl t3_le_t6) (pt_not_bot nle_t5_t3)
    (pt_not_bot nle_t6_t3) (pt_disj t5t6_le_t3)
  rcases hC with h1 | h1 <;> rcases hT with h2 | h2
  · exact pt_ne (Or.inl nle_c1_t5) (h1.trans h2.symm)
  · exact pt_ne (Or.inr nle_t6_c1) (h1.trans h2.symm)
  · exact pt_ne (Or.inl nle_g1_t5) (h1.trans h2.symm)
  · exact pt_ne (Or.inl nle_g1_t6) (h1.trans h2.symm)

/-- **REFUTED: `[t3, ⊤] ≅ F0` as posets.** -/
theorem t3_filter_not_iso : ¬ Nonempty (Set.Ici T3 ≃o RNClass) :=
  fun ⟨f⟩ => ici_no_core (hasCore_of_iso f rnclass_core)

end NotIso
end F0
end PLLND

/-! ## Axiom pins -/

#axioms_within PLLND.F0.NotIso.le_of_deriv [propext, Quot.sound]
#axioms_within PLLND.F0.NotIso.not_le_of_check [propext, Quot.sound]
#axioms_within PLLND.F0.NotIso.disjoint_pair_has_negOBot [propext, Quot.sound]
#axioms_within PLLND.F0.NotIso.two_disjoint_pairs_above_t3 [propext, Quot.sound]
#axioms_within PLLND.F0.NotIso.hasCore_of_iso [propext, Quot.sound]
#axioms_within PLLND.F0.NotIso.rnclass_core [propext, Quot.sound]
#axioms_within PLLND.F0.NotIso.ici_no_core [propext, Quot.sound]
#axioms_within PLLND.F0.NotIso.t3_filter_not_iso [propext, Quot.sound]
