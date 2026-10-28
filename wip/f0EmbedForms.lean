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

## Results

All PROVED, pins `[propext, Quot.sound]`, or `[]` where nothing is used; no `sorry`, no
`native_decide`, no `Classical.choice`.

* `pairwiseHimp : PairwiseHimp` (`himp_le`, `himp_eq_iff`), over Mathlib's
  `HeytingAlgebra` (`le_himp_iff`, `himp_inf_le`).
* `shift : Shift` (`shift_le`).
* `shiftH2 : ShiftH2` (`shift2_pos`, `shift2_sep`, `shift2_bot`) and
  `shift2_orderEmb : ShiftOrderEmb`.  (ii) needs no consistency of `σ²⊥`:
  `[h A] ⊢ ⊥` gives `[h A] ⊢ h ⊥ = σ²⊥` by ex falso, and `freePair_reflects`
  gives `[A] ⊢ ⊥`.  The same argument is `shift_le` with `b' = ⊥ ≤ σ²⊥`.
* `shiftMeetFails : ShiftMeetFails`: `h p ∧ h ¬p ⊣⊢ σ²⊥`
  (`shift2_meet_le`, `shift2_meet_ge`) and `σ²⊥ ⊬ ⊥` (`b2_consistent`, the
  one-world model with no `S`-point), while `p ∧ ¬p ⊢ ⊥` in IPC.

Status note: `wip/f0EmbedForms-STATUS.md`.
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

/-! ## Lemma 1: the pairwise lemma -/

section Pairwise

universe u v

variable {H : Type u} {K : Type v} [HeytingAlgebra H] [HeytingAlgebra K]

/-- `e (a ⇨ c) ≤ e a ⇨ e c`, since `e (a ⇨ c) ⊓ e a = e ((a ⇨ c) ⊓ a) ≤ e c`. -/
theorem himp_le (e : H → K) (he : ∀ x y, e x ≤ e y ↔ x ≤ y)
    (hinf : ∀ x y, e (x ⊓ y) = e x ⊓ e y) (a c : H) : e (a ⇨ c) ≤ e a ⇨ e c := by
  apply le_himp_iff.mpr
  rw [← hinf]
  exact (he _ _).mpr himp_inf_le

/-- `e a ⇨ e c` is the image of `a ⇨ c` as soon as it is the image of anything:
from `e d = e a ⇨ e c`, `e (d ⊓ a) ≤ e c`, so `d ⊓ a ≤ c`, `d ≤ a ⇨ c`. -/
theorem himp_eq_iff (e : H → K) (he : ∀ x y, e x ≤ e y ↔ x ≤ y)
    (hinf : ∀ x y, e (x ⊓ y) = e x ⊓ e y) (a c : H) :
    e a ⇨ e c = e (a ⇨ c) ↔ ∃ d, e d = e a ⇨ e c := by
  constructor
  · intro h
    exact ⟨a ⇨ c, h.symm⟩
  · rintro ⟨d, hd⟩
    have h1 : e (d ⊓ a) ≤ e c := by
      rw [hinf, hd]
      exact himp_inf_le
    have h2 : d ≤ a ⇨ c := le_himp_iff.mpr ((he _ _).mp h1)
    have h3 : e a ⇨ e c ≤ e (a ⇨ c) :=
      calc e a ⇨ e c = e d := hd.symm
        _ ≤ e (a ⇨ c) := (he _ _).mpr h2
    exact le_antisymm h3 (himp_le e he hinf a c)

end Pairwise

/-- **PROVED: Lemma 1.** -/
theorem pairwiseHimp : PairwiseHimp := by
  intro H K _ _ e he hinf a c
  exact ⟨himp_le e he hinf a c, himp_eq_iff e he hinf a c⟩

/-! ## The shift, abstractly -/

section ShiftSec

universe u v

variable {H : Type u} {K : Type v} [PartialOrder H] [OrderBot H] [DecidableEq H] [Preorder K]

/-- **The shift**: `x ↦ if x = ⊥ then b' else e x` is an order embedding when
`e` is one and `b' ≤ e ⊥`.  At `x ≠ ⊥`, `y = ⊥`: `e x ≤ b' ≤ e ⊥` would give
`x ≤ ⊥`. -/
theorem shift_le (e : H → K) (he : ∀ x y, e x ≤ e y ↔ x ≤ y) (b' : K) (hb : b' ≤ e ⊥)
    (x y : H) :
    ((if x = (⊥ : H) then b' else e x) ≤ (if y = (⊥ : H) then b' else e y) ↔ x ≤ y) := by
  have hbe : ∀ z, b' ≤ e z := fun z => le_trans hb ((he _ _).mpr bot_le)
  rcases Decidable.em (x = ⊥) with hx | hx
  · have hxy : x ≤ y := by
      rw [hx]
      exact bot_le
    rcases Decidable.em (y = ⊥) with hy | hy
    · rw [if_pos hx, if_pos hy]
      exact iff_of_true (le_refl b') hxy
    · rw [if_pos hx, if_neg hy]
      exact iff_of_true (hbe y) hxy
  · rcases Decidable.em (y = ⊥) with hy | hy
    · rw [if_neg hx, if_pos hy]
      refine iff_of_false (fun h => hx (le_bot_iff.mp ((he _ _).mp (le_trans h hb)))) ?_
      intro h
      rw [hy] at h
      exact hx (le_bot_iff.mp h)
    · rw [if_neg hx, if_neg hy]
      exact he x y

end ShiftSec

/-- **PROVED: the shift.** -/
theorem shift : Shift := by
  intro H K _ _ _ _ e he b' hb x y
  exact shift_le e he b' hb x y

/-! ## Lemma 2: the shift for `H₂` with bottom `⊥` -/

/-- **(i)** `FreePair` restricted to the classes other than `⊥`. -/
theorem shift2_pos {A B : PLLFormula} (hA : boxFree A = true) (hB : boxFree B = true)
    (vA : varsBelow 2 A = true) (vB : varsBelow 2 B = true)
    (_hA0 : ¬ Deriv [A] .falsePLL) (_hB0 : ¬ Deriv [B] .falsePLL) :
    Deriv [A] B ↔ Deriv [relB b2 xs A] (relB b2 xs B) :=
  freePair A B hA hB vA vB

/-- **(ii)** `e A = h A` is not below `e ⊥ = ⊥`: `[h A] ⊢ ⊥` gives
`[h A] ⊢ h ⊥ = σ²⊥` by ex falso, and `freePair_reflects` gives `[A] ⊢ ⊥`. -/
theorem shift2_sep {A : PLLFormula} (hA : boxFree A = true) (vA : varsBelow 2 A = true)
    (hA0 : ¬ Deriv [A] .falsePLL) : ¬ Deriv [relB b2 xs A] .falsePLL := fun hd =>
  hA0 (freePair_reflects (B := .falsePLL) hA rfl vA rfl (Deriv.falsoElim _ hd))

/-- **(iii)** `e ⊥ = ⊥` is below everything. -/
theorem shift2_bot (B : PLLFormula) : Deriv [.falsePLL] (relB b2 xs B) :=
  Deriv.falsoElim _ (Deriv.iden (.head _))

/-- **PROVED: Lemma 2.** -/
theorem shiftH2 : ShiftH2 := fun _ B hA hB vA vB =>
  ⟨fun h1 h2 => shift2_pos hA hB vA vB h1 h2, shift2_sep hA vA, shift2_bot B⟩

/-- **PROVED: the shifted map is an order embedding of `H₂` into F0.** -/
theorem shift2_orderEmb : ShiftOrderEmb := by
  intro A B φ ψ hA hB vA vB hφ hψ
  rcases hφ with ⟨hA0, rfl⟩ | ⟨hA0, rfl⟩
  · exact iff_of_true (Deriv.falsoElim B hA0) (Deriv.falsoElim ψ (Deriv.iden (.head _)))
  · rcases hψ with ⟨hB0, rfl⟩ | ⟨hB0, rfl⟩
    · exact iff_of_false (fun h => hA0 (Deriv.cutHead h hB0)) (shift2_sep hA vA hA0)
    · exact shift2_pos hA hB vA vB hA0 hB0

/-! ## The shift does not preserve `∧`

`[p ∧ ¬p] ⊢ ⊥`, so the shifted map sends `p ∧ ¬p` to `⊥`; but
`h p ∧ h ¬p ⊣⊢ σ²⊥` and `σ²⊥ ⊬ ⊥`.  Countermodels: one world, no `S`-point
(`◯` holds vacuously there, so `σ²⊥ = ◯t3 ∨ (◯t3 ↠ t3)` holds), kernel-checked
by `SubTab.no`. -/

set_option maxRecDepth 100000

/-- `⊬ σ²⊥ ↠ ⊥` (one world, no `S`-point). -/
theorem b2_imp_bot : ¬ Deriv [] (b2.ifThen .falsePLL) :=
  SubTab.no.verdict (b2.ifThen .falsePLL)
    { n := 1, root := 0, le := [[true]], S := [false], val := [[]] }

/-- **`σ²⊥` is consistent**: `[σ²⊥] ⊬ ⊥`. -/
theorem b2_consistent : ¬ Deriv [b2] .falsePLL := fun hd => b2_imp_bot (Deriv.impIntro hd)

/-- IPC: `⊬ p ↠ ⊥` (one world forcing `p`). -/
theorem ipc_p_imp_bot : ¬ Deriv [] (pP.ifThen .falsePLL) :=
  SubTab.no.verdict (pP.ifThen .falsePLL)
    { n := 1, root := 0, le := [[true]], S := [false], val := [["p"]] }

/-- IPC: `⊬ ¬p ↠ ⊥` (one world refuting `p`). -/
theorem ipc_np_imp_bot : ¬ Deriv [] ((negF pP).ifThen .falsePLL) :=
  SubTab.no.verdict ((negF pP).ifThen .falsePLL)
    { n := 1, root := 0, le := [[true]], S := [false], val := [[]] }

/-- IPC: `[p ∧ ¬p] ⊢ ⊥`. -/
theorem ipc_meet_bot : Deriv [pP.and (negF pP)] .falsePLL :=
  Deriv.impElim (Deriv.andElim2 (Deriv.iden (.head _))) (Deriv.andElim1 (Deriv.iden (.head _)))

/-- `[h p ∧ h ¬p] ⊢ σ²⊥`: `h ¬p = h p ↠ σ²⊥`. -/
theorem shift2_meet_le : Deriv [(relB b2 xs pP).and (relB b2 xs (negF pP))] b2 :=
  Deriv.impElim (Deriv.andElim2 (Deriv.iden (.head _))) (Deriv.andElim1 (Deriv.iden (.head _)))

/-- `[σ²⊥] ⊢ h p ∧ h ¬p`: `σ²⊥ ≤ x₀ = h p` and `σ²⊥ ≤ h p ↠ σ²⊥`. -/
theorem shift2_meet_ge : Deriv [b2] ((relB b2 xs pP).and (relB b2 xs (negF pP))) :=
  Deriv.andIntro (b2_le_xs (pvar 0)) (Deriv.impIntro (Deriv.iden (.tail _ (.head _))))

/-- `[h p ∧ h ¬p] ⊬ ⊥`. -/
theorem shift2_meet_not_bot :
    ¬ Deriv [(relB b2 xs pP).and (relB b2 xs (negF pP))] .falsePLL := fun hd =>
  b2_consistent (Deriv.cutHead shift2_meet_ge hd)

/-- **PROVED: the shift does not preserve `∧`.** -/
theorem shiftMeetFails : ShiftMeetFails :=
  ⟨ipc_meet_bot, fun hd => ipc_p_imp_bot (Deriv.impIntro hd),
    fun hd => ipc_np_imp_bot (Deriv.impIntro hd), shift2_meet_not_bot⟩

end EmbedForms
end F0
end PLLND

/-! ## Axiom pins -/

#axioms_within PLLND.F0.EmbedForms.himp_le []
#axioms_within PLLND.F0.EmbedForms.himp_eq_iff []
#axioms_within PLLND.F0.EmbedForms.pairwiseHimp []
#axioms_within PLLND.F0.EmbedForms.shift_le []
#axioms_within PLLND.F0.EmbedForms.shift []
#axioms_within PLLND.F0.EmbedForms.shift2_pos [propext, Quot.sound]
#axioms_within PLLND.F0.EmbedForms.shift2_sep [propext, Quot.sound]
#axioms_within PLLND.F0.EmbedForms.shift2_bot []
#axioms_within PLLND.F0.EmbedForms.shiftH2 [propext, Quot.sound]
#axioms_within PLLND.F0.EmbedForms.shift2_orderEmb [propext, Quot.sound]
#axioms_within PLLND.F0.EmbedForms.b2_imp_bot [propext, Quot.sound]
#axioms_within PLLND.F0.EmbedForms.b2_consistent [propext, Quot.sound]
#axioms_within PLLND.F0.EmbedForms.ipc_p_imp_bot [propext, Quot.sound]
#axioms_within PLLND.F0.EmbedForms.ipc_np_imp_bot [propext, Quot.sound]
#axioms_within PLLND.F0.EmbedForms.ipc_meet_bot []
#axioms_within PLLND.F0.EmbedForms.shift2_meet_le []
#axioms_within PLLND.F0.EmbedForms.shift2_meet_ge []
#axioms_within PLLND.F0.EmbedForms.shift2_meet_not_bot [propext, Quot.sound]
#axioms_within PLLND.F0.EmbedForms.shiftMeetFails [propext, Quot.sound]
