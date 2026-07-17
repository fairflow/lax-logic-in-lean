import LaxLogic.PLLCompleteness
import LaxLogic.PLLFiniteModel
import LaxLogic.PLLG4Dec
import LaxLogic.PLLCountermodelEmit

/-!
# Finitary completeness for PLL — the canonical model without Zorn

This file rebuilds the canonical-model completeness proof of
`PLLCompleteness.lean` over a *finite* subformula closure, with the Zorn
Lindenbaum lemma replaced by an **iterated decided extension**: at each
closure formula the decision "add to `val` or add to `fal`" is made by the
mechanised decision procedure (`decidablePLL`), and the else-branch is
justified by the same disjunction-combination argument that classically
proves `mem_val_or_mem_fal`.

Contents (mirroring F&M §4 / `PLLCompleteness.lean` case for case):

1. **Part 1 (foundation)** — finite theory triples `FTheory`
   (`val`/`fal`/`mfal` as `Finset`s), consistency reused verbatim from the
   classical development through `FTheory.toTheory`, its *decidability*
   (`cons_iff_check`: consistency of a finite triple is one derivability
   check on the full selection, decided by `decidablePLL`), the extension
   dichotomy `cons_insVal_or_insFal`, and the **constructive Lindenbaum**
   `lindenbaum`: a computable fold extending any consistent triple to a
   closure-total one, leaving `mfal` untouched.
2. Part 2 — the finite Lemma 4.2 suite (`ded_closed`, `or_mem`, `imp_mem`,
   `fal_or`, `fal_and`, `mfal_sub_fal`, …) relative to a subformula-closed
   `cl`, by the classical proofs with `∈ cl` side conditions (maximality is
   consumed *only* through the extension-failure witnesses, which
   closure-totality supplies).
3. Part 3 — the truth lemma on the finite canonical model (worlds = the
   closure-total consistent triples; `Rᵢ` = inclusion on `val`; `Rₘ` =
   inclusion on `val` and `mfal`), with the three Lindenbaum extension
   steps of the classical proof replaced by `lindenbaum`.
4. Part 4 — enumeration of the (finitely many) worlds into a `FinCM`,
   `checkB` certification, and **emitter completeness**: every underivable
   sequent has a checked countermodel.  The composition with the
   presented-strategy squeeze lives in `PLLRealCompleteness.lean`.

Audit note (updated 2026-07-17, after the axiom-hygiene pass): the
mathematics here is finitary (no Zorn anywhere).  The incidental
classical steps in the cut-elimination chain are now scrubbed
(`cutElimination` and `G4c.equiv_tm` audit `[propext, Quot.sound]`),
but this development still audits
`[propext, Classical.choice, Quot.sound]`, and a dependency-frontier
measurement shows the remainder is structural, not tactic hygiene:

1. the decidability infrastructure (`decidablePLL`, `G4c_iff_search`)
   sits on Mathlib `Finset` operations whose bodies embed choice, and
   on a `Nat.find` minimal-height induction — see the audit note in
   `PLLG4Dec.lean`;
2. the world enumeration here (`worldFinset`, `worldList`,
   `cons_iff_check`) uses `Finset.powerset`/`Finset.toList`, and
   `Multiset.toList` is defined by `Classical.choice` outright;
3. `not_consistent_iff` (`PLLCompleteness.lean`) is a `push_neg`
   double negation over an existential with no choice-free decider.

A choice-free audit therefore needs a list-based world representation
and a list-based decider, not further proof repairs.
-/

open PLLFormula

namespace PLLND
namespace FinComp

/-! ## Finite theory triples -/

/-- A finite theory triple: `val`idated / `fal`sified / `mfal` = falsified
at every `Rₘ`-successor, all finite. -/
structure FTheory where
  val : Finset PLLFormula
  fal : Finset PLLFormula
  mfal : Finset PLLFormula
  deriving DecidableEq

namespace FTheory

/-- The associated (set-valued) theory of the classical development. -/
def toTheory (T : FTheory) : Theory := ⟨↑T.val, ↑T.fal, ↑T.mfal⟩

@[simp] theorem toTheory_val (T : FTheory) : T.toTheory.val = ↑T.val := rfl
@[simp] theorem toTheory_fal (T : FTheory) : T.toTheory.fal = ↑T.fal := rfl
@[simp] theorem toTheory_mfal (T : FTheory) : T.toTheory.mfal = ↑T.mfal := rfl

/-- Consistency, reused from the classical development. -/
def Cons (T : FTheory) : Prop := Consistent T.toTheory

/-- Componentwise inclusion. -/
def le (T T' : FTheory) : Prop :=
  T.val ⊆ T'.val ∧ T.fal ⊆ T'.fal ∧ T.mfal ⊆ T'.mfal

theorem le_refl (T : FTheory) : T.le T := ⟨subset_rfl, subset_rfl, subset_rfl⟩

theorem le_trans {T₁ T₂ T₃ : FTheory} (h : T₁.le T₂) (h' : T₂.le T₃) :
    T₁.le T₃ :=
  ⟨h.1.trans h'.1, h.2.1.trans h'.2.1, h.2.2.trans h'.2.2⟩

/-- Insert into the validated part. -/
def insVal (φ : PLLFormula) (T : FTheory) : FTheory :=
  ⟨insert φ T.val, T.fal, T.mfal⟩

/-- Insert into the falsified part. -/
def insFal (φ : PLLFormula) (T : FTheory) : FTheory :=
  ⟨T.val, insert φ T.fal, T.mfal⟩

end FTheory

/-! ## Decidability of consistency -/

/-- Set-derivability from a finset coercion is list-derivability from its
`toList`. -/
theorem setDeriv_coe_iff {V : Finset PLLFormula} {φ : PLLFormula} :
    (↑V : Set PLLFormula) ⊩ φ ↔ Nonempty (LaxND V.toList φ) := by
  constructor
  · rintro ⟨L, hL, ⟨p⟩⟩
    exact ⟨p.rename fun ψ hψ => Finset.mem_toList.mpr (hL ψ hψ)⟩
  · rintro ⟨p⟩
    exact ⟨V.toList, fun ψ hψ => Finset.mem_toList.mp hψ, ⟨p⟩⟩

noncomputable instance (V : Finset PLLFormula) (φ : PLLFormula) :
    Decidable ((↑V : Set PLLFormula) ⊩ φ) :=
  decidable_of_iff _ (curry_howard.trans setDeriv_coe_iff.symm)

/-- Consistency of a finite triple is a single derivability check on the
full selection (empty selections aside): `disjOf` is monotone, so the full
lists are the worst case. -/
theorem cons_iff_check (T : FTheory) :
    T.Cons ↔ (T.fal = ∅ ∧ T.mfal = ∅) ∨
      ¬ (↑T.val : Set PLLFormula) ⊩ disjOf T.fal.toList T.mfal.toList := by
  constructor
  · intro hT
    by_cases he : T.fal = ∅ ∧ T.mfal = ∅
    · exact .inl he
    · refine .inr (hT T.fal.toList T.mfal.toList
        (fun ψ hψ => Finset.mem_toList.mp hψ)
        (fun ψ hψ => Finset.mem_toList.mp hψ) ?_)
      intro hnil
      rcases List.append_eq_nil_iff.mp hnil with ⟨h₁, h₂⟩
      exact he ⟨Finset.toList_eq_nil.mp h₁, Finset.toList_eq_nil.mp h₂⟩
  · rintro (⟨he₁, he₂⟩ | hnd) Ds Ts hDs hTs hg hder
    · cases Ds with
      | nil =>
          cases Ts with
          | nil => exact hg rfl
          | cons K Ts =>
              have := hTs K (List.mem_cons_self ..)
              rw [FTheory.toTheory_mfal, he₂] at this
              simp at this
      | cons D Ds =>
          have := hDs D (List.mem_cons_self ..)
          rw [FTheory.toTheory_fal, he₁] at this
          simp at this
    · refine hnd (disjOf_mono ?_ ?_ hder)
      · exact fun ψ hψ => Finset.mem_toList.mpr (hDs ψ hψ)
      · exact fun ψ hψ => Finset.mem_toList.mpr (hTs ψ hψ)

noncomputable instance (T : FTheory) : Decidable T.Cons :=
  decidable_of_iff _ (cons_iff_check T).symm

/-! ## The extension dichotomy -/

/-- **The decided extension is safe**: a consistent triple stays consistent
when a formula is added to `val` or, failing that, to `fal` — the finite
mirror of the classical `mem_val_or_mem_fal` combination argument. -/
theorem cons_insVal_or_insFal {T : FTheory} (hT : T.Cons) (φ : PLLFormula) :
    (T.insVal φ).Cons ∨ (T.insFal φ).Cons := by
  by_cases h1 : (T.insVal φ).Cons
  · exact .inl h1
  by_cases h2 : (T.insFal φ).Cons
  · exact .inr h2
  exfalso
  rw [FTheory.Cons, not_consistent_iff] at h1 h2
  obtain ⟨Ds₁, Ts₁, hDs₁, hTs₁, hg₁, hd₁⟩ := h1
  obtain ⟨Ds₂, Ts₂, hDs₂, hTs₂, hg₂, hd₂⟩ := h2
  simp only [FTheory.insVal, FTheory.insFal, FTheory.toTheory,
    Finset.coe_insert] at hDs₁ hTs₁ hd₁ hDs₂ hTs₂ hd₂
  have hd : (↑T.val : Set PLLFormula) ⊩
      disjOf (Ds₁ ++ rmv φ Ds₂) (Ts₁ ++ Ts₂) := by
    refine disjOf_transform hd₂ (fun ψ hψ => ?_)
      (fun ψ hψ => List.mem_append.mpr (.inr hψ))
    by_cases he : ψ = φ
    · subst he
      exact disjOf_mono
        (fun χ hχ => List.mem_append.mpr (.inl hχ))
        (fun χ hχ => List.mem_append.mpr (.inl hχ)) hd₁
    · exact disjOf_intro_fal
        (List.mem_append.mpr (.inr (mem_rmv_iff.mpr ⟨hψ, he⟩)))
        (SetDeriv.of_mem (Set.mem_insert ..))
  refine hT _ _ ?_ ?_ (guard_append hg₁) hd
  · intro ψ hψ
    rcases List.mem_append.mp hψ with h | h
    · exact hDs₁ ψ h
    · obtain ⟨hin, hne⟩ := mem_rmv_iff.mp h
      rcases hDs₂ ψ hin with rfl | h'
      · exact absurd rfl hne
      · exact h'
  · intro ψ hψ
    rcases List.mem_append.mp hψ with h | h
    exacts [hTs₁ ψ h, hTs₂ ψ h]

/-! ## The constructive Lindenbaum extension -/

/-- One decided extension step: add `φ` to `val` if that is consistent,
otherwise to `fal`.  (`noncomputable` only because Mathlib's
`Finset.toList` picks a representative by choice; the fold is effective
once the closure is enumerated as a list, which the model-construction
layer does.) -/
noncomputable def extendStep (T : FTheory) (φ : PLLFormula) : FTheory :=
  if (T.insVal φ).Cons then T.insVal φ else T.insFal φ

/-- Fold the decided extension over a list of formulas. -/
noncomputable def extendAll (T : FTheory) (l : List PLLFormula) : FTheory :=
  l.foldl extendStep T

theorem extendStep_cons {T : FTheory} (hT : T.Cons) (φ : PLLFormula) :
    (extendStep T φ).Cons := by
  unfold extendStep
  split
  · assumption
  · exact (cons_insVal_or_insFal hT φ).resolve_left (by assumption)

theorem extendStep_le (T : FTheory) (φ : PLLFormula) :
    T.le (extendStep T φ) := by
  unfold extendStep
  split
  · exact ⟨Finset.subset_insert .., subset_rfl, subset_rfl⟩
  · exact ⟨subset_rfl, Finset.subset_insert .., subset_rfl⟩

theorem extendStep_mem (T : FTheory) (φ : PLLFormula) :
    φ ∈ (extendStep T φ).val ∨ φ ∈ (extendStep T φ).fal := by
  unfold extendStep
  split
  · exact .inl (Finset.mem_insert_self ..)
  · exact .inr (Finset.mem_insert_self ..)

theorem extendStep_mfal (T : FTheory) (φ : PLLFormula) :
    (extendStep T φ).mfal = T.mfal := by
  unfold extendStep
  split <;> rfl

theorem extendAll_cons {T : FTheory} (hT : T.Cons) (l : List PLLFormula) :
    (extendAll T l).Cons := by
  induction l generalizing T with
  | nil => exact hT
  | cons φ l ih => exact ih (extendStep_cons hT φ)

theorem extendAll_le (T : FTheory) (l : List PLLFormula) :
    T.le (extendAll T l) := by
  induction l generalizing T with
  | nil => exact FTheory.le_refl T
  | cons φ l ih =>
      exact FTheory.le_trans (extendStep_le T φ) (ih (extendStep T φ))

theorem extendAll_mfal (T : FTheory) (l : List PLLFormula) :
    (extendAll T l).mfal = T.mfal := by
  induction l generalizing T with
  | nil => rfl
  | cons φ l ih =>
      rw [extendAll, List.foldl_cons, ← extendAll, ih, extendStep_mfal]

theorem extendAll_total (T : FTheory) (l : List PLLFormula) :
    ∀ φ ∈ l, φ ∈ (extendAll T l).val ∨ φ ∈ (extendAll T l).fal := by
  induction l generalizing T with
  | nil => intro φ h; cases h
  | cons ψ l ih =>
      intro φ h
      rw [extendAll, List.foldl_cons, ← extendAll]
      rcases List.mem_cons.mp h with rfl | h'
      · rcases extendStep_mem T φ with hv | hf
        · exact .inl ((extendAll_le (extendStep T φ) l).1 hv)
        · exact .inr ((extendAll_le (extendStep T φ) l).2.1 hf)
      · exact ih (extendStep T ψ) φ h'

/-! ## Closure-maximal triples and the Lindenbaum theorem -/

/-- All three components inside the closure. -/
def InCl (cl : Finset PLLFormula) (T : FTheory) : Prop :=
  T.val ⊆ cl ∧ T.fal ⊆ cl ∧ T.mfal ⊆ cl

/-- Closure-maximality: consistent, inside the closure, and total on it —
every closure formula is validated or falsified.  (This is what the
classical Lemma 4.2 suite actually consumes: extension-failure witnesses
for closure formulas are derivable from totality plus consistency.) -/
def MaxIn (cl : Finset PLLFormula) (T : FTheory) : Prop :=
  T.Cons ∧ InCl cl T ∧ ∀ φ ∈ cl, φ ∈ T.val ∨ φ ∈ T.fal

/-- **Constructive Lindenbaum**: every consistent triple inside the closure
extends — by a computable fold of decided steps, no Zorn — to a
closure-maximal one with the *same* promises (`mfal` untouched, as the
truth-lemma constructions require). -/
theorem lindenbaum {cl : Finset PLLFormula} {T : FTheory}
    (hT : T.Cons) (hIn : InCl cl T) :
    ∃ T', T.le T' ∧ MaxIn cl T' ∧ T'.mfal = T.mfal := by
  refine ⟨extendAll T cl.toList, extendAll_le T _,
    ⟨extendAll_cons hT _, ?_, fun φ hφ =>
      extendAll_total T _ φ (Finset.mem_toList.mpr hφ)⟩,
    extendAll_mfal T _⟩
  -- the extension stays inside the closure
  have step : ∀ (T' : FTheory) (l : List PLLFormula), InCl cl T' →
      (∀ φ ∈ l, φ ∈ cl) → InCl cl (extendAll T' l) := by
    intro T' l
    induction l generalizing T' with
    | nil => intro h _; exact h
    | cons ψ l ih =>
        intro h hl
        rw [extendAll, List.foldl_cons, ← extendAll]
        refine ih _ ?_ (fun φ hφ => hl φ (List.mem_cons_of_mem _ hφ))
        have hψ : ψ ∈ cl := hl ψ (List.mem_cons_self ..)
        unfold extendStep
        split
        · exact ⟨Finset.insert_subset hψ h.1, h.2.1, h.2.2⟩
        · exact ⟨h.1, Finset.insert_subset hψ h.2.1, h.2.2⟩
  exact step T cl.toList hIn (fun φ hφ => Finset.mem_toList.mp hφ)

/-! ## Part 2: the Lemma 4.2 suite, closure-relative

With totality in hand, the classical witness-combination proofs collapse:
every extension-failure witness is a singleton selection. -/

open SetDeriv

namespace MaxIn

variable {cl : Finset PLLFormula} {T : FTheory}

/-- Derivability of a falsified formula is absurd. -/
theorem not_fal_deriv (hM : MaxIn cl T) {φ : PLLFormula} (hφ : φ ∈ T.fal)
    (hd : (↑T.val : Set PLLFormula) ⊩ φ) : False := by
  refine hM.1 [φ] [] (by simpa using hφ) (by simp) (by simp) ?_
  rw [disjOf_nil_right]
  exact bigOr_intro (List.mem_cons_self ..) hd

theorem not_mem_fal_of_mem_val (hM : MaxIn cl T) {φ : PLLFormula}
    (hv : φ ∈ T.val) : φ ∉ T.fal :=
  fun hf => hM.not_fal_deriv hf (of_mem (Finset.mem_coe.mpr hv))

/-- Deductive closure on the closure. -/
theorem ded_closed (hM : MaxIn cl T) {φ : PLLFormula} (hφcl : φ ∈ cl)
    (hd : (↑T.val : Set PLLFormula) ⊩ φ) : φ ∈ T.val := by
  rcases hM.2.2 φ hφcl with hv | hf
  · exact hv
  · exact (hM.not_fal_deriv hf hd).elim

/-- Primeness of the validated part. -/
theorem or_mem (hM : MaxIn cl T) (hcl : SubClosed cl) {φ ψ : PLLFormula}
    (h : φ.or ψ ∈ T.val) : φ ∈ T.val ∨ ψ ∈ T.val := by
  obtain ⟨hCons, ⟨hvcl, hfcl, hmcl⟩, htot⟩ := hM
  rcases htot φ (hcl.or_left (hvcl h)) with hv | hf
  · exact .inl hv
  rcases htot ψ (hcl.or_right (hvcl h)) with hv | hf'
  · exact .inr hv
  exfalso
  refine hCons [φ, ψ] [] ?_ (by simp) (by simp) ?_
  · intro χ hχ
    rcases List.mem_cons.mp hχ with rfl | hχ
    · simpa using hf
    · rcases List.mem_cons.mp hχ with rfl | hχ
      · simpa using hf'
      · cases hχ
  · rw [disjOf_nil_right]
    refine orE (of_mem (Finset.mem_coe.mpr h)) ?_ ?_
    · exact bigOr_intro (List.mem_cons_self ..) (of_mem (Set.mem_insert ..))
    · exact bigOr_intro (List.mem_cons_of_mem _ (List.mem_cons_self ..))
        (of_mem (Set.mem_insert ..))

/-- Implication decomposition. -/
theorem imp_mem (hM : MaxIn cl T) (hcl : SubClosed cl) {φ ψ : PLLFormula}
    (h : φ.ifThen ψ ∈ T.val) : φ ∈ T.fal ∨ ψ ∈ T.val := by
  have hφcl := hcl.imp_left (hM.2.1.1 h)
  have hψcl := hcl.imp_right (hM.2.1.1 h)
  rcases hM.2.2 φ hφcl with hv | hf
  · refine .inr (hM.ded_closed hψcl ?_)
    exact mp (of_mem (Finset.mem_coe.mpr h)) (of_mem (Finset.mem_coe.mpr hv))
  · exact .inl hf

/-- Falsified disjunctions decompose conjunctively. -/
theorem fal_or (hM : MaxIn cl T) (hcl : SubClosed cl) {φ ψ : PLLFormula}
    (h : φ.or ψ ∈ T.fal) : φ ∈ T.fal ∧ ψ ∈ T.fal := by
  have hocl : φ.or ψ ∈ cl := hM.2.1.2.1 h
  constructor
  · rcases hM.2.2 φ (hcl.or_left hocl) with hv | hf
    · exact (hM.not_fal_deriv h (orL _ (of_mem (Finset.mem_coe.mpr hv)))).elim
    · exact hf
  · rcases hM.2.2 ψ (hcl.or_right hocl) with hv | hf
    · exact (hM.not_fal_deriv h (orR _ (of_mem (Finset.mem_coe.mpr hv)))).elim
    · exact hf

/-- Falsified conjunctions decompose disjunctively. -/
theorem fal_and (hM : MaxIn cl T) (hcl : SubClosed cl) {φ ψ : PLLFormula}
    (h : φ.and ψ ∈ T.fal) : φ ∈ T.fal ∨ ψ ∈ T.fal := by
  have hacl : φ.and ψ ∈ cl := hM.2.1.2.1 h
  rcases hM.2.2 φ (hcl.and_left hacl) with hv | hf
  · rcases hM.2.2 ψ (hcl.and_right hacl) with hv' | hf'
    · exact (hM.not_fal_deriv h (map₂ (fun p₁ p₂ => .andIntro p₁ p₂)
        (of_mem (Finset.mem_coe.mpr hv))
        (of_mem (Finset.mem_coe.mpr hv')))).elim
    · exact .inr hf'
  · exact .inl hf

/-- Modally falsified formulas are falsified. -/
theorem mfal_sub_fal (hM : MaxIn cl T) {φ : PLLFormula} (h : φ ∈ T.mfal) :
    φ ∈ T.fal := by
  rcases hM.2.2 φ (hM.2.1.2.2 h) with hv | hf
  · exfalso
    refine hM.1 [] [φ] (by simp) (by simpa using h) (by simp) ?_
    rw [disjOf_nil_left]
    refine map (fun p => .laxIntro p) ?_
    exact bigOr_intro (List.mem_cons_self ..) (of_mem (Finset.mem_coe.mpr hv))
  · exact hf

end MaxIn

/-! ## Part 3: the finite canonical model and the truth lemma -/

/-- The finite canonical model over a closure: worlds are the
closure-maximal triples; `Rᵢ` is inclusion on `val`, `Rₘ` inclusion on
`val` and `mfal`; atoms outside the closure hold everywhere (the
filtration's convention, needed for `full_F`). -/
def canonFin (cl : Finset PLLFormula) : ConstraintModel where
  W := {T : FTheory // MaxIn cl T}
  Ri T T' := T.1.val ⊆ T'.1.val
  Rm T T' := T.1.val ⊆ T'.1.val ∧ T.1.mfal ⊆ T'.1.mfal
  F := {T | PLLFormula.falsePLL ∈ T.1.val}
  V a := {T | PLLFormula.prop a ∉ cl ∨ PLLFormula.prop a ∈ T.1.val}
  refl_i _ := subset_rfl
  trans_i h h' := h.trans h'
  refl_m _ := ⟨subset_rfl, subset_rfl⟩
  trans_m h h' := ⟨h.1.trans h'.1, h.2.trans h'.2⟩
  sub_mi h := h.1
  hered_F h hw := h hw
  hered_V h hw := hw.imp_right (fun h' => h h')
  full_F {a} {T} hw := by
    by_cases hcl : PLLFormula.prop a ∈ cl
    · exact .inr (T.2.ded_closed hcl
        (falso _ (of_mem (Finset.mem_coe.mpr hw))))
    · exact .inl hcl

/-- **The truth lemma**, finitely: on the finite canonical model over a
subformula-closed closure, membership in `val` forces and membership in
`fal` refutes — with all three extension steps supplied by the
constructive `lindenbaum`. -/
theorem truth_lemma {cl : Finset PLLFormula} (hcl : SubClosed cl) :
    ∀ (φ : PLLFormula), φ ∈ cl → ∀ T : (canonFin cl).W,
      (φ ∈ T.1.val → (canonFin cl).force T φ) ∧
        (φ ∈ T.1.fal → ¬ (canonFin cl).force T φ) := by
  intro φ
  induction φ with
  | prop a =>
      intro hφ T
      refine ⟨fun h => .inr h, fun h hf => ?_⟩
      rcases hf with hout | hv
      · exact hout (T.2.2.1.2.1 h)
      · exact T.2.not_fal_deriv h (of_mem (Finset.mem_coe.mpr hv))
  | falsePLL =>
      intro hφ T
      refine ⟨fun h => h, fun h hf => ?_⟩
      exact T.2.not_fal_deriv h (of_mem (Finset.mem_coe.mpr hf))
  | and φ ψ ihφ ihψ =>
      intro hφ T
      have hφ₁ := hcl.and_left hφ
      have hψ₁ := hcl.and_right hφ
      constructor
      · intro h
        have h₁ : φ ∈ T.1.val := T.2.ded_closed hφ₁
          (map (fun p => .andElim1 p) (of_mem (Finset.mem_coe.mpr h)))
        have h₂ : ψ ∈ T.1.val := T.2.ded_closed hψ₁
          (map (fun p => .andElim2 p) (of_mem (Finset.mem_coe.mpr h)))
        exact ⟨(ihφ hφ₁ T).1 h₁, (ihψ hψ₁ T).1 h₂⟩
      · intro h hf
        rcases T.2.fal_and hcl h with h' | h'
        · exact (ihφ hφ₁ T).2 h' hf.1
        · exact (ihψ hψ₁ T).2 h' hf.2
  | or φ ψ ihφ ihψ =>
      intro hφ T
      have hφ₁ := hcl.or_left hφ
      have hψ₁ := hcl.or_right hφ
      constructor
      · intro h
        rcases T.2.or_mem hcl h with h' | h'
        · exact .inl ((ihφ hφ₁ T).1 h')
        · exact .inr ((ihψ hψ₁ T).1 h')
      · intro h hf
        obtain ⟨h₁, h₂⟩ := T.2.fal_or hcl h
        rcases hf with hf | hf
        · exact (ihφ hφ₁ T).2 h₁ hf
        · exact (ihψ hψ₁ T).2 h₂ hf
  | ifThen φ ψ ihφ ihψ =>
      intro hφ T
      have hφ₁ := hcl.imp_left hφ
      have hψ₁ := hcl.imp_right hφ
      constructor
      · intro h T' hle hfφ
        rcases T'.2.imp_mem hcl (hle h) with h'' | h''
        · exact absurd hfφ ((ihφ hφ₁ T').2 h'')
        · exact (ihψ hψ₁ T').1 h''
      · intro h hf
        -- extend ⟨insert φ val, {ψ}, ∅⟩ by the constructive Lindenbaum
        have hcons : (⟨insert φ T.1.val, {ψ}, ∅⟩ : FTheory).Cons := by
          intro Ds Ts hDs hTs hg hder
          have hTs' : Ts = [] := by
            cases Ts with
            | nil => rfl
            | cons K Ts => simpa using hTs K (List.mem_cons_self ..)
          subst hTs'
          rw [disjOf_nil_right] at hder
          have hψd : (insert φ (↑T.1.val : Set PLLFormula)) ⊩ ψ := by
            refine bigOr_collapse (fun χ hχ => ?_) (by simpa using hder)
            simpa using hDs χ hχ
          exact T.2.not_fal_deriv h (deduct hψd)
        obtain ⟨T', hle, hM', _⟩ := lindenbaum hcons
          ⟨Finset.insert_subset hφ₁ T.2.2.1.1,
           Finset.singleton_subset_iff.mpr hψ₁, Finset.empty_subset _⟩
        have hRi : T.1.val ⊆ T'.val :=
          (Finset.subset_insert ..).trans hle.1
        have hfφ' : (canonFin cl).force ⟨T', hM'⟩ φ :=
          (ihφ hφ₁ ⟨T', hM'⟩).1 (hle.1 (Finset.mem_insert_self ..))
        have hfψ' : ¬ (canonFin cl).force ⟨T', hM'⟩ ψ :=
          (ihψ hψ₁ ⟨T', hM'⟩).2 (hle.2.1 (Finset.mem_singleton_self ..))
        exact hfψ' (hf ⟨T', hM'⟩ hRi hfφ')
  | somehow φ ih =>
      intro hφ T
      have hφ₁ := hcl.lax hφ
      constructor
      · intro h T₁ hle
        -- ◯φ ∈ val ⊆ val₁; extend ⟨insert φ val₁, ∅, mfal₁⟩
        have hcons : (⟨insert φ T₁.1.val, ∅, T₁.1.mfal⟩ : FTheory).Cons := by
          intro Ds Ts hDs hTs hg hder
          have hDs' : Ds = [] := by
            cases Ds with
            | nil => rfl
            | cons D Ds => simpa using hDs D (List.mem_cons_self ..)
          subst hDs'
          cases Ts with
          | nil => exact hg rfl
          | cons K Ts =>
              rw [disjOf_nil_left] at hder
              have himp : (↑T₁.1.val : Set PLLFormula) ⊩
                  φ.ifThen (.somehow (bigOr (K :: Ts))) :=
                deduct (by simpa using hder)
              have hlax : (↑T₁.1.val : Set PLLFormula) ⊩
                  .somehow (bigOr (K :: Ts)) :=
                somehow_bind (of_mem (Finset.mem_coe.mpr (hle h))) himp
              refine T₁.2.1 [] (K :: Ts) (by simp) (by simpa using hTs)
                (by simp) ?_
              rwa [disjOf_nil_left]
        obtain ⟨T₂, hle₂, hM₂, hmf₂⟩ := lindenbaum hcons
          ⟨Finset.insert_subset hφ₁ T₁.2.2.1.1, Finset.empty_subset _,
           T₁.2.2.1.2.2⟩
        refine ⟨⟨T₂, hM₂⟩,
          ⟨(Finset.subset_insert ..).trans hle₂.1, hmf₂ ▸ subset_rfl⟩, ?_⟩
        exact (ih hφ₁ ⟨T₂, hM₂⟩).1 (hle₂.1 (Finset.mem_insert_self ..))
      · intro h hf
        -- extend ⟨val, ∅, {φ}⟩: its Rₘ-successors all refute φ
        have hcons : (⟨T.1.val, ∅, {φ}⟩ : FTheory).Cons := by
          intro Ds Ts hDs hTs hg hder
          have hDs' : Ds = [] := by
            cases Ds with
            | nil => rfl
            | cons D Ds => simpa using hDs D (List.mem_cons_self ..)
          subst hDs'
          cases Ts with
          | nil => exact hg rfl
          | cons K Ts =>
              rw [disjOf_nil_left] at hder
              have hφd : (↑T.1.val : Set PLLFormula) ⊩ .somehow φ := by
                refine somehow_mono hder ?_
                refine bigOr_collapse (fun χ hχ => ?_)
                  (of_mem (Set.mem_insert ..))
                simpa using hTs χ hχ
              exact T.2.not_fal_deriv h hφd
        obtain ⟨T', hle, hM', hmf'⟩ := lindenbaum hcons
          ⟨T.2.2.1.1, Finset.empty_subset _,
           Finset.singleton_subset_iff.mpr hφ₁⟩
        obtain ⟨T₂, hRm, hfφ⟩ := hf ⟨T', hM'⟩ hle.1
        have hmem : φ ∈ T₂.1.mfal :=
          hRm.2 (hmf' ▸ Finset.mem_singleton_self ..)
        exact (ih hφ₁ T₂).2 (T₂.2.mfal_sub_fal hmem) hfφ

/-! ## The closure of a sequent, and countermodel existence -/

/-- The subformula closure of a sequent, `⊥` included. -/
def clOf (Γ : List PLLFormula) (C : PLLFormula) : Finset PLLFormula :=
  insert .falsePLL ((C :: Γ).foldr (fun φ s => subF φ ∪ s) ∅)

theorem mem_foldr_subF {l : List PLLFormula} {φ : PLLFormula} :
    φ ∈ l.foldr (fun φ s => subF φ ∪ s) ∅ ↔ ∃ χ ∈ l, φ ∈ subF χ := by
  induction l with
  | nil => simp
  | cons ψ l ih => simp [ih]

theorem mem_clOf {Γ : List PLLFormula} {C : PLLFormula} :
    ∀ φ ∈ C :: Γ, φ ∈ clOf Γ C := by
  intro φ hφ
  exact Finset.mem_insert_of_mem
    (mem_foldr_subF.mpr ⟨φ, hφ, self_mem_subF φ⟩)

theorem clOf_subClosed (Γ : List PLLFormula) (C : PLLFormula) :
    SubClosed (clOf Γ C) := by
  have step : ∀ {φ ψ : PLLFormula}, ψ ∈ subF φ → φ ∈ clOf Γ C →
      ψ ∈ clOf Γ C := by
    intro φ ψ hψ hφ
    rcases Finset.mem_insert.mp hφ with rfl | hφ
    · simp only [subF, Finset.mem_singleton] at hψ
      subst hψ
      exact Finset.mem_insert_self ..
    · obtain ⟨χ, hχ, hφχ⟩ := mem_foldr_subF.mp hφ
      exact Finset.mem_insert_of_mem
        (mem_foldr_subF.mpr ⟨χ, hχ, subF_trans χ hφχ hψ⟩)
  refine ⟨Finset.mem_insert_self .., ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first
      | (intro φ ψ h; exact step (by simp [subF]) h)
      | (intro φ h; exact step (by simp [subF]) h)

/-- **Countermodel existence, finitely and without Zorn**: every
underivable sequent is refuted at a world of its finite canonical model —
the hypotheses forced, the conclusion not. -/
theorem finite_canonical_countermodel {Γ : List PLLFormula} {C : PLLFormula}
    (h : ¬ Nonempty (LaxND Γ C)) :
    ∃ T : (canonFin (clOf Γ C)).W,
      (∀ ψ ∈ Γ, (canonFin (clOf Γ C)).force T ψ) ∧
        ¬ (canonFin (clOf Γ C)).force T C := by
  have hcons : (⟨Γ.toFinset, {C}, ∅⟩ : FTheory).Cons := by
    intro Ds Ts hDs hTs hg hder
    have hTs' : Ts = [] := by
      cases Ts with
      | nil => rfl
      | cons K Ts => simpa using hTs K (List.mem_cons_self ..)
    subst hTs'
    rw [disjOf_nil_right] at hder
    have hd : (↑Γ.toFinset : Set PLLFormula) ⊩ C := by
      refine bigOr_collapse (fun χ hχ => ?_) hder
      simpa using hDs χ hχ
    obtain ⟨L, hL, ⟨p⟩⟩ := hd
    exact h ⟨p.rename fun ψ hψ => by simpa using hL ψ hψ⟩
  obtain ⟨T, hle, hM, _⟩ := lindenbaum hcons
    ⟨fun ψ hψ => mem_clOf ψ (List.mem_cons_of_mem _
        (List.mem_toFinset.mp hψ)),
     Finset.singleton_subset_iff.mpr (mem_clOf C (List.mem_cons_self ..)),
     Finset.empty_subset _⟩
  refine ⟨⟨T, hM⟩, fun ψ hψ => ?_, ?_⟩
  · exact (truth_lemma (clOf_subClosed Γ C) ψ
      (mem_clOf ψ (List.mem_cons_of_mem _ hψ)) ⟨T, hM⟩).1
      (hle.1 (List.mem_toFinset.mpr hψ))
  · exact (truth_lemma (clOf_subClosed Γ C) C
      (mem_clOf C (List.mem_cons_self ..)) ⟨T, hM⟩).2
      (hle.2.1 (Finset.mem_singleton_self ..))

/-! ## Part 4: enumeration into a `FinCM`, and emitter completeness -/

instance : Inhabited FTheory := ⟨⟨∅, ∅, ∅⟩⟩

noncomputable instance (cl : Finset PLLFormula) :
    DecidablePred (MaxIn cl) := fun T => by
  unfold MaxIn InCl
  infer_instance

/-- All closure-maximal triples, as a finset. -/
noncomputable def worldFinset (cl : Finset PLLFormula) : Finset FTheory :=
  ((cl.powerset ×ˢ cl.powerset ×ˢ cl.powerset).image
    fun p => (⟨p.1, p.2.1, p.2.2⟩ : FTheory)).filter (MaxIn cl)

theorem mem_worldFinset {cl : Finset PLLFormula} {T : FTheory} :
    T ∈ worldFinset cl ↔ MaxIn cl T := by
  simp only [worldFinset, Finset.mem_filter, Finset.mem_image,
    Finset.mem_product]
  constructor
  · rintro ⟨_, hM⟩
    exact hM
  · intro hM
    exact ⟨⟨(T.val, T.fal, T.mfal),
      ⟨Finset.mem_powerset.mpr hM.2.1.1,
       Finset.mem_powerset.mpr hM.2.1.2.1,
       Finset.mem_powerset.mpr hM.2.1.2.2⟩, rfl⟩, hM⟩

/-- The enumerated worlds. -/
noncomputable def worldList (cl : Finset PLLFormula) : List FTheory :=
  (worldFinset cl).toList

theorem mem_worldList {cl : Finset PLLFormula} {T : FTheory} :
    T ∈ worldList cl ↔ MaxIn cl T := by
  rw [worldList, Finset.mem_toList, mem_worldFinset]

/-- The finite canonical model as checker data. -/
noncomputable def canonFinCM (cl : Finset PLLFormula) : FinCM :=
  { n := (worldList cl).length
    ri := (List.range (worldList cl).length).flatMap fun i =>
      (List.range (worldList cl).length).filterMap fun j =>
        if (worldList cl)[i]!.val ⊆ (worldList cl)[j]!.val then
          some (i, j) else none
    rm := (List.range (worldList cl).length).flatMap fun i =>
      (List.range (worldList cl).length).filterMap fun j =>
        if (worldList cl)[i]!.val ⊆ (worldList cl)[j]!.val ∧
            (worldList cl)[i]!.mfal ⊆ (worldList cl)[j]!.mfal then
          some (i, j) else none
    fall := (List.range (worldList cl).length).filter fun i =>
      decide (PLLFormula.falsePLL ∈ (worldList cl)[i]!.val)
    val := (List.range (worldList cl).length).flatMap fun i =>
      (worldList cl)[i]!.val.toList.filterMap fun φ =>
        match φ with | .prop a => some (i, a) | _ => none }

@[simp] theorem canonFinCM_n (cl : Finset PLLFormula) :
    (canonFinCM cl).n = (worldList cl).length := rfl

/-! ### Characterisation of the built data -/

section Charac

variable {cl : Finset PLLFormula}

private theorem wl_get_eq {i : Nat} (hi : i < (worldList cl).length) :
    (worldList cl)[i]! = (worldList cl)[i] := by
  exact getElem!_pos (worldList cl) i hi

theorem ri_mem_iff {i j : Nat} :
    (i, j) ∈ (canonFinCM cl).ri ↔
      i < (worldList cl).length ∧ j < (worldList cl).length ∧
        (worldList cl)[i]!.val ⊆ (worldList cl)[j]!.val := by
  simp only [canonFinCM, List.mem_flatMap, List.mem_filterMap,
    List.mem_range]
  constructor
  · rintro ⟨i', hi', j', hj', hif⟩
    split at hif
    · simp only [Option.some.injEq, Prod.mk.injEq] at hif
      obtain ⟨rfl, rfl⟩ := hif
      exact ⟨hi', hj', by assumption⟩
    · cases hif
  · rintro ⟨hi, hj, hsub⟩
    exact ⟨i, hi, j, hj, if_pos hsub⟩

theorem rm_mem_iff {i j : Nat} :
    (i, j) ∈ (canonFinCM cl).rm ↔
      i < (worldList cl).length ∧ j < (worldList cl).length ∧
        ((worldList cl)[i]!.val ⊆ (worldList cl)[j]!.val ∧
          (worldList cl)[i]!.mfal ⊆ (worldList cl)[j]!.mfal) := by
  simp only [canonFinCM, List.mem_flatMap, List.mem_filterMap,
    List.mem_range]
  constructor
  · rintro ⟨i', hi', j', hj', hif⟩
    split at hif
    · simp only [Option.some.injEq, Prod.mk.injEq] at hif
      obtain ⟨rfl, rfl⟩ := hif
      exact ⟨hi', hj', by assumption⟩
    · cases hif
  · rintro ⟨hi, hj, hsub⟩
    exact ⟨i, hi, j, hj, if_pos hsub⟩

theorem fall_mem_iff {i : Nat} :
    i ∈ (canonFinCM cl).fall ↔
      i < (worldList cl).length ∧
        PLLFormula.falsePLL ∈ (worldList cl)[i]!.val := by
  simp only [canonFinCM, List.mem_filter, List.mem_range,
    decide_eq_true_eq]

theorem valPair_mem_iff {i : Nat} {a : String} :
    (i, a) ∈ (canonFinCM cl).val ↔
      i < (worldList cl).length ∧
        PLLFormula.prop a ∈ (worldList cl)[i]!.val := by
  simp only [canonFinCM, List.mem_flatMap, List.mem_filterMap,
    List.mem_range]
  constructor
  · rintro ⟨i', hi', φ, hφ, hmatch⟩
    cases φ with
    | prop b =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hmatch
        obtain ⟨rfl, rfl⟩ := hmatch
        exact ⟨hi', Finset.mem_toList.mp hφ⟩
    | falsePLL => cases hmatch
    | and _ _ => cases hmatch
    | or _ _ => cases hmatch
    | ifThen _ _ => cases hmatch
    | somehow _ => cases hmatch
  · rintro ⟨hi, hmem⟩
    exact ⟨i, hi, .prop a, Finset.mem_toList.mpr hmem, rfl⟩

theorem maxIn_get {i : Nat} (hi : i < (worldList cl).length) :
    MaxIn cl (worldList cl)[i]! := by
  rw [wl_get_eq hi]
  exact mem_worldList.mp (List.getElem_mem ..)

theorem riB_iff {i j : Nat} (hi : i < (worldList cl).length)
    (hj : j < (worldList cl).length) :
    (canonFinCM cl).riB i j = true ↔
      (worldList cl)[i]!.val ⊆ (worldList cl)[j]!.val := by
  simp only [FinCM.riB, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro (hmem | rfl)
    · exact (ri_mem_iff.mp hmem).2.2
    · exact subset_rfl
  · intro h
    exact .inl (ri_mem_iff.mpr ⟨hi, hj, h⟩)

theorem rmB_iff {i j : Nat} (hi : i < (worldList cl).length)
    (hj : j < (worldList cl).length) :
    (canonFinCM cl).rmB i j = true ↔
      ((worldList cl)[i]!.val ⊆ (worldList cl)[j]!.val ∧
        (worldList cl)[i]!.mfal ⊆ (worldList cl)[j]!.mfal) := by
  simp only [FinCM.rmB, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro (hmem | rfl)
    · exact (rm_mem_iff.mp hmem).2.2
    · exact ⟨subset_rfl, subset_rfl⟩
  · intro h
    exact .inl (rm_mem_iff.mpr ⟨hi, hj, h⟩)

theorem fallB_iff {i : Nat} (hi : i < (worldList cl).length) :
    (canonFinCM cl).fallB i = true ↔
      PLLFormula.falsePLL ∈ (worldList cl)[i]!.val := by
  simp only [FinCM.fallB, decide_eq_true_eq]
  constructor
  · intro h
    exact (fall_mem_iff.mp h).2
  · intro h
    exact fall_mem_iff.mpr ⟨hi, h⟩

theorem valB_of_mem {i : Nat} {a : String}
    (hi : i < (worldList cl).length)
    (h : PLLFormula.prop a ∈ (worldList cl)[i]!.val) :
    (canonFinCM cl).valB i a = true := by
  simp only [FinCM.valB, Bool.or_eq_true, decide_eq_true_eq]
  exact .inl (valPair_mem_iff.mpr ⟨hi, h⟩)

theorem valB_iff {i : Nat} {a : String} (hi : i < (worldList cl).length)
    (ha : PLLFormula.prop a ∈ cl) :
    (canonFinCM cl).valB i a = true ↔
      PLLFormula.prop a ∈ (worldList cl)[i]!.val := by
  constructor
  · intro h
    simp only [FinCM.valB, FinCM.fallB, Bool.or_eq_true,
      decide_eq_true_eq] at h
    rcases h with hmem | hfall
    · exact (valPair_mem_iff.mp hmem).2
    · exact (maxIn_get hi).ded_closed ha (falso _ (of_mem
        (Finset.mem_coe.mpr ((fall_mem_iff.mp hfall).2))))
  · exact valB_of_mem hi

/-- The built model satisfies the frame conditions. -/
theorem canonFinCM_wf : (canonFinCM cl).WellFormed := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro w hw v hv u hu h₁ h₂
    exact (riB_iff hw hu).mpr
      (((riB_iff hw hv).mp h₁).trans ((riB_iff hv hu).mp h₂))
  · intro w hw v hv u hu h₁ h₂
    obtain ⟨ha₁, hb₁⟩ := (rmB_iff hw hv).mp h₁
    obtain ⟨ha₂, hb₂⟩ := (rmB_iff hv hu).mp h₂
    exact (rmB_iff hw hu).mpr ⟨ha₁.trans ha₂, hb₁.trans hb₂⟩
  · intro w hw v hv h
    exact (riB_iff hw hv).mpr ((rmB_iff hw hv).mp h).1
  · intro w hw v hv h hf
    exact (fallB_iff hv).mpr ((riB_iff hw hv).mp h ((fallB_iff hw).mp hf))
  · intro p hp v hv h
    obtain ⟨hi, hmem⟩ := valPair_mem_iff.mp hp
    exact valB_of_mem hv ((riB_iff hi hv).mp h hmem)

/-- The world of an index. -/
noncomputable def wAt (i : Fin (canonFinCM cl).n) : (canonFin cl).W :=
  ⟨(worldList cl)[i.1]!, maxIn_get i.2⟩

theorem exists_idx (T : (canonFin cl).W) :
    ∃ i : Fin (canonFinCM cl).n, (worldList cl)[i.1]! = T.1 := by
  have hmem : T.1 ∈ worldList cl := mem_worldList.mpr T.2
  obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hmem
  exact ⟨⟨i, hi⟩, by rw [wl_get_eq hi]; exact heq⟩

/-- **The transfer lemma**: on closure formulas, forcing in the checker
model coincides with forcing in the finite canonical model. -/
theorem transfer (hcl : SubClosed cl) :
    ∀ φ, φ ∈ cl → ∀ i : Fin (canonFinCM cl).n,
      ((canonFinCM cl).toModel canonFinCM_wf).force i φ ↔
        (canonFin cl).force (wAt i) φ := by
  intro φ
  induction φ with
  | prop a =>
      intro hφ i
      constructor
      · intro h
        exact .inr ((valB_iff i.2 hφ).mp h)
      · rintro (hout | hv)
        · exact absurd hφ hout
        · exact (valB_iff i.2 hφ).mpr hv
  | falsePLL =>
      intro hφ i
      exact fallB_iff i.2
  | and φ ψ ihφ ihψ =>
      intro hφ i
      exact and_congr (ihφ (hcl.and_left hφ) i) (ihψ (hcl.and_right hφ) i)
  | or φ ψ ihφ ihψ =>
      intro hφ i
      exact or_congr (ihφ (hcl.or_left hφ) i) (ihψ (hcl.or_right hφ) i)
  | ifThen φ ψ ihφ ihψ =>
      intro hφ i
      have hφ₁ := hcl.imp_left hφ
      have hψ₁ := hcl.imp_right hφ
      constructor
      · intro H T' hle hφ'
        obtain ⟨j, hj⟩ := exists_idx T'
        have hwj : wAt j = T' := Subtype.ext hj
        have hri : (canonFinCM cl).riB i.1 j.1 = true :=
          (riB_iff i.2 j.2).mpr (by rw [hj]; exact hle)
        have hφj : ((canonFinCM cl).toModel canonFinCM_wf).force j φ :=
          (ihφ hφ₁ j).mpr (by rw [hwj]; exact hφ')
        have := (ihψ hψ₁ j).mp (H j hri hφj)
        rwa [hwj] at this
      · intro H v hri hφv
        have hsub := (riB_iff i.2 v.2).mp hri
        exact (ihψ hψ₁ v).mpr (H (wAt v) hsub ((ihφ hφ₁ v).mp hφv))
  | somehow φ ih =>
      intro hφ i
      have hφ₁ := hcl.lax hφ
      constructor
      · intro H T' hle
        obtain ⟨j, hj⟩ := exists_idx T'
        have hwj : wAt j = T' := Subtype.ext hj
        have hri : (canonFinCM cl).riB i.1 j.1 = true :=
          (riB_iff i.2 j.2).mpr (by rw [hj]; exact hle)
        obtain ⟨u, hrm, hu⟩ := H j hri
        refine ⟨wAt u, ?_, (ih hφ₁ u).mp hu⟩
        have := (rmB_iff j.2 u.2).mp hrm
        rw [← hwj]
        exact this
      · intro H v hri
        have hsub := (riB_iff i.2 v.2).mp hri
        obtain ⟨T₂, hRm, hf⟩ := H (wAt v) hsub
        obtain ⟨u, hu⟩ := exists_idx T₂
        have hwu : wAt u = T₂ := Subtype.ext hu
        refine ⟨u, (rmB_iff v.2 u.2).mpr (by rw [hu]; exact hRm), ?_⟩
        exact (ih hφ₁ u).mpr (by rw [hwu]; exact hf)

/-- **Emitter completeness**: every underivable sequent has a finite
countermodel *as checker data* — a `FinCM` and a world passing the
verified `checkB`.  Composed with `realP_refutes_sequent` (`PLLEvidence.lean`),
this closes the completeness of PLL for `⊩ᵖ`-realisability over decorated
finite models — see `PLLRealCompleteness.lean`. -/
theorem emitter_completeness {Γ : List PLLFormula} {C : PLLFormula}
    (h : ¬ Nonempty (LaxND Γ C)) :
    ∃ (M : FinCM) (w : Nat), FinCM.checkB M w Γ C = true := by
  obtain ⟨T, hΓ, hC⟩ := finite_canonical_countermodel h
  obtain ⟨i, hieq⟩ := exists_idx T
  have hwT : wAt i = T := Subtype.ext hieq
  refine ⟨canonFinCM (clOf Γ C), i.1,
    FinCM.checkB_intro canonFinCM_wf i.2 ?_ ?_⟩
  · intro ψ hψ
    refine (transfer (clOf_subClosed Γ C) ψ
      (mem_clOf ψ (List.mem_cons_of_mem _ hψ)) i).mpr ?_
    rw [hwT]
    exact hΓ ψ hψ
  · intro hf
    refine hC ?_
    rw [← hwT]
    exact (transfer (clOf_subClosed Γ C) C
      (mem_clOf C (List.mem_cons_self ..)) i).mp hf

end Charac

end FinComp
end PLLND

#print axioms PLLND.FinComp.lindenbaum
#print axioms PLLND.FinComp.cons_insVal_or_insFal
#print axioms PLLND.FinComp.truth_lemma
#print axioms PLLND.FinComp.finite_canonical_countermodel
#print axioms PLLND.FinComp.emitter_completeness
