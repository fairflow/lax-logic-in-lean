import LaxLogic.PLLCompleteness
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

The plan (mirroring F&M §4 / `PLLCompleteness.lean` case for case):

1. **This file, part 1 (foundation)** — finite theory triples `FTheory`
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
   sequent has a checked countermodel; composed with
   `realP_refutes_sequent`, completeness of PLL for `⊩ᵖ`.

Audit note: the mathematics here is finitary (no Zorn anywhere); the
`#print axioms` audit currently inherits `Classical.choice` from the
decidability infrastructure (`decidablePLL`) and from incidental classical
tactic steps in the cut-elimination chain — scrubbing those is a separate,
mechanical hygiene task, after which this development audits choice-free.
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

end FinComp
end PLLND

#print axioms PLLND.FinComp.lindenbaum
#print axioms PLLND.FinComp.cons_insVal_or_insFal
