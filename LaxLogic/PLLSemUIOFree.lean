import LaxLogic.PLLSemUI

/-!
# The ◯-free fragment under the semantic quantifiers: agreement with IPC

For a ◯-free formula `M` in the single variable `p` (the
Rieger–Nishimura fragment RN({p})), Pitts's IPC quantifiers take
CLOSED ◯-free values — for one variable that means `⊤` (when `⊢ M`)
or `⊥` (when `⊬ M`).  Over PLL the closed p-free formulas form the
infinite ladder RN(◯,{}), so a priori a ◯-free row could acquire a
ladder value (`◯⊥`, `¬¬◯⊥`, …) — the quantifier would ESCAPE the
fragment at the ground floor, and the variable-by-variable climb
through the free variables of a general formula would leave every
fragment it enters.

This file PROVES the necessity half of agreement: the value of an
underivable ◯-free row is excluded from BOTH derivability cones over
the ladder's two atoms.

* `topExt C` — the fallible-top extension: one fallible world
  adjoined above everything, constraint-reachable from everywhere.
  `topExt_force_iff`: forcing of ◯-FREE formulas at original worlds
  is unchanged (the top forces everything, so it never constrains an
  implication); `topExt_boxBot`: `◯⊥` becomes GLOBAL.  Hence a
  ◯-free M refuted anywhere is refuted at a ◯⊥-world:
  **no lower bound of M lies in the ◯⊥-cone**
  (`no_lower_bound_above_boxBot`).
* `flat_neg_boxBot`: in a fallibility-free model `¬◯⊥` is global.
  Hence a ◯-free M refuted over such a model (e.g. any IPC
  countermodel, read as a PLL model with `F = ∅`) has
  **no lower bound in the ¬◯⊥-cone**
  (`no_lower_bound_above_negBoxBot` — this half needs no
  ◯-freeness).

Consequently (`semAll_value_bot_of_cones`): a ∀p-value of such an M
that lies in either cone — or is `⊥` — must be `⊥`.  Every closed
ladder rung tested so far lies in one of the two cones
(oracle-checked; the coverage of RN(◯,{}) ∖ {⊥} by the two cones is
the remaining OPEN step to the unconditional statement), so closed
values of underivable ◯-free rows collapse to `⊥` — exactly Pitts's
value, evidence that the semantic route can climb the free variables
without leaving the fragment tower.  The dual ∃-side exclusions
(`semEx_value_not_derives_negBoxBot`, `semEx_value_not_derives_boxBot`)
pin the ∃p-value of a consistent ◯-free row away from both coatoms'
cones dually.

The EXISTENCE half (that `⊥` actually satisfies the ∀p-spec for each
underivable ◯-free row, i.e. every non-fallible world has a p-variant
refuting M) remains per-row work — the reconstruction-law sweep
certifies it row by row to weight 8 via `isSemAll_of_poolRec`.
-/

open PLLFormula

namespace PLLND
namespace SemUI

/-- ◯-freeness, computably. -/
def boxFree : PLLFormula → Bool
  | .prop _ => true
  | .falsePLL => true
  | .and φ ψ => boxFree φ && boxFree ψ
  | .or φ ψ => boxFree φ && boxFree ψ
  | .ifThen φ ψ => boxFree φ && boxFree ψ
  | .somehow _ => false

/-! ## The fallible-top extension -/

/-- One fallible world adjoined above everything, constraint-reachable
from everywhere. -/
def topExt (C : ConstraintModel) : ConstraintModel where
  W := C.W ⊕ Unit
  Ri := fun a b =>
    match a, b with
    | .inl x, .inl y => C.Ri x y
    | .inl _, .inr _ => True
    | .inr _, .inl _ => False
    | .inr _, .inr _ => True
  Rm := fun a b =>
    match a, b with
    | .inl x, .inl y => C.Rm x y
    | .inl _, .inr _ => True
    | .inr _, .inl _ => False
    | .inr _, .inr _ => True
  F := fun a => match a with
    | .inl x => x ∈ C.F
    | .inr _ => True
  V := fun q a => match a with
    | .inl x => x ∈ C.V q
    | .inr _ => True
  refl_i := by
    intro a
    rcases a with x | u
    · exact C.refl_i x
    · exact True.intro
  trans_i := by
    intro a b c h₁ h₂
    rcases a with x | u <;> rcases b with y | t <;> rcases c with y' | s
    · exact C.trans_i h₁ h₂
    · exact True.intro
    · exact h₂.elim
    · exact True.intro
    · exact h₁.elim
    · exact True.intro
    · exact h₂.elim
    · exact True.intro
  refl_m := by
    intro a
    rcases a with x | u
    · exact C.refl_m x
    · exact True.intro
  trans_m := by
    intro a b c h₁ h₂
    rcases a with x | u <;> rcases b with y | t <;> rcases c with y' | s
    · exact C.trans_m h₁ h₂
    · exact True.intro
    · exact h₂.elim
    · exact True.intro
    · exact h₁.elim
    · exact True.intro
    · exact h₂.elim
    · exact True.intro
  sub_mi := by
    intro a b h
    rcases a with x | u <;> rcases b with y | t
    · exact C.sub_mi h
    · exact True.intro
    · exact h.elim
    · exact True.intro
  hered_F := by
    intro a b h hF
    rcases a with x | u <;> rcases b with y | t
    · exact C.hered_F h hF
    · exact True.intro
    · exact h.elim
    · exact True.intro
  hered_V := by
    intro q a b h hV
    rcases a with x | u <;> rcases b with y | t
    · exact C.hered_V h hV
    · exact True.intro
    · exact h.elim
    · exact True.intro
  full_F := by
    intro q a hF
    rcases a with x | u
    · exact C.full_F hF
    · exact True.intro

/-- **Forcing of ◯-free formulas at original worlds is unchanged** by
the fallible top: the new world forces everything, so it never
constrains an implication.  (False for `¬◯⊥`, which the top
destroys — ◯-freeness is essential.) -/
theorem topExt_force_iff (C : ConstraintModel) :
    ∀ {θ : PLLFormula}, boxFree θ = true →
    ∀ x : C.W, ((topExt C).force (.inl x) θ ↔ C.force x θ) := by
  intro θ
  induction θ with
  | prop a => exact fun _ _ => Iff.rfl
  | falsePLL => exact fun _ _ => Iff.rfl
  | and φ ψ ihφ ihψ =>
      intro h x
      simp only [boxFree, Bool.and_eq_true] at h
      simp only [ConstraintModel.force]
      exact and_congr (ihφ h.1 x) (ihψ h.2 x)
  | or φ ψ ihφ ihψ =>
      intro h x
      simp only [boxFree, Bool.and_eq_true] at h
      simp only [ConstraintModel.force]
      exact or_congr (ihφ h.1 x) (ihψ h.2 x)
  | ifThen φ ψ ihφ ihψ =>
      intro h x
      simp only [boxFree, Bool.and_eq_true] at h
      simp only [ConstraintModel.force]
      constructor
      · intro hf v hv hφ
        exact (ihψ h.2 v).mp (hf (.inl v) hv ((ihφ h.1 v).mpr hφ))
      · intro hf b hb hφ
        rcases b with y | u
        · exact (ihψ h.2 y).mpr (hf y hb ((ihφ h.1 y).mp hφ))
        · exact (topExt C).force_of_fallible True.intro
  | somehow φ ih =>
      intro h
      exact absurd h (by simp [boxFree])

/-- `◯⊥` holds everywhere in the extension: the fallible top is a
constraint successor of every world. -/
theorem topExt_boxBot (C : ConstraintModel) (a : (topExt C).W) :
    (topExt C).force a PLLFormula.falsePLL.somehow := by
  intro b hb
  refine ⟨.inr (), ?_, True.intro⟩
  rcases b with y | u
  · exact True.intro
  · exact True.intro

/-! ## The two cone exclusions -/

/-- **No underivable ◯-free formula has a lower bound in the
◯⊥-cone**: if some world of some model refutes M (◯-free), then no ξ
derivable from `◯⊥` derives M — adjoin the fallible top: the refuting
world keeps refuting M but now forces `◯⊥`, hence ξ. -/
theorem no_lower_bound_above_boxBot {M : PLLFormula}
    (hM : boxFree M = true) {D : ConstraintModel} {d : D.W}
    (hd : ¬ D.force d M) {ξ : PLLFormula}
    (hlow : Nonempty (LaxND [ξ] M))
    (hcone : Nonempty (LaxND [PLLFormula.falsePLL.somehow] ξ)) : False := by
  obtain ⟨dlow⟩ := hlow
  obtain ⟨dcone⟩ := hcone
  have hξ : (topExt D).force (.inl d) ξ :=
    soundness dcone (topExt D) (.inl d) (fun χ hχ => by
      simp only [List.mem_singleton] at hχ
      exact hχ ▸ topExt_boxBot D _)
  have hMf : (topExt D).force (.inl d) M :=
    soundness dlow (topExt D) (.inl d) (fun χ hχ => by
      simp only [List.mem_singleton] at hχ
      exact hχ ▸ hξ)
  exact hd ((topExt_force_iff D hM d).mp hMf)

/-- With no fallible worlds, `¬◯⊥` holds everywhere. -/
theorem flat_neg_boxBot {C : ConstraintModel} (hF : C.F = ∅) (w : C.W) :
    C.force w (PLLFormula.falsePLL.somehow.ifThen .falsePLL) := by
  intro v hv hbox
  obtain ⟨u, -, hu⟩ := hbox v (C.refl_i v)
  have hu' : u ∈ C.F := hu
  rw [hF] at hu'
  exact absurd hu' (fun h => h)

/-- **No formula refuted over a fallibility-free model has a lower
bound in the ¬◯⊥-cone** (any IPC countermodel, read as a PLL model
with `F = ∅`, qualifies — here even ◯-freeness is not needed). -/
theorem no_lower_bound_above_negBoxBot {M : PLLFormula}
    {D : ConstraintModel} (hDF : D.F = ∅) {d : D.W}
    (hd : ¬ D.force d M) {ξ : PLLFormula}
    (hlow : Nonempty (LaxND [ξ] M))
    (hcone : Nonempty (LaxND
      [PLLFormula.falsePLL.somehow.ifThen .falsePLL] ξ)) : False := by
  obtain ⟨dlow⟩ := hlow
  obtain ⟨dcone⟩ := hcone
  have hξ : D.force d ξ :=
    soundness dcone D d (fun χ hχ => by
      simp only [List.mem_singleton] at hχ
      exact hχ ▸ flat_neg_boxBot hDF d)
  exact hd (soundness dlow D d (fun χ hχ => by
    simp only [List.mem_singleton] at hχ
    exact hχ ▸ hξ))

/-! ## The value corollaries (∀-side) -/

/-- The ∀p-value of a ◯-free M refuted somewhere never lies in the
◯⊥-cone. -/
theorem semAll_value_not_above_boxBot {p : String} {M ψ : PLLFormula}
    (hM : boxFree M = true) (h : IsSemAll p M ψ)
    {D : ConstraintModel} {d : D.W} (hd : ¬ D.force d M) :
    ¬ Nonempty (LaxND [PLLFormula.falsePLL.somehow] ψ) :=
  fun hcone => no_lower_bound_above_boxBot hM hd (semAll_lower h) hcone

/-- The ∀p-value of an M refuted over a fallibility-free model never
lies in the ¬◯⊥-cone. -/
theorem semAll_value_not_above_negBoxBot {p : String} {M ψ : PLLFormula}
    (h : IsSemAll p M ψ) {D : ConstraintModel} (hDF : D.F = ∅)
    {d : D.W} (hd : ¬ D.force d M) :
    ¬ Nonempty (LaxND [PLLFormula.falsePLL.somehow.ifThen .falsePLL] ψ) :=
  fun hcone => no_lower_bound_above_negBoxBot hDF hd (semAll_lower h) hcone

/-- If `⊢ M` then any ∀p-value of M is derivable — the value is ⊤, in
PLL as in IPC. -/
theorem semAll_value_of_derivable {p : String} {M ψ : PLLFormula}
    (h : IsSemAll p M ψ) (hM : Nonempty (LaxND [] M)) :
    Nonempty (LaxND [] ψ) := by
  obtain ⟨d⟩ := hM
  refine completeness ?_
  intro C w _
  refine (h.2 C w).mpr ?_
  intro v hv N B v' hZ
  exact soundness d N v' (fun χ hχ => absurd hχ List.not_mem_nil)

/-- **Agreement with IPC on ◯-free rows, modulo cone coverage**: an
underivable ◯-free M (refuted at a general world and at a
fallibility-free world) has its ∀p-value excluded from both cones; so
a value lying in either cone — or `≡ ⊥` — is `⊥`, Pitts's value.  The
coverage of RN(◯,{}) ∖ {⊥} by the two cones (every nonzero closed
formula derivable from `◯⊥` or from `¬◯⊥`) is the remaining OPEN step
to the unconditional collapse; it holds for every rung tested. -/
theorem semAll_value_bot_of_cones {p : String} {M ψ : PLLFormula}
    (hM : boxFree M = true) (h : IsSemAll p M ψ)
    {D₁ : ConstraintModel} {d₁ : D₁.W} (hd₁ : ¬ D₁.force d₁ M)
    {D₂ : ConstraintModel} (hDF : D₂.F = ∅) {d₂ : D₂.W}
    (hd₂ : ¬ D₂.force d₂ M)
    (hcov : Nonempty (LaxND [PLLFormula.falsePLL.somehow] ψ) ∨
      Nonempty (LaxND [PLLFormula.falsePLL.somehow.ifThen .falsePLL] ψ) ∨
      Nonempty (LaxND [ψ] .falsePLL)) :
    Nonempty (LaxND [ψ] .falsePLL) := by
  rcases hcov with h1 | h2 | h3
  · exact absurd h1 (semAll_value_not_above_boxBot hM h hd₁)
  · exact absurd h2 (semAll_value_not_above_negBoxBot h hDF hd₂)
  · exact h3

/-! ## The dual exclusions (∃-side) -/

/-- The ∃p-value of a ◯-free M forced at a non-fallible world never
derives `¬◯⊥`: the fallible top gives an M-world forcing `◯⊥`
non-fallibly. -/
theorem semEx_value_not_derives_negBoxBot {p : String} {M ψ : PLLFormula}
    (hM : boxFree M = true) (h : IsSemEx p M ψ)
    {D : ConstraintModel} {d : D.W} (hdF : d ∉ D.F) (hd : D.force d M) :
    ¬ Nonempty (LaxND [ψ]
      (PLLFormula.falsePLL.somehow.ifThen .falsePLL)) := by
  rintro ⟨e⟩
  obtain ⟨u⟩ := semEx_upper h
  have hψ : (topExt D).force (.inl d) ψ :=
    soundness u (topExt D) (.inl d) (fun χ hχ => by
      simp only [List.mem_singleton] at hχ
      exact hχ ▸ (topExt_force_iff D hM d).mpr hd)
  have hneg := soundness e (topExt D) (.inl d) (fun χ hχ => by
    simp only [List.mem_singleton] at hχ
    exact hχ ▸ hψ)
  exact hdF (hneg (.inl d) ((topExt D).refl_i _) (topExt_boxBot D _))

/-- The ∃p-value of an M forced over a fallibility-free model never
derives `◯⊥`. -/
theorem semEx_value_not_derives_boxBot {p : String} {M ψ : PLLFormula}
    (h : IsSemEx p M ψ) {D : ConstraintModel} (hDF : D.F = ∅)
    {d : D.W} (hd : D.force d M) :
    ¬ Nonempty (LaxND [ψ] PLLFormula.falsePLL.somehow) := by
  rintro ⟨e⟩
  obtain ⟨u⟩ := semEx_upper h
  have hψ : D.force d ψ := soundness u D d (fun χ hχ => by
    simp only [List.mem_singleton] at hχ
    exact hχ ▸ hd)
  have hbox := soundness e D d (fun χ hχ => by
    simp only [List.mem_singleton] at hχ
    exact hχ ▸ hψ)
  obtain ⟨y, -, hy⟩ := hbox d (D.refl_i d)
  have hy' : y ∈ D.F := hy
  rw [hDF] at hy'
  exact absurd hy' (fun h => h)

/-! ## Axiom audit (pinned) -/

/--
info: 'PLLND.SemUI.semAll_value_bot_of_cones' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms semAll_value_bot_of_cones

end SemUI
end PLLND
