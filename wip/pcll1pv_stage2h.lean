/-
STAGE 2, part (h): the STABLE-REGION structural kit.

`StableCore`'s configuration lives at promise-stable canonical worlds
(the (f)-derivation: if the stuck branch recurs for every choice, all
promises are already honoured).  This file proves the three structural
facts that make the stable region rigid, and the instability
extraction that feeds the promise-seeded route:

1. `val_eq_of_stable_rmC` — at a promise-stable `Δ`, EVERY canonical
   `RmC`-successor is val-equal to `Δ` (◯-adequacy turns the
   anticipation clause into membership in the promise set, which
   stability collapses into `val Δ`).
2. `trace_const_of_stable` — hence the K-side `Rₘ`-cone above any
   `Δ`-tracing world is TRACE-CONSTANT (`traceC_mforth` would
   otherwise manufacture a non-val-`Δ` `RmC`-successor).
3. `exists_broken_promise` — at an UNSTABLE world some promise
   `boxOf χ ∈ val` is unhonoured (`χ ∉ val`); `boxUnit` gives the
   reverse inclusion, so instability is exactly a broken promise.
-/
import wip.pcll1pv_stage2g

namespace PLLND
open FinComp
namespace SemUI

open Classical

variable {p : String} {K M : ConstraintModel}

/-- Promise-stability: the collected promises are already the world. -/
def PromiseStable {cl : Finset PLLFormula} (hadeq : OBoxAdeq cl)
    (Δ : (canonFinC cl).W) : Prop :=
  (obInvW hadeq Δ).1.val = Δ.1.val

/-- At a promise-stable world every `RmC`-successor is val-equal:
its members are `cl`-members (◯-adequate), so anticipated boxes put
them in the promise set, which stability collapses into `val Δ`. -/
theorem val_eq_of_stable_rmC {cl : Finset PLLFormula}
    {hadeq : OBoxAdeq cl} {Δ Δ'' : (canonFinC cl).W}
    (hst : PromiseStable hadeq Δ) (h : (canonFinC cl).Rm Δ Δ'') :
    Δ''.1.val = Δ.1.val := by
  apply Finset.Subset.antisymm
  · intro χ hχ
    have hχcl : χ ∈ cl := Δ''.2.1.2.1.1 hχ
    have hbox : boxOf χ ∈ Δ.1.val := h.2 χ (hadeq _ hχcl) hχ
    have : χ ∈ (obInvW hadeq Δ).1.val :=
      obInvFT_val_iff.mpr ⟨hχcl, hbox⟩
    rwa [hst] at this
  · exact h.1

/-- The K-side `Rₘ`-cone above a `Δ`-tracing world is trace-constant
at promise-stable `Δ`. -/
theorem trace_const_of_stable {cl : Finset PLLFormula}
    {hadeq : OBoxAdeq cl} {Δ : (canonFinC cl).W}
    (hK : MutuallyConfluent K) {k κ : K.W}
    (hst : PromiseStable hadeq Δ)
    (hΔk : (traceT K cl k).val = Δ.1.val) (h : K.Rm k κ) :
    (traceT K cl κ).val = Δ.1.val := by
  have hRm : (canonFinC cl).Rm Δ (traceC hK cl κ) := by
    have hmf := traceC_mforth (cl := cl) hK h
    refine ⟨?_, ?_⟩
    · intro χ hχ
      rw [← hΔk] at hχ
      exact hmf.1 hχ
    · intro χ hbcl hχ
      rw [← hΔk]
      exact hmf.2 χ hbcl hχ
  exact val_eq_of_stable_rmC hst hRm

/-- Instability is exactly a broken promise: some `χ ∈ cl` with
`boxOf χ ∈ val Δ` but `χ ∉ val Δ`. -/
theorem exists_broken_promise {cl : Finset PLLFormula}
    {hadeq : OBoxAdeq cl} {Δ : (canonFinC cl).W}
    (h : ¬ PromiseStable hadeq Δ) :
    ∃ χ ∈ cl, boxOf χ ∈ Δ.1.val ∧ χ ∉ Δ.1.val := by
  have hsup : Δ.1.val ⊆ (obInvW hadeq Δ).1.val := by
    intro χ hχ
    have hχcl : χ ∈ cl := Δ.2.1.2.1.1 hχ
    refine obInvFT_val_iff.mpr ⟨hχcl, ?_⟩
    cases χ with
    | somehow ψ => exact hχ
    | prop a => exact boxUnit (T := ⟨Δ.1, Δ.2.1⟩) (hadeq _ hχcl) hχ
    | falsePLL => exact boxUnit (T := ⟨Δ.1, Δ.2.1⟩) (hadeq _ hχcl) hχ
    | and a b => exact boxUnit (T := ⟨Δ.1, Δ.2.1⟩) (hadeq _ hχcl) hχ
    | or a b => exact boxUnit (T := ⟨Δ.1, Δ.2.1⟩) (hadeq _ hχcl) hχ
    | ifThen a b => exact boxUnit (T := ⟨Δ.1, Δ.2.1⟩) (hadeq _ hχcl) hχ
  have hne : ¬ ((obInvW hadeq Δ).1.val ⊆ Δ.1.val) := by
    intro hsub
    exact h (Finset.Subset.antisymm hsub hsup)
  obtain ⟨χ, hχ, hnχ⟩ := Finset.not_subset.mp hne
  obtain ⟨hχcl, hbox⟩ := obInvFT_val_iff.mp hχ
  exact ⟨χ, hχcl, hbox, hnχ⟩

/-! ## Pins -/

/--
info: 'PLLND.SemUI.val_eq_of_stable_rmC' depends on axioms: [propext, choice, Quot.sound]
-/
#guard_msgs in
#print axioms val_eq_of_stable_rmC

/--
info: 'PLLND.SemUI.trace_const_of_stable' depends on axioms: [propext, choice, Quot.sound]
-/
#guard_msgs in
#print axioms trace_const_of_stable

/--
info: 'PLLND.SemUI.exists_broken_promise' depends on axioms: [propext, choice, Quot.sound]
-/
#guard_msgs in
#print axioms exists_broken_promise

end SemUI
end PLLND
