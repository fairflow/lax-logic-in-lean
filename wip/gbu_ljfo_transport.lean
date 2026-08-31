/-
# `≐`-transport for `Gbu◯(G)`

Set-equal contexts derive the same sequents, in both judgments.  This is
the ONLY transport the LJF◯ → Gbu◯ translation uses: `GbuIC` is not
monotone (`gbuIC_not_monotone`, `wip/gbu_ljfo_support.lean`), so
irregular derivations are never moved across context GROWTH — only
across `≐` (same members, different presentation), which preserves
membership, `Clo` (both ways), and `¬ Clo`.
-/
import wip.gbu_ljfo_support

namespace FRJ.Gbu.LJFT

open FRJ Form

/-- Extending both sides of `≐` by the same formula. -/
theorem ctxEq_cons {Ψ Ψ' : List Form} (h : Ψ ≐ Ψ') (X : Form) :
    (X :: Ψ) ≐ (X :: Ψ') := fun y =>
  ⟨fun hy => (List.mem_cons.mp hy).elim (fun e => e ▸ List.mem_cons_self ..)
      (fun hy' => List.mem_cons_of_mem _ ((h y).mp hy')),
    fun hy => (List.mem_cons.mp hy).elim (fun e => e ▸ List.mem_cons_self ..)
      (fun hy' => List.mem_cons_of_mem _ ((h y).mpr hy'))⟩

/-- `Clo` respects `≐`. -/
theorem clo_ctxEq {Ψ Ψ' : List Form} (h : Ψ ≐ Ψ') {X : Form}
    (hc : Clo Ψ X) : Clo Ψ' X :=
  clo_mono h.subset hc

mutual

/-- Transport a regular `Gbu◯` derivation along `≐`. -/
def transportRC {G : Form} : ∀ {Ψ Ψ' : List Form} {C : Form},
    GbuRC G Ψ C → Ψ ≐ Ψ' → GbuRC G Ψ' C
  | _, _, _, .ax A hΓ, h => .ax A (h.symm.trans hΓ)
  | _, _, _, .lbot C hΓ, h => .lbot C (h.symm.trans hΓ)
  | _, _, _, .landL d hΓ, h => .landL d (h.symm.trans hΓ)
  | _, _, _, .randR d₁ d₂, h => .randR (transportRC d₁ h) (transportRC d₂ h)
  | _, _, _, .lorL d₁ d₂ hΓ, h => .lorL d₁ d₂ (h.symm.trans hΓ)
  | _, _, _, .rorR1 d, h => .rorR1 (transportIC d h)
  | _, _, _, .rorR2 d, h => .rorR2 (transportIC d h)
  | _, _, _, .limpL d₁ d₂ hΓ, h => .limpL d₁ d₂ (h.symm.trans hΓ)
  | _, _, _, .rimpI d hA, h => .rimpI (transportRC d h) (clo_ctxEq h hA)
  | _, _, _, .rimpNI d hA, h =>
      .rimpNI (transportRC d (ctxEq_cons h _))
        (fun hc => hA (clo_ctxEq h.symm hc))
  | _, _, _, .lcirc d hprin hΓ, h => .lcirc d hprin (h.symm.trans hΓ)
  | _, _, _, .rcirc d hgoal, h => .rcirc (transportIC d h) hgoal

/-- Transport an irregular `Gbu◯` derivation along `≐`. -/
def transportIC {G : Form} : ∀ {Ψ Ψ' : List Form} {C : Form},
    GbuIC G Ψ C → Ψ ≐ Ψ' → GbuIC G Ψ' C
  | _, _, _, .ax A hΓ, h => .ax A (h.symm.trans hΓ)
  | _, _, _, .randI d₁ d₂, h => .randI (transportIC d₁ h) (transportIC d₂ h)
  | _, _, _, .rorI1 d, h => .rorI1 (transportIC d h)
  | _, _, _, .rorI2 d, h => .rorI2 (transportIC d h)
  | _, _, _, .rimpII d hA, h => .rimpII (transportIC d h) (clo_ctxEq h hA)
  | _, _, _, .rimpNII d hA, h =>
      .rimpNII (transportRC d (ctxEq_cons h _))
        (fun hc => hA (clo_ctxEq h.symm hc))
  | _, _, _, .lcircI d hprin hΓ, h => .lcircI d hprin (h.symm.trans hΓ)
  | _, _, _, .limpLI d₁ d₂ hsz hgoal hΓ, h =>
      .limpLI d₁ d₂ hsz hgoal (h.symm.trans hΓ)
  | _, _, _, .lbotI hgoal hΓ, h => .lbotI hgoal (h.symm.trans hΓ)
  | _, _, _, .landLI d hgoal hΓ, h => .landLI d hgoal (h.symm.trans hΓ)
  | _, _, _, .lorLI d₁ d₂ hgoal hΓ, h => .lorLI d₁ d₂ hgoal (h.symm.trans hΓ)
  | _, _, _, .rcircI d hgoal, h => .rcircI (transportIC d h) hgoal

end

/-! ## The `↓↑`-freedom invariant

`posOfO` never produces `↓↑` (a `down` immediately over an `up`), and
one translation case — right focus, lax flag, on `↓(↑P)` — is exactly
the case with no sound Gbu◯ image (its demand would be an UNWRAPPED
irregular positive from a lax subtree, refuted by `[◯p] ⊬irr p`).  The
invariant excludes it. -/

mutual

/-- No `down (up _)` subterm, positive side. -/
def noDUP : LJFO.Pos → Bool
  | .atom _ => true
  | .fls => true
  | .or P Q => noDUP P && noDUP Q
  | .down (.up _) => false
  | .down N => noDUN N

/-- No `down (up _)` subterm, negative side. -/
def noDUN : LJFO.Neg → Bool
  | .up P => noDUP P
  | .imp Q N => noDUP Q && noDUN N
  | .and M N => noDUN M && noDUN N
  | .circ P => noDUP P

end

mutual

theorem noDUP_posOfO : ∀ φ : PLLFormula, noDUP (LJFO.posOfO φ) = true
  | .prop _ => rfl
  | .falsePLL => rfl
  | .or φ ψ => by
      simp only [LJFO.posOfO, noDUP, Bool.and_eq_true]
      exact ⟨noDUP_posOfO φ, noDUP_posOfO ψ⟩
  | .and φ ψ => by
      simp only [LJFO.posOfO, noDUP, noDUN, Bool.and_eq_true]
      exact ⟨noDUN_negOfO φ, noDUN_negOfO ψ⟩
  | .ifThen φ ψ => by
      simp only [LJFO.posOfO, noDUP, noDUN, Bool.and_eq_true]
      exact ⟨noDUP_posOfO φ, noDUN_negOfO ψ⟩
  | .somehow φ => by
      simp only [LJFO.posOfO, noDUP, noDUN]
      exact noDUP_posOfO φ

theorem noDUN_negOfO : ∀ φ : PLLFormula, noDUN (LJFO.negOfO φ) = true
  | .prop _ => rfl
  | .falsePLL => rfl
  | .or φ ψ => by
      simp only [LJFO.negOfO, noDUN, noDUP, Bool.and_eq_true]
      exact ⟨noDUP_posOfO φ, noDUP_posOfO ψ⟩
  | .and φ ψ => by
      simp only [LJFO.negOfO, noDUN, Bool.and_eq_true]
      exact ⟨noDUN_negOfO φ, noDUN_negOfO ψ⟩
  | .ifThen φ ψ => by
      simp only [LJFO.negOfO, noDUN, Bool.and_eq_true]
      exact ⟨noDUP_posOfO φ, noDUN_negOfO ψ⟩
  | .somehow φ => by
      simp only [LJFO.negOfO, noDUN]
      exact noDUP_posOfO φ

end

/-- `noDUP` on a non-`up` `down` unfolds to the body. -/
@[simp] theorem noDUP_down_imp {Q : LJFO.Pos} {N : LJFO.Neg} :
    noDUP (.down (.imp Q N)) = noDUN (.imp Q N) := rfl
@[simp] theorem noDUP_down_and {M N : LJFO.Neg} :
    noDUP (.down (.and M N)) = noDUN (.and M N) := rfl
@[simp] theorem noDUP_down_circ {P : LJFO.Pos} :
    noDUP (.down (.circ P)) = noDUP P := rfl

/-! ## The counting measure for the saturation retry -/

theorem length_filter_le_of_imp {α} (l : List α) (p q : α → Bool)
    (h : ∀ a, p a = true → q a = true) :
    (l.filter p).length ≤ (l.filter q).length := by
  induction l with
  | nil => exact Nat.le.refl
  | cons a l ih =>
      rw [List.filter_cons, List.filter_cons]
      cases hp : p a with
      | true =>
          rw [h a hp]
          simp only [reduceIte, List.length_cons]
          exact Nat.succ_le_succ ih
      | false =>
          cases hq : q a with
          | true =>
              simp only [reduceIte, List.length_cons]
              exact Nat.le_succ_of_le ih
          | false =>
              rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
              exact ih

theorem length_filter_lt_of_imp {α} (l : List α) (p q : α → Bool)
    (h : ∀ a, p a = true → q a = true) {x : α}
    (hx : x ∈ l) (hpx : p x = false) (hqx : q x = true) :
    (l.filter p).length < (l.filter q).length := by
  induction l with
  | nil => cases hx
  | cons a l ih =>
      rw [List.filter_cons, List.filter_cons]
      rcases List.mem_cons.mp hx with rfl | hx'
      · rw [hpx, hqx]
        simp only [reduceIte, List.length_cons]
        exact Nat.lt_succ_of_le (length_filter_le_of_imp l p q h)
      · cases hp : p a with
        | true =>
            rw [h a hp]
            simp only [reduceIte, List.length_cons]
            exact Nat.succ_lt_succ (ih hx')
        | false =>
            cases hq : q a with
            | true =>
                simp only [reduceIte, List.length_cons]
                exact Nat.lt_succ_of_lt (ih hx')
            | false =>
                rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
                exact ih hx'

/-- The retry measure strictly drops when the context genuinely grew
inside the universe `U`. -/
theorem satMeasure_lt {U Ψ Ψ' : List Form} (hsub : Ψ ⊆ Ψ')
    {x : Form} (hxU : x ∈ U) (hxΨ' : x ∈ Ψ') (hxΨ : x ∉ Ψ) :
    (U.filter (fun y => decide (y ∉ Ψ'))).length <
      (U.filter (fun y => decide (y ∉ Ψ))).length := by
  refine length_filter_lt_of_imp U _ _ (fun a ha => ?_) hxU ?_ ?_
  · exact decide_eq_true (fun hmem => of_decide_eq_true ha (hsub hmem))
  · exact decide_eq_false (fun hn => hn hxΨ')
  · exact decide_eq_true hxΨ

end FRJ.Gbu.LJFT
