/-
# LJF◯ → Gbu◯: the `↓↑`-freedom invariant and the saturation measure

The `≐`-transport that the translation uses (`transportRC`,
`transportIC`, with `ctxEq_cons` and `clo_ctxEq`) was hoisted to
`FRJ/Gbu/Transport.lean` on 2026-09-02, since it is a property of the
calculus rather than of this route; it is re-exported here by the
import, in namespace `FRJ.Gbu`, so every use below is unqualified as
before.
-/
import wip.gbu_ljfo_support
import FRJ.Gbu.Transport

namespace FRJ.Gbu.LJFT

open FRJ Form

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
