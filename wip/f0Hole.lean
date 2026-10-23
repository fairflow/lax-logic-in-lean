import wip.floor
import wip.f0Structure
import Meta.Audit

/-!
# The copies of ℚ hang from a hole (R4)

Write `f d = Dy.formula d` and `h n = f (1/2^n)` (`half n`).  The chain
`h n` is a meet of `n` fresh odd gaps (`half_step`):

    h 0 = ⊤,     h (n+1)  ⊣⊢  h n ∧ g(2·x(n+1, 1) + 1),     x(n+1, 1) = 2^(n+1) + 1,

so `h n ⊣⊢ g 7 ∧ g 11 ∧ g 19 ∧ … ∧ g(2^(n+2) + 3)`.  Since `h 1 ⊣⊢ g 7` and
`t16 ⊬ g 7`, the bound of `ladder_le_formula` (`t n ⊢ f d` for `n ≤ 15`) is
sharp (`t16_not_le_half`).  It descends strictly
(`dyadic_embedding`) and is bounded below by `t15` (`ladder_le_formula`) and
by every `Wit b` (`Wit_below_halves`), but it has NO greatest lower bound
(`halves_no_glb`):

    ¬ ∃ χ,  (∀ n, χ ⊢ h n)  ∧  ∀ ψ, (∀ n, ψ ⊢ h n) → ψ ⊢ χ,

and likewise inside F0 (`halves_no_glb_vf`, all formulas variable-free).

The proof adapts `wip/floor.lean`.  `L_bounded` needs `χ ⊢ g k` for every
`k ≥ 1`; here `χ` reaches only the gaps of the chain, so `L_bounded_cofinal`
takes the cofinal hypothesis `∀ N, ∃ k ≥ N + 1, χ ⊢ g k` and runs the same
argument on the edged lift `cmE (k − 1)`, whose edge world refutes `g k`
(`gap_fails`).  A glb would sit above every `Wit b`, so it would be forced on
the plain ladder at every world `b + 3` (`Wit_force_high`), an unbounded
trace, against `L_bounded_cofinal`.

**Pin.**  `[propext, Classical.choice, Quot.sound]`.  The choice is the
excluded middle in `plain_trace_dichotomy` (a plain-ladder truth set is all of
ℕ or bounded), used by `edge_stability` and by `L_bounded_cofinal`;
`Wit_below_all_gaps` and `Wit_force_high` carry choice as pinned in
`wip/floor.lean`.  A choice-free proof would have to compute the trace bound
of a formula on the plain ladder; that is not attempted here.
-/

open PLLFormula

namespace PLLND
namespace F0

open SemUI RNEmbed PLLND.SemUI.RND
open PLLND.LaxInfinite (atomFree)

/-- The dyadic `1/2^n`. -/
def half (n : Nat) : Dy := ⟨1, n, Nat.two_pow_pos n⟩

theorem half_poly (n : Nat) :
    F (n + 1) 1 = (LPoly.bot).or ((F n 1).and (.var (idx (n + 1) 1))) := by
  have e : F (n + 1) (2 * 0 + 1) =
      (F n 0).or ((F n (0 + 1)).and (.var (idx (n + 1) (2 * 0 + 1)))) := F_odd n 0
  rw [F_zero] at e
  exact e

/-- **The chain is a meet of fresh odd gaps**:
`h (n+1) ⊣⊢ h n ∧ g(2·x(n+1,1)+1)`. -/
theorem half_step (n : Nat) :
    Interd (half (n + 1)).formula
      ((half n).formula.and (gap (2 * idx (n + 1) 1 + 1))) := by
  show Interd (F (n + 1) 1).den _
  rw [half_poly]
  refine ⟨?_, Deriv.orIntro2 (Deriv.iden (.head _))⟩
  exact Deriv.orElim (Deriv.iden (.head _))
    (Deriv.falsoElim _ (Deriv.iden (.head _)))
    (Deriv.iden (.head _))

/-- `h 0 = ⊤`. -/
theorem half_zero : (half 0).formula = .ifThen .falsePLL .falsePLL := rfl

theorem half_gap (n : Nat) : Deriv [(half (n + 1)).formula] (gap (2 * idx (n + 1) 1 + 1)) :=
  Deriv.andElim2 (half_step n).1

/-- **The bound 15 of `ladder_le_formula` is sharp**: `t16 ⊬ f(1/2)`, since
`f(1/2) ⊢ g 7` and `t16 ⊬ g 7` (`even_not_le_gap`, `wip/connect.lean`). -/
theorem t16_not_le_half : [rnSub 16] ⊬ (half 1).formula := fun h =>
  even_not_le_gap (k := 7) (by decide) (Deriv.cutHead h (half_gap 0))

theorem lt_two_pow' : ∀ n : Nat, n < 2 ^ n
  | 0 => Nat.zero_lt_one
  | n + 1 => by
      have ih := lt_two_pow' n
      have hpow := two_pow_succ n
      omega

/-- A lower bound of the chain reaches cofinally many gaps. -/
theorem half_lower_gap {χ : PLLFormula} (h : ∀ n, Deriv [χ] (half n).formula) :
    ∀ N : Nat, ∃ k : Nat, N + 1 ≤ k ∧ Deriv [χ] (gap k) := fun N => by
  refine ⟨2 * idx (N + 1) 1 + 1, ?_, Deriv.cutHead (h (N + 1)) (half_gap N)⟩
  have h1 := lt_two_pow' (N + 1)
  unfold idx
  omega

/-- **`L_bounded` from a cofinal set of gaps.**  If `χ ⊢ g k` for cofinally
many `k`, the plain-ladder trace of `χ` is bounded. -/
theorem L_bounded_cofinal {χ : PLLFormula}
    (h : ∀ N : Nat, ∃ k : Nat, N + 1 ≤ k ∧ Deriv [χ] (gap k)) :
    ∃ B : Nat, ∀ n : Nat, B ≤ n → ¬ ladder.cm.force (some n) χ := by
  rcases plain_trace_dichotomy χ with hall | hb
  · exfalso
    obtain ⟨M, hM⟩ := edge_stability χ
    obtain ⟨k, hk, ⟨d⟩⟩ := h M
    have hforce : (cmE (k - 1)).force (some (k - 1 + 3)) χ :=
      (hM (k - 1) (by omega)).mpr (hall (k - 1 + 3))
    have hs := soundness d (cmE (k - 1)) (some (k - 1 + 3)) (fun ψ hψ => by
      have e : ψ = χ := by
        cases hψ with
        | head => rfl
        | tail _ h' => cases h'
      subst e
      exact hforce)
    exact gap_fails (k - 1) k (by omega) (by omega) hs
  · exact hb

/-- Every `Wit b` lies under the whole chain. -/
theorem Wit_below_halves (b n : Nat) : Deriv [Wit b] (half n).formula :=
  true_entails_ctx (fun _ => true) (Wit b) (F n 1)
    (fun i _ _ => Wit_below_all_gaps b (k := 2 * i + 1) (by omega))
    (F_eval_true n 1 (Nat.succ_pos 0))

/-- **R4.  The chain `f (1/2^n)` has no greatest lower bound.** -/
theorem halves_no_glb :
    ¬ ∃ χ : PLLFormula, (∀ n, Deriv [χ] (half n).formula) ∧
      ∀ ψ : PLLFormula, (∀ n, Deriv [ψ] (half n).formula) → Deriv [ψ] χ := by
  rintro ⟨χ, hlow, hglb⟩
  obtain ⟨B, hB⟩ := L_bounded_cofinal (half_lower_gap hlow)
  obtain ⟨d⟩ := hglb (Wit B) (Wit_below_halves B)
  have hs := soundness d ladder.cm (some (B + 3)) (fun ψ hψ => by
    have e : ψ = Wit B := by
      cases hψ with
      | head => rfl
      | tail _ h' => cases h'
    subst e
    exact Wit_force_high B)
  exact hB (B + 3) (by omega) hs

/-- **R4 inside F0**: no variable-free greatest lower bound among the
variable-free lower bounds. -/
theorem halves_no_glb_vf :
    ¬ ∃ χ : PLLFormula, atomFree χ = true ∧ (∀ n, Deriv [χ] (half n).formula) ∧
      ∀ ψ : PLLFormula, atomFree ψ = true →
        (∀ n, Deriv [ψ] (half n).formula) → Deriv [ψ] χ := by
  rintro ⟨χ, -, hlow, hglb⟩
  obtain ⟨B, hB⟩ := L_bounded_cofinal (half_lower_gap hlow)
  obtain ⟨d⟩ := hglb (Wit B) (Wit_atomFree B) (Wit_below_halves B)
  have hs := soundness d ladder.cm (some (B + 3)) (fun ψ hψ => by
    have e : ψ = Wit B := by
      cases hψ with
      | head => rfl
      | tail _ h' => cases h'
    subst e
    exact Wit_force_high B)
  exact hB (B + 3) (by omega) hs

end F0
end PLLND

/-! ## Axiom pins -/

#axioms_within PLLND.F0.half_step [propext, Quot.sound]
#axioms_within PLLND.F0.half_lower_gap [propext, Quot.sound]
#axioms_within PLLND.F0.t16_not_le_half [propext, Classical.choice, Quot.sound]
#axioms_within PLLND.F0.L_bounded_cofinal [propext, Classical.choice, Quot.sound]
#axioms_within PLLND.F0.Wit_below_halves [propext, Classical.choice, Quot.sound]
#axioms_within PLLND.F0.halves_no_glb [propext, Classical.choice, Quot.sound]
#axioms_within PLLND.F0.halves_no_glb_vf [propext, Classical.choice, Quot.sound]
