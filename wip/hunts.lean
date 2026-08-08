import LaxLogic.PLLUIChains
import LaxLogic.PLLNoFall
import wip.gapWidth
import wip.uiObstruct

/-!
# The two hunts, instantiated: the chains are armed

`LaxLogic/PLLUIChains.lean` proves the two refutation criteria generically.
This file instantiates them with the repository's mechanised chains, so that
each hunt is reduced to exactly its two remaining obligations about a witness
formula `φ`.

* **∀p side**: the ascending chain is `chainF k = ◯t(2k+1)`, strictness
  `chain_lt_strict` (`wip/chainStrict.lean`).
* **∃p side**: the descending chain is `Gmeet n` (the gap partial meets),
  strictness proved HERE (`Gmeet_strict`) from the `cmE` machinery of
  `wip/gapWidth.lean` — a fact the floor campaign never needed to pin.

`P` is instantiated at `NoFall.VarFree` (closed = variable-free), which at one
propositional variable is exactly `p`-freeness.  Closedness of the chain
members is proved via a substitution lemma: `embed = substP pv ◯⊥` produces a
variable-free formula whenever the argument mentions at most `pv`.
-/

open PLLFormula

namespace PLLND
namespace Hunts

open SemUI RNEmbed UIChains NoFall

/-! ## Closedness of the chain members -/

/-- `A` mentions at most the variable `pv`. -/
def OnlyPv : PLLFormula → Prop
  | .prop a     => a = RNEmbed.pv
  | .falsePLL   => True
  | .and φ ψ    => OnlyPv φ ∧ OnlyPv ψ
  | .or φ ψ     => OnlyPv φ ∧ OnlyPv ψ
  | .ifThen φ ψ => OnlyPv φ ∧ OnlyPv ψ
  | .somehow φ  => OnlyPv φ

/-- Substituting `◯⊥` for `pv` in an `OnlyPv` formula is variable-free. -/
theorem varFree_embed : ∀ (A : PLLFormula), OnlyPv A → VarFree (RNEmbed.embed A)
  | .prop a, h => by
      have h' : a = RNEmbed.pv := h
      show VarFree (if a = RNEmbed.pv then RNEmbed.oBot else .prop a)
      rw [if_pos h']
      exact (trivial : VarFree RNEmbed.oBot)
  | .falsePLL, _ => trivial
  | .and φ ψ, h => ⟨varFree_embed φ h.1, varFree_embed ψ h.2⟩
  | .or φ ψ, h => ⟨varFree_embed φ h.1, varFree_embed ψ h.2⟩
  | .ifThen φ ψ, h => ⟨varFree_embed φ h.1, varFree_embed ψ h.2⟩
  | .somehow φ, h => varFree_embed φ h

/-- Both components of every `rnP k` mention at most `pv`. -/
theorem onlyPv_rnP : ∀ k : Nat, OnlyPv (rnP k).1 ∧ OnlyPv (rnP k).2
  | 0 => ⟨rfl, ⟨rfl, trivial⟩⟩
  | k + 1 =>
      let ih := onlyPv_rnP k
      ⟨⟨ih.1, ih.2⟩, ⟨⟨ih.1, ih.2⟩, ih.1⟩⟩

/-- Every rung mentions at most `pv`. -/
theorem onlyPv_rn : ∀ n : Nat, OnlyPv (rn n)
  | 0 => trivial
  | n + 1 => by
      show OnlyPv (if n % 2 = 0 then (rnP (n / 2)).1 else (rnP (n / 2)).2)
      split
      · exact (onlyPv_rnP _).1
      · exact (onlyPv_rnP _).2

/-- The substituted rungs are variable-free. -/
theorem varFree_rnSub (n : Nat) : VarFree (rnSub n) :=
  varFree_embed (rn n) (onlyPv_rn n)

/-- The boxed odd rungs are variable-free. -/
theorem varFree_chainF (k : Nat) : VarFree (chainF k) :=
  varFree_rnSub (2 * k + 1)

/-- The gaps are variable-free. -/
theorem varFree_gap (k : Nat) : VarFree (gap k) :=
  ⟨varFree_chainF k, varFree_rnSub (2 * k + 1)⟩

/-- The gap partial meets are variable-free. -/
theorem varFree_Gmeet : ∀ n : Nat, VarFree (Gmeet n)
  | 0 => varFree_gap 1
  | n + 1 => ⟨varFree_Gmeet n, varFree_gap (n + 2)⟩

/-! ## Strict descent of `Gmeet`

`Gmeet (n+1) = Gmeet n ∧ gap (n+2)`, so strictness is
`Gmeet n ⊬ gap (n+2)`.  Countermodel: the edged lift `cmE (n+1)`, at whose
world `some (n+4)` every gap except `n+2`, `n+3` is forced (`gap_forced`) —
in particular gaps `1..n+1`, hence `Gmeet n` — while `gap (n+2)` fails
(`gap_fails`). -/

/-- `Gmeet n` is forced wherever gaps `1..n+1` are. -/
theorem force_Gmeet_cmE (m : Nat) (x : Nat)
    (h : ∀ k : Nat, 1 ≤ k → k ≤ m → (cmE m).force (some x) (gap k)) :
    ∀ n : Nat, n + 1 ≤ m → (cmE m).force (some x) (Gmeet n)
  | 0, hn => h 1 (by omega) (by omega)
  | n + 1, hn =>
      ⟨force_Gmeet_cmE m x h n (by omega), h (n + 2) (by omega) (by omega)⟩

/-- **Strict descent**: `Gmeet n ⊬ gap (n+2)`, hence
`Gmeet n ⊬ Gmeet (n+1)`. -/
theorem Gmeet_strict (n : Nat) : ¬ Deriv [Gmeet n] (Gmeet (n + 1)) := by
  rintro ⟨d⟩
  -- soundness at cmE (n+1), world n+4
  have hs := soundness d (cmE (n + 1)) (some (n + 4)) (fun ψ hψ => by
    have e : ψ = Gmeet n := by
      cases hψ with
      | head => rfl
      | tail _ h' => cases h'
    subst e
    exact force_Gmeet_cmE (n + 1) (n + 4)
      (fun k hk1 hk2 => gap_forced (n + 1) k (by omega) (by omega) (n + 4))
      n (by omega))
  exact gap_fails (n + 1) (n + 2) (by omega) (by omega) hs.2

/-! ## The armed criteria -/

/-- **The ∃p hunt, armed.**  A witness `φ` now needs exactly two facts:
it lies below every `Gmeet n`, and its variable-free consequences are trapped
above the chain.  Given those, `φ` has NO least variable-free consequence —
no post-interpolant — and uniform interpolation fails at one variable. -/
theorem no_existsP_of_trap (φ : PLLFormula)
    (hbelow : ∀ n, Deriv [φ] (Gmeet n))
    (htrap : ∀ ψ, VarFree ψ → Deriv [φ] ψ → ∃ n, Deriv [Gmeet n] ψ) :
    ¬ ∃ χ, VarFree χ ∧ Deriv [φ] χ ∧
        (∀ ψ, VarFree ψ → Deriv [φ] ψ → Deriv [χ] ψ) :=
  no_least_consequence VarFree Gmeet varFree_Gmeet Gmeet_strict φ hbelow htrap

/-- **The ∀p hunt, armed.**  A witness `φ` now needs exactly two facts:
every `chainF k` entails it, and every variable-free formula entailing it sits
below some `chainF k`.  Given those, `φ` has NO greatest variable-free
antecedent — no pre-interpolant. -/
theorem no_forallP_of_trap (φ : PLLFormula)
    (habove : ∀ k, Deriv [chainF k] φ)
    (htrap : ∀ ψ, VarFree ψ → Deriv [ψ] φ → ∃ k, Deriv [ψ] (chainF k)) :
    ¬ ∃ χ, VarFree χ ∧ Deriv [χ] φ ∧
        (∀ ψ, VarFree ψ → Deriv [ψ] φ → Deriv [ψ] χ) :=
  no_greatest_antecedent VarFree chainF varFree_chainF
    (fun k => chain_step_strict k) φ habove htrap

end Hunts
end PLLND

/-! ### Axiom audit — measured and pinned on creation (2026-08-08). -/

/-- info: 'PLLND.Hunts.Gmeet_strict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.Hunts.Gmeet_strict

/-- info: 'PLLND.Hunts.no_existsP_of_trap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.Hunts.no_existsP_of_trap

/-- info: 'PLLND.Hunts.no_forallP_of_trap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.Hunts.no_forallP_of_trap
