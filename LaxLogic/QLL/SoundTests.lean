/-
# `LaxLogic.QLL.SoundTests` — soundness, instantiated

A theorem about all models and all derivations says nothing until it is pointed
at one.  These cells point it at `𝔅` — one individual, `Bool` for atoms, `P`
witnessed by `true` and not by `false` — and check that the hypothesis is doing
work rather than being vacuously available.
-/
import LaxLogic.QLL.Sound
import LaxLogic.QLL.Judgement

namespace LaxLogic.QLL.SoundTests

open LaxLogic.QLL LaxLogic.QLL.Surface

def 𝔅 : Model where
  D := Unit
  C := Bool
  fn := fun _ _ => ()
  atom := fun _ _ c => c = true
  d₀ := ()
  c₀ := false

def ρ₀ : String → 𝔅.D := fun _ => ()

/-! ## A closed derivation

`⊢ val∀ * : ◯∀ ⊤`, the rule Fig. 5 gives for both modalities.  The constraint
is the singleton on `|⊤| = Unit`, and soundness says it refines `◯∀ ⊤`. -/

def d_val : qd[⊢ val[∀] * : ◯[∀] ⊤] := .circI .topI

theorem val_sound : Refines 𝔅 [] ρ₀ qf[◯[∀] ⊤] (denoteC 𝔅 d_val ρ₀) :=
  soundness 𝔅 d_val trivial .nil ρ₀ .nil

/-! ## `∀I`, where the interpretation crosses a binder

`⟨* | x⟩ : ∀x. ⊤` — the case that needs `Val_openWith` and the opening lemma. -/

def d_gen : qd[⊢ ⟨* | x⟩ : ∀ a, ⊤] :=
  .allI "x" ⟨by decide, by decide, by decide⟩ .topI

theorem gen_sound : Refines 𝔅 [] ρ₀ qf[∀ a, ⊤] (denoteC 𝔅 d_gen ρ₀) :=
  soundness 𝔅 d_gen trivial .nil ρ₀ .nil

/-! ## Where the hypothesis bites

`u : P ⊢ val∃ u : ◯∃ P`.  The conclusion is only true of an environment that
gives `u` a witness of `P`, and in `𝔅` that means `true`. -/

def d_ex : qd[u : P ⊢ val[∃] u : ◯[∃] P] := .circI (.var (by decide))

/-- The good environment: `u` is given `true`, which does witness `P`. -/
def η_ok : PEnv 𝔅 qc[u : P] := .cons true .nil

theorem η_ok_sat : CtxRefines 𝔅 ρ₀ qc[u : P] η_ok := .cons rfl .nil

theorem ex_sound : Refines 𝔅 [] ρ₀ qf[◯[∃] P] (denote 𝔅 d_ex η_ok ρ₀) :=
  soundness 𝔅 d_ex trivial η_ok ρ₀ η_ok_sat

/-- Unfolded, that is: some witness the constraint admits does refine `P`. -/
example : ∃ c : Bool, (true = c) ∧ c = true := ex_sound

/-- And the bad environment is refused at the hypothesis, not at the
conclusion: `false` does not witness `P`, so it never satisfies the context. -/
theorem η_bad_not_sat : ¬ CtxRefines 𝔅 ρ₀ qc[u : P] (.cons false .nil) := by
  intro h
  cases h with
  | cons hv _ => exact Bool.noConfusion hv

/-! ## Axioms -/

/-- info: 'LaxLogic.QLL.soundness' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms soundness

/-- info: 'LaxLogic.QLL.Refines_openAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Refines_openAt

/-- info: 'LaxLogic.QLL.SoundTests.ex_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ex_sound

end LaxLogic.QLL.SoundTests
