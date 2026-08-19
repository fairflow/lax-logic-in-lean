/-
# Are all the modal relations needed?

The PLL semantics quantifies over models whose modal relation `Rm` is an
ARBITRARY reflexive-transitive subrelation of the intuitionistic order
`Ri`.  Matthew's question (2026-08-18): is that generality necessary, or
would some restricted family of `Rm`-shapes already give completeness?

The question has an exact form.  For a class `𝒞` of models, exhibit a
formula `φ` with

    (a)  ∀ M ∈ 𝒞, M ⊨ φ        (b)  ¬ PLL ⊢ φ

Then **completeness fails for `𝒞`**, so the models outside `𝒞` are
needed.  This file carries such separators, machine-checked, one class at
a time.  Soundness (`PLLND.soundness_valid`) turns (b) into the exhibition
of a single countermodel.
-/
import LaxLogic.PLLKripke
import LaxLogic.PLLNDCore

namespace PLLND
namespace Need

open PLLFormula

/-! ## Notation for the two formulas used below -/

/-- `p`. -/
abbrev p : PLLFormula := .prop "p"

/-! ## Class 1: the TRANSPARENT models, `Rm = id`

Here `◯` is the identity operation, so every instance of `◯φ ⊃ φ` is
valid — and `◯p ⊃ p` is not a PLL theorem. -/

/-- The modal relation is the identity. -/
def Transparent (C : ConstraintModel) : Prop := ∀ w v : C.W, C.Rm w v → v = w

/-- **On a transparent model `◯φ` and `φ` are the same proposition.**  The
forward direction takes the `Ri`-reflexive instance and collapses the
modal successor; the backward direction is heredity. -/
theorem force_somehow_iff_of_transparent {C : ConstraintModel}
    (h : Transparent C) (w : C.W) (φ : PLLFormula) :
    C.force w (.somehow φ) ↔ C.force w φ := by
  constructor
  · intro hc
    obtain ⟨u, hru, hu⟩ := hc w (C.refl_i w)
    exact (h w u hru) ▸ hu
  · intro hf v hiv
    exact ⟨v, C.refl_m v, C.force_hered hiv hf⟩

/-- **(a) for class 1**: `◯p ⊃ p` holds at every world of every
transparent model. -/
theorem transparent_forces_circ_imp {C : ConstraintModel} (h : Transparent C)
    (w : C.W) : C.force w (.ifThen (.somehow p) p) :=
  fun v _ hv => (force_somehow_iff_of_transparent h v p).1 hv

/-! ### The countermodel: two worlds, `Rm = Ri`

`W = Bool` ordered `false ≤ true`, `p` true only at `true`, no fallible
world, and `Rm = Ri`.  At `false` the formula `◯p` holds — every world
above `false` reaches `true`, where `p` holds — while `p` does not. -/

/-- `false ≤ true`. -/
def two : ConstraintModel where
  W := Bool
  Ri := fun x y => x = true → y = true
  Rm := fun x y => x = true → y = true
  F := ∅
  V := fun a w => a = "p" ∧ w = true
  refl_i := fun _ h => h
  trans_i := fun h₁ h₂ h => h₂ (h₁ h)
  refl_m := fun _ h => h
  trans_m := fun h₁ h₂ h => h₂ (h₁ h)
  sub_mi := fun h => h
  hered_F := fun _ h => h.elim
  hered_V := by
    rintro a w v hwv ⟨ha, hw⟩
    exact ⟨ha, hwv hw⟩
  full_F := fun h => h.elim

/-- `two` is not transparent: `false Rm true`. -/
theorem two_not_transparent : ¬ Transparent two :=
  fun h => Bool.noConfusion (h false true (fun hc => Bool.noConfusion hc))

/-- `two` refutes `◯p ⊃ p` at its root. -/
theorem two_refutes : ¬ two.force false (.ifThen (.somehow p) p) := by
  intro h
  have hc : two.force false (.somehow p) := by
    intro v _
    exact ⟨true, fun _ => rfl, ⟨rfl, rfl⟩⟩
  have := h false (fun hc => Bool.noConfusion hc) hc
  exact Bool.noConfusion this.2

/-- **(b) for class 1**: `◯p ⊃ p` is not a PLL theorem. -/
theorem not_provable_circ_imp : [] ⊬ .ifThen (.somehow p) p :=
  fun ⟨d⟩ => two_refutes (soundness_valid d two false)

/-- **The transparent models are not enough.**  `Rm = id` validates a
non-theorem, so completeness fails on that class: the models with a
non-trivial modal relation are NEEDED. -/
theorem transparent_incomplete :
    (∀ C : ConstraintModel, Transparent C → ∀ w : C.W,
        C.force w (.ifThen (.somehow p) p))
      ∧ [] ⊬ .ifThen (.somehow p) p :=
  ⟨fun _ h w => transparent_forces_circ_imp h w, not_provable_circ_imp⟩


/-! ## Classes 2 and 3: `Rm = Ri`, and the ENDPOINT-SEEING models

Both are separated by ONE closed formula,

    ◯¬◯⊥   =   ◯(◯⊥ ⊃ ⊥)

found by a sweep over every model on ≤ 3 worlds (posets, all
reflexive-transitive `Rm ⊆ Ri`, all hereditary `F` and `V`): it is
refuted somewhere in the full class and NOWHERE in either restricted
class.  The two validity proofs below are independent — `Rm = Ri` does
not imply endpoint-seeing for infinite models — and the countermodel is
shared. -/

/-- `◯⊥`. -/
abbrev circBot : PLLFormula := .somehow .falsePLL

/-- `¬◯⊥`. -/
abbrev nCircBot : PLLFormula := .ifThen circBot .falsePLL

/-- The separator `◯¬◯⊥`. -/
abbrev sep : PLLFormula := .somehow nCircBot

/-- The modal relation is the whole order. -/
def RmFull (C : ConstraintModel) : Prop := ∀ w v : C.W, C.Ri w v → C.Rm w v

/-- **(a) for class 2**: `◯¬◯⊥` holds at every world of every model with
`Rm = Ri`, finite or not.  Given `v`, either `v ⊩ ¬◯⊥` and `v` is its own
witness, or some `t ≥ v` forces `◯⊥` while refuting `⊥` — and `t ⊩ ◯⊥`
applied at `t` itself hands over a FALLIBLE world above `t`, which forces
everything, `¬◯⊥` included. -/
theorem rmFull_forces_sep {C : ConstraintModel} (h : RmFull C) (w : C.W) :
    C.force w sep := by
  intro v hwv
  by_cases hv : C.force v nCircBot
  · exact ⟨v, C.refl_m v, hv⟩
  · have : ∃ t, C.Ri v t ∧ C.force t circBot ∧ ¬ C.force t .falsePLL := by
      by_contra hno
      push_neg at hno
      exact hv (fun t hvt ht => hno t hvt ht)
    obtain ⟨t, hvt, hct, -⟩ := this
    obtain ⟨s, hts, hs⟩ := hct t (C.refl_i t)
    exact ⟨s, h v s (C.trans_i hvt (C.sub_mi hts)), C.force_of_fallible hs⟩

/-- Every modal cone contains a maximal world. -/
def EndpointSeeing (C : ConstraintModel) : Prop :=
  ∀ w : C.W, ∃ m : C.W, C.Rm w m ∧ ∀ u, C.Ri m u → u = m

/-- At a maximal world `◯φ ⊃ φ` holds: the modal successor cannot leave
the world. -/
theorem force_circ_imp_of_maximal {C : ConstraintModel} {m : C.W}
    (hmax : ∀ u, C.Ri m u → u = m) (φ : PLLFormula) :
    C.force m (.ifThen (.somehow φ) φ) := by
  intro v hiv hv
  obtain ⟨u, hru, hu⟩ := hv v (C.refl_i v)
  have hvm : v = m := hmax v hiv
  have hum : u = m := hmax u (C.trans_i hiv (C.sub_mi hru))
  rw [hvm]; rw [hum] at hu; exact hu

/-- **(a) for class 3**: on an endpoint-seeing model EVERY instance of
`◯(◯φ ⊃ φ)` holds — take the endpoint in the cone of each `v ≥ w`. -/
theorem endpointSeeing_forces {C : ConstraintModel} (h : EndpointSeeing C)
    (w : C.W) (φ : PLLFormula) :
    C.force w (.somehow (.ifThen (.somehow φ) φ)) := by
  intro v _
  obtain ⟨m, hrm, hmax⟩ := h v
  exact ⟨m, hrm, force_circ_imp_of_maximal hmax φ⟩

/-! ### The shared countermodel: a 3-chain with a fallible top

    a  <  b  <  c        c fallible;  Rm = id ∪ {(b,c)}

`b ⊩ ◯⊥` (it modally sees the fallible `c`) while `b ⊮ ⊥`, so `a ⊮ ¬◯⊥`;
and the modal cone of `a` is `{a}`, so `a ⊮ ◯¬◯⊥`.  The frame is neither
transparent, nor `Rm = Ri`, nor endpoint-seeing — `a` sees no maximal
world. -/

inductive Th where | a | b | c
  deriving DecidableEq

/-- `a ≤ b ≤ c`. -/
def riB : Th → Th → Bool
  | .a, _ => true
  | .b, .a => false
  | .b, _ => true
  | .c, .c => true
  | .c, _ => false

/-- The identity together with `b Rm c`. -/
def rmB : Th → Th → Bool
  | .a, .a => true
  | .b, .b => true
  | .b, .c => true
  | .c, .c => true
  | _, _ => false

/-- Only the top world is fallible. -/
def falB : Th → Bool
  | .c => true
  | _ => false

def three : ConstraintModel where
  W := Th
  Ri := fun x y => riB x y = true
  Rm := fun x y => rmB x y = true
  F := fun w => falB w = true
  V := fun _ w => falB w = true
  refl_i := by intro w; cases w <;> rfl
  trans_i := by intro w v u h₁ h₂; cases w <;> cases v <;> cases u <;> simp_all [riB]
  refl_m := by intro w; cases w <;> rfl
  trans_m := by intro w v u h₁ h₂; cases w <;> cases v <;> cases u <;> simp_all [rmB]
  sub_mi := by intro w v h; cases w <;> cases v <;> simp_all [rmB, riB]
  hered_F := by
    intro w v h₁ h₂
    cases w <;> cases v <;>
      first | rfl | exact Bool.noConfusion h₁ | exact Bool.noConfusion h₂
  hered_V := by
    intro _ w v h₁ h₂
    cases w <;> cases v <;>
      first | rfl | exact Bool.noConfusion h₁ | exact Bool.noConfusion h₂
  full_F := fun h => h

/-- The three restrictions all fail here. -/
theorem three_not_transparent : ¬ Transparent three :=
  fun h => Th.noConfusion (h .b .c rfl)

theorem three_not_rmFull : ¬ RmFull three :=
  fun h => Bool.noConfusion (h .a .b rfl)

theorem three_not_endpointSeeing : ¬ EndpointSeeing three := by
  rintro h
  obtain ⟨m, hrm, hmax⟩ := h .a
  cases m
  · exact Th.noConfusion (hmax .b rfl)
  · exact Bool.noConfusion hrm
  · exact Bool.noConfusion hrm

/-- `b ⊩ ◯⊥`: every world above `b` modally sees the fallible `c`. -/
theorem three_b_circBot : three.force .b circBot := by
  intro x hx
  cases x
  · exact Bool.noConfusion hx
  · exact ⟨.c, rfl, rfl⟩
  · exact ⟨.c, rfl, rfl⟩

/-- **(b)**: the 3-chain refutes `◯¬◯⊥` at its root. -/
theorem three_refutes : ¬ three.force .a sep := by
  intro h
  obtain ⟨u, hru, hu⟩ := h .a rfl
  cases u
  · exact Bool.noConfusion (hu .b rfl three_b_circBot)
  · exact Bool.noConfusion hru
  · exact Bool.noConfusion hru

/-- `◯¬◯⊥` is not a PLL theorem. -/
theorem not_provable_sep : [] ⊬ sep :=
  fun ⟨d⟩ => three_refutes (soundness_valid d three .a)

/-- **The `Rm = Ri` models are not enough.** -/
theorem rmFull_incomplete :
    (∀ C : ConstraintModel, RmFull C → ∀ w : C.W, C.force w sep)
      ∧ [] ⊬ sep :=
  ⟨fun _ h w => rmFull_forces_sep h w, not_provable_sep⟩

/-- **The endpoint-seeing models are not enough** — so the class on which
`FRJ.completeness_of_endpoints` proves FRJ◯ complete is a PROPER
restriction, and the models outside it are needed for PLL. -/
theorem endpointSeeing_incomplete :
    (∀ C : ConstraintModel, EndpointSeeing C → ∀ w : C.W, C.force w sep)
      ∧ [] ⊬ sep :=
  ⟨fun _ h w => endpointSeeing_forces h w .falsePLL, not_provable_sep⟩

end Need
end PLLND

#print axioms PLLND.Need.transparent_incomplete
#print axioms PLLND.Need.rmFull_incomplete
#print axioms PLLND.Need.endpointSeeing_incomplete
