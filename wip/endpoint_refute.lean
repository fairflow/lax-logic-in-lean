/-
# The endpoint class is NOT complete for PLL

`completeness_of_endpoints` (`FRJ/Saturate.lean`) proves: an
ENDPOINT-SEEING countermodel yields an FRJ derivation, where

    K.Endpoints := ∀ a, ∃ m, K.Rm a m ∧ (∀ u, K.le m u → u = m)

("every modal cone contains a `≤`-maximal world").  It is the strongest
unconditional completeness result of the whole FRJ(◯) campaign, and
`completenessV_of_endpoints` is literally it, transported.  The obvious
way to finish the campaign would be to show every PLL non-theorem has an
endpoint-seeing countermodel.  **That route is dead**, and this file
kills it.

The semantic content of the frame condition is a COLLAPSE.  At a
`≤`-maximal world `m`, `Rm ⊆ ≤` forces the modal cone to be `{m}`, so

    m ⊩ ◯A   ⟺   m ⊩ A          (◯ is the identity at an endpoint)

and therefore `m ⊩ ◯A ⊃ A` — the co-unit, which PLL does not prove,
holds at every endpoint.  `Endpoints` says every modal cone reaches such
a world, which is exactly what it takes to make `◯(◯p ⊃ p)` valid.

    endpoints_valid_circ_counit : K.Endpoints → K.valid (◯(◯p ⊃ p))
    not_PLL_circ_counit         : ¬ PLL (◯(◯p ⊃ p))

The countermodel `K3m` for the second is the 3-chain `0 < 1 < 2` with
`Rm = refl ∪ {(1,2)}` and `p` at `2`: at `1` the cone reaches `2`, so
`1 ⊩ ◯p` while `1 ⊮ p`, hence `1 ⊮ ◯p ⊃ p`; and the cone of `0` is
`{0}`, which therefore supplies no witness for `◯(◯p ⊃ p)` at the root.
`K3m` is infallible, so the refutation is against the paper's validity
too.

Consequence: no choice of countermodel, and no model transformation,
can upgrade `completeness_of_endpoints` to unconditional completeness —
the class of endpoint-seeing models is not complete for PLL.  (`K3m` is
also, unsurprisingly, the frame whose FILTRATION fails to be
endpoint-seeing: filtration `Rm` demands the `F_m` component GROW, while
`F_m` shrinks upwards, so the root's image is `Rm`-isolated.)
-/
import FRJ.Saturate

namespace FRJ.EndpointRefute

open Form

/-! ## Every endpoint-seeing model validates `◯(◯p ⊃ p)` -/

/-- At a `≤`-maximal world the modal cone is a singleton, so `◯` is the
identity there and the co-unit holds. -/
theorem force_counit_of_max {K : Kripke} {m : K.W} {x : String}
    (hmax : ∀ u, K.le m u → u = m) :
    K.force m (.imp (.circ (.atom x)) (.atom x)) := by
  intro d hmd hOp
  obtain ⟨c, hrc, hc⟩ := hOp d (K.le_refl d)
  have hdm : d = m := hmax d hmd
  have hcm : c = m := hmax c (K.le_trans hmd (K.sub_mi hrc))
  exact (hcm.trans hdm.symm) ▸ hc

/-- **`◯(◯p ⊃ p)` is valid on every endpoint-seeing model.**  Each world
`b` hands the `◯`-clause the endpoint of its own modal cone. -/
theorem endpoints_valid_circ_counit {K : Kripke} (hep : K.Endpoints)
    (x : String) :
    K.valid (.circ (.imp (.circ (.atom x)) (.atom x))) := by
  intro b _
  exact ⟨(hep b).m, (hep b).rm, force_counit_of_max (hep b).max⟩

/-! ## But it is not PLL-valid: the 3-chain `K3m` -/

/-! ### The frame, on a bare 3-element type

`Fin 3` would drag mathlib's order instances (and with them
`Classical.choice`) into the model.  A hand type with a `Nat` index
keeps every obligation decidable and the whole file choice-free. -/

inductive W3 where | e0 | e1 | e2
  deriving DecidableEq

def idx : W3 → Nat | .e0 => 0 | .e1 => 1 | .e2 => 2

def le3 (a b : W3) : Prop := idx a ≤ idx b
def rm3 (a b : W3) : Prop := a = b ∨ (a = .e1 ∧ b = .e2)
def v3 (w : W3) (s : String) : Prop := w = .e2 ∧ s = "p"

instance decLe3 (a b : W3) : Decidable (le3 a b) := Nat.decLe _ _
instance decRm3 (a b : W3) : Decidable (rm3 a b) :=
  inferInstanceAs (Decidable (a = b ∨ (a = .e1 ∧ b = .e2)))
instance decV3 (w : W3) (s : String) : Decidable (v3 w s) :=
  inferInstanceAs (Decidable (w = .e2 ∧ s = "p"))

theorem le3_refl : ∀ a, le3 a a := fun a => by cases a <;> decide
theorem le3_trans : ∀ a b c, le3 a b → le3 b c → le3 a c := by
  intro a b c; cases a <;> cases b <;> cases c <;> decide
theorem le3_antisymm : ∀ a b, le3 a b → le3 b a → a = b := by
  intro a b; cases a <;> cases b <;> decide
theorem le3_root : ∀ a, le3 .e0 a := fun a => by cases a <;> decide
theorem v3_mono : ∀ a b, le3 a b → ∀ s, v3 a s → v3 b s := by
  intro a b hab s hv
  obtain ⟨ha, hs⟩ := hv
  subst ha
  refine ⟨?_, hs⟩
  cases b <;> first | rfl | exact absurd hab (by decide)
theorem rm3_refl : ∀ a, rm3 a a := fun _ => Or.inl rfl
theorem rm3_trans : ∀ a b c, rm3 a b → rm3 b c → rm3 a c := by
  intro a b c; cases a <;> cases b <;> cases c <;> decide
theorem rm3_sub : ∀ a b, rm3 a b → le3 a b := by
  intro a b; cases a <;> cases b <;> decide

/-- `0 < 1 < 2`, `Rm = refl ∪ {(1,2)}`, `p` at `2`, infallible. -/
def K3m : Kripke where
  W := W3
  elems := [.e0, .e1, .e2]
  complete := fun w => by cases w <;> decide
  decEq := inferInstance
  le := le3
  le_refl := le3_refl
  le_trans := fun {a b c} => le3_trans a b c
  le_antisymm := fun {a b} => le3_antisymm a b
  root := .e0
  root_le := le3_root
  V := v3
  V_mono := fun {a b} hab => v3_mono a b hab
  Rm := rm3
  rm_refl := rm3_refl
  rm_trans := fun {a b c} => rm3_trans a b c
  sub_mi := fun {a b} => rm3_sub a b
  Fal := fun _ => False
  fal_mono := fun _ h => h
  fal_V := fun h => h.elim
  decLe := fun a b => inferInstanceAs (Decidable (le3 a b))
  decV := fun w s => inferInstanceAs (Decidable (v3 w s))
  decRm := fun a b => inferInstanceAs (Decidable (rm3 a b))
  decFal := fun _ => isFalse (fun h => h)

theorem K3m_infallible : K3m.Infallible := fun _ h => h

/-- `2 ⊩ p`. -/
theorem force_two_p : K3m.force .e2 (.atom "p") := ⟨rfl, rfl⟩

/-- `1 ⊮ p`. -/
theorem not_force_one_p : ¬ K3m.force .e1 (.atom "p") := by
  rintro ⟨h, -⟩; exact absurd h (by decide)

/-- `1 ⊩ ◯p`: the two worlds above `1` both reach `2`, which forces `p`. -/
theorem force_one_circ_p : K3m.force .e1 (.circ (.atom "p")) := by
  intro v hv
  refine ⟨.e2, ?_, force_two_p⟩
  cases v
  · exact absurd hv (by decide)
  · exact Or.inr ⟨rfl, rfl⟩
  · exact Or.inl rfl

/-- `1 ⊮ ◯p ⊃ p`: the co-unit fails at `1`. -/
theorem not_force_one_counit :
    ¬ K3m.force .e1 (.imp (.circ (.atom "p")) (.atom "p")) :=
  fun h => not_force_one_p (h .e1 (le3_refl _) force_one_circ_p)

/-- The modal cone of the root is `{0}`. -/
theorem cone_root : ∀ c, K3m.Rm .e0 c → c = .e0 := by
  intro c hc
  cases c
  · rfl
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)

/-- `0 ⊮ ◯p ⊃ p` — the root refutes the co-unit, because `1` does. -/
theorem not_force_root_counit :
    ¬ K3m.force .e0 (.imp (.circ (.atom "p")) (.atom "p")) :=
  fun h => not_force_one_p (h .e1 (by decide) force_one_circ_p)

/-- **The root refutes `◯(◯p ⊃ p)`**: its modal cone is `{0}`, and `0`
itself refutes the co-unit, so the `◯`-clause has no witness. -/
theorem not_valid_circ_counit :
    ¬ K3m.valid (.circ (.imp (.circ (.atom "p")) (.atom "p"))) := by
  intro h
  obtain ⟨c, hrc, hc⟩ := h .e0 (le3_refl _)
  exact not_force_root_counit ((cone_root c hrc) ▸ hc)

theorem not_PLL_circ_counit :
    ¬ PLL (.circ (.imp (.circ (.atom "p")) (.atom "p"))) :=
  not_PLL_of_countermodel not_valid_circ_counit

/-- info: 'FRJ.EndpointRefute.not_PLL_circ_counit' depends on axioms: [propext] -/
#guard_msgs in
#print axioms not_PLL_circ_counit

/-! ## The consequence -/

/-- **The endpoint-seeing class is NOT complete for PLL.**  There is a
PLL non-theorem — `◯(◯p ⊃ p)` — that every endpoint-seeing model
validates, so it has NO endpoint-seeing countermodel and
`completeness_of_endpoints` can never be upgraded to unconditional
completeness by any choice of countermodel. -/
theorem endpoints_not_complete :
    ∃ G : Form, ¬ PLL G ∧ ∀ K : Kripke, K.Endpoints → K.valid G :=
  ⟨.circ (.imp (.circ (.atom "p")) (.atom "p")),
   not_PLL_circ_counit,
   fun _ hep => endpoints_valid_circ_counit hep "p"⟩

/-- info: 'FRJ.EndpointRefute.endpoints_valid_circ_counit' does not depend on any axioms -/
#guard_msgs in
#print axioms endpoints_valid_circ_counit

/-- info: 'FRJ.EndpointRefute.endpoints_not_complete' depends on axioms: [propext] -/
#guard_msgs in
#print axioms endpoints_not_complete

end FRJ.EndpointRefute
