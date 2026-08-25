import LaxLogic.PLLKripke
import Mathlib.Tactic.DeriveFintype

/-!
# Frame conditions and finite counter-models (F&M Figure 3, Theorem 4.5)

Forcing on a finite model with decidable data is decidable, so the three
counter-models of F&M Figure 3 give *machine-checked underivability* results
by `decide`, via soundness:

* `◯⊥` is satisfiable: `¬◯⊥` is not a theorem of PLL;
* `◯(A ∨ B) ⊃ (◯A ∨ ◯B)` is not a theorem;
* `(◯A ⊃ ◯B) ⊃ ◯(A ⊃ B)` is not a theorem.

We also prove the soundness halves of F&M Theorem 4.5, the frame
correspondences for the first two schemes:

* on models with `F = ∅`, `¬◯⊥` is valid;
* on models whose two frames are *mutually confluent*, `◯` collapses to the
  simple ∃-clause and `◯(M ∨ N) ⊃ (◯M ∨ ◯N)` is valid.
-/

open PLLFormula

namespace PLLND

/-! ### Decidable forcing on finite models -/

/-- Forcing is decidable over a finite model with decidable data. -/
def ConstraintModel.decForce (C : ConstraintModel)
    [Fintype C.W] [DecidableRel C.Ri] [DecidableRel C.Rm]
    [DecidablePred (· ∈ C.F)] [∀ a, DecidablePred (· ∈ C.V a)] :
    ∀ (φ : PLLFormula) (w : C.W), Decidable (C.force w φ)
  | .prop a, w => inferInstanceAs (Decidable (w ∈ C.V a))
  | .falsePLL, w => inferInstanceAs (Decidable (w ∈ C.F))
  | .and φ ψ, w =>
      letI := C.decForce φ w
      letI := C.decForce ψ w
      inferInstanceAs (Decidable (C.force w φ ∧ C.force w ψ))
  | .or φ ψ, w =>
      letI := C.decForce φ w
      letI := C.decForce ψ w
      inferInstanceAs (Decidable (C.force w φ ∨ C.force w ψ))
  | .ifThen φ ψ, w =>
      letI := fun v => C.decForce φ v
      letI := fun v => C.decForce ψ v
      inferInstanceAs (Decidable (∀ v, C.Ri w v → C.force v φ → C.force v ψ))
  | .somehow φ, w =>
      letI := fun v => C.decForce φ v
      inferInstanceAs
        (Decidable (∀ v, C.Ri w v → ∃ u, C.Rm v u ∧ C.force u φ))

/-! ### Counter-model 1: `¬◯⊥` is not a theorem (fallible worlds at work)

Two worlds `false ≤ true` (both frames), world `true` fallible.  The root
forces `◯⊥` but is not itself fallible, so `¬◯⊥` fails at the root. -/

/-- `x ≤ y` on `Bool` as a plain definition. -/
def leB (x y : Bool) : Prop := x = y ∨ y = true

instance : DecidableRel leB := fun x y =>
  inferInstanceAs (Decidable (x = y ∨ y = true))

@[reducible] def modelFallible : ConstraintModel where
  W := Bool
  Ri := leB
  Rm := leB
  F := {x | x = true}
  V _ := {x | x = true}
  refl_i _ := .inl rfl
  trans_i {x y z} h h' :=
    (by decide : ∀ x y z : Bool, leB x y → leB y z → leB x z) x y z h h'
  refl_m _ := .inl rfl
  trans_m {x y z} h h' :=
    (by decide : ∀ x y z : Bool, leB x y → leB y z → leB x z) x y z h h'
  sub_mi h := h
  hered_F {x y} h hw :=
    (by decide : ∀ x y : Bool, leB x y → x = true → y = true) x y h hw
  hered_V {_ x y} h hw :=
    (by decide : ∀ x y : Bool, leB x y → x = true → y = true) x y h hw
  full_F hw := hw

instance (φ : PLLFormula) (w : modelFallible.W) :
    Decidable (modelFallible.force w φ) :=
  modelFallible.decForce φ w

/-- `¬◯⊥` is **not** a theorem of PLL (F&M Figure 3, left model). -/
theorem not_provable_not_somehow_false :
    [] ⊬ notPLL (somehow falsePLL) := by
  rintro ⟨p⟩
  exact absurd (soundness_valid p modelFallible false) (by decide)

/-! ### Counter-model 2: `◯(A ∨ B) ⊃ (◯A ∨ ◯B)` is not a theorem

A root `r` with two maximal points `a ⊨ A` and `b ⊨ B` (both frames equal).
The root forces `◯(A ∨ B)` — every point can reach `a` or `b` — but forces
neither `◯A` (blocked at `b`) nor `◯B` (blocked at `a`). -/

inductive W3 : Type
  | r | a | b
  deriving DecidableEq, Fintype

/-- The flat order: `r` below the two maximal points. -/
def riSplit (x y : W3) : Prop := x = y ∨ x = .r

instance : DecidableRel riSplit := fun x y =>
  inferInstanceAs (Decidable (x = y ∨ x = .r))

/-- Valuation: `A` at `a`, `B` at `b`. -/
def vSplit (s : String) : Set W3 :=
  {x | (s = "A" ∧ x = .a) ∨ (s = "B" ∧ x = .b)}

instance (s : String) : DecidablePred (· ∈ vSplit s) := fun x =>
  inferInstanceAs (Decidable ((s = "A" ∧ x = .a) ∨ (s = "B" ∧ x = .b)))

@[reducible] def modelOrSplit : ConstraintModel where
  W := W3
  Ri := riSplit
  Rm := riSplit
  F := ∅
  V := vSplit
  refl_i _ := .inl rfl
  trans_i {x y z} h h' :=
    (by decide : ∀ x y z : W3, riSplit x y → riSplit y z → riSplit x z) x y z h h'
  refl_m _ := .inl rfl
  trans_m {x y z} h h' :=
    (by decide : ∀ x y z : W3, riSplit x y → riSplit y z → riSplit x z) x y z h h'
  sub_mi h := h
  hered_F _ hw := hw.elim
  hered_V {s x y} h hw := by
    rcases h with rfl | rfl
    · exact hw
    · rcases hw with ⟨_, h'⟩ | ⟨_, h'⟩ <;> cases h'
  full_F hw := hw.elim

instance (φ : PLLFormula) (w : modelOrSplit.W) :
    Decidable (modelOrSplit.force w φ) :=
  modelOrSplit.decForce φ w

/-- `◯(A ∨ B) ⊃ (◯A ∨ ◯B)` is **not** a theorem of PLL
(F&M Figure 3, middle model). -/
theorem not_provable_somehow_or_dist :
    [] ⊬ (somehow ((prop "A").or (prop "B"))).ifThen
        ((somehow (prop "A")).or (somehow (prop "B"))) := by
  rintro ⟨p⟩
  exact absurd (soundness_valid p modelOrSplit .r) (by decide)

/-! ### Counter-model 3: `(◯A ⊃ ◯B) ⊃ ◯(A ⊃ B)` is not a theorem

A chain `r ≤ a ≤ b` with `Rₘ` only reflexive plus `a Rₘ b`; `A` holds at
`a, b` and `B` only at `b`.  Then `◯A ⊃ ◯B` holds at `r` (the worlds forcing
`◯A` are `a, b`, which also force `◯B`), but `◯(A ⊃ B)` fails at `r`: from
`r` only `r` itself is `Rₘ`-reachable, and `r ⊭ A ⊃ B` (witness `a`). -/

/-- The chain order `r ≤ a ≤ b`. -/
def riChain (x y : W3) : Prop := x = y ∨ x = .r ∨ (x = .a ∧ y = .b)

instance : DecidableRel riChain := fun x y =>
  inferInstanceAs (Decidable (x = y ∨ x = .r ∨ (x = .a ∧ y = .b)))

/-- The modal frame: reflexive, plus `a Rₘ b`. -/
def rmChain (x y : W3) : Prop := x = y ∨ (x = .a ∧ y = .b)

instance : DecidableRel rmChain := fun x y =>
  inferInstanceAs (Decidable (x = y ∨ (x = .a ∧ y = .b)))

/-- Valuation: `A` off the root, `B` only at the top. -/
def vChain (s : String) : Set W3 :=
  {x | (s = "A" ∧ x ≠ .r) ∨ (s = "B" ∧ x = .b)}

instance (s : String) : DecidablePred (· ∈ vChain s) := fun x =>
  inferInstanceAs (Decidable ((s = "A" ∧ x ≠ .r) ∨ (s = "B" ∧ x = .b)))

@[reducible] def modelNoImpDist : ConstraintModel where
  W := W3
  Ri := riChain
  Rm := rmChain
  F := ∅
  V := vChain
  refl_i _ := .inl rfl
  trans_i {x y z} h h' :=
    (by decide : ∀ x y z : W3, riChain x y → riChain y z → riChain x z) x y z h h'
  refl_m _ := .inl rfl
  trans_m {x y z} h h' :=
    (by decide : ∀ x y z : W3, rmChain x y → rmChain y z → rmChain x z) x y z h h'
  sub_mi {x y} h :=
    (by decide : ∀ x y : W3, rmChain x y → riChain x y) x y h
  hered_F _ hw := hw.elim
  hered_V {s x y} h hw := by
    rcases hw with ⟨rfl, hne⟩ | ⟨rfl, rfl⟩
    · refine .inl ⟨rfl, ?_⟩
      revert hne
      exact (by decide : ∀ x y : W3, riChain x y → x ≠ .r → y ≠ .r) x y h
    · refine .inr ⟨rfl, ?_⟩
      exact (by decide : ∀ y : W3, riChain .b y → y = .b) y h
  full_F hw := hw.elim

instance (φ : PLLFormula) (w : modelNoImpDist.W) :
    Decidable (modelNoImpDist.force w φ) :=
  modelNoImpDist.decForce φ w

/-- `(◯A ⊃ ◯B) ⊃ ◯(A ⊃ B)` is **not** a theorem of PLL
(F&M Figure 3, right model). -/
theorem not_provable_imp_somehow_dist :
    [] ⊬ ((somehow (prop "A")).ifThen (somehow (prop "B"))).ifThen
        (somehow ((prop "A").ifThen (prop "B"))) := by
  rintro ⟨p⟩
  exact absurd (soundness_valid p modelNoImpDist .r) (by decide)

/-! ### Frame correspondences (soundness halves of F&M Theorem 4.5) -/

/-- On models without fallible worlds, `¬◯⊥` is valid. -/
theorem force_not_somehow_false_of_F_empty (C : ConstraintModel)
    (hF : C.F = ∅) (w : C.W) :
    C.force w (notPLL (somehow falsePLL)) := by
  intro v _ hf
  obtain ⟨u, _, hu⟩ := hf v (C.refl_i v)
  rw [show C.force u falsePLL = (u ∈ C.F) from rfl, hF] at hu
  exact hu.elim

/-- Mutual confluence of the two frames (F&M Theorem 4.5). -/
def MutuallyConfluent (C : ConstraintModel) : Prop :=
  ∀ {x w v : C.W}, C.Rm x w → C.Ri x v → ∃ u, C.Ri w u ∧ C.Rm v u

/-- On mutually confluent models the ∀∃ clause for `◯` collapses to the
simple possibility clause. -/
theorem force_somehow_iff_of_confluent {C : ConstraintModel}
    (hc : MutuallyConfluent C) {w : C.W} {φ : PLLFormula} :
    C.force w (somehow φ) ↔ ∃ u, C.Rm w u ∧ C.force u φ := by
  constructor
  · intro h
    exact h w (C.refl_i w)
  · rintro ⟨u, hwu, hu⟩ v hwv
    obtain ⟨t, hut, hvt⟩ := hc hwu hwv
    exact ⟨t, hvt, C.force_hered hut hu⟩

/-- On mutually confluent models, `◯(M ∨ N) ⊃ (◯M ∨ ◯N)` is valid. -/
theorem force_somehow_or_dist_of_confluent {C : ConstraintModel}
    (hc : MutuallyConfluent C) (w : C.W) (M N : PLLFormula) :
    C.force w ((somehow (M.or N)).ifThen ((somehow M).or (somehow N))) := by
  intro v _ hf
  rw [force_somehow_iff_of_confluent hc] at hf
  obtain ⟨u, hvu, hu⟩ := hf
  rcases hu with h | h
  · exact Or.inl ((force_somehow_iff_of_confluent hc).mpr ⟨u, hvu, h⟩)
  · exact Or.inr ((force_somehow_iff_of_confluent hc).mpr ⟨u, hvu, h⟩)

end PLLND
