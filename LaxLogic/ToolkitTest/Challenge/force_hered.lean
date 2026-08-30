/- Challenge: `force_hered`.  Group: soundness.
   Replace the `sorry`.  Do not look for the original proof.

   Deliberately not stated here: where this comes from, how long the known
   proof is, or how hard it is.  Those were hints. -/
import LaxLogic.PLLNDCore

/-!
# Kripke constraint models for PLL, and soundness

Following Fairtlough & Mendler, *Propositional Lax Logic*, Information and
Computation 137(1), 1997 — Definitions 3.1 (constraint model), 3.2 (validity)
and Theorem 3.3 (soundness), over the slime-free system `PLLND.LaxND` of
`PLLNDCore.lean`.

A constraint model is `(W, Rₘ, Rᵢ, V, F)`: two preorders with `Rₘ ⊆ Rᵢ`, a
hereditary set `F` of *fallible* worlds at which `⊥` (and hence everything)
holds, and a hereditary valuation that is *full* on `F`.  The lax modality is
interpreted by the ∀∃ clause

  `w ⊨ ◯N  iff  ∀ v. w Rᵢ v → ∃ u. v Rₘ u ∧ u ⊨ N`,

which gives `◯` its mixed possibility/necessity flavour.

Everything here is `Prop`-valued: no casts, no transport.
-/

open PLLFormula

namespace PLLND

/-- Fairtlough–Mendler constraint model (Definition 3.1). -/
structure ConstraintModel where
  W : Type
  /-- intuitionistic accessibility -/
  Ri : W → W → Prop
  /-- modal (constraint) accessibility -/
  Rm : W → W → Prop
  /-- fallible worlds -/
  F : Set W
  /-- valuation on propositional constants -/
  V : String → Set W
  refl_i : ∀ w, Ri w w
  trans_i : ∀ {w v u}, Ri w v → Ri v u → Ri w u
  refl_m : ∀ w, Rm w w
  trans_m : ∀ {w v u}, Rm w v → Rm v u → Rm w u
  /-- the ◯-frame is a subrelation of the ⊃-frame -/
  sub_mi : ∀ {w v}, Rm w v → Ri w v
  hered_F : ∀ {w v}, Ri w v → w ∈ F → v ∈ F
  hered_V : ∀ {a : String} {w v}, Ri w v → w ∈ V a → v ∈ V a
  /-- `V` is full on `F`: fallible worlds validate every atom -/
  full_F : ∀ {a : String} {w}, w ∈ F → w ∈ V a

namespace ConstraintModel

/-- Forcing (Definition 3.2).  `⊥` holds exactly at fallible worlds. -/
def force (C : ConstraintModel) : C.W → PLLFormula → Prop
  | w, .prop a     => w ∈ C.V a
  | w, .falsePLL   => w ∈ C.F
  | w, .and φ ψ    => C.force w φ ∧ C.force w ψ
  | w, .or φ ψ     => C.force w φ ∨ C.force w ψ
  | w, .ifThen φ ψ => ∀ v, C.Ri w v → C.force v φ → C.force v ψ
  | w, .somehow φ  => ∀ v, C.Ri w v → ∃ u, C.Rm v u ∧ C.force u φ

/-- Validity is hereditary along `Rᵢ` (and hence along `Rₘ ⊆ Rᵢ`). -/
theorem force_hered (C : ConstraintModel) {φ : PLLFormula} :
    ∀ {w v : C.W}, C.Ri w v → C.force w φ → C.force v φ := by
  sorry
