import LaxLogic.PLLSemUIHenkin

/-!
# `WitTripleC` — the recalibrated witnessing triple (PCLL, bare possibility)

Branch `ui-confluence`.  The general `WitTriple` (`PLLSemUIHenkin.lean`)
carries layered links at `2·d` and `2·d+1` because `crank` charges ◯ = 2.
`crankC` charges ◯ = 1 (`wip/crankC.lean`, `force_iff_of_layeredC`), so
the recalibrated triple `WitTripleC` carries links at `d` and `d+1`, and
the amalgamation entry budget drops from `2·cl.card+1` to `cl.card+1`.

This file: the recalibrated structure, the amalgam over it, and the
assembly `amalgamation_assembledC` (PROVED modulo the two claims, exactly
as in the general case).  The two claims `wit_pbisimC`/`wit_forceC` are
`sorry` — and, unlike the recalibration, they are NOT a port: they need a
CONFLUENT finite canonical model (obInv-based, no `mfal`; the finite
analogue of `PLLConfluentComplete.canonU`), whose construction is the
interactive target.  See the closing note.
-/

open PLLFormula

namespace PLLND
namespace SemUI

open FinComp

variable {p : String} {K M : ConstraintModel}

/-- **Recalibrated witnessing triple.**  As `WitTriple`, but the layered
links sit at `canonDepth` and `canonDepth + 1` (not `2·canonDepth`),
reflecting `crankC`'s one-level ◯-move. -/
structure WitTripleC (cl : Finset PLLFormula)
    (B : LayeredBisimE (fun a => a ≠ p) K M)
    (Δ : (canonFin cl).W) (m : M.W) where
  k' : K.W
  k : K.W
  m' : M.W
  hΔk : (traceT K cl k) = Δ.1
  hΔk' : (traceT K cl k') = Δ.1
  hik : K.Ri k' k
  him : M.Ri m' m
  hZ' : B.Z (canonDepth cl Δ + 1) k' m'
  hZ : B.Z (canonDepth cl Δ) k m

variable (cl : Finset PLLFormula) (B : LayeredBisimE (fun a => a ≠ p) K M)

/-- The amalgam over the recalibrated triple (frame data verbatim from
`witAmalgam`; only the admissibility predicate changes). -/
def witAmalgamC : ConstraintModel where
  W := {q : (canonFin cl).W × M.W // Nonempty (WitTripleC cl B q.1 q.2)}
  Ri := fun a b => (canonFin cl).Ri a.1.1 b.1.1 ∧ M.Ri a.1.2 b.1.2
  Rm := fun a b => (canonFin cl).Rm a.1.1 b.1.1 ∧ M.Rm a.1.2 b.1.2
  F := fun a => a.1.2 ∈ M.F
  V := fun x a =>
    if x = p then a.1.1 ∈ (canonFin cl).V x ∨ a.1.2 ∈ M.F
    else a.1.2 ∈ M.V x
  refl_i := fun a => ⟨(canonFin cl).refl_i _, M.refl_i _⟩
  trans_i := fun h₁ h₂ =>
    ⟨(canonFin cl).trans_i h₁.1 h₂.1, M.trans_i h₁.2 h₂.2⟩
  refl_m := fun a => ⟨(canonFin cl).refl_m _, M.refl_m _⟩
  trans_m := fun h₁ h₂ =>
    ⟨(canonFin cl).trans_m h₁.1 h₂.1, M.trans_m h₁.2 h₂.2⟩
  sub_mi := fun h => ⟨(canonFin cl).sub_mi h.1, M.sub_mi h.2⟩
  hered_F := fun h hF => M.hered_F h.2 hF
  hered_V := by
    intro x a b h hv
    have hv' : (if x = p then a.1.1 ∈ (canonFin cl).V x ∨ a.1.2 ∈ M.F
        else a.1.2 ∈ M.V x) := hv
    show (if x = p then b.1.1 ∈ (canonFin cl).V x ∨ b.1.2 ∈ M.F
        else b.1.2 ∈ M.V x)
    by_cases hx : x = p
    · rw [if_pos hx] at hv' ⊢
      rcases hv' with hΔ | hm
      · exact Or.inl ((canonFin cl).hered_V h.1 hΔ)
      · exact Or.inr (M.hered_F h.2 hm)
    · rw [if_neg hx] at hv' ⊢
      exact M.hered_V h.2 hv'
  full_F := by
    intro x a hF
    show (if x = p then a.1.1 ∈ (canonFin cl).V x ∨ a.1.2 ∈ M.F
        else a.1.2 ∈ M.V x)
    by_cases hx : x = p
    · rw [if_pos hx]
      exact Or.inr hF
    · rw [if_neg hx]
      exact M.full_F hF

/-- **Claim 1 (confluent), OPEN — needs the confluent canonical model.** -/
theorem wit_pbisimC :
    ∃ C : PBisim p M (witAmalgamC cl B),
      ∀ (q : (witAmalgamC cl B).W), C.Z q.1.2 q := by
  sorry

/-- **Claim 2 (confluent truth lemma), OPEN — the ◯-case is definitional
via `obInv` once the canonical side is confluent. -/
theorem wit_forceC (hcl : SubClosed cl) :
    ∀ (q : (witAmalgamC cl B).W) (φ : PLLFormula), φ ∈ cl →
      ((witAmalgamC cl B).force q φ ↔ φ ∈ q.1.1.1.val) := by
  sorry

/-- **The assembly, recalibrated** — PROVED modulo the two claims, with
entry budget `cl.card + 1` (half the general `2·cl.card+1`). -/
theorem amalgamation_assembledC (hcl : SubClosed cl)
    (k₀ : K.W) (m₀ : M.W)
    (hB : B.Z (cl.card + 1) k₀ m₀) :
    ∃ (N : ConstraintModel) (C : PBisim p M N) (n₀ : N.W),
      C.Z m₀ n₀ ∧ ∀ φ ∈ cl, (N.force n₀ φ ↔ K.force k₀ φ) := by
  classical
  set Δ₀ : (canonFin cl).W := trace K cl k₀ with hΔ₀
  have hbudget : canonDepth cl Δ₀ + 1 ≤ cl.card + 1 := by
    have := canonDepth_le cl Δ₀; omega
  have htrip : Nonempty (WitTripleC cl B Δ₀ m₀) := by
    refine ⟨⟨k₀, k₀, m₀, rfl, rfl, K.refl_i _, M.refl_i _, ?_, ?_⟩⟩
    · exact B.mono_le hbudget hB
    · exact B.mono_le (by omega) hB
  obtain ⟨C, hC⟩ := wit_pbisimC cl B
  refine ⟨witAmalgamC cl B, C, ⟨(Δ₀, m₀), htrip⟩,
    hC ⟨(Δ₀, m₀), htrip⟩, ?_⟩
  intro φ hφ
  rw [wit_forceC cl B hcl _ φ hφ]
  constructor
  · intro h
    exact (mem_traceT_val.mp h).2
  · intro h
    exact mem_traceT_val.mpr ⟨hφ, h⟩

end SemUI
end PLLND
