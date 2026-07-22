import LaxLogic.PLLSemUIHenkin
import wip.canonFinC

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
open ConfluentU

variable {p : String} {K M : ConstraintModel}

/-! ## The K-side trace is backed (confluent soundness)

The one new mathematical fact needed to re-index the amalgam onto the
confluent `canonFinC`: on a mutually confluent `K`, the trace of a world
is backed by that world's `DerivU`-theory — `SClosed` by `derivU_sound`,
`SPrime` by the `∨`-clause of forcing. -/

/-- The trace `traceT K cl k` is `Backed` when `K` is mutually confluent. -/
theorem trace_backed {K : ConstraintModel} (hK : MutuallyConfluent K)
    {cl : Finset PLLFormula} (k : K.W) : Backed cl (traceT K cl k) := by
  refine ⟨{φ | K.force k φ}, ?_, ?_, ?_⟩
  · rintro χ ⟨Γ, hΓ, hd⟩
    exact derivU_sound hd hK k hΓ
  · intro A B hAB
    exact hAB
  · intro φ hφcl
    rw [mem_traceT_val]
    exact ⟨fun h => h.2, fun h => ⟨hφcl, h⟩⟩

/-- The **confluent** descriptions functor: the trace as a world of
`canonFinC` (a backed `WC cl`). -/
noncomputable def traceC {K : ConstraintModel} (hK : MutuallyConfluent K)
    (cl : Finset PLLFormula) (k : K.W) : (canonFinC cl).W :=
  ⟨traceT K cl k, traceT_maxIn K cl k, trace_backed hK k⟩

#print axioms trace_backed

/-- Depth in the confluent finite model (same formula as `canonDepth`). -/
def canonDepthC (cl : Finset PLLFormula) (Δ : (canonFinC cl).W) : Nat :=
  cl.card - Δ.1.val.card

theorem canonDepthC_le (cl : Finset PLLFormula) (Δ : (canonFinC cl).W) :
    canonDepthC cl Δ ≤ cl.card := Nat.sub_le _ _

/-- Strict `val`-growth strictly drops the confluent depth. -/
theorem canonDepthC_lt {cl : Finset PLLFormula} {Δ Δ' : (canonFinC cl).W}
    (hsub : Δ.1.val ⊆ Δ'.1.val) (hne : Δ.1.val ≠ Δ'.1.val) :
    canonDepthC cl Δ' < canonDepthC cl Δ := by
  have hlt : Δ.1.val.card < Δ'.1.val.card :=
    Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
  have hle : Δ'.1.val.card ≤ cl.card := Finset.card_le_card Δ'.2.1.2.1.1
  unfold canonDepthC
  omega

/-- **Recalibrated witnessing triple.**  As `WitTriple`, but the layered
links sit at `canonDepth` and `canonDepth + 1` (not `2·canonDepth`),
reflecting `crankC`'s one-level ◯-move. -/
structure WitTripleC (cl : Finset PLLFormula)
    (B : LayeredBisimE (fun a => a ≠ p) K M)
    (Δ : (canonFinC cl).W) (m : M.W) where
  k' : K.W
  k : K.W
  m' : M.W
  hΔk : (traceT K cl k).val = Δ.1.val
  hΔk' : (traceT K cl k').val = Δ.1.val
  hik : K.Ri k' k
  him : M.Ri m' m
  hZ' : B.Z (canonDepthC cl Δ + 1) k' m'
  hZ : B.Z (canonDepthC cl Δ) k m

variable (cl : Finset PLLFormula) (B : LayeredBisimE (fun a => a ≠ p) K M)

/-- The amalgam over the recalibrated triple (frame data verbatim from
`witAmalgam`; only the admissibility predicate changes). -/
def witAmalgamC : ConstraintModel where
  W := {q : (canonFinC cl).W × M.W // Nonempty (WitTripleC cl B q.1 q.2)}
  Ri := fun a b => (canonFinC cl).Ri a.1.1 b.1.1 ∧ M.Ri a.1.2 b.1.2
  Rm := fun a b => (canonFinC cl).Rm a.1.1 b.1.1 ∧ M.Rm a.1.2 b.1.2
  F := fun a => a.1.2 ∈ M.F
  V := fun x a =>
    if x = p then a.1.1 ∈ (canonFinC cl).V x ∨ a.1.2 ∈ M.F
    else a.1.2 ∈ M.V x
  refl_i := fun a => ⟨(canonFinC cl).refl_i _, M.refl_i _⟩
  trans_i := fun h₁ h₂ =>
    ⟨(canonFinC cl).trans_i h₁.1 h₂.1, M.trans_i h₁.2 h₂.2⟩
  refl_m := fun a => ⟨(canonFinC cl).refl_m _, M.refl_m _⟩
  trans_m := fun h₁ h₂ =>
    ⟨(canonFinC cl).trans_m h₁.1 h₂.1, M.trans_m h₁.2 h₂.2⟩
  sub_mi := fun h => ⟨(canonFinC cl).sub_mi h.1, M.sub_mi h.2⟩
  hered_F := fun h hF => M.hered_F h.2 hF
  hered_V := by
    intro x a b h hv
    have hv' : (if x = p then a.1.1 ∈ (canonFinC cl).V x ∨ a.1.2 ∈ M.F
        else a.1.2 ∈ M.V x) := hv
    show (if x = p then b.1.1 ∈ (canonFinC cl).V x ∨ b.1.2 ∈ M.F
        else b.1.2 ∈ M.V x)
    by_cases hx : x = p
    · rw [if_pos hx] at hv' ⊢
      rcases hv' with hΔ | hm
      · exact Or.inl ((canonFinC cl).hered_V h.1 hΔ)
      · exact Or.inr (M.hered_F h.2 hm)
    · rw [if_neg hx] at hv' ⊢
      exact M.hered_V h.2 hv'
  full_F := by
    intro x a hF
    show (if x = p then a.1.1 ∈ (canonFinC cl).V x ∨ a.1.2 ∈ M.F
        else a.1.2 ∈ M.V x)
    by_cases hx : x = p
    · rw [if_pos hx]
      exact Or.inr hF
    · rw [if_neg hx]
      exact M.full_F hF

/-- **The financed `iforth` maintenance** (the crux of Lemma 5.4): an
M-move `m → v` is matched by a canonical move `Δ → Δ'` carrying a fresh
witnessing triple.  Two-case reservoir accounting:
  • **strict** (the trace grows): `canonDepthC` drops, so the base link at
    the dropped depth doubles as the reservoir (`mono_le`);
  • **same trace**: `Δ' = Δ` and the reservoir link `hZ'` is spent as the
    new primed link — surplus 1 covers the cost-1 same-depth move.
The `B.iback` move on the primed (reservoir) link supplies the K-partner
`kv`; persistence (`trace_iforth`) gives `Ri Δ Δ'`.  (Fallible escape
`v ∈ M.F` still `sorry`.) -/
theorem witTriple_iforth (hK : MutuallyConfluent K)
    {Δ : (canonFinC cl).W} {m : M.W} (ht : WitTripleC cl B Δ m)
    {v : M.W} (hmv : M.Ri m v) :
    ∃ Δ' : (canonFinC cl).W, (canonFinC cl).Ri Δ Δ' ∧
      Nonempty (WitTripleC cl B Δ' v) := by
  have hm'v : M.Ri ht.m' v := M.trans_i ht.him hmv
  rcases B.iback ht.hZ' hm'v with ⟨kv, hk'kv, hZkv⟩ | hvF
  · by_cases hsame : (traceT K cl kv).val = Δ.1.val
    · -- same trace: Δ' = Δ, spend the reservoir link as the new primed link
      exact ⟨Δ, (canonFinC cl).refl_i Δ,
        ⟨⟨ht.k', kv, ht.m', hsame, ht.hΔk', hk'kv, hm'v, ht.hZ', hZkv⟩⟩⟩
    · -- strict: Δ' = traceC kv, the depth drop finances a fresh triple
      have hRi : Δ.1.val ⊆ (traceC hK cl kv).1.val := by
        rw [← ht.hΔk']; exact trace_iforth hk'kv
      have hlt : canonDepthC cl (traceC hK cl kv) < canonDepthC cl Δ :=
        canonDepthC_lt hRi (fun h => hsame h.symm)
      exact ⟨traceC hK cl kv, hRi,
        ⟨⟨kv, kv, v, rfl, rfl, K.refl_i kv, M.refl_i v,
          B.mono_le (by omega) hZkv, B.mono_le (by omega) hZkv⟩⟩⟩
  · -- fallible escape: v ∈ M.F
    sorry

/-- **The financed `mforth` maintenance** (the ◯-move): an M-`Rₘ`-move
`m → u` is matched by a canonical `Rₘ`-move `Δ → Δ'` (via `obInvW`)
carrying a witnessing triple.  This is the WALL: the base link sits at
level `d`, one below what `B.mback` needs; the reservoir `hZ'` (level
`d+1`, at the predecessors `k' m'`) must finance the single ◯-move. -/
theorem witTriple_mforth (hK : MutuallyConfluent K) (hM : MutuallyConfluent M)
    {Δ : (canonFinC cl).W} {m : M.W} (ht : WitTripleC cl B Δ m)
    {u : M.W} (hmu : M.Rm m u) :
    ∃ Δ' : (canonFinC cl).W, (canonFinC cl).Rm Δ Δ' ∧
      Nonempty (WitTripleC cl B Δ' u) := by
  sorry

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
theorem amalgamation_assembledC (hcl : SubClosed cl) (hK : MutuallyConfluent K)
    (k₀ : K.W) (m₀ : M.W)
    (hB : B.Z (cl.card + 1) k₀ m₀) :
    ∃ (N : ConstraintModel) (C : PBisim p M N) (n₀ : N.W),
      C.Z m₀ n₀ ∧ ∀ φ ∈ cl, (N.force n₀ φ ↔ K.force k₀ φ) := by
  classical
  set Δ₀ : (canonFinC cl).W := traceC hK cl k₀ with hΔ₀
  have hbudget : canonDepthC cl Δ₀ + 1 ≤ cl.card + 1 := by
    have := canonDepthC_le cl Δ₀; omega
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
