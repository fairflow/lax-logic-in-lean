/-
STAGE 2, part (f): `MwitResidue` for the levelled agreement family,
reduced to the promise-stable kernel (derivation:
docs/pcll-1pv-ui-plan.md §"(f) reduced to the promise-stable kernel").

The symmetric ping-pong at the base pair discharges the residue's
fallible branch (top at the partner's trace) and its grown branch (the
depth drop finances a fresh reflexive proper triple — the
`witTriple_mforth` strict-growth pattern).  What survives is the
same-trace matched configuration — `StableCore` below, stated with
FEWER hypotheses than the branch supplies (a strictly stronger
isolation, deliberately: the extra data of the residue configuration
is available to any discharge but not demanded by the statement).
-/
import wip.pcll1pv_stage2e
import wip.witOut

namespace PLLND
open FinComp
namespace SemUI

open Classical

variable {p : String} {K M : ConstraintModel}

/-- **The isolated stage-2 kernel**: a same-trace matched pair one
level short of the proper base.  All that remains of `MwitResidue`
for the levelled family after the ping-pong branches discharge. -/
def StableCore (cl : Finset PLLFormula)
    (B : LayeredBisimWit (fun a => a ≠ p) K M) : Prop :=
  ∀ (_hK : MutuallyConfluent K) {Δ : (canonFinC cl).W} {m : M.W}
    {k t : K.W} {u₂ : M.W} {ψ : PLLFormula},
    SubClosed cl → PLLFormula.falsePLL ∉ Δ.1.val →
    (traceT K cl k).val = Δ.1.val → (traceT K cl t).val = Δ.1.val →
    K.Rm k t → B.Z (2 * canonDepthC cl Δ - 1) t u₂ →
    M.Rm m u₂ → M.force u₂ ψ →
    ∃ (u₃ : M.W) (Δ' : (canonFinC cl).W), M.Rm m u₃ ∧ M.force u₃ ψ ∧
      (canonFinC cl).Rm Δ Δ' ∧ WitTripleC cl B Δ' u₃

/-- **The residue for the levelled family, modulo the kernel**: the
witness-form residue's fallible and grown branches are discharged by
the symmetric ping-pong; the same-trace branch is the kernel. -/
theorem mwitResidue_of_stableCore {cl : Finset PLLFormula}
    (hK : MutuallyConfluent K) (hM : MutuallyConfluent M)
    (hPK : PPure p K) (hPM : PPure p M)
    (hcore : StableCore cl (lvlB (p := p) hK hM hPK hPM)) :
    MwitResidue cl (lvlB (p := p) hK hM hPK hPM) := by
  intro _hK Δ k' k kv κ m' m u' ψ hcl hbot hΔk hΔk' hik him hmu' hψ hu'F hZ' hZ
    hk'kv hZkv hsame hkκ hZκ hκsame
  classical
  -- the symmetric ping-pong at the base pair (k, m), M-side seed u′
  have hd : 1 ≤ canonDepthC cl Δ := canonDepthC_pos hcl hbot
  have hZbase : (lvlB (p := p) hK hM hPK hPM).Z
      (2 * canonDepthC cl Δ - 1 + 1) k m := by
    have h2 : 2 * canonDepthC cl Δ - 1 + 1 = 2 * canonDepthC cl Δ := by omega
    rw [h2]; exact hZ
  obtain ⟨u₂, t, hmu₂, hψ₂, hkt, hres⟩ :=
    lvlB_mwitM hK hM hPK hPM hZbase ⟨u', hmu', hψ⟩
  -- the canonical RmC-move to the partner's trace, shared by two branches
  have hRmt : (canonFinC cl).Rm Δ (traceC hK cl t) := by
    have h := traceC_mforth (cl := cl) hK hkt
    refine ⟨?_, ?_⟩
    · intro χ hχ
      rw [← hΔk] at hχ
      exact h.1 hχ
    · intro χ hbcl hχ
      rw [← hΔk]
      exact h.2 χ hbcl hχ
  rcases hres with hZt | ⟨htF, hu₂F⟩
  · by_cases hts : (traceT K cl t).val = Δ.1.val
    · -- SAME-trace matched: the kernel
      exact hcore hK hcl hbot hΔk hts hkt hZt hmu₂ hψ₂
    · -- GROWN: the depth drop finances a fresh reflexive triple
      have hsub : Δ.1.val ⊆ (traceC hK cl t).1.val := by
        intro φ hφ
        rw [← hΔk] at hφ
        obtain ⟨hφcl, hf⟩ := mem_traceT_val.mp hφ
        exact mem_traceT_val.mpr
          ⟨hφcl, K.force_hered (K.sub_mi hkt) hf⟩
      have hlt : canonDepthC cl (traceC hK cl t) < canonDepthC cl Δ :=
        canonDepthC_lt hsub (fun h => hts h.symm)
      exact ⟨u₂, traceC hK cl t, hmu₂, hψ₂, hRmt,
        .proper t t u₂ rfl rfl (M.refl_i u₂)
          ((lvlB (p := p) hK hM hPK hPM).mono_le (by omega) hZt)
          ((lvlB (p := p) hK hM hPK hPM).mono_le (by omega) hZt)
          (K.refl_i t)⟩
  · -- FALLIBLE pair: top at the partner's trace
    exact ⟨u₂, traceC hK cl t, hmu₂, hψ₂, hRmt,
      .top (mem_traceT_val.mpr ⟨hcl.bot, K.force_of_fallible htF⟩) hu₂F⟩

/-! ## Pins -/

/--
info: 'PLLND.SemUI.mwitResidue_of_stableCore' depends on axioms: [propext, choice, Quot.sound]
-/
#guard_msgs in
#print axioms mwitResidue_of_stableCore

end SemUI
end PLLND
