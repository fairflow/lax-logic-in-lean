/-
STAGE 3, part (a): the one-variable confluent amalgamation, ASSEMBLED.

The W-chain instantiated at the levelled family, with every clause now
in hand: i-clauses and witness m-clauses from stage 2(a)–(e), the
residue from stage 2(i), the corner from stage 2(j) — everything
conditional only on `ClosedCollapse 6`.  The statement is stage 0's
target in witness form: two mutually confluent p-pure models linked by
closed-formula agreement at the entry budget amalgamate into a
CONFLUENT p-variant of `M` matching `K`'s `cl`-theory at the root and
transferring every p-free formula.
-/
import wip.pcll1pv_stage2j

namespace PLLND
open FinComp
namespace SemUI

open Classical

variable {p : String} {K M : ConstraintModel}

/-- **The one-variable confluent amalgamation** (Thm 5.1's semantic
heart), modulo `ClosedCollapse 6`. -/
theorem oneVarConfluentAmalgamationW {cl : Finset PLLFormula}
    (hadeq : OBoxAdeq cl) (hcl : SubClosed cl) (hcol : ClosedCollapse 6)
    (hK : MutuallyConfluent K) (hM : MutuallyConfluent M)
    (hPK : PPure p K) (hPM : PPure p M)
    (k₀ : K.W) (m₀ : M.W)
    (hB : lvlZ K M (2 * cl.card + 1) k₀ m₀) :
    ∃ (N : ConstraintModel), MutuallyConfluent N ∧
      ∃ (C : PBisimWit p M N) (n₀ : N.W),
        C.Z m₀ n₀ ∧ (∀ φ ∈ cl, (N.force n₀ φ ↔ K.force k₀ φ)) ∧
        (∀ χ : PLLFormula, (∀ a ∈ χ.atoms, a ≠ p) →
          (M.force m₀ χ ↔ N.force n₀ χ)) := by
  classical
  have hmw : (lvlB (p := p) hK hM hPK hPM).MWitM := lvlB_mwitM hK hM hPK hPM
  have hres : MwitResidue cl (lvlB (p := p) hK hM hPK hPM) :=
    mwitResidue_of_collapse hadeq hcol hK hM hPK hPM
  have hAC : MutuallyConfluent (witAmalgamC cl (lvlB (p := p) hK hM hPK hPM)) :=
    amalgamConfluent_of_collapse hadeq hcl hcol hK hM hPK hPM hK hM
  set Δ₀ : (canonFinC cl).W := traceC hK cl k₀ with hΔ₀
  have hd₀ := canonDepthC_le cl Δ₀
  have htrip : WitTripleC cl (lvlB (p := p) hK hM hPK hPM) Δ₀ m₀ :=
    .proper k₀ k₀ m₀ rfl rfl (M.refl_i m₀)
      ((lvlB (p := p) hK hM hPK hPM).mono_le (by omega) hB)
      ((lvlB (p := p) hK hM hPK hPM).mono_le (by omega) hB) (K.refl_i k₀)
  obtain ⟨C, hC⟩ :=
    wit_pbisimW cl (lvlB (p := p) hK hM hPK hPM) hcl hK hmw hres
  refine ⟨witAmalgamC cl (lvlB (p := p) hK hM hPK hPM), hAC, C,
    ⟨(Δ₀, m₀), htrip⟩, hC ⟨(Δ₀, m₀), htrip⟩, ?_, ?_⟩
  · intro φ hφ
    rw [wit_forceC cl (lvlB (p := p) hK hM hPK hPM) hcl hadeq hK φ hφ
      ⟨(Δ₀, m₀), htrip⟩]
    constructor
    · intro h
      exact (mem_traceT_val.mp h).2
    · intro h
      exact mem_traceT_val.mpr ⟨hφ, h⟩
  · intro χ hχ
    exact force_iff_of_witOut hM C hχ (hC ⟨(Δ₀, m₀), htrip⟩)

/-! ## Pins -/

/--
info: 'PLLND.SemUI.oneVarConfluentAmalgamationW' depends on axioms: [propext, choice, Quot.sound]
-/
#guard_msgs in
#print axioms oneVarConfluentAmalgamationW

end SemUI
end PLLND
