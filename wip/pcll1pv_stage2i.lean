/-
STAGE 2, part (i): CLOSING `StableCore`.

Two regions, two arguments:

* **Promised `⊥`** (`◯⊥ ∈ val Δ`): closes OUTRIGHT.  The K-side
  promise yields a fallible `Rₘ`-successor `κ₀` of `k` (bare
  possibility), whose trace is a lawful `RmC`-successor
  (`traceC_mforth`).  `◯⊥` costs crank 2, so it transfers across the
  one-short link `Z(2d−1) t u₂` for every `d ≥ 1`; bare possibility
  on the M side then escalates the witness to a fallible `u₃ ⊒ₘ u₂`,
  and `top` answers with `ψ` forced vacuously.
* **`◯⊥`-free**: depth 1 is IMPOSSIBLE here — a depth-1 world's val
  is exactly `cl \ {⊥}`, which contains `◯⊥` (◯-adequacy).  So
  `d ≥ 2`, hence `4d − 2 ≥ 6`, and a CLOSED-FRAGMENT COLLAPSE at
  crank 6 (`ClosedCollapse 6`, the probe's target) promotes the
  one-short link to EVERY level — the reflexive triple answers with
  the promoted link serving both slots.

The invariant one-short wall thus reduces to one finite,
certificate-checkable statement about closed PCLL formulas.
-/
import wip.pcll1pv_stage2h
import wip.pcll1pv_stage2f

namespace PLLND
open FinComp
namespace SemUI

open Classical

variable {p : String} {K M : ConstraintModel}

/-- **The closed-fragment collapse at crank `R₀`** (over the mutually
confluent class): every closed formula is force-equivalent to a closed
representative of crank ≤ `R₀`.  Discharged by finitely many `DerivU`
interderivability certificates via `derivU_sound`. -/
def ClosedCollapse (R₀ : Nat) : Prop :=
  ∀ χ : PLLFormula, (∀ a ∈ χ.atoms, a ∈ (∅ : Finset String)) →
    ∃ ρ : PLLFormula, crank ρ ≤ R₀ ∧
      (∀ a ∈ ρ.atoms, a ∈ (∅ : Finset String)) ∧
      ∀ (C : ConstraintModel), MutuallyConfluent C →
        ∀ w, (C.force w χ ↔ C.force w ρ)

/-- The collapse promotes the levelled agreement from any level with
`2α ≥ R₀` to EVERY level. -/
theorem lvlZ_promote {R₀ : Nat} (hcol : ClosedCollapse R₀)
    (hK : MutuallyConfluent K) (hM : MutuallyConfluent M)
    {α : Nat} {k : K.W} {m : M.W} (hα : R₀ ≤ 2 * α)
    (h : lvlZ K M α k m) : ∀ β, lvlZ K M β k m := by
  intro β χ _hc ha
  obtain ⟨ρ, hρc, hρa, hρe⟩ := hcol χ ha
  exact ((hρe K hK k).trans
    ((h ρ (le_trans hρc hα) hρa).trans (hρe M hM m).symm))

/-- **`StableCore`, closed** modulo `ClosedCollapse 6`. -/
theorem stableCore_of_collapse {cl : Finset PLLFormula}
    (hadeq : OBoxAdeq cl) (hcol : ClosedCollapse 6)
    (hK : MutuallyConfluent K) (hM : MutuallyConfluent M)
    (hPK : PPure p K) (hPM : PPure p M) :
    StableCore cl (lvlB (p := p) hK hM hPK hPM) := by
  intro _hK Δ m k t u₂ ψ hcl hbot hΔk hts hkt hZt hmu hψu
  have hd : 1 ≤ canonDepthC cl Δ := canonDepthC_pos hcl hbot
  by_cases hb : (PLLFormula.falsePLL).somehow ∈ Δ.1.val
  · -- PROMISED ⊥: fallible realisers on both sides, `top` at the trace
    have hkbox : K.force k ((PLLFormula.falsePLL).somehow) := by
      rw [← hΔk] at hb
      exact (mem_traceT_val.mp hb).2
    obtain ⟨κ₀, hkκ₀, hκ₀F⟩ :=
      (force_somehow_iff_of_confluent hK).mp hkbox
    have htbox : K.force t ((PLLFormula.falsePLL).somehow) := by
      rw [← hts] at hb
      exact (mem_traceT_val.mp hb).2
    have hubox : M.force u₂ ((PLLFormula.falsePLL).somehow) :=
      (hZt ((PLLFormula.falsePLL).somehow)
        (by simp [crank]; omega)
        (by intro a ha; simp [PLLFormula.atoms] at ha)).mp htbox
    obtain ⟨u₃, hu₂u₃, hu₃F⟩ :=
      (force_somehow_iff_of_confluent hM).mp hubox
    have hRmκ : (canonFinC cl).Rm Δ (traceC hK cl κ₀) := by
      have h := traceC_mforth (cl := cl) hK hkκ₀
      refine ⟨?_, ?_⟩
      · intro χ hχ
        rw [← hΔk] at hχ
        exact h.1 hχ
      · intro χ hbcl hχ
        rw [← hΔk]
        exact h.2 χ hbcl hχ
    exact ⟨u₃, traceC hK cl κ₀, M.trans_m hmu hu₂u₃,
      M.force_of_fallible hu₃F, hRmκ,
      .top (mem_traceT_val.mpr ⟨hcl.bot, K.force_of_fallible hκ₀F⟩) hu₃F⟩
  · -- ◯⊥-FREE: depth ≥ 2, promote the link, answer reflexively
    have hd2 : 2 ≤ canonDepthC cl Δ := by
      rcases Nat.lt_or_ge (canonDepthC cl Δ) 2 with hlt | hge
      · -- depth 1: val = cl \ {⊥}, which contains ◯⊥ — contradiction
        exfalso
        have hd1 : canonDepthC cl Δ = 1 := by omega
        have hsub : Δ.1.val ⊆ cl := Δ.2.1.2.1.1
        have hcard : (cl \ Δ.1.val).card = 1 := by
          rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub]
          exact hd1
        have hbotmem : PLLFormula.falsePLL ∈ cl \ Δ.1.val :=
          Finset.mem_sdiff.mpr ⟨hcl.bot, hbot⟩
        have hsingle : cl \ Δ.1.val = {PLLFormula.falsePLL} := by
          obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcard
          rw [hx] at hbotmem ⊢
          rw [Finset.mem_singleton.mp hbotmem]
        have hboxcl : (PLLFormula.falsePLL).somehow ∈ cl :=
          hadeq _ hcl.bot
        have : (PLLFormula.falsePLL).somehow ∈ cl \ Δ.1.val :=
          Finset.mem_sdiff.mpr ⟨hboxcl, hb⟩
        rw [hsingle, Finset.mem_singleton] at this
        exact PLLFormula.noConfusion this
      · exact hge
    have hZall : ∀ β, lvlZ K M β t u₂ :=
      lvlZ_promote hcol hK hM (α := 2 * canonDepthC cl Δ - 1)
        (by omega) hZt
    exact ⟨u₂, Δ, hmu, hψu, (canonFinC cl).refl_m Δ,
      .proper t t u₂ hts hts (M.refl_i u₂)
        (hZall (2 * canonDepthC cl Δ + 1))
        (hZall (2 * canonDepthC cl Δ)) (K.refl_i t)⟩

/-- **The residue, closed** modulo the collapse: the witness-form
residue of the levelled family holds outright given `ClosedCollapse 6`. -/
theorem mwitResidue_of_collapse {cl : Finset PLLFormula}
    (hadeq : OBoxAdeq cl) (hcol : ClosedCollapse 6)
    (hK : MutuallyConfluent K) (hM : MutuallyConfluent M)
    (hPK : PPure p K) (hPM : PPure p M) :
    MwitResidue cl (lvlB (p := p) hK hM hPK hPM) :=
  mwitResidue_of_stableCore hK hM hPK hPM
    (stableCore_of_collapse hadeq hcol hK hM hPK hPM)

/-! ## Pins -/

/--
info: 'PLLND.SemUI.lvlZ_promote' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms lvlZ_promote

/--
info: 'PLLND.SemUI.stableCore_of_collapse' depends on axioms: [propext, choice, Quot.sound]
-/
#guard_msgs in
#print axioms stableCore_of_collapse

/--
info: 'PLLND.SemUI.mwitResidue_of_collapse' depends on axioms: [propext, choice, Quot.sound]
-/
#guard_msgs in
#print axioms mwitResidue_of_collapse

end SemUI
end PLLND
