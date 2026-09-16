/-
# FRJ◯ W5 — completeness, reduced to ONE named statement

The route (plan §3.2), with everything upstream PROVED on this branch:

    ¬ Nonempty (LaxND Γ C)
      →  finite REDUCED countermodel        Reject/Reduce: exists_reduced_countermodel
      →  BUILT tree countermodel            Reject/Complete: built_countermodel / gen_of_reduced
      →  FRJD derivation                    RECONSTRUCTION — the one open statement below

`Reconstruction` is RK(Ξ)'s Lemma 1 with zones, run over `Built`'s own
two constructors (`solo` ↦ the 0-child `world` node, `join` ↦ `world`
with the cone from `RootData.S`); T2's `gen_of_reduced` already did
the bisimulation work of putting the countermodel INTO that shape, so
the induction is on `Built`, not on an arbitrary model.  The side
conditions of `worldOK` hold semantically: `clB`-membership implies
provability implies forcing (G4 soundness), so a refuted goal is
never in the closure, and the ◯-positive obligations read off the
join's own cone data.

With it, `completenessFRJO` below is the goal theorem; its reduction
is PROVED here, choice included only through the upstream (R) chain.
-/
import FRJO.Extract
import Reject.Reduce

namespace FRJO

open PLLND PLLFormula

/-- **W5**: every sequent with a BUILT countermodel has an FRJ◯
derivation whose stable zone the context enters.

**PROVED** (2026-08-16) as `FRJO.reconstruction` in `FRJO/Recon.lean`,
so `completenessFRJO` below is unconditional — see
`FRJO.completenessFRJO'`.  The proof's content is the choice-free
`FRJO.recon`, pinned `[propext, Quot.sound]`. -/
def Reconstruction (b : Nat) : Prop :=
  ∀ (Γ : List PLLFormula) (C : PLLFormula)
    (M : PLLND.ConstraintModel) (r : M.W),
    Reject.Built M → (∀ φ ∈ Γ, M.force r φ) → ¬ M.force r C →
    ∃ S : Reg ⟨Γ, C⟩, S.goal = C ∧ Γ ⊆ S.stable ∧
      Nonempty (FRJD ⟨Γ, C⟩ b S)

/-- **Completeness for LJF◯'s logic, via FRJ◯** — PROVED conditional
on `Reconstruction` alone; every other link is a theorem of this
branch (`not_laxND_iff_built`'s forward direction
`built_countermodel`). -/
theorem completenessFRJO {b : Nat} (hR : Reconstruction b)
    {Γ : List PLLFormula} {C : PLLFormula}
    (h : ¬ Nonempty (PLLND.LaxND Γ C)) :
    ∃ S : Reg ⟨Γ, C⟩, S.goal = C ∧ Γ ⊆ S.stable ∧
      Nonempty (FRJD ⟨Γ, C⟩ b S) := by
  obtain ⟨M, r, hB, hΓ, hC⟩ := Reject.built_countermodel h
  exact hR Γ C M r hB hΓ hC

/-- And the two-sided reading: with `ExtractForces` (W3b) as well,
derivability of the refutation calculus is EXACTLY underivability —
the biconditional that makes "REFUTED" a derivation.

**CAUTION (2026-08-16)**: `ExtractForces` is REFUTED for `worldOK` v3
(`FRJO/Screen.lean`, three certified cells), so this theorem is
currently VACUOUS.  It becomes usable only with the v4 repair of the
`world` rule specified there. -/
theorem frjd_iff_not_laxND {b : Nat} {Γ : List PLLFormula} {C : PLLFormula}
    (hE : ExtractForces ⟨Γ, C⟩ b) :
    (∃ S : Reg ⟨Γ, C⟩, S.goal = C ∧ Γ ⊆ S.stable ∧
        Nonempty (FRJD ⟨Γ, C⟩ b S) ∧ S.stable = Γ) →
      ¬ Nonempty (PLLND.LaxND Γ C) := by
  rintro ⟨S, hg, _, ⟨d⟩, hs⟩
  have := not_laxND_of_FRJD hE d
  rw [hs, hg] at this
  exact this

/-! ## Pins -/

/-- info: 'FRJO.completenessFRJO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms completenessFRJO

end FRJO
