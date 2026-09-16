/-
STAGE 4: the PICLL corollary.

PICLL is the infallible confluent class (`¬◯⊥`; semantically `F = ∅`).
The arc report's asymmetry — "the prover gains and the refuter loses"
— is made exact here:

* **The closed dichotomy** (`closed_dichotomy_infallible`): over
  INFALLIBLE constraint models (confluence not even needed), every
  closed formula is globally valid or globally refuted.  The refuter
  loses every closed distinction: no fallible-world countermodel
  survives `¬◯⊥`, and with it every closed separation of the fallible
  battery dies.
* **The rank-1 collapse** (`closedCollapseInf_one`): consequently the
  infallible analogue of `ClosedCollapse` holds AT RANK 1 with
  representatives `⊥` and `⊤ := ⊥ ⊃ ⊥` — by a forty-line induction,
  no certificate search needed.  Contrast the fallible class, where
  `ClosedCollapse 6` is the probe's open target.

TRANSFER NOTE (the plan's stage-4 item): the stage-2/3 chain is
instantiated over the fallible confluent class; re-instantiating it
over PICLL would make both kernels conditional on the PROVABLE rank-1
collapse — nothing new — but requires the `DerivUNoFall` completeness
anchor in place of `derivU_iff_confluent_valid`.  That anchor
(`PLLNoFall.lean`) is the one remaining transfer condition, recorded
in the plan.  On the general-PLL sorries (`PLLSemUIChar.lean:322/327`)
the stage-2 machinery says nothing directly — the σ-ping-pong consumes
mutual confluence at every growth step, and the walls it dissolved are
exactly the ones that remain real over unrestricted constraint models.
-/
import wip.pcll1pv_stage3b

namespace PLLND
open FinComp
namespace SemUI

open Classical

/-- **The closed dichotomy over infallible models**: every closed
formula is globally valid or globally refuted (confluence not
required). -/
theorem closed_dichotomy_infallible :
    ∀ χ : PLLFormula, (∀ a ∈ χ.atoms, a ∈ (∅ : Finset String)) →
      (∀ (C : ConstraintModel), C.F = ∅ → ∀ w, C.force w χ) ∨
      (∀ (C : ConstraintModel), C.F = ∅ → ∀ w, ¬ C.force w χ) := by
  intro χ
  induction χ with
  | prop a =>
      intro hA
      exact absurd (hA a (by simp [PLLFormula.atoms])) (by simp)
  | falsePLL =>
      intro _
      refine .inr (fun C hF w h => ?_)
      have h' : w ∈ C.F := h
      rw [hF] at h'
      exact h'
  | and φ ψ ihφ ihψ =>
      intro hA
      have h1 := ihφ (fun a ha => hA a (by simp [PLLFormula.atoms, ha]))
      have h2 := ihψ (fun a ha => hA a (by simp [PLLFormula.atoms, ha]))
      rcases h1 with h1 | h1
      · rcases h2 with h2 | h2
        · exact .inl (fun C hF w => ⟨h1 C hF w, h2 C hF w⟩)
        · exact .inr (fun C hF w h => h2 C hF w h.2)
      · exact .inr (fun C hF w h => h1 C hF w h.1)
  | or φ ψ ihφ ihψ =>
      intro hA
      have h1 := ihφ (fun a ha => hA a (by simp [PLLFormula.atoms, ha]))
      have h2 := ihψ (fun a ha => hA a (by simp [PLLFormula.atoms, ha]))
      rcases h1 with h1 | h1
      · exact .inl (fun C hF w => .inl (h1 C hF w))
      · rcases h2 with h2 | h2
        · exact .inl (fun C hF w => .inr (h2 C hF w))
        · refine .inr (fun C hF w h => ?_)
          rcases h with h | h
          · exact h1 C hF w h
          · exact h2 C hF w h
  | ifThen φ ψ ihφ ihψ =>
      intro hA
      have h1 := ihφ (fun a ha => hA a (by simp [PLLFormula.atoms, ha]))
      have h2 := ihψ (fun a ha => hA a (by simp [PLLFormula.atoms, ha]))
      rcases h1 with h1 | h1
      · rcases h2 with h2 | h2
        · exact .inl (fun C hF w v _ _ => h2 C hF v)
        · refine .inr (fun C hF w h => ?_)
          exact h2 C hF w (h w (C.refl_i w) (h1 C hF w))
      · exact .inl (fun C hF w v _ hφ => absurd hφ (h1 C hF v))
  | somehow φ ih =>
      intro hA
      have h1 := ih (fun a ha => hA a (by simp [PLLFormula.atoms, ha]))
      rcases h1 with h1 | h1
      · exact .inl (fun C hF w v _ => ⟨v, C.refl_m v, h1 C hF v⟩)
      · refine .inr (fun C hF w h => ?_)
        obtain ⟨u, _, hu⟩ := h w (C.refl_i w)
        exact h1 C hF u hu

/-- The infallible analogue of `ClosedCollapse`, at rank `R₀`. -/
def ClosedCollapseInf (R₀ : Nat) : Prop :=
  ∀ χ : PLLFormula, (∀ a ∈ χ.atoms, a ∈ (∅ : Finset String)) →
    ∃ ρ : PLLFormula, crank ρ ≤ R₀ ∧
      (∀ a ∈ ρ.atoms, a ∈ (∅ : Finset String)) ∧
      ∀ (C : ConstraintModel), C.F = ∅ → MutuallyConfluent C →
        ∀ w, (C.force w χ ↔ C.force w ρ)

/-- **The PICLL collapse is PROVABLE, at rank 1**: representatives
`⊤ := ⊥ ⊃ ⊥` and `⊥`. -/
theorem closedCollapseInf_one : ClosedCollapseInf 1 := by
  intro χ hχ
  rcases closed_dichotomy_infallible χ hχ with hval | hinv
  · refine ⟨.ifThen .falsePLL .falsePLL, by simp [crank],
      (by intro a ha; simp [PLLFormula.atoms] at ha), ?_⟩
    intro C hF _ w
    exact iff_of_true (hval C hF w) (fun _v _hv h => h)
  · refine ⟨.falsePLL, by simp [crank],
      (by intro a ha; simp [PLLFormula.atoms] at ha), ?_⟩
    intro C hF _ w
    refine iff_of_false (hinv C hF w) (fun h => ?_)
    have h' : w ∈ C.F := h
    rw [hF] at h'
    exact h'

/-! ## Pins -/

/--
info: 'PLLND.SemUI.closed_dichotomy_infallible' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms closed_dichotomy_infallible

/--
info: 'PLLND.SemUI.closedCollapseInf_one' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms closedCollapseInf_one

end SemUI
end PLLND
