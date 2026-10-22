import wip.gapWidth
import Meta.Audit

/-!
# Independence of the odd gaps, one gap on the right

The gaps are `g k = gap k = ◯t(2k+1) ↠ t(2k+1)` (`wip/gapWidth.lean`), with
`t n = rnSub n`.  The conjecture under test (`wip/f0IndepBlueprint.lean`) is

    Indep:  for all finite disjoint S, T ⊆ ℕ,   ⋀_{i∈S} g(2i+1)  ⊬  ⋁_{j∈T} g(2j+1).

This file settles the case `|T| = 1` (PROVED):

    ⋀_{i∈S} g(2i+1)  ⊬  g(2j+1)        for every finite S with j ∉ S

(`odd_gaps_single`, the conjunction as `SemUI.bigAnd`; `odd_gaps_single_ctx`,
the conjuncts as a context).  The argument is that of `gap_incomparable`: on
the edged lift `cmE m` with `m = 2j`, the edge world `2j+3` refutes exactly
the gaps of index `m+1 = 2j+1` and `m+2 = 2j+2` (`gap_fails`) and forces every
other gap (`gap_forced`).  The window `{2j+1, 2j+2}` holds one odd index only,
so every `g(2i+1)` with `i ≠ j` is forced there.

In particular B1's first designed cell, `g1 ∧ g5 ⊬ g3`, is the instance
`S = [0, 2]`, `j = 1` (`cell_g1_g5_g3`).

**Axioms.**  The pins are `[propext, Classical.choice, Quot.sound]`, not
`[propext, Quot.sound]`: `Classical.choice` is inherited from the two lemmas
reused, through the model itself and the rung truth sets
(`#choice_path`, 2026-10-22):

    cmE_box_force → cmE → cmE._proof_6 → Classical.byContradiction
    sat_rn_odd → sat_rnP → sat_rnP._proof_1_5 → Classical.propDecidable

(`omega`/`by_contra` steps in the frame-law proof of `cmE` in
`wip/chainOff.lean` and in the truth-set induction of `wip/rnEmbed.lean`).
The statement itself needs no choice; removing it means re-proving those two
lemmas choice-free, not done here.
-/

open PLLFormula

namespace PLLND
namespace F0

open SemUI RNEmbed

/-- **One odd gap on the right, the conjuncts as a context**: for every finite
`S` with `j ∉ S`,  `{g(2i+1) : i ∈ S} ⊬ g(2j+1)`. -/
theorem odd_gaps_single_ctx (S : List Nat) {j : Nat} (hj : j ∉ S) :
    (S.map fun i => gap (2 * i + 1)) ⊬ gap (2 * j + 1) := by
  rintro ⟨d⟩
  have hs := soundness d (cmE (2 * j)) (some (2 * j + 3)) (fun ψ hψ => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hψ
    have hij : i ≠ j := fun h => hj (h ▸ hi)
    exact gap_forced (2 * j) (2 * i + 1) (by omega) (by omega) (2 * j + 3))
  exact gap_fails (2 * j) (2 * j + 1) (by omega) (by omega) hs

/-- **One odd gap on the right**: for every finite `S` with `j ∉ S`,

    ⋀_{i∈S} g(2i+1)  ⊬  g(2j+1). -/
theorem odd_gaps_single (S : List Nat) {j : Nat} (hj : j ∉ S) :
    [bigAnd (S.map fun i => gap (2 * i + 1))] ⊬ gap (2 * j + 1) := fun h =>
  odd_gaps_single_ctx S hj
    (Deriv.cutHead (Deriv.bigAndIntro fun _ hD => Deriv.iden hD) h)

/-- B1's first designed cell, settled without the tool: `g1 ∧ g5 ⊬ g3`. -/
theorem cell_g1_g5_g3 : [(gap 1).and (gap 5)] ⊬ gap 3 :=
  odd_gaps_single [0, 2] (j := 1) (by decide)

end F0
end PLLND

#axioms_within PLLND.F0.odd_gaps_single_ctx [propext, Classical.choice, Quot.sound]
#axioms_within PLLND.F0.odd_gaps_single [propext, Classical.choice, Quot.sound]
#axioms_within PLLND.F0.cell_g1_g5_g3 [propext, Classical.choice, Quot.sound]
