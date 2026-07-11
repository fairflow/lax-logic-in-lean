import LaxLogic.PLLG4UITrunc

/-!
# WIP scaffold: the absorption lemma (budget stabilization)

Target (docs/ui-endgame.md): above the jump-state threshold, adjacent
budgets are interderivable — the one genuinely novel lemma of the UI
tower.  Structure:

* `itp_absorb_base` — the base band `(K+1 → K)`: the cascade with the
  pigeonhole/splice argument.  THE crux.
* `itp_absorb_of_base` — the upper band by induction on `b − K`,
  consuming the base at all fuels; mechanically parallel to
  `itp_budget_mono` (agent-able).

Isolated below as micro-lemmas: the two boxed-position maps whose
exact budget annotations decide the cascade's shape.  Everything here
may contain `sorry`; nothing is imported by the library root.
-/

open PLLFormula

namespace PLLND

/-- Budget cap: overcounts the jump states
`{E} ∪ {A_F, ◯A_F : ◯A_F⊃B ∈ S} ∪ {A⊃B : (A⊃B)⊃D ∈ S}`. -/
def bcap (S : Finset PLLFormula) : Nat := 2 * S.card + 4

/-- Phase B (the crux): the base band. -/
theorem itp_absorb_base (p : String) (S : Finset PLLFormula) : ∀ fuel,
    (∀ Γ, G4c [itpE p S fuel (bcap S) Γ] (itpE p S fuel (bcap S + 1) Γ)) ∧
    (∀ Γ C, G4c [itpA p S fuel (bcap S + 1) Γ C]
      (itpA p S fuel (bcap S) Γ C)) := by
  sorry

/-- Phase A: the upper band from the base, by induction on the slack;
each step is a fuel induction structurally parallel to
`itp_budget_mono` with the jump components consuming the previous
band member. -/
theorem itp_absorb_of_base (p : String) (S : Finset PLLFormula)
    (hbase : ∀ fuel,
      (∀ Γ, G4c [itpE p S fuel (bcap S) Γ] (itpE p S fuel (bcap S + 1) Γ)) ∧
      (∀ Γ C, G4c [itpA p S fuel (bcap S + 1) Γ C]
        (itpA p S fuel (bcap S) Γ C))) :
    ∀ (j fuel : Nat),
    (∀ Γ, G4c [itpE p S fuel (bcap S + j) Γ]
      (itpE p S fuel (bcap S + j + 1) Γ)) ∧
    (∀ Γ C, G4c [itpA p S fuel (bcap S + j + 1) Γ C]
      (itpA p S fuel (bcap S + j) Γ C)) := by
  sorry

/-- Packaged: all budgets above the cap are interderivable. -/
theorem itp_absorb (p : String) (S : Finset PLLFormula) {b : Nat}
    (hb : bcap S ≤ b) (fuel : Nat) :
    (∀ Γ, G4c [itpE p S fuel b Γ] (itpE p S fuel (b + 1) Γ)) ∧
    (∀ Γ C, G4c [itpA p S fuel (b + 1) Γ C] (itpA p S fuel b Γ C)) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hb
  exact itp_absorb_of_base p S (itp_absorb_base p S) j fuel

/-! ### The boxed-position micro-obligations (exact annotations)

The cascade's only genuinely hard positions are under `◯(E ⇢ ·)`.
Candidate resolution: the guard `E` transports ambient into the box —
`laxL` the source box against the (◯-shaped) target, then the
antecedent `E` is available as ambient for the consequent map
(`box_guard_collapse`-style), and the repeat-shortcut's
budget-monotonicity move applies to the in-context inner value.
The two micro-lemmas below pin the annotation question: with the
source guard at `E @ b` and the target guard at `E @ b'` (`b' ≤ b`),
which direction of E-glue is needed, and does it stay inside the
band? -/

/-- γ-map, candidate form: source box at budgets (E@b, A@b), target
box at (E@b', A@b') with `b' + 1 = b`; the E-glue needed after
`laxL`+`laxR`+`impR` is `E@b'` ⊢-feeding the antecedent `E@b`, i.e.
budget-monotonicity of E in the LOW-to-HIGH direction — which is the
ABSORB direction, hence in-band only if `bcap S ≤ b'`. -/
theorem gamma_box_map (p : String) (S : Finset PLLFormula)
    (fuel b : Nat) (Γ : List PLLFormula) (g : PLLFormula)
    (hA : G4c ((itpE p S fuel b Γ) ::
                (itpA p S fuel b Γ g) :: [])
              (itpA p S fuel (b - 1) Γ g)) :
    G4c [((itpE p S fuel b Γ).ifThen (itpA p S fuel b Γ g)).somehow]
        (((itpE p S fuel (b - 1) Γ).ifThen
          (itpA p S fuel (b - 1) Γ g)).somehow) := by
  sorry

end PLLND
