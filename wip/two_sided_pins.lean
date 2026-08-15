/-
Kernel-level exemplars of the two-sided engine's certificate formats —
one per side, `decide`-checked end to end, so the whole pipeline
"Bool = true ⟹ (non)derivability" is demonstrated at the kernel, not
only at runtime.

The formulas are corpus cells: ρ3 = ¬◯⊥, ρ4 = ¬◯⊥ ∨ ◯⊥ (a real order
edge), and [◯⊥] ⊬ ⊥ on the two-world fallible-leaf tree.
-/
import wip.ljfo_link

open PLLND PLLFormula TwoSidedLink

namespace TwoSidedPins

def oBot : PLLFormula := .somehow .falsePLL
def nOBot : PLLFormula := .ifThen oBot .falsePLL

/-- **Proof-side exemplar**: `[¬◯⊥] ⊢ ¬◯⊥ ∨ ◯⊥` because the LJF◯
searcher finds it at fuel 16 — and the KERNEL re-runs the search
inside `decide`. -/
theorem edge_rho3_rho4 : Nonempty (LaxND [nOBot] (.or nOBot oBot)) :=
  laxND_of_searchProves (f := 16) (by decide)

/-- **Refutation-side exemplar**: `[◯⊥] ⊬ ⊥` on the two-world tree
with a fallible leaf — a `Built` certificate, `decide`-checked. -/
theorem obot_not_bot : ¬ Nonempty (LaxND [oBot] .falsePLL) :=
  Reject.not_laxND_of_certifies
    (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (by decide)

/-! ## Pins -/

/-- info: 'TwoSidedPins.edge_rho3_rho4' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms edge_rho3_rho4

/-- info: 'TwoSidedPins.obot_not_bot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms obot_not_bot

end TwoSidedPins
