/-
# Soundness of FRJ(G) — in progress

Section 3.1 and the appendix "Soundness of FRJ(G)" of Fiorentini–Ferrari.
The architecture, derived from the paper's own proof, is written out in
`docs/frj-fidelity.md`.

Landed here so far: the `Ax^R` case of Lemma 3.9(i), which is the base
case of the main induction and the first exercise of the `PModel` kit.
The remaining cases are OPEN; nothing in this file is asserted beyond
what it proves.
-/
import FRJ.Model

namespace FRJ

open Form

/-! ## The `Ax^R` case of Lemma 3.9(i)

"We have `σ = Ĝ_at \ {C} ⇒ C`, with `C ∈ Prime`.  Since `φ(σ) = σ` and
`V(σ) = Ĝ_at \ {C}`, (i) immediately follows."
-/

/-- The model extracted from an `Ax^R` leaf: the single world whose label
is `Ĝ_at \ {F}`. -/
def axRModel (G F : Form) : PModel :=
  PModel.solo ((gAt G).erase F) (by
    intro X hX
    have := Finset.mem_of_mem_erase hX
    simpa [gAt] using (Finset.mem_filter.mp this).2)

/-- **The `Ax^R` case, PROVED.**  The extracted world forces the whole
left-hand side and refutes the goal.  For `F = ⊥` this is because no
world forces `⊥`; for `F` a variable it is because `F` was erased from
the valuation. -/
theorem axR_sound (G F : Form) (hF : F.isPrime) :
    (axRModel G F).K.forces (axRModel G F).K.root ((gAt G).erase F) ∧
      ¬ (axRModel G F).K.force (axRModel G F).K.root F := by
  refine ⟨(axRModel G F).forces_lhs _, ?_⟩
  match F, hF with
  | .bot, _ => exact fun h => h
  | .atom p, _ =>
      intro h
      exact (Finset.notMem_erase _ _) ((axRModel G (.atom p)).val_eq _ p |>.mp h)

/-! ## Sanity checks on the encoding

The two smallest instances: an atom and `⊥` are both underivable in IPC
and both provable in `FRJ(G)` by `Ax^R` alone.  These check that the
indices of the family are inhabited as intended — the encoding is usable,
not merely well-typed.
-/

example (p : String) : Provable (.atom p) :=
  ⟨(gAt (.atom p)).erase (.atom p), ⟨.axR (.atom p) trivial (sfR_self _)⟩⟩

example : Provable .bot :=
  ⟨(gAt .bot).erase .bot, ⟨.axR .bot trivial (sfR_self _)⟩⟩

end FRJ
