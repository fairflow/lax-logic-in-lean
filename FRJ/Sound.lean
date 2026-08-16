/-
# Soundness of FRJ(G) — in progress

Section 3.1 and the appendix "Soundness of FRJ(G)" of Fiorentini–Ferrari.

The paper's proof is a single induction on the height of a sequent
occurrence in the derivation `D`, carried out in the one model `Mod(D)`,
using Lemma 3.4(iii) and applying its own induction hypothesis at
p-sequents above the one under consideration.  That is the proof to
follow; it is NOT reorganised here into invariants carried by the
construction.

Landed so far: the `Ax^R` case of Lemma 3.9(i), which is the base case
of that induction.  Every other case is OPEN and nothing is claimed for
it.
-/
import FRJ.Model

namespace FRJ

open Form

/-! ## The `Ax^R` case of Lemma 3.9(i)

"We have `σ = Ĝ_at \ {C} ⇒ C`, with `C ∈ Prime`.  Since `φ(σ) = σ` and
`V(σ) = Ĝ_at \ {C}`, (i) immediately follows."
-/

/-- `Mod(D)` for a derivation `D` consisting of a single `Ax^R` axiom:
one world, whose `V` is `Lhs(σ) ∩ PV = Ĝ_at \ {F}`. -/
def axRModel (G F : Form) : Kripke := solo ((gAt G).erase F)

/-- **The `Ax^R` case of Lemma 3.9(i), PROVED.**  Here `φ(σ) = σ`, so the
claim is that the axiom's own world forces `Ĝ_at \ {F}` and refutes `F`.
For `F = ⊥` because no world forces `⊥`; for `F` a variable because `F`
was erased from `V(σ)`. -/
theorem axR_sound (G F : Form) (hF : F.isPrime) :
    (axRModel G F).forces (axRModel G F).root ((gAt G).erase F) ∧
      ¬ (axRModel G F).force (axRModel G F).root F := by
  constructor
  · refine solo_forces_root (fun X hX => ?_) (subset_refl _)
    have := Finset.mem_of_mem_erase hX
    simpa [gAt] using (Finset.mem_filter.mp this).2
  · match F, hF with
    | .bot, _ => exact fun h => h
    | .atom p, _ => exact fun h => (Finset.notMem_erase _ _) h

/-! ## Sanity checks on the encoding

An atom and `⊥` are both IPC-underivable and both provable in `FRJ(G)`
by `Ax^R` alone: the indexed family is inhabited as intended.
-/

example (p : String) : Provable (.atom p) :=
  ⟨(gAt (.atom p)).erase (.atom p), ⟨.axR (.atom p) trivial (sfR_self _)⟩⟩

example : Provable .bot :=
  ⟨(gAt .bot).erase .bot, ⟨.axR .bot trivial (sfR_self _)⟩⟩

end FRJ
