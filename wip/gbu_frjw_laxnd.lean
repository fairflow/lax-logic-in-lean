/-
# The crown, read syntactically

The crown of the dichotomy decides the SEMANTIC `PLL`
(`FRJ.PLL A := ∀ K : Kripke, K.valid A`, validity in every finite rooted
constraint model of `FRJ/Basic.lean`).  This file connects it to
natural-deduction provability, `Nonempty (LaxND [] φ)`, in both
directions, without choice:

    LaxND ⊢ φ  ⟹  PLL (ofPLL φ)        `FRJ.Bridge.valid_of_derivable`
    PLL (ofPLL φ)  ⟹  LaxND ⊢ φ         this file: PLL ⟹ no FRJW disproof
                                          (`soundnessW`) ⟹ `Gbu◯` proof
                                          (`gbuw_complete`) ⟹ `LaxND`
                                          (`laxOfR`, wip/gbu_laxnd.lean)

Two corollaries follow at once: natural-deduction provability is
decidable by the same procedure (`decideLaxND`), and PLL has the finite
POSET model property (validity over `FRJ.Kripke`, whose order is
antisymmetric, already characterises theoremhood), which the filtration
proof of `finite_model_property` does not give, its models being
preorders.
-/
import wip.gbu_frjw_saturate
import wip.gbu_laxnd

namespace FRJ.Gbu.W

open PLLND FRJ

/-- **The syntactic bridge**: semantic validity over the FRJ models
yields a natural deduction derivation. -/
theorem laxND_of_PLL {φ : PLLFormula} (h : PLL (ofPLL φ)) :
    Nonempty (LaxND [] φ) :=
  have hnd : ¬ DisprovableW (ofPLL φ) := fun hd => soundnessW hd h
  have hp : ProvableGbuC (ofPLL φ) := gbuw_complete hnd
  (toPLL_ofPLL φ) ▸ laxND_of_provableGbuC hp

/-- Semantic `PLL` over the FRJ models coincides with `LaxND` provability. -/
theorem PLL_iff_laxND {φ : PLLFormula} :
    PLL (ofPLL φ) ↔ Nonempty (LaxND [] φ) :=
  ⟨laxND_of_PLL, fun ⟨p⟩ K => valid_of_derivable p K⟩

/-- The same, from the FRJ side of the syntax. -/
theorem PLL_iff_laxND' {A : Form} : PLL A ↔ Nonempty (LaxND [] (toPLL A)) := by
  have h := @PLL_iff_laxND (toPLL A)
  rwa [ofPLL_toPLL] at h

/-- **Finite poset model property**: a formula is a theorem of PLL iff it is
valid in every finite rooted POSET constraint model (every `FRJ.Kripke`). -/
theorem finite_poset_model_property {φ : PLLFormula} :
    Nonempty (LaxND [] φ) ↔ ∀ K : Kripke, K.valid (ofPLL φ) :=
  PLL_iff_laxND.symm

/-- **Natural-deduction provability is decidable**, by the crown's
procedure transported along the bridge. -/
def decideLaxND (φ : PLLFormula) : Decidable (Nonempty (LaxND [] φ)) :=
  @decidable_of_iff _ _ PLL_iff_laxND (decidePLL (ofPLL φ))

/-! ## Pins -/

/-- info: 'FRJ.Gbu.W.laxND_of_PLL' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms laxND_of_PLL

/-- info: 'FRJ.Gbu.W.PLL_iff_laxND' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PLL_iff_laxND

/-- info: 'FRJ.Gbu.W.finite_poset_model_property' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms finite_poset_model_property

/-- info: 'FRJ.Gbu.W.decideLaxND' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms decideLaxND

end FRJ.Gbu.W
