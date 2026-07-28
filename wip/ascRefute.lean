import wip.cascadeBox
import LaxLogic.PLLSearchCmd

/-!
# `AmbGuardAscent` is FALSE — the interface refuted, kernel-checked

`wip/cascadeBox.lean` reduces the `◯`-involving low-budget descent to four
interface propositions.  This file refutes the first of them.

`AmbGuardAscent p S` asserts the one-step *ascent* of the existential
quantifier table at a freshly grown context, financed by the ambient table
at the ungrown context:

    Δ ⊢ E@(c+1)(Γ)   ⟹   E@c(X::Γ), Δ ⊢ E@(c+1)(X::Γ)      (X ∈ S, X ∉ Γ)

It was abstracted out of the three paired-implication growth arms, where the
box-free clone had financed the same step from the room-funded existential
half of its mutual pair.  It is **false at the budget floor**: with

    S = {◯p ⊃ r, r, ◯r ⊃ s, s},  Γ = [◯p ⊃ r],  X = ◯r ⊃ s,  c = 1,

the instance fails in the two-world infallible model `0 ⊑ 1`, `0 ⊳ 1` with
`r`, `s` true exactly at world `1` — the Kripke form of the countermodel the
algebraic battery first exhibited (3-chain, nucleus `j(0) = 0`, `j(x) = 2`,
valuation `r = s = 1`).  The failure is stable in the fuel (identical at
fuels 3, 4, 5) and confined to the floor (no failure at budget ≥ 2), which is
the signature of the low-budget wall itself.

**Consequence.**  The three growth arms of `oth_descent` that consume this
interface need a different treatment; the ascent cannot be assumed at the
grown context in the form stated.  What survives untouched: `oth_descent` and
`cascade_box` as *conditional* theorems, and the other three interfaces
(`GammaPairFloorA`, `GammaPairFloorBox`, `JumpPairFloor`), which the battery
supports.  `cascade_box_unconditional` is now known to rest on a false
hypothesis and must not be quoted as evidence for the kernel.
-/

open PLLFormula

namespace PLLND
namespace AscRefute

/-- The refuting space: the chained configuration of the battery. -/
def Sr : Finset PLLFormula :=
  {((prop "p").somehow).ifThen (prop "r"), prop "r",
   ((prop "r").somehow).ifThen (prop "s"), prop "s"}

/-- The context. -/
def Gr : List PLLFormula := [((prop "p").somehow).ifThen (prop "r")]

/-- The fresh space piece. -/
def Xr : PLLFormula := ((prop "r").somehow).ifThen (prop "s")

/-- The ambient existential table at the ungrown context. -/
def ambr : PLLFormula := itpE "p" Sr 4 2 Gr

/-- The existential table at the grown context, budget `1`. -/
def lowr : PLLFormula := itpE "p" Sr 3 1 (Xr :: Gr)

/-- The existential table at the grown context, budget `2` — the ascent's
target. -/
def hir : PLLFormula := itpE "p" Sr 3 2 (Xr :: Gr)

/-- The refuting model: two worlds `0 ⊑ 1` with `0 ⊳ 1`, no fallible world,
`r` and `s` forced exactly at world `1`. -/
def Mr : FinCM := ⟨2, [(0, 1)], [(0, 1)], [], [(1, "r"), (1, "s")]⟩

/-- The ascent instance fails in `Mr` at world `0`. -/
theorem check_fails : FinCM.checkB Mr 0 [lowr, ambr] hir = true := by decide

/-- The ascent instance is underivable. -/
theorem not_derivable : ¬ G4c [lowr, ambr] hir := fun h =>
  FinCM.not_provable_of_check check_fails (G4c.equiv_nd.mp h)

/-- **`AmbGuardAscent` is false.**  Instantiate at `fl = 3`, `c = 1`, the
configuration above, with the ambient itself as the deriving context. -/
theorem not_ambGuardAscent : ¬ AmbGuardAscent "p" Sr := by
  intro h
  exact not_derivable
    (h 3 1 Gr Xr [ambr] (by decide) (by decide) (by decide)
      (G4c.identity_mem (List.mem_cons_self ..)))

end AscRefute
end PLLND

/-! ### Axiom audit -/

/-- info: 'PLLND.AscRefute.not_ambGuardAscent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.AscRefute.not_ambGuardAscent
