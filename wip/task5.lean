/-
# Task #5, settled: `◯¬◯⊥ ⊢ ◯⊥ ∨ ¬◯⊥` is NOT derivable in PLL

The sequent has been open in the repo task list since before the FRJ work.  It is
REFUTED, and the certificate already existed in the RN(◯,{}) development under
dictionary numbering: it is literally `[q5] ⊢ q4` of `wip/rnDict.lean`, where

    q0 = ⊥        q2 = ◯⊥              q3 = ◯⊥ ⊃ ⊥ = ¬◯⊥
    q4 = q2 ∨ q3 = ◯⊥ ∨ ¬◯⊥            q5 = ◯q3   = ◯¬◯⊥

This file restates the result in explicit formulas rather than dictionary indices,
so it can be quoted without decoding, and re-pins the axioms.

The refutation is by `RNC.rnc_ref_5_4` (`wip/rncCert.lean`), a PCLL countermodel
checked by `not_derivU_of_checkConf`, transferred to PLL along `nle_of_rnc`
(`wip/overlap.lean`): a PCLL refutation is a fortiori a PLL refutation.

The countermodel, four worlds, `Rᵢ` drawn upward so `w₃` is the root:

    W       = {w₀, w₁, w₂, w₃}
    Rᵢ      = refl ∪ {(1,0), (2,0), (3,0), (3,1), (3,2)}
    Rₘ      = refl ∪ {(2,0), (3,1)}
    F       = {w₀}                       (no atoms — this is the closed fragment)

    ⊥          holds at {w₀}
    ◯⊥         holds at {w₀, w₂}
    ¬◯⊥        holds at {w₀, w₁}
    ◯¬◯⊥       holds at {w₀, w₁, w₂, w₃}   — in particular at the root
    ◯⊥ ∨ ¬◯⊥   holds at {w₀, w₁, w₂}       — fails at the root

Every `Rᵢ`-successor of `w₃` reaches, modally, some world satisfying `¬◯⊥`, which is
all `◯` demands; but `w₃` lies below a world where `◯⊥` holds (`w₂`) and a world
where `¬◯⊥` holds (`w₁`), so no single disjunct is forced there.  A failure of the
disjunction property for a `◯` whose witness world is not unique.

Independent second certificate: `RNSep.sep_1_8 : ¬ Interd q1 q8` (`wip/rnSep.lean`),
where `q1 = ⊤` and `q8 = q5 ⊃ q4` is the implication form of this very sequent — a
different model and a different checker (`FinCM.not_provable_of_check`).

Neither certificate depends on the round-1 or round-2 dictionary being sound (it is
not: `rnDict15`/`rnDict16` carry `sorryAx`, and 83 round-2 entries are certified
false).  Both are standalone theorems in sorry-free files; only the *definitions*
`q0`–`q5` are used here, and those are unfolded explicitly below.
-/
import wip.overlap

namespace PLLND
namespace Task5

open PLLFormula SemUI PLLND.SemUI.RND

/-- `◯⊥`. -/
abbrev circBot : PLLFormula := .somehow .falsePLL

/-- `¬◯⊥`, i.e. `◯⊥ ⊃ ⊥`. -/
abbrev nCircBot : PLLFormula := .ifThen circBot .falsePLL

/-- The dictionary entries really are the formulas claimed. -/
example : q5 = .somehow nCircBot := rfl
example : q4 = .or circBot nCircBot := rfl

/-- **Task #5, REFUTED.**

    ◯¬◯⊥  ⊬  ◯⊥ ∨ ¬◯⊥

`⊬` is the notation of `LaxLogic/PLLNDCore.lean`, and unfolds to
`¬ Nonempty (LaxND [◯¬◯⊥] (◯⊥ ∨ ¬◯⊥))`; since `Deriv Γ φ = Nonempty (LaxND Γ φ)`
by definition, the semantic-fragment spelling `¬ SemUI.Deriv …` and the
natural-deduction one are the SAME statement, and this single theorem carries
both.  (They were two theorems until the `⊬` migration made the types
literally equal.) -/
theorem not_deriv_circ_nCircBot :
    [.somehow nCircBot] ⊬ .or circBot nCircBot :=
  RNEmbed.nle_of_rnc RNC.rnc_ref_5_4

-- Displays in the `⊬` notation, not as `¬ Nonempty (LaxND …)`:
#check @not_deriv_circ_nCircBot

end Task5
end PLLND

#print axioms PLLND.Task5.not_deriv_circ_nCircBot
