import LaxLogic.PLL.SubTab.Sound
import LaxLogic.PLL.Semantics.CountermodelEmit
import LJF.OCheckDeriv

/-!
# The decider's soundness statements for `fincm` and `ljfo`

2026-10-27, F0 re-implementation plan step 4
(`docs/engine-adoption-statements.md` §2.2, §2.4 and §9; status in
`docs/f0-step4-STATUS.md`).  Statements first (gate G2, lean-certify R10):
each is a `Prop`, proved in `Harness/Tools.lean`.

The specification is the subframe tableau's (decisions M1 and M9), not a
second constant:

    PLLND.SubTab.Holds φ := Nonempty ([] ⊢ φ)          (LaxLogic/PLL/SubTab/Sound.lean)

Both certificates are Boolean-checked data, judged by a structurally
recursive checker.

* `FincmNoSound`, the `fincm` disprover: a finite constraint model `M` with a
  world `w` that the checker accepts against `⊢ φ` refutes `φ`.

      FinCM.checkB M w [] φ = true  →  Holds φ → False

  Expected proof: `FinCM.not_provable_of_check` at `Γ := []`, whose
  conclusion `[] ⊬ φ` is `¬ Nonempty ([] ⊢ φ)`.

* `LjfoYesSound`, the `ljfo` prover: a derivation tree that `checkDeriv`
  accepts at the LJF◯ goal of `⊢ φ` proves `φ`.

      checkDeriv (decideSeq [] φ) t = true  →  Holds φ

  Expected proof: `LJFO.laxND_of_checkDeriv` at `Γ := []`.

* `HoldsImpIff`, the way a one-hypothesis question (the F0 store's base
  facts) is asked of the formula-level decider: the deduction theorem at the
  empty context.

      Nonempty ([φ] ⊢ ψ)  ↔  Holds (φ ↠ ψ)

  Expected proof: `PLLND.deduction_iff` at `Γ := []`.
-/

open PLLND

namespace PLLDecider

/-- **Statement** (`fincm`): a finite constraint model accepted by
`FinCM.checkB` against `⊢ φ` at some world refutes `Holds φ`. -/
def FincmNoSound : Prop :=
  ∀ (φ : PLLFormula) (M : FinCM) (w : Nat),
    FinCM.checkB M w [] φ = true → SubTab.Holds φ → False

/-- **Statement** (`ljfo`): an LJF◯ derivation tree accepted by `checkDeriv`
at the goal `decideSeq [] φ` proves `Holds φ`. -/
def LjfoYesSound : Prop :=
  ∀ (φ : PLLFormula) (t : LJFO.DerivTree),
    LJFO.checkDeriv (LJFO.decideSeq [] φ) t = true → SubTab.Holds φ

/-- **Statement** (one-hypothesis questions): `[φ] ⊢ ψ` is decided as the
formula `φ ↠ ψ`. -/
def HoldsImpIff : Prop :=
  ∀ φ ψ : PLLFormula, Nonempty ([φ] ⊢ ψ) ↔ SubTab.Holds (φ ↠ ψ)

end PLLDecider
