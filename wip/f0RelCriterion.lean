import wip.f0NestPLL
import Meta.Audit

/-!
# The relative criterion for a faithful copy of PLL in `[ξ, ζ]`

Matthew, 2026-11-02 (approved via the LaxLogic manager): "a kind of sandwich
result ... especially if true".  For PLL formulas `ξ`, `ζ` (open or closed)
with `[ξ] ⊢ ζ` and a fresh renaming `ρ`, the conjecture is

    FreeInPLL ξ ζ (coreGen ξ ζ ρ)   ⟺   [ζ] ⊬ ◯ξ ↠ ξ   ∧   [ζ] ⊬ (◯ξ ↠ ξ) ↠ ξ.

Here `coreGen ξ ζ ρ p = (ρ p ∨ ξ) ∧ ζ` and `rel ξ ζ y` is the interval
translation (`⊥ ↦ ξ`, `p ↦ y p`, `A → B ↦ (rel A ↠ rel B) ∧ ζ`,
`◯A ↦ ◯(rel A) ∧ ζ`).  A formula `ξ` is *stable* when `◯ξ ⊣⊢ ξ`; the first
clause says that `ξ` is not stable relative to `ζ`.  It would generalise
`Endpoints.baseCriterion` (closed `ξ`, `ζ = ⊤`) and `NestPLL.coreLemmaPLL`
(◯-free `ξ`, `ζ`).

## The statements (Stage 1, committed before any proof, METHOD.md §1)

    (R0) RelClauses ξ ζ :     [ζ] ⊬ ◯ξ ↠ ξ  ∧  [ζ] ⊬ (◯ξ ↠ ξ) ↠ ξ
    (R1) RelNecessary :       FreeInPLL ξ ζ x  ⟹  RelClauses ξ ζ
    (R2) RelSufficient :      [ξ] ⊢ ζ,  RelClauses ξ ζ,  Fresh ρ ξ ζ  ⟹  FreeInPLL ξ ζ (coreGen ξ ζ ρ)
    (R3) RelCriterion :       [ξ] ⊢ ζ,  Fresh ρ ξ ζ  ⟹  (FreeInPLL ξ ζ (coreGen ξ ζ ρ) ⟺ RelClauses ξ ζ)

Corollaries of (R3), each stated on its own:

    ClausesStrict :        RelClauses ξ ζ  ⟹  [ζ] ⊬ ξ  ∧  [ζ] ⊬ ◯ξ
    ClausesBoxFree :       ξ, ζ ◯-free  ⟹  (RelClauses ξ ζ ⟺ [ζ] ⊬ ξ)
    RelCriterionBoxFree :  (R3) for ◯-free ξ, ζ          (the form of coreLemmaPLL)
    RelCriterionTop :      (R3) at ζ = ⊤, every ξ        (closed ξ: the form of baseCriterion)
    RelClausesMono :       [ζ′] ⊢ ζ,  RelClauses ξ ζ  ⟹  RelClauses ξ ζ′

Transport (R4), `gR = relB σ³⊥ xr`:

    RelMain :     a, b, x variable-free,  FreeInPLL a b x,  [ξ] ⊢ ζ,  RelClauses ξ ζ
                    ⟹  FreePLLIn (rel a b x ξ) (rel a b x ζ)
    RelInGR :     [ξ] ⊢ ζ,  RelClauses ξ ζ  ⟹  FreePLLIn (gR ξ) (gR ζ)
    RelNestAll :  the tower of NestPLL.towerP with  ∀ d, [ξ_d] ⊢ ζ_d ∧ RelClauses ξ_d ζ_d
                    ⟹  the conclusions of NestPLL.NestAllPLL at every depth

Weakenings to screen (expected REFUTED):

    RelSufficientFirst :   (R2) with the first clause only    (witness ξ = ¬◯⊥, ζ = ⊤)
    RelSufficientSecond :  (R2) with the second clause only   (witness ξ = ◯p, ζ = ⊤)

Added at Stage 1 from the pen refutation stage (the brief's route checked
before any cell; see the status note):

    RelSufficientDisj :    (R2) with the single clause  [ζ] ⊬ (◯ξ ↠ ξ) ∨ ((◯ξ ↠ ξ) ↠ ξ)
    RelCopyNecessary :     FreeInPLL ξ ζ x  ⟹  TopAvoid ξ ζ
                             (TopAvoid ξ ζ :  ∀ C closed,  [ζ] ⊢ C[⊥ := ξ]  ⟹  ⊢ C)
    RelCopyCriterion :     [ξ] ⊢ ζ,  Fresh ρ ξ ζ  ⟹  (FreeInPLL ξ ζ (coreGen ξ ζ ρ) ⟺ TopAvoid ξ ζ)

Status of every statement at Stage 1: OPEN (statements only, no theorem, no
`sorry`).  Pen expectation recorded in the status note: (R2) fails at
`ξ = ⊥`, `ζ = t3` (closed `C = t3`) and at a ◯-free top `ζ = p ∨ ¬p`.

Status note: `wip/f0RelCriterion-STATUS.md`.
-/

set_option autoImplicit false

open PLLFormula

namespace PLLND
namespace F0
namespace RelCrit

open SemUI Sig FreeHAn Base3 FreePLL MovingTop
open Interval (rel FreeInPLL topF Fresh coreGen nestGen freshRen ICopy)
open NestPLL (FreePLLIn towerP)
open PLLND.LaxInfinite (atomFree)

/-! ## The statements -/

/-- `◯ξ ↠ ξ`: `ξ` is stable exactly when this is derivable. -/
def stab (ξ : PLLFormula) : PLLFormula := (PLLFormula.somehow ξ).ifThen ξ

/-- `(◯ξ ↠ ξ) ↠ ξ`. -/
def stab2 (ξ : PLLFormula) : PLLFormula := (stab ξ).ifThen ξ

/-- **(R0) The two clauses**, relative to the top `ζ`. -/
def RelClauses (ξ ζ : PLLFormula) : Prop :=
  ¬ Deriv [ζ] (stab ξ) ∧ ¬ Deriv [ζ] (stab2 ξ)

/-- **(R1)** The clauses are necessary for any faithful copy in `[ξ, ζ]`. -/
def RelNecessary : Prop :=
  ∀ (ξ ζ : PLLFormula) (x : String → PLLFormula), FreeInPLL ξ ζ x → RelClauses ξ ζ

/-- **(R2)** The clauses suffice for the core generators. -/
def RelSufficient : Prop :=
  ∀ (ξ ζ : PLLFormula) (ρ : String → String), Deriv [ξ] ζ → RelClauses ξ ζ → Fresh ρ ξ ζ →
    FreeInPLL ξ ζ (coreGen ξ ζ ρ)

/-- **(R3) The relative criterion.** -/
def RelCriterion : Prop :=
  ∀ (ξ ζ : PLLFormula) (ρ : String → String), Deriv [ξ] ζ → Fresh ρ ξ ζ →
    (FreeInPLL ξ ζ (coreGen ξ ζ ρ) ↔ RelClauses ξ ζ)

/-! ### Corollaries of (R3), stated on their own -/

/-- The clauses imply `[ζ] ⊬ ξ` and `[ζ] ⊬ ◯ξ`. -/
def ClausesStrict : Prop :=
  ∀ ξ ζ : PLLFormula, RelClauses ξ ζ → ¬ Deriv [ζ] ξ ∧ ¬ Deriv [ζ] (.somehow ξ)

/-- For ◯-free `ξ`, `ζ` the clauses say `[ζ] ⊬ ξ`. -/
def ClausesBoxFree : Prop :=
  ∀ ξ ζ : PLLFormula, boxFree ξ = true → boxFree ζ = true → (RelClauses ξ ζ ↔ ¬ Deriv [ζ] ξ)

/-- (R3) for ◯-free `ξ`, `ζ` (the form of `coreLemmaPLL`). -/
def RelCriterionBoxFree : Prop :=
  ∀ (ξ ζ : PLLFormula) (ρ : String → String), boxFree ξ = true → boxFree ζ = true →
    Deriv [ξ] ζ → Fresh ρ ξ ζ → (FreeInPLL ξ ζ (coreGen ξ ζ ρ) ↔ RelClauses ξ ζ)

/-- (R3) at `ζ = ⊤`, every `ξ`, open or closed (closed `ξ`: the form of
`baseCriterion`). -/
def RelCriterionTop : Prop :=
  ∀ (ξ : PLLFormula) (ρ : String → String), Fresh ρ ξ topF →
    (FreeInPLL ξ topF (coreGen ξ topF ρ) ↔ RelClauses ξ topF)

/-- The clauses are inherited by every larger top. -/
def RelClausesMono : Prop :=
  ∀ ξ ζ ζ' : PLLFormula, Deriv [ζ'] ζ → RelClauses ξ ζ → RelClauses ξ ζ'

/-! ### (R4) Transport -/

/-- **(R4)** Inside a faithful copy with variable-free data. -/
def RelMain : Prop :=
  ∀ (a b : PLLFormula) (x : String → PLLFormula) (ξ ζ : PLLFormula),
    atomFree a = true → atomFree b = true → (∀ p, atomFree (x p) = true) → FreeInPLL a b x →
    Deriv [ξ] ζ → RelClauses ξ ζ → FreePLLIn (rel a b x ξ) (rel a b x ζ)

/-- **(R4)** In the coordinates of the readers' copy. -/
def RelInGR : Prop :=
  ∀ ξ ζ : PLLFormula, Deriv [ξ] ζ → RelClauses ξ ζ → FreePLLIn (gR ξ) (gR ζ)

/-- The tower hypothesis with the clauses at each depth. -/
def RelTowerHyp (ξs ζs : Nat → PLLFormula) : Prop :=
  ∀ d, Deriv [ξs d] (ζs d) ∧ RelClauses (ξs d) (ζs d)

/-- **(R4)** Every finite depth. -/
def RelNestAll : Prop :=
  ∀ ξs ζs : Nat → PLLFormula, RelTowerHyp ξs ζs → ∀ d : Nat,
    FreeInPLL (towerP ξs ζs d).a (towerP ξs ζs d).b (towerP ξs ζs d).x ∧
    (∀ p, atomFree ((towerP ξs ζs d).x p) = true) ∧
    ¬ Deriv [(towerP ξs ζs d).b] (towerP ξs ζs d).a ∧
    Deriv [(towerP ξs ζs d).a] (towerP ξs ζs (d + 1)).a ∧
    Deriv [(towerP ξs ζs (d + 1)).a] (towerP ξs ζs (d + 1)).b ∧
    Deriv [(towerP ξs ζs (d + 1)).b] (towerP ξs ζs d).b

/-! ### Weakenings -/

/-- (R2) with the first clause only. -/
def RelSufficientFirst : Prop :=
  ∀ (ξ ζ : PLLFormula) (ρ : String → String), Deriv [ξ] ζ → ¬ Deriv [ζ] (stab ξ) →
    Fresh ρ ξ ζ → FreeInPLL ξ ζ (coreGen ξ ζ ρ)

/-- (R2) with the second clause only. -/
def RelSufficientSecond : Prop :=
  ∀ (ξ ζ : PLLFormula) (ρ : String → String), Deriv [ξ] ζ → ¬ Deriv [ζ] (stab2 ξ) →
    Fresh ρ ξ ζ → FreeInPLL ξ ζ (coreGen ξ ζ ρ)

/-! ### Added at Stage 1 from the pen refutation stage -/

/-- (R2) with the single, stronger clause `[ζ] ⊬ (◯ξ ↠ ξ) ∨ ((◯ξ ↠ ξ) ↠ ξ)`. -/
def RelSufficientDisj : Prop :=
  ∀ (ξ ζ : PLLFormula) (ρ : String → String), Deriv [ξ] ζ →
    ¬ Deriv [ζ] ((stab ξ).or (stab2 ξ)) → Fresh ρ ξ ζ → FreeInPLL ξ ζ (coreGen ξ ζ ρ)

/-- Every closed instance is necessary: `TopAvoid ξ ζ`. -/
def RelCopyNecessary : Prop :=
  ∀ (ξ ζ : PLLFormula) (x : String → PLLFormula), FreeInPLL ξ ζ x → TopAvoid ξ ζ

/-- **The candidate exact criterion** (OPEN at Stage 1): the core copy of PLL is
faithful exactly when the closed part is. -/
def RelCopyCriterion : Prop :=
  ∀ (ξ ζ : PLLFormula) (ρ : String → String), Deriv [ξ] ζ → Fresh ρ ξ ζ →
    (FreeInPLL ξ ζ (coreGen ξ ζ ρ) ↔ TopAvoid ξ ζ)

end RelCrit
end F0
end PLLND
