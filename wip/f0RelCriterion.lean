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

## Results (Stage 3)

All pins `[propext, Quot.sound]`; no `Classical.choice`, no `sorry`, no
`native_decide`.

**REFUTED**: (R2) `not_relSufficient`, (R3) `not_relCriterion`, at

    ξ = ⊥,  ζ = t3 = ◯⊥ ∨ ¬◯⊥:   RelClauses ⊥ t3,  but  [t3] ⊢ t3[⊥ := ⊥]  and  ⊬ t3,

so `[⊥, t3]` carries no faithful copy of PLL for any generators.  Also REFUTED:
(R2) for ◯-free `ζ` (`ζ = p ∨ ¬p`, `ξ = (p ∧ ¬◯⊥) ∨ (¬p ∧ ◯⊥)`), for ◯-free `ξ`,
for closed `ξ`, `ζ`; the one-clause form (`ξ = ⊥`, `ζ = t6`); (R4) `RelMain`,
`RelInGR`, `RelNestAll`; the two weakenings; `RelClausesMono` (its inclusion
was the wrong way round; `RelClausesUp` is the intended statement).

**PROVED**: (R1) `relNecessary`; `clausesStrict`, `clausesBoxFree`,
`relCriterionBoxFree`, `relClausesUp`, `relCopyNecessary`; and the criterion
at the top `⊤`, for every `ξ`, open or closed (`relCriterionTop`):

    FreeInPLL ξ ⊤ (coreGen ξ ⊤ ρ)   ⟺   ⊬ ◯ξ ↠ ξ   ∧   ⊬ (◯ξ ↠ ξ) ↠ ξ,

which gives back `baseCriterion` at closed `ξ` (`selfTopIff`).  The corrected
transport (`goodCore`, `goodMain`, `goodInGR`, `goodNestAll`) holds for the
pairs `GoodPair ξ ζ`: ◯-free with `[ζ] ⊬ ξ`, or `ζ = ⊤` with the clauses.

**OPEN**: `RelCopyCriterion`, direction `⟸` (it contains the OPEN
`Endpoints.CopySelf`).

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

/-! ## Stage 2: the designed cells (refutation stage, CLAUDE.md rules 7 and 9)

Read off the structure of the rules; no sweep, no decider run.  Countermodels
are `SubCM` tables judged by `SubTab.no` (`decide +kernel`); derivations are
semantic (`Interval.deriv_of_sem`).  `p = ""`, `q = "\x00"`; the renaming of the
copy cells is `Interval.Cells.ρc1` (`p ↦ "\x01"`, `q ↦ "\x02"`).

* (A) `ξ = ¬◯⊥` under `ζ ∈ {⊤, ¬◯⊥ ∨ p, t6}`: the first clause holds, the
  second fails (`⊢ (◯¬◯⊥ ↠ ¬◯⊥) ↠ ¬◯⊥`), and there is no copy (`C = ¬¬◯⊥`).
* (B) the weakenings: first clause only, REFUTED at `ξ = ¬◯⊥`, `ζ = ⊤`; second
  clause only, REFUTED at `ξ = ◯p`, `ζ = ⊤`.
* (C) non-stable `ξ` with `◯` where the clauses hold: `ξ = t3` under `ζ = ⊤`
  and `ζ = t6`, and the open `ξ = ◯p ∨ ¬◯p` under `ζ = ⊤`; the core copy
  separates `C = ◯q → q` and `O3` in all three.
* (D) the counterexamples to (R2): `ξ = ⊥`, `ζ = t3`; `ξ = ⊥`, `ζ = t6` (also
  against the one-clause form); `ζ = p ∨ ¬p`, `ξ = (p ∧ ¬◯⊥) ∨ (¬p ∧ ◯⊥)`.
* (E) a pair whose clauses hold at `⊤` and fail relative to `ζ`
  (`ξ = ⊥`, `ζ = ◯⊥`); the opposite kind of pair cannot exist (monotonicity,
  stage 3). -/

namespace PLLND
namespace F0
namespace RelCrit

open SemUI Sig FreeHAn Base3 FreePLL MovingTop
open Interval (rel FreeInPLL topF Fresh coreGen nestGen freshRen ICopy)
open NestPLL (FreePLLIn towerP)
open PLLND.LaxInfinite (atomFree)

section Cells

set_option maxRecDepth 100000

/-! ### Tools for the cells -/

/-- A table refuting `ζ ↠ φ` gives `[ζ] ⊬ φ`. -/
theorem ndc {ζ φ : PLLFormula} (m : SubTab.SubCM) (h : m.refutes (ζ.ifThen φ) = true) :
    ¬ Deriv [ζ] φ :=
  fun hd => SubTab.SubCM.refutes_sound h (Deriv.impIntro hd)

/-- Weakening a theorem into the context `[ζ]`. -/
theorem wk {ζ φ : PLLFormula} (h : Deriv [] φ) : Deriv [ζ] φ :=
  Deriv.rename (fun _ hx => absurd hx List.not_mem_nil) h

/-- **The closed-part necessary condition** (`Endpoints.necClosed`): a closed
non-theorem `C` with `[ζ] ⊢ C[⊥ := ξ]` leaves `[ξ, ζ]` without a faithful copy of
PLL, whatever the generators. -/
theorem no_copy {ξ ζ C : PLLFormula} (hC : atomFree C = true) (hnd : ¬ Deriv [] C)
    (hd : Deriv [ζ] (subBot ξ C)) (x : String → PLLFormula) : ¬ FreeInPLL ξ ζ x := fun hF =>
  Endpoints.necClosed ξ ζ (Deriv.cutHead (hF.1 "") (hF.2.1 "")) (Endpoints.copy_of_free hF) C hC
    hnd hd

/-- The atom `q = "\x00"` and the target `◯q → q`. -/
def Cq : PLLFormula := (PLLFormula.somehow qA).ifThen qA

/-- `K3` with the atoms renamed by `ρc1`. -/
def K3r : SubTab.SubCM :=
  { n := 3, root := 0, le := [[true, true, true], [false, true, false], [false, false, true]],
    S := [false, true, true], val := [[], ["\x01"], ["\x02"]] }

/-- The renamed atoms, true at the attached worlds. -/
def rAts : List String := ["\x01", "\x02"]

/-- The core translation of a copy cell. -/
abbrev relc (ξ ζ : PLLFormula) : PLLFormula → PLLFormula := rel ξ ζ (coreGen ξ ζ Interval.Cells.ρc1)

/-- A copy cell: `[rel ⊤] ⊬ rel C`. -/
def CopyCell (ξ ζ C : PLLFormula) : Prop := ¬ Deriv [relc ξ ζ topF] (relc ξ ζ C)

/-! ### (A) `ξ = ¬◯⊥` -/

/-- One world outside `S`, `p` true. -/
def K0p : SubTab.SubCM := { n := 1, root := 0, le := [[true]], S := [false], val := [[""]] }

/-- `ζ = ¬◯⊥ ∨ p`. -/
def zNeP : PLLFormula := ne.or pA

theorem a_top_c1 : ¬ Deriv [topF] (stab ne) := ndc K0 (by decide +kernel)

theorem a_neP_c1 : ¬ Deriv [zNeP] (stab ne) := ndc K0p (by decide +kernel)

theorem a_t6_c1 : ¬ Deriv [t6] (stab ne) := ndc K0 (by decide +kernel)

/-- `⊢ (◯¬◯⊥ ↠ ¬◯⊥) ↠ ¬◯⊥`: the second clause fails under every top. -/
theorem a_c2 (ζ : PLLFormula) : Deriv [ζ] (stab2 ne) := wk Endpoints.d_ne_nne

/-- **(A), the direct cell**: no copy in `[¬◯⊥, ζ]`, any top, any generators
(`C = ¬¬◯⊥`). -/
theorem a_no_copy (ζ : PLLFormula) (x : String → PLLFormula) : ¬ FreeInPLL ne ζ x :=
  no_copy rfl Endpoints.nd_nne (a_c2 ζ) x

/-! ### (B) the weakenings -/

/-- **REFUTED: the first clause alone** (`ξ = ¬◯⊥`, `ζ = ⊤`). -/
theorem not_relSufficientFirst : ¬ RelSufficientFirst := fun h =>
  a_no_copy topF _ (h ne topF (freshRen ne topF) (MovingTop.le_top _) a_top_c1
    (Interval.fresh_freshRen _ _))

/-- `[⊤] ⊬ (◯◯p ↠ ◯p) ↠ ◯p` (one world in `S`). -/
theorem b_c2 : ¬ Deriv [topF] (stab2 (.somehow pA)) := ndc Endpoints.KS (by decide +kernel)

/-- `⊢ ◯◯p ↠ ◯p`: the first clause fails. -/
theorem b_c1 : Deriv [topF] (stab (.somehow pA)) :=
  wk (Deriv.impIntro (Deriv.rename (fun z hz => by rw [List.mem_singleton.mp hz]; exact .head _)
    (NestPLL.box_box pA)))

/-- **REFUTED: the second clause alone** (`ξ = ◯p`, `ζ = ⊤`). -/
theorem not_relSufficientSecond : ¬ RelSufficientSecond := fun h =>
  NestPLL.not_freeInPLL_of_fixed (NestPLL.box_box pA)
    (h (.somehow pA) topF (freshRen _ _) (MovingTop.le_top _) b_c2 (Interval.fresh_freshRen _ _))

/-! ### (C) copies where the clauses hold -/

theorem c_t3_top : RelClauses t3 topF :=
  ⟨fun h => Endpoints.baseYes_t3.1 (of_top h), fun h => Endpoints.baseYes_t3.2 (of_top h)⟩

theorem c_t3_t6 : RelClauses t3 t6 :=
  ⟨ndc Tfork (by decide +kernel), ndc (extT Endpoints.KS []) (by decide +kernel)⟩

/-- `◯p ∨ ¬◯p`, open. -/
def xO2 : PLLFormula := O2

theorem c_O2_top : RelClauses xO2 topF :=
  ⟨ndc Tfork (by decide +kernel), ndc FreePLL.K2 (by decide +kernel)⟩

theorem c_t3_top_Cq : CopyCell t3 topF Cq := ndc (extT FreePLL.K1 rAts) (by decide +kernel)

theorem c_t3_top_O3 : CopyCell t3 topF O3 := ndc (extT K3r rAts) (by decide +kernel)

theorem c_t3_t6_Cq : CopyCell t3 t6 Cq := ndc (extT FreePLL.K1 rAts) (by decide +kernel)

theorem c_t3_t6_O3 : CopyCell t3 t6 O3 := ndc (extT K3r rAts) (by decide +kernel)

/-- The two-sided table for `Cq` over `ξ = ◯p ∨ ¬◯p`: the world of `K1` below
the strict successors of the `Tfork` root (`S`-top and non-`S` top). -/
def TOq : SubTab.SubCM :=
  { n := 3, root := 0, le := [[true, true, true], [false, true, false], [false, false, true]],
    S := [false, true, false], val := [[], rAts, rAts] }

/-- The two-sided table for `O3`: `K3r` below the strict successor of the `K2`
root (a non-`S` top). -/
def TO3 : SubTab.SubCM :=
  { n := 4, root := 0,
    le := [[true, true, true, true], [false, true, false, true], [false, false, true, true],
           [false, false, false, true]],
    S := [false, true, true, false], val := [[], ["\x01"], ["\x02"], rAts] }

theorem c_O2_top_Cq : CopyCell xO2 topF Cq := ndc TOq (by decide +kernel)

theorem c_O2_top_O3 : CopyCell xO2 topF O3 := ndc TO3 (by decide +kernel)

/-! ### (D) the counterexamples to (R2) -/

theorem d_t3_c1 : ¬ Deriv [t3] (stab .falsePLL) := ndc K0 (by decide +kernel)

theorem d_t3_c2 : ¬ Deriv [t3] (stab2 .falsePLL) := ndc Endpoints.KS (by decide +kernel)

/-- **(D1) `ξ = ⊥`, `ζ = t3`: the clauses hold.** -/
theorem d_t3_clauses : RelClauses .falsePLL t3 := ⟨d_t3_c1, d_t3_c2⟩

/-- **(D1) but no copy**: `[t3] ⊢ t3[⊥ := ⊥]`, `⊬ t3`. -/
theorem d_t3_no_copy (x : String → PLLFormula) : ¬ FreeInPLL .falsePLL t3 x :=
  no_copy rfl nd_t3 (Deriv.iden (.head _)) x

/-- **(D2) `ξ = ⊥`, `ζ = t6`: even the one-clause form holds** (the root of
`Tfork`). -/
theorem d_t6_disj : ¬ Deriv [t6] ((stab .falsePLL).or (stab2 .falsePLL)) :=
  ndc Tfork (by decide +kernel)

theorem d_t6_clauses : RelClauses .falsePLL t6 :=
  ⟨fun h => d_t6_disj (Deriv.orIntro1 h), fun h => d_t6_disj (Deriv.orIntro2 h)⟩

/-- **(D2) but no copy** (`C = t6`). -/
theorem d_t6_no_copy (x : String → PLLFormula) : ¬ FreeInPLL .falsePLL t6 x :=
  no_copy rfl nd_t6 (Deriv.iden (.head _)) x

/-- `¬p`. -/
def np : PLLFormula := pA.ifThen .falsePLL

/-- **(D3)** the ◯-free top `ζ = p ∨ ¬p`. -/
def z3 : PLLFormula := pA.or np

/-- **(D3)** `ξ = (p ∧ ¬◯⊥) ∨ (¬p ∧ ◯⊥)`. -/
def x3 : PLLFormula := (pA.and ne).or (np.and e)

theorem d3_le : Deriv [x3] z3 := Interval.deriv_of_sem fun _ _ _ h =>
  h.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)

/-- The first clause, on the `p` side (one world outside `S`, `p` true). -/
theorem d3_c1 : ¬ Deriv [z3] (stab x3) := ndc K0p (by decide +kernel)

/-- The second clause, on the `¬p` side (one world in `S`). -/
theorem d3_c2 : ¬ Deriv [z3] (stab2 x3) := ndc Endpoints.KS (by decide +kernel)

theorem d3_clauses : RelClauses x3 z3 := ⟨d3_c1, d3_c2⟩

/-- `⊬ ¬◯⊥ ∨ ¬¬◯⊥` (the root of `Tfork`). -/
theorem nd_ne_nne : ¬ Deriv [] (ne.or Endpoints.nne) := SubTab.no.verdict _ Tfork

/-- `[p ∨ ¬p] ⊢ (◯ξ ↠ ξ) ∨ ((◯ξ ↠ ξ) ↠ ξ)` for `ξ = (p ∧ ¬◯⊥) ∨ (¬p ∧ ◯⊥)`:
on the `p` side the second disjunct, on the `¬p` side the first. -/
theorem d3_disj : Deriv [z3] (subBot x3 (ne.or Endpoints.nne)) := by
  refine Interval.deriv_of_sem fun M _ v hv => ?_
  rcases hv with hp | hnp
  · -- the `p` side: every world above forcing `◯ξ ↠ ξ` forces `¬◯⊥`
    refine Or.inr fun u hvu hst => Or.inl ⟨M.hered hvu hp, fun u' huu' he => ?_⟩
    have hbox : M.force u' (.somehow x3) := fun s hs hS => False.elim (he s hs hS)
    rcases hst u' huu' hbox with h | h
    · exact h.2 u' (M.refl u') he
    · exact h.1 u' (M.refl u') (M.hered (M.trans hvu huu') hp)
  · -- the `¬p` side: every world above forcing `◯ξ` forces `◯⊥`
    refine Or.inl fun u hvu hbox => Or.inr ⟨fun u' huu' hp' => hnp u' (M.trans hvu huu') hp',
      fun s hus hS => ?_⟩
    rcases hbox s hus hS with h | h
    · exact hnp s (M.trans hvu hus) h.1
    · exact h.2 s (M.refl s) hS

/-- **(D3) but no copy** (`C = ¬◯⊥ ∨ ¬¬◯⊥`). -/
theorem d3_no_copy (x : String → PLLFormula) : ¬ FreeInPLL x3 z3 x :=
  no_copy rfl nd_ne_nne d3_disj x

/-! ### (E) clauses at `⊤` but not relative to `ζ` -/

theorem e_top : RelClauses .falsePLL topF :=
  ⟨fun h => Endpoints.nd_ne (of_top h), fun h => Endpoints.nd_nne (of_top h)⟩

/-- `[◯⊥] ⊢ ¬¬◯⊥`. -/
theorem e_box : Deriv [e] (stab2 .falsePLL) :=
  Deriv.impIntro (Deriv.impElim (Deriv.iden (.head _)) (Deriv.iden (.tail _ (.head _))))

theorem e_not : ¬ RelClauses .falsePLL e := fun h => h.2 e_box

/-! ### The gates, watched failing -/

/-- The checker rejects every table on a derivable cell: the copy tables on the
image of the theorem `◯◯p → ◯p`, the clause tables on `[t3] ⊢ t3`, `[◯⊥] ⊢ ¬¬◯⊥`,
and the (D3) clause tables on its derivable disjunction. -/
theorem gate_cells :
    TOq.refutes ((relc xO2 topF topF).ifThen (relc xO2 topF NestPLL.Cells.CP)) = false ∧
    TO3.refutes ((relc xO2 topF topF).ifThen (relc xO2 topF NestPLL.Cells.CP)) = false ∧
    (extT K3r rAts).refutes ((relc t3 t6 topF).ifThen (relc t3 t6 NestPLL.Cells.CP)) = false ∧
    Tfork.refutes (t3.ifThen t3) = false ∧
    Endpoints.KS.refutes (e.ifThen (stab2 .falsePLL)) = false ∧
    K0p.refutes (z3.ifThen (subBot x3 (ne.or Endpoints.nne))) = false ∧
    Endpoints.KS.refutes (z3.ifThen (subBot x3 (ne.or Endpoints.nne))) = false := by
  decide +kernel

end Cells

end RelCrit
end F0
end PLLND

/-! ## Axiom pins: stage 2 -/

#axioms_within PLLND.F0.RelCrit.no_copy [propext, Quot.sound]
#axioms_within PLLND.F0.RelCrit.a_top_c1 [propext, Quot.sound]
#axioms_within PLLND.F0.RelCrit.a_neP_c1 [propext, Quot.sound]
#axioms_within PLLND.F0.RelCrit.a_t6_c1 [propext, Quot.sound]
#axioms_within PLLND.F0.RelCrit.a_c2 [propext, Quot.sound]
#axioms_within PLLND.F0.RelCrit.a_no_copy [propext, Quot.sound]
#axioms_within PLLND.F0.RelCrit.not_relSufficientFirst [propext, Quot.sound]
#axioms_within PLLND.F0.RelCrit.b_c1 [propext, Quot.sound]
#axioms_within PLLND.F0.RelCrit.b_c2 [propext, Quot.sound]
#axioms_within PLLND.F0.RelCrit.not_relSufficientSecond [propext, Quot.sound]
#axioms_within PLLND.F0.RelCrit.c_t3_top [propext, Quot.sound]
#axioms_within PLLND.F0.RelCrit.c_t3_t6 [propext, Quot.sound]
#axioms_within PLLND.F0.RelCrit.c_O2_top [propext, Quot.sound]
#axioms_within PLLND.F0.RelCrit.c_t3_top_Cq [propext, Quot.sound]
#axioms_within PLLND.F0.RelCrit.c_t3_top_O3 [propext, Quot.sound]
#axioms_within PLLND.F0.RelCrit.c_t3_t6_Cq [propext, Quot.sound]
#axioms_within PLLND.F0.RelCrit.c_t3_t6_O3 [propext, Quot.sound]
#axioms_within PLLND.F0.RelCrit.c_O2_top_Cq [propext, Quot.sound]
#axioms_within PLLND.F0.RelCrit.c_O2_top_O3 [propext, Quot.sound]
#axioms_within PLLND.F0.RelCrit.d_t3_clauses [propext, Quot.sound]
#axioms_within PLLND.F0.RelCrit.d_t3_no_copy [propext, Quot.sound]
#axioms_within PLLND.F0.RelCrit.d_t6_disj [propext, Quot.sound]
#axioms_within PLLND.F0.RelCrit.d_t6_clauses [propext, Quot.sound]
#axioms_within PLLND.F0.RelCrit.d_t6_no_copy [propext, Quot.sound]
#axioms_within PLLND.F0.RelCrit.d3_le [propext, Quot.sound]
#axioms_within PLLND.F0.RelCrit.d3_clauses [propext, Quot.sound]
#axioms_within PLLND.F0.RelCrit.d3_disj [propext, Quot.sound]
#axioms_within PLLND.F0.RelCrit.d3_no_copy [propext, Quot.sound]
#axioms_within PLLND.F0.RelCrit.e_top [propext, Quot.sound]
#axioms_within PLLND.F0.RelCrit.e_not [propext, Quot.sound]
#axioms_within PLLND.F0.RelCrit.gate_cells [propext, Quot.sound]

/-! ## Stage 3: the proofs

**PROVED**: (R1) `relNecessary`; `clausesStrict`; `clausesBoxFree`;
`relCriterionBoxFree` (from `coreLemmaPLL`); **`relCriterionTop`**, the
criterion at `ζ = ⊤` for every `ξ`, open or closed, by the two-sided
construction with atoms (`TSA`); `relCopyNecessary`.

**REFUTED**: (R2) `not_relSufficient`, (R3) `not_relCriterion` (pair D1),
`not_relSufficientDisj` (D2), (R4) `not_relMain`, `not_relInGR`,
`not_relNestAll` (D1 transported), the two weakenings (stage 2), and
`not_relClausesMono`: the Stage 1 statement `RelClausesMono` had its top
inclusion the wrong way round; cell (E) refutes it, and the intended
statement is `RelClausesUp` (PROVED).

**Added at stage 3** (each stated as a `Prop` before its proof):

    RelClausesUp :          [ζ] ⊢ ζ′,  RelClauses ξ ζ  ⟹  RelClauses ξ ζ′
    SelfTopIff :            a closed  ⟹  (SelfStep a ⊤ ⟺ RelClauses a ⊤)        (the base criterion, again)
    RelSufficientBoxFreeTop :  (R2) for ◯-free ζ        REFUTED (D3)
    RelSufficientBoxFreeBot :  (R2) for ◯-free ξ        REFUTED (D1)
    RelSufficientClosed :      (R2) for closed ξ, ζ     REFUTED (D1)
    NestOfCore :   FreeInPLL a b x,  FreeInPLL ξ ζ y  ⟹  FreeInPLL (rel a b x ξ) (rel a b x ζ) (rel a b x ∘ y)
    GoodPair ξ ζ :  (ξ, ζ ◯-free ∧ [ξ] ⊢ ζ ∧ [ζ] ⊬ ξ)  ∨  (ζ = ⊤ ∧ RelClauses ξ ⊤)
    GoodCore :     GoodPair ξ ζ  ⟹  FreeInPLL ξ ζ (coreGen ξ ζ (freshRen ξ ζ))
    GoodMain, GoodInGR, GoodNestAll :  (R4) with GoodPair in place of [ξ] ⊢ ζ ∧ RelClauses ξ ζ

**OPEN**: `RelCopyCriterion`, direction `⟸` (at closed `ξ`, `ζ` it is the
OPEN `Endpoints.CopySelf`). -/

namespace PLLND
namespace F0
namespace RelCrit

open SemUI Sig FreeHAn Base3 FreePLL MovingTop
open Interval (rel FreeInPLL topF Fresh coreGen nestGen freshRen ICopy)
open NestPLL (FreePLLIn towerP)
open PLLND.LaxInfinite (atomFree)
open SubframeModel.CF (FinDec)

/-! ### Statements added at stage 3 -/

/-- The clauses pass to every larger top. -/
def RelClausesUp : Prop :=
  ∀ ξ ζ ζ' : PLLFormula, Deriv [ζ] ζ' → RelClauses ξ ζ → RelClauses ξ ζ'

/-- The base criterion in the language of the clauses. -/
def SelfTopIff : Prop :=
  ∀ a : PLLFormula, atomFree a = true → (Endpoints.SelfStep a topF ↔ RelClauses a topF)

/-- (R2) for a ◯-free top. -/
def RelSufficientBoxFreeTop : Prop :=
  ∀ (ξ ζ : PLLFormula) (ρ : String → String), boxFree ζ = true → Deriv [ξ] ζ →
    RelClauses ξ ζ → Fresh ρ ξ ζ → FreeInPLL ξ ζ (coreGen ξ ζ ρ)

/-- (R2) for a ◯-free bottom. -/
def RelSufficientBoxFreeBot : Prop :=
  ∀ (ξ ζ : PLLFormula) (ρ : String → String), boxFree ξ = true → Deriv [ξ] ζ →
    RelClauses ξ ζ → Fresh ρ ξ ζ → FreeInPLL ξ ζ (coreGen ξ ζ ρ)

/-- (R2) for closed endpoints. -/
def RelSufficientClosed : Prop :=
  ∀ (ξ ζ : PLLFormula) (ρ : String → String), atomFree ξ = true → atomFree ζ = true →
    Deriv [ξ] ζ → RelClauses ξ ζ → Fresh ρ ξ ζ → FreeInPLL ξ ζ (coreGen ξ ζ ρ)

/-- **Composition**: a faithful copy of PLL inside a faithful copy of PLL. -/
def NestOfCore : Prop :=
  ∀ (a b : PLLFormula) (x : String → PLLFormula) (ξ ζ : PLLFormula) (y : String → PLLFormula),
    FreeInPLL a b x → FreeInPLL ξ ζ y →
    FreeInPLL (rel a b x ξ) (rel a b x ζ) (fun p => rel a b x (y p))

/-- The pairs for which the core copy is PROVED here. -/
def GoodPair (ξ ζ : PLLFormula) : Prop :=
  (boxFree ξ = true ∧ boxFree ζ = true ∧ Deriv [ξ] ζ ∧ ¬ Deriv [ζ] ξ) ∨
    (ζ = topF ∧ RelClauses ξ topF)

/-- The core copy with the chosen fresh renaming. -/
def CoreCopy (ξ ζ : PLLFormula) : Prop := FreeInPLL ξ ζ (coreGen ξ ζ (freshRen ξ ζ))

def GoodCore : Prop := ∀ ξ ζ : PLLFormula, GoodPair ξ ζ → CoreCopy ξ ζ

/-- (R4), corrected: inside a faithful copy with variable-free data. -/
def GoodMain : Prop :=
  ∀ (a b : PLLFormula) (x : String → PLLFormula) (ξ ζ : PLLFormula),
    atomFree a = true → atomFree b = true → (∀ p, atomFree (x p) = true) → FreeInPLL a b x →
    GoodPair ξ ζ → FreePLLIn (rel a b x ξ) (rel a b x ζ)

/-- (R4), corrected: in the coordinates of the readers' copy. -/
def GoodInGR : Prop := ∀ ξ ζ : PLLFormula, GoodPair ξ ζ → FreePLLIn (gR ξ) (gR ζ)

/-- (R4), corrected: every finite depth. -/
def GoodNestAll : Prop :=
  ∀ ξs ζs : Nat → PLLFormula, (∀ d, GoodPair (ξs d) (ζs d)) → ∀ d : Nat,
    FreeInPLL (towerP ξs ζs d).a (towerP ξs ζs d).b (towerP ξs ζs d).x ∧
    (∀ p, atomFree ((towerP ξs ζs d).x p) = true) ∧
    ¬ Deriv [(towerP ξs ζs d).b] (towerP ξs ζs d).a ∧
    Deriv [(towerP ξs ζs d).a] (towerP ξs ζs (d + 1)).a ∧
    Deriv [(towerP ξs ζs (d + 1)).a] (towerP ξs ζs (d + 1)).b ∧
    Deriv [(towerP ξs ζs (d + 1)).b] (towerP ξs ζs d).b

/-! ### (R1) and the clause lemmas -/

/-- **PROVED: (R1).**  Faithfulness at `C = ¬◯⊥` and `C = ¬¬◯⊥`. -/
theorem relNecessary : RelNecessary := by
  intro ξ ζ x hF
  constructor
  · intro hd
    apply Endpoints.nd_ne
    apply of_top
    refine (hF.2.2 topF ne).mpr (Interval.deriv_of_sem fun M _ v hv => ?_)
    refine ⟨fun u _ hu => ?_, hv.2⟩
    exact Interval.sem_of_deriv hd M u hu.2 u (M.refl u) hu.1
  · intro hd
    apply Endpoints.nd_nne
    apply of_top
    refine (hF.2.2 topF Endpoints.nne).mpr (Interval.deriv_of_sem fun M _ v hv => ?_)
    refine ⟨fun u _ hu => ?_, hv.2⟩
    exact Interval.sem_of_deriv hd M u hu.2 u (M.refl u)
      (fun w huw hb => hu.1 w huw ⟨hb, SubframeModel.force_mono M ζ huw hu.2⟩)

/-- **PROVED.** -/
theorem clausesStrict : ClausesStrict := fun _ ζ h =>
  ⟨fun hd => h.1 (Interval.deriv_of_sem fun M _ _ hv u hvu _ =>
      Interval.sem_of_deriv hd M u (SubframeModel.force_mono M ζ hvu hv)),
   fun hd => h.2 (Interval.deriv_of_sem fun M _ _ hv u hvu hst =>
      hst u (M.refl u) (Interval.sem_of_deriv hd M u (SubframeModel.force_mono M ζ hvu hv)))⟩

/-- `M` with its `S` replaced by `T`. -/
def withS (M : SubframeModel) (T : Set M.W) : SubframeModel where
  W := M.W
  le := M.le
  S := T
  V := M.V
  refl := M.refl
  trans := M.trans
  hered := M.hered

/-- A ◯-free formula does not read `S`. -/
theorem force_withS (M : SubframeModel) (T : Set M.W) :
    ∀ φ : PLLFormula, boxFree φ = true → ∀ w : M.W, ((withS M T).force w φ ↔ M.force w φ)
  | .prop _, _, _ => Iff.rfl
  | .falsePLL, _, _ => Iff.rfl
  | .and A B, h, w => by
      have h' := Bool.and_eq_true_iff.mp (h : (boxFree A && boxFree B) = true)
      exact and_congr (force_withS M T A h'.1 w) (force_withS M T B h'.2 w)
  | .or A B, h, w => by
      have h' := Bool.and_eq_true_iff.mp (h : (boxFree A && boxFree B) = true)
      exact or_congr (force_withS M T A h'.1 w) (force_withS M T B h'.2 w)
  | .ifThen A B, h, w => by
      have h' := Bool.and_eq_true_iff.mp (h : (boxFree A && boxFree B) = true)
      have ihA := force_withS M T A h'.1
      have ihB := force_withS M T B h'.2
      show (∀ u, M.le w u → (withS M T).force u A → (withS M T).force u B) ↔
        (∀ u, M.le w u → M.force u A → M.force u B)
      exact ⟨fun h u hu ha => (ihB u).mp (h u hu ((ihA u).mpr ha)),
        fun h u hu ha => (ihB u).mpr (h u hu ((ihA u).mp ha))⟩
  | .somehow _, h, _ => nomatch h

/-- **PROVED**: for ◯-free `ξ`, `ζ` the clauses say `[ζ] ⊬ ξ` (read `◯` as the
constant `⊤`, `S = ∅`, for the first; as the identity, `S` everything, for the
second). -/
theorem clausesBoxFree : ClausesBoxFree := by
  intro ξ ζ hξ hζ
  refine ⟨fun h => (clausesStrict ξ ζ h).1, fun hn => ⟨fun hd => hn ?_, fun hd => hn ?_⟩⟩
  · refine Interval.deriv_of_sem fun M _ v hv => ?_
    have h1 := Interval.sem_of_deriv hd (withS M ∅) v ((force_withS M ∅ ζ hζ v).mpr hv)
    exact (force_withS M ∅ ξ hξ v).mp (h1 v (M.refl v) (fun _ _ hS => (hS : False).elim))
  · refine Interval.deriv_of_sem fun M _ v hv => ?_
    have h1 := Interval.sem_of_deriv hd (withS M Set.univ) v
      ((force_withS M Set.univ ζ hζ v).mpr hv)
    exact (force_withS M Set.univ ξ hξ v).mp (h1 v (M.refl v) (fun u _ hb => hb u (M.refl u) trivial))

/-- **PROVED: (R3) for ◯-free `ξ`, `ζ`.** -/
theorem relCriterionBoxFree : RelCriterionBoxFree := fun ξ ζ ρ hξ hζ hle hfr =>
  ⟨relNecessary ξ ζ _, fun h =>
    NestPLL.coreLemmaPLL ξ ζ ρ hξ hζ hle ((clausesBoxFree ξ ζ hξ hζ).mp h) hfr⟩

/-- **PROVED.** -/
theorem relClausesUp : RelClausesUp := fun _ _ _ h hc =>
  ⟨fun hd => hc.1 (Deriv.cutHead h hd), fun hd => hc.2 (Deriv.cutHead h hd)⟩

/-- **REFUTED: `RelClausesMono` as stated at Stage 1** (the inclusion of tops
the wrong way round): `[◯⊥] ⊢ ⊤`, `RelClauses ⊥ ⊤`, not `RelClauses ⊥ ◯⊥`. -/
theorem not_relClausesMono : ¬ RelClausesMono := fun h =>
  e_not (h .falsePLL topF e (MovingTop.le_top e) e_top)

/-- **PROVED**: every closed instance is necessary. -/
theorem relCopyNecessary : RelCopyNecessary := fun ξ ζ _ hF =>
  (copyIffTopAvoid ξ ζ (Deriv.cutHead (hF.1 "") (hF.2.1 ""))).mp (Endpoints.copy_of_free hF)

/-! ### The refutations -/

/-- **REFUTED: (R2)** at `ξ = ⊥`, `ζ = t3`. -/
theorem not_relSufficient : ¬ RelSufficient := fun h =>
  d_t3_no_copy _ (h .falsePLL t3 (freshRen _ _) (MovingTop.bot_le _) d_t3_clauses
    (Interval.fresh_freshRen _ _))

/-- **REFUTED: (R3)**, direction `⟸`, at `ξ = ⊥`, `ζ = t3`. -/
theorem not_relCriterion : ¬ RelCriterion := fun h =>
  d_t3_no_copy _ ((h .falsePLL t3 (freshRen _ _) (MovingTop.bot_le _)
    (Interval.fresh_freshRen _ _)).mpr d_t3_clauses)

/-- **REFUTED: the one-clause form** at `ξ = ⊥`, `ζ = t6`. -/
theorem not_relSufficientDisj : ¬ RelSufficientDisj := fun h =>
  d_t6_no_copy _ (h .falsePLL t6 (freshRen _ _) (MovingTop.bot_le _) d_t6_disj
    (Interval.fresh_freshRen _ _))

/-- **REFUTED: (R2) for a ◯-free top** (D3). -/
theorem not_relSufficientBoxFreeTop : ¬ RelSufficientBoxFreeTop := fun h =>
  d3_no_copy _ (h x3 z3 (freshRen _ _) rfl d3_le d3_clauses (Interval.fresh_freshRen _ _))

/-- **REFUTED: (R2) for a ◯-free bottom** (D1). -/
theorem not_relSufficientBoxFreeBot : ¬ RelSufficientBoxFreeBot := fun h =>
  d_t3_no_copy _ (h .falsePLL t3 (freshRen _ _) rfl (MovingTop.bot_le _) d_t3_clauses
    (Interval.fresh_freshRen _ _))

/-- **REFUTED: (R2) for closed endpoints** (D1). -/
theorem not_relSufficientClosed : ¬ RelSufficientClosed := fun h =>
  d_t3_no_copy _ (h .falsePLL t3 (freshRen _ _) rfl rfl (MovingTop.bot_le _) d_t3_clauses
    (Interval.fresh_freshRen _ _))

/-- `gR t3 = t3[⊥ := σ³⊥]`, so `[σ³⊥, σ³t3]` carries no faithful copy. -/
theorem no_copy_gR_t3 (y : String → PLLFormula) : ¬ FreeInPLL (gR .falsePLL) (gR t3) y := by
  have h : gR t3 = subBot (gR .falsePLL) t3 := relB_closed b3 xr t3 rfl
  exact no_copy rfl nd_t3 (by rw [← h]; exact Deriv.iden (.head _)) y

/-- **REFUTED: (R4) in the readers' coordinates** (D1 transported). -/
theorem not_relInGR : ¬ RelInGR := fun h =>
  let ⟨y, _, hF⟩ := h .falsePLL t3 (MovingTop.bot_le _) d_t3_clauses
  no_copy_gR_t3 y hF

/-- No faithful copy in `[rel σ³⊥ ⊤ xr ⊥, rel σ³⊥ ⊤ xr t3]`. -/
theorem no_copy_rel_t3 (y : String → PLLFormula) :
    ¬ FreeInPLL (rel (base 3) topF xr .falsePLL) (rel (base 3) topF xr t3) y := fun hF =>
  no_copy_gR_t3 y (NestPLL.freeInPLL_congr hF (NestPLL.rel_top_interd_gR _)
    (NestPLL.rel_top_interd_gR _))

/-- **REFUTED: (R4) inside the readers' copy** (D1 transported). -/
theorem not_relMain : ¬ RelMain := fun h =>
  let ⟨y, _, hF⟩ := h (base 3) topF xr .falsePLL t3 b3_vf rfl xr_vf NestPLL.bridgePLL3
    (MovingTop.bot_le _) d_t3_clauses
  no_copy_rel_t3 y hF

/-- **REFUTED: (R4) at every depth**: depth one already fails for
`ξ_d = ⊥`, `ζ_d = t3`. -/
theorem not_relNestAll : ¬ RelNestAll := fun h =>
  no_copy_rel_t3 _ (h (fun _ => .falsePLL) (fun _ => t3)
    (fun _ => ⟨MovingTop.bot_le _, d_t3_clauses⟩) 1).1

/-! ### The base criterion with atoms: `ζ = ⊤`, any `ξ`

The two-sided extension `Endpoints.TS` with a valuation: a copy world `x` of
`K` carries the fresh atom `ρ p` iff `x ⊩_K p`, and an old atom `c` iff `c`
holds at `m₁` when `x` sees `S`, and at `m₂` when `x` sees a world with no
`S` above it; the attached worlds keep their own atoms and carry every fresh
atom.  A terminal cluster of `K` sees exactly one of the two, so it is
bisimilar, atoms included, to the cluster of `m₁` or of `m₂`. -/

section TopCase

open Endpoints (SeesS SeesE tsLe tsS IsBisim TS bisimK₁ bisimK₂ bisimIn bisimOut isBisimK₁
  isBisimK₂ isBisimIn isBisimOut seesS_mono seesE_mono exists_terminal SideIn SideOut)

/-- **Closed under bisimulation, atoms outside the range of `ρ` included.** -/
theorem bisim_forceR {N K : SubframeModel} {B : N.W → K.W → Prop} (hB : IsBisim N K B)
    {ρ : String → String}
    (hV : ∀ {w k}, B w k → ∀ c, (∀ p, ρ p ≠ c) → (w ∈ N.V c ↔ k ∈ K.V c)) :
    ∀ φ : PLLFormula, (∀ p, Interval.occ (ρ p) φ = false) → ∀ w k, B w k →
      (N.force w φ ↔ K.force k φ)
  | .prop c, ho, w, k, hb => hV hb c fun p e => by
      have h1 : decide (c = ρ p) = false := ho p
      exact absurd e.symm (of_decide_eq_false h1)
  | .falsePLL, _, _, _, _ => Iff.rfl
  | .and A C, ho, w, k, hb =>
      and_congr (bisim_forceR hB hV A (fun p => (Interval.or_eq_false_split (ho p)).1) w k hb)
        (bisim_forceR hB hV C (fun p => (Interval.or_eq_false_split (ho p)).2) w k hb)
  | .or A C, ho, w, k, hb =>
      or_congr (bisim_forceR hB hV A (fun p => (Interval.or_eq_false_split (ho p)).1) w k hb)
        (bisim_forceR hB hV C (fun p => (Interval.or_eq_false_split (ho p)).2) w k hb)
  | .ifThen A C, ho, w, k, hb => by
      have hA : ∀ p, Interval.occ (ρ p) A = false := fun p => (Interval.or_eq_false_split (ho p)).1
      have hC : ∀ p, Interval.occ (ρ p) C = false := fun p => (Interval.or_eq_false_split (ho p)).2
      constructor
      · intro hw k' hkk' hk
        obtain ⟨w', hww', hb'⟩ := hB.back hb hkk'
        exact (bisim_forceR hB hV C hC w' k' hb').mp
          (hw w' hww' ((bisim_forceR hB hV A hA w' k' hb').mpr hk))
      · intro hk w' hww' hw
        obtain ⟨k', hkk', hb'⟩ := hB.forth hb hww'
        exact (bisim_forceR hB hV C hC w' k' hb').mpr
          (hk k' hkk' ((bisim_forceR hB hV A hA w' k' hb').mp hw))
  | .somehow A, ho, w, k, hb => by
      constructor
      · intro hw k' hkk' hS
        obtain ⟨w', hww', hS', hb'⟩ := hB.backS hb hkk' hS
        exact (bisim_forceR hB hV A ho w' k' hb').mp (hw w' hww' hS')
      · intro hk w' hww' hS
        obtain ⟨k', hkk', hS', hb'⟩ := hB.forthS hb hww' hS
        exact (bisim_forceR hB hV A ho w' k' hb').mpr (hk k' hkk' hS')

variable (M K₁ K₂ : SubframeModel) (m₁ : K₁.W) (m₂ : K₂.W) (ρ : String → String)

/-- The valuation of the two-sided extension with atoms. -/
def taV (c : String) : M.W ⊕ (K₁.W ⊕ K₂.W) → Prop
  | .inl x => (∃ p, ρ p = c ∧ x ∈ M.V p) ∨
      ((∀ p, ρ p ≠ c) ∧ (SeesS M x → m₁ ∈ K₁.V c) ∧ (SeesE M x → m₂ ∈ K₂.V c))
  | .inr (.inl k) => (∃ p, ρ p = c) ∨ k ∈ K₁.V c
  | .inr (.inr k) => (∃ p, ρ p = c) ∨ k ∈ K₂.V c

theorem taV_hered {c : String} {u v : M.W ⊕ (K₁.W ⊕ K₂.W)} (h : tsLe M K₁ K₂ m₁ m₂ u v)
    (hu : taV M K₁ K₂ m₁ m₂ ρ c u) : taV M K₁ K₂ m₁ m₂ ρ c v := by
  rcases u with x | k | k <;> rcases v with y | l | l
  · rcases hu with ⟨p, hp, hx⟩ | ⟨hne, hS, hE⟩
    · exact Or.inl ⟨p, hp, M.hered h hx⟩
    · exact Or.inr ⟨hne, fun hy => hS (seesS_mono M h hy), fun hy => hE (seesE_mono M h hy)⟩
  · rcases hu with ⟨p, hp, _⟩ | ⟨_, hS, _⟩
    · exact Or.inl ⟨p, hp⟩
    · exact Or.inr (K₁.hered h.2.1 (hS h.1))
  · rcases hu with ⟨p, hp, _⟩ | ⟨_, _, hE⟩
    · exact Or.inl ⟨p, hp⟩
    · exact Or.inr (K₂.hered h.2.1 (hE h.1))
  · exact False.elim h
  · exact Or.elim hu Or.inl fun hk => Or.inr (K₁.hered h hk)
  · exact False.elim h
  · exact False.elim h
  · exact False.elim h
  · exact Or.elim hu Or.inl fun hk => Or.inr (K₂.hered h hk)

/-- **The two-sided extension with atoms.** -/
def TSA : SubframeModel where
  W := M.W ⊕ (K₁.W ⊕ K₂.W)
  le := tsLe M K₁ K₂ m₁ m₂
  S := {w | tsS M K₁ K₂ w}
  V c := {w | taV M K₁ K₂ m₁ m₂ ρ c w}
  refl := Endpoints.tsLe_refl M K₁ K₂ m₁ m₂
  trans h₁ h₂ := Endpoints.tsLe_trans M K₁ K₂ m₁ m₂ h₁ h₂
  hered h hu := taV_hered M K₁ K₂ m₁ m₂ ρ h hu

variable {M K₁ K₂ m₁ m₂ ρ}

/-- A bisimulation of `TS` is one of `TSA` (same order, same `S`). -/
theorem isBisim_TSA {K : SubframeModel} {B : (TS M K₁ K₂ m₁ m₂).W → K.W → Prop}
    (h : IsBisim (TS M K₁ K₂ m₁ m₂) K B) : IsBisim (TSA M K₁ K₂ m₁ m₂ ρ) K B :=
  ⟨h.forth, h.back, h.forthS, h.backS⟩

theorem atoms_K₁ {w : (TSA M K₁ K₂ m₁ m₂ ρ).W} {k : K₁.W} (hb : bisimK₁ M K₁ K₂ m₁ m₂ w k)
    (c : String) (hc : ∀ p, ρ p ≠ c) : (w ∈ (TSA M K₁ K₂ m₁ m₂ ρ).V c ↔ k ∈ K₁.V c) := by
  rcases w with x | k₀ | k₀
  · exact False.elim hb
  · have hb' : k₀ = k := hb
    cases hb'
    show ((∃ p, ρ p = c) ∨ k ∈ K₁.V c) ↔ k ∈ K₁.V c
    exact ⟨fun h => Or.elim h (fun ⟨p, hp⟩ => absurd hp (hc p)) id, Or.inr⟩
  · exact False.elim hb

theorem atoms_K₂ {w : (TSA M K₁ K₂ m₁ m₂ ρ).W} {k : K₂.W} (hb : bisimK₂ M K₁ K₂ m₁ m₂ w k)
    (c : String) (hc : ∀ p, ρ p ≠ c) : (w ∈ (TSA M K₁ K₂ m₁ m₂ ρ).V c ↔ k ∈ K₂.V c) := by
  rcases w with x | k₀ | k₀
  · exact False.elim hb
  · exact False.elim hb
  · have hb' : k₀ = k := hb
    cases hb'
    show ((∃ p, ρ p = c) ∨ k ∈ K₂.V c) ↔ k ∈ K₂.V c
    exact ⟨fun h => Or.elim h (fun ⟨p, hp⟩ => absurd hp (hc p)) id, Or.inr⟩

theorem atoms_In {y s : M.W} (hterm : ∀ z, M.le y z → M.le z y) (hys : M.le y s)
    (hs : s ∈ M.S) {w : (TSA M K₁ K₂ m₁ m₂ ρ).W} {k : K₁.W}
    (hb : bisimIn M K₁ K₂ m₁ m₂ y w k) (c : String) (hc : ∀ p, ρ p ≠ c) :
    (w ∈ (TSA M K₁ K₂ m₁ m₂ ρ).V c ↔ k ∈ K₁.V c) := by
  rcases w with q | k₀ | k₀
  · have hb' : M.le y q ∧ K₁.le m₁ k ∧ K₁.le k m₁ := hb
    have hS : SeesS M q := ⟨s, M.trans (hterm q hb'.1) hys, hs⟩
    have hE : ¬ SeesE M q := fun ⟨z, hqz, hz⟩ =>
      hz s (M.trans (hterm z (M.trans hb'.1 hqz)) hys) hs
    show ((∃ p, ρ p = c ∧ q ∈ M.V p) ∨
      ((∀ p, ρ p ≠ c) ∧ (SeesS M q → m₁ ∈ K₁.V c) ∧ (SeesE M q → m₂ ∈ K₂.V c))) ↔ k ∈ K₁.V c
    constructor
    · intro h
      rcases h with ⟨p, hp, _⟩ | ⟨_, h1, _⟩
      · exact absurd hp (hc p)
      · exact K₁.hered hb'.2.1 (h1 hS)
    · intro h
      exact Or.inr ⟨hc, fun _ => K₁.hered hb'.2.2 h, fun h' => absurd h' hE⟩
  · have hb' : k₀ = k := hb
    cases hb'
    show ((∃ p, ρ p = c) ∨ k ∈ K₁.V c) ↔ k ∈ K₁.V c
    exact ⟨fun h => Or.elim h (fun ⟨p, hp⟩ => absurd hp (hc p)) id, Or.inr⟩
  · exact False.elim hb

theorem atoms_Out {y : M.W} (hno : ¬ SeesS M y) {w : (TSA M K₁ K₂ m₁ m₂ ρ).W} {k : K₂.W}
    (hb : bisimOut M K₁ K₂ m₁ m₂ y w k) (c : String) (hc : ∀ p, ρ p ≠ c) :
    (w ∈ (TSA M K₁ K₂ m₁ m₂ ρ).V c ↔ k ∈ K₂.V c) := by
  rcases w with q | k₀ | k₀
  · have hb' : M.le y q ∧ K₂.le m₂ k ∧ K₂.le k m₂ := hb
    have hS : ¬ SeesS M q := fun h => hno (seesS_mono M hb'.1 h)
    have hE : SeesE M q := ⟨q, M.refl q, fun z hqz hz => hno ⟨z, M.trans hb'.1 hqz, hz⟩⟩
    show ((∃ p, ρ p = c ∧ q ∈ M.V p) ∨
      ((∀ p, ρ p ≠ c) ∧ (SeesS M q → m₁ ∈ K₁.V c) ∧ (SeesE M q → m₂ ∈ K₂.V c))) ↔ k ∈ K₂.V c
    constructor
    · intro h
      rcases h with ⟨p, hp, _⟩ | ⟨_, _, h2⟩
      · exact absurd hp (hc p)
      · exact K₂.hered hb'.2.1 (h2 hE)
    · intro h
      exact Or.inr ⟨hc, fun h' => absurd h' hS, fun _ => K₂.hered hb'.2.2 h⟩
  · exact False.elim hb
  · have hb' : k₀ = k := hb
    cases hb'
    show ((∃ p, ρ p = c) ∨ k ∈ K₂.V c) ↔ k ∈ K₂.V c
    exact ⟨fun h => Or.elim h (fun ⟨p, hp⟩ => absurd hp (hc p)) id, Or.inr⟩

/-- **The realization with atoms**: on the copy of `M`, the relativised image of
every formula holds exactly where the formula holds in `M`. -/
theorem tsa_transfer [FinDec M] [FinDec K₁] [FinDec K₂] {ξ : PLLFormula} (hfr : Fresh ρ ξ topF)
    (hm₁S : m₁ ∈ K₁.S) (hm₁a : ¬ K₁.force m₁ ξ)
    (hm₁up : ∀ w, K₁.le m₁ w → ¬ K₁.le w m₁ → K₁.force w ξ)
    (hm₂S : ∀ w, K₂.le m₂ w → K₂.le w m₂ → w ∉ K₂.S) (hm₂a : ¬ K₂.force m₂ ξ)
    (hm₂up : ∀ w, K₂.le m₂ w → ¬ K₂.le w m₂ → K₂.force w ξ) :
    ∀ (A : PLLFormula) (x : M.W),
      ((TSA M K₁ K₂ m₁ m₂ ρ).force (.inl x) (relB ξ (coreGen ξ topF ρ) A) ↔ M.force x A) := by
  have hoξ : ∀ p, Interval.occ (ρ p) ξ = false := fun p => (hfr.2 p).1
  have hK₁ : ∀ k : K₁.W, ((TSA M K₁ K₂ m₁ m₂ ρ).force (.inr (.inl k)) ξ ↔ K₁.force k ξ) :=
    fun k => bisim_forceR (isBisim_TSA (isBisimK₁ M K₁ K₂ m₁ m₂))
      (fun hb c hc => atoms_K₁ hb c hc) ξ hoξ _ k
      (show bisimK₁ M K₁ K₂ m₁ m₂ (Sum.inr (Sum.inl k)) k from rfl)
  have hK₂ : ∀ k : K₂.W, ((TSA M K₁ K₂ m₁ m₂ ρ).force (.inr (.inr k)) ξ ↔ K₂.force k ξ) :=
    fun k => bisim_forceR (isBisim_TSA (isBisimK₂ M K₁ K₂ m₁ m₂))
      (fun hb c hc => atoms_K₂ hb c hc) ξ hoξ _ k
      (show bisimK₂ M K₁ K₂ m₁ m₂ (Sum.inr (Sum.inr k)) k from rfl)
  have hnot : ∀ x : M.W, ¬ (TSA M K₁ K₂ m₁ m₂ ρ).force (.inl x) ξ := by
    intro x hx
    obtain ⟨y, hxy, hterm⟩ := exists_terminal M x
    have hy := SubframeModel.force_mono (TSA M K₁ K₂ m₁ m₂ ρ) ξ (u := Sum.inl x)
      (v := Sum.inl y) hxy hx
    rcases Decidable.em (∃ s ∈ FinDec.elems (M := M), M.le y s ∧ s ∈ M.S) with
      ⟨s, _, hys, hs⟩ | hno
    · have hb : bisimIn M K₁ K₂ m₁ m₂ y (Sum.inl y) m₁ := ⟨M.refl y, K₁.refl m₁, K₁.refl m₁⟩
      exact hm₁a ((bisim_forceR
        (isBisim_TSA (ρ := ρ) (isBisimIn (K₂ := K₂) (m₂ := m₂) hm₁S hterm hys hs))
        (fun hb c hc => atoms_In hterm hys hs hb c hc) ξ hoξ _ m₁ hb).mp hy)
    · have hno' : ¬ SeesS M y := fun ⟨s, hys, hs⟩ => hno ⟨s, FinDec.complete s, hys, hs⟩
      have hb : bisimOut M K₁ K₂ m₁ m₂ y (Sum.inl y) m₂ := ⟨M.refl y, K₂.refl m₂, K₂.refl m₂⟩
      exact hm₂a ((bisim_forceR
        (isBisim_TSA (ρ := ρ) (isBisimOut (K₁ := K₁) (m₁ := m₁) hm₂S hterm hno'))
        (fun hb c hc => atoms_Out hno' hb c hc) ξ hoξ _ m₂ hb).mp hy)
  have hback : ∀ (x : M.W) (v : (TSA M K₁ K₂ m₁ m₂ ρ).W), (TSA M K₁ K₂ m₁ m₂ ρ).le (.inl x) v →
      (TSA M K₁ K₂ m₁ m₂ ρ).force v ξ ∨ ∃ j, M.le x j ∧ Sum.inl j = v := by
    intro x v hv
    rcases v with j | k | k
    · exact Or.inr ⟨j, hv, rfl⟩
    · exact Or.inl ((hK₁ k).mpr (hm₁up k hv.2.1 hv.2.2))
    · exact Or.inl ((hK₂ k).mpr (hm₂up k hv.2.1 hv.2.2))
  have hatom : ∀ (x : M.W) p,
      ((TSA M K₁ K₂ m₁ m₂ ρ).force (.inl x) (coreGen ξ topF ρ p) ↔ x ∈ M.V p) := by
    intro x p
    constructor
    · intro h
      rcases h.1 with hv | hv
      · rcases hv with ⟨p', hp', hx⟩ | ⟨hne, _⟩
        · rw [hfr.1 p' p hp'] at hx
          exact hx
        · exact absurd rfl (hne p)
      · exact absurd hv (hnot x)
    · intro h
      exact ⟨Or.inl (Or.inl ⟨p, rfl, h⟩), Interval.force_topF _ _⟩
  have hbx : ∀ (v : (TSA M K₁ K₂ m₁ m₂ ρ).W) p, (TSA M K₁ K₂ m₁ m₂ ρ).force v ξ →
      (TSA M K₁ K₂ m₁ m₂ ρ).force v (coreGen ξ topF ρ p) :=
    fun v _ hv => ⟨Or.inr hv, Interval.force_topF _ _⟩
  exact relB_transferO (TSA M K₁ K₂ m₁ m₂ ρ) ξ (coreGen ξ topF ρ) M Sum.inl hbx hnot
    (fun h => h) hback (fun _ => Iff.rfl) hatom

end TopCase

/-- `SideIn` and `SideOut` from the two clauses, any `ξ` (the proof of
`Endpoints.sidesOfNd`, which does not read closedness). -/
theorem sidesOfNdOpen (a : PLLFormula) :
    (¬ Deriv [] (stab2 a) → Endpoints.SideIn a) ∧ (¬ Deriv [] (stab a) → Endpoints.SideOut a) := by
  constructor
  · intro hnd
    rcases SubTab.complete (stab2 a) with ⟨c, hc⟩ | ⟨m, hm⟩
    · exact absurd (SubTab.holds_of_check hc) hnd
    · obtain ⟨hok, _, hroot⟩ := Endpoints.root_refutes hm
      obtain ⟨y, _, hH, hya⟩ := Endpoints.exists_of_not_imp hroot
      obtain ⟨z, hyz, hza, hmax⟩ :=
        Interval.exists_max_not (m.toModel hok) a _ y (Nat.le_refl _) hya
      have hbox : ¬ (m.toModel hok).force z (.somehow a) := fun hb => hza (hH z hyz hb)
      obtain ⟨u, hzu, huS, hua⟩ := Endpoints.exists_of_not_box hbox
      have huz : (m.toModel hok).le u z := (hmax u hzu).resolve_left hua
      refine ⟨m.toModel hok, inferInstance, u, huS, hua, fun w huw hwu => ?_⟩
      rcases hmax w ((m.toModel hok).trans hzu huw) with hw | hw
      · exact hw
      · exact absurd ((m.toModel hok).trans hw hzu) hwu
  · intro hnd
    rcases SubTab.complete (stab a) with ⟨c, hc⟩ | ⟨m, hm⟩
    · exact absurd (SubTab.holds_of_check hc) hnd
    · obtain ⟨hok, _, hroot⟩ := Endpoints.root_refutes hm
      obtain ⟨y, _, hbox, hya⟩ := Endpoints.exists_of_not_imp hroot
      obtain ⟨z, hyz, hza, hmax⟩ :=
        Interval.exists_max_not (m.toModel hok) a _ y (Nat.le_refl _) hya
      refine ⟨m.toModel hok, inferInstance, z, fun w hzw hwz hwS => ?_, hza, fun w hzw hwz => ?_⟩
      · exact hza (SubframeModel.force_mono (m.toModel hok) a hwz
          (hbox w ((m.toModel hok).trans hyz hzw) hwS))
      · exact (hmax w hzw).resolve_right hwz

/-- **`⟸` at `ζ = ⊤`, by the two-sided extension with atoms.** -/
theorem top_reflects {ξ : PLLFormula} {ρ : String → String} (hfr : Fresh ρ ξ topF)
    (hin : Endpoints.SideIn ξ) (hout : Endpoints.SideOut ξ) {A B : PLLFormula}
    (hd : Deriv [rel ξ topF (coreGen ξ topF ρ) A] (rel ξ topF (coreGen ξ topF ρ) B)) :
    Deriv [A] B := by
  obtain ⟨K₁, i₁, m₁, hm₁S, hm₁a, hm₁up⟩ := hin
  obtain ⟨K₂, i₂, m₂, hm₂S, hm₂a, hm₂up⟩ := hout
  refine Interval.deriv_of_sem fun M _ u hu => ?_
  have htr := tsa_transfer (M := M) (K₁ := K₁) (K₂ := K₂) (m₁ := m₁) (m₂ := m₂) (ρ := ρ)
    hfr hm₁S hm₁a hm₁up hm₂S hm₂a hm₂up
  have hrA : (TSA M K₁ K₂ m₁ m₂ ρ).force (Sum.inl u) (rel ξ topF (coreGen ξ topF ρ) A) :=
    (rel_iff_relB_gen (TSA M K₁ K₂ m₁ m₂ ρ) ξ topF _ _ (fun _ _ _ => Iff.rfl) A (Sum.inl u)
      (Interval.force_topF _ _)).mpr ((htr A u).mpr hu)
  have hrB := Interval.sem_of_deriv hd (TSA M K₁ K₂ m₁ m₂ ρ) (Sum.inl u) hrA
  exact (htr B u).mp ((rel_iff_relB_gen (TSA M K₁ K₂ m₁ m₂ ρ) ξ topF _ _ (fun _ _ _ => Iff.rfl) B
    (Sum.inl u) (Interval.force_topF _ _)).mp hrB)

/-- **PROVED: the relative criterion at `ζ = ⊤`, every `ξ`, open or closed.** -/
theorem relCriterionTop : RelCriterionTop := by
  intro ξ ρ hfr
  refine ⟨relNecessary ξ topF _, fun hc => ?_⟩
  have n1 : ¬ Deriv [] (stab ξ) := fun h => hc.1 (wk h)
  have n2 : ¬ Deriv [] (stab2 ξ) := fun h => hc.2 (wk h)
  refine ⟨fun p => (Interval.core_bounds (MovingTop.le_top ξ) p).1,
    fun p => (Interval.core_bounds (MovingTop.le_top ξ) p).2, fun A B => ⟨?_,
      top_reflects hfr ((sidesOfNdOpen ξ).1 n2) ((sidesOfNdOpen ξ).2 n1)⟩⟩
  exact NestPLL.rel_preservesPLL ξ topF (coreGen ξ topF ρ)
    (fun M v _ hv => ⟨Or.inr hv, Interval.force_topF M v⟩) (fun _ _ _ hv => hv.2)

theorem occ_atomFree (c : String) : ∀ φ : PLLFormula, atomFree φ = true → Interval.occ c φ = false
  | .prop _, h => nomatch h
  | .falsePLL, _ => rfl
  | .and A B, h => by
      have h' := Bool.and_eq_true_iff.mp (h : (atomFree A && atomFree B) = true)
      show (Interval.occ c A || Interval.occ c B) = false
      rw [occ_atomFree c A h'.1, occ_atomFree c B h'.2]
      rfl
  | .or A B, h => by
      have h' := Bool.and_eq_true_iff.mp (h : (atomFree A && atomFree B) = true)
      show (Interval.occ c A || Interval.occ c B) = false
      rw [occ_atomFree c A h'.1, occ_atomFree c B h'.2]
      rfl
  | .ifThen A B, h => by
      have h' := Bool.and_eq_true_iff.mp (h : (atomFree A && atomFree B) = true)
      show (Interval.occ c A || Interval.occ c B) = false
      rw [occ_atomFree c A h'.1, occ_atomFree c B h'.2]
      rfl
  | .somehow A, h => occ_atomFree c A h

/-- **PROVED: the base criterion recovered** (`ρ = id`, `coreGen a ⊤ id = selfGen a ⊤`). -/
theorem selfTopIff : SelfTopIff := fun a ha =>
  relCriterionTop a id ⟨fun _ _ h => h, fun p => ⟨occ_atomFree p a ha, rfl⟩⟩

/-! ### The corrected transport -/

/-- **PROVED: composition** (the proof of `NestPLL.nestPLL`, any inner copy). -/
theorem nestOfCore : NestOfCore := by
  intro a b x ξ ζ y hF hC
  obtain ⟨hax, hxb, hfaith⟩ := hF
  obtain ⟨hyl, hyu, hyf⟩ := hC
  have sxb : ∀ (M : SubframeModel) v p, M.force v (x p) → M.force v b := fun M v p h =>
    Interval.sem_of_deriv (hxb p) M v h
  have sab : ∀ (M : SubframeModel) v, M.force v a → M.force v b := fun M v h =>
    sxb M v "" (Interval.sem_of_deriv (hax "") M v h)
  refine ⟨fun p => (hfaith _ _).mp (hyl p), fun p => (hfaith _ _).mp (hyu p), fun A B => ?_⟩
  refine (hyf A B).trans ((hfaith _ _).trans (Interval.deriv_congr ?_ ?_))
  · exact fun M v => (Interval.rel_comp M a b x ξ ζ y (sab M) (sxb M) A v).symm
  · exact fun M v => (Interval.rel_comp M a b x ξ ζ y (sab M) (sxb M) B v).symm

theorem goodPair_le {ξ ζ : PLLFormula} (h : GoodPair ξ ζ) : Deriv [ξ] ζ := by
  rcases h with ⟨_, _, hle, _⟩ | ⟨rfl, _⟩
  · exact hle
  · exact MovingTop.le_top ξ

/-- **PROVED.** -/
theorem goodCore : GoodCore := by
  intro ξ ζ h
  rcases h with ⟨hξ, hζ, hle, hstrict⟩ | ⟨rfl, hc⟩
  · exact NestPLL.coreLemmaPLL ξ ζ _ hξ hζ hle hstrict (Interval.fresh_freshRen ξ ζ)
  · exact (relCriterionTop ξ _ (Interval.fresh_freshRen ξ topF)).mpr hc

/-- **PROVED.** -/
theorem goodMain : GoodMain := by
  intro a b x ξ ζ ha hb hx hF h
  exact ⟨nestGen a b x ξ ζ (freshRen ξ ζ), fun p => Interval.atomFree_rel ha hb hx _,
    nestOfCore a b x ξ ζ _ hF (goodCore ξ ζ h)⟩

/-- **PROVED.** -/
theorem goodInGR : GoodInGR := fun ξ ζ h =>
  ⟨fun p => gR (coreGen ξ ζ (freshRen ξ ζ) p), fun _ => g_af _,
    Endpoints.transportG ξ ζ _ (goodCore ξ ζ h)⟩

theorem towerGood_props (ξs ζs : Nat → PLLFormula) (h : ∀ d, GoodPair (ξs d) (ζs d)) :
    ∀ d : Nat,
    FreeInPLL (towerP ξs ζs d).a (towerP ξs ζs d).b (towerP ξs ζs d).x ∧
    (∀ p, atomFree ((towerP ξs ζs d).x p) = true) ∧
    atomFree (towerP ξs ζs d).a = true ∧ atomFree (towerP ξs ζs d).b = true
  | 0 => ⟨NestPLL.bridgePLL3, xr_vf, b3_vf, rfl⟩
  | d + 1 => by
      obtain ⟨hF, hx, ha, hb⟩ := towerGood_props ξs ζs h d
      exact ⟨nestOfCore _ _ _ _ _ _ hF (goodCore _ _ (h d)),
        fun _ => Interval.atomFree_rel ha hb hx _, Interval.atomFree_rel ha hb hx _,
        Interval.atomFree_rel ha hb hx _⟩

/-- **PROVED: (R4) corrected, every finite depth.** -/
theorem goodNestAll : GoodNestAll := by
  intro ξs ζs h d
  obtain ⟨hF, hx, _, _⟩ := towerGood_props ξs ζs h d
  refine ⟨hF, hx, NestPLL.freeInPLL_strict hF, ?_, ?_, ?_⟩
  · exact (hF.2.2 .falsePLL (ξs d)).mp (MovingTop.bot_le _)
  · exact (hF.2.2 (ξs d) (ζs d)).mp (goodPair_le (h d))
  · exact Deriv.cutHead ((hF.2.2 (ζs d) topF).mp (MovingTop.le_top _))
      (Deriv.andElim2 (Deriv.iden (.head _)))

end RelCrit
end F0
end PLLND

/-! ## Axiom pins: stage 3 -/

#axioms_within PLLND.F0.RelCrit.relNecessary [propext, Quot.sound]
#axioms_within PLLND.F0.RelCrit.clausesStrict [propext, Quot.sound]
#axioms_within PLLND.F0.RelCrit.force_withS [propext, Quot.sound]
#axioms_within PLLND.F0.RelCrit.clausesBoxFree [propext, Quot.sound]
#axioms_within PLLND.F0.RelCrit.relCriterionBoxFree [propext, Quot.sound]
#axioms_within PLLND.F0.RelCrit.relClausesUp [propext, Quot.sound]
#axioms_within PLLND.F0.RelCrit.not_relClausesMono [propext, Quot.sound]
#axioms_within PLLND.F0.RelCrit.relCopyNecessary [propext, Quot.sound]
#axioms_within PLLND.F0.RelCrit.not_relSufficient [propext, Quot.sound]
#axioms_within PLLND.F0.RelCrit.not_relCriterion [propext, Quot.sound]
#axioms_within PLLND.F0.RelCrit.not_relSufficientDisj [propext, Quot.sound]
#axioms_within PLLND.F0.RelCrit.not_relSufficientBoxFreeTop [propext, Quot.sound]
#axioms_within PLLND.F0.RelCrit.not_relSufficientBoxFreeBot [propext, Quot.sound]
#axioms_within PLLND.F0.RelCrit.not_relSufficientClosed [propext, Quot.sound]
#axioms_within PLLND.F0.RelCrit.no_copy_gR_t3 [propext, Quot.sound]
#axioms_within PLLND.F0.RelCrit.not_relInGR [propext, Quot.sound]
#axioms_within PLLND.F0.RelCrit.no_copy_rel_t3 [propext, Quot.sound]
#axioms_within PLLND.F0.RelCrit.not_relMain [propext, Quot.sound]
#axioms_within PLLND.F0.RelCrit.not_relNestAll [propext, Quot.sound]
#axioms_within PLLND.F0.RelCrit.bisim_forceR [propext, Quot.sound]
#axioms_within PLLND.F0.RelCrit.taV_hered [propext, Quot.sound]
#axioms_within PLLND.F0.RelCrit.atoms_In [propext, Quot.sound]
#axioms_within PLLND.F0.RelCrit.atoms_Out [propext, Quot.sound]
#axioms_within PLLND.F0.RelCrit.tsa_transfer [propext, Quot.sound]
#axioms_within PLLND.F0.RelCrit.sidesOfNdOpen [propext, Quot.sound]
#axioms_within PLLND.F0.RelCrit.top_reflects [propext, Quot.sound]
#axioms_within PLLND.F0.RelCrit.relCriterionTop [propext, Quot.sound]
#axioms_within PLLND.F0.RelCrit.selfTopIff [propext, Quot.sound]
#axioms_within PLLND.F0.RelCrit.nestOfCore [propext, Quot.sound]
#axioms_within PLLND.F0.RelCrit.goodCore [propext, Quot.sound]
#axioms_within PLLND.F0.RelCrit.goodMain [propext, Quot.sound]
#axioms_within PLLND.F0.RelCrit.goodInGR [propext, Quot.sound]
#axioms_within PLLND.F0.RelCrit.goodNestAll [propext, Quot.sound]
