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
