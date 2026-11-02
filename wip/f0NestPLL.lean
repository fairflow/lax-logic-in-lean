import wip.f0Endpoints
import Meta.Audit

/-!
# Faithful copies of PLL in nested intervals of F0 (◯-free endpoints); covers above `σ³⊥`

Matthew, 2026-11-02: the clearest statement that, for `σ³⊥ ≤ a < b ≤ ⊤`, the
free PLL algebra `F_ω` embeds faithfully in `[a, b]`, `◯` included, under
conditions on `a`, `b`.  Unconditionally it is REFUTED: a `◯`-fixed bottom
(`[◯a] ⊢ a`, e.g. `a = ◯σ³⊥`) admits no faithful copy even of F0
(`Endpoints.necBox`).  Two tasks, approved the same day:

1. the PLL version of the nested-interval theorem of `wip/f0FreeInterval.lean`
   for ◯-free endpoints, at every depth;
2. a cover check above `σ³⊥`: is `[σ³⊥, ◯σ³⊥]` (the `σ³`-image of the cover
   `⊥ ⋖ ◯⊥`, `cover_0_1`) a cover of F0?

## The statements (Stage 1, committed before any proof, METHOD.md §1)

`rel a b x` is the interval translation of `wip/f0FreeInterval.lean`
(`⊥ ↦ a`, `p ↦ x p`, `∧ ∨` kept, `A → B ↦ (rel A ↠ rel B) ∧ b`,
`◯A ↦ ◯(rel A) ∧ b`), `coreGen ξ ζ ρ p = (ρ p ∨ ξ) ∧ ζ`,
`nestGen a b x ξ ζ ρ p = rel a b x (coreGen ξ ζ ρ p)`, `xr a = gen (code a + 1)`
the readers of `wip/f0FreePLL.lean`, `gR = relB σ³⊥ xr` (`MovingTop.gR`).

    FreeInPLL a b x :  (∀ p, [a] ⊢ x p) ∧ (∀ p, [x p] ⊢ b) ∧
                         ∀ A B,  [A] ⊢ B  ⟺  [rel a b x A] ⊢ rel a b x B
    FreePLLIn a b :    ∃ x, (∀ p, x p variable-free) ∧ FreeInPLL a b x
                         (= `Endpoints.ClosedStep a b`)

### Task 1

    (P1) CoreLemmaPLL :  ξ, ζ ◯-free,  [ξ] ⊢ ζ,  [ζ] ⊬ ξ,  Fresh ρ ξ ζ
                           ⟹  FreeInPLL ξ ζ (coreGen ξ ζ ρ)
    (P2) NestPLLFree :   FreeInPLL a b x,  ξ, ζ ◯-free,  [ξ] ⊢ ζ,  [ζ] ⊬ ξ,  Fresh ρ ξ ζ
                           ⟹  FreeInPLL (rel a b x ξ) (rel a b x ζ) (nestGen a b x ξ ζ ρ)
                         (this is `Interval.NestPLL`, OPEN in `wip/f0FreeInterval.lean`)
    (P3) MainPLL :       a, b, x variable-free,  FreeInPLL a b x,  ξ, ζ ◯-free,  [ξ] ⊢ ζ,  [ζ] ⊬ ξ
                           ⟹  FreePLLIn (rel a b x ξ) (rel a b x ζ)
    (P4) BridgePLL3 :    FreeInPLL σ³⊥ ⊤ xr
    (P5) NestAllPLL :    the tower  (a₀, b₀, x₀) = (σ³⊥, ⊤, xr),
                           (a_{d+1}, b_{d+1}, x_{d+1}) = (rel_d ξ_d, rel_d ζ_d, nestGen a_d b_d x_d ξ_d ζ_d (freshRen ξ_d ζ_d)),
                         every (ξ_d, ζ_d) ◯-free with [ξ_d] ⊢ ζ_d, [ζ_d] ⊬ ξ_d (`TowerHyp`):  ∀ d,
                           FreeInPLL a_d b_d x_d,  x_d p variable-free,  [b_d] ⊬ a_d,
                           [a_d] ⊢ a_{d+1},  [a_{d+1}] ⊢ b_{d+1},  [b_{d+1}] ⊢ b_d
    NestOnePLL :         ξ, ζ ◯-free,  [ξ] ⊢ ζ,  [ζ] ⊬ ξ
                           ⟹  FreePLLIn (rel σ³⊥ ⊤ xr ξ) (rel σ³⊥ ⊤ xr ζ)

The ◯-free hypotheses, tested (expected REFUTED; the remark of the brief):

    CoreLemmaPLLAnyXi :    (P1) without "ξ ◯-free"   (witness ξ = ◯q, ζ = ⊤: [◯ξ] ⊢ ξ)
    CoreLemmaPLLAnyZeta :  (P1) without "ζ ◯-free"   (witness ξ = ⊥, ζ = ◯⊥: [ζ] ⊢ ◯ξ)
    CoreNoStrictPLL :      (P1) without "[ζ] ⊬ ξ"    (witness ξ = ζ = ⊥)

### Task 2

`Covers u v` is `F0.Covers` of `wip/f0Covers.lean`: `[u] ⊢ v`, `[v] ⊬ u`, and
every variable-free `x` with `[u] ⊢ x ⊢ v` is `⊣⊢ u` or `⊣⊢ v`.

    CoverSig3 :          Covers σ³⊥ (◯σ³⊥)                     (expected REFUTED)
    RangeNoCover :       [A] ⊢ B,  [B] ⊬ A  ⟹  ¬ Covers (gR A) (gR B)
    Sig3ImageNotCover :  c, d variable-free,  [c] ⊢ d,  [d] ⊬ c  ⟹  ¬ Covers (σ³c) (σ³d)
    RangeBelowSig2T5 :   [gR A] ⊢ σ²t5  ⟹  [A] ⊢ ⊥
                         (the σ²-image [σ³⊥, σ²t5] of the cover t3 ⋖ t5 meets the range of gR
                          only at its bottom)
    CoverSig2T5 :        Covers σ³⊥ (σ²t5)                      (OPEN, not attempted)

Status of every statement at Stage 1: OPEN (statements only, no theorem, no
`sorry`).

Status note: `wip/f0NestPLL-STATUS.md`.
-/

set_option autoImplicit false

open PLLFormula

namespace PLLND
namespace F0
namespace NestPLL

open SemUI Sig FreeHAn Base3 FreePLL MovingTop
open Interval (rel FreeInPLL topF Fresh coreGen nestGen freshRen ICopy TowerHyp)
open PLLND.LaxInfinite (atomFree)

/-! ## Task 1: the statements -/

/-- **`[a, b]` carries a faithful copy of PLL** (`◯` included) with variable-free
generators; the same as `Endpoints.ClosedStep a b`. -/
def FreePLLIn (a b : PLLFormula) : Prop :=
  ∃ x : String → PLLFormula, (∀ p, atomFree (x p) = true) ∧ FreeInPLL a b x

/-- **(P1) The core lemma for PLL**: for ◯-free `ξ`, `ζ` with `[ξ] ⊢ ζ`,
`[ζ] ⊬ ξ` and a fresh renaming `ρ`, the generators `(ρ p ∨ ξ) ∧ ζ` give a
faithful copy of PLL in `[ξ, ζ]`, all formulas, `◯` included. -/
def CoreLemmaPLL : Prop :=
  ∀ (ξ ζ : PLLFormula) (ρ : String → String), boxFree ξ = true → boxFree ζ = true →
    Deriv [ξ] ζ → ¬ Deriv [ζ] ξ → Fresh ρ ξ ζ → FreeInPLL ξ ζ (coreGen ξ ζ ρ)

/-- **(P2) Nesting for PLL, ◯-free endpoints**: `Interval.NestPLL`. -/
def NestPLLFree : Prop := Interval.NestPLL

/-- **(P3) The main theorem for PLL**: a faithful interval copy of PLL with
variable-free data contains a faithful copy of PLL, with variable-free
generators, in each strict sub-interval `[rel ξ, rel ζ]`, ◯-free `ξ`, `ζ`. -/
def MainPLL : Prop :=
  ∀ (a b : PLLFormula) (x : String → PLLFormula) (ξ ζ : PLLFormula),
    atomFree a = true → atomFree b = true → (∀ p, atomFree (x p) = true) → FreeInPLL a b x →
    boxFree ξ = true → boxFree ζ = true → Deriv [ξ] ζ → ¬ Deriv [ζ] ξ →
    FreePLLIn (rel a b x ξ) (rel a b x ζ)

/-- **(P4) The base copy of PLL as an interval copy**: `FreeInPLL σ³⊥ ⊤ xr`. -/
def BridgePLL3 : Prop := FreeInPLL (base 3) topF xr

/-- **The PLL tower** over the pairs `(ξs d, ζs d)`, starting from the readers'
copy `(σ³⊥, ⊤, xr)`. -/
def towerP (ξs ζs : Nat → PLLFormula) : Nat → ICopy
  | 0 => ⟨base 3, topF, xr⟩
  | d + 1 => (towerP ξs ζs d).step (ξs d) (ζs d)

/-- **(P5) Every finite depth**: each `[a_d, b_d]` carries a faithful copy of
PLL with variable-free generators, is non-degenerate, and contains the next. -/
def NestAllPLL : Prop :=
  ∀ ξs ζs : Nat → PLLFormula, TowerHyp ξs ζs → ∀ d : Nat,
    FreeInPLL (towerP ξs ζs d).a (towerP ξs ζs d).b (towerP ξs ζs d).x ∧
    (∀ p, atomFree ((towerP ξs ζs d).x p) = true) ∧
    ¬ Deriv [(towerP ξs ζs d).b] (towerP ξs ζs d).a ∧
    Deriv [(towerP ξs ζs d).a] (towerP ξs ζs (d + 1)).a ∧
    Deriv [(towerP ξs ζs (d + 1)).a] (towerP ξs ζs (d + 1)).b ∧
    Deriv [(towerP ξs ζs (d + 1)).b] (towerP ξs ζs d).b

/-- **Depth one inside the base copy**: for ◯-free `ξ < ζ`, the interval
`[rel σ³⊥ ⊤ xr ξ, rel σ³⊥ ⊤ xr ζ]` carries a faithful copy of PLL. -/
def NestOnePLL : Prop :=
  ∀ ξ ζ : PLLFormula, boxFree ξ = true → boxFree ζ = true → Deriv [ξ] ζ → ¬ Deriv [ζ] ξ →
    FreePLLIn (rel (base 3) topF xr ξ) (rel (base 3) topF xr ζ)

/-! ### The hypotheses of (P1), each dropped -/

/-- (P1) with `◯` allowed in `ξ`. -/
def CoreLemmaPLLAnyXi : Prop :=
  ∀ (ξ ζ : PLLFormula) (ρ : String → String), boxFree ζ = true →
    Deriv [ξ] ζ → ¬ Deriv [ζ] ξ → Fresh ρ ξ ζ → FreeInPLL ξ ζ (coreGen ξ ζ ρ)

/-- (P1) with `◯` allowed in `ζ`. -/
def CoreLemmaPLLAnyZeta : Prop :=
  ∀ (ξ ζ : PLLFormula) (ρ : String → String), boxFree ξ = true →
    Deriv [ξ] ζ → ¬ Deriv [ζ] ξ → Fresh ρ ξ ζ → FreeInPLL ξ ζ (coreGen ξ ζ ρ)

/-- (P1) without `[ζ] ⊬ ξ`. -/
def CoreNoStrictPLL : Prop :=
  ∀ (ξ ζ : PLLFormula) (ρ : String → String), boxFree ξ = true → boxFree ζ = true →
    Deriv [ξ] ζ → Fresh ρ ξ ζ → FreeInPLL ξ ζ (coreGen ξ ζ ρ)

/-! ## Task 2: the statements -/

/-- **Is `[σ³⊥, ◯σ³⊥]` a cover?** (the `σ³`-image of `⊥ ⋖ ◯⊥`). -/
def CoverSig3 : Prop := Covers (base 3) (.somehow (base 3))

/-- **No cover has both ends in the range of the readers' copy `gR`.** -/
def RangeNoCover : Prop :=
  ∀ A B : PLLFormula, Deriv [A] B → ¬ Deriv [B] A → ¬ Covers (gR A) (gR B)

/-- **No `σ³`-image of a strict pair of F0 is a cover.** -/
def Sig3ImageNotCover : Prop :=
  ∀ c d : PLLFormula, atomFree c = true → atomFree d = true → Deriv [c] d → ¬ Deriv [d] c →
    ¬ Covers (sigN 3 c) (sigN 3 d)

/-- **Below `σ²t5` the range of `gR` has only its bottom.** -/
def RangeBelowSig2T5 : Prop :=
  ∀ A : PLLFormula, Deriv [gR A] (sigN 2 t5) → Deriv [A] .falsePLL

/-- **OPEN, not attempted**: is `σ³⊥ ⋖ σ²t5`, the `σ²`-image of `t3 ⋖ t5`? -/
def CoverSig2T5 : Prop := Covers (base 3) (sigN 2 t5)

end NestPLL
end F0
end PLLND
