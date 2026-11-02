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

## Results (Stage 3)

All pins `[propext, Quot.sound]`; no `Classical.choice`, no `sorry`, no
`native_decide`.  `#axiom_sweep [wip.f0NestPLL] allowing [propext, Quot.sound]`
passes on all 127 declarations; with `allowing []` 70 escape (the gate watched
failing).

**PROVED**: (P1) `coreLemmaPLL`; (P2) `nestPLL`, hence `Interval.NestPLL`
(`nestPLL_interval`); (P3) `mainPLL`; (P4) `bridgePLL3`; (P5) `nestAllPLL`
(with `freePLLIn_tower`); `nestOnePLL`; and, in the coordinates of the
readers' copy `gR` (added at stage 3),

    ξ, ζ ◯-free,  [ξ] ⊢ ζ,  [ζ] ⊬ ξ   ⟹   FreePLLIn (gR ξ) (gR ζ)      (pllInGRInterval)

Task 2: `rangeNoCover`, `sig3ImageNotCover`, `rangeBelowSig2T5`,
`sig2t5_not_in_range`.  Added at stage 3: `noPLLBelowBox`, `noPLLInSig3Box`,
`hωInSig3Box`: the interval `[σ³⊥, ◯σ³⊥]` carries `H_ω` but no sub-interval of
it carries a faithful copy of PLL.

**REFUTED**: `CoreLemmaPLLAnyXi`, `CoreLemmaPLLAnyZeta`, `CoreNoStrictPLL`,
`CoverSig3` (`not_coverSig3`, and again `not_coverSig3'`).

**OPEN**: `CoverSig2T5` (not attempted).

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
/-! ## Stage 2: the designed cells (refutation stage, CLAUDE.md rules 7 and 9)

Task 1, read off the pen argument; no sweep.

* (i) Level one inside the base copy: `ξ = p₀ ∧ p₁`, `ζ = p₁` (`p₀ = ""`,
  `p₁ = "\x00"`), renaming `ρc1` (`"" ↦ "\x01"`, `"\x00" ↦ "\x02"`), as in
  `Interval.Cells`; the base copy is now the readers' `xr` (`a ↦ gen (code a + 1)`)
  and the targets contain `◯`: `O1 = ◯p → p`, `O3 = ◯(p ∨ q) → ◯p ∨ ◯q`
  (`p = ""`, `q = "\x00"`).  `[rel₁ ⊤] ⊬ rel₁ O1` (`cell1_O1`, 13 worlds) and
  `[rel₁ ⊤] ⊬ rel₁ O3` (`cell1_O3`, 17 worlds).  The PLL theorem
  `◯◯p → ◯p` transfers (`cell1_pos`), and the table of `cell1_O1` does not
  refute it (`gate_watch`, the check watched failing).
* (ii) Depth two: `[rel₁ ⊥, rel₁ p]` with renaming `ρc2` (`"" ↦ "\x00"`),
  target `O1`: `[rel₂ ⊤] ⊬ rel₂ O1` (`cell2_O1`, 15 worlds).
* (iii) The negative test `ξ = ζ`: no `FreeInPLL a a x` (`cell_diagPLL`), so
  the core lemma without `[ζ] ⊬ ξ` is REFUTED (`not_coreNoStrictPLL`), also
  at `ξ = ζ = p₀ ∧ p₁` in the base copy (`cell3_base3P`).
* The ◯-free hypotheses.  A `◯`-fixed bottom (`[◯a] ⊢ a`) admits no faithful
  copy (`not_freeInPLL_of_fixed`, through `Endpoints.necBox`), nor does a top
  below `◯a` (`not_freeInPLL_of_top_box`: `[rel ⊤] ⊢ rel ◯⊥`).  Hence (P1)
  without "ξ ◯-free" is REFUTED at `ξ = ◯p`, `ζ = ⊤`
  (`not_coreLemmaPLLAnyXi`) and without "ζ ◯-free" at `ξ = ⊥`, `ζ = ◯⊥`
  (`not_coreLemmaPLLAnyZeta`); both pairs satisfy every other hypothesis.

The tables are the pen proof's construction.  The PLL countermodel of `C`
(`O1`: one world outside `S`; `O3`: `FreePLL.K3`) is glued into the one-world
countermodel of `[ζ] ⊢ ξ`: each copy forces `p₁`, refutes `p₀`, and carries
`ρ p` iff it forces `p`.  The worlds above `w` force `ξ`, hence every
relativised formula, and are dropped.  Then the readers' gadget over the
result, `gadP R rd K`: `Interval.Cells.gadW` with the copies carrying `K`'s
own `S`, the reader `m_r` for the atom `rd[r-1]` (code `r - 1`), read by
`gen r` (`readsP`).

Task 2: candidates `x` with `[σ³⊥] ⊢ x ⊢ ◯σ³⊥`.

* `x₁ = ◯σ³⊥ ∧ gen 1`, the image `gR (◯⊥ ∧ p)`, is strictly between:
  `[x₁] ⊬ σ³⊥` (`c1_not_lo`, the gadget over a one-world model of `p` outside
  `S`) and `[◯σ³⊥] ⊬ x₁` (`c1_not_hi`, over the empty one-world model).  So
  **`CoverSig3` is REFUTED** (`not_coverSig3`).
* The brief's `x = ◯σ³⊥ ∧ (σ³⊥ ∨ y)`, `y ∈ {¬◯⊥, t4, t3}`, all collapse to the
  bottom, `[x] ⊢ σ³⊥` (`cy_ne_lo`, `cy_t4_lo`, `cy_t3_lo`), because
  `y ⊢ t5 ⊢ σ²⊥ ⊢ σ³⊥`; and `[◯σ³⊥] ⊬ x` (`cy_ne_hi`, `cy_t4_hi`, `cy_t3_hi`,
  from `[◯σ³⊥] ⊬ σ³⊥`, `base3_not_box`).  The subframe tableau
  (`_out/nestprobe.lean`, untrusted) gave the same six verdicts.
* `σ³⊥ < σ²t5` (`sig2t5_lo`, `sig2t5_strict`): the strict pair of the OPEN
  candidate `CoverSig2T5`. -/

namespace PLLND
namespace F0
namespace NestPLL

open SemUI Sig FreeHAn Base3 FreePLL MovingTop
open Interval (rel FreeInPLL topF Fresh coreGen nestGen freshRen ICopy TowerHyp)
open PLLND.LaxInfinite (atomFree)

section Cells

set_option maxRecDepth 100000

namespace Cells

open Interval.Cells (ξc ζc ρc1 ρc2 gadW upSS rdS)

/-- **The readers' gadget over a table `K`**: `Interval.Cells.gadW` with the
copies carrying `K`'s own `S`. -/
def gadP (R : Nat) (rd : List String) (K : SubTab.SubCM) : SubTab.SubCM :=
  { gadW R rd K with
    S := (List.range (2 * R + 6)).map (upSS R) ++ (List.range K.n).map K.SB }

/-- The readers `gen 1 … gen R` read the valuation at every copy, and the
copies carry `K`'s `S`. -/
def readsP (R : Nat) (rd : List String) (K : SubTab.SubCM) : Bool :=
  (List.range K.n).all fun k =>
    ((List.range R).all fun r =>
      (gadP R rd K).forceB (2 * R + 6 + k) (gen (r + 1)) == K.vB (rdS rd (r + 1)) k) &&
    ((gadP R rd K).SB (2 * R + 6 + k) == K.SB k)

/-- Level one, `a₁ = rel σ³⊥ ⊤ xr (p₀ ∧ p₁)`. -/
def a1P : PLLFormula := rel (base 3) topF xr ξc

/-- Level one, `b₁ = rel σ³⊥ ⊤ xr p₁`. -/
def b1P : PLLFormula := rel (base 3) topF xr ζc

/-- Level one, `x₁ = nestGen σ³⊥ ⊤ xr ξ ζ ρc1`. -/
def x1P : String → PLLFormula := nestGen (base 3) topF xr ξc ζc ρc1

/-- Level two, `a₂ = rel₁ ⊥`. -/
def a2P : PLLFormula := rel a1P b1P x1P .falsePLL

/-- Level two, `b₂ = rel₁ p`. -/
def b2P : PLLFormula := rel a1P b1P x1P (.prop "")

/-- Level two, `x₂ = nestGen a₁ b₁ x₁ ⊥ p ρc2`. -/
def x2P : String → PLLFormula := nestGen a1P b1P x1P .falsePLL (.prop "") ρc2

/-- The PLL theorem `◯◯p → ◯p`. -/
def CP : PLLFormula :=
  (PLLFormula.somehow (PLLFormula.somehow pA)).ifThen (PLLFormula.somehow pA)

/-- The glued model for `O1` at level one: one world outside `S`, `p₁` only. -/
def KO1 : SubTab.SubCM :=
  { n := 1, root := 0, le := [[true]], S := [false], val := [["\x00"]] }

/-- The glued model for `O3` at level one: `FreePLL.K3` with `p₁` everywhere,
`ρc1 p = "\x01"` at the `p`-world, `ρc1 q = "\x02"` at the `q`-world. -/
def KO3 : SubTab.SubCM :=
  { n := 3, root := 0, le := [[true, true, true], [false, true, false], [false, false, true]],
    S := [false, true, true], val := [["\x00"], ["\x00", "\x01"], ["\x00", "\x02"]] }

/-- The glued model for `O1` at level two (glued twice): one world outside
`S`, `p₁` and `ρc1 p₀ = "\x01"`. -/
def KT1 : SubTab.SubCM :=
  { n := 1, root := 0, le := [[true]], S := [false], val := [["\x00", "\x01"]] }

/-- The atoms read by `gen 1, gen 2, gen 3`. -/
def rd3 : List String := ["", "\x00", "\x01"]

/-- The atoms read by `gen 1, …, gen 4`. -/
def rd4 : List String := ["", "\x00", "\x01", "\x02"]

theorem reads_KO1 : readsP 3 rd3 KO1 = true := by decide +kernel

theorem reads_KO3 : readsP 4 rd4 KO3 = true := by decide +kernel

theorem reads_KT1 : readsP 4 rd4 KT1 = true := by decide +kernel

/-- Cell (i), `O1`, the implication form (13 worlds). -/
theorem cell1_O1_imp : ¬ Deriv [] ((rel a1P b1P x1P topF).ifThen (rel a1P b1P x1P O1)) :=
  SubTab.no.verdict _ (gadP 3 rd3 KO1)

/-- **Cell (i) PASSES, `O1`**: `[rel₁ ⊤] ⊬ rel₁(◯p → p)`, as `⊬ ◯p → p`. -/
theorem cell1_O1 : ¬ Deriv [rel a1P b1P x1P topF] (rel a1P b1P x1P O1) := fun h =>
  cell1_O1_imp (Deriv.impIntro h)

/-- Cell (i), `O3`, the implication form (17 worlds). -/
theorem cell1_O3_imp : ¬ Deriv [] ((rel a1P b1P x1P topF).ifThen (rel a1P b1P x1P O3)) :=
  SubTab.no.verdict _ (gadP 4 rd4 KO3)

/-- **Cell (i) PASSES, `O3`**: `[rel₁ ⊤] ⊬ rel₁(◯(p ∨ q) → ◯p ∨ ◯q)`. -/
theorem cell1_O3 : ¬ Deriv [rel a1P b1P x1P topF] (rel a1P b1P x1P O3) := fun h =>
  cell1_O3_imp (Deriv.impIntro h)

/-- Cell (ii), the implication form (15 worlds). -/
theorem cell2_O1_imp : ¬ Deriv [] ((rel a2P b2P x2P topF).ifThen (rel a2P b2P x2P O1)) :=
  SubTab.no.verdict _ (gadP 4 rd4 KT1)

/-- **Cell (ii) PASSES**: `[rel₂ ⊤] ⊬ rel₂(◯p → p)` at depth two. -/
theorem cell2_O1 : ¬ Deriv [rel a2P b2P x2P topF] (rel a2P b2P x2P O1) := fun h =>
  cell2_O1_imp (Deriv.impIntro h)

/-- PLL: `⊢ ◯◯p → ◯p`. -/
theorem pll_CP : Deriv [] CP :=
  Deriv.impIntro (Interval.deriv_of_sem fun M _ _ hv u hu hS => hv u hu hS u (M.refl u) hS)

/-- **Cell (i), the theorem**: `[rel₁ ⊤] ⊢ rel₁(◯◯p → ◯p)`. -/
theorem cell1_pos : Deriv [rel a1P b1P x1P topF] (rel a1P b1P x1P CP) :=
  Interval.deriv_of_sem fun M _ _ hv =>
    ⟨fun _ _ hu => ⟨fun w huw hwS => (hu.1 w huw hwS).1 w (M.refl w) hwS, hu.2⟩, hv.2⟩

/-- The check watched failing: the table of `cell1_O1` does not refute the
transferred theorem. -/
theorem gate_watch :
    (gadP 3 rd3 KO1).refutes ((rel a1P b1P x1P topF).ifThen (rel a1P b1P x1P CP)) = false := by
  decide +kernel

end Cells

/-! ### Cell (iii) and the ◯-free hypotheses -/

/-- **Cell (iii) FAILS, as designed**: no translation into `[a, a]` is
faithful on PLL. -/
theorem cell_diagPLL (a : PLLFormula) (x : String → PLLFormula) : ¬ FreeInPLL a a x :=
  fun ⟨_, _, hf⟩ => Interval.ipc_top_bot ((hf topF .falsePLL).mpr (Interval.rel_top_bot_diag a x))

/-- **REFUTED: (P1) without `[ζ] ⊬ ξ`** (`ξ = ζ = ⊥`, `ρ = id`). -/
theorem not_coreNoStrictPLL : ¬ CoreNoStrictPLL := fun h =>
  cell_diagPLL .falsePLL _ (h .falsePLL .falsePLL id rfl rfl (Deriv.iden (.head _))
    ⟨fun _ _ e => e, fun _ => ⟨rfl, rfl⟩⟩)

/-- The base-copy instance of (iii): `ξ = ζ = p₀ ∧ p₁`. -/
theorem cell3_base3P :
    ¬ FreeInPLL Cells.a1P Cells.a1P (nestGen (base 3) topF xr Interval.Cells.ξc
      Interval.Cells.ξc Interval.Cells.ρc1) :=
  cell_diagPLL _ _

/-- **A `◯`-fixed bottom admits no faithful copy of PLL** (`necBox`). -/
theorem not_freeInPLL_of_fixed {a b : PLLFormula} {x : String → PLLFormula}
    (h : Deriv [.somehow a] a) : ¬ FreeInPLL a b x := fun hF =>
  Endpoints.necBox a b h (Endpoints.copy_of_free hF)

/-- `[⊤] ⊬ ◯⊥`. -/
theorem nd_top_box : ¬ Deriv [topF] (PLLFormula.somehow .falsePLL) := fun h =>
  Endpoints.nd_e (of_top h)

/-- **A top below `◯a` admits no faithful copy of PLL**: `rel ⊤ ⊢ b ⊢ ◯a`, so
`[rel ⊤] ⊢ rel ◯⊥ = ◯a ∧ b`, while `[⊤] ⊬ ◯⊥`. -/
theorem not_freeInPLL_of_top_box {a b : PLLFormula} {x : String → PLLFormula}
    (h : Deriv [b] (.somehow a)) : ¬ FreeInPLL a b x := fun ⟨_, _, hf⟩ =>
  nd_top_box ((hf topF (.somehow .falsePLL)).mpr
    (Deriv.andIntro (Deriv.cutHead (Deriv.andElim2 (Deriv.iden (.head _))) h)
      (Deriv.andElim2 (Deriv.iden (.head _)))))

/-- The atom `p = ""`. -/
def qP : PLLFormula := .prop ""

/-- `⊬ ⊤ → ◯p` (one world, in `S`). -/
theorem nd_top_boxq_imp : ¬ Deriv [] (topF.ifThen (PLLFormula.somehow qP)) :=
  SubTab.no.verdict _ { n := 1, root := 0, le := [[true]], S := [true], val := [[]] }

/-- `[◯◯A] ⊢ ◯A`. -/
theorem box_box (A : PLLFormula) : Deriv [.somehow (.somehow A)] (.somehow A) :=
  Interval.deriv_of_sem fun M _ _ hv u hu hS => hv u hu hS u (M.refl u) hS

/-- **REFUTED: (P1) with `◯` in `ξ`** (`ξ = ◯p`, `ζ = ⊤`). -/
theorem not_coreLemmaPLLAnyXi : ¬ CoreLemmaPLLAnyXi := fun h =>
  not_freeInPLL_of_fixed (box_box qP)
    (h (.somehow qP) topF (freshRen _ _) rfl (le_top _)
      (fun hd => nd_top_boxq_imp (Deriv.impIntro hd)) (Interval.fresh_freshRen _ _))

/-- **REFUTED: (P1) with `◯` in `ζ`** (`ξ = ⊥`, `ζ = ◯⊥`). -/
theorem not_coreLemmaPLLAnyZeta : ¬ CoreLemmaPLLAnyZeta := fun h =>
  not_freeInPLL_of_top_box
    (Deriv.iden (.head _) : Deriv [PLLFormula.somehow .falsePLL] (PLLFormula.somehow .falsePLL))
    (h .falsePLL (.somehow .falsePLL) (freshRen _ _) rfl (bot_le _) nd_e_bot
      (Interval.fresh_freshRen _ _))

/-! ### Task 2: the candidates -/

/-- `x₁ = ◯σ³⊥ ∧ gen 1 = gR (◯⊥ ∧ p)`. -/
def xC1 : PLLFormula := (PLLFormula.somehow (base 3)).and (gen 1)

/-- The brief's candidates `◯σ³⊥ ∧ (σ³⊥ ∨ y)`. -/
def xC (y : PLLFormula) : PLLFormula := (PLLFormula.somehow (base 3)).and ((base 3).or y)

/-- One world outside `S`, `p = a0` true. -/
def KA : SubTab.SubCM := { n := 1, root := 0, le := [[true]], S := [false], val := [[a0]] }

theorem xC1_vf : atomFree xC1 = true :=
  (Bool.and_eq_true_iff.mpr ⟨b3_vf, gen_vf 1⟩ : (atomFree (base 3) && atomFree (gen 1)) = true)

theorem c1_lo : Deriv [base 3] xC1 := Deriv.andIntro (b3_le_gen 0) (b3_le_gen 1)

theorem c1_hi : Deriv [xC1] (.somehow (base 3)) := Deriv.andElim1 (Deriv.iden (.head _))

theorem c1_not_lo_imp : ¬ Deriv [] (xC1.ifThen (base 3)) := SubTab.no.verdict _ (gadT KA)

/-- **`[x₁] ⊬ σ³⊥`** (the gadget over `KA`, 11 worlds). -/
theorem c1_not_lo : ¬ Deriv [xC1] (base 3) := fun h => c1_not_lo_imp (Deriv.impIntro h)

theorem c1_not_hi_imp : ¬ Deriv [] ((PLLFormula.somehow (base 3)).ifThen xC1) :=
  SubTab.no.verdict _ (gadT FreePLL.K1)

/-- **`[◯σ³⊥] ⊬ x₁`** (the gadget over the empty one-world model, 11 worlds). -/
theorem c1_not_hi : ¬ Deriv [.somehow (base 3)] xC1 := fun h => c1_not_hi_imp (Deriv.impIntro h)

/-- **REFUTED: `[σ³⊥, ◯σ³⊥]` is not a cover**: `x₁` lies strictly between. -/
theorem not_coverSig3 : ¬ CoverSig3 := fun ⟨_, _, h⟩ =>
  (h xC1 xC1_vf c1_lo c1_hi).elim (fun i => c1_not_lo i.1) (fun i => c1_not_hi i.2)

theorem base3_not_box_imp : ¬ Deriv [] ((PLLFormula.somehow (base 3)).ifThen (base 3)) :=
  SubTab.no.verdict _ (gadT FreePLL.K1)

/-- `[◯σ³⊥] ⊬ σ³⊥` (the gadget over the empty one-world model). -/
theorem base3_not_box : ¬ Deriv [.somehow (base 3)] (base 3) := fun h =>
  base3_not_box_imp (Deriv.impIntro h)

theorem xC_bounds (y : PLLFormula) :
    Deriv [base 3] (xC y) ∧ Deriv [xC y] (.somehow (base 3)) :=
  ⟨Deriv.andIntro (b3_le_gen 0) (Deriv.orIntro1 (Deriv.iden (.head _))),
   Deriv.andElim1 (Deriv.iden (.head _))⟩

/-- A candidate with `y ⊢ σ³⊥` collapses to the bottom. -/
theorem xC_lo (y : PLLFormula) (hy : Deriv [y] (base 3)) : Deriv [xC y] (base 3) :=
  Deriv.orElim (Deriv.andElim2 (Deriv.iden (.head _))) (Deriv.iden (.head _)) hy.toHead

theorem xC_hi (y : PLLFormula) (hy : Deriv [y] (base 3)) : ¬ Deriv [.somehow (base 3)] (xC y) :=
  fun h => base3_not_box (Deriv.cutHead h (xC_lo y hy))

/-- `t3 ⊢ σ²⊥ = ◯t3 ∨ (◯t3 → t3)`. -/
theorem t3_b2 : Deriv [t3] (base 2) := Deriv.orIntro2 (Deriv.impIntro (Deriv.iden (.tail _ (.head _))))

/-- `σ²⊥ ⊢ σ³⊥ = ◯σ²⊥ ∨ (◯σ²⊥ → σ²⊥)`. -/
theorem b2_b3 : Deriv [base 2] (base 3) :=
  Deriv.orIntro2 (Deriv.impIntro (Deriv.iden (.tail _ (.head _))))

/-- `t5 ⊢ σ²⊥` (through `t5 ⊢ g1 = ◯t3 → t3`, `SigOnto.t5_le_g1F`). -/
theorem t5_b2 : Deriv [t5] (base 2) := Deriv.orIntro2 SigOnto.t5_le_g1F

theorem ne_b3 : Deriv [ne] (base 3) :=
  Deriv.cutHead (Deriv.cutHead (Deriv.orIntro2 (Deriv.iden (.head _)) : Deriv [ne] t3) t3_b2) b2_b3

theorem t4_b3 : Deriv [t4] (base 3) :=
  Deriv.cutHead (Deriv.cutHead (Deriv.orIntro2 (Deriv.iden (.head _)) : Deriv [t4] t5) t5_b2) b2_b3

theorem t3_b3 : Deriv [t3] (base 3) := Deriv.cutHead t3_b2 b2_b3

/-- `y = ¬◯⊥`: collapses, `[x] ⊢ σ³⊥`. -/
theorem cy_ne_lo : Deriv [xC ne] (base 3) := xC_lo ne ne_b3

/-- `y = t4`: collapses. -/
theorem cy_t4_lo : Deriv [xC t4] (base 3) := xC_lo t4 t4_b3

/-- `y = t3`: collapses. -/
theorem cy_t3_lo : Deriv [xC t3] (base 3) := xC_lo t3 t3_b3

theorem cy_ne_hi : ¬ Deriv [.somehow (base 3)] (xC ne) := xC_hi ne ne_b3

theorem cy_t4_hi : ¬ Deriv [.somehow (base 3)] (xC t4) := xC_hi t4 t4_b3

theorem cy_t3_hi : ¬ Deriv [.somehow (base 3)] (xC t3) := xC_hi t3 t3_b3

/-- `σ³⊥ ⊢ σ²t5 = σ³⊥ ∨ (σ³⊥ → ◯σ²⊥)`. -/
theorem sig2t5_lo : Deriv [base 3] (sigN 2 t5) := Deriv.orIntro1 (Deriv.iden (.head _))

/-- `σ²t5 ⊬ σ³⊥` (`σ²` reflects, `t5 ⊬ t3`). -/
theorem sig2t5_strict : ¬ Deriv [sigN 2 t5] (base 3) := fun h =>
  nd_t5_t3 (sigN_reflects_ctx 2 (φ := t5) (ψ := t3) h)

end Cells

end NestPLL
end F0
end PLLND

/-! ## Axiom pins: stage 2 -/

#axioms_within PLLND.F0.NestPLL.Cells.reads_KO1 [propext, Quot.sound]
#axioms_within PLLND.F0.NestPLL.Cells.reads_KO3 [propext, Quot.sound]
#axioms_within PLLND.F0.NestPLL.Cells.reads_KT1 [propext, Quot.sound]
#axioms_within PLLND.F0.NestPLL.Cells.cell1_O1 [propext, Quot.sound]
#axioms_within PLLND.F0.NestPLL.Cells.cell1_O3 [propext, Quot.sound]
#axioms_within PLLND.F0.NestPLL.Cells.cell2_O1 [propext, Quot.sound]
#axioms_within PLLND.F0.NestPLL.Cells.pll_CP [propext, Quot.sound]
#axioms_within PLLND.F0.NestPLL.Cells.cell1_pos [propext, Quot.sound]
#axioms_within PLLND.F0.NestPLL.Cells.gate_watch [propext, Quot.sound]
#axioms_within PLLND.F0.NestPLL.cell_diagPLL [propext, Quot.sound]
#axioms_within PLLND.F0.NestPLL.not_coreNoStrictPLL [propext, Quot.sound]
#axioms_within PLLND.F0.NestPLL.cell3_base3P [propext, Quot.sound]
#axioms_within PLLND.F0.NestPLL.not_freeInPLL_of_fixed [propext, Quot.sound]
#axioms_within PLLND.F0.NestPLL.not_freeInPLL_of_top_box [propext, Quot.sound]
#axioms_within PLLND.F0.NestPLL.not_coreLemmaPLLAnyXi [propext, Quot.sound]
#axioms_within PLLND.F0.NestPLL.not_coreLemmaPLLAnyZeta [propext, Quot.sound]
#axioms_within PLLND.F0.NestPLL.c1_not_lo [propext, Quot.sound]
#axioms_within PLLND.F0.NestPLL.c1_not_hi [propext, Quot.sound]
#axioms_within PLLND.F0.NestPLL.not_coverSig3 [propext, Quot.sound]
#axioms_within PLLND.F0.NestPLL.base3_not_box [propext, Quot.sound]
#axioms_within PLLND.F0.NestPLL.cy_ne_lo [propext, Quot.sound]
#axioms_within PLLND.F0.NestPLL.cy_t4_lo [propext, Quot.sound]
#axioms_within PLLND.F0.NestPLL.cy_t3_lo [propext, Quot.sound]
#axioms_within PLLND.F0.NestPLL.cy_ne_hi [propext, Quot.sound]
#axioms_within PLLND.F0.NestPLL.cy_t4_hi [propext, Quot.sound]
#axioms_within PLLND.F0.NestPLL.cy_t3_hi [propext, Quot.sound]
#axioms_within PLLND.F0.NestPLL.sig2t5_lo [propext, Quot.sound]
#axioms_within PLLND.F0.NestPLL.sig2t5_strict [propext, Quot.sound]

/-! ## Stage 3: the proofs

**Task 1.**  The pen argument of the brief, mechanised as planned.

* Preservation (`rel_preservesPLL`): `relB_preservesO` of `wip/f0FreePLL.lean`
  (all formulas), through `rel_iff_relB_gen` of `wip/f0MovingTop.lean` (at a
  world forcing the top, `rel` and `relB` agree on every formula, `◯`
  included), since every `rel`-image forces the top (`force_rel_b`).
* Reflection (`core_reflectsPLL`): the gluing `Interval.Glue.G` of the IPC
  proof unchanged.  The copy of `K` keeps `K`'s own `S` (`Glue.SG`), so the
  relativisation lemma with `◯` (`relB_transferO`) applies with
  `hS : inl k ∈ S ⟺ k ∈ K.S` by `Iff.rfl`; `Glue.collapse` is used for `ξ`,
  `ζ` only, which is where "◯-free" enters.
* Nesting (`nestPLL`), main theorem (`mainPLL`), bridge (`bridgePLL3`), depth
  one (`nestOnePLL`) and the tower (`nestAllPLL`): the IPC proofs with `FreeIn`
  replaced by `FreeInPLL`; `rel_comp` already covered `◯`.

**Task 2.**  `rangeNoCover`: `gR (B ∧ (A ∨ q))`, `q` fresh, lies strictly
inside `[gR A, gR B]` (PLL with the atom `q` set true, respectively false, on a
countermodel of `[B] ⊢ A`; then the faithfulness of `gR`).  `sig3ImageNotCover`
is its instance at closed `A`, `B` (`gR c = σ³c`, `Endpoints.gR_closed`).
`rangeBelowSig2T5`: every copy world of the readers' gadget refutes `σ²t5`
(it sees the `S`-killer, which forces `σ³⊥` and refutes `◯σ²⊥`).

**Added at stage 3** (the second half of Matthew's question, "such intervals
inside every interval"):

    NoPLLBelowBox :   [b] ⊢ ◯a,  [a] ⊢ a′,  [b′] ⊢ b  ⟹  ¬ FreeInPLL a′ b′ x
    NoPLLInSig3Box :  no sub-interval of [σ³⊥, ◯σ³⊥] carries a faithful copy of PLL
    HωInSig3Box :     [σ³⊥, ◯σ³⊥] carries a faithful copy of H_ω (`Interval.FreeHAωIn`)
    PLLInGRInterval : ξ, ζ ◯-free, [ξ] ⊢ ζ, [ζ] ⊬ ξ  ⟹  FreePLLIn (gR ξ) (gR ζ)

So "a faithful copy of PLL inside every interval" is REFUTED in this form: the
interval `[σ³⊥, ◯σ³⊥]` contains `H_ω` but no sub-interval carrying PLL. -/

namespace PLLND
namespace F0
namespace NestPLL

open SemUI Sig FreeHAn Base3 FreePLL MovingTop
open Interval (rel FreeInPLL topF Fresh coreGen nestGen freshRen ICopy TowerHyp sem_of_deriv
  deriv_of_sem deriv_congr force_rel_b rel_comp)
open PLLND.LaxInfinite (atomFree)
open SubframeModel.CF (FinDec)

/-! ### Stage 3 (a): preservation, all formulas -/

/-- **Preservation (`⟹`), `◯` included**: for `a ≤ x p ≤ b` in every model,
`[A] ⊢ B` gives `[rel a b x A] ⊢ rel a b x B`. -/
theorem rel_preservesPLL (a b : PLLFormula) (x : String → PLLFormula)
    (hax : ∀ (M : SubframeModel) v p, M.force v a → M.force v (x p))
    (hxb : ∀ (M : SubframeModel) v p, M.force v (x p) → M.force v b)
    {A B : PLLFormula} (hd : Deriv [A] B) : Deriv [rel a b x A] (rel a b x B) := by
  have hR := relB_preservesO a x (fun M v p hv => hax M v p hv) hd
  refine deriv_of_sem fun M _ v hv => ?_
  have hb := force_rel_b M a b x (fun u hu => hxb M u "" (hax M u "" hu)) (hxb M) A v hv
  exact (rel_iff_relB_gen M a b x x (fun _ _ _ => Iff.rfl) B v hb).mpr
    (sem_of_deriv hR M v ((rel_iff_relB_gen M a b x x (fun _ _ _ => Iff.rfl) A v hb).mp hv))

/-! ### Stage 3 (b): the core lemma for PLL -/

/-- **The core lemma, `⟸`, by the gluing, `◯` included**: in the glued model
the copy of `u` forces `rel ξ ζ y A` iff `u ⊩ A`, for every `A`. -/
theorem core_reflectsPLL {ξ ζ : PLLFormula} {ρ : String → String} (hξ : boxFree ξ = true)
    (hζ : boxFree ζ = true) (hle : Deriv [ξ] ζ) (hstrict : ¬ Deriv [ζ] ξ) (hfr : Fresh ρ ξ ζ)
    {A B : PLLFormula}
    (hd : Deriv [rel ξ ζ (coreGen ξ ζ ρ) A] (rel ξ ζ (coreGen ξ ζ ρ) B)) : Deriv [A] B := by
  have h0 : ¬ Deriv [] (ζ.ifThen ξ) := fun h =>
    hstrict (Deriv.impElim (h.rename fun _ h => absurd h List.not_mem_nil) (Deriv.iden (.head _)))
  obtain ⟨N, hN, k, hk⟩ := SubframeModel.CF.exists_countermodel h0
  obtain ⟨w₁, _, hw₁ζ, hw₁ξ⟩ := SubframeModel.CF.exists_of_not_force_imp hk
  obtain ⟨w, hw₁w, hwξ, hmax⟩ := Interval.exists_max_not N ξ _ w₁ (Nat.le_refl _) hw₁ξ
  have hwζ : N.force w ζ := SubframeModel.force_mono N ζ hw₁w hw₁ζ
  have hoξ : ∀ p, Interval.occ (ρ p) ξ = false := fun p => (hfr.2 p).1
  have hoζ : ∀ p, Interval.occ (ρ p) ζ = false := fun p => (hfr.2 p).2
  refine deriv_of_sem fun K _ u hu => ?_
  let Gm := Interval.Glue.G N w ξ K ρ
  have cξ := Interval.Glue.collapse (K := K) (ρ := ρ) hmax ξ hξ hoξ
  have cζ := Interval.Glue.collapse (K := K) (ρ := ρ) hmax ζ hζ hoζ
  have hb : ∀ u' : K.W, ¬ Gm.force (.inl u') ξ := fun u' h => hwξ ((cξ (.inl u')).mp h)
  have hz : ∀ u' : K.W, Gm.force (.inl u') ζ := fun u' => (cζ (.inl u')).mpr hwζ
  have hbx : ∀ (v : Gm.W) p, Gm.force v ξ → Gm.force v (coreGen ξ ζ ρ p) := fun v _ hv =>
    ⟨Or.inr hv, sem_of_deriv hle Gm v hv⟩
  have hback : ∀ (u' : K.W) (v : Gm.W), Gm.le (.inl u') v →
      Gm.force v ξ ∨ ∃ j, K.le u' j ∧ Sum.inl j = v := by
    intro u' v hv
    cases v with
    | inl j => exact Or.inr ⟨j, hv, rfl⟩
    | inr n => exact Or.inl ((cξ (.inr n)).mpr hv.2)
  have hatom : ∀ (u' : K.W) p, (Gm.force (.inl u') (coreGen ξ ζ ρ p) ↔ u' ∈ K.V p) := by
    intro u' p
    constructor
    · intro h
      rcases h.1 with hv | hv
      · rcases hv with ⟨p', e, hu'⟩ | ⟨hne, _⟩
        · rw [hfr.1 p' p e] at hu'
          exact hu'
        · exact absurd rfl (hne p)
      · exact absurd hv (hb u')
    · intro h
      exact ⟨Or.inl (Or.inl ⟨p, rfl, h⟩), hz u'⟩
  have htr := relB_transferO Gm ξ (coreGen ξ ζ ρ) K Sum.inl hbx hb (fun h => h) hback
    (fun _ => Iff.rfl) hatom
  have hrA : Gm.force (.inl u) (rel ξ ζ (coreGen ξ ζ ρ) A) :=
    (rel_iff_relB_gen Gm ξ ζ _ _ (fun _ _ _ => Iff.rfl) A (.inl u) (hz u)).mpr ((htr A u).mpr hu)
  have hrB := sem_of_deriv hd Gm (.inl u) hrA
  exact (htr B u).mp
    ((rel_iff_relB_gen Gm ξ ζ _ _ (fun _ _ _ => Iff.rfl) B (.inl u) (hz u)).mp hrB)

/-- **PROVED: (P1), the core lemma for PLL.** -/
theorem coreLemmaPLL : CoreLemmaPLL := by
  intro ξ ζ ρ hξ hζ hle hstrict hfr
  refine ⟨fun p => (Interval.core_bounds hle p).1, fun p => (Interval.core_bounds hle p).2,
    fun A B => ?_⟩
  exact ⟨rel_preservesPLL ξ ζ (coreGen ξ ζ ρ)
      (fun M v _ hv => ⟨Or.inr hv, sem_of_deriv hle M v hv⟩) (fun _ _ _ hv => hv.2),
    core_reflectsPLL hξ hζ hle hstrict hfr⟩

/-! ### Stage 3 (c): nesting, the main theorem, the bridge, every depth -/

/-- **PROVED: (P2)**, so `Interval.NestPLL` (OPEN in `wip/f0FreeInterval.lean`)
holds. -/
theorem nestPLL : NestPLLFree := by
  intro a b x ξ ζ ρ hF hξ hζ hle hstrict hfr
  obtain ⟨hax, hxb, hfaith⟩ := hF
  obtain ⟨hyl, hyu, hyf⟩ := coreLemmaPLL ξ ζ ρ hξ hζ hle hstrict hfr
  have sxb : ∀ (M : SubframeModel) v p, M.force v (x p) → M.force v b := fun M v p h =>
    sem_of_deriv (hxb p) M v h
  have sab : ∀ (M : SubframeModel) v, M.force v a → M.force v b := fun M v h =>
    sxb M v "" (sem_of_deriv (hax "") M v h)
  refine ⟨fun p => (hfaith _ _).mp (hyl p), fun p => (hfaith _ _).mp (hyu p), fun A B => ?_⟩
  refine (hyf A B).trans ((hfaith _ _).trans (deriv_congr ?_ ?_))
  · exact fun M v => (rel_comp M a b x ξ ζ (coreGen ξ ζ ρ) (sab M) (sxb M) A v).symm
  · exact fun M v => (rel_comp M a b x ξ ζ (coreGen ξ ζ ρ) (sab M) (sxb M) B v).symm

/-- `Interval.NestPLL`, as stated there. -/
theorem nestPLL_interval : Interval.NestPLL := nestPLL

/-- **PROVED: (P3), the main theorem for PLL.** -/
theorem mainPLL : MainPLL := by
  intro a b x ξ ζ ha hb hx hF hξ hζ hle hstrict
  exact ⟨nestGen a b x ξ ζ (freshRen ξ ζ), fun p => Interval.atomFree_rel ha hb hx _,
    nestPLL a b x ξ ζ _ hF hξ hζ hle hstrict (Interval.fresh_freshRen ξ ζ)⟩

/-- **PROVED: (P4)**, the readers' copy of PLL as an interval copy in `[σ³⊥, ⊤]`. -/
theorem bridgePLL3 : BridgePLL3 := by
  refine ⟨b3_le_xr, fun _ => le_top _, fun A B => ?_⟩
  exact (freeReaders A B).trans (deriv_congr
    (fun M v => (rel_iff_relB_gen M (base 3) topF xr xr (fun _ _ _ => Iff.rfl) A v
      (Interval.force_topF M v)).symm)
    (fun M v => (rel_iff_relB_gen M (base 3) topF xr xr (fun _ _ _ => Iff.rfl) B v
      (Interval.force_topF M v)).symm))

/-- **PROVED: depth one inside the base copy.** -/
theorem nestOnePLL : NestOnePLL := fun ξ ζ hξ hζ hle hstrict =>
  mainPLL _ _ _ ξ ζ b3_vf rfl xr_vf bridgePLL3 hξ hζ hle hstrict

/-- A faithful copy is non-degenerate: `[b] ⊬ a`. -/
theorem freeInPLL_strict {a b : PLLFormula} {x : String → PLLFormula} (hF : FreeInPLL a b x) :
    ¬ Deriv [b] a := fun h =>
  Interval.ipc_top_bot ((hF.2.2 topF .falsePLL).mpr
    (Deriv.cutHead (Deriv.andElim2 (Deriv.iden (.head _))) h))

/-- What the induction on the depth carries. -/
theorem towerP_props (ξs ζs : Nat → PLLFormula) (h : TowerHyp ξs ζs) : ∀ d : Nat,
    FreeInPLL (towerP ξs ζs d).a (towerP ξs ζs d).b (towerP ξs ζs d).x ∧
    (∀ p, atomFree ((towerP ξs ζs d).x p) = true) ∧
    atomFree (towerP ξs ζs d).a = true ∧ atomFree (towerP ξs ζs d).b = true
  | 0 => ⟨bridgePLL3, xr_vf, b3_vf, rfl⟩
  | d + 1 => by
      obtain ⟨hF, hx, ha, hb⟩ := towerP_props ξs ζs h d
      obtain ⟨h1, h2, h3, h4⟩ := h d
      exact ⟨nestPLL _ _ _ _ _ _ hF h1 h2 h3 h4 (Interval.fresh_freshRen _ _),
        fun _ => Interval.atomFree_rel ha hb hx _, Interval.atomFree_rel ha hb hx _,
        Interval.atomFree_rel ha hb hx _⟩

/-- **PROVED: (P5), every finite depth.** -/
theorem nestAllPLL : NestAllPLL := by
  intro ξs ζs h d
  obtain ⟨hF, hx, _, _⟩ := towerP_props ξs ζs h d
  obtain ⟨_, _, h3, _⟩ := h d
  refine ⟨hF, hx, freeInPLL_strict hF, ?_, ?_, ?_⟩
  · exact (hF.2.2 .falsePLL (ξs d)).mp (bot_le _)
  · exact (hF.2.2 (ξs d) (ζs d)).mp h3
  · exact Deriv.cutHead ((hF.2.2 (ζs d) topF).mp (le_top _)) (Deriv.andElim2 (Deriv.iden (.head _)))

/-- **PROVED: every depth of the tower carries PLL inside F0.** -/
theorem freePLLIn_tower (ξs ζs : Nat → PLLFormula) (h : TowerHyp ξs ζs) (d : Nat) :
    FreePLLIn (towerP ξs ζs d).a (towerP ξs ζs d).b :=
  ⟨(towerP ξs ζs d).x, (towerP_props ξs ζs h d).2.1, (towerP_props ξs ζs h d).1⟩

/-! ### Stage 3 (d): the statement in the coordinates of the readers' copy (added at stage 3) -/

/-- The interval translation respects `⊣⊢` of its endpoints, in every model. -/
theorem rel_congr_force (M : SubframeModel) {a b a' b' : PLLFormula} (x : String → PLLFormula)
    (ha : ∀ v, M.force v a ↔ M.force v a') (hb : ∀ v, M.force v b ↔ M.force v b') :
    ∀ (A : PLLFormula) (v : M.W), M.force v (rel a b x A) ↔ M.force v (rel a' b' x A)
  | .prop _, _ => Iff.rfl
  | .falsePLL, v => ha v
  | .and A B, v => and_congr (rel_congr_force M x ha hb A v) (rel_congr_force M x ha hb B v)
  | .or A B, v => or_congr (rel_congr_force M x ha hb A v) (rel_congr_force M x ha hb B v)
  | .ifThen A B, v => by
      have ihA := rel_congr_force M x ha hb A
      have ihB := rel_congr_force M x ha hb B
      show ((∀ u, M.le v u → M.force u (rel a b x A) → M.force u (rel a b x B)) ∧ M.force v b) ↔
        ((∀ u, M.le v u → M.force u (rel a' b' x A) → M.force u (rel a' b' x B)) ∧ M.force v b')
      exact and_congr
        ⟨fun h u hu hA => (ihB u).mp (h u hu ((ihA u).mpr hA)),
         fun h u hu hA => (ihB u).mpr (h u hu ((ihA u).mp hA))⟩ (hb v)
  | .somehow A, v => by
      have ihA := rel_congr_force M x ha hb A
      show ((∀ u, M.le v u → u ∈ M.S → M.force u (rel a b x A)) ∧ M.force v b) ↔
        ((∀ u, M.le v u → u ∈ M.S → M.force u (rel a' b' x A)) ∧ M.force v b')
      exact and_congr
        ⟨fun h u hu hS => (ihA u).mp (h u hu hS), fun h u hu hS => (ihA u).mpr (h u hu hS)⟩ (hb v)

/-- A faithful copy is carried along `⊣⊢` of its endpoints. -/
theorem freeInPLL_congr {a b a' b' : PLLFormula} {x : String → PLLFormula}
    (hF : FreeInPLL a b x) (ha : Interd a a') (hb : Interd b b') : FreeInPLL a' b' x := by
  obtain ⟨hax, hxb, hf⟩ := hF
  have sa : ∀ (M : SubframeModel) v, M.force v a ↔ M.force v a' := fun M v =>
    ⟨sem_of_deriv ha.1 M v, sem_of_deriv ha.2 M v⟩
  have sb : ∀ (M : SubframeModel) v, M.force v b ↔ M.force v b' := fun M v =>
    ⟨sem_of_deriv hb.1 M v, sem_of_deriv hb.2 M v⟩
  refine ⟨fun p => Deriv.cutHead ha.2 (hax p), fun p => Deriv.cutHead (hxb p) hb.1,
    fun A B => (hf A B).trans (deriv_congr ?_ ?_)⟩
  · exact fun M v => rel_congr_force M x (sa M) (sb M) A v
  · exact fun M v => rel_congr_force M x (sa M) (sb M) B v

/-- In `[σ³⊥, ⊤]`, the interval translation is the readers' copy: `rel σ³⊥ ⊤ xr A ⊣⊢ gR A`. -/
theorem rel_top_interd_gR (A : PLLFormula) : Interd (rel (base 3) topF xr A) (gR A) :=
  interd_of_sem fun M v =>
    rel_iff_relB_gen M (base 3) topF xr xr (fun _ _ _ => Iff.rfl) A v (Interval.force_topF M v)

/-- **The clearest form (added at stage 3)**: for ◯-free `ξ`, `ζ` with `[ξ] ⊢ ζ`
and `[ζ] ⊬ ξ`, the interval `[gR ξ, gR ζ]` of F0 carries a faithful copy of PLL,
`◯` included, with variable-free generators. -/
def PLLInGRInterval : Prop :=
  ∀ ξ ζ : PLLFormula, boxFree ξ = true → boxFree ζ = true → Deriv [ξ] ζ → ¬ Deriv [ζ] ξ →
    FreePLLIn (gR ξ) (gR ζ)

/-- **PROVED.** -/
theorem pllInGRInterval : PLLInGRInterval := fun ξ ζ hξ hζ hle hstrict =>
  let ⟨x, hx, hF⟩ := nestOnePLL ξ ζ hξ hζ hle hstrict
  ⟨x, hx, freeInPLL_congr hF (rel_top_interd_gR ξ) (rel_top_interd_gR ζ)⟩

/-! ### Stage 3 (e): not inside every interval (added at stage 3) -/

/-- **(added at stage 3)** No sub-interval of an interval `[a, b]` with
`[b] ⊢ ◯a` carries a faithful copy of PLL. -/
def NoPLLBelowBox : Prop :=
  ∀ (a b a' b' : PLLFormula) (x : String → PLLFormula),
    Deriv [b] (.somehow a) → Deriv [a] a' → Deriv [b'] b → ¬ FreeInPLL a' b' x

/-- **(added at stage 3)** The instance `[σ³⊥, ◯σ³⊥]`. -/
def NoPLLInSig3Box : Prop :=
  ∀ (a' b' : PLLFormula) (x : String → PLLFormula),
    Deriv [base 3] a' → Deriv [b'] (.somehow (base 3)) → ¬ FreeInPLL a' b' x

/-- **(added at stage 3)** `[σ³⊥, ◯σ³⊥]` carries a faithful copy of `H_ω`. -/
def HωInSig3Box : Prop := Interval.FreeHAωIn (base 3) (.somehow (base 3))

/-- **PROVED**: `[b′] ⊢ b ⊢ ◯a ⊢ ◯a′`, then `not_freeInPLL_of_top_box`. -/
theorem noPLLBelowBox : NoPLLBelowBox := fun _ _ _ _ _ hb ha hb' =>
  not_freeInPLL_of_top_box (Deriv.cutHead (Deriv.cutHead hb' hb) (Deriv.somehowMono ha))

/-- **PROVED.** -/
theorem noPLLInSig3Box : NoPLLInSig3Box := fun a' b' x ha hb' =>
  noPLLBelowBox (base 3) (.somehow (base 3)) a' b' x (Deriv.iden (.head _)) ha hb'

theorem code_empty : Base3.code "" = 0 := by decide

theorem xω_empty : rel (base 3) topF xω (.prop "") = .somehow (base 3) := by
  show gen (Base3.code "") = _
  rw [code_empty]
  rfl

/-- **PROVED**: `[σ³⊥, ◯σ³⊥] = [rel ⊥, rel p₀]` in the `xω` copy of `H_ω`
(`◯σ³⊥ = x₀`), so `Interval.nestOne` applies. -/
theorem hωInSig3Box : HωInSig3Box := by
  have h := Interval.nestOne .falsePLL (.prop "") rfl rfl Interval.Cells.hyp2_le
    Interval.Cells.hyp2_strict
  rw [xω_empty] at h
  exact h

/-! ### Stage 3 (f): Task 2 -/

/-- The model `M` with the atom `q` set to the constant `P`. -/
def setAtom (M : SubframeModel) (q : String) (P : Prop) : SubframeModel where
  W := M.W
  le := M.le
  S := M.S
  V c := fun w => if c = q then P else w ∈ M.V c
  refl := M.refl
  trans := M.trans
  hered {c u v} h hu := by
    have hu' : (if c = q then P else u ∈ M.V c) := hu
    show (if c = q then P else v ∈ M.V c)
    rcases Decidable.em (c = q) with hc | hc
    · rw [if_pos hc] at hu' ⊢
      exact hu'
    · rw [if_neg hc] at hu' ⊢
      exact M.hered h hu'

/-- Setting an atom that does not occur changes nothing. -/
theorem force_setAtom (M : SubframeModel) (q : String) (P : Prop) :
    ∀ (φ : PLLFormula), Interval.occ q φ = false → ∀ w : M.W,
      ((setAtom M q P).force w φ ↔ M.force w φ)
  | .prop c, h, w => by
      have hc : ¬ c = q := of_decide_eq_false h
      show (if c = q then P else w ∈ M.V c) ↔ w ∈ M.V c
      rw [if_neg hc]
  | .falsePLL, _, _ => Iff.rfl
  | .and A B, h, w =>
      and_congr (force_setAtom M q P A (Interval.or_eq_false_split h).1 w)
        (force_setAtom M q P B (Interval.or_eq_false_split h).2 w)
  | .or A B, h, w =>
      or_congr (force_setAtom M q P A (Interval.or_eq_false_split h).1 w)
        (force_setAtom M q P B (Interval.or_eq_false_split h).2 w)
  | .ifThen A B, h, w => by
      have hA := force_setAtom M q P A (Interval.or_eq_false_split h).1
      have hB := force_setAtom M q P B (Interval.or_eq_false_split h).2
      show (∀ u, M.le w u → (setAtom M q P).force u A → (setAtom M q P).force u B) ↔
        (∀ u, M.le w u → M.force u A → M.force u B)
      exact ⟨fun h' u hu ha => (hB u).mp (h' u hu ((hA u).mpr ha)),
        fun h' u hu ha => (hB u).mpr (h' u hu ((hA u).mp ha))⟩
  | .somehow A, h, w => by
      have hA := force_setAtom M q P A h
      show (∀ u, M.le w u → u ∈ M.S → (setAtom M q P).force u A) ↔
        (∀ u, M.le w u → u ∈ M.S → M.force u A)
      exact ⟨fun h' u hu hS => (hA u).mp (h' u hu hS), fun h' u hu hS => (hA u).mpr (h' u hu hS)⟩

theorem force_setAtom_q (M : SubframeModel) (q : String) (P : Prop) (w : M.W) :
    (setAtom M q P).force w (.prop q) ↔ P := by
  show (if q = q then P else w ∈ M.V q) ↔ P
  rw [if_pos rfl]

/-- **Density in PLL**: for `q` occurring in neither `A` nor `B`, `[B] ⊬ A`
gives `A < B ∧ (A ∨ q) < B` strictly (the countermodel of `[B] ⊢ A` with `q`
set true, respectively false). -/
theorem nd_between {A B : PLLFormula} (q : String) (hqA : Interval.occ q A = false)
    (hqB : Interval.occ q B = false) (h : ¬ Deriv [B] A) :
    ¬ Deriv [B.and (A.or (.prop q))] A ∧ ¬ Deriv [B] (B.and (A.or (.prop q))) := by
  have h0 : ¬ Deriv [] (B.ifThen A) := fun h' =>
    h (Deriv.impElim (h'.rename fun _ h => absurd h List.not_mem_nil) (Deriv.iden (.head _)))
  obtain ⟨N, _, k, hk⟩ := SubframeModel.CF.exists_countermodel h0
  obtain ⟨w, _, hwB, hwA⟩ := SubframeModel.CF.exists_of_not_force_imp hk
  constructor
  · intro hd
    have h1 : (setAtom N q True).force w (B.and (A.or (.prop q))) :=
      ⟨(force_setAtom N q True B hqB w).mpr hwB, Or.inr ((force_setAtom_q N q True w).mpr trivial)⟩
    exact hwA ((force_setAtom N q True A hqA w).mp (sem_of_deriv hd (setAtom N q True) w h1))
  · intro hd
    have h1 := sem_of_deriv hd (setAtom N q False) w ((force_setAtom N q False B hqB w).mpr hwB)
    rcases h1.2 with hA | hq
    · exact hwA ((force_setAtom N q False A hqA w).mp hA)
    · exact (force_setAtom_q N q False w).mp hq

/-- **PROVED: no cover has both ends in the range of `gR`**: `gR (B ∧ (A ∨ q))`,
`q` fresh, lies strictly between `gR A` and `gR B`. -/
theorem rangeNoCover : RangeNoCover := by
  rintro A B hAB hBA ⟨-, -, hc⟩
  have hq := (Interval.fresh_freshRen A B).2 ""
  obtain ⟨n1, n2⟩ := nd_between (freshRen A B "") hq.1 hq.2 hBA
  have hlo : Deriv [gR A] (gR (B.and (A.or (.prop (freshRen A B ""))))) :=
    (g_faithful _ _).mp (Deriv.andIntro hAB (Deriv.orIntro1 (Deriv.iden (.head _))))
  have hhi : Deriv [gR (B.and (A.or (.prop (freshRen A B ""))))] (gR B) :=
    (g_faithful _ _).mp (Deriv.andElim1 (Deriv.iden (.head _)))
  rcases hc _ (g_af _) hlo hhi with i | i
  · exact n1 ((g_faithful _ _).mpr i.1)
  · exact n2 ((g_faithful _ _).mpr i.2)

/-- **PROVED: no `σ³`-image of a strict pair of F0 (in particular of a cover)
is a cover.** -/
theorem sig3ImageNotCover : Sig3ImageNotCover := by
  intro c d hc hd hcd hdc
  have h := rangeNoCover c d hcd hdc
  rw [Endpoints.gR_closed hc, Endpoints.gR_closed hd] at h
  exact h

/-- `REFUTED CoverSig3` again, from `rangeNoCover` (`σ³⊥ = gR ⊥`, `◯σ³⊥ = gR ◯⊥`). -/
theorem not_coverSig3' : ¬ CoverSig3 :=
  rangeNoCover .falsePLL (.somehow .falsePLL) (bot_le _) nd_e_bot

/-- `σ²t5 = σ³⊥ ∨ (σ³⊥ → ◯σ²⊥)`. -/
theorem sig2t5_eq : sigN 2 t5 = (base 3).or ((base 3).ifThen (.somehow (base 2))) := rfl

/-- Every copy world of the readers' gadget refutes `σ²t5`. -/
theorem w_not_sig2t5 {K : SubframeModel} {Sw : K.W → Prop} (k : K.W) :
    ¬ (GadR.MS K Sw).force (Base3.Gad.Pt.w k) (sigN 2 t5) := by
  rw [sig2t5_eq]
  intro h
  rcases h with h | h
  · exact GadR.w_not_b3 k h
  · have h1 := h (Base3.Gad.Pt.z 0 (Cell.bot 0)) trivial (GadR.z_b3 0 _)
    exact GadR.kS_not_b2 (h1 _ ((GadR.MS K Sw).refl _) GadR.kS_S)

/-- **PROVED: below `σ²t5` the range of `gR` has only its bottom.** -/
theorem rangeBelowSig2T5 : RangeBelowSig2T5 := fun A h =>
  deriv_of_sem fun K _ k hk => absurd
    (sem_of_deriv h (GadR.MS K (· ∈ K.S)) (Base3.Gad.Pt.w k) ((GadR.transfer A k).mpr hk))
    (w_not_sig2t5 k)

/-- **PROVED: `σ²t5` is not in the range of `gR`.** -/
theorem sig2t5_not_in_range : ¬ ∃ A : PLLFormula, Interd (gR A) (sigN 2 t5) := by
  rintro ⟨A, i⟩
  have hA := rangeBelowSig2T5 A i.1
  have h1 : Deriv [gR A] (base 3) := (g_faithful A .falsePLL).mp hA
  exact sig2t5_strict (Deriv.cutHead i.2 h1)

end NestPLL
end F0
end PLLND

/-! ## Axiom pins: stage 3 -/

#axioms_within PLLND.F0.NestPLL.rel_preservesPLL [propext, Quot.sound]
#axioms_within PLLND.F0.NestPLL.core_reflectsPLL [propext, Quot.sound]
#axioms_within PLLND.F0.NestPLL.coreLemmaPLL [propext, Quot.sound]
#axioms_within PLLND.F0.NestPLL.nestPLL [propext, Quot.sound]
#axioms_within PLLND.F0.NestPLL.nestPLL_interval [propext, Quot.sound]
#axioms_within PLLND.F0.NestPLL.mainPLL [propext, Quot.sound]
#axioms_within PLLND.F0.NestPLL.bridgePLL3 [propext, Quot.sound]
#axioms_within PLLND.F0.NestPLL.nestOnePLL [propext, Quot.sound]
#axioms_within PLLND.F0.NestPLL.freeInPLL_strict [propext, Quot.sound]
#axioms_within PLLND.F0.NestPLL.towerP_props [propext, Quot.sound]
#axioms_within PLLND.F0.NestPLL.nestAllPLL [propext, Quot.sound]
#axioms_within PLLND.F0.NestPLL.freePLLIn_tower [propext, Quot.sound]
#axioms_within PLLND.F0.NestPLL.rel_congr_force [propext, Quot.sound]
#axioms_within PLLND.F0.NestPLL.freeInPLL_congr [propext, Quot.sound]
#axioms_within PLLND.F0.NestPLL.rel_top_interd_gR [propext, Quot.sound]
#axioms_within PLLND.F0.NestPLL.pllInGRInterval [propext, Quot.sound]
#axioms_within PLLND.F0.NestPLL.noPLLBelowBox [propext, Quot.sound]
#axioms_within PLLND.F0.NestPLL.noPLLInSig3Box [propext, Quot.sound]
#axioms_within PLLND.F0.NestPLL.code_empty [propext, Quot.sound]
#axioms_within PLLND.F0.NestPLL.hωInSig3Box [propext, Quot.sound]
#axioms_within PLLND.F0.NestPLL.force_setAtom [propext, Quot.sound]
#axioms_within PLLND.F0.NestPLL.nd_between [propext, Quot.sound]
#axioms_within PLLND.F0.NestPLL.rangeNoCover [propext, Quot.sound]
#axioms_within PLLND.F0.NestPLL.sig3ImageNotCover [propext, Quot.sound]
#axioms_within PLLND.F0.NestPLL.not_coverSig3' [propext, Quot.sound]
#axioms_within PLLND.F0.NestPLL.w_not_sig2t5 [propext, Quot.sound]
#axioms_within PLLND.F0.NestPLL.rangeBelowSig2T5 [propext, Quot.sound]
#axioms_within PLLND.F0.NestPLL.sig2t5_not_in_range [propext, Quot.sound]
