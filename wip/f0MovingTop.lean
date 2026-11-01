import wip.f0FreeInterval
import wip.f0FreePLL
import wip.f0InsideOut
import LaxLogic.PLL.Sequent.Sequent
import Meta.Audit

/-!
# Faithful copies of F0 and of PLL in intervals strictly below `⊤`

Matthew, 2026-11-01: "mechanise the reduction, run the test(s)".  The question:
can the faithful embedding of PLL into its closed fragment F0 be repeated
inside an interval `[a, b]` with `b < ⊤`?  And (addition the same day) the
recursive form, as for `H_ω`: iterate the interval translation.

## The statements (Stage 1, committed before any proof, METHOD.md §1)

`rel a b x` is the interval translation of `wip/f0FreeInterval.lean`
(`⊥ ↦ a`, `p ↦ x p`, `∧ ∨` kept, `A → B ↦ (rel A ↠ rel B) ∧ b`,
`◯A ↦ ◯(rel A) ∧ b`); `subBot a C = C[⊥ := a]`, `σ = subBot t3`;
`relB a x` is the relativisation of `wip/f0FreeHAn.lean` (`⊥ ↦ a`,
`p ↦ x p`, connectives kept).  On closed formulas `rel a b x` does not depend
on `x`; `relC a b = rel a b (fun _ => a)`.

    CopyF0In a b :  ∀ A B closed,  [A] ⊢ B  ⟺  [relC a b A] ⊢ relC a b B
    TopAvoid a b :  ∀ C closed,  [b] ⊢ C[⊥ := a]  ⟹  ⊢ C

(R)   RelClosed :       A closed, [a] ⊢ b   ⟹   rel a b x A ⊣⊢ A[⊥ := a] ∧ b
      CopyIffTopAvoid : [a] ⊢ b   ⟹   (CopyF0In a b ⟺ TopAvoid a b)
(R')  RelGen :          [a] ⊢ b   ⟹   rel a b (p ↦ x p ∧ b) C ⊣⊢ relB a x C ∧ b   (every C)
      GenIff :          [a] ⊢ b,  ∀ p, [a] ⊢ x p   ⟹
                          (FreeInPLL a b (p ↦ x p ∧ b)  ⟺  ∀ C, [b] ⊢ relB a x C ⟹ ⊢ C)
(N)   CopyAtBot :       b closed   ⟹   (CopyF0In ⊥ b ⟺ ⊢ b)
(T5)  T5Cell :          [t5] ⊢ σ²⊥;     the candidates TopAvoid t3 t5, CopyF0In t3 t5
(T6)  SigAvoidT6 :      ∀ C,  [t6] ⊢ σC  ⟹  ⊢ C          (every formula C)
      TopAvoidT3T6, T6Below :  TopAvoid t3 t6;   [t3] ⊢ t6,  ⊬ t6
(W1)  CopyT3T6 :        CopyF0In t3 t6
(T6n) TopAvoidN :       n ≥ 1  ⟹  TopAvoid (σⁿ⊥) (t6 ∨ σⁿ⊥)  ∧  ⊬ t6 ∨ σⁿ⊥
(C)   NotCofinal :      ∀ n,  [t6] ⊬ σⁿ⊥
      BasesOnlyTop :    x closed,  (∀ n, [σⁿ⊥] ⊢ x)  ⟹  ⊢ x
(F)   with τ = relC a b and τᵈ its iterates (`tauN a b d`), a, b closed, [a] ⊢ b:
      IterBounds :      [τᵈ⊥] ⊢ τᵈ⁺¹⊥,   [τᵈ⁺¹⊤] ⊢ τᵈ⊤,   [τᵈ⊥] ⊢ τᵈA ⊢ τᵈ⊤   (A closed)
      FixedInAll :      x closed, τx ⊣⊢ x   ⟹   ∀ d,  [τᵈ⊥] ⊢ x ⊢ τᵈ⊤
      SigFixedTop :     x closed, σx ⊣⊢ x   ⟹   ⊢ x
      TauFixedPoint :   ∃ x closed,  relC t3 t6 x ⊣⊢ x            (OPEN, not attempted)
(W2)  IterRel :         τᵈ A ⊣⊢ relC (τᵈ⊥) (τᵈ⊤) A   (A closed);   W2: the instance (t3, t6)
(W3)  StrictNestOf :    CopyF0In a b,  [a] ⊬ ⊥,  ⊬ b   ⟹   StrictNest a b:
                          [τᵈ⊥] ⊢ τᵈ⁺¹⊥,  [τᵈ⁺¹⊥] ⊬ τᵈ⊥,  [τᵈ⁺¹⊤] ⊢ τᵈ⊤,  [τᵈ⊤] ⊬ τᵈ⁺¹⊤
      W3 :              StrictNest t3 t6
(W4)  IterCopyOf :      a, b, x closed,  [a] ⊬ ⊥,  ⊬ b,  FreeInPLL a b x   ⟹   IterCopy a b x:
                          ∀ d,  A ↦ τᵈ(rel a b x A) is faithful on PLL, lies in [τᵈa, τᵈb],
                          and the intervals are strictly nested at both ends
      W4 :              PLLBelowTop  ⟹  IterCopy σ³⊥ b (p ↦ y p ∧ b)

The target (OPEN at Stage 1), with `b = t6 ∨ σ³⊥` and the readers `y = xr` of
`wip/f0FreePLL.lean`:

    PLLBelowTop :        FreeInPLL σ³⊥ b (p ↦ y p ∧ b)
    PLLBelowTopReduced : ∀ C,  [b] ⊢ relB σ³⊥ y C  ⟹  ⊢ C          (equivalent, by GenIff)
    refutation cells:    [b] ⊢? relB σ³⊥ y Oᵢ,   O1 = ◯p → p,  O2 = ◯p ∨ ¬◯p,  O3 = ◯(p ∨ q) → ◯p ∨ ◯q

## Statements added at Stage 2 (the manager, 2026-11-01): the new target

The copy of PLL below `⊤` by composition, and the tower built in the free PLL
algebra and carried into F0 by `g = relB σ³⊥ y` (the shape of the `H_ω` tower).
With `x_P p = (p ∨ t3) ∧ t6` and `τ_P = rel t3 t6 x_P` on ALL formulas
(`τ_P A ⊣⊢ A^{t3} ∧ t6`, `A^{t3} = aTr t3 A` Friedman's A-translation):

    (Q1) PLLSelf :         FreeInPLL t3 t6 x_P
         PLLSelfReduced :  ∀ C,  [t6] ⊢ aTr t3 C  ⟹  ⊢ C
    (Q2) PLLSelfTower :    ∀ d,  τ_Pᵈ faithful on PLL,  FreeInPLL (τ_Pᵈ⊥) (τ_Pᵈ⊤) (τ_Pᵈ ∘ p),
                             τ_Pᵈ A ⊣⊢ rel (τ_Pᵈ⊥) (τ_Pᵈ⊤) (τ_Pᵈ ∘ p) A,
                             [τ_Pᵈ⊥, τ_Pᵈ⊤] strictly nested at both ends
    (Q3) PLLTowerInF0 :    ∀ d,  g ∘ τ_Pᵈ faithful on PLL, in [g τ_Pᵈ⊥, g τ_Pᵈ⊤] ⊆ [σ³⊥, ⊤],
                             these intervals strictly nested, the depth-(d+1) copy inside
                             the depth-d interval
         TowerFirstStep :  g(τ_P ⊥) = σ⁴⊥,   g(τ_P ⊤) ⊣⊢ σ³ t6
    (P1) PLLInT6 :         FreeInPLL (τ σ³⊥) t6 (τ ∘ y),   τ = relC t3 t6
         BaseTauIncomparable :  [σ³⊥] ⊬ τ σ³⊥  and  [τ σ³⊥] ⊬ σ³⊥
                             (so the intervals [τᵈ σ³⊥, τᵈ⊤] of the composite τᵈ ∘ g are not
                             nested; that form of the tower is not stated)

## Results

All pins `[propext, Quot.sound]` (no `Classical.choice`, no `sorry`, no
`native_decide`); narrowed pins watched failing (`_out/gatewatch.lean`).

**PROVED**: (R) `relClosed`, `copyIffTopAvoid`, (R') `relGen`, `genIff`,
(N) `copyAtBot`, (T5) `t5Cell`, (T6) `sigAvoidT6` (every formula),
`topAvoidT3T6`, `t6Below`, (W1) `copyT3T6`, (T6n) `topAvoidN`, (C)
`notCofinal`, `basesOnlyTop`, (F) `iterBounds`, `fixedInAll`, `sigFixedTop`,
(W2) `iterRel`, `w2`, (W3) `strictNestOf`, `w3`, (W4) `iterCopyOf`, `w4`,
(Q1) `pllSelfReduced`, `pllSelf`, (Q2) `pllSelfTower`, (Q3) `pllTowerInF0`,
`towerFirstStep`, (P1) `pllInT6`, `baseTauIncomparable`.

**REFUTED**: `TopAvoidT3T5`, `CopyT3T5` (`not_topAvoidT3T5`,
`not_copyT3T5`); the first target `PLLBelowTop` (`not_pllBelowTop`,
`not_pllBelowTopReduced`): under `t6` the reader of the code-1 atom collapses,

    [t6] ⊢ y q = gen 2        (t6_gen2)

so the copy sends `q` to the top of `[σ³⊥, t6 ∨ σ³⊥]`, and the cell O3 is
derivable (`bT_O3`).  Cells O1, O2 pass (`targetCell_O1`, `targetCell_O2`).

**OPEN**: `TauFixedPoint` (not attempted).

So PLL embeds faithfully into `[t3, t6]` of PLL itself (`pllSelf`, by
`τ_P A = A^{t3} ∧ t6`), the iterates give strictly nested intervals
`[τ_Pᵈ⊥, τ_Pᵈ⊤]` each carrying a faithful copy of PLL as an interval
translation (`pllSelfTower`), and the readers carry the whole tower into F0
inside `[σ³⊥, ⊤]`, first step `[σ⁴⊥, σ³ t6]` (`pllTowerInF0`,
`towerFirstStep`).

Status note: `wip/f0MovingTop-STATUS.md`.
-/

set_option autoImplicit false

open PLLFormula

namespace PLLND
namespace F0
namespace MovingTop

open SemUI Sig FreeHAn Base3 FreePLL
open Interval (rel FreeInPLL topF)
open Pair (b2)
open PLLND.LaxInfinite (atomFree)

/-! ## Definitions -/

/-- `t6 = t5 ↠ t3`, interderivable with `¬¬◯⊥ ↠ ◯⊥` (`T6.t6_regular`). -/
abbrev t6 : PLLFormula := T6.t6F

/-- **The interval translation on closed formulas**, `rel a b` with the
generators fixed to `a` (on closed formulas the generators are not read). -/
def relC (a b : PLLFormula) : PLLFormula → PLLFormula := rel a b (fun _ => a)

/-- **A faithful copy of F0 in `[a, b]`**: the interval translation reflects and
preserves derivability between closed formulas. -/
def CopyF0In (a b : PLLFormula) : Prop :=
  ∀ A B : PLLFormula, atomFree A = true → atomFree B = true →
    (Deriv [A] B ↔ Deriv [relC a b A] (relC a b B))

/-- **`b` avoids the theorems pushed to `a`**: `[b] ⊢ C[⊥ := a]` only for
theorems `C` (closed `C`). -/
def TopAvoid (a b : PLLFormula) : Prop :=
  ∀ C : PLLFormula, atomFree C = true → Deriv [b] (subBot a C) → Deriv [] C

/-- The iterates `τᵈ` of `τ = relC a b`. -/
def tauN (a b : PLLFormula) : Nat → PLLFormula → PLLFormula
  | 0, A => A
  | d + 1, A => tauN a b d (relC a b A)

/-- The top of the target interval, `b = t6 ∨ σ³⊥`. -/
def bT : PLLFormula := t6.or b3

/-- The target generators `y p ∧ b`. -/
def yT (p : String) : PLLFormula := (xr p).and bT

/-! ## (R): the meet with `b` on closed formulas -/

/-- **(R)** On closed formulas, `rel a b x A ⊣⊢ A[⊥ := a] ∧ b`. -/
def RelClosed : Prop :=
  ∀ (a b : PLLFormula) (x : String → PLLFormula) (A : PLLFormula), atomFree A = true →
    Deriv [a] b → Interd (rel a b x A) ((subBot a A).and b)

/-- **The reduction**: a faithful copy of F0 in `[a, b]` exactly when `b` avoids
the pushed theorems. -/
def CopyIffTopAvoid : Prop :=
  ∀ a b : PLLFormula, Deriv [a] b → (CopyF0In a b ↔ TopAvoid a b)

/-! ## (R'): with generators -/

/-- **(R')** `rel a b (p ↦ x p ∧ b) C ⊣⊢ relB a x C ∧ b`, every formula `C`. -/
def RelGen : Prop :=
  ∀ (a b : PLLFormula) (x : String → PLLFormula) (C : PLLFormula), Deriv [a] b →
    Interd (rel a b (fun p => (x p).and b) C) ((relB a x C).and b)

/-- **The reduction with generators**. -/
def GenIff : Prop :=
  ∀ (a b : PLLFormula) (x : String → PLLFormula), Deriv [a] b → (∀ p, Deriv [a] (x p)) →
    (FreeInPLL a b (fun p => (x p).and b) ↔ ∀ C, Deriv [b] (relB a x C) → Deriv [] C)

/-! ## (N): the bottom interval -/

/-- **(N)** `CopyF0In ⊥ b ⟺ ⊢ b`, for closed `b`. -/
def CopyAtBot : Prop :=
  ∀ b : PLLFormula, atomFree b = true → (CopyF0In .falsePLL b ↔ Deriv [] b)

/-! ## (T5): a candidate that fails -/

/-- **(T5)** `[t5] ⊢ σ²⊥`. -/
def T5Cell : Prop := Deriv [t5] (sigN 2 .falsePLL)

/-- The candidate `TopAvoid t3 t5` (to be refuted with `C = t3`). -/
def TopAvoidT3T5 : Prop := TopAvoid t3 t5

/-- The candidate `CopyF0In t3 t5`. -/
def CopyT3T5 : Prop := CopyF0In t3 t5

/-! ## (T6): a copy of F0 in `[t3, t6]`, `t6 < ⊤` -/

/-- **(T6), every formula**: `[t6] ⊢ σC ⟹ ⊢ C`. -/
def SigAvoidT6 : Prop := ∀ C : PLLFormula, Deriv [t6] (sig C) → Deriv [] C

/-- **(T6)** `TopAvoid t3 t6`. -/
def TopAvoidT3T6 : Prop := TopAvoid t3 t6

/-- `t6` lies in `[t3, ⊤)`: `[t3] ⊢ t6` and `⊬ t6`. -/
def T6Below : Prop := Deriv [t3] t6 ∧ ¬ Deriv [] t6

/-- **(W1)** `τ = relC t3 t6` is faithful on closed formulas. -/
def CopyT3T6 : Prop := CopyF0In t3 t6

/-! ## (T6n): the family `[σⁿ⊥, t6 ∨ σⁿ⊥]` -/

/-- **(T6n)** -/
def TopAvoidN : Prop :=
  ∀ n : Nat, 1 ≤ n →
    TopAvoid (sigN n .falsePLL) (t6.or (sigN n .falsePLL)) ∧
      ¬ Deriv [] (t6.or (sigN n .falsePLL))

/-! ## (C): the bases `σⁿ⊥` -/

/-- **(C)** The bases are not cofinal below `t6`: `[t6] ⊬ σⁿ⊥`. -/
def NotCofinal : Prop := ∀ n : Nat, ¬ Deriv [t6] (sigN n .falsePLL)

/-- **(C)** The only upper bound of the bases is `⊤`. -/
def BasesOnlyTop : Prop :=
  ∀ x : PLLFormula, atomFree x = true → (∀ n, Deriv [sigN n .falsePLL] x) → Deriv [] x

/-! ## (F): iterates -/

/-- **(F)** The iterates move the ends inwards and bound every image. -/
def IterBounds : Prop :=
  ∀ a b : PLLFormula, atomFree a = true → atomFree b = true → Deriv [a] b → ∀ d : Nat,
    Deriv [tauN a b d .falsePLL] (tauN a b (d + 1) .falsePLL) ∧
    Deriv [tauN a b (d + 1) topF] (tauN a b d topF) ∧
    ∀ A : PLLFormula, atomFree A = true →
      Deriv [tauN a b d .falsePLL] (tauN a b d A) ∧ Deriv [tauN a b d A] (tauN a b d topF)

/-- **(F)** A fixed point of `τ` lies in every `[τᵈ⊥, τᵈ⊤]`. -/
def FixedInAll : Prop :=
  ∀ a b : PLLFormula, atomFree a = true → atomFree b = true → Deriv [a] b →
    ∀ x : PLLFormula, atomFree x = true → Interd (relC a b x) x → ∀ d : Nat,
      Deriv [tauN a b d .falsePLL] x ∧ Deriv [x] (tauN a b d topF)

/-- **(F)** The only fixed point of `σ` in F0 is `⊤`. -/
def SigFixedTop : Prop := ∀ x : PLLFormula, atomFree x = true → Interd (sig x) x → Deriv [] x

/-- **OPEN, not attempted**: `τ = relC t3 t6` has a closed fixed point. -/
def TauFixedPoint : Prop := ∃ x : PLLFormula, atomFree x = true ∧ Interd (relC t3 t6 x) x

/-! ## (W2): the iterates are interval translations -/

/-- **(W2), general** `τᵈ A ⊣⊢ relC (τᵈ⊥) (τᵈ⊤) A` for closed `A`. -/
def IterRel : Prop :=
  ∀ a b : PLLFormula, atomFree a = true → atomFree b = true → Deriv [a] b →
    ∀ (d : Nat) (A : PLLFormula), atomFree A = true →
      Interd (tauN a b d A) (relC (tauN a b d .falsePLL) (tauN a b d topF) A)

/-- **(W2)** the instance `τ = relC t3 t6`. -/
def W2 : Prop :=
  ∀ (d : Nat) (A : PLLFormula), atomFree A = true →
    Interd (tauN t3 t6 d A) (relC (tauN t3 t6 d .falsePLL) (tauN t3 t6 d topF) A)

/-! ## (W3): strict nesting at both ends -/

/-- Strict nesting of `[τᵈ⊥, τᵈ⊤]` at both ends. -/
def StrictNest (a b : PLLFormula) : Prop :=
  ∀ d : Nat,
    Deriv [tauN a b d .falsePLL] (tauN a b (d + 1) .falsePLL) ∧
    ¬ Deriv [tauN a b (d + 1) .falsePLL] (tauN a b d .falsePLL) ∧
    Deriv [tauN a b (d + 1) topF] (tauN a b d topF) ∧
    ¬ Deriv [tauN a b d topF] (tauN a b (d + 1) topF)

/-- **(W3), general** -/
def StrictNestOf : Prop :=
  ∀ a b : PLLFormula, atomFree a = true → atomFree b = true → Deriv [a] b →
    CopyF0In a b → ¬ Deriv [a] .falsePLL → ¬ Deriv [] b → StrictNest a b

/-- **(W3)** -/
def W3 : Prop := StrictNest t3 t6

/-! ## (W4): the recursive copy of PLL -/

/-- **The composite `τᵈ ∘ rel a b x`**: faithful on PLL for every `d`, with image
in `[τᵈ a, τᵈ b]`, the intervals strictly nested at both ends. -/
def IterCopy (a b : PLLFormula) (x : String → PLLFormula) : Prop :=
  ∀ d : Nat,
    (∀ A B : PLLFormula,
      Deriv [A] B ↔ Deriv [tauN a b d (rel a b x A)] (tauN a b d (rel a b x B))) ∧
    (∀ A : PLLFormula, Deriv [tauN a b d a] (tauN a b d (rel a b x A)) ∧
      Deriv [tauN a b d (rel a b x A)] (tauN a b d b)) ∧
    Deriv [tauN a b d a] (tauN a b (d + 1) a) ∧ ¬ Deriv [tauN a b (d + 1) a] (tauN a b d a) ∧
    Deriv [tauN a b (d + 1) b] (tauN a b d b) ∧ ¬ Deriv [tauN a b d b] (tauN a b (d + 1) b)

/-- **(W4), general** -/
def IterCopyOf : Prop :=
  ∀ (a b : PLLFormula) (x : String → PLLFormula), atomFree a = true → atomFree b = true →
    (∀ p, atomFree (x p) = true) → ¬ Deriv [a] .falsePLL → ¬ Deriv [] b →
    FreeInPLL a b x → IterCopy a b x

/-! ## The target -/

/-- **The target (OPEN at Stage 1)**: a faithful copy of PLL in `[σ³⊥, t6 ∨ σ³⊥]`,
generators `y p ∧ b`. -/
def PLLBelowTop : Prop := FreeInPLL b3 bT yT

/-- **The target, reduced by (R')**. -/
def PLLBelowTopReduced : Prop := ∀ C : PLLFormula, Deriv [bT] (relB b3 xr C) → Deriv [] C

/-- **(W4)** conditional on the target. -/
def W4 : Prop := PLLBelowTop → IterCopy b3 bT yT

/-- A refutation cell of the target: `[b] ⊬ relB σ³⊥ y C` (needed for every
non-theorem `C`). -/
def TargetCell (C : PLLFormula) : Prop := ¬ Deriv [bT] (relB b3 xr C)

/-! ## The new target (added at Stage 2): the tower in the free PLL algebra -/

/-- The generators `x_P p = (p ∨ t3) ∧ t6`. -/
def xP (p : String) : PLLFormula := ((PLLFormula.prop p).or t3).and t6

/-- `τ_P = rel t3 t6 x_P`, on all formulas. -/
def tauP : PLLFormula → PLLFormula := rel t3 t6 xP

/-- The iterates `τ_Pᵈ`. -/
def tauPN : Nat → PLLFormula → PLLFormula
  | 0, A => A
  | d + 1, A => tauPN d (tauP A)

/-- The faithful copy of PLL above `σ³⊥`, `g = relB σ³⊥ y`. -/
def gR (A : PLLFormula) : PLLFormula := relB b3 xr A

/-- **(Q1)** `τ_P` is a faithful copy of PLL in `[t3, t6]`. -/
def PLLSelf : Prop := FreeInPLL t3 t6 xP

/-- **(Q1), reduced by (R')** -/
def PLLSelfReduced : Prop := ∀ C : PLLFormula, Deriv [t6] (aTr t3 C) → Deriv [] C

/-- **(Q2)** the tower of copies of PLL inside the free PLL algebra. -/
def PLLSelfTower : Prop :=
  ∀ d : Nat,
    (∀ A B : PLLFormula, Deriv [A] B ↔ Deriv [tauPN d A] (tauPN d B)) ∧
    FreeInPLL (tauPN d .falsePLL) (tauPN d topF) (fun p => tauPN d (.prop p)) ∧
    (∀ A : PLLFormula, Interd (tauPN d A)
      (rel (tauPN d .falsePLL) (tauPN d topF) (fun p => tauPN d (.prop p)) A)) ∧
    Deriv [tauPN d .falsePLL] (tauPN (d + 1) .falsePLL) ∧
    ¬ Deriv [tauPN (d + 1) .falsePLL] (tauPN d .falsePLL) ∧
    Deriv [tauPN (d + 1) topF] (tauPN d topF) ∧
    ¬ Deriv [tauPN d topF] (tauPN (d + 1) topF)

/-- **(Q3)** the tower carried into F0 by `g`. -/
def PLLTowerInF0 : Prop :=
  ∀ d : Nat,
    (∀ A B : PLLFormula, Deriv [A] B ↔ Deriv [gR (tauPN d A)] (gR (tauPN d B))) ∧
    (∀ A : PLLFormula, Deriv [gR (tauPN d .falsePLL)] (gR (tauPN d A)) ∧
      Deriv [gR (tauPN d A)] (gR (tauPN d topF))) ∧
    Deriv [b3] (gR (tauPN d .falsePLL)) ∧
    Deriv [gR (tauPN d .falsePLL)] (gR (tauPN (d + 1) .falsePLL)) ∧
    ¬ Deriv [gR (tauPN (d + 1) .falsePLL)] (gR (tauPN d .falsePLL)) ∧
    Deriv [gR (tauPN (d + 1) topF)] (gR (tauPN d topF)) ∧
    ¬ Deriv [gR (tauPN d topF)] (gR (tauPN (d + 1) topF)) ∧
    (∀ A : PLLFormula, Deriv [gR (tauPN d .falsePLL)] (gR (tauPN (d + 1) A)) ∧
      Deriv [gR (tauPN (d + 1) A)] (gR (tauPN d topF)))

/-- **(Q3)** the first step is `[σ⁴⊥, σ³ t6]`. -/
def TowerFirstStep : Prop :=
  gR (tauPN 1 .falsePLL) = sigN 4 .falsePLL ∧ Interd (gR (tauPN 1 topF)) (sigN 3 t6)

/-- **(P1)** the composite `τ ∘ g` is a faithful copy of PLL in `[τ σ³⊥, t6]`. -/
def PLLInT6 : Prop := FreeInPLL (relC t3 t6 b3) t6 (fun p => relC t3 t6 (xr p))

/-- Why the composite tower `τᵈ ∘ g` is not stated: its bottoms are incomparable. -/
def BaseTauIncomparable : Prop :=
  ¬ Deriv [b3] (relC t3 t6 b3) ∧ ¬ Deriv [relC t3 t6 b3] b3

/-! ## Stage 2: the designed cells

Every countermodel is a `SubCM` table judged by `SubTab.no` in the kernel
(`decide`); the closed tableau of (T5) is judged by `SubTab.yes'`.  The tables
of (T5)–(T6), (C) and `BaseTauIncomparable` were produced by the subframe
tableau (`SubTab.solve`, untrusted) and minimised (`minimiseCM`); the tables of
the target and of (Q1) are designed (below). -/

section Cells

set_option maxRecDepth 100000

/-- The closed tableau of `t5 ↠ σ²⊥` (subframe tableau, 6604 characters). -/
def certT5 : PLLND.SubTab.TCert :=
  (.impR (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).or (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow))) ((((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).somehow).or ((((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).somehow).ifThen ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)))) (.orL ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)) (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow)) (.orL (PLLFormula.falsePLL.somehow) ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL) (.orR (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).somehow) ((((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).somehow).ifThen ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL))) (.boxR ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)) (.boxL PLLFormula.falsePLL .bot))) (.impL (PLLFormula.falsePLL.somehow) PLLFormula.falsePLL (.orR (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).somehow) ((((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).somehow).ifThen ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL))) (.boxR ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)) (.impL (PLLFormula.falsePLL.somehow) PLLFormula.falsePLL (.orL (PLLFormula.falsePLL.somehow) ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL) (.boxL PLLFormula.falsePLL .bot) (.orL ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)) (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow)) (.boxLoc PLLFormula.falsePLL (.ax ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)))) (.impL ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)) (PLLFormula.falsePLL.somehow) (.ax ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL))) (.boxL PLLFormula.falsePLL .bot)))) .bot))) .bot)) (.impL ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)) (PLLFormula.falsePLL.somehow) (.orR (PLLFormula.falsePLL.somehow) ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL) (.orR (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).somehow) ((((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).somehow).ifThen ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL))) (.impR (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).somehow) ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)) (.impL ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)) (PLLFormula.falsePLL.somehow) (.orL ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)) (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow)) (.orL (PLLFormula.falsePLL.somehow) ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL) (.ax ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL))) (.impL (PLLFormula.falsePLL.somehow) PLLFormula.falsePLL (.ax ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL))) .bot)) (.orR (PLLFormula.falsePLL.somehow) ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL) (.boxR PLLFormula.falsePLL (.impL ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)) (PLLFormula.falsePLL.somehow) (.orL ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)) (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow)) (.orL (PLLFormula.falsePLL.somehow) ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL) (.boxL PLLFormula.falsePLL .bot) (.impL (PLLFormula.falsePLL.somehow) PLLFormula.falsePLL (.boxL ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)) (.boxLoc PLLFormula.falsePLL (.ax ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL))))) .bot)) (.boxL ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)) (.orL (PLLFormula.falsePLL.somehow) ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL) (.boxL PLLFormula.falsePLL .bot) (.impL (PLLFormula.falsePLL.somehow) PLLFormula.falsePLL (.boxLoc PLLFormula.falsePLL (.ax ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)))) .bot)))) (.boxL PLLFormula.falsePLL .bot))))) (.orL ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)) (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow)) (.orL (PLLFormula.falsePLL.somehow) ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL) (.ax ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL))) (.impL (PLLFormula.falsePLL.somehow) PLLFormula.falsePLL (.ax (PLLFormula.falsePLL.somehow)) .bot)) (.orR (PLLFormula.falsePLL.somehow) ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL) (.ax (PLLFormula.falsePLL.somehow)))))))) (.orR (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).somehow) ((((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).somehow).ifThen ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL))) (.boxR ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)) (.boxL PLLFormula.falsePLL .bot))))))

/-- One world, outside `S`, no atoms. -/
def K0 : PLLND.SubTab.SubCM := { n := 1, root := 0, le := [[true]], S := [false], val := [[]] }

/-- The chain `r < s < e`, `s ∈ S`, `r, e ∉ S`: refutes `t6` at `r`, where `σ²⊥` and
`σ³⊥` hold (subframe tableau, minimised). -/
def Tchain : PLLND.SubTab.SubCM :=
  { n := 3, root := 0, le := [[true, true, true], [false, true, true], [false, false, true]],
    S := [false, true, false], val := [[], [], []] }

/-- A root below an `S`-top and a non-`S` top: refutes `t3`. -/
def Tfork : PLLND.SubTab.SubCM :=
  { n := 3, root := 0, le := [[true, true, true], [false, true, false], [false, false, true]],
    S := [false, true, false], val := [[], [], []] }

/-- `[t6] ⊬ σ²⊥` (subframe tableau, 15 worlds, minimised to 7). -/
def Tt6s2 : PLLND.SubTab.SubCM :=
  { n := 7, root := 0, le := [[true, true, true, true, true, true, true], [false, true, true, true, false, false, false], [false, false, true, false, false, false, false], [false, false, false, true, false, false, false], [false, false, false, false, true, true, true], [false, false, false, false, false, true, false], [false, false, false, false, false, false, true]],
    S := [false, true, false, true, false, false, true], val := [[], [], [], [], [], [], []] }

/-- `[t6] ⊬ σ³⊥` (subframe tableau, 29 worlds, minimised to 12). -/
def Tt6s3 : PLLND.SubTab.SubCM :=
  { n := 12, root := 0, le := [[true, true, true, true, true, true, true, true, true, true, true, true], [false, true, true, true, true, false, false, false, false, false, false, false], [false, false, true, true, true, false, false, false, false, false, false, false], [false, false, false, true, false, false, false, false, false, false, false, false], [false, false, false, false, true, false, false, false, false, false, false, false], [false, false, false, false, false, true, true, true, true, true, true, true], [false, false, false, false, false, false, true, true, true, false, false, false], [false, false, false, false, false, false, false, true, false, false, false, false], [false, false, false, false, false, false, false, false, true, false, false, false], [false, false, false, false, false, false, false, false, false, true, true, true], [false, false, false, false, false, false, false, false, false, false, true, false], [false, false, false, false, false, false, false, false, false, false, false, true]],
    S := [false, true, false, false, true, false, true, false, true, false, false, true], val := [[], [], [], [], [], [], [], [], [], [], [], []] }

/-- `[τ σ³⊥] ⊬ σ³⊥` (subframe tableau, 34 worlds, minimised to 12; the same
frame as `Tt6s3`). -/
def Ttaub3 : PLLND.SubTab.SubCM := Tt6s3

/-- **The target's O1 table** (designed): two tops `nT ∈ S`, `eT ∉ S` (worlds
5, 6) over `r < m, k`, `m, k < s, e`, with `k, s ∈ S`; `t6` holds everywhere,
`y₀ = gen 1` fails only at the root `r`, and `◯y₀` holds there. -/
def T1 : PLLND.SubTab.SubCM :=
  { n := 7, root := 0,
    le := [[true, true, true, true, true, true, true],
           [false, true, false, true, true, true, true],
           [false, false, true, true, true, true, true],
           [false, false, false, true, false, true, true],
           [false, false, false, false, true, true, true],
           [false, false, false, false, false, true, false],
           [false, false, false, false, false, false, true]],
    S := [false, false, true, true, false, true, false],
    val := [[], [], [], [], [], [], []] }

/-- **The target's O2 table** (designed): `T1` with a new root in `S`. -/
def T2 : PLLND.SubTab.SubCM :=
  { n := 8, root := 0,
    le := [[true, true, true, true, true, true, true, true],
           [false, true, true, true, true, true, true, true],
           [false, false, true, false, true, true, true, true],
           [false, false, false, true, true, true, true, true],
           [false, false, false, false, true, false, true, true],
           [false, false, false, false, false, true, true, true],
           [false, false, false, false, false, false, true, false],
           [false, false, false, false, false, false, false, true]],
    S := [true, false, false, true, true, false, true, false],
    val := [[], [], [], [], [], [], [], []] }

/-- **The two tops of `ext`, as a table**: `nT ∈ S` and `eT ∉ S` above every
world, the atoms `ats` true at both (the construction of `Sig.ext`). -/
def extT (K : PLLND.SubTab.SubCM) (ats : List String) : PLLND.SubTab.SubCM :=
  { n := K.n + 2, root := K.root,
    le := ((List.range K.n).map fun i => (List.range K.n).map (K.leB i) ++ [true, true]) ++
      [List.replicate K.n false ++ [true, false], List.replicate K.n false ++ [false, true]],
    S := (List.range K.n).map K.SB ++ [true, false],
    val := (List.range K.n).map (fun i => K.val.getD i []) ++ [ats, ats] }

/-! ### (T5), (T6), (C) -/

theorem t5_sig2_imp : Deriv [] (t5.ifThen (sigN 2 .falsePLL)) :=
  PLLND.SubTab.yes'.verdict _ certT5

/-- **(T5) PROVED**: `[t5] ⊢ σ²⊥`. -/
theorem t5Cell : T5Cell :=
  Deriv.impElim (Deriv.rename (fun _ h => absurd h List.not_mem_nil) t5_sig2_imp)
    (Deriv.iden (.head _))

/-- The gate of (T5), watched failing: the same tableau is rejected for `t6 ↠ σ²⊥`. -/
theorem gate_t5 : PLLND.SubTab.check ⟨false, [], [t6.ifThen (sigN 2 .falsePLL)]⟩ certT5 = false := by
  decide +kernel

theorem nd_t3 : ¬ Deriv [] t3 := SubTab.no.verdict t3 Tfork

/-- **(T5) REFUTED**: `TopAvoid t3 t5` fails at `C = t3` (`t3[⊥ := t3] = σ²⊥`). -/
theorem not_topAvoidT3T5 : ¬ TopAvoidT3T5 := fun h => nd_t3 (h t3 rfl t5Cell)

/-- `[t3] ⊢ t6`. -/
theorem t3_t6 : Deriv [t3] t6 := Deriv.impIntro (Deriv.iden (.tail _ (.head _)))

theorem nd_t6 : ¬ Deriv [] t6 := SubTab.no.verdict t6 Tchain

/-- **PROVED**: `[t3] ⊢ t6` and `⊬ t6`. -/
theorem t6Below : T6Below := ⟨t3_t6, nd_t6⟩

theorem nd_t6_sig2_imp : ¬ Deriv [] (t6.ifThen (sigN 2 .falsePLL)) := SubTab.no.verdict _ Tt6s2

/-- (C), `n = 2`: `[t6] ⊬ σ²⊥`. -/
theorem nd_t6_sig2 : ¬ Deriv [t6] (sigN 2 .falsePLL) := fun h => nd_t6_sig2_imp (Deriv.impIntro h)

theorem nd_t6_sig3_imp : ¬ Deriv [] (t6.ifThen (sigN 3 .falsePLL)) := SubTab.no.verdict _ Tt6s3

/-- (C), `n = 3`: `[t6] ⊬ σ³⊥`. -/
theorem nd_t6_sig3 : ¬ Deriv [t6] (sigN 3 .falsePLL) := fun h => nd_t6_sig3_imp (Deriv.impIntro h)

theorem nd_sig2_t6_imp : ¬ Deriv [] ((sigN 2 .falsePLL).ifThen t6) := SubTab.no.verdict _ Tchain

/-- `[σ²⊥] ⊬ t6`, so `[σⁿ⊥] ⊢ t6` fails at `n = 2`. -/
theorem nd_sig2_t6 : ¬ Deriv [sigN 2 .falsePLL] t6 := fun h => nd_sig2_t6_imp (Deriv.impIntro h)

theorem nd_b3_t6_imp : ¬ Deriv [] (b3.ifThen t6) := SubTab.no.verdict _ Tchain

/-- `[σ³⊥] ⊬ t6`. -/
theorem nd_b3_t6 : ¬ Deriv [b3] t6 := fun h => nd_b3_t6_imp (Deriv.impIntro h)

theorem nd_b3_taub3_imp : ¬ Deriv [] (b3.ifThen (relC t3 t6 b3)) := SubTab.no.verdict _ Tchain

theorem nd_taub3_b3_imp : ¬ Deriv [] ((relC t3 t6 b3).ifThen b3) := SubTab.no.verdict _ Ttaub3

/-- **PROVED**: the bottoms `σ³⊥` and `τ σ³⊥` are incomparable. -/
theorem baseTauIncomparable : BaseTauIncomparable :=
  ⟨fun h => nd_b3_taub3_imp (Deriv.impIntro h), fun h => nd_taub3_b3_imp (Deriv.impIntro h)⟩

/-! ### The target: `[t6] ⊢ y q` for the code-1 atom `q`

Under `t6`, `Y = t4 ∨ ¬t4` and `t3` hold at the same worlds, so `◯Y` and
`◯t3` do; then `σ²⊥ ⊢ relX (rn 3)`, and the odd rung `φ₃ = relX (rn 7)` has
the form `A ∨ (A ↠ relX (rn 3))`, which gives `(φ₃ ↠ σ²⊥) ↠ σ²⊥`, hence
`(c₂ ↠ σ²⊥) ↠ σ²⊥` and `gen 2`. -/

section Collapse

variable (M : SubframeModel)

theorem e_t4 {u : M.W} (h : M.force u e) : M.force u t4 :=
  fun _ hw _ => SubframeModel.force_mono M e hw h

theorem ne_not_t4 {u : M.W} (hn : M.force u ne) (h4 : M.force u t4) : False :=
  hn u (M.refl u) (h4 u (M.refl u) (Or.inr hn))

/-- `t3 ⊢ Y`. -/
theorem t3_Y {v : M.W} (h : M.force v t3) : M.force v Yf := by
  rcases (h : M.force v e ∨ M.force v ne) with he | hn
  · exact Or.inl (e_t4 M he)
  · exact Or.inr fun w hw h4 => ne_not_t4 M (SubframeModel.force_mono M ne hw hn) h4

/-- `[t6] ⊢ Y ↠ t3`. -/
theorem Y_t3 {v : M.W} (h6 : M.force v t6) (hY : M.force v Yf) : M.force v t3 := by
  rcases (hY : M.force v t4 ∨ M.force v (t4.ifThen .falsePLL)) with h4 | hn4
  · exact h6 v (M.refl v) (Or.inr h4)
  · exact Or.inr fun w hw he => hn4 w hw (e_t4 M he)

/-- `◯t3 ⊢ ◯Y`. -/
theorem boxt3_xf {v : M.W} (h : M.force v (.somehow t3)) : M.force v xf :=
  fun u hu hS => t3_Y M (h u hu hS)

/-- `[t6] ⊢ ◯Y ↠ ◯t3`. -/
theorem xf_boxt3 {v : M.W} (h6 : M.force v t6) (hx : M.force v xf) :
    M.force v (.somehow t3) :=
  fun u hu hS => Y_t3 M (SubframeModel.force_mono M t6 hu h6) (hx u hu hS)

/-- `[t6] ⊢ σ²⊥ ↠ relX (rn 3)`. -/
theorem b2_rX3 {v : M.W} (h6 : M.force v t6) (hb : M.force v b2) :
    M.force v (ZL.relX (RNEmbed.rnP 1).1) := by
  rcases (hb : M.force v (.somehow t3) ∨ M.force v ((PLLFormula.somehow t3).ifThen t3)) with hc | hg
  · exact Or.inl (boxt3_xf M hc)
  · exact Or.inr fun u hu hx => hg u hu (xf_boxt3 M (SubframeModel.force_mono M t6 hu h6) hx)

/-- `[t6] ⊢ (φ₃ ↠ σ²⊥) ↠ σ²⊥`, `φ₃ = relX (rn 7)`. -/
theorem phi3_b2 {v : M.W} (h6 : M.force v t6) :
    M.force v (((phiK 3).ifThen b2).ifThen b2) := by
  have e3 : phiK 3 = (ZL.relX (RNEmbed.rnP 2).1).or
      ((ZL.relX (RNEmbed.rnP 2).1).ifThen (ZL.relX (RNEmbed.rnP 1).1)) := by
    unfold phiK
    rw [RNEmbed.rn_odd_eq]
    rfl
  rw [e3]
  intro u hu H
  refine H u (M.refl u) (Or.inr fun w hw hA => ?_)
  exact b2_rX3 M (SubframeModel.force_mono M t6 (M.trans hu hw) h6) (H w hw (Or.inl hA))

/-- **`[t6] ⊢ gen 2`**, semantically. -/
theorem force_gen2 {v : M.W} (h6 : M.force v t6) : M.force v (gen 2) := by
  refine Or.inr fun u hu H => ?_
  exact phi3_b2 M h6 u hu fun w hw h3 => H w hw (Or.inl h3)

end Collapse

/-- **PROVED: `[t6] ⊢ y q`**, `q` the atom of code `1`. -/
theorem t6_gen2 : Deriv [t6] (gen 2) :=
  Interval.deriv_of_sem fun M _ _ hv => force_gen2 M hv

theorem xr_a1 : xr a1 = gen 2 := rfl

/-- **PROVED: `[t6 ∨ σ³⊥] ⊢ y q`**. -/
theorem bT_xr_a1 : Deriv [bT] (xr a1) := by
  rw [xr_a1]
  exact Deriv.orElim (Deriv.iden (.head _)) (Deriv.toHead t6_gen2) (Deriv.toHead (b3_le_gen 2))

/-- **Cell O3 FAILS (the cell holds)**: `[t6 ∨ σ³⊥] ⊢ relB σ³⊥ y (◯(p ∨ q) → ◯p ∨ ◯q)`. -/
theorem bT_O3 : Deriv [bT] (relB b3 xr O3) := by
  have h : Deriv ((PLLFormula.somehow ((xr a0).or (xr a1))) :: [bT]) (xr a1) :=
    Deriv.rename (fun _ hx => .tail _ hx) bT_xr_a1
  have h' : Deriv ((PLLFormula.somehow ((xr a0).or (xr a1))) :: [bT])
      (PLLFormula.somehow (xr a1)) := h.elim fun d => ⟨.laxIntro d⟩
  exact Deriv.impIntro (Deriv.orIntro2 h')

/-- **REFUTED: the target cell at O3**. -/
theorem not_targetCell_O3 : ¬ TargetCell O3 := fun h => h bT_O3

/-- **Cell O1 PASSES**: `[t6 ∨ σ³⊥] ⊬ relB σ³⊥ y (◯p → p)` (table `T1`). -/
theorem targetCell_O1 : TargetCell O1 := fun h =>
  (SubTab.no.verdict (bT.ifThen (relB b3 xr O1)) T1) (Deriv.impIntro h)

/-- **Cell O2 PASSES**: `[t6 ∨ σ³⊥] ⊬ relB σ³⊥ y (◯p ∨ ¬◯p)` (table `T2`). -/
theorem targetCell_O2 : TargetCell O2 := fun h =>
  (SubTab.no.verdict (bT.ifThen (relB b3 xr O2)) T2) (Deriv.impIntro h)

/-- The gate of the target's tables, watched failing: neither refutes the
derivable O3 cell. -/
theorem gate_T1 : T1.refutes (bT.ifThen (relB b3 xr O3)) = false ∧
    T2.refutes (bT.ifThen (relB b3 xr O3)) = false := by
  decide +kernel

theorem nd_top_q_imp : ¬ Deriv [] (topF.ifThen (.prop a1)) := SubTab.no.verdict _ K0

/-- **REFUTED: the target `PLLBelowTop`**: the copy sends `q` to the top,
`rel ⊤ ⊣⊢ b ⊢ y q ∧ b = rel q`, while `[⊤] ⊬ q`. -/
theorem not_pllBelowTop : ¬ PLLBelowTop := fun ⟨_, _, hf⟩ => by
  have h : Deriv [rel b3 bT yT topF] (rel b3 bT yT (.prop a1)) :=
    Deriv.andIntro (Deriv.cutHead (Deriv.andElim2 (Deriv.iden (.head _))) bT_xr_a1)
      (Deriv.andElim2 (Deriv.iden (.head _)))
  exact nd_top_q_imp (Deriv.impIntro ((hf topF (.prop a1)).mpr h))

/-- **REFUTED: the reduced target** (`C = O3`, `⊬ O3`). -/
theorem not_pllBelowTopReduced : ¬ PLLBelowTopReduced := fun h => pll_O3 (h O3 bT_O3)

/-! ### The cells of (Q1): `[t6] ⊬ aTr t3 C`, on the tables `ext K` -/

theorem q1_cell_p : ¬ Deriv [t6] (aTr t3 pA) := fun h =>
  (SubTab.no.verdict (t6.ifThen (aTr t3 pA)) (extT K0 [a0, a1])) (Deriv.impIntro h)

theorem q1_cell_O1 : ¬ Deriv [t6] (aTr t3 O1) := fun h =>
  (SubTab.no.verdict (t6.ifThen (aTr t3 O1)) (extT FreePLL.K1 [a0, a1])) (Deriv.impIntro h)

theorem q1_cell_O2 : ¬ Deriv [t6] (aTr t3 O2) := fun h =>
  (SubTab.no.verdict (t6.ifThen (aTr t3 O2)) (extT FreePLL.K2 [a0, a1])) (Deriv.impIntro h)

theorem q1_cell_O3 : ¬ Deriv [t6] (aTr t3 O3) := fun h =>
  (SubTab.no.verdict (t6.ifThen (aTr t3 O3)) (extT FreePLL.K3 [a0, a1])) (Deriv.impIntro h)

/-- The gate of the (Q1) tables, watched failing: `ext K1` does not refute the
image of the theorem `p → p`. -/
theorem gate_q1 :
    (extT FreePLL.K1 [a0, a1]).refutes (t6.ifThen (aTr t3 (pA.ifThen pA))) = false := by
  decide +kernel

end Cells

/-! ## Stage 3: proofs -/

/-! ### Semantic toolkit -/

/-- Forcing-equivalence in every model gives interderivability. -/
theorem interd_of_sem {φ ψ : PLLFormula}
    (h : ∀ (M : SubframeModel) (v : M.W), M.force v φ ↔ M.force v ψ) : Interd φ ψ :=
  ⟨Interval.deriv_of_sem fun M _ v hv => (h M v).mp hv,
   Interval.deriv_of_sem fun M _ v hv => (h M v).mpr hv⟩

theorem sem_of_interd {φ ψ : PLLFormula} (h : Interd φ ψ) (M : SubframeModel) (v : M.W) :
    M.force v φ ↔ M.force v ψ :=
  ⟨Interval.sem_of_deriv h.1 M v, Interval.sem_of_deriv h.2 M v⟩

theorem and_split {A B : PLLFormula} (h : atomFree (A.and B) = true) :
    atomFree A = true ∧ atomFree B = true :=
  Bool.and_eq_true_iff.mp h

theorem or_split {A B : PLLFormula} (h : atomFree (A.or B) = true) :
    atomFree A = true ∧ atomFree B = true :=
  Bool.and_eq_true_iff.mp h

theorem imp_split {A B : PLLFormula} (h : atomFree (A.ifThen B) = true) :
    atomFree A = true ∧ atomFree B = true :=
  Bool.and_eq_true_iff.mp h

/-- From `⊢ A ↠ B` to `[A] ⊢ B`. -/
theorem ctx_of_imp {A B : PLLFormula} (h : Deriv [] (A.ifThen B)) : Deriv [A] B :=
  Deriv.impElim (Deriv.rename (fun _ hx => absurd hx List.not_mem_nil) h) (Deriv.iden (.head _))

theorem deriv_top : Deriv [] topF := Deriv.impIntro (Deriv.iden (.head _))

/-- From `[⊤] ⊢ C` to `⊢ C`. -/
theorem of_top {C : PLLFormula} (h : Deriv [topF] C) : Deriv [] C := Deriv.cutHead deriv_top h

/-! ### Syntax: generators on closed formulas, `relB` and `subBot` -/

theorem rel_closed_indep (a b : PLLFormula) (x x' : String → PLLFormula) :
    ∀ A : PLLFormula, atomFree A = true → rel a b x A = rel a b x' A
  | .prop _, h => nomatch h
  | .falsePLL, _ => rfl
  | .and A B, h => by
      show (rel a b x A).and (rel a b x B) = (rel a b x' A).and (rel a b x' B)
      rw [rel_closed_indep a b x x' A (and_split h).1, rel_closed_indep a b x x' B (and_split h).2]
  | .or A B, h => by
      show (rel a b x A).or (rel a b x B) = (rel a b x' A).or (rel a b x' B)
      rw [rel_closed_indep a b x x' A (or_split h).1, rel_closed_indep a b x x' B (or_split h).2]
  | .ifThen A B, h => by
      show ((rel a b x A).ifThen (rel a b x B)).and b = ((rel a b x' A).ifThen (rel a b x' B)).and b
      rw [rel_closed_indep a b x x' A (imp_split h).1, rel_closed_indep a b x x' B (imp_split h).2]
  | .somehow A, h => by
      show (rel a b x A).somehow.and b = (rel a b x' A).somehow.and b
      rw [rel_closed_indep a b x x' A h]

theorem relB_closed (a : PLLFormula) (x : String → PLLFormula) :
    ∀ A : PLLFormula, atomFree A = true → relB a x A = subBot a A
  | .prop _, h => nomatch h
  | .falsePLL, _ => rfl
  | .and A B, h => by
      show (relB a x A).and (relB a x B) = (subBot a A).and (subBot a B)
      rw [relB_closed a x A (and_split h).1, relB_closed a x B (and_split h).2]
  | .or A B, h => by
      show (relB a x A).or (relB a x B) = (subBot a A).or (subBot a B)
      rw [relB_closed a x A (or_split h).1, relB_closed a x B (or_split h).2]
  | .ifThen A B, h => by
      show (relB a x A).ifThen (relB a x B) = (subBot a A).ifThen (subBot a B)
      rw [relB_closed a x A (imp_split h).1, relB_closed a x B (imp_split h).2]
  | .somehow A, h => by
      show (relB a x A).somehow = (subBot a A).somehow
      rw [relB_closed a x A h]

theorem relB_af {a : PLLFormula} {x : String → PLLFormula} (ha : atomFree a = true)
    (hx : ∀ p, atomFree (x p) = true) : ∀ A : PLLFormula, atomFree (relB a x A) = true
  | .prop p => hx p
  | .falsePLL => ha
  | .and A B => by
      show (atomFree (relB a x A) && atomFree (relB a x B)) = true
      rw [relB_af ha hx A, relB_af ha hx B]; rfl
  | .or A B => by
      show (atomFree (relB a x A) && atomFree (relB a x B)) = true
      rw [relB_af ha hx A, relB_af ha hx B]; rfl
  | .ifThen A B => by
      show (atomFree (relB a x A) && atomFree (relB a x B)) = true
      rw [relB_af ha hx A, relB_af ha hx B]; rfl
  | .somehow A => relB_af ha hx A

theorem subBot_bot : ∀ φ : PLLFormula, subBot .falsePLL φ = φ
  | .prop _ => rfl
  | .falsePLL => rfl
  | .and A B => by show (subBot _ A).and (subBot _ B) = _; rw [subBot_bot A, subBot_bot B]
  | .or A B => by show (subBot _ A).or (subBot _ B) = _; rw [subBot_bot A, subBot_bot B]
  | .ifThen A B => by show (subBot _ A).ifThen (subBot _ B) = _; rw [subBot_bot A, subBot_bot B]
  | .somehow A => by show (subBot _ A).somehow = _; rw [subBot_bot A]

theorem subBot_comp (a c : PLLFormula) :
    ∀ φ : PLLFormula, subBot a (subBot c φ) = subBot (subBot a c) φ
  | .prop _ => rfl
  | .falsePLL => rfl
  | .and A B => by
      show (subBot a (subBot c A)).and (subBot a (subBot c B)) = _
      rw [subBot_comp a c A, subBot_comp a c B]; rfl
  | .or A B => by
      show (subBot a (subBot c A)).or (subBot a (subBot c B)) = _
      rw [subBot_comp a c A, subBot_comp a c B]; rfl
  | .ifThen A B => by
      show (subBot a (subBot c A)).ifThen (subBot a (subBot c B)) = _
      rw [subBot_comp a c A, subBot_comp a c B]; rfl
  | .somehow A => by
      show (subBot a (subBot c A)).somehow = _
      rw [subBot_comp a c A]; rfl

/-- `σⁿ φ = φ[⊥ := σⁿ⊥]`. -/
theorem sigN_eq_subBot : ∀ (n : Nat) (φ : PLLFormula), sigN n φ = subBot (sigN n .falsePLL) φ
  | 0, φ => (subBot_bot φ).symm
  | n + 1, φ => by
      rw [InsideOut.sigN_succ, InsideOut.sigN_succ, sigN_eq_subBot n φ]
      exact subBot_comp t3 (sigN n .falsePLL) φ

/-- `relB t3 (p ↦ p ∨ t3) = aTr t3`. -/
theorem relB_eq_aTr : ∀ C : PLLFormula, relB t3 (fun p => (PLLFormula.prop p).or t3) C = aTr t3 C
  | .prop _ => rfl
  | .falsePLL => rfl
  | .and A B => by
      show (relB _ _ A).and (relB _ _ B) = (aTr t3 A).and (aTr t3 B)
      rw [relB_eq_aTr A, relB_eq_aTr B]
  | .or A B => by
      show (relB _ _ A).or (relB _ _ B) = (aTr t3 A).or (aTr t3 B)
      rw [relB_eq_aTr A, relB_eq_aTr B]
  | .ifThen A B => by
      show (relB _ _ A).ifThen (relB _ _ B) = (aTr t3 A).ifThen (aTr t3 B)
      rw [relB_eq_aTr A, relB_eq_aTr B]
  | .somehow A => by
      show (relB _ _ A).somehow = (aTr t3 A).somehow
      rw [relB_eq_aTr A]

/-- **The composition identity**: `rel (rel a b x c) b (rel a b x ∘ y) = rel a b x ∘ relB c y`. -/
theorem rel_relB (a b c : PLLFormula) (x y : String → PLLFormula) :
    ∀ A : PLLFormula,
      rel (rel a b x c) b (fun p => rel a b x (y p)) A = rel a b x (relB c y A)
  | .prop _ => rfl
  | .falsePLL => rfl
  | .and A B => by
      show (rel _ _ _ A).and (rel _ _ _ B) = _
      rw [rel_relB a b c x y A, rel_relB a b c x y B]; rfl
  | .or A B => by
      show (rel _ _ _ A).or (rel _ _ _ B) = _
      rw [rel_relB a b c x y A, rel_relB a b c x y B]; rfl
  | .ifThen A B => by
      show ((rel _ _ _ A).ifThen (rel _ _ _ B)).and b = _
      rw [rel_relB a b c x y A, rel_relB a b c x y B]; rfl
  | .somehow A => by
      show (rel _ _ _ A).somehow.and b = _
      rw [rel_relB a b c x y A]; rfl

/-! ### The semantics of `rel` at worlds forcing `b` -/

section RelSem

variable (M : SubframeModel) (a b : PLLFormula)

/-- At a world forcing `b`, `rel a b x' C ⟺ relB a x C` when `x' p ⟺ x p` there. -/
theorem rel_iff_relB_gen (x x' : String → PLLFormula)
    (hx : ∀ v p, M.force v b → (M.force v (x' p) ↔ M.force v (x p))) :
    ∀ (C : PLLFormula) (v : M.W), M.force v b → (M.force v (rel a b x' C) ↔ M.force v (relB a x C))
  | .prop p, v, hv => hx v p hv
  | .falsePLL, _, _ => Iff.rfl
  | .and A B, v, hv => and_congr (rel_iff_relB_gen x x' hx A v hv) (rel_iff_relB_gen x x' hx B v hv)
  | .or A B, v, hv => or_congr (rel_iff_relB_gen x x' hx A v hv) (rel_iff_relB_gen x x' hx B v hv)
  | .ifThen A B, v, hv => by
      show ((∀ u, M.le v u → M.force u (rel a b x' A) → M.force u (rel a b x' B)) ∧ M.force v b) ↔
        (∀ u, M.le v u → M.force u (relB a x A) → M.force u (relB a x B))
      constructor
      · intro h u hu hA
        have hub := SubframeModel.force_mono M b hu hv
        exact (rel_iff_relB_gen x x' hx B u hub).mp
          (h.1 u hu ((rel_iff_relB_gen x x' hx A u hub).mpr hA))
      · intro h
        refine ⟨fun u hu hA => ?_, hv⟩
        have hub := SubframeModel.force_mono M b hu hv
        exact (rel_iff_relB_gen x x' hx B u hub).mpr
          (h u hu ((rel_iff_relB_gen x x' hx A u hub).mp hA))
  | .somehow A, v, hv => by
      show ((∀ u, M.le v u → u ∈ M.S → M.force u (rel a b x' A)) ∧ M.force v b) ↔
        (∀ u, M.le v u → u ∈ M.S → M.force u (relB a x A))
      constructor
      · intro h u hu hS
        exact (rel_iff_relB_gen x x' hx A u (SubframeModel.force_mono M b hu hv)).mp (h.1 u hu hS)
      · intro h
        exact ⟨fun u hu hS => (rel_iff_relB_gen x x' hx A u
          (SubframeModel.force_mono M b hu hv)).mpr (h u hu hS), hv⟩

/-- `a ≤ rel a b x A` when `a ≤ b` and `a ≤ x p`. -/
theorem force_rel_of_a (x : String → PLLFormula) (hab : ∀ v, M.force v a → M.force v b)
    (hax : ∀ v p, M.force v a → M.force v (x p)) :
    ∀ (A : PLLFormula) (v : M.W), M.force v a → M.force v (rel a b x A)
  | .prop p, v, hv => hax v p hv
  | .falsePLL, _, hv => hv
  | .and A B, v, hv => ⟨force_rel_of_a x hab hax A v hv, force_rel_of_a x hab hax B v hv⟩
  | .or A _, v, hv => Or.inl (force_rel_of_a x hab hax A v hv)
  | .ifThen _ B, v, hv =>
      ⟨fun u hu _ => force_rel_of_a x hab hax B u (SubframeModel.force_mono M a hu hv), hab v hv⟩
  | .somehow A, v, hv =>
      ⟨fun u hu _ => force_rel_of_a x hab hax A u (SubframeModel.force_mono M a hu hv), hab v hv⟩

end RelSem

theorem hab_of {a b : PLLFormula} (h : Deriv [a] b) (M : SubframeModel) :
    ∀ v, M.force v a → M.force v b := fun v hv => Interval.sem_of_deriv h M v hv

/-! ### (R) and (R') -/

/-- **(R) PROVED** -/
theorem relClosed : RelClosed := by
  intro a b x A hA hab
  rw [rel_closed_indep a b x (fun _ => a) A hA]
  refine interd_of_sem fun M v => ?_
  have hab' := hab_of hab M
  have hb := fun hv => Interval.force_rel_b M a b (fun _ => a) hab' (fun u _ hu => hab' u hu) A v hv
  have hiff := rel_iff_relB_gen M a b (fun _ => a) (fun _ => a) (fun _ _ _ => Iff.rfl) A v
  rw [relB_closed a (fun _ => a) A hA] at hiff
  exact ⟨fun hv => ⟨(hiff (hb hv)).mp hv, hb hv⟩, fun hv => (hiff hv.2).mpr hv.1⟩

/-- **(R') PROVED** -/
theorem relGen : RelGen := by
  intro a b x C hab
  refine interd_of_sem fun M v => ?_
  have hab' := hab_of hab M
  have hb := fun hv => Interval.force_rel_b M a b (fun p => (x p).and b) hab'
    (fun _ _ hu => hu.2) C v hv
  have hiff := rel_iff_relB_gen M a b x (fun p => (x p).and b)
    (fun _ _ hv => ⟨fun h => h.1, fun h => ⟨h, hv⟩⟩) C v
  exact ⟨fun hv => ⟨(hiff (hb hv)).mp hv, hb hv⟩, fun hv => (hiff hv.2).mpr hv.1⟩

/-- `relC a b A ⊣⊢ A[⊥ := a] ∧ b` for closed `A`. -/
theorem relC_interd {a b : PLLFormula} (hab : Deriv [a] b) {A : PLLFormula}
    (hA : atomFree A = true) : Interd (relC a b A) ((subBot a A).and b) :=
  relClosed a b (fun _ => a) A hA hab

/-- `relC a b A ⊢ b`. -/
theorem relC_le_b {a b : PLLFormula} (hab : Deriv [a] b) {A : PLLFormula}
    (hA : atomFree A = true) : Deriv [relC a b A] b :=
  Deriv.andElim2 (relC_interd hab hA).1

/-- `τ = relC a b` preserves derivability between closed formulas. -/
theorem relC_mono {a b : PLLFormula} (hab : Deriv [a] b) {A B : PLLFormula}
    (hA : atomFree A = true) (hB : atomFree B = true) (h : Deriv [A] B) :
    Deriv [relC a b A] (relC a b B) := by
  have hs : Deriv [subBot a A] (subBot a B) :=
    subBot_deriv a (Γ := [A]) (fun ψ hψ => by rw [List.mem_singleton.mp hψ]; exact hA) hB h
  refine Deriv.cutHead ?_ (relC_interd hab hB).2
  exact Deriv.andIntro (Deriv.cutHead (Deriv.andElim1 (relC_interd hab hA).1) hs)
    (relC_le_b hab hA)

/-- **The reduction PROVED**: `[a] ⊢ b ⟹ (CopyF0In a b ⟺ TopAvoid a b)`. -/
theorem copyIffTopAvoid : CopyIffTopAvoid := by
  intro a b hab
  constructor
  · intro hc C hC h
    have h1 : Deriv [relC a b topF] (relC a b C) := by
      refine Deriv.cutHead ?_ (relC_interd hab hC).2
      have hb : Deriv [relC a b topF] b := relC_le_b hab rfl
      exact Deriv.andIntro (Deriv.cutHead hb h) hb
    exact of_top ((hc topF C rfl hC).mpr h1)
  · intro ht A B hA hB
    refine ⟨relC_mono hab hA hB, fun h => ?_⟩
    have h1 : Deriv [(subBot a A).and b] (subBot a B) :=
      Deriv.andElim1 (Deriv.cutHead (Deriv.cutHead (relC_interd hab hA).2 h) (relC_interd hab hB).1)
    have h2 : Deriv [b] (subBot a (A.ifThen B)) :=
      Deriv.impIntro (Deriv.cutHead (Deriv.andIntro (Deriv.iden (.head _))
        (Deriv.iden (.tail _ (.head _)))) h1)
    exact ctx_of_imp (ht (A.ifThen B) (Bool.and_eq_true_iff.mpr ⟨hA, hB⟩) h2)

/-- **(R') with generators PROVED**. -/
theorem genIff : GenIff := by
  intro a b x hab hax
  have hiff := fun C => relGen a b x C hab
  constructor
  · intro ⟨_, _, hf⟩ C h
    have h1 : Deriv [rel a b (fun p => (x p).and b) topF] (rel a b (fun p => (x p).and b) C) := by
      refine Deriv.cutHead ?_ (hiff C).2
      have hb : Deriv [rel a b (fun p => (x p).and b) topF] b :=
        Deriv.andElim2 (Deriv.iden (.head _))
      exact Deriv.andIntro (Deriv.cutHead hb h) hb
    exact of_top ((hf topF C).mpr h1)
  · intro ht
    refine ⟨fun p => Deriv.andIntro (hax p) hab, fun p => Deriv.andElim2 (Deriv.iden (.head _)),
      fun A B => ⟨fun h => ?_, fun h => ?_⟩⟩
    · have hr := relB_preservesO a x (fun M v p hv => Interval.sem_of_deriv (hax p) M v hv) h
      refine Deriv.cutHead ?_ (hiff B).2
      exact Deriv.andIntro (Deriv.cutHead (Deriv.andElim1 (hiff A).1) hr)
        (Deriv.andElim2 (hiff A).1)
    · have h1 : Deriv [(relB a x A).and b] (relB a x B) :=
        Deriv.andElim1 (Deriv.cutHead (Deriv.cutHead (hiff A).2 h) (hiff B).1)
      have h2 : Deriv [b] (relB a x (A.ifThen B)) :=
        Deriv.impIntro (Deriv.cutHead (Deriv.andIntro (Deriv.iden (.head _))
          (Deriv.iden (.tail _ (.head _)))) h1)
      exact ctx_of_imp (ht (A.ifThen B) h2)

/-- **(N) PROVED**: `CopyF0In ⊥ b ⟺ ⊢ b`, `b` closed. -/
theorem copyAtBot : CopyAtBot := by
  intro b hb
  rw [copyIffTopAvoid .falsePLL b (Deriv.falsoElim _ (Deriv.iden (.head _)))]
  constructor
  · intro ht
    exact ht b hb (by rw [subBot_bot]; exact Deriv.iden (.head _))
  · intro hd C _ h
    rw [subBot_bot] at h
    exact Deriv.cutHead hd h

/-! ### (T6) -/

/-- `t6` holds at every world of `ext M`. -/
theorem t6_ext (M : SubframeModel) : ∀ w : XW M.W, (ext M).force w t6 := by
  intro w u _ h5
  cases u with
  | orig x =>
    exfalso
    rcases (h5 : (ext M).force (XW.orig x) t3 ∨ (ext M).force (XW.orig x) t4) with h3 | h4
    · exact t3_orig M x h3
    · exact not_e_nT M (h4 XW.nT trivial (t3_top M trivial))
  | nT => exact t3_top M trivial
  | eT => exact t3_top M trivial

/-- **(T6) PROVED, every formula**: `[t6] ⊢ σC ⟹ ⊢ C`. -/
theorem sigAvoidT6 : SigAvoidT6 := by
  intro χ h
  rcases SubTab.complete χ with ⟨c, hc⟩ | ⟨m, hm⟩
  · exact SubTab.holds_of_check hc
  · exfalso
    have hm0 : m.refutes χ = true := hm
    simp only [SubTab.SubCM.refutes, Bool.and_eq_true, Bool.not_eq_true'] at hm0
    have hr := (SubTab.SubCM.ok_parts hm0.1).1
    have hs := Interval.sem_of_deriv h (ext (m.toModel hm0.1)) (XW.orig ⟨m.root, hr⟩)
      (t6_ext _ _)
    have hf := (orig_sig (m.toModel hm0.1) χ ⟨m.root, hr⟩).mp hs
    have hb := (SubTab.SubCM.forceB_iff hm0.1 χ ⟨m.root, hr⟩).mpr hf
    rw [hm0.2] at hb
    exact Bool.false_ne_true hb

/-- **(T6) PROVED** -/
theorem topAvoidT3T6 : TopAvoidT3T6 := fun C _ h => sigAvoidT6 C h

/-- **(W1) PROVED**: `τ = relC t3 t6` is faithful on closed formulas. -/
theorem copyT3T6 : CopyT3T6 := (copyIffTopAvoid t3 t6 t3_t6).mpr topAvoidT3T6

/-- **(T5) REFUTED**: no copy of F0 in `[t3, t5]` by `relC`. -/
theorem not_copyT3T5 : ¬ CopyT3T5 := fun h =>
  not_topAvoidT3T5 ((copyIffTopAvoid t3 t5 (Deriv.orIntro1 (Deriv.iden (.head _)))).mp h)

/-! ### (Q1): Friedman's translation reflects theorems under `t6` -/

/-- The tops of `ext M` satisfy every `aTr t3`-formula. -/
theorem top_aTr (M : SubframeModel) :
    ∀ (ψ : PLLFormula) (w : XW M.W), isTopX M w → (ext M).force w (aTr t3 ψ)
  | .prop _, _, hw => Or.inr (t3_top M hw)
  | .falsePLL, _, hw => t3_top M hw
  | .and A B, w, hw => ⟨top_aTr M A w hw, top_aTr M B w hw⟩
  | .or A _, w, hw => Or.inl (top_aTr M A w hw)
  | .ifThen _ B, _, hw => fun v hv _ => top_aTr M B v (topX_up M hw hv)
  | .somehow A, _, hw => fun v hv _ => top_aTr M A v (topX_up M hw hv)

/-- **At old worlds of `ext M`, `aTr t3 ψ` holds exactly where `ψ` holds in `M`.** -/
theorem orig_aTr (M : SubframeModel) :
    ∀ (ψ : PLLFormula) (x : M.W), (ext M).force (XW.orig x) (aTr t3 ψ) ↔ M.force x ψ
  | .prop _, x => ⟨fun h => h.elim id fun h3 => (t3_orig M x h3).elim, Or.inl⟩
  | .falsePLL, x => ⟨fun h => t3_orig M x h, False.elim⟩
  | .and A B, x => and_congr (orig_aTr M A x) (orig_aTr M B x)
  | .or A B, x => or_congr (orig_aTr M A x) (orig_aTr M B x)
  | .ifThen A B, x =>
      ⟨fun h y hxy hA => (orig_aTr M B y).mp (h (XW.orig y) hxy ((orig_aTr M A y).mpr hA)),
       fun h v hv hA => by
        cases v with
        | orig y => exact (orig_aTr M B y).mpr (h y hv ((orig_aTr M A y).mp hA))
        | nT => exact top_aTr M B XW.nT trivial
        | eT => exact top_aTr M B XW.eT trivial⟩
  | .somehow A, x =>
      ⟨fun h y hxy hS => (orig_aTr M A y).mp (h (XW.orig y) hxy hS),
       fun h v hv hS => by
        cases v with
        | orig y => exact (orig_aTr M A y).mpr (h y hv hS)
        | nT => exact top_aTr M A XW.nT trivial
        | eT => exact False.elim hS⟩

/-- **(Q1), reduced, PROVED**: `[t6] ⊢ aTr t3 C ⟹ ⊢ C`. -/
theorem pllSelfReduced : PLLSelfReduced := by
  intro χ h
  rcases SubTab.complete χ with ⟨c, hc⟩ | ⟨m, hm⟩
  · exact SubTab.holds_of_check hc
  · exfalso
    have hm0 : m.refutes χ = true := hm
    simp only [SubTab.SubCM.refutes, Bool.and_eq_true, Bool.not_eq_true'] at hm0
    have hr := (SubTab.SubCM.ok_parts hm0.1).1
    have hs := Interval.sem_of_deriv h (ext (m.toModel hm0.1)) (XW.orig ⟨m.root, hr⟩)
      (t6_ext _ _)
    have hf := (orig_aTr (m.toModel hm0.1) χ ⟨m.root, hr⟩).mp hs
    have hb := (SubTab.SubCM.forceB_iff hm0.1 χ ⟨m.root, hr⟩).mpr hf
    rw [hm0.2] at hb
    exact Bool.false_ne_true hb

/-- **(Q1) PROVED**: `τ_P` is a faithful copy of PLL in `[t3, t6]`. -/
theorem pllSelf : PLLSelf := by
  have h := (genIff t3 t6 (fun p => (PLLFormula.prop p).or t3) t3_t6
    (fun _ => Deriv.orIntro2 (Deriv.iden (.head _)))).mpr fun C hC => by
      rw [relB_eq_aTr] at hC
      exact pllSelfReduced C hC
  exact h

/-! ### (T6n) and (C) -/

theorem nd_bot : ¬ Deriv [] .falsePLL := SubTab.no.verdict .falsePLL K0

theorem nd_sigN_bot (n : Nat) : ¬ Deriv [] (sigN n .falsePLL) := fun h =>
  nd_bot (sigN_reflects n _ h)

/-- **(T6n) PROVED** -/
theorem topAvoidN : TopAvoidN := by
  intro n hn
  cases n with
  | zero => exact absurd hn (Nat.not_succ_le_zero 0)
  | succ m =>
    refine ⟨fun C _ h => ?_, fun h => (disjunction_property h).elim nd_t6 (nd_sigN_bot (m + 1))⟩
    rw [← sigN_eq_subBot] at h
    have h' : Deriv [t6] (sigN (m + 1) C) := Deriv.cutHead (Deriv.orIntro1 (Deriv.iden (.head _))) h
    rw [InsideOut.sigN_succ] at h'
    exact sigN_reflects m C (sigAvoidT6 _ h')

theorem nd_t6_bot_imp : ¬ Deriv [] (t6.ifThen .falsePLL) := SubTab.no.verdict _ K0

/-- **(C) PROVED**: `[t6] ⊬ σⁿ⊥`. -/
theorem notCofinal : NotCofinal
  | 0, h => nd_t6_bot_imp (Deriv.impIntro h)
  | m + 1, h => by
      rw [InsideOut.sigN_succ] at h
      exact nd_sigN_bot m (sigAvoidT6 _ h)

/-- **(C) PROVED**: the only upper bound of the bases `σⁿ⊥` is `⊤`. -/
theorem basesOnlyTop : BasesOnlyTop := by
  intro x _ h
  rcases SubTab.complete x with ⟨c, hc⟩ | ⟨m, hm⟩
  · exact SubTab.holds_of_check hc
  · obtain ⟨N, hN⟩ := InsideOut.cm_eventually (x := x) (m := m) hm
    exact absurd (h N) (hN N (Nat.le_refl N))

/-! ### (F): iterates -/

theorem relC_af {a b : PLLFormula} (ha : atomFree a = true) (hb : atomFree b = true)
    (A : PLLFormula) : atomFree (relC a b A) = true :=
  Interval.atomFree_rel ha hb (fun _ => ha) A

theorem tauN_af {a b : PLLFormula} (ha : atomFree a = true) (hb : atomFree b = true) :
    ∀ (d : Nat) (A : PLLFormula), atomFree A = true → atomFree (tauN a b d A) = true
  | 0, _, hA => hA
  | d + 1, A, _ => tauN_af ha hb d (relC a b A) (relC_af ha hb A)

theorem tauN_succ' (a b : PLLFormula) :
    ∀ (d : Nat) (A : PLLFormula), tauN a b (d + 1) A = relC a b (tauN a b d A)
  | 0, _ => rfl
  | d + 1, A => tauN_succ' a b d (relC a b A)

theorem tauN_mono {a b : PLLFormula} (ha : atomFree a = true) (hb : atomFree b = true)
    (hab : Deriv [a] b) : ∀ (d : Nat) {A B : PLLFormula}, atomFree A = true →
      atomFree B = true → Deriv [A] B → Deriv [tauN a b d A] (tauN a b d B)
  | 0, _, _, _, _, h => h
  | d + 1, _, _, hA, hB, h =>
      tauN_mono ha hb hab d (relC_af ha hb _) (relC_af ha hb _) (relC_mono hab hA hB h)

theorem tauN_faithful {a b : PLLFormula} (ha : atomFree a = true) (hb : atomFree b = true)
    (hc : CopyF0In a b) : ∀ (d : Nat) {A B : PLLFormula}, atomFree A = true →
      atomFree B = true → (Deriv [A] B ↔ Deriv [tauN a b d A] (tauN a b d B))
  | 0, _, _, _, _ => Iff.rfl
  | d + 1, _, _, hA, hB =>
      (hc _ _ hA hB).trans (tauN_faithful ha hb hc d (relC_af ha hb _) (relC_af ha hb _))

theorem bot_le (A : PLLFormula) : Deriv [.falsePLL] A := Deriv.falsoElim _ (Deriv.iden (.head _))

theorem le_top (A : PLLFormula) : Deriv [A] topF := Deriv.impIntro (Deriv.iden (.head _))

/-- **(F) PROVED** -/
theorem iterBounds : IterBounds := by
  intro a b ha hb hab d
  exact ⟨tauN_mono ha hb hab d (A := .falsePLL) (B := relC a b .falsePLL) rfl
      (relC_af ha hb _) (bot_le _),
    tauN_mono ha hb hab d (A := relC a b topF) (B := topF) (relC_af ha hb _) rfl (le_top _),
    fun A hA => ⟨tauN_mono ha hb hab d rfl hA (bot_le A), tauN_mono ha hb hab d hA rfl (le_top A)⟩⟩

/-- **(F) PROVED**: a fixed point of `τ` lies in every `[τᵈ⊥, τᵈ⊤]`. -/
theorem fixedInAll : FixedInAll := by
  intro a b ha hb hab x hx hfix d
  have key : ∀ d, Interd (tauN a b d x) x := by
    intro d
    induction d with
    | zero => exact Interd.refl x
    | succ d ih =>
      rw [tauN_succ']
      exact ⟨Deriv.cutHead (relC_mono hab (tauN_af ha hb d x hx) hx ih.1) hfix.1,
        Deriv.cutHead hfix.2 (relC_mono hab hx (tauN_af ha hb d x hx) ih.2)⟩
  have hbd := (iterBounds a b ha hb hab d).2.2 x hx
  exact ⟨Deriv.cutHead hbd.1 (key d).1, Deriv.cutHead (key d).2 hbd.2⟩

/-- **(F) PROVED**: the only fixed point of `σ` is `⊤`. -/
theorem sigFixedTop : SigFixedTop := by
  intro x hx hfix
  have key : ∀ n, Interd (sigN n x) x := by
    intro n
    induction n with
    | zero => exact Interd.refl x
    | succ n ih =>
      rw [InsideOut.sigN_succ]
      exact ⟨Deriv.cutHead (sig_mono (sigN_vf n hx) hx ih.1) hfix.1,
        Deriv.cutHead hfix.2 (sig_mono hx (sigN_vf n hx) ih.2)⟩
  exact basesOnlyTop x hx fun n => Deriv.cutHead (sigN_bot_le n x hx) (key n).1

/-! ### (W2), (W3), (W4) -/

theorem interd_and_top (A : PLLFormula) : Interd A (A.and topF) :=
  ⟨Deriv.andIntro (Deriv.iden (.head _)) (le_top A), Deriv.andElim1 (Deriv.iden (.head _))⟩

/-- **(W2), general, PROVED**: the iterates are interval translations. -/
theorem iterRel : IterRel := by
  intro a b ha hb hab d
  induction d with
  | zero =>
    intro A hA
    have h := relC_interd (a := .falsePLL) (b := topF) (le_top _) hA
    rw [subBot_bot] at h
    exact (interd_and_top A).trans h.symm
  | succ d ih =>
    intro A hA
    rw [tauN_succ' a b d A, tauN_succ' a b d .falsePLL, tauN_succ' a b d topF]
    have hξ := tauN_af ha hb d .falsePLL rfl
    have hζ := tauN_af ha hb d topF rfl
    have hr := relC_af hξ hζ A
    have h1 : Interd (relC a b (tauN a b d A)) (relC a b (relC (tauN a b d .falsePLL)
        (tauN a b d topF) A)) :=
      ⟨relC_mono hab (tauN_af ha hb d A hA) hr (ih A hA).1,
       relC_mono hab hr (tauN_af ha hb d A hA) (ih A hA).2⟩
    refine h1.trans (interd_of_sem fun M v => ?_)
    have hab' := hab_of hab M
    exact (Interval.rel_comp M a b (fun _ => a) (tauN a b d .falsePLL) (tauN a b d topF)
      (fun _ => tauN a b d .falsePLL) hab' (fun u _ hu => hab' u hu) A v).symm

/-- **(W2) PROVED** -/
theorem w2 : W2 := iterRel t3 t6 rfl rfl t3_t6

/-- **(W3), general, PROVED** -/
theorem strictNestOf : StrictNestOf := by
  intro a b ha hb hab hc ha0 hb0 d
  have hbd := iterBounds a b ha hb hab d
  refine ⟨hbd.1, fun h => ha0 ((tauN_faithful ha hb hc d (A := a) (B := .falsePLL) ha rfl).mpr h),
    hbd.2.1, fun h => hb0 ?_⟩
  have h1 : Deriv [topF] (relC a b topF) :=
    (tauN_faithful ha hb hc d (A := topF) (B := relC a b topF) rfl (relC_af ha hb _)).mpr h
  exact of_top (Deriv.cutHead h1 (relC_le_b hab rfl))

/-- **(W3) PROVED** -/
theorem w3 : W3 := strictNestOf t3 t6 rfl rfl t3_t6 copyT3T6 nd_t3_bot nd_t6

/-- **(W4), general, PROVED** -/
theorem iterCopyOf : IterCopyOf := by
  intro a b x ha hb hx ha0 hb0 ⟨hax, hxb, hf⟩ d
  have hab : Deriv [a] b := Deriv.cutHead (hax "") (hxb "")
  have hc : CopyF0In a b := fun A B hA hB => by
    have h := hf A B
    rw [rel_closed_indep a b x (fun _ => a) A hA, rel_closed_indep a b x (fun _ => a) B hB] at h
    exact h
  have hrel : ∀ A, atomFree (rel a b x A) = true := Interval.atomFree_rel ha hb hx
  have hlo : ∀ A, Deriv [a] (rel a b x A) := fun A => Interval.deriv_of_sem fun M _ v hv =>
    force_rel_of_a M a b x (hab_of hab M) (fun u p hu => Interval.sem_of_deriv (hax p) M u hu) A v hv
  have hhi : ∀ A, Deriv [rel a b x A] b := fun A => Interval.deriv_of_sem fun M _ v hv =>
    Interval.force_rel_b M a b x (hab_of hab M)
      (fun u p hu => Interval.sem_of_deriv (hxb p) M u hu) A v hv
  have haa : Deriv [a] (relC a b a) :=
    Deriv.cutHead (Deriv.andIntro (subBot_top a ha) hab) (relC_interd hab ha).2
  refine ⟨fun A B => (hf A B).trans (tauN_faithful ha hb hc d (hrel A) (hrel B)),
    fun A => ⟨tauN_mono ha hb hab d ha (hrel A) (hlo A), tauN_mono ha hb hab d (hrel A) hb (hhi A)⟩,
    tauN_mono ha hb hab d (A := a) (B := relC a b a) ha (relC_af ha hb a) haa,
    fun h => ha0 ((hc a .falsePLL ha rfl).mpr
      ((tauN_faithful ha hb hc d (A := relC a b a) (B := a) (relC_af ha hb a) ha).mpr h)),
    tauN_mono ha hb hab d (A := relC a b b) (B := b) (relC_af ha hb b) hb (relC_le_b hab hb),
    fun h => hb0 ?_⟩
  have h1 : Deriv [b] (relC a b b) :=
    (tauN_faithful ha hb hc d (A := b) (B := relC a b b) hb (relC_af ha hb b)).mpr h
  exact of_top ((hc topF b rfl hb).mpr (Deriv.cutHead (relC_le_b hab rfl) h1))

theorem yT_af (p : String) : atomFree (yT p) = true := by
  show (atomFree (xr p) && atomFree bT) = true
  rw [xr_vf]
  rfl

theorem nd_b3_bot : ¬ Deriv [b3] .falsePLL := fun h =>
  (sigN_bot_strict 2).2 (Deriv.falsoElim _ h)

theorem nd_bT : ¬ Deriv [] bT := fun h =>
  (disjunction_property h).elim nd_t6 (nd_sigN_bot 3)

/-- **(W4) PROVED** (conditional on the REFUTED target, so of no further use). -/
theorem w4 : W4 := fun h => iterCopyOf b3 bT yT rfl rfl yT_af nd_b3_bot nd_bT h

/-! ### (Q2): the tower in the free PLL algebra -/

theorem tauP_faithful : ∀ A B : PLLFormula, Deriv [A] B ↔ Deriv [tauP A] (tauP B) := pllSelf.2.2

theorem tauPN_faithful : ∀ (d : Nat) (A B : PLLFormula),
    Deriv [A] B ↔ Deriv [tauPN d A] (tauPN d B)
  | 0, _, _ => Iff.rfl
  | d + 1, A, B => (tauP_faithful A B).trans (tauPN_faithful d (tauP A) (tauP B))

theorem tauPN_succ' : ∀ (d : Nat) (A : PLLFormula), tauPN (d + 1) A = tauP (tauPN d A)
  | 0, _ => rfl
  | d + 1, A => tauPN_succ' d (tauP A)

theorem tauP_interd {A B : PLLFormula} (h : Interd A B) : Interd (tauP A) (tauP B) :=
  ⟨(tauP_faithful A B).mp h.1, (tauP_faithful B A).mp h.2⟩

theorem relB_id : ∀ A : PLLFormula, relB .falsePLL (fun p => .prop p) A = A
  | .prop _ => rfl
  | .falsePLL => rfl
  | .and A B => by show (relB _ _ A).and (relB _ _ B) = _; rw [relB_id A, relB_id B]
  | .or A B => by show (relB _ _ A).or (relB _ _ B) = _; rw [relB_id A, relB_id B]
  | .ifThen A B => by show (relB _ _ A).ifThen (relB _ _ B) = _; rw [relB_id A, relB_id B]
  | .somehow A => by show (relB _ _ A).somehow = _; rw [relB_id A]

theorem deriv_iff_of_interd {A A' B B' : PLLFormula} (hA : Interd A A') (hB : Interd B B') :
    Deriv [A] B ↔ Deriv [A'] B' :=
  ⟨fun h => Deriv.cutHead (Deriv.cutHead hA.2 h) hB.1,
   fun h => Deriv.cutHead (Deriv.cutHead hA.1 h) hB.2⟩

/-- `τ_Pᵈ` is the interval translation of `[τ_Pᵈ⊥, τ_Pᵈ⊤]` with generators `τ_Pᵈ p`. -/
theorem tauPN_rel : ∀ (d : Nat) (A : PLLFormula), Interd (tauPN d A)
    (rel (tauPN d .falsePLL) (tauPN d topF) (fun p => tauPN d (.prop p)) A)
  | 0, A => interd_of_sem fun M v => by
      have h := rel_iff_relB_gen M .falsePLL topF (fun p => .prop p) (fun p => .prop p)
        (fun _ _ _ => Iff.rfl) A v (fun _ _ h => h)
      rw [relB_id] at h
      exact h.symm
  | d + 1, A => by
      have hfun : (fun p => tauPN (d + 1) (.prop p)) = fun p => tauP (tauPN d (.prop p)) :=
        funext fun p => tauPN_succ' d (.prop p)
      rw [hfun, tauPN_succ' d A, tauPN_succ' d .falsePLL, tauPN_succ' d topF]
      refine (tauP_interd (tauPN_rel d A)).trans (interd_of_sem fun M v => ?_)
      exact (Interval.rel_comp M t3 t6 xP (tauPN d .falsePLL) (tauPN d topF)
        (fun p => tauPN d (.prop p)) (hab_of t3_t6 M) (fun _ _ h => h.2) A v).symm

/-- **(Q2) PROVED** -/
theorem pllSelfTower : PLLSelfTower := by
  intro d
  refine ⟨tauPN_faithful d, ⟨fun p => (tauPN_faithful d _ _).mp (bot_le _),
      fun p => (tauPN_faithful d _ _).mp (le_top _),
      fun A B => (tauPN_faithful d A B).trans
        (deriv_iff_of_interd (tauPN_rel d A) (tauPN_rel d B))⟩,
    tauPN_rel d,
    (tauPN_faithful d .falsePLL (tauP .falsePLL)).mp (bot_le _),
    fun h => nd_t3_bot ((tauPN_faithful d (tauP .falsePLL) .falsePLL).mpr h),
    (tauPN_faithful d (tauP topF) topF).mp (le_top _),
    fun h => nd_t6 (of_top (Deriv.andElim2 ((tauPN_faithful d topF (tauP topF)).mpr h)))⟩

/-! ### (Q3): the tower carried into F0 by `g` -/

theorem g_faithful (A B : PLLFormula) : Deriv [A] B ↔ Deriv [gR A] (gR B) := freeReaders A B

theorem b3_le_g (A : PLLFormula) : Deriv [b3] (gR A) :=
  Interval.deriv_of_sem fun M _ v hv =>
    Pair.force_relB_of_b M b3 xr (fun u a hu => b3_le_xr_sem M u a hu) A v hv

/-- **(Q3) PROVED** -/
theorem pllTowerInF0 : PLLTowerInF0 := by
  intro d
  obtain ⟨hf, _, _, h1, h2, h3, h4⟩ := pllSelfTower d
  refine ⟨fun A B => (hf A B).trans (g_faithful _ _),
    fun A => ⟨(g_faithful _ _).mp ((hf _ _).mp (bot_le A)), (g_faithful _ _).mp ((hf _ _).mp (le_top A))⟩,
    b3_le_g _, (g_faithful _ _).mp h1, fun h => h2 ((g_faithful _ _).mpr h),
    (g_faithful _ _).mp h3, fun h => h4 ((g_faithful _ _).mpr h),
    fun A => ⟨(g_faithful _ _).mp (Deriv.cutHead h1 ((tauPN_faithful (d + 1) _ _).mp (bot_le A))),
      (g_faithful _ _).mp (Deriv.cutHead ((tauPN_faithful (d + 1) _ _).mp (le_top A)) h3)⟩⟩

/-- **PROVED**: the first step of the tower in F0 is `[σ⁴⊥, σ³ t6]`. -/
theorem towerFirstStep : TowerFirstStep := by
  refine ⟨(InsideOut.sigN_succ_bot 3).symm, ?_⟩
  have e : gR t6 = sigN 3 t6 := by
    show relB b3 xr t6 = sigN 3 t6
    rw [relB_closed b3 xr t6 rfl, sigN_eq_subBot 3 t6]
    rfl
  show Interd (((gR t3).ifThen (gR t3)).and (gR t6)) (sigN 3 t6)
  rw [e]
  exact ⟨Deriv.andElim2 (Deriv.iden (.head _)),
    Deriv.andIntro (Deriv.impIntro (Deriv.iden (.head _))) (Deriv.iden (.head _))⟩

/-! ### (P1): the composite `τ ∘ g` -/

theorem g_af (A : PLLFormula) : atomFree (gR A) = true := relB_af rfl xr_vf A

/-- **(P1) PROVED**: `τ ∘ g` is a faithful copy of PLL in `[τ σ³⊥, t6]`. -/
theorem pllInT6 : PLLInT6 := by
  refine ⟨fun p => relC_mono t3_t6 rfl (xr_vf p) (b3_le_xr p),
    fun p => relC_le_b t3_t6 (xr_vf p), fun A B => ?_⟩
  show Deriv [A] B ↔
    Deriv [rel (rel t3 t6 (fun _ => t3) b3) t6 (fun p => rel t3 t6 (fun _ => t3) (xr p)) A]
      (rel (rel t3 t6 (fun _ => t3) b3) t6 (fun p => rel t3 t6 (fun _ => t3) (xr p)) B)
  rw [rel_relB t3 t6 b3 (fun _ => t3) xr A, rel_relB t3 t6 b3 (fun _ => t3) xr B]
  exact (g_faithful A B).trans (copyT3T6 _ _ (g_af A) (g_af B))

end MovingTop
end F0
end PLLND

/-! ## Axiom pins -/

#axioms_within PLLND.F0.MovingTop.t5_sig2_imp [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.t5Cell [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.gate_t5 [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.nd_t3 [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.not_topAvoidT3T5 [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.t3_t6 [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.nd_t6 [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.t6Below [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.nd_t6_sig2 [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.nd_t6_sig3 [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.nd_sig2_t6 [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.nd_b3_t6 [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.baseTauIncomparable [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.t3_Y [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.Y_t3 [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.b2_rX3 [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.phi3_b2 [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.force_gen2 [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.t6_gen2 [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.xr_a1 [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.bT_xr_a1 [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.bT_O3 [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.not_targetCell_O3 [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.targetCell_O1 [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.targetCell_O2 [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.gate_T1 [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.not_pllBelowTop [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.not_pllBelowTopReduced [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.q1_cell_p [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.q1_cell_O1 [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.q1_cell_O2 [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.q1_cell_O3 [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.gate_q1 [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.relClosed [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.relGen [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.copyIffTopAvoid [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.genIff [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.copyAtBot [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.sigAvoidT6 [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.copyT3T6 [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.not_copyT3T5 [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.pllSelfReduced [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.pllSelf [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.interd_of_sem [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.rel_closed_indep [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.relB_closed [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.subBot_comp [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.sigN_eq_subBot [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.relB_eq_aTr [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.rel_relB [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.rel_iff_relB_gen [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.force_rel_of_a [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.relC_mono [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.t6_ext [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.topAvoidT3T6 [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.orig_aTr [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.topAvoidN [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.notCofinal [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.basesOnlyTop [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.tauN_faithful [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.iterBounds [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.fixedInAll [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.sigFixedTop [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.iterRel [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.w2 [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.strictNestOf [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.w3 [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.iterCopyOf [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.w4 [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.tauPN_faithful [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.tauPN_rel [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.pllSelfTower [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.b3_le_g [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.pllTowerInF0 [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.towerFirstStep [propext, Quot.sound]
#axioms_within PLLND.F0.MovingTop.pllInT6 [propext, Quot.sound]
