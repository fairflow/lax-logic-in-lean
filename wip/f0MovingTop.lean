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
