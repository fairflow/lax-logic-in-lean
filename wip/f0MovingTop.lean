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

open PLLFormula

namespace PLLND
namespace F0
namespace MovingTop

open SemUI Sig FreeHAn Base3 FreePLL
open Interval (rel FreeInPLL topF)
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

end MovingTop
end F0
end PLLND
