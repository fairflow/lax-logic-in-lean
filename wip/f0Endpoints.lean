import wip.f0MovingTop
import Meta.Audit

/-!
# Endpoint conditions for faithful interval copies of F0 and of PLL

Matthew, 2026-11-01: "I STILL do not know what conditions on endpoints are
required to nest the PLL tower within an interval `[a, b]` and it seems a more
general result hasn't yet been attempted."  This file states the question for
arbitrary closed endpoints `a`, `b` with `[a] ⊢ b`, the conditions known to be
necessary, a sufficient condition by gadgets (the template of `Sig.ext`), and
the conjectures K1–K5 of the manager's brief.

## The statements (Stage 1, committed before any proof, METHOD.md §1)

`rel a b x` is the interval translation (`wip/f0FreeInterval.lean`), `relC a b`
its closed form, `subBot a C = C[⊥ := a]`, `aTr a` Friedman's A-translation
(`p ↦ p ∨ a`, `⊥ ↦ a`), `σ = subBot t3`, `◯⊥ = e`, `¬◯⊥ = ne`,
`¬¬◯⊥ = nne` (`⊣⊢ t4`), `T a = t3[⊥ := a] = ◯a ∨ (◯a ↠ a)`.

    SelfStep a b   :  FreeInPLL a b (p ↦ (p ∨ a) ∧ b)
    SelfStepReduced a b :  ∀ C,  [b] ⊢ aTr a C  ⟹  ⊢ C
    ClosedStep a b :  ∃ x,  (∀ p, x p closed)  ∧  FreeInPLL a b x
    CopyStep a b   :  CopyF0In a b   ( ⟺ ∀ C closed, [b] ⊢ C[⊥:=a] ⟹ ⊢ C, `copyIffTopAvoid`)

### Cheap implications

    SelfIffReduced :  [a] ⊢ b  ⟹  (SelfStep a b ⟺ SelfStepReduced a b)
    SelfToCopy :      SelfStep a b  ⟹  CopyStep a b
    ClosedToCopy :    ClosedStep a b  ⟹  CopyStep a b
    TransportG :      FreeInPLL a b x  ⟹  FreeInPLL (g a) (g b) (g ∘ x),   g = relB σ³⊥ y
    SelfToClosed :    a, b closed,  SelfStep a b  ⟹  ClosedStep (σ³a) (σ³b)
    SelfTower :       a, b closed,  SelfStep a b,  [a] ⊬ ⊥,  ⊬ b  ⟹
                        ∀ d,  τᵈ faithful on PLL,  FreeInPLL (τᵈ⊥) (τᵈ⊤) (τᵈ ∘ p),
                        [τᵈ⊥, τᵈ⊤] strictly nested at both ends      (τ = rel a b (p ↦ (p ∨ a) ∧ b))

### Necessary conditions

    (Na) NecBox :     [◯a] ⊢ a  ⟹  ¬ CopyStep a b
    (Nb) NecPow :     [a] ⊢ b,  CopyStep a b  ⟹  ∀ n,  [b] ⊬ Tⁿ(a),   Tⁿ(a) = (σⁿ⊥)[⊥ := a]
    (Nc) NecClosed :  [a] ⊢ b,  CopyStep a b  ⟹  ∀ C closed,  ⊬ C  ⟹  [b] ⊬ C[⊥ := a]
         NecCells :   the instances C = ⊥, ◯⊥, ¬◯⊥, ¬¬◯⊥:
                        [b] ⊬ a,   [b] ⊬ ◯a,   [b] ⊬ ◯a ↠ a,   [b] ⊬ (◯a ↠ a) ↠ a

### K1: the gadget criterion (sufficient)

`glue M G`: the worlds of `M` (old) and of `G` (new), every new world above
every old one, `M`'s order, `S` and atoms on the old worlds, `G`'s order and
`S` on the new ones, every atom true at every new world.

    IsGadget G a b :  (∀ M, ∀ x old,  glue M G, x ⊮ a)  ∧  (∀ g, G, g ⊩ a)  ∧
                      (∀ M, ∀ w,  glue M G, w ⊩ b)
    GadgetSelf :      a, b closed,  [a] ⊢ b,  IsGadget G a b  ⟹  SelfStep a b

### K2: bases (`b = ⊤`), and its refinement

    BaseGadget (K2) :  a closed  ⟹  (CopyStep a ⊤  ⟺  ∃ G finite,  IsGadget G a ⊤)

Refinement, stated at Stage 1 from the pen analysis (the brief's K2 asks for ONE
gadget above every world; a world in `S` and a world outside `S` may need
different ones):

    SideIn a :   ∃ finite K, m ∈ S,  K, m ⊮ a,  every strict successor of m forces a
    SideOut a :  ∃ finite K, m,  no world of m's cluster in S,  K, m ⊮ a,
                   every strict successor of m forces a
    TwoSidedSelf :   a closed,  SideIn a,  SideOut a  ⟹  SelfStep a ⊤
    SidesOfNd :      a closed  ⟹  (⊬ (◯a ↠ a) ↠ a ⟹ SideIn a)  ∧  (⊬ ◯a ↠ a ⟹ SideOut a)
    BaseCriterion :  a closed  ⟹  (CopyStep a ⊤ ⟺ SelfStep a ⊤)  ∧
                       (CopyStep a ⊤  ⟺  ⊬ ◯a ↠ a  ∧  ⊬ (◯a ↠ a) ↠ a)

The candidate refuter of K2 as stated:

    aK = t6 ∧ (◯t3 ↠ t3)
    NoGadgetAK :     ∀ G,  ¬ IsGadget G aK ⊤

Base cells: `BaseNo a` (a closed `C` with `⊢ C[⊥ := a]`, `⊬ C`) or `BaseYes a`
(`⊬ ◯a ↠ a` and `⊬ (◯a ↠ a) ↠ a`), for
`a ∈ {◯⊥, ¬◯⊥, t4, t5, t6, σ²⊥, ◯t3, aK}`.

### K3: tops over the base `t3` for the gadget `ext`

    ExtTop b :   ∀ M, ∀ w,  ext M, w ⊩ b
    ExtTops :    b closed  ⟹  (ExtTop b ⟺ [t6] ⊢ b)
    cells:       b₁ = t6 ∧ σ²⊥,  b₂ = t6 ∧ σ t6,  b₃ = t6 ∧ ((◯t3 ↠ t3) ↠ t5):
                   [t3] ⊢ bᵢ,  [bᵢ] ⊢ t6,  [t6] ⊬ bᵢ   (bᵢ fails in some ext K)

### K4: F0 copy against P copy

    CopySelf :   a, b closed,  [a] ⊢ b,  CopyStep a b  ⟹  SelfStep a b
    K4Cell a b C :  [b] ⊬ aTr a C
    cells:       (a, b) ∈ {(t3, ⊤), (t3, t6), (σ²⊥, ⊤)},
                 C ∈ {p ∨ ¬p, ¬¬p → p, (p → q) ∨ (q → p), O1, O2, O3}

### K5: closed generators over `t3`

    K5 :             ClosedStep t3 t6
    NoClosedStepT3 : ∀ b,  ¬ ClosedStep t3 b

Status of every statement at Stage 1: OPEN (statements only, no theorem, no
`sorry`).

## Stage 2: the designed cells (kernel-checked, pins `[propext, Quot.sound]`)

Base table (`b = ⊤`):

| `a` | verdict | object |
|---|---|---|
| `◯⊥` | REFUTED, `C = ¬◯⊥` (`baseNo_e`) | `⊢ ◯◯⊥ ↠ ◯⊥`; `K0` |
| `¬◯⊥` | REFUTED, `C = ¬¬◯⊥` (`baseNo_ne`) | `⊢ (◯¬◯⊥ ↠ ¬◯⊥) ↠ ¬◯⊥`; `KS` |
| `t4` | REFUTED, `C = ¬◯⊥` (`baseNo_t4`) | `⊢ ◯t4 ↠ t4`; `K0` |
| `t5` | passes both cells (`baseYes_t5`) | `Rout`, `Rin` |
| `t6` | REFUTED, `C = ¬◯⊥` (`baseNo_t6`) | `⊢ ◯t6 ↠ t6`; `K0` |
| `σ²⊥` | passes both cells (`baseYes_s2`) | `DOut`, `DIn` |
| `◯t3` | REFUTED, `C = ¬◯⊥` (`baseNo_c1`) | `⊢ ◯◯t3 ↠ ◯t3`; `K0` |
| `aK = t6 ∧ g1` | passes both cells (`baseYes_aK`) | `Rout`, `Pin` |
| `t3` | passes both cells (`baseYes_t3`) | `Rout`, `Pin` |

K3: `[t3] ⊢ bᵢ ⊢ t6` and `[t6] ⊬ bᵢ` for `b₁, b₂, b₃` (`t3_b1` … `nd_t6_b3`), on
`ext Tfork`, `ext Tchain`, `ext KS`.  K4: all 18 cells pass (`k4_…`), on
`ext K` (pairs `(t3, t6)`, `(t3, ⊤)`) and `ext (ext K)` (pair `(σ²⊥, ⊤)`).
K5: the designed generators `p ↦ ◯t3 ∧ t6`, `q ↦ g1 ∧ t6` fail
(`k5_cell`).  Gates watched failing: `gate_base`, `gate_k3`, `gate_k4`.

Status note: `wip/f0Endpoints-STATUS.md`.
-/

set_option autoImplicit false

open PLLFormula

namespace PLLND
namespace F0
namespace Endpoints

open SemUI Sig FreeHAn Base3 FreePLL MovingTop
open Interval (rel FreeInPLL topF)
open PLLND.LaxInfinite (atomFree)

/-! ## The four step notions -/

/-- The A-translation generators `p ↦ (p ∨ a) ∧ b`. -/
def selfGen (a b : PLLFormula) (p : String) : PLLFormula := ((PLLFormula.prop p).or a).and b

/-- **PLL into its own interval `[a, b]`**, by the A-translation. -/
def SelfStep (a b : PLLFormula) : Prop := FreeInPLL a b (selfGen a b)

/-- **The reduced form** (`genIff`): `[b] ⊢ aTr a C ⟹ ⊢ C`. -/
def SelfStepReduced (a b : PLLFormula) : Prop :=
  ∀ C : PLLFormula, Deriv [b] (aTr a C) → Deriv [] C

/-- **PLL into F0's `[a, b]`**, closed generators. -/
def ClosedStep (a b : PLLFormula) : Prop :=
  ∃ x : String → PLLFormula, (∀ p, atomFree (x p) = true) ∧ FreeInPLL a b x

/-- **F0 into its own `[a, b]`**: the closed part. -/
def CopyStep (a b : PLLFormula) : Prop := CopyF0In a b

/-- `Tⁿ(a) = (σⁿ⊥)[⊥ := a]`. -/
def Tpow (a : PLLFormula) (n : Nat) : PLLFormula := subBot a (sigN n .falsePLL)

/-- `¬¬◯⊥` (`⊣⊢ t4`). -/
def nne : PLLFormula := ne.ifThen .falsePLL

/-! ## Cheap implications -/

def SelfIffReduced : Prop :=
  ∀ a b : PLLFormula, Deriv [a] b → (SelfStep a b ↔ SelfStepReduced a b)

def SelfToCopy : Prop := ∀ a b : PLLFormula, SelfStep a b → CopyStep a b

def ClosedToCopy : Prop := ∀ a b : PLLFormula, ClosedStep a b → CopyStep a b

/-- Transport by the readers `g = relB σ³⊥ y`. -/
def TransportG : Prop :=
  ∀ (a b : PLLFormula) (x : String → PLLFormula),
    FreeInPLL a b x → FreeInPLL (gR a) (gR b) (fun p => gR (x p))

def SelfToClosed : Prop :=
  ∀ a b : PLLFormula, atomFree a = true → atomFree b = true →
    SelfStep a b → ClosedStep (sigN 3 a) (sigN 3 b)

/-- `τ = rel a b (p ↦ (p ∨ a) ∧ b)`. -/
def tauS (a b : PLLFormula) : PLLFormula → PLLFormula := rel a b (selfGen a b)

/-- Its iterates. -/
def tauSN (a b : PLLFormula) : Nat → PLLFormula → PLLFormula
  | 0, A => A
  | d + 1, A => tauSN a b d (tauS a b A)

/-- The tower of copies of PLL for `[a, b]` (the form of `PLLSelfTower`). -/
def SelfTowerAt (a b : PLLFormula) : Prop :=
  ∀ d : Nat,
    (∀ A B : PLLFormula, Deriv [A] B ↔ Deriv [tauSN a b d A] (tauSN a b d B)) ∧
    FreeInPLL (tauSN a b d .falsePLL) (tauSN a b d topF) (fun p => tauSN a b d (.prop p)) ∧
    Deriv [tauSN a b d .falsePLL] (tauSN a b (d + 1) .falsePLL) ∧
    ¬ Deriv [tauSN a b (d + 1) .falsePLL] (tauSN a b d .falsePLL) ∧
    Deriv [tauSN a b (d + 1) topF] (tauSN a b d topF) ∧
    ¬ Deriv [tauSN a b d topF] (tauSN a b (d + 1) topF)

def SelfTower : Prop :=
  ∀ a b : PLLFormula, atomFree a = true → atomFree b = true → SelfStep a b →
    ¬ Deriv [a] .falsePLL → ¬ Deriv [] b → SelfTowerAt a b

/-! ## Necessary conditions -/

/-- **(Na)** -/
def NecBox : Prop := ∀ a b : PLLFormula, Deriv [.somehow a] a → ¬ CopyStep a b

/-- **(Nb)** -/
def NecPow : Prop :=
  ∀ a b : PLLFormula, Deriv [a] b → CopyStep a b → ∀ n : Nat, ¬ Deriv [b] (Tpow a n)

/-- **(Nc)** -/
def NecClosed : Prop :=
  ∀ a b : PLLFormula, Deriv [a] b → CopyStep a b →
    ∀ C : PLLFormula, atomFree C = true → ¬ Deriv [] C → ¬ Deriv [b] (subBot a C)

/-- **(Nc), four instances**: `C = ⊥, ◯⊥, ¬◯⊥, ¬¬◯⊥`. -/
def NecCells : Prop :=
  ∀ a b : PLLFormula, Deriv [a] b → CopyStep a b →
    ¬ Deriv [b] a ∧ ¬ Deriv [b] (.somehow a) ∧ ¬ Deriv [b] (subBot a ne) ∧
      ¬ Deriv [b] (subBot a nne)

/-! ## K1: gadgets -/

/-- The order of `glue M G`. -/
def glueLe (M G : SubframeModel) : M.W ⊕ G.W → M.W ⊕ G.W → Prop
  | .inl x, .inl y => M.le x y
  | .inl _, .inr _ => True
  | .inr g, .inr h => G.le g h
  | .inr _, .inl _ => False

theorem glueLe_trans (M G : SubframeModel) {u v w : M.W ⊕ G.W} (h₁ : glueLe M G u v)
    (h₂ : glueLe M G v w) : glueLe M G u w := by
  cases u <;> cases v <;> cases w <;>
    first
    | exact trivial
    | exact M.trans h₁ h₂
    | exact G.trans h₁ h₂
    | exact False.elim h₁
    | exact False.elim h₂

/-- The `S` of `glue M G`. -/
def glueS (M G : SubframeModel) : M.W ⊕ G.W → Prop
  | .inl x => x ∈ M.S
  | .inr g => g ∈ G.S

/-- The valuation of `glue M G`: every atom true on `G`. -/
def glueV (M G : SubframeModel) (p : String) : M.W ⊕ G.W → Prop
  | .inl x => x ∈ M.V p
  | .inr _ => True

theorem glueV_hered (M G : SubframeModel) {p : String} {u v : M.W ⊕ G.W}
    (h : glueLe M G u v) (hu : glueV M G p u) : glueV M G p v := by
  cases u <;> cases v
  · exact M.hered h hu
  · exact trivial
  · exact False.elim h
  · exact trivial

/-- **`M ⊕ G`**: `G` above every world of `M`, every atom true on `G`. -/
def glue (M G : SubframeModel) : SubframeModel where
  W := M.W ⊕ G.W
  le := glueLe M G
  S := {w | glueS M G w}
  V p := {w | glueV M G p w}
  refl w := by
    cases w with
    | inl x => exact M.refl x
    | inr g => exact G.refl g
  trans h₁ h₂ := glueLe_trans M G h₁ h₂
  hered h hu := glueV_hered M G h hu

/-- **A gadget for `(a, b)`**. -/
def IsGadget (G : SubframeModel) (a b : PLLFormula) : Prop :=
  (∀ (M : SubframeModel) (x : M.W), ¬ (glue M G).force (.inl x) a) ∧
  (∀ g : G.W, G.force g a) ∧
  (∀ (M : SubframeModel) (w : (glue M G).W), (glue M G).force w b)

/-- **(K1)** -/
def GadgetSelf : Prop :=
  ∀ (G : SubframeModel) (a b : PLLFormula), atomFree a = true → atomFree b = true →
    Deriv [a] b → IsGadget G a b → SelfStep a b

/-! ## K2: bases -/

/-- **(K2)** as in the brief: one finite gadget above every world. -/
def BaseGadget : Prop :=
  ∀ a : PLLFormula, atomFree a = true →
    (CopyStep a topF ↔
      ∃ G : SubframeModel, Nonempty (SubframeModel.CF.FinDec G) ∧ IsGadget G a topF)

/-- A world in `S` refuting `a` whose strict successors all force `a`. -/
def SideIn (a : PLLFormula) : Prop :=
  ∃ (K : SubframeModel) (_ : SubframeModel.CF.FinDec K) (m : K.W),
    m ∈ K.S ∧ ¬ K.force m a ∧ ∀ w, K.le m w → ¬ K.le w m → K.force w a

/-- A world refuting `a`, no world of its cluster in `S`, whose strict
successors all force `a`. -/
def SideOut (a : PLLFormula) : Prop :=
  ∃ (K : SubframeModel) (_ : SubframeModel.CF.FinDec K) (m : K.W),
    (∀ w, K.le m w → K.le w m → w ∉ K.S) ∧ ¬ K.force m a ∧
      ∀ w, K.le m w → ¬ K.le w m → K.force w a

/-- **(K1′)** the two-sided gadget. -/
def TwoSidedSelf : Prop :=
  ∀ a : PLLFormula, atomFree a = true → SideIn a → SideOut a → SelfStep a topF

/-- The sides from two non-theorems. -/
def SidesOfNd : Prop :=
  ∀ a : PLLFormula, atomFree a = true →
    (¬ Deriv [] (subBot a nne) → SideIn a) ∧ (¬ Deriv [] (subBot a ne) → SideOut a)

/-- **(K2′) The base criterion.** -/
def BaseCriterion : Prop :=
  ∀ a : PLLFormula, atomFree a = true →
    (CopyStep a topF ↔ SelfStep a topF) ∧
    (CopyStep a topF ↔ (¬ Deriv [] (subBot a ne) ∧ ¬ Deriv [] (subBot a nne)))

/-- A refuted base: a closed `C` with `⊢ C[⊥ := a]` and `⊬ C`. -/
def BaseNo (a : PLLFormula) : Prop :=
  ∃ C : PLLFormula, atomFree C = true ∧ Deriv [] (subBot a C) ∧ ¬ Deriv [] C

/-- A base passing the two cells of the criterion. -/
def BaseYes (a : PLLFormula) : Prop :=
  ¬ Deriv [] (subBot a ne) ∧ ¬ Deriv [] (subBot a nne)

/-- `◯t3 ↠ t3 = σ(¬◯⊥) = g1`. -/
def g1 : PLLFormula := (PLLFormula.somehow t3).ifThen t3

/-- The candidate refuter of K2: `aK = t6 ∧ g1`. -/
def aK : PLLFormula := t6.and g1

/-- No gadget for `aK`. -/
def NoGadgetAK : Prop := ∀ G : SubframeModel, ¬ IsGadget G aK topF

/-! ## K3: tops for the gadget `ext` -/

/-- `b` holds at every world of every `ext M`. -/
def ExtTop (b : PLLFormula) : Prop := ∀ (M : SubframeModel) (w : XW M.W), (ext M).force w b

/-- **(K3)** `t6` is the least such `b`. -/
def ExtTops : Prop := ∀ b : PLLFormula, atomFree b = true → (ExtTop b ↔ Deriv [t6] b)

/-- The K3 cells. -/
def b1 : PLLFormula := t6.and (sigN 2 .falsePLL)
def b2 : PLLFormula := t6.and (sig t6)
def b3K : PLLFormula := t6.and (g1.ifThen t5)

/-! ## K4 -/

/-- **(K4)** -/
def CopySelf : Prop :=
  ∀ a b : PLLFormula, atomFree a = true → atomFree b = true → Deriv [a] b →
    CopyStep a b → SelfStep a b

/-- A K4 cell. -/
def K4Cell (a b C : PLLFormula) : Prop := ¬ Deriv [b] (aTr a C)

/-- The K4 formulas over `p = pA`, `q = qA`. -/
def negP : PLLFormula := pA.ifThen .falsePLL
def LEM : PLLFormula := pA.or negP
def DNE : PLLFormula := (negP.ifThen .falsePLL).ifThen pA
def LIN : PLLFormula := (pA.ifThen qA).or (qA.ifThen pA)

/-! ## K5 -/

/-- **(K5)** -/
def K5 : Prop := ClosedStep t3 t6

/-- K5 for every top. -/
def NoClosedStepT3 : Prop := ∀ b : PLLFormula, ¬ ClosedStep t3 b

end Endpoints
end F0
end PLLND

/-! ## Stage 2: the designed cells

Countermodels are `SubCM` tables judged by `SubTab.no` (`decide` in the
kernel); derivations are semantic (`Interval.deriv_of_sem`, finite models).
Every table is designed from the pen analysis (no decider run): `KS` one
`S`-world, `Pin` an `S`-world below a non-`S` top, `Rout = Tfork` a non-`S`
world below an `S`-top and a non-`S` top, `Rin` the same with the root in
`S`, `DOut`, `DIn` the double `ext` of `K0`, `KS`. -/

namespace PLLND
namespace F0
namespace Endpoints

open SemUI Sig FreeHAn Base3 FreePLL MovingTop
open Interval (rel FreeInPLL topF)
open PLLND.LaxInfinite (atomFree)

section Cells

set_option maxRecDepth 100000

/-- One world, in `S`. -/
def KS : SubTab.SubCM := { n := 1, root := 0, le := [[true]], S := [true], val := [[]] }

/-- An `S`-world below a non-`S` top. -/
def Pin : SubTab.SubCM :=
  { n := 2, root := 0, le := [[true, true], [false, true]], S := [true, false], val := [[], []] }

/-- A non-`S` root below an `S`-top and a non-`S` top. -/
def Rout : SubTab.SubCM := Tfork

/-- An `S`-root below an `S`-top and a non-`S` top. -/
def Rin : SubTab.SubCM :=
  { n := 3, root := 0, le := [[true, true, true], [false, true, false], [false, false, true]],
    S := [true, true, false], val := [[], [], []] }

/-- `ext (ext K0)` and `ext (ext KS)` as tables. -/
def DOut : SubTab.SubCM := extT (extT K0 []) []
def DIn : SubTab.SubCM := extT (extT KS []) []

/-- Validity from truth in every finite model. -/
theorem deriv_nil_of_sem {φ : PLLFormula}
    (h : ∀ (M : SubframeModel) [SubframeModel.CF.FinDec M] (v : M.W), M.force v φ) :
    Deriv [] φ :=
  of_top (Interval.deriv_of_sem fun M _ v _ => h M v)

/-! ### The base table -/

theorem nd_ne : ¬ Deriv [] ne := SubTab.no.verdict ne K0

theorem nd_nne : ¬ Deriv [] nne := SubTab.no.verdict nne KS

/-- `⊢ ◯◯A ↠ ◯A`. -/
theorem box_idem (A : PLLFormula) :
    Deriv [] ((PLLFormula.somehow (PLLFormula.somehow A)).ifThen (PLLFormula.somehow A)) :=
  Deriv.impIntro ⟨.laxElim (.iden (.head _)) (.iden (.head _))⟩

/-- `⊢ (◯¬◯⊥ ↠ ¬◯⊥) ↠ ¬◯⊥`, i.e. `⊢ nne[⊥ := ne]`. -/
theorem d_ne_nne : Deriv [] (subBot ne nne) := deriv_nil_of_sem fun M _ _ => by
  intro w _ H u hwu hue
  have hbox : M.force u (PLLFormula.somehow ne) := fun s hus hs => False.elim (hue s hus hs)
  exact H u hwu hbox u (M.refl u) hue

/-- `⊢ ◯t4 ↠ t4`, i.e. `⊢ ne[⊥ := t4]`. -/
theorem d_t4_ne : Deriv [] (subBot t4 ne) := deriv_nil_of_sem fun M _ _ => by
  intro w _ hbox u hwu h3 s hus hs
  rcases h3 with he | hn
  · exact he s hus hs
  · have h4 := hbox s (M.trans hwu hus) hs
    exact h4 s (M.refl s) (Or.inr (SubframeModel.force_mono M ne hus hn)) s (M.refl s) hs

/-- `⊢ ◯t6 ↠ t6`, i.e. `⊢ ne[⊥ := t6]`: `t6` is a fixed point of `◯`. -/
theorem d_t6_ne : Deriv [] (subBot t6 ne) := deriv_nil_of_sem fun M _ _ => by
  intro w _ hbox u hwu h5
  rcases h5 with h3 | h4
  · exact h3
  · refine Or.inl fun s hus hs => ?_
    have h6 := hbox s (M.trans hwu hus) hs
    have h4s := SubframeModel.force_mono M t4 hus h4
    exact h4s s (M.refl s) (h6 s (M.refl s) (Or.inr h4s)) s (M.refl s) hs

/-- **Base `◯⊥` REFUTED** (`C = ¬◯⊥`). -/
theorem baseNo_e : BaseNo e := ⟨ne, rfl, box_idem .falsePLL, nd_ne⟩

/-- **Base `¬◯⊥` REFUTED** (`C = ¬¬◯⊥`). -/
theorem baseNo_ne : BaseNo ne := ⟨nne, rfl, d_ne_nne, nd_nne⟩

/-- **Base `t4` REFUTED** (`C = ¬◯⊥`). -/
theorem baseNo_t4 : BaseNo t4 := ⟨ne, rfl, d_t4_ne, nd_ne⟩

/-- **Base `t6` REFUTED** (`C = ¬◯⊥`). -/
theorem baseNo_t6 : BaseNo t6 := ⟨ne, rfl, d_t6_ne, nd_ne⟩

/-- **Base `◯t3` REFUTED** (`C = ¬◯⊥`). -/
theorem baseNo_c1 : BaseNo (.somehow t3) := ⟨ne, rfl, box_idem t3, nd_ne⟩

/-- **Base `t3` passes** (the known case). -/
theorem baseYes_t3 : BaseYes t3 :=
  ⟨SubTab.no.verdict (subBot t3 ne) Rout, SubTab.no.verdict (subBot t3 nne) Pin⟩

/-- **Base `t5` passes.** -/
theorem baseYes_t5 : BaseYes t5 :=
  ⟨SubTab.no.verdict (subBot t5 ne) Rout, SubTab.no.verdict (subBot t5 nne) Rin⟩

/-- **Base `σ²⊥` passes.** -/
theorem baseYes_s2 : BaseYes (sigN 2 .falsePLL) :=
  ⟨SubTab.no.verdict (subBot (sigN 2 .falsePLL) ne) DOut,
   SubTab.no.verdict (subBot (sigN 2 .falsePLL) nne) DIn⟩

/-- **Base `aK = t6 ∧ g1` passes.** -/
theorem baseYes_aK : BaseYes aK :=
  ⟨SubTab.no.verdict (subBot aK ne) Rout, SubTab.no.verdict (subBot aK nne) Pin⟩

/-- The gate of the base tables, watched failing: none refutes a derivable cell. -/
theorem gate_base : Rout.refutes (subBot t6 ne) = false ∧ Pin.refutes (subBot t4 ne) = false ∧
    Rin.refutes (subBot ne nne) = false ∧ DOut.refutes (subBot e ne) = false := by
  decide +kernel

/-! ### K3: three tops below `t6`, each failing in some `ext K` -/

theorem t3_b1 : Deriv [t3] b1 := Deriv.andIntro t3_t6 (subBot_top t3 (φ := t3) rfl)

theorem t3_b2 : Deriv [t3] b2 := Deriv.andIntro t3_t6 (subBot_top t3 (φ := t6) rfl)

theorem t3_b3 : Deriv [t3] b3K :=
  Deriv.andIntro t3_t6 (Deriv.impIntro (Deriv.orIntro1 (Deriv.iden (.tail _ (.head _)))))

theorem nd_t6_b1 : ¬ Deriv [t6] b1 := fun h =>
  (SubTab.no.verdict (t6.ifThen b1) (extT Tfork [])) (Deriv.impIntro h)

theorem nd_t6_b2 : ¬ Deriv [t6] b2 := fun h =>
  (SubTab.no.verdict (t6.ifThen b2) (extT Tchain [])) (Deriv.impIntro h)

theorem nd_t6_b3 : ¬ Deriv [t6] b3K := fun h =>
  (SubTab.no.verdict (t6.ifThen b3K) (extT KS [])) (Deriv.impIntro h)

/-- The gate of the K3 tables, watched failing: they do not refute `[t3] ⊢ bᵢ`. -/
theorem gate_k3 : (extT Tfork []).refutes (t3.ifThen b1) = false ∧
    (extT Tchain []).refutes (t3.ifThen b2) = false ∧
    (extT KS []).refutes (t3.ifThen b3K) = false := by
  decide +kernel

/-! ### K4: the images of six non-theorems, at three pairs -/

/-- `p` false at the root, true above: refutes `p ∨ ¬p` and `¬¬p → p`. -/
def Klem : SubTab.SubCM :=
  { n := 2, root := 0, le := [[true, true], [false, true]], S := [false, false], val := [[], [a0]] }

/-- Two incomparable tops, `p` at one, `q` at the other: refutes `(p → q) ∨ (q → p)`. -/
def Klin : SubTab.SubCM :=
  { n := 3, root := 0, le := [[true, true, true], [false, true, false], [false, false, true]],
    S := [false, false, false], val := [[], [a0], [a1]] }

theorem k4_of {a b C : PLLFormula} (m : SubTab.SubCM)
    (h : m.refutes (b.ifThen (aTr a C)) = true) : K4Cell a b C :=
  fun hd => SubTab.SubCM.refutes_sound h (Deriv.impIntro hd)

/-- The double `ext` with the atoms true at the tops. -/
def ext2 (K : SubTab.SubCM) : SubTab.SubCM := extT (extT K [a0, a1]) [a0, a1]

theorem k4_t3_t6_lem : K4Cell t3 t6 LEM := k4_of (extT Klem [a0, a1]) (by decide +kernel)
theorem k4_t3_t6_dne : K4Cell t3 t6 DNE := k4_of (extT Klem [a0, a1]) (by decide +kernel)
theorem k4_t3_t6_lin : K4Cell t3 t6 LIN := k4_of (extT Klin [a0, a1]) (by decide +kernel)
theorem k4_t3_t6_O1 : K4Cell t3 t6 O1 := k4_of (extT FreePLL.K1 [a0, a1]) (by decide +kernel)
theorem k4_t3_t6_O2 : K4Cell t3 t6 O2 := k4_of (extT FreePLL.K2 [a0, a1]) (by decide +kernel)
theorem k4_t3_t6_O3 : K4Cell t3 t6 O3 := k4_of (extT FreePLL.K3 [a0, a1]) (by decide +kernel)

theorem k4_t3_top_lem : K4Cell t3 topF LEM := k4_of (extT Klem [a0, a1]) (by decide +kernel)
theorem k4_t3_top_dne : K4Cell t3 topF DNE := k4_of (extT Klem [a0, a1]) (by decide +kernel)
theorem k4_t3_top_lin : K4Cell t3 topF LIN := k4_of (extT Klin [a0, a1]) (by decide +kernel)
theorem k4_t3_top_O1 : K4Cell t3 topF O1 := k4_of (extT FreePLL.K1 [a0, a1]) (by decide +kernel)
theorem k4_t3_top_O2 : K4Cell t3 topF O2 := k4_of (extT FreePLL.K2 [a0, a1]) (by decide +kernel)
theorem k4_t3_top_O3 : K4Cell t3 topF O3 := k4_of (extT FreePLL.K3 [a0, a1]) (by decide +kernel)

theorem k4_s2_top_lem : K4Cell (sigN 2 .falsePLL) topF LEM := k4_of (ext2 Klem) (by decide +kernel)
theorem k4_s2_top_dne : K4Cell (sigN 2 .falsePLL) topF DNE := k4_of (ext2 Klem) (by decide +kernel)
theorem k4_s2_top_lin : K4Cell (sigN 2 .falsePLL) topF LIN := k4_of (ext2 Klin) (by decide +kernel)
theorem k4_s2_top_O1 : K4Cell (sigN 2 .falsePLL) topF O1 := k4_of (ext2 FreePLL.K1) (by decide +kernel)
theorem k4_s2_top_O2 : K4Cell (sigN 2 .falsePLL) topF O2 := k4_of (ext2 FreePLL.K2) (by decide +kernel)
theorem k4_s2_top_O3 : K4Cell (sigN 2 .falsePLL) topF O3 := k4_of (ext2 FreePLL.K3) (by decide +kernel)

/-- The gate of the K4 tables, watched failing: the image of the theorem `p → p`
is not refuted. -/
theorem gate_k4 : (extT Klem [a0, a1]).refutes (t6.ifThen (aTr t3 (pA.ifThen pA))) = false ∧
    (ext2 Klin).refutes (topF.ifThen (aTr (sigN 2 .falsePLL) (pA.ifThen pA))) = false := by
  decide +kernel

/-! ### K5: a designed pair of closed generators in `[t3, t6]` -/

/-- `p ↦ ◯t3 ∧ t6`, `q ↦ g1 ∧ t6` (`g1 = ◯t3 ↠ t3`): the one-generator copy of
`freeIPL1` (`p ↦ ◯t3`) with its relative complement as the second generator. -/
def xK5 (p : String) : PLLFormula :=
  if p = "q" then g1.and t6 else (PLLFormula.somehow t3).and t6

theorem xK5_p : xK5 "p" = (PLLFormula.somehow t3).and t6 := if_neg (by decide)

theorem xK5_q : xK5 "q" = g1.and t6 := if_pos rfl

/-- **The K5 cell**: `[rel ⊤] ⊢ rel ¬(p ∧ q)`, while `[⊤] ⊬ ¬(p ∧ q)`. -/
theorem k5_cell : ¬ FreeInPLL t3 t6 xK5 := fun ⟨_, _, hf⟩ => by
  have h : Deriv [rel t3 t6 xK5 topF] (rel t3 t6 xK5 (FreeIPL.negConj (true, true))) := by
    show Deriv [(t3.ifThen t3).and t6] ((((xK5 "p").and (xK5 "q")).ifThen t3).and t6)
    rw [xK5_p, xK5_q]
    refine Deriv.andIntro (Deriv.impIntro ?_) (Deriv.andElim2 (Deriv.iden (.head _)))
    exact Deriv.impElim (Deriv.andElim1 (Deriv.andElim2 (Deriv.iden (.head _))))
      (Deriv.andElim1 (Deriv.andElim1 (Deriv.iden (.head _))))
  exact FreeIPL.ipc_negConj (true, true) ((hf _ _).mpr h)

end Cells

end Endpoints
end F0
end PLLND

/-! ## Axiom pins: the cells -/

#axioms_within PLLND.F0.Endpoints.nd_ne [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.nd_nne [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.d_ne_nne [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.d_t4_ne [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.d_t6_ne [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.baseNo_e [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.baseNo_ne [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.baseNo_t4 [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.baseNo_t6 [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.baseNo_c1 [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.baseYes_t3 [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.baseYes_t5 [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.baseYes_s2 [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.baseYes_aK [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.gate_base [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.t3_b1 [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.t3_b2 [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.t3_b3 [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.nd_t6_b1 [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.nd_t6_b2 [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.nd_t6_b3 [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.gate_k3 [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.k4_t3_t6_lem [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.k4_t3_t6_dne [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.k4_t3_t6_lin [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.k4_t3_t6_O1 [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.k4_t3_t6_O2 [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.k4_t3_t6_O3 [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.k4_t3_top_lem [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.k4_t3_top_dne [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.k4_t3_top_lin [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.k4_t3_top_O1 [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.k4_t3_top_O2 [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.k4_t3_top_O3 [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.k4_s2_top_lem [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.k4_s2_top_dne [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.k4_s2_top_lin [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.k4_s2_top_O1 [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.k4_s2_top_O2 [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.k4_s2_top_O3 [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.gate_k4 [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.k5_cell [propext, Quot.sound]
