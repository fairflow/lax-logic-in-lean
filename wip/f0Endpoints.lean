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

## Stage 3: proofs (pins `[propext, Quot.sound]`)

**PROVED**: `SelfIffReduced` (`selfIffReduced`), `SelfToCopy`, `ClosedToCopy`,
`TransportG`, `SelfToClosed`, `SelfTower` (`selfTower`); (Na) `necBox`, (Nb)
`necPow`, (Nc) `necClosed`, `necCells`; (K1) `gadgetSelf`; (K1′)
`twoSidedSelf`, `sidesOfNd`; **(K2′) `baseCriterion`**:

    a closed:   CopyStep a ⊤  ⟺  SelfStep a ⊤  ⟺  ⊬ ◯a ↠ a  ∧  ⊬ (◯a ↠ a) ↠ a

(K4 at `b = ⊤`, `copySelf_top`); `noGadgetAK`, hence **K2 as briefed REFUTED**
(`not_baseGadget`); **(K3) `extTops`**; **K5 REFUTED for every top**
(`noClosedStepT3`, `not_k5`).  Validation of K1: the gadget `G2` of `ext` for
`(t3, t6)` (`gadget_t3_t6`, reproving `pllSelf`) and for `t5`
(`selfStep_t5_t56`, a new strictly nested PLL tower in `[t5, t5 ∨ t6]`,
`tower_t5`).

The proof of `baseCriterion` (`ts_realizes`): from countermodels of the two
formulas take a world maximal among the refuters of `a`, in `S` (`SideIn`) and
with no `S` in its cluster (`SideOut`); above every world of a finite `M` that
sees `S` put the strict successors of the first, above every world that sees a
world with no `S` above it the strict successors of the second (`TS`); a
terminal cluster of `M` is bisimilar to the matching side (`isBisimIn`,
`isBisimOut`), so `a` fails exactly on `M`, and the induction of `orig_aTr`
(`realize`) reads `M` off the image.

**Tops over `t3`** (the manager's addition, statements below): `b′ = (◯t3 ↠ t3)
↠ t5` is a top with a faithful copy of PLL (`topT3Alt`, by the realization
`MinR`), incomparable with `t6`; `t6 ∧ b′` is not a top (`meetNotTop`); so the
tops over `t3` are not closed under `∧` (`topsT3NotMeet`) and have no least
element (`noLeastTopT3`).

**The limit of the `t6` tower** (statements below): `τᵈ⊤ ⊣⊢ U_d`,
`τᵈ⊥ ⊣⊢ σᵈ⊥ ∧ U_d` (`towerEnds`); closing (`closing`); the intersection of the
intervals has at most one element and it is a fixed point (`inAllUnique`,
`inAllFixed`); `TauFixedPoint ⟺ ∃ x closed in every interval`
(`fixedIffInAll`).  `⊤`, `t6`, `U₂` are not fixed points (`notFixed_…`).

**OPEN**: `CopySelf` for general `b`; `NoTauFixedPoint` (L4).

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

/-! ## Stage 3: proofs -/

namespace PLLND
namespace F0
namespace Endpoints

open SemUI Sig FreeHAn Base3 FreePLL MovingTop
open Interval (rel FreeInPLL topF)
open PLLND.LaxInfinite (atomFree)
open SubframeModel.CF (FinDec)

/-! ### Cheap implications -/

/-- `relB a (p ↦ p ∨ a) = aTr a`. -/
theorem relB_aTr (a : PLLFormula) :
    ∀ C : PLLFormula, relB a (fun p => (PLLFormula.prop p).or a) C = aTr a C
  | .prop _ => rfl
  | .falsePLL => rfl
  | .and A B => by
      show (relB _ _ A).and (relB _ _ B) = (aTr a A).and (aTr a B)
      rw [relB_aTr a A, relB_aTr a B]
  | .or A B => by
      show (relB _ _ A).or (relB _ _ B) = (aTr a A).or (aTr a B)
      rw [relB_aTr a A, relB_aTr a B]
  | .ifThen A B => by
      show (relB _ _ A).ifThen (relB _ _ B) = (aTr a A).ifThen (aTr a B)
      rw [relB_aTr a A, relB_aTr a B]
  | .somehow A => by
      show (relB _ _ A).somehow = (aTr a A).somehow
      rw [relB_aTr a A]

/-- **PROVED** `[a] ⊢ b ⟹ (SelfStep a b ⟺ SelfStepReduced a b)` (`genIff`). -/
theorem selfIffReduced : SelfIffReduced := by
  intro a b hab
  have h := genIff a b (fun p => (PLLFormula.prop p).or a) hab
    (fun _ => Deriv.orIntro2 (Deriv.iden (.head _)))
  constructor
  · intro hs C hC
    exact h.mp hs C (by rw [relB_aTr]; exact hC)
  · intro hr
    exact h.mpr fun C hC => hr C (by rw [relB_aTr] at hC; exact hC)

/-- Any faithful interval copy of PLL is a faithful copy of F0 on closed formulas. -/
theorem copy_of_free {a b : PLLFormula} {x : String → PLLFormula} (h : FreeInPLL a b x) :
    CopyStep a b := by
  intro A B hA hB
  have h' := h.2.2 A B
  rw [rel_closed_indep a b x (fun _ => a) A hA, rel_closed_indep a b x (fun _ => a) B hB] at h'
  exact h'

/-- **PROVED** -/
theorem selfToCopy : SelfToCopy := fun _ _ h => copy_of_free h

/-- **PROVED** -/
theorem closedToCopy : ClosedToCopy := fun _ _ ⟨_, _, h⟩ => copy_of_free h

/-- The readers commute with the interval translation, syntactically. -/
theorem gR_rel (a b : PLLFormula) (x : String → PLLFormula) :
    ∀ A : PLLFormula, gR (rel a b x A) = rel (gR a) (gR b) (fun p => gR (x p)) A
  | .prop _ => rfl
  | .falsePLL => rfl
  | .and A B => by
      show (gR (rel a b x A)).and (gR (rel a b x B)) = _
      rw [gR_rel a b x A, gR_rel a b x B]; rfl
  | .or A B => by
      show (gR (rel a b x A)).or (gR (rel a b x B)) = _
      rw [gR_rel a b x A, gR_rel a b x B]; rfl
  | .ifThen A B => by
      show ((gR (rel a b x A)).ifThen (gR (rel a b x B))).and (gR b) = _
      rw [gR_rel a b x A, gR_rel a b x B]; rfl
  | .somehow A => by
      show (gR (rel a b x A)).somehow.and (gR b) = _
      rw [gR_rel a b x A]; rfl

/-- **PROVED** transport by the readers. -/
theorem transportG : TransportG := by
  intro a b x ⟨hax, hxb, hf⟩
  refine ⟨fun p => (g_faithful _ _).mp (hax p), fun p => (g_faithful _ _).mp (hxb p),
    fun A B => ?_⟩
  rw [← gR_rel, ← gR_rel]
  exact (hf A B).trans (g_faithful _ _)

theorem gR_closed {a : PLLFormula} (ha : atomFree a = true) : gR a = sigN 3 a := by
  show relB b3 xr a = sigN 3 a
  rw [relB_closed b3 xr a ha, sigN_eq_subBot 3 a]
  rfl

/-- **PROVED** `SelfStep a b ⟹ ClosedStep (σ³a) (σ³b)`. -/
theorem selfToClosed : SelfToClosed := by
  intro a b ha hb h
  have ht := transportG a b (selfGen a b) h
  rw [gR_closed ha, gR_closed hb] at ht
  exact ⟨_, fun _ => g_af _, ht⟩

/-! ### The tower -/

section Tower

variable {a b : PLLFormula}

theorem tauSN_faithful (h : SelfStep a b) : ∀ (d : Nat) (A B : PLLFormula),
    Deriv [A] B ↔ Deriv [tauSN a b d A] (tauSN a b d B)
  | 0, _, _ => Iff.rfl
  | d + 1, A, B => (h.2.2 A B).trans (tauSN_faithful h d (tauS a b A) (tauS a b B))

theorem tauSN_succ' : ∀ (d : Nat) (A : PLLFormula), tauSN a b (d + 1) A = tauS a b (tauSN a b d A)
  | 0, _ => rfl
  | d + 1, A => tauSN_succ' d (tauS a b A)

theorem tauS_interd (h : SelfStep a b) {A B : PLLFormula} (hi : Interd A B) :
    Interd (tauS a b A) (tauS a b B) :=
  ⟨(h.2.2 A B).mp hi.1, (h.2.2 B A).mp hi.2⟩

theorem tauSN_rel (h : SelfStep a b) : ∀ (d : Nat) (A : PLLFormula), Interd (tauSN a b d A)
    (rel (tauSN a b d .falsePLL) (tauSN a b d topF) (fun p => tauSN a b d (.prop p)) A)
  | 0, A => interd_of_sem fun M v => by
      have h0 := rel_iff_relB_gen M .falsePLL topF (fun p => .prop p) (fun p => .prop p)
        (fun _ _ _ => Iff.rfl) A v (fun _ _ h => h)
      rw [relB_id] at h0
      exact h0.symm
  | d + 1, A => by
      have hab : Deriv [a] b := Deriv.cutHead (h.1 "") (h.2.1 "")
      have hfun : (fun p => tauSN a b (d + 1) (.prop p)) = fun p => tauS a b (tauSN a b d (.prop p)) :=
        funext fun p => tauSN_succ' d (.prop p)
      rw [hfun, tauSN_succ' d A, tauSN_succ' d .falsePLL, tauSN_succ' d topF]
      refine (tauS_interd h (tauSN_rel h d A)).trans (interd_of_sem fun M v => ?_)
      exact (Interval.rel_comp M a b (selfGen a b) (tauSN a b d .falsePLL) (tauSN a b d topF)
        (fun p => tauSN a b d (.prop p)) (hab_of hab M) (fun _ _ h => h.2) A v).symm

end Tower

/-- **PROVED** the tower for any `SelfStep` pair. -/
theorem selfTower : SelfTower := by
  intro a b _ _ h ha0 hb0 d
  refine ⟨tauSN_faithful h d, ⟨fun p => (tauSN_faithful h d _ _).mp (bot_le _),
      fun p => (tauSN_faithful h d _ _).mp (le_top _),
      fun A B => (tauSN_faithful h d A B).trans
        (deriv_iff_of_interd (tauSN_rel h d A) (tauSN_rel h d B))⟩,
    (tauSN_faithful h d .falsePLL (tauS a b .falsePLL)).mp (bot_le _),
    fun hd => ha0 ((tauSN_faithful h d (tauS a b .falsePLL) .falsePLL).mpr hd),
    (tauSN_faithful h d (tauS a b topF) topF).mp (le_top _),
    fun hd => hb0 (of_top (Deriv.andElim2 ((tauSN_faithful h d topF (tauS a b topF)).mpr hd)))⟩

/-! ### Necessary conditions -/

/-- **(Na) PROVED** -/
theorem necBox : NecBox := by
  intro a b h hc
  have h1 : Deriv [relC a b (PLLFormula.somehow .falsePLL)] (relC a b .falsePLL) :=
    Deriv.cutHead (Deriv.andElim1 (Deriv.iden (.head _))) h
  exact nd_e_bot ((hc _ _ rfl rfl).mpr h1)

/-- **(Nc) PROVED** -/
theorem necClosed : NecClosed := fun a b hab hc C hC hnd h =>
  hnd ((copyIffTopAvoid a b hab).mp hc C hC h)

/-- **(Nb) PROVED** -/
theorem necPow : NecPow := fun a b hab hc n h =>
  necClosed a b hab hc _ (sigN_vf n rfl) (nd_sigN_bot n) h

theorem nd_e : ¬ Deriv [] e := SubTab.no.verdict e KS

/-- **(Nc), four instances, PROVED** -/
theorem necCells : NecCells := fun a b hab hc =>
  ⟨necClosed a b hab hc .falsePLL rfl nd_bot, necClosed a b hab hc e rfl nd_e,
   necClosed a b hab hc ne rfl nd_ne, necClosed a b hab hc nne rfl nd_nne⟩

/-- A refuted base is refuted under every top above it. -/
theorem not_copy_of_baseNo {a : PLLFormula} (h : BaseNo a) (b : PLLFormula) (hab : Deriv [a] b) :
    ¬ CopyStep a b := fun hc => by
  obtain ⟨C, hC, hd, hnd⟩ := h
  exact necClosed a b hab hc C hC hnd (Deriv.rename (fun _ hx => absurd hx List.not_mem_nil) hd)

/-! ### A bisimulation for closed formulas, and the realization lemma -/

/-- A bisimulation between subframe models (order and `S`; atoms not read). -/
structure IsBisim (N K : SubframeModel) (B : N.W → K.W → Prop) : Prop where
  forth : ∀ {w k w'}, B w k → N.le w w' → ∃ k', K.le k k' ∧ B w' k'
  back : ∀ {w k k'}, B w k → K.le k k' → ∃ w', N.le w w' ∧ B w' k'
  forthS : ∀ {w k w'}, B w k → N.le w w' → w' ∈ N.S → ∃ k', K.le k k' ∧ k' ∈ K.S ∧ B w' k'
  backS : ∀ {w k k'}, B w k → K.le k k' → k' ∈ K.S → ∃ w', N.le w w' ∧ w' ∈ N.S ∧ B w' k'

/-- **Closed formulas are invariant under bisimulation.** -/
theorem bisim_force {N K : SubframeModel} {B : N.W → K.W → Prop} (hB : IsBisim N K B) :
    ∀ φ : PLLFormula, atomFree φ = true → ∀ w k, B w k → (N.force w φ ↔ K.force k φ)
  | .prop _, h, _, _, _ => nomatch h
  | .falsePLL, _, _, _, _ => Iff.rfl
  | .and A C, h, w, k, hb =>
      and_congr (bisim_force hB A (and_split h).1 w k hb) (bisim_force hB C (and_split h).2 w k hb)
  | .or A C, h, w, k, hb =>
      or_congr (bisim_force hB A (or_split h).1 w k hb) (bisim_force hB C (or_split h).2 w k hb)
  | .ifThen A C, h, w, k, hb => by
      have hA := (imp_split h).1
      have hC := (imp_split h).2
      constructor
      · intro hw k' hkk' hk
        obtain ⟨w', hww', hb'⟩ := hB.back hb hkk'
        exact (bisim_force hB C hC w' k' hb').mp (hw w' hww' ((bisim_force hB A hA w' k' hb').mpr hk))
      · intro hk w' hww' hw
        obtain ⟨k', hkk', hb'⟩ := hB.forth hb hww'
        exact (bisim_force hB C hC w' k' hb').mpr (hk k' hkk' ((bisim_force hB A hA w' k' hb').mp hw))
  | .somehow A, h, w, k, hb => by
      constructor
      · intro hw k' hkk' hS
        obtain ⟨w', hww', hS', hb'⟩ := hB.backS hb hkk' hS
        exact (bisim_force hB A h w' k' hb').mp (hw w' hww' hS')
      · intro hk w' hww' hS
        obtain ⟨k', hkk', hS', hb'⟩ := hB.forthS hb hww' hS
        exact (bisim_force hB A h w' k' hb').mpr (hk k' hkk' hS')

/-- **`M` realized in `N` as the refuters of `a`**: `ι` embeds `M`, every world
above the image is in the image or forces `a`, `S` and atoms are kept, and `a`
fails on the image. -/
structure Realizes (N M : SubframeModel) (ι : M.W → N.W) (a : PLLFormula) : Prop where
  le_iff : ∀ x y, N.le (ι x) (ι y) ↔ M.le x y
  up : ∀ x w, N.le (ι x) w → (∃ y, w = ι y) ∨ N.force w a
  S_iff : ∀ x, ι x ∈ N.S ↔ x ∈ M.S
  V_iff : ∀ p x, ι x ∈ N.V p ↔ x ∈ M.V p
  not_a : ∀ x, ¬ N.force (ι x) a

/-- **The realization lemma** (the induction of `orig_aTr`, for any realization):
on the image, `aTr a ψ` holds exactly where `ψ` holds in `M`. -/
theorem realize {N M : SubframeModel} {ι : M.W → N.W} {a : PLLFormula} (hR : Realizes N M ι a) :
    ∀ (ψ : PLLFormula) (x : M.W), N.force (ι x) (aTr a ψ) ↔ M.force x ψ
  | .prop p, x =>
      ⟨fun h => h.elim (hR.V_iff p x).mp fun h' => (hR.not_a x h').elim,
       fun h => Or.inl ((hR.V_iff p x).mpr h)⟩
  | .falsePLL, x => ⟨fun h => (hR.not_a x h).elim, False.elim⟩
  | .and A B, x => and_congr (realize hR A x) (realize hR B x)
  | .or A B, x => or_congr (realize hR A x) (realize hR B x)
  | .ifThen A B, x =>
      ⟨fun h y hxy hA => (realize hR B y).mp
          (h (ι y) ((hR.le_iff x y).mpr hxy) ((realize hR A y).mpr hA)),
       fun h w hw hA => by
        rcases hR.up x w hw with ⟨y, rfl⟩ | haw
        · exact (realize hR B y).mpr (h y ((hR.le_iff x y).mp hw) ((realize hR A y).mp hA))
        · exact Interval.sem_of_deriv (aTr_top a B) N w haw⟩
  | .somehow A, x =>
      ⟨fun h y hxy hS => (realize hR A y).mp
          (h (ι y) ((hR.le_iff x y).mpr hxy) ((hR.S_iff y).mpr hS)),
       fun h w hw hSw => by
        rcases hR.up x w hw with ⟨y, rfl⟩ | haw
        · exact (realize hR A y).mpr (h y ((hR.le_iff x y).mp hw) ((hR.S_iff y).mp hSw))
        · exact Interval.sem_of_deriv (aTr_top a A) N w haw⟩

/-- **Realizations give the reduced step**: if every finite `M` is realized as
the refuters of `a` with `b` at the image of a chosen world, then
`[b] ⊢ aTr a C ⟹ ⊢ C`. -/
theorem reduced_of_realize {a b : PLLFormula}
    (h : ∀ (M : SubframeModel) [FinDec M] (r : M.W),
      ∃ (N : SubframeModel) (ι : M.W → N.W), Realizes N M ι a ∧ N.force (ι r) b) :
    SelfStepReduced a b := by
  intro χ hd
  rcases SubTab.complete χ with ⟨c, hc⟩ | ⟨m, hm⟩
  · exact SubTab.holds_of_check hc
  · exfalso
    have hm0 : m.refutes χ = true := hm
    simp only [SubTab.SubCM.refutes, Bool.and_eq_true, Bool.not_eq_true'] at hm0
    have hr := (SubTab.SubCM.ok_parts hm0.1).1
    obtain ⟨N, ι, hR, hb⟩ := h (m.toModel hm0.1) ⟨m.root, hr⟩
    have hs := Interval.sem_of_deriv hd N (ι ⟨m.root, hr⟩) hb
    have hf := (realize hR χ ⟨m.root, hr⟩).mp hs
    have hbool := (SubTab.SubCM.forceB_iff hm0.1 χ ⟨m.root, hr⟩).mpr hf
    rw [hm0.2] at hbool
    exact Bool.false_ne_true hbool

/-! ### K1: one gadget above every world -/

/-- The new part of `glue M G` is a generated copy of `G`. -/
theorem glue_new_bisim (M G : SubframeModel) :
    IsBisim (glue M G) G (fun w g => w = Sum.inr g) where
  forth {w k w'} hb hle := by
    subst hb
    cases w' with
    | inl _ => exact False.elim hle
    | inr g' => exact ⟨g', hle, rfl⟩
  back {w k k'} hb hle := by
    subst hb
    exact ⟨Sum.inr k', hle, rfl⟩
  forthS {w k w'} hb hle hS := by
    subst hb
    cases w' with
    | inl _ => exact False.elim hle
    | inr g' => exact ⟨g', hle, hS, rfl⟩
  backS {w k k'} hb hle hS := by
    subst hb
    exact ⟨Sum.inr k', hle, hS, rfl⟩

theorem glue_new_force {M G : SubframeModel} {φ : PLLFormula} (hφ : atomFree φ = true) (g : G.W) :
    (glue M G).force (Sum.inr g) φ ↔ G.force g φ :=
  bisim_force (glue_new_bisim M G) φ hφ _ g rfl

/-- **(K1) PROVED** -/
theorem gadgetSelf : GadgetSelf := by
  intro G a b ha _ hab hG
  refine (selfIffReduced a b hab).mpr (reduced_of_realize fun M _ _ =>
    ⟨glue M G, Sum.inl, ?_, hG.2.2 M _⟩)
  exact
    { le_iff := fun _ _ => Iff.rfl
      up := fun _ w _ => by
        cases w with
        | inl y => exact Or.inl ⟨y, rfl⟩
        | inr g => exact Or.inr ((glue_new_force ha g).mpr (hG.2.1 g))
      S_iff := fun _ => Iff.rfl
      V_iff := fun _ _ => Iff.rfl
      not_a := hG.1 M }

/-! ### K5: no closed generators over `t3`, whatever the top -/

theorem rel_sgn_le (b : PLLFormula) (x : String → PLLFormula) (ε : Bool) (q : String) :
    Deriv [rel t3 b x (FreeIPL.sgnP ε (.prop q))] (FreeIPL.sgn ε (x q)) := by
  cases ε
  · exact Deriv.andElim1 (Deriv.iden (.head _))
  · exact Deriv.iden (.head _)

/-- **(K5) REFUTED, for every top**: `noFreeHA2` gives a signed conjunction of
the two generators below `t3`, so the copy sends `¬(p^ε₁ ∧ q^ε₂)` to the top. -/
theorem noClosedStepT3 : NoClosedStepT3 := by
  intro b ⟨x, hx, _, _, hf⟩
  obtain ⟨ε, hd⟩ := FreeIPL.noFreeHA2 (x "p") (x "q") (hx "p") (hx "q")
  have h : Deriv [rel t3 b x topF] (rel t3 b x (FreeIPL.negConj ε)) := by
    show Deriv [(t3.ifThen t3).and b]
      ((((rel t3 b x (FreeIPL.sgnP ε.1 (.prop "p"))).and
        (rel t3 b x (FreeIPL.sgnP ε.2 (.prop "q")))).ifThen t3).and b)
    refine Deriv.andIntro (Deriv.impIntro ?_) (Deriv.andElim2 (Deriv.iden (.head _)))
    have hc : Deriv [(rel t3 b x (FreeIPL.sgnP ε.1 (.prop "p"))).and
        (rel t3 b x (FreeIPL.sgnP ε.2 (.prop "q")))]
        ((FreeIPL.sgn ε.1 (x "p")).and (FreeIPL.sgn ε.2 (x "q"))) :=
      Deriv.andIntro (Deriv.cutHead (Deriv.andElim1 (Deriv.iden (.head _))) (rel_sgn_le b x ε.1 "p"))
        (Deriv.cutHead (Deriv.andElim2 (Deriv.iden (.head _))) (rel_sgn_le b x ε.2 "q"))
    exact Deriv.rename (fun z hz => by rw [List.mem_singleton.mp hz]; exact .head _)
      (Deriv.cutHead hc (ctx_of_imp hd))
  exact FreeIPL.ipc_negConj ε ((hf _ _).mpr h)

/-- **(K5) REFUTED** -/
theorem not_k5 : ¬ K5 := noClosedStepT3 t6

end Endpoints
end F0
end PLLND

namespace PLLND
namespace F0
namespace Endpoints

open SemUI Sig FreeHAn Base3 FreePLL MovingTop
open Interval (rel FreeInPLL topF)
open PLLND.LaxInfinite (atomFree)
open SubframeModel.CF (FinDec)

/-! ### Finite-model search: witnesses from failed forcing -/

theorem exists_of_not_imp {K : SubframeModel} [FinDec K] {r : K.W} {A B : PLLFormula}
    (h : ¬ K.force r (A.ifThen B)) : ∃ y, K.le r y ∧ K.force y A ∧ ¬ K.force y B := by
  rcases Decidable.em (∃ y ∈ FinDec.elems (M := K), K.le r y ∧ K.force y A ∧ ¬ K.force y B)
    with ⟨y, _, hy⟩ | hno
  · exact ⟨y, hy⟩
  · exact absurd (fun y hy hA => Decidable.byContradiction fun hB =>
      hno ⟨y, FinDec.complete y, hy, hA, hB⟩) h

theorem exists_of_not_box {K : SubframeModel} [FinDec K] {r : K.W} {A : PLLFormula}
    (h : ¬ K.force r (.somehow A)) : ∃ u, K.le r u ∧ u ∈ K.S ∧ ¬ K.force u A := by
  rcases Decidable.em (∃ u ∈ FinDec.elems (M := K), K.le r u ∧ u ∈ K.S ∧ ¬ K.force u A)
    with ⟨u, _, hu⟩ | hno
  · exact ⟨u, hu⟩
  · exact absurd (fun u hu hS => Decidable.byContradiction fun hA =>
      hno ⟨u, FinDec.complete u, hu, hS, hA⟩) h

/-- A world above `x` all of whose successors lie below it. -/
theorem exists_terminal (M : SubframeModel) [FinDec M] (x : M.W) :
    ∃ y, M.le x y ∧ ∀ z, M.le y z → M.le z y := by
  obtain ⟨y, hxy, _, hmax⟩ := Interval.exists_max_not M .falsePLL _ x (Nat.le_refl _) id
  exact ⟨y, hxy, fun z hz => (hmax z hz).elim False.elim id⟩

/-! ### K1′: two gadgets, one for worlds in `S`, one for worlds outside -/

section TwoSided

variable (M K₁ K₂ : SubframeModel) (m₁ : K₁.W) (m₂ : K₂.W)

/-- `x` sees a world in `S`. -/
def SeesS (x : M.W) : Prop := ∃ y, M.le x y ∧ y ∈ M.S

/-- `x` sees a world with no world of `S` above it. -/
def SeesE (x : M.W) : Prop := ∃ y, M.le x y ∧ ∀ z, M.le y z → z ∉ M.S

theorem seesS_mono {x y : M.W} (h : M.le x y) (hy : SeesS M y) : SeesS M x :=
  let ⟨z, hz, hS⟩ := hy
  ⟨z, M.trans h hz, hS⟩

theorem seesE_mono {x y : M.W} (h : M.le x y) (hy : SeesE M y) : SeesE M x :=
  let ⟨z, hz, hE⟩ := hy
  ⟨z, M.trans h hz, hE⟩

/-- The order of the two-sided extension: `K₁` strictly above `m₁` is seen from
the worlds of `M` that see `S`, `K₂` strictly above `m₂` from those that see a
world with no `S` above it. -/
def tsLe : M.W ⊕ (K₁.W ⊕ K₂.W) → M.W ⊕ (K₁.W ⊕ K₂.W) → Prop
  | .inl x, .inl y => M.le x y
  | .inl x, .inr (.inl k) => SeesS M x ∧ K₁.le m₁ k ∧ ¬ K₁.le k m₁
  | .inl x, .inr (.inr k) => SeesE M x ∧ K₂.le m₂ k ∧ ¬ K₂.le k m₂
  | .inr (.inl k), .inr (.inl k') => K₁.le k k'
  | .inr (.inr k), .inr (.inr k') => K₂.le k k'
  | .inr (.inl _), .inl _ => False
  | .inr (.inr _), .inl _ => False
  | .inr (.inl _), .inr (.inr _) => False
  | .inr (.inr _), .inr (.inl _) => False

theorem tsLe_trans {u v w : M.W ⊕ (K₁.W ⊕ K₂.W)} (h₁ : tsLe M K₁ K₂ m₁ m₂ u v)
    (h₂ : tsLe M K₁ K₂ m₁ m₂ v w) : tsLe M K₁ K₂ m₁ m₂ u w := by
  rcases u with x | k | k <;> rcases v with y | l | l <;> rcases w with z | j | j <;>
    first
    | exact M.trans h₁ h₂
    | exact K₁.trans h₁ h₂
    | exact K₂.trans h₁ h₂
    | exact ⟨seesS_mono M h₁ h₂.1, h₂.2⟩
    | exact ⟨seesE_mono M h₁ h₂.1, h₂.2⟩
    | exact ⟨h₁.1, K₁.trans h₁.2.1 h₂, fun h => h₁.2.2 (K₁.trans h₂ h)⟩
    | exact ⟨h₁.1, K₂.trans h₁.2.1 h₂, fun h => h₁.2.2 (K₂.trans h₂ h)⟩
    | exact False.elim h₁
    | exact False.elim h₂

def tsS : M.W ⊕ (K₁.W ⊕ K₂.W) → Prop
  | .inl x => x ∈ M.S
  | .inr (.inl k) => k ∈ K₁.S
  | .inr (.inr k) => k ∈ K₂.S

def tsV (p : String) : M.W ⊕ (K₁.W ⊕ K₂.W) → Prop
  | .inl x => x ∈ M.V p
  | .inr _ => True

theorem tsV_hered {p : String} {u v : M.W ⊕ (K₁.W ⊕ K₂.W)} (h : tsLe M K₁ K₂ m₁ m₂ u v)
    (hu : tsV M K₁ K₂ p u) : tsV M K₁ K₂ p v := by
  rcases u with x | k | k <;> rcases v with y | l | l <;>
    first
    | exact M.hered h hu
    | exact trivial
    | exact False.elim h

theorem tsLe_refl : ∀ w : M.W ⊕ (K₁.W ⊕ K₂.W), tsLe M K₁ K₂ m₁ m₂ w w
  | .inl x => M.refl x
  | .inr (.inl k) => K₁.refl k
  | .inr (.inr k) => K₂.refl k

/-- **The two-sided extension of `M`.** -/
def TS : SubframeModel where
  W := M.W ⊕ (K₁.W ⊕ K₂.W)
  le := tsLe M K₁ K₂ m₁ m₂
  S := {w | tsS M K₁ K₂ w}
  V p := {w | tsV M K₁ K₂ p w}
  refl := tsLe_refl M K₁ K₂ m₁ m₂
  trans h₁ h₂ := tsLe_trans M K₁ K₂ m₁ m₂ h₁ h₂
  hered h hu := tsV_hered M K₁ K₂ m₁ m₂ h hu

/-- The copy of `K₁` is generated. -/
def bisimK₁ : (TS M K₁ K₂ m₁ m₂).W → K₁.W → Prop
  | .inr (.inl k), k' => k = k'
  | _, _ => False

/-- The copy of `K₂` is generated. -/
def bisimK₂ : (TS M K₁ K₂ m₁ m₂).W → K₂.W → Prop
  | .inr (.inr k), k' => k = k'
  | _, _ => False

theorem isBisimK₁ : IsBisim (TS M K₁ K₂ m₁ m₂) K₁ (bisimK₁ M K₁ K₂ m₁ m₂) where
  forth {w k w'} hb hle := by
    rcases w with _ | k₀ | _ <;> rcases w' with _ | k' | _ <;>
      first
      | exact False.elim hb
      | exact False.elim hle
      | exact ⟨k', by subst hb; exact hle, rfl⟩
  back {w k k'} hb hle := by
    rcases w with _ | k₀ | _ <;> first | exact False.elim hb | exact ⟨.inr (.inl k'), by subst hb; exact hle, rfl⟩
  forthS {w k w'} hb hle hS := by
    rcases w with _ | k₀ | _ <;> rcases w' with _ | k' | _ <;>
      first
      | exact False.elim hb
      | exact False.elim hle
      | exact ⟨k', by subst hb; exact hle, hS, rfl⟩
  backS {w k k'} hb hle hS := by
    rcases w with _ | k₀ | _ <;>
      first | exact False.elim hb | exact ⟨.inr (.inl k'), by subst hb; exact hle, hS, rfl⟩

theorem isBisimK₂ : IsBisim (TS M K₁ K₂ m₁ m₂) K₂ (bisimK₂ M K₁ K₂ m₁ m₂) where
  forth {w k w'} hb hle := by
    rcases w with _ | _ | k₀ <;> rcases w' with _ | _ | k' <;>
      first
      | exact False.elim hb
      | exact False.elim hle
      | exact ⟨k', by subst hb; exact hle, rfl⟩
  back {w k k'} hb hle := by
    rcases w with _ | _ | k₀ <;> first | exact False.elim hb | exact ⟨.inr (.inr k'), by subst hb; exact hle, rfl⟩
  forthS {w k w'} hb hle hS := by
    rcases w with _ | _ | k₀ <;> rcases w' with _ | _ | k' <;>
      first
      | exact False.elim hb
      | exact False.elim hle
      | exact ⟨k', by subst hb; exact hle, hS, rfl⟩
  backS {w k k'} hb hle hS := by
    rcases w with _ | _ | k₀ <;>
      first | exact False.elim hb | exact ⟨.inr (.inr k'), by subst hb; exact hle, hS, rfl⟩

/-- A terminal cluster seeing `S`, matched with the cluster of `m₁`. -/
def bisimIn (y : M.W) : (TS M K₁ K₂ m₁ m₂).W → K₁.W → Prop
  | .inl q, k => M.le y q ∧ K₁.le m₁ k ∧ K₁.le k m₁
  | .inr (.inl k'), k => k' = k
  | .inr (.inr _), _ => False

/-- A terminal cluster with no `S`, matched with the cluster of `m₂`. -/
def bisimOut (y : M.W) : (TS M K₁ K₂ m₁ m₂).W → K₂.W → Prop
  | .inl q, k => M.le y q ∧ K₂.le m₂ k ∧ K₂.le k m₂
  | .inr (.inr k'), k => k' = k
  | .inr (.inl _), _ => False

variable {M K₁ K₂ m₁ m₂}

theorem isBisimIn [FinDec K₁] (hm₁ : m₁ ∈ K₁.S) {y s : M.W}
    (hterm : ∀ z, M.le y z → M.le z y) (hys : M.le y s) (hs : s ∈ M.S) :
    IsBisim (TS M K₁ K₂ m₁ m₂) K₁ (bisimIn M K₁ K₂ m₁ m₂ y) where
  forth {w k w'} hb hle := by
    rcases w with q | k₀ | k₀
    · rcases w' with q' | k' | k'
      · exact ⟨k, K₁.refl k, M.trans hb.1 hle, hb.2⟩
      · exact ⟨k', K₁.trans hb.2.2 hle.2.1, rfl⟩
      · exfalso
        obtain ⟨z, hqz, hz⟩ := hle.1
        exact hz s (M.trans (hterm z (M.trans hb.1 hqz)) hys) hs
    · rcases w' with q' | k' | k'
      · exact False.elim hle
      · exact ⟨k', by subst hb; exact hle, rfl⟩
      · exact False.elim hle
    · exact False.elim hb
  back {w k k'} hb hle := by
    rcases w with q | k₀ | k₀
    · rcases Decidable.em (K₁.le k' m₁) with hk | hk
      · exact ⟨.inl q, M.refl q, hb.1, K₁.trans hb.2.1 hle, hk⟩
      · exact ⟨.inr (.inl k'),
          ⟨⟨s, M.trans (hterm q hb.1) hys, hs⟩, K₁.trans hb.2.1 hle, hk⟩, rfl⟩
    · exact ⟨.inr (.inl k'), by subst hb; exact hle, rfl⟩
    · exact False.elim hb
  forthS {w k w'} hb hle hS := by
    rcases w with q | k₀ | k₀
    · rcases w' with q' | k' | k'
      · exact ⟨m₁, hb.2.2, hm₁, M.trans hb.1 hle, K₁.refl m₁, K₁.refl m₁⟩
      · exact ⟨k', K₁.trans hb.2.2 hle.2.1, hS, rfl⟩
      · exfalso
        obtain ⟨z, hqz, hz⟩ := hle.1
        exact hz s (M.trans (hterm z (M.trans hb.1 hqz)) hys) hs
    · rcases w' with q' | k' | k'
      · exact False.elim hle
      · exact ⟨k', by subst hb; exact hle, hS, rfl⟩
      · exact False.elim hle
    · exact False.elim hb
  backS {w k k'} hb hle hS := by
    rcases w with q | k₀ | k₀
    · rcases Decidable.em (K₁.le k' m₁) with hk | hk
      · exact ⟨.inl s, M.trans (hterm q hb.1) hys, hs, hys, K₁.trans hb.2.1 hle, hk⟩
      · exact ⟨.inr (.inl k'),
          ⟨⟨s, M.trans (hterm q hb.1) hys, hs⟩, K₁.trans hb.2.1 hle, hk⟩, hS, rfl⟩
    · exact ⟨.inr (.inl k'), by subst hb; exact hle, hS, rfl⟩
    · exact False.elim hb

theorem isBisimOut [FinDec K₂] (hm₂ : ∀ w, K₂.le m₂ w → K₂.le w m₂ → w ∉ K₂.S) {y : M.W}
    (hterm : ∀ z, M.le y z → M.le z y) (hno : ¬ SeesS M y) :
    IsBisim (TS M K₁ K₂ m₁ m₂) K₂ (bisimOut M K₁ K₂ m₁ m₂ y) where
  forth {w k w'} hb hle := by
    rcases w with q | k₀ | k₀
    · rcases w' with q' | k' | k'
      · exact ⟨k, K₂.refl k, M.trans hb.1 hle, hb.2⟩
      · exfalso
        obtain ⟨z, hqz, hz⟩ := hle.1
        exact hno ⟨z, M.trans hb.1 hqz, hz⟩
      · exact ⟨k', K₂.trans hb.2.2 hle.2.1, rfl⟩
    · exact False.elim hb
    · rcases w' with q' | k' | k'
      · exact False.elim hle
      · exact False.elim hle
      · exact ⟨k', by subst hb; exact hle, rfl⟩
  back {w k k'} hb hle := by
    rcases w with q | k₀ | k₀
    · rcases Decidable.em (K₂.le k' m₂) with hk | hk
      · exact ⟨.inl q, M.refl q, hb.1, K₂.trans hb.2.1 hle, hk⟩
      · exact ⟨.inr (.inr k'),
          ⟨⟨y, hterm q hb.1, fun z hyz hz => hno ⟨z, hyz, hz⟩⟩, K₂.trans hb.2.1 hle, hk⟩, rfl⟩
    · exact False.elim hb
    · exact ⟨.inr (.inr k'), by subst hb; exact hle, rfl⟩
  forthS {w k w'} hb hle hS := by
    rcases w with q | k₀ | k₀
    · rcases w' with q' | k' | k'
      · exact False.elim (hno ⟨q', M.trans hb.1 hle, hS⟩)
      · exfalso
        obtain ⟨z, hqz, hz⟩ := hle.1
        exact hno ⟨z, M.trans hb.1 hqz, hz⟩
      · exact ⟨k', K₂.trans hb.2.2 hle.2.1, hS, rfl⟩
    · exact False.elim hb
    · rcases w' with q' | k' | k'
      · exact False.elim hle
      · exact False.elim hle
      · exact ⟨k', by subst hb; exact hle, hS, rfl⟩
  backS {w k k'} hb hle hS := by
    rcases w with q | k₀ | k₀
    · rcases Decidable.em (K₂.le k' m₂) with hk | hk
      · exact False.elim (hm₂ k' (K₂.trans hb.2.1 hle) hk hS)
      · exact ⟨.inr (.inr k'),
          ⟨⟨y, hterm q hb.1, fun z hyz hz => hno ⟨z, hyz, hz⟩⟩, K₂.trans hb.2.1 hle, hk⟩, hS, rfl⟩
    · exact False.elim hb
    · exact ⟨.inr (.inr k'), by subst hb; exact hle, hS, rfl⟩

/-- **The two-sided extension realizes `M` as the refuters of `a`.** -/
theorem ts_realizes [FinDec M] [FinDec K₁] [FinDec K₂] {a : PLLFormula} (ha : atomFree a = true)
    (hm₁S : m₁ ∈ K₁.S) (hm₁a : ¬ K₁.force m₁ a) (hm₁up : ∀ w, K₁.le m₁ w → ¬ K₁.le w m₁ → K₁.force w a)
    (hm₂S : ∀ w, K₂.le m₂ w → K₂.le w m₂ → w ∉ K₂.S) (hm₂a : ¬ K₂.force m₂ a)
    (hm₂up : ∀ w, K₂.le m₂ w → ¬ K₂.le w m₂ → K₂.force w a) :
    Realizes (TS M K₁ K₂ m₁ m₂) M Sum.inl a where
  le_iff _ _ := Iff.rfl
  up x w hw := by
    rcases w with y | k | k
    · exact Or.inl ⟨y, rfl⟩
    · exact Or.inr ((bisim_force (isBisimK₁ M K₁ K₂ m₁ m₂) a ha (Sum.inr (Sum.inl k)) k
        (show bisimK₁ M K₁ K₂ m₁ m₂ (Sum.inr (Sum.inl k)) k from rfl)).mpr
        (hm₁up k hw.2.1 hw.2.2))
    · exact Or.inr ((bisim_force (isBisimK₂ M K₁ K₂ m₁ m₂) a ha (Sum.inr (Sum.inr k)) k
        (show bisimK₂ M K₁ K₂ m₁ m₂ (Sum.inr (Sum.inr k)) k from rfl)).mpr
        (hm₂up k hw.2.1 hw.2.2))
  S_iff _ := Iff.rfl
  V_iff _ _ := Iff.rfl
  not_a x hx := by
    obtain ⟨y, hxy, hterm⟩ := exists_terminal M x
    have hy := SubframeModel.force_mono (TS M K₁ K₂ m₁ m₂) a (u := Sum.inl x) (v := Sum.inl y) hxy hx
    rcases Decidable.em (∃ s ∈ FinDec.elems (M := M), M.le y s ∧ s ∈ M.S) with ⟨s, _, hys, hs⟩ | hno
    · have hb : bisimIn M K₁ K₂ m₁ m₂ y (Sum.inl y) m₁ := ⟨M.refl y, K₁.refl m₁, K₁.refl m₁⟩
      exact hm₁a ((bisim_force (isBisimIn hm₁S hterm hys hs) a ha _ m₁ hb).mp hy)
    · have hno' : ¬ SeesS M y := fun ⟨s, hys, hs⟩ => hno ⟨s, FinDec.complete s, hys, hs⟩
      have hb : bisimOut M K₁ K₂ m₁ m₂ y (Sum.inl y) m₂ := ⟨M.refl y, K₂.refl m₂, K₂.refl m₂⟩
      exact hm₂a ((bisim_force (isBisimOut (m₁ := m₁) hm₂S hterm hno') a ha _ m₂ hb).mp hy)

end TwoSided

/-- **(K1′) PROVED** -/
theorem twoSidedSelf : TwoSidedSelf := by
  intro a ha ⟨K₁, i₁, m₁, hm₁S, hm₁a, hm₁up⟩ ⟨K₂, i₂, m₂, hm₂S, hm₂a, hm₂up⟩
  refine (selfIffReduced a topF (le_top a)).mpr (reduced_of_realize fun M _ r =>
    ⟨TS M K₁ K₂ m₁ m₂, Sum.inl, ?_, Interval.force_topF _ _⟩)
  exact ts_realizes ha hm₁S hm₁a hm₁up hm₂S hm₂a hm₂up

/-- The root of a `SubCM` countermodel refutes the formula in its model. -/
theorem root_refutes {φ : PLLFormula} {m : SubTab.SubCM} (hm : SubTab.no.check φ m = true) :
    ∃ (h : m.okB = true) (hr : m.root < m.n), ¬ (m.toModel h).force ⟨m.root, hr⟩ φ := by
  have hm0 : m.refutes φ = true := hm
  simp only [SubTab.SubCM.refutes, Bool.and_eq_true, Bool.not_eq_true'] at hm0
  have hr := (SubTab.SubCM.ok_parts hm0.1).1
  refine ⟨hm0.1, hr, fun hf => ?_⟩
  have hb := (SubTab.SubCM.forceB_iff hm0.1 φ ⟨m.root, hr⟩).mpr hf
  rw [hm0.2] at hb
  exact Bool.false_ne_true hb

/-- **PROVED** the two sides from the two non-theorems. -/
theorem sidesOfNd : SidesOfNd := by
  intro a _
  constructor
  · intro hnd
    rcases SubTab.complete (subBot a nne) with ⟨c, hc⟩ | ⟨m, hm⟩
    · exact absurd (SubTab.holds_of_check hc) hnd
    · obtain ⟨hok, hr, hroot⟩ := root_refutes hm
      obtain ⟨y, _, hH, hya⟩ := exists_of_not_imp hroot
      obtain ⟨z, hyz, hza, hmax⟩ :=
        Interval.exists_max_not (m.toModel hok) a _ y (Nat.le_refl _) hya
      have hbox : ¬ (m.toModel hok).force z (.somehow a) := fun hb => hza (hH z hyz hb)
      obtain ⟨u, hzu, huS, hua⟩ := exists_of_not_box hbox
      have huz : (m.toModel hok).le u z := (hmax u hzu).resolve_left hua
      refine ⟨m.toModel hok, inferInstance, u, huS, hua, fun w huw hwu => ?_⟩
      rcases hmax w ((m.toModel hok).trans hzu huw) with hw | hw
      · exact hw
      · exact absurd ((m.toModel hok).trans hw hzu) hwu
  · intro hnd
    rcases SubTab.complete (subBot a ne) with ⟨c, hc⟩ | ⟨m, hm⟩
    · exact absurd (SubTab.holds_of_check hc) hnd
    · obtain ⟨hok, hr, hroot⟩ := root_refutes hm
      obtain ⟨y, _, hbox, hya⟩ := exists_of_not_imp hroot
      obtain ⟨z, hyz, hza, hmax⟩ :=
        Interval.exists_max_not (m.toModel hok) a _ y (Nat.le_refl _) hya
      refine ⟨m.toModel hok, inferInstance, z, fun w hzw hwz hwS => ?_, hza, fun w hzw hwz => ?_⟩
      · exact hza (SubframeModel.force_mono (m.toModel hok) a hwz
          (hbox w ((m.toModel hok).trans hyz hzw) hwS))
      · exact (hmax w hzw).resolve_right hwz

/-- **(K2′) The base criterion, PROVED.** -/
theorem baseCriterion : BaseCriterion := by
  intro a ha
  have hab : Deriv [a] topF := le_top a
  have wk : ∀ {X : PLLFormula}, Deriv [] X → Deriv [topF] X :=
    fun h => Deriv.rename (fun _ hx => absurd hx List.not_mem_nil) h
  have h1 : CopyStep a topF → ¬ Deriv [] (subBot a ne) ∧ ¬ Deriv [] (subBot a nne) := fun hc =>
    ⟨fun h => (necCells a topF hab hc).2.2.1 (wk h), fun h => (necCells a topF hab hc).2.2.2 (wk h)⟩
  have h2 : ¬ Deriv [] (subBot a ne) ∧ ¬ Deriv [] (subBot a nne) → SelfStep a topF :=
    fun ⟨n1, n2⟩ => twoSidedSelf a ha ((sidesOfNd a ha).1 n2) ((sidesOfNd a ha).2 n1)
  exact ⟨⟨fun hc => h2 (h1 hc), selfToCopy a topF⟩, ⟨h1, fun hn => selfToCopy a topF (h2 hn)⟩⟩

/-- **(K4) at `b = ⊤`, PROVED.** -/
theorem copySelf_top {a : PLLFormula} (ha : atomFree a = true) (h : CopyStep a topF) :
    SelfStep a topF :=
  ((baseCriterion a ha).1).mp h

/-- **The passing bases give PLL copies.** -/
theorem selfStep_t5 : SelfStep t5 topF :=
  ((baseCriterion t5 rfl).1).mp (((baseCriterion t5 rfl).2).mpr baseYes_t5)

theorem selfStep_s2 : SelfStep (sigN 2 .falsePLL) topF :=
  ((baseCriterion _ rfl).1).mp (((baseCriterion _ rfl).2).mpr baseYes_s2)

theorem selfStep_aK : SelfStep aK topF :=
  ((baseCriterion aK rfl).1).mp (((baseCriterion aK rfl).2).mpr baseYes_aK)

/-! ### K2 as briefed: REFUTED at `aK` -/

/-- One world, in `S` iff `s`. -/
def one (s : Bool) : SubframeModel where
  W := Unit
  le _ _ := True
  S := fun _ => s = true
  V _ := fun _ => False
  refl _ := trivial
  trans _ _ := trivial
  hered _ h := h

/-- **PROVED: no gadget for `aK`.** -/
theorem noGadgetAK : NoGadgetAK := by
  intro G ⟨h1, h2, _⟩
  have hnew : ∀ (s : Bool) (g : G.W), (glue (one s) G).force (Sum.inr g) aK :=
    fun _ g => (glue_new_force rfl g).mpr (h2 g)
  -- at the non-`S` root, from `t4` at the `S`-root
  have hout : (glue (one true) G).force (Sum.inl ()) t4 → False := by
    intro h4
    have he : ∀ g : G.W, G.force g e := fun g => by
      have h4g := SubframeModel.force_mono (glue (one true) G) t4 (u := Sum.inl ())
        (v := Sum.inr g) trivial h4
      have h3g : (glue (one true) G).force (Sum.inr g) t3 :=
        (hnew true g).1 (Sum.inr g) ((glue (one true) G).refl _) (Or.inr h4g)
      exact (glue_new_force rfl g).mp (h4g (Sum.inr g) ((glue (one true) G).refl _) h3g)
    have heo : (glue (one false) G).force (Sum.inl ()) e := by
      intro w _ hS
      cases w with
      | inl _ => exact Bool.noConfusion (hS : false = true)
      | inr g =>
          have heg : (glue (one false) G).force (Sum.inr g) e :=
            (glue_new_force (M := one false) rfl g).mpr (he g)
          exact heg (Sum.inr g) ((glue (one false) G).refl _) hS
    have h3 : (glue (one false) G).force (Sum.inl ()) t3 := Or.inl heo
    exact h1 (one false) () ⟨fun u hu _ => SubframeModel.force_mono _ t3 hu h3,
      fun u hu _ => SubframeModel.force_mono _ t3 hu h3⟩
  -- so `t4` fails at the `S`-root, and then `aK` holds there
  apply h1 (one true) ()
  refine ⟨fun w hw h5 => ?_, fun w hw hc => ?_⟩
  · cases w with
    | inl _ => exact h5.elim id fun h4 => (hout h4).elim
    | inr g => exact (hnew true g).1 (Sum.inr g) ((glue (one true) G).refl _) h5
  · cases w with
    | inl _ => exact hc (Sum.inl ()) trivial rfl
    | inr g => exact (hnew true g).2 (Sum.inr g) ((glue (one true) G).refl _) hc

/-- **K2 as briefed is REFUTED**: `aK` gives a faithful copy of F0 (indeed of
PLL) above it, but no gadget. -/
theorem not_baseGadget : ¬ BaseGadget := fun h => by
  obtain ⟨G, _, hG⟩ := (h aK rfl).mp (((baseCriterion aK rfl).2).mpr baseYes_aK)
  exact noGadgetAK G hG

/-! ### Validation of K1: the gadget of `ext` -/

/-- The two tops of `ext`: `true ∈ S`, `false ∉ S`, incomparable. -/
def G2 : SubframeModel where
  W := Bool
  le x y := x = y
  S := fun x => x = true
  V _ := fun _ => True
  refl _ := rfl
  trans h₁ h₂ := h₁.trans h₂
  hered _ _ := trivial

theorem G2_e_false : G2.force false e := fun w hw hS => by
  have h : false = w := hw
  subst h
  exact Bool.noConfusion (hS : false = true)

theorem G2_not_e_true : ¬ G2.force true e := fun h => h true rfl rfl

theorem G2_t3 : ∀ g : G2.W, G2.force g t3
  | false => Or.inl G2_e_false
  | true => Or.inr fun w hw hw' => by
      have h : true = w := hw
      subst h
      exact G2_not_e_true hw'

theorem glue_G2_t3_new (M : SubframeModel) (g : G2.W) : (glue M G2).force (Sum.inr g) t3 :=
  (glue_new_force (M := M) (G := G2) (φ := t3) rfl g).mpr (G2_t3 g)

theorem glue_G2_not_e (M : SubframeModel) (x : M.W) : ¬ (glue M G2).force (Sum.inl x) e :=
  fun h => h (Sum.inr true) trivial rfl

theorem glue_G2_e_false (M : SubframeModel) :
    (glue M G2).force (Sum.inr (show G2.W from false)) e :=
  (glue_new_force (M := M) (G := G2) (φ := e) rfl false).mpr G2_e_false

theorem glue_G2_not_t3 (M : SubframeModel) (x : M.W) : ¬ (glue M G2).force (Sum.inl x) t3
  | Or.inl h => glue_G2_not_e M x h
  | Or.inr h => h (Sum.inr false) trivial (glue_G2_e_false M)

theorem glue_G2_not_t4 (M : SubframeModel) (x : M.W) : ¬ (glue M G2).force (Sum.inl x) t4 :=
  fun h => G2_not_e_true ((glue_new_force (M := M) (G := G2) (φ := e) rfl true).mp
    (h (Sum.inr true) trivial (glue_G2_t3_new M true)))

theorem glue_G2_t6 (M : SubframeModel) (w : (glue M G2).W) : (glue M G2).force w t6 := by
  intro u hu h5
  rcases w with x | g₀ <;> rcases u with y | g
  · exact h5.elim (fun h => (glue_G2_not_t3 M y h).elim) (fun h => (glue_G2_not_t4 M y h).elim)
  · exact glue_G2_t3_new M g
  · exact False.elim hu
  · exact glue_G2_t3_new M g

/-- **The gadget of `ext` for `(t3, t6)`.** -/
theorem gadget_t3_t6 : IsGadget G2 t3 t6 :=
  ⟨glue_G2_not_t3, G2_t3, glue_G2_t6⟩

/-- **The gadget of `ext` for `(t5, ⊤)` and `(t5, t5 ∨ t6)`.** -/
theorem gadget_t5 (b : PLLFormula) (hb : ∀ M w, (glue M G2).force w b) : IsGadget G2 t5 b :=
  ⟨fun M x h => h.elim (glue_G2_not_t3 M x) (glue_G2_not_t4 M x), fun g => Or.inl (G2_t3 g), hb⟩

/-- **K1 reproves `pllSelf`.** -/
theorem selfStep_t3_t6 : SelfStep t3 t6 := gadgetSelf G2 t3 t6 rfl rfl t3_t6 gadget_t3_t6

/-- **A new interval with a PLL tower**: `[t5, t5 ∨ t6]`. -/
theorem selfStep_t5_t56 : SelfStep t5 (t5.or t6) :=
  gadgetSelf G2 t5 (t5.or t6) rfl rfl (Deriv.orIntro1 (Deriv.iden (.head _)))
    (gadget_t5 _ fun M w => Or.inr (glue_G2_t6 M w))

theorem nd_t5 : ¬ Deriv [] t5 := SubTab.no.verdict t5 Rout

theorem nd_t5_bot : ¬ Deriv [t5] .falsePLL := fun h =>
  nd_t3_bot (Deriv.cutHead (Deriv.orIntro1 (Deriv.iden (.head _))) h)

theorem nd_t56 : ¬ Deriv [] (t5.or t6) := fun h =>
  (disjunction_property h).elim nd_t5 nd_t6

/-- **PROVED: the strictly nested PLL tower in `[t5, t5 ∨ t6]`.** -/
theorem tower_t5 : SelfTowerAt t5 (t5.or t6) :=
  selfTower t5 (t5.or t6) rfl rfl selfStep_t5_t56 nd_t5_bot nd_t56

end Endpoints
end F0
end PLLND

namespace PLLND
namespace F0
namespace Endpoints

open SemUI Sig FreeHAn Base3 FreePLL MovingTop
open Interval (rel FreeInPLL topF)
open PLLND.LaxInfinite (atomFree)
open SubframeModel.CF (FinDec)

/-! ### K3: `t6` is the least top of the gadget `ext`

A finite model of `t6` is bisimilar, for closed formulas, to `ext` of its
`R`-part (the worlds refuting `t3` and forcing `t6`): under `t6` every such
world sees a world forcing `◯⊥` and an `S`-world forcing `¬◯⊥`, which play
`eT` and `nT`. -/

/-- The `R`-part of a model under `t6`. -/
def rPart (N : SubframeModel) : SubframeModel where
  W := {w : N.W // ¬ N.force w t3 ∧ N.force w t6}
  le x y := N.le x.1 y.1
  S := fun x => x.1 ∈ N.S
  V p := fun x => x.1 ∈ N.V p
  refl x := N.refl x.1
  trans h₁ h₂ := N.trans h₁ h₂
  hered h hu := N.hered h hu

/-- The bisimulation: an `R`-world with its copy, `¬◯⊥`-worlds with `nT`,
`◯⊥`-worlds with `eT`. -/
def bisimExt (N : SubframeModel) : N.W → XW (rPart N).W → Prop
  | w, .orig x => w = x.1
  | w, .nT => N.force w ne
  | w, .eT => N.force w e

section ExtBisim

variable {N : SubframeModel} [FinDec N]

omit [FinDec N] in
theorem e_notS {w : N.W} (he : N.force w e) : w ∉ N.S := fun hS => he w (N.refl w) hS

theorem sees_S_ne {w : N.W} (hn : N.force w ne) : ∃ s, N.le w s ∧ s ∈ N.S ∧ N.force s ne := by
  have hne : ¬ N.force w e := fun he => hn w (N.refl w) he
  obtain ⟨s, hws, hsS, _⟩ := exists_of_not_box hne
  exact ⟨s, hws, hsS, SubframeModel.force_mono N ne hws hn⟩

theorem rPart_sees_e (x : (rPart N).W) : ∃ u, N.le x.1 u ∧ N.force u e := by
  have hn : ¬ N.force x.1 ne := fun h => x.2.1 (Or.inr h)
  obtain ⟨u, hu, he, _⟩ := exists_of_not_imp hn
  exact ⟨u, hu, he⟩

theorem rPart_sees_ne (x : (rPart N).W) : ∃ u, N.le x.1 u ∧ N.force u ne := by
  have h4 : ¬ N.force x.1 t4 := fun h => x.2.1 (x.2.2 x.1 (N.refl _) (Or.inr h))
  obtain ⟨u, hu, h3, hne⟩ := exists_of_not_imp h4
  exact ⟨u, hu, h3.resolve_left hne⟩

theorem isBisimExt : IsBisim N (ext (rPart N)) (bisimExt N) where
  forth {w k w'} hb hle := by
    rcases k with x | _ | _
    · have hw : w = x.1 := hb
      subst hw
      rcases Decidable.em (N.force w' t3) with h3 | h3
      · rcases h3 with he | hn
        · exact ⟨XW.eT, trivial, he⟩
        · exact ⟨XW.nT, trivial, hn⟩
      · exact ⟨XW.orig ⟨w', h3, SubframeModel.force_mono N t6 hle x.2.2⟩, hle, rfl⟩
    · exact ⟨XW.nT, trivial, SubframeModel.force_mono N ne hle hb⟩
    · exact ⟨XW.eT, trivial, SubframeModel.force_mono N e hle hb⟩
  back {w k k'} hb hle := by
    rcases k with x | _ | _
    · have hw : w = x.1 := hb
      subst hw
      rcases k' with y | _ | _
      · exact ⟨y.1, hle, rfl⟩
      · obtain ⟨u, hu, hn⟩ := rPart_sees_ne x
        exact ⟨u, hu, hn⟩
      · obtain ⟨u, hu, he⟩ := rPart_sees_e x
        exact ⟨u, hu, he⟩
    · rcases k' with _ | _ | _
      · exact False.elim hle
      · exact ⟨w, N.refl w, hb⟩
      · exact False.elim hle
    · rcases k' with _ | _ | _
      · exact False.elim hle
      · exact False.elim hle
      · exact ⟨w, N.refl w, hb⟩
  forthS {w k w'} hb hle hS := by
    rcases k with x | _ | _
    · have hw : w = x.1 := hb
      subst hw
      rcases Decidable.em (N.force w' t3) with h3 | h3
      · rcases h3 with he | hn
        · exact absurd hS (e_notS he)
        · exact ⟨XW.nT, trivial, trivial, hn⟩
      · exact ⟨XW.orig ⟨w', h3, SubframeModel.force_mono N t6 hle x.2.2⟩, hle, hS, rfl⟩
    · exact ⟨XW.nT, trivial, trivial, SubframeModel.force_mono N ne hle hb⟩
    · exact absurd hS (e_notS (SubframeModel.force_mono N e hle hb))
  backS {w k k'} hb hle hS := by
    rcases k with x | _ | _
    · have hw : w = x.1 := hb
      subst hw
      rcases k' with y | _ | _
      · exact ⟨y.1, hle, hS, rfl⟩
      · obtain ⟨u, hu, hn⟩ := rPart_sees_ne x
        obtain ⟨s, hus, hsS, hsn⟩ := sees_S_ne hn
        exact ⟨s, N.trans hu hus, hsS, hsn⟩
      · exact False.elim hS
    · rcases k' with _ | _ | _
      · exact False.elim hle
      · obtain ⟨s, hws, hsS, hsn⟩ := sees_S_ne hb
        exact ⟨s, hws, hsS, hsn⟩
      · exact False.elim hle
    · rcases k' with _ | _ | _
      · exact False.elim hle
      · exact False.elim hle
      · exact False.elim hS

end ExtBisim

/-- **(K3) PROVED**: `b` holds throughout every `ext M` iff `[t6] ⊢ b`. -/
theorem extTops : ExtTops := by
  intro b hb
  constructor
  · intro hext
    refine Interval.deriv_of_sem fun N _ v hv => ?_
    rcases Decidable.em (N.force v t3) with h3 | h3
    · rcases h3 with he | hn
      · exact (bisim_force isBisimExt b hb v XW.eT he).mpr (hext _ _)
      · exact (bisim_force isBisimExt b hb v XW.nT hn).mpr (hext _ _)
    · exact (bisim_force isBisimExt b hb v (XW.orig ⟨v, h3, hv⟩) rfl).mpr (hext _ _)
  · intro hd M w
    exact Interval.sem_of_deriv hd (ext M) w (t6_ext M w)

/-- The K3 cells as statements about `ext`: none of `b₁, b₂, b₃` is an `ext`-top. -/
theorem not_extTop_b1 : ¬ ExtTop b1 := fun h => nd_t6_b1 ((extTops b1 rfl).mp h)
theorem not_extTop_b2 : ¬ ExtTop b2 := fun h => nd_t6_b2 ((extTops b2 rfl).mp h)
theorem not_extTop_b3 : ¬ ExtTop b3K := fun h => nd_t6_b3 ((extTops b3K rfl).mp h)

end Endpoints
end F0
end PLLND

/-! ## Addition (the manager, 2026-11-01): tops over `t3` beyond `ext`

Statements committed with their cells, before any proof:

    b′ = (◯t3 ↠ t3) ↠ t5 = g1 ↠ t5
    (T1)  TopT3Alt :      SelfStep t3 b′  ∧  [t6] ⊬ b′  ∧  [b′] ⊬ t6
    (T2)  MeetNotTop :    ¬ CopyStep t3 (t6 ∧ b′)
          TopsT3NotMeet : ∃ b b′,  CopyStep t3 b  ∧  CopyStep t3 b′  ∧  ¬ CopyStep t3 (b ∧ b′)
          NoLeastTopT3 :  ¬ ∃ b₀,  [t3] ⊢ b₀  ∧  CopyStep t3 b₀  ∧
                            ∀ b,  [t3] ⊢ b  ⟹  CopyStep t3 b  ⟹  [b₀] ⊢ b

Pen: the realization of `M` that attaches the non-`S` top above every world and
the `S`-top only above the worlds seeing a world with no `S` above it (`MinR`)
makes the old worlds exactly the refuters of `t3` and forces `b′` on them;
under `t6 ∧ b′` no `R`-world in `S` is terminal, so `σ(¬¬◯⊥) = g1 ↠ t3` follows. -/

namespace PLLND
namespace F0
namespace Endpoints

open SemUI Sig FreeHAn Base3 FreePLL MovingTop
open Interval (rel FreeInPLL topF)
open PLLND.LaxInfinite (atomFree)

/-- `b′ = g1 ↠ t5`. -/
def bP : PLLFormula := g1.ifThen t5

/-- **(T1)** -/
def TopT3Alt : Prop := SelfStep t3 bP ∧ ¬ Deriv [t6] bP ∧ ¬ Deriv [bP] t6

/-- **(T2)** -/
def MeetNotTop : Prop := ¬ CopyStep t3 (t6.and bP)

def TopsT3NotMeet : Prop :=
  ∃ b b' : PLLFormula, CopyStep t3 b ∧ CopyStep t3 b' ∧ ¬ CopyStep t3 (b.and b')

def NoLeastTopT3 : Prop :=
  ¬ ∃ b₀ : PLLFormula, Deriv [t3] b₀ ∧ CopyStep t3 b₀ ∧
    ∀ b : PLLFormula, Deriv [t3] b → CopyStep t3 b → Deriv [b₀] b

/-! ### The cells -/

theorem t3_bP : Deriv [t3] bP :=
  Deriv.impIntro (Deriv.orIntro1 (Deriv.iden (.tail _ (.head _))))

/-- `[b′] ⊬ t6`: an `S`-world below a non-`S` top forces `t4`, so `t5`, so `b′`,
and refutes `t3`, so `t6`. -/
theorem nd_bP_t6 : ¬ Deriv [bP] t6 := fun h =>
  (SubTab.no.verdict (bP.ifThen t6) Pin) (Deriv.impIntro h)

/-- `[t6] ⊬ b′` (`ext KS`). -/
theorem nd_t6_bP : ¬ Deriv [t6] bP := fun h =>
  (SubTab.no.verdict (t6.ifThen bP) (extT KS [])) (Deriv.impIntro h)

/-- **The T2 cell**: `[t6 ∧ b′] ⊢ σ(¬¬◯⊥) = g1 ↠ t3`, while `⊬ ¬¬◯⊥`. -/
theorem meet_sig_nne : Deriv [t6.and bP] (subBot t3 nne) :=
  Deriv.impIntro (Deriv.impElim (Deriv.andElim1 (Deriv.iden (.tail _ (.head _))))
    (Deriv.impElim (Deriv.andElim2 (Deriv.iden (.tail _ (.head _)))) (Deriv.iden (.head _))))

/-- **(T2) PROVED** -/
theorem meetNotTop : MeetNotTop := fun hc =>
  nd_nne ((copyIffTopAvoid t3 _ (Deriv.andIntro t3_t6 t3_bP)).mp hc nne rfl meet_sig_nne)

/-- The gate of the T tables, watched failing: they do not refute `[t3] ⊢ b′`. -/
theorem gate_T : Pin.refutes (t3.ifThen bP) = false ∧ (extT KS []).refutes (t3.ifThen bP) = false := by
  decide +kernel

end Endpoints
end F0
end PLLND

namespace PLLND
namespace F0
namespace Endpoints

open SemUI Sig FreeHAn Base3 FreePLL MovingTop
open Interval (rel FreeInPLL topF)
open PLLND.LaxInfinite (atomFree)
open SubframeModel.CF (FinDec)

/-! ### (T1): the realization `MinR`

Two new worlds: `false` (outside `S`) above every world, `true` (in `S`) above
the worlds that see a world with no `S` above it. -/

section MinR

variable (M : SubframeModel)

def minLe : M.W ⊕ Bool → M.W ⊕ Bool → Prop
  | .inl x, .inl y => M.le x y
  | .inl _, .inr false => True
  | .inl x, .inr true => SeesE M x
  | .inr b, .inr b' => b = b'
  | .inr _, .inl _ => False

theorem minLe_trans : ∀ {u v w : M.W ⊕ Bool}, minLe M u v → minLe M v w → minLe M u w
  | .inl _, .inl _, .inl _, h₁, h₂ => M.trans h₁ h₂
  | .inl _, .inl _, .inr false, _, _ => trivial
  | .inl _, .inl _, .inr true, h₁, h₂ => seesE_mono M h₁ h₂
  | .inl _, .inr b, .inr b', h₁, h₂ => by
      have e' : b = b' := h₂
      subst e'
      exact h₁
  | .inr _, .inr _, .inr _, h₁, h₂ => Eq.trans h₁ h₂
  | .inl _, .inr _, .inl _, _, h₂ => False.elim h₂
  | .inr _, .inl _, _, h₁, _ => False.elim h₁
  | .inr _, .inr _, .inl _, _, h₂ => False.elim h₂

theorem minLe_refl : ∀ w : M.W ⊕ Bool, minLe M w w
  | .inl x => M.refl x
  | .inr _ => rfl

def minS : M.W ⊕ Bool → Prop
  | .inl x => x ∈ M.S
  | .inr b => b = true

def minV (p : String) : M.W ⊕ Bool → Prop
  | .inl x => x ∈ M.V p
  | .inr _ => True

theorem minV_hered {p : String} : ∀ {u v : M.W ⊕ Bool}, minLe M u v → minV M p u → minV M p v
  | .inl _, .inl _, h, hu => M.hered h hu
  | .inl _, .inr _, _, _ => trivial
  | .inr _, .inr _, _, _ => trivial
  | .inr _, .inl _, h, _ => False.elim h

/-- **The realization `MinR M`.** -/
def MinR : SubframeModel where
  W := M.W ⊕ Bool
  le := minLe M
  S := fun w => minS M w
  V p := fun w => minV M p w
  refl := minLe_refl M
  trans h₁ h₂ := minLe_trans M h₁ h₂
  hered h hu := minV_hered M h hu

theorem minR_e_false : (MinR M).force (Sum.inr false) e := fun w hw hS => by
  rcases w with _ | b
  · exact False.elim hw
  · have e' : false = b := hw
    subst e'
    exact Bool.noConfusion (hS : false = true)

theorem minR_not_e_true : ¬ (MinR M).force (Sum.inr true) e := fun h =>
  h (Sum.inr true) (rfl : true = true) (rfl : true = true)

theorem minR_t3_new : ∀ b : Bool, (MinR M).force (Sum.inr b) t3
  | false => Or.inl (minR_e_false M)
  | true => Or.inr fun w hw he => by
      rcases w with _ | b
      · exact False.elim hw
      · have e' : true = b := hw
        subst e'
        exact minR_not_e_true M he

theorem minR_not_t3 [FinDec M] (x : M.W) : ¬ (MinR M).force (Sum.inl x) t3
  | Or.inl he => by
      obtain ⟨y, hxy, hterm⟩ := exists_terminal M x
      rcases Decidable.em (∃ s ∈ FinDec.elems (M := M), M.le y s ∧ s ∈ M.S)
        with ⟨s, _, hys, hs⟩ | hno
      · exact he (Sum.inl s) (M.trans hxy hys) hs
      · exact he (Sum.inr true)
          ⟨y, hxy, fun z hyz hz => hno ⟨z, FinDec.complete z, hyz, hz⟩⟩ (rfl : true = true)
  | Or.inr hn => hn (Sum.inr false) trivial (minR_e_false M)

theorem minR_realizes [FinDec M] : Realizes (MinR M) M Sum.inl t3 where
  le_iff _ _ := Iff.rfl
  up _ w _ := by
    rcases w with y | b
    · exact Or.inl ⟨y, rfl⟩
    · exact Or.inr (minR_t3_new M b)
  S_iff _ := Iff.rfl
  V_iff _ _ := Iff.rfl
  not_a := minR_not_t3 M

/-- **`b′` holds on the old worlds of `MinR M`.** -/
theorem minR_bP [FinDec M] (x : M.W) : (MinR M).force (Sum.inl x) bP := by
  intro w _ hg
  rcases w with y | b
  · refine Or.inr fun u hu h3 => ?_
    rcases u with z | b
    · exact absurd h3 (minR_not_t3 M z)
    · cases b with
      | false => exact minR_e_false M
      | true =>
          exfalso
          obtain ⟨z, hyz, hz⟩ := (hu : SeesE M y)
          have hc : (MinR M).force (Sum.inl z) (PLLFormula.somehow t3) := fun w hw hS => by
            rcases w with z' | b'
            · exact absurd (hS : z' ∈ M.S) (hz z' hw)
            · exact minR_t3_new M b'
          exact minR_not_t3 M z (hg (Sum.inl z) hyz hc)
  · exact Or.inl (minR_t3_new M b)

end MinR

/-- **PROVED**: PLL embeds in `[t3, b′]` by the A-translation. -/
theorem selfStep_t3_bP : SelfStep t3 bP :=
  (selfIffReduced t3 bP t3_bP).mpr (reduced_of_realize fun M _ r =>
    ⟨MinR M, Sum.inl, minR_realizes M, minR_bP M r⟩)

/-- **(T1) PROVED** -/
theorem topT3Alt : TopT3Alt := ⟨selfStep_t3_bP, nd_t6_bP, nd_bP_t6⟩

/-- **PROVED**: the tops over `t3` are not closed under `∧`. -/
theorem topsT3NotMeet : TopsT3NotMeet :=
  ⟨t6, bP, copyT3T6, selfToCopy _ _ selfStep_t3_bP, meetNotTop⟩

/-- **PROVED**: there is no least top over `t3`. -/
theorem noLeastTopT3 : NoLeastTopT3 := by
  rintro ⟨b₀, hb₀, hc₀, hleast⟩
  have h6 := hleast t6 t3_t6 copyT3T6
  have hP := hleast bP t3_bP (selfToCopy _ _ selfStep_t3_bP)
  have hta := (copyIffTopAvoid t3 b₀ hb₀).mp hc₀
  exact meetNotTop ((copyIffTopAvoid t3 _ (Deriv.andIntro t3_t6 t3_bP)).mpr fun C hC h =>
    hta C hC (Deriv.cutHead (Deriv.andIntro h6 hP) h))

end Endpoints
end F0
end PLLND

/-! ## Addition (Matthew via the manager, 2026-11-01): the limit of the `t6` tower

Statements committed with their cells, before any proof.  `τ = relC t3 t6`,
`τᵈ = tauN t3 t6 d`, `U_d = ⊤ ∧ t6 ∧ σt6 ∧ ⋯ ∧ σ^{d-1} t6`.

    (L1) TowerEnds :     τᵈ⊤ ⊣⊢ U_d   and   τᵈ⊥ ⊣⊢ σᵈ⊥ ∧ U_d
    (L2) Closing :       y, z closed,  (∀ d, [y] ⊢ τᵈ⊤),  (∀ d, [τᵈ⊥] ⊢ z)  ⟹  [y] ⊢ z
         InAll x :       ∀ d,  [τᵈ⊥] ⊢ x ⊢ τᵈ⊤
         InAllUnique :   x, x′ closed,  InAll x,  InAll x′  ⟹  x ⊣⊢ x′
         InAllFixed :    x closed,  InAll x  ⟹  τx ⊣⊢ x
    (L3) FixedIffInAll : TauFixedPoint  ⟺  ∃ x closed, InAll x
    (L4) NoTauFixedPoint :  ¬ TauFixedPoint          (the conjecture; OPEN)
         cells:          x ∈ {⊤, t6, U₂}:  [x] ⊬ τx -/

namespace PLLND
namespace F0
namespace Endpoints

open SemUI Sig FreeHAn Base3 FreePLL MovingTop
open Interval (rel FreeInPLL topF)
open PLLND.LaxInfinite (atomFree)

/-- `U_d = ⊤ ∧ t6 ∧ σt6 ∧ ⋯ ∧ σ^{d-1} t6`. -/
def Ud : Nat → PLLFormula
  | 0 => topF
  | d + 1 => (Ud d).and (sigN d t6)

/-- **(L1)** -/
def TowerEnds : Prop :=
  ∀ d : Nat, Interd (tauN t3 t6 d topF) (Ud d) ∧
    Interd (tauN t3 t6 d .falsePLL) ((sigN d .falsePLL).and (Ud d))

/-- **(L2)** -/
def Closing : Prop :=
  ∀ y z : PLLFormula, atomFree y = true → atomFree z = true →
    (∀ d, Deriv [y] (tauN t3 t6 d topF)) → (∀ d, Deriv [tauN t3 t6 d .falsePLL] z) → Deriv [y] z

/-- `x` lies in every interval of the tower. -/
def InAll (x : PLLFormula) : Prop :=
  ∀ d : Nat, Deriv [tauN t3 t6 d .falsePLL] x ∧ Deriv [x] (tauN t3 t6 d topF)

def InAllUnique : Prop :=
  ∀ x x' : PLLFormula, atomFree x = true → atomFree x' = true → InAll x → InAll x' → Interd x x'

def InAllFixed : Prop :=
  ∀ x : PLLFormula, atomFree x = true → InAll x → Interd (relC t3 t6 x) x

/-- **(L3)** -/
def FixedIffInAll : Prop := TauFixedPoint ↔ ∃ x : PLLFormula, atomFree x = true ∧ InAll x

/-- **(L4)**, the conjecture (OPEN). -/
def NoTauFixedPoint : Prop := ¬ TauFixedPoint

/-! ### The L4 cells: three named candidates are not fixed points -/

section LCells

set_option maxRecDepth 100000

theorem notFixed_top : ¬ Deriv [topF] (relC t3 t6 topF) := fun h =>
  (SubTab.no.verdict (topF.ifThen (relC t3 t6 topF)) Tchain) (Deriv.impIntro h)

theorem notFixed_t6 : ¬ Deriv [t6] (relC t3 t6 t6) := fun h =>
  (SubTab.no.verdict (t6.ifThen (relC t3 t6 t6)) (extT Tchain [])) (Deriv.impIntro h)

theorem notFixed_U2 : ¬ Deriv [Ud 2] (relC t3 t6 (Ud 2)) := fun h =>
  (SubTab.no.verdict ((Ud 2).ifThen (relC t3 t6 (Ud 2))) (extT (extT Tchain []) []))
    (Deriv.impIntro h)

/-- The gate of the L4 tables, watched failing: they do not refute the derivable
`[τx] ⊢ x`. -/
theorem gate_L : Tchain.refutes ((relC t3 t6 topF).ifThen topF) = false ∧
    (extT Tchain []).refutes ((relC t3 t6 t6).ifThen t6) = false ∧
    (extT (extT Tchain []) []).refutes ((relC t3 t6 (Ud 2)).ifThen (Ud 2)) = false := by
  decide +kernel

end LCells

end Endpoints
end F0
end PLLND

namespace PLLND
namespace F0
namespace Endpoints

open SemUI Sig FreeHAn Base3 FreePLL MovingTop
open Interval (rel FreeInPLL topF)
open PLLND.LaxInfinite (atomFree)

/-! ### L1–L3: the ends of the tower and its intersection -/

theorem Ud_af : ∀ d : Nat, atomFree (Ud d) = true
  | 0 => rfl
  | d + 1 => by
      show (atomFree (Ud d) && atomFree (sigN d t6)) = true
      rw [Ud_af d, sigN_vf d (φ := t6) rfl]
      rfl

theorem force_Ud (M : SubframeModel) (w : M.W) :
    ∀ d : Nat, M.force w (Ud d) ↔ ∀ k, k < d → M.force w (sigN k t6)
  | 0 => ⟨fun _ k hk => absurd hk (Nat.not_lt_zero k), fun _ _ _ h => h⟩
  | d + 1 => by
      show (M.force w (Ud d) ∧ M.force w (sigN d t6)) ↔ _
      rw [force_Ud M w d]
      constructor
      · rintro ⟨h, hd⟩ k hk
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk' | hk'
        · exact h k hk'
        · rw [hk']
          exact hd
      · intro h
        exact ⟨fun k hk => h k (Nat.lt_succ_of_lt hk), h d (Nat.lt_succ_self d)⟩

theorem force_sig_top (M : SubframeModel) (w : M.W) : M.force w (sig topF) := fun _ _ h => h

theorem force_sig_Ud (M : SubframeModel) (w : M.W) : ∀ d : Nat,
    M.force w (sig (Ud d)) ↔ (M.force w (sig topF) ∧ ∀ k, k < d → M.force w (sigN (k + 1) t6))
  | 0 => ⟨fun h => ⟨h, fun k hk => absurd hk (Nat.not_lt_zero k)⟩, fun h => h.1⟩
  | d + 1 => by
      show (M.force w (sig (Ud d)) ∧ M.force w (sig (sigN d t6))) ↔ _
      rw [force_sig_Ud M w d, ← InsideOut.sigN_succ]
      constructor
      · rintro ⟨⟨h0, h⟩, hd⟩
        refine ⟨h0, fun k hk => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk' | hk'
        · exact h k hk'
        · rw [hk']
          exact hd
      · rintro ⟨h0, h⟩
        exact ⟨⟨h0, fun k hk => h k (Nat.lt_succ_of_lt hk)⟩, h d (Nat.lt_succ_self d)⟩

/-- `σ U_d ∧ t6 ⊣⊢ U_{d+1}`. -/
theorem sig_Ud (d : Nat) : Interd ((sig (Ud d)).and t6) (Ud (d + 1)) := interd_of_sem fun M v => by
  show (M.force v (sig (Ud d)) ∧ M.force v t6) ↔ M.force v (Ud (d + 1))
  rw [force_sig_Ud M v d, force_Ud M v (d + 1)]
  constructor
  · rintro ⟨⟨_, h⟩, h6⟩ k hk
    cases k with
    | zero => exact h6
    | succ k => exact h k (Nat.lt_of_succ_lt_succ hk)
  · intro h
    exact ⟨⟨force_sig_top M v, fun k hk => h (k + 1) (Nat.succ_lt_succ hk)⟩, h 0 (Nat.succ_pos d)⟩

/-- **`τᵈ A ⊣⊢ σᵈ A ∧ U_d`** for closed `A`. -/
theorem tauN_closed : ∀ (d : Nat) (A : PLLFormula), atomFree A = true →
    Interd (tauN t3 t6 d A) ((sigN d A).and (Ud d))
  | 0, A, _ => interd_and_top A
  | d + 1, A, hA => by
      rw [tauN_succ' t3 t6 d A]
      have hX := tauN_af (a := t3) (b := t6) rfl rfl d A hA
      have hY : atomFree ((sigN d A).and (Ud d)) = true := by
        show (atomFree (sigN d A) && atomFree (Ud d)) = true
        rw [sigN_vf d hA, Ud_af d]
        rfl
      have ih := tauN_closed d A hA
      have h1 := relC_interd t3_t6 hX
      have h2 : Interd (sig (tauN t3 t6 d A)) (sig ((sigN d A).and (Ud d))) :=
        ⟨sig_mono hX hY ih.1, sig_mono hY hX ih.2⟩
      refine h1.trans (interd_of_sem fun M v => ?_)
      have e2 := sem_of_interd h2 M v
      have e3 := sem_of_interd (sig_Ud d) M v
      rw [InsideOut.sigN_succ]
      show (M.force v (sig (tauN t3 t6 d A)) ∧ M.force v t6) ↔
        (M.force v (sig (sigN d A)) ∧ M.force v (Ud (d + 1)))
      rw [e2, ← e3]
      show ((M.force v (sig (sigN d A)) ∧ M.force v (sig (Ud d))) ∧ M.force v t6) ↔
        (M.force v (sig (sigN d A)) ∧ (M.force v (sig (Ud d)) ∧ M.force v t6))
      exact and_assoc

theorem force_sigN_top (M : SubframeModel) (v : M.W) (d : Nat) : M.force v (sigN d topF) := by
  show M.force v (sigN d (PLLFormula.ifThen .falsePLL .falsePLL))
  rw [sigN_imp]
  exact fun _ _ h => h

/-- **(L1) PROVED** -/
theorem towerEnds : TowerEnds := fun d =>
  ⟨(tauN_closed d topF rfl).trans (interd_of_sem fun M v =>
      ⟨fun h => h.2, fun h => ⟨force_sigN_top M v d, h⟩⟩),
   tauN_closed d .falsePLL rfl⟩

/-- **(L2) PROVED**: in a finite model `σᴺ⊥` eventually holds everywhere
(`cm_eventually`), and there the ends `σᴺ⊥ ∧ U_N` and `U_N` agree. -/
theorem closing : Closing := by
  intro y z _ _ hy hz
  rcases SubTab.complete (y.ifThen z) with ⟨c, hc⟩ | ⟨m, hm⟩
  · exact ctx_of_imp (SubTab.holds_of_check hc)
  · obtain ⟨N, hN⟩ := InsideOut.cm_eventually (x := y.ifThen z) (m := m) hm
    exfalso
    apply hN N (Nat.le_refl N)
    have hU : Deriv [y] (Ud N) := Deriv.cutHead (hy N) (towerEnds N).1.1
    have hb : Deriv [(sigN N .falsePLL).and (Ud N)] z := Deriv.cutHead (towerEnds N).2.2 (hz N)
    exact Deriv.impIntro (Deriv.cutHead
      (Deriv.andIntro (Deriv.iden (.tail _ (.head _))) (Deriv.cutHead (Deriv.iden (.head _)) hU)) hb)

/-- **PROVED**: the intersection of the intervals has at most one element. -/
theorem inAllUnique : InAllUnique := fun x x' hx hx' h h' =>
  ⟨closing x x' hx hx' (fun d => (h d).2) (fun d => (h' d).1),
   closing x' x hx' hx (fun d => (h' d).2) (fun d => (h d).1)⟩

theorem inAll_tau {x : PLLFormula} (hx : atomFree x = true) (h : InAll x) :
    InAll (relC t3 t6 x) := by
  intro d
  cases d with
  | zero => exact ⟨bot_le _, le_top _⟩
  | succ d =>
      rw [tauN_succ' t3 t6 d .falsePLL, tauN_succ' t3 t6 d topF]
      exact ⟨relC_mono t3_t6 (tauN_af rfl rfl d _ rfl) hx (h d).1,
        relC_mono t3_t6 hx (tauN_af rfl rfl d _ rfl) (h d).2⟩

/-- **PROVED**: an element of the intersection is a fixed point. -/
theorem inAllFixed : InAllFixed := fun x hx h =>
  inAllUnique _ x (relC_af rfl rfl x) hx (inAll_tau hx h) h

/-- **(L3) PROVED** -/
theorem fixedIffInAll : FixedIffInAll :=
  ⟨fun ⟨x, hx, hfix⟩ => ⟨x, hx, fun d => fixedInAll t3 t6 rfl rfl t3_t6 x hx hfix d⟩,
   fun ⟨x, hx, h⟩ => ⟨x, hx, inAllFixed x hx h⟩⟩

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

/-! ## Axiom pins: the proofs -/

#axioms_within PLLND.F0.Endpoints.selfIffReduced [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.copy_of_free [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.selfToCopy [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.closedToCopy [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.gR_rel [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.transportG [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.selfToClosed [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.tauSN_rel [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.selfTower [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.necBox [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.necClosed [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.necPow [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.necCells [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.not_copy_of_baseNo [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.bisim_force [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.realize [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.reduced_of_realize [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.glue_new_force [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.gadgetSelf [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.noClosedStepT3 [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.not_k5 [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.exists_of_not_imp [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.exists_of_not_box [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.exists_terminal [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.ts_realizes [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.twoSidedSelf [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.sidesOfNd [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.baseCriterion [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.copySelf_top [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.selfStep_t5 [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.selfStep_s2 [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.selfStep_aK [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.noGadgetAK [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.not_baseGadget [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.gadget_t3_t6 [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.selfStep_t3_t6 [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.selfStep_t5_t56 [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.tower_t5 [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.isBisimExt [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.extTops [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.not_extTop_b1 [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.not_extTop_b2 [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.not_extTop_b3 [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.t3_bP [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.nd_bP_t6 [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.nd_t6_bP [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.meet_sig_nne [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.meetNotTop [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.gate_T [propext, Quot.sound]

/-! ## Axiom pins: T1 and the L cells -/

#axioms_within PLLND.F0.Endpoints.minR_not_t3 [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.minR_realizes [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.minR_bP [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.selfStep_t3_bP [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.topT3Alt [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.topsT3NotMeet [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.noLeastTopT3 [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.notFixed_top [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.notFixed_t6 [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.notFixed_U2 [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.gate_L [propext, Quot.sound]

/-! ## Axiom pins: L1–L3 -/

#axioms_within PLLND.F0.Endpoints.sig_Ud [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.tauN_closed [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.towerEnds [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.closing [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.inAllUnique [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.inAllFixed [propext, Quot.sound]
#axioms_within PLLND.F0.Endpoints.fixedIffInAll [propext, Quot.sound]
