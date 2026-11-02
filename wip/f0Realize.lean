import wip.f0Endpoints
import Meta.Audit

/-!
# Realizers: faithfulness of a translation from realizing models (spike S1)

Matthew, 2026-11-02, the category-theory programme, spike study S1.  Every
faithfulness proof of the F0 work builds countermodels: `ext`
(`wip/f0SelfSim.lean`), the readers' gadget (`wip/f0FreePLL.lean`), the
A-translation realizations (`wip/f0MovingTop.lean`, `wip/f0Endpoints.lean`).
In the language of duality: a translation `h` is injective on the Lindenbaum
algebra because the induced map on finite dual models is onto, every finite
countermodel of the source being realized by a model of the target.  This file
tests whether one abstract lemma and composable realizers can replace the glue
that each existing proof repeats.

## Notions

A *translation* is a function `h : PLLFormula → PLLFormula`.  A *pointed model*
is a subframe model `M` with a chosen world `r`; it is *finite* when `M` carries
`FinDec` (a list of all worlds, decidable order, `S` and valuation).

    Realizes h M r N w   :   ∀ A,  N, w ⊨ h A  ⟺  M, r ⊨ A
    RealizesC h M r N w  :   the same for closed A
    Realizer h           :   every finite pointed (M, r) has a finite (N, w) with Realizes h M r N w
    RealizerInf h        :   every finite pointed (M, r) has a pointed (N, w), N not necessarily
                             finite, with Realizes h M r N w
    RealizerC, RealizerInfC :  the closed-formula versions
    Preserves h          :   ∀ A B,  [A] ⊢ B  ⟹  [h A] ⊢ h B
    Faithful h           :   ∀ A B,  [A] ⊢ B  ⟺  [h A] ⊢ h B
    PreservesC, FaithfulC :  the same for closed A, B

`(N, w)` is then called a *realizing model* of `(M, r)` through `h`.

## Statements (Stage 1: committed before any proof, METHOD.md §1)

(D1) faithfulness from realization:

    FaithfulOfRealizer :   Preserves h  ∧  RealizerInf h   ⟹   Faithful h
    FaithfulCOfRealizer :  PreservesC h ∧  RealizerInfC h  ⟹   FaithfulC h

(D2) composition (`h ∘ k` applies `k` first):

    RealizerComp :     Realizer h  ∧  Realizer k     ⟹   Realizer (h ∘ k)
    RealizerInfComp :  RealizerInf h  ∧  Realizer k  ⟹   RealizerInf (h ∘ k)
    RealizerCComp :    k sends closed formulas to closed formulas,
                       RealizerC h  ∧  RealizerC k  ⟹   RealizerC (h ∘ k)

(D3) instances, and the two operations every instance needs:

    MeetRealizes :     Realizes h M r N w,  N, w ⊨ b   ⟹   Realizes (A ↦ h A ∧ b) M r N w
    CongrRealizes :    (∀ A,  h A ⊣⊢ h' A),  Realizes h M r N w   ⟹   Realizes h' M r N w
    RealizerSig :      Realizer σ                       (σ = ⊥ ↦ t3; the model ext M)
    RealizerATrT3 :    Realizer (aTr t3)                (Friedman's A-translation; ext M)
    RealizerTauP :     Realizer τ_P                     (τ_P A ⊣⊢ aTr t3 A ∧ t6; ext M, t6 everywhere)
    RealizerTauPN :    ∀ d,  Realizer τ_Pᵈ
    RealizerCRelC :    RealizerC (relC t3 t6)           (relC t3 t6 A ⊣⊢ σA ∧ t6, closed A)
    RealizerInfReaders :  RealizerInf g                 (g = relB σ³⊥ y; the readers' gadget GadR.MS)
    RealizerTwoSided : a closed,  SideIn a,  SideOut a   ⟹   RealizerInf (aTr a)   (the model TS)
    SelfStepOfRealizer :  [a] ⊢ b,  RealizerInf (A ↦ aTr a A ∧ b)   ⟹   SelfStep a b

(D4) re-derivations, as new theorems of this file (the originals untouched):
`CopyT3T6`, `PLLSelf`, `PLLSelfTower`, `PLLTowerInF0` of `wip/f0MovingTop.lean`,
and the sufficiency half of `BaseCriterion` of `wip/f0Endpoints.lean`:

    BaseSufficiency :  a closed,  ⊬ ◯a ↠ a,  ⊬ (◯a ↠ a) ↠ a   ⟹   SelfStep a ⊤

(D5) the converse, a CONJECTURE to screen:

    FinRealizerOfFaithful :    Faithful h   ⟹   Realizer h
    FinRealizerCOfFaithfulC :  FaithfulC h  ⟹   RealizerC h
    FinRealizerOnOfFaithful :  Faithful h,  P a finite set of atoms   ⟹
                                 every finite (M, r) has a finite (N, w) realizing it
                                 for the formulas over P

with the designed cells, all at `M₀` = one world, not in `S`, no atom true
(the table `FreePLL.K1`), translation `g` (faithful: `freeReaders`):

    CellInf :      some pointed (N, w) realizes (M₀, r₀) through g         (the gadget, infinite)
    CellAll :      no finite pointed (N, w) realizes (M₀, r₀) through g
    CellClosed :   RealizerC g
    CellTwoAtoms : a finite (N, w) realizes (M₀, r₀) through g for the formulas over {a0, a1}

Status of every statement at Stage 1: OPEN (statements only; no theorem, no
`sorry`).
-/

set_option autoImplicit false

open PLLFormula

namespace PLLND
namespace F0
namespace Realize

open SemUI Sig FreeHAn Base3 FreePLL MovingTop
open Interval (rel FreeInPLL topF)
open PLLND.LaxInfinite (atomFree)
open SubframeModel.CF (FinDec)

/-! ## Notions -/

/-- A translation of formulas. -/
abbrev Tr := PLLFormula → PLLFormula

/-- `h` preserves derivability. -/
def Preserves (h : Tr) : Prop := ∀ A B : PLLFormula, Deriv [A] B → Deriv [h A] (h B)

/-- `h` preserves and reflects derivability. -/
def Faithful (h : Tr) : Prop := ∀ A B : PLLFormula, Deriv [A] B ↔ Deriv [h A] (h B)

/-- `h` preserves derivability between closed formulas. -/
def PreservesC (h : Tr) : Prop :=
  ∀ A B : PLLFormula, atomFree A = true → atomFree B = true → Deriv [A] B → Deriv [h A] (h B)

/-- `h` preserves and reflects derivability between closed formulas. -/
def FaithfulC (h : Tr) : Prop :=
  ∀ A B : PLLFormula, atomFree A = true → atomFree B = true → (Deriv [A] B ↔ Deriv [h A] (h B))

/-- **`(N, w)` realizes `(M, r)` through `h`**: `N, w ⊨ h A ⟺ M, r ⊨ A` for every `A`. -/
def Realizes (h : Tr) (M : SubframeModel) (r : M.W) (N : SubframeModel) (w : N.W) : Prop :=
  ∀ A : PLLFormula, N.force w (h A) ↔ M.force r A

/-- The same, closed formulas only. -/
def RealizesC (h : Tr) (M : SubframeModel) (r : M.W) (N : SubframeModel) (w : N.W) : Prop :=
  ∀ A : PLLFormula, atomFree A = true → (N.force w (h A) ↔ M.force r A)

/-- **A realizer**: every finite pointed model is realized by a finite one. -/
def Realizer (h : Tr) : Prop :=
  ∀ (M : SubframeModel) [FinDec M] (r : M.W),
    ∃ (N : SubframeModel) (_ : FinDec N) (w : N.W), Realizes h M r N w

/-- A realizer whose realizing models need not be finite. -/
def RealizerInf (h : Tr) : Prop :=
  ∀ (M : SubframeModel) [FinDec M] (r : M.W), ∃ (N : SubframeModel) (w : N.W), Realizes h M r N w

/-- The closed-formula realizer, finite realizing models. -/
def RealizerC (h : Tr) : Prop :=
  ∀ (M : SubframeModel) [FinDec M] (r : M.W),
    ∃ (N : SubframeModel) (_ : FinDec N) (w : N.W), RealizesC h M r N w

/-- The closed-formula realizer, realizing models not necessarily finite. -/
def RealizerInfC (h : Tr) : Prop :=
  ∀ (M : SubframeModel) [FinDec M] (r : M.W), ∃ (N : SubframeModel) (w : N.W), RealizesC h M r N w

/-! ## (D1) faithfulness from realization -/

/-- **(D1)** -/
def FaithfulOfRealizer : Prop := ∀ h : Tr, Preserves h → RealizerInf h → Faithful h

/-- **(D1), closed formulas** -/
def FaithfulCOfRealizer : Prop := ∀ h : Tr, PreservesC h → RealizerInfC h → FaithfulC h

/-! ## (D2) composition -/

/-- **(D2)** -/
def RealizerComp : Prop := ∀ h k : Tr, Realizer h → Realizer k → Realizer (h ∘ k)

/-- **(D2)**, the outer realizing models not necessarily finite. -/
def RealizerInfComp : Prop := ∀ h k : Tr, RealizerInf h → Realizer k → RealizerInf (h ∘ k)

/-- **(D2), closed formulas** -/
def RealizerCComp : Prop :=
  ∀ h k : Tr, (∀ A, atomFree A = true → atomFree (k A) = true) →
    RealizerC h → RealizerC k → RealizerC (h ∘ k)

/-! ## (D3) instances -/

/-- The interval meet: a realization through `h` at a world forcing `b` is one through
`A ↦ h A ∧ b`. -/
def MeetRealizes : Prop :=
  ∀ (h : Tr) (b : PLLFormula) (M : SubframeModel) (r : M.W) (N : SubframeModel) (w : N.W),
    Realizes h M r N w → N.force w b → Realizes (fun A => (h A).and b) M r N w

/-- Realization is invariant under replacing `h` by a pointwise interderivable `h'`. -/
def CongrRealizes : Prop :=
  ∀ (h h' : Tr) (M : SubframeModel) (r : M.W) (N : SubframeModel) (w : N.W),
    (∀ A, Interd (h A) (h' A)) → Realizes h M r N w → Realizes h' M r N w

/-- **(D3)** `σ = ⊥ ↦ t3` (the model `ext M`). -/
def RealizerSig : Prop := Realizer sig

/-- **(D3)** Friedman's A-translation `aTr t3` (the model `ext M`). -/
def RealizerATrT3 : Prop := Realizer (aTr t3)

/-- **(D3)** `τ_P = rel t3 t6 x_P` (the model `ext M`, where `t6` holds everywhere). -/
def RealizerTauP : Prop := Realizer tauP

/-- **(D3)** the iterates `τ_Pᵈ` (the composites of D2). -/
def RealizerTauPN : Prop := ∀ d : Nat, Realizer (tauPN d)

/-- **(D3)** the copy of F0 in `[t3, t6]`, closed formulas. -/
def RealizerCRelC : Prop := RealizerC (relC t3 t6)

/-- **(D3)** the readers `g = relB σ³⊥ y` (the gadget `GadR.MS`, infinite). -/
def RealizerInfReaders : Prop := RealizerInf gR

/-- **(D3)** the two-sided realization of `wip/f0Endpoints.lean` (the model `TS`). -/
def RealizerTwoSided : Prop :=
  ∀ a : PLLFormula, atomFree a = true → Endpoints.SideIn a → Endpoints.SideOut a →
    RealizerInf (aTr a)

/-- **(D3)** the A-translation step from a realizer of `A ↦ aTr a A ∧ b`. -/
def SelfStepOfRealizer : Prop :=
  ∀ a b : PLLFormula, Deriv [a] b → RealizerInf (fun A => (aTr a A).and b) →
    Endpoints.SelfStep a b

/-! ## (D4) the sufficiency half of the base criterion

The other D4 targets are the Props `CopyT3T6`, `PLLSelf`, `PLLSelfTower` and
`PLLTowerInF0` of `wip/f0MovingTop.lean`. -/

/-- **(D4)** the sufficiency half of `Endpoints.BaseCriterion`. -/
def BaseSufficiency : Prop :=
  ∀ a : PLLFormula, atomFree a = true → ¬ Deriv [] (subBot a ne) →
    ¬ Deriv [] (subBot a Endpoints.nne) → Endpoints.SelfStep a topF

/-! ## (D5) the converse, a conjecture to screen -/

/-- The atoms of `A` lie in `P`. -/
def atomsIn (P : String → Bool) : PLLFormula → Bool
  | .prop a => P a
  | .falsePLL => true
  | .and A B => atomsIn P A && atomsIn P B
  | .or A B => atomsIn P A && atomsIn P B
  | .ifThen A B => atomsIn P A && atomsIn P B
  | .somehow A => atomsIn P A

/-- Realization for the formulas over the atoms `P`. -/
def RealizesOn (P : String → Bool) (h : Tr) (M : SubframeModel) (r : M.W) (N : SubframeModel)
    (w : N.W) : Prop :=
  ∀ A : PLLFormula, atomsIn P A = true → (N.force w (h A) ↔ M.force r A)

/-- **(D5)**, all formulas: a CONJECTURE. -/
def FinRealizerOfFaithful : Prop := ∀ h : Tr, Faithful h → Realizer h

/-- **(D5)**, closed formulas: a CONJECTURE. -/
def FinRealizerCOfFaithfulC : Prop := ∀ h : Tr, FaithfulC h → RealizerC h

/-- **(D5)**, the formulas over a finite set of atoms: a CONJECTURE. -/
def FinRealizerOnOfFaithful : Prop :=
  ∀ (h : Tr) (P : String → Bool), (∃ l : List String, ∀ a, P a = true → a ∈ l) → Faithful h →
    ∀ (M : SubframeModel) [FinDec M] (r : M.W),
      ∃ (N : SubframeModel) (_ : FinDec N) (w : N.W), RealizesOn P h M r N w

/-- The table `M₀ = FreePLL.K1` is a finite model. -/
theorem k1_ok : FreePLL.K1.okB = true := by decide

/-- `M₀`: one world, not in `S`, no atom true. -/
abbrev M0 : SubframeModel := FreePLL.K1.toModel k1_ok

/-- Its world. -/
def r0 : M0.W := ⟨0, by decide⟩

/-- **Cell (Inf)**: some pointed model realizes `(M₀, r₀)` through `g`. -/
def CellInf : Prop := ∃ (N : SubframeModel) (w : N.W), Realizes gR M0 r0 N w

/-- **Cell (All)**: no finite pointed model realizes `(M₀, r₀)` through `g`. -/
def CellAll : Prop := ¬ ∃ (N : SubframeModel) (_ : FinDec N) (w : N.W), Realizes gR M0 r0 N w

/-- **Cell (Closed)**: `g` has a finite realizer for closed formulas. -/
def CellClosed : Prop := RealizerC gR

/-- The two atoms `a0 = ""`, `a1 = "\x00"`. -/
def P01 (a : String) : Bool := a == a0 || a == a1

/-- **Cell (TwoAtoms)**: a finite pointed model realizes `(M₀, r₀)` through `g` for the
formulas over `{a0, a1}`. -/
def CellTwoAtoms : Prop :=
  ∃ (N : SubframeModel) (_ : FinDec N) (w : N.W), RealizesOn P01 gR M0 r0 N w

end Realize
end F0
end PLLND
