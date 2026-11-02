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

/-! # Stage 2: the realization API, `ext` finite, and the designed cells

The D5 cells are kernel-checked theorems (pins `[propext, Quot.sound]`):

* `cellInf`: the readers' gadget realizes `M₀` (infinite model);
* `cellAll`: no FINITE model realizes `M₀` through `g`.  In a finite model the odd
  rungs `φ_k` eventually hold everywhere (`phiK_eventually`: they increase, and once
  `φ_{n+1} ⊢ φ_n` holds pointwise, `φ_{n+2} = φ_{n+1} ∨ (φ_{n+1} ↠ φ_n)` holds
  everywhere), so every reader of large code holds everywhere (`force_xr_of`), while
  `M₀` refutes every atom; atoms of every code exist (`code_bigStr`).  Hence
  `not_finRealizerOfFaithful`: (D5) for all formulas is REFUTED;
* `cellClosed`: `RealizerC g` (on closed formulas `g = σ³`, realized by `ext³ M`);
* `cellTwoAtoms`: the finite table `gadT K1` realizes `M₀` for the formulas over
  `{a0, a1}`, and not over `{a0, a1, a2}` (`gate_third`, `not_table_three`).

Sanity cells for D3 (`sane_…`) and the gate `gate_ext` (each one-top version of
`ext` fails to realize `M₀` through `σ` at `⊥`). -/

namespace PLLND
namespace F0
namespace Realize

open SemUI Sig FreeHAn Base3 FreePLL MovingTop
open Interval (rel FreeInPLL topF)
open PLLND.LaxInfinite (atomFree)
open SubframeModel.CF (FinDec)

/-! ## The realization API -/

theorem realizes_comp {h k : Tr} {M : SubframeModel} {r : M.W} {N : SubframeModel} {w : N.W}
    {P : SubframeModel} {u : P.W} (hk : Realizes k M r N w) (hh : Realizes h N w P u) :
    Realizes (h ∘ k) M r P u := fun A => (hh (k A)).trans (hk A)

theorem realizes_id (M : SubframeModel) (r : M.W) : Realizes id M r M r := fun _ => Iff.rfl

theorem meetRealizes : MeetRealizes := fun _ _ _ _ _ _ hR hb A =>
  ⟨fun h => (hR A).mp h.1, fun h => ⟨(hR A).mpr h, hb⟩⟩

theorem congrRealizes : CongrRealizes := fun _ _ _ _ N w hi hR A =>
  (sem_of_interd (hi A) N w).symm.trans (hR A)

/-- **(D2) PROVED** -/
theorem realizerComp : RealizerComp := by
  intro h k hh hk M _ r
  obtain ⟨N, iN, w, hw⟩ := hk M r
  obtain ⟨P, iP, u, hu⟩ := hh N w
  exact ⟨P, iP, u, realizes_comp hw hu⟩

/-- **(D2) PROVED** -/
theorem realizerInfComp : RealizerInfComp := by
  intro h k hh hk M _ r
  obtain ⟨N, iN, w, hw⟩ := hk M r
  obtain ⟨P, u, hu⟩ := hh N w
  exact ⟨P, u, realizes_comp hw hu⟩

/-- **(D2), closed formulas, PROVED** -/
theorem realizerCComp : RealizerCComp := by
  intro h k hcl hh hk M _ r
  obtain ⟨N, iN, w, hw⟩ := hk M r
  obtain ⟨P, iP, u, hu⟩ := hh N w
  exact ⟨P, iP, u, fun A hA => (hu (k A) (hcl A hA)).trans (hw A hA)⟩

theorem realizerInf_of {h : Tr} (hR : Realizer h) : RealizerInf h := fun M _ r =>
  let ⟨N, _, w, hw⟩ := hR M r
  ⟨N, w, hw⟩

/-! ## `ext M` is finite when `M` is -/

instance extFinDec (M : SubframeModel) [FinDec M] : FinDec (ext M) where
  elems := (FinDec.elems (M := M)).map XW.orig ++ [XW.nT, XW.eT]
  complete w := by
    cases w with
    | orig x => exact List.mem_append_left _ (List.mem_map_of_mem (FinDec.complete x))
    | nT => exact List.mem_append_right _ (List.Mem.head _)
    | eT => exact List.mem_append_right _ (List.Mem.tail _ (List.Mem.head _))
  decLe u v := by
    cases u <;> cases v <;>
      first
      | (show Decidable (M.le _ _); infer_instance)
      | exact isTrue trivial
      | exact isFalse id
  decS u := by
    cases u <;>
      first
      | (show Decidable (_ ∈ M.S); infer_instance)
      | exact isTrue trivial
      | exact isFalse id
  decV a u := by
    cases u <;>
      first
      | (show Decidable (_ ∈ M.V a); infer_instance)
      | exact isTrue trivial

/-! ## (D3): `σ`, its iterates, and the readers -/

/-- **(D3) PROVED**: `ext M` realizes `M` through `σ`. -/
theorem realizerSig : RealizerSig := fun M _ r =>
  ⟨ext M, inferInstance, XW.orig r, fun A => orig_sig M A r⟩

theorem realizer_sigN : ∀ n : Nat, Realizer (sigN n)
  | 0 => fun M _ r => ⟨M, inferInstance, r, fun _ => Iff.rfl⟩
  | n + 1 => realizerComp (sigN n) sig (realizer_sigN n) realizerSig

/-- **(D3) PROVED**: the readers' gadget realizes every finite model. -/
theorem realizerInfReaders : RealizerInfReaders := fun M _ r =>
  ⟨GadR.MS M (· ∈ M.S), Base3.Gad.Pt.w r, fun A => GadR.transfer A r⟩

/-! ## Stage 2: the D5 cells -/

/-- **Cell (Inf) PROVED** -/
theorem cellInf : CellInf := realizerInfReaders M0 r0

/-- **Cell (Closed) PROVED**: on closed formulas `g = σ³`, realized by `ext³ M`. -/
theorem cellClosed : CellClosed := fun M _ r => by
  obtain ⟨N, iN, w, hw⟩ := realizer_sigN 3 M r
  exact ⟨N, iN, w, fun A hA => by rw [Endpoints.gR_closed hA]; exact hw A⟩

/-! ### Cell (All): every reader eventually holds everywhere in a finite model -/

open RNEmbed (rnP rn_odd_eq)

theorem phiK_succ (k : Nat) : phiK (k + 1) = (phiK k).or (ZL.relX (rnP k).2) := by
  unfold phiK
  rw [rn_odd_eq, rn_odd_eq]
  rfl

theorem relX_snd (k : Nat) : ZL.relX (rnP (k + 1)).2 = (phiK (k + 1)).ifThen (phiK k) := by
  unfold phiK
  rw [rn_odd_eq, rn_odd_eq]
  rfl

/-- `φ_{k+2} = φ_{k+1} ∨ (φ_{k+1} ↠ φ_k)`. -/
theorem phiK_two (k : Nat) : phiK (k + 2) = (phiK (k + 1)).or ((phiK (k + 1)).ifThen (phiK k)) := by
  rw [phiK_succ (k + 1), relX_snd]

/-- The truth value of `φ n` at the `i`-th listed world. -/
def readF (N : SubframeModel) [FinDec N] (φ : Nat → PLLFormula) (n i : Nat) : Bool :=
  match (FinDec.elems (M := N))[i]? with
  | some v => decide (N.force v (φ n))
  | none => false

theorem readF_some {N : SubframeModel} [FinDec N] {φ : Nat → PLLFormula} {n i : Nat} {v : N.W}
    (h : (FinDec.elems (M := N))[i]? = some v) : readF N φ n i = true ↔ N.force v (φ n) := by
  unfold readF
  rw [h]
  exact decide_eq_true_iff

theorem readF_none {N : SubframeModel} [FinDec N] {φ : Nat → PLLFormula} {n i : Nat}
    (h : (FinDec.elems (M := N))[i]? = none) : readF N φ n i = false := by
  unfold readF
  rw [h]

/-- **A monotone sequence of formulas stabilises in a finite model.** -/
theorem stab_findec (N : SubframeModel) [FinDec N] (φ : Nat → PLLFormula)
    (mono : ∀ n v, N.force v (φ n) → N.force v (φ (n + 1))) :
    ∃ n, ∀ v, N.force v (φ (n + 1)) → N.force v (φ n) := by
  obtain ⟨n, hn⟩ := InsideOut.stabilise (readF N φ) (FinDec.elems (M := N)).length
    (fun m i _ h => by
      cases hv : (FinDec.elems (M := N))[i]? with
      | none => rw [readF_none hv] at h; exact absurd h Bool.false_ne_true
      | some v => exact (readF_some hv).mpr (mono m v ((readF_some hv).mp h)))
  refine ⟨n, fun v hv => ?_⟩
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp (FinDec.complete v)
  obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hi
  exact (readF_some hi).mp (hn i hlt ((readF_some hi).mpr hv))

/-- **In a finite model the odd rungs `φ_k` eventually hold everywhere**: they
increase, and once `φ_{n+1} ⊢ φ_n` holds pointwise, `φ_{n+2} = φ_{n+1} ∨ (φ_{n+1} ↠ φ_n)`
holds everywhere. -/
theorem phiK_eventually (N : SubframeModel) [FinDec N] :
    ∃ n, ∀ k, n ≤ k → ∀ v, N.force v (phiK k) := by
  have mono : ∀ k v, N.force v (phiK k) → N.force v (phiK (k + 1)) := fun k v h => by
    rw [phiK_succ]
    exact Or.inl h
  obtain ⟨n, hn⟩ := stab_findec N phiK mono
  have h2 : ∀ j v, N.force v (phiK (n + 2 + j)) := by
    intro j
    induction j with
    | zero =>
        intro v
        show N.force v (phiK (n + 2))
        rw [phiK_two]
        exact Or.inr fun u _ hu => hn u hu
    | succ j ih => exact fun v => mono _ v (ih v)
  refine ⟨n + 2, fun k hk => ?_⟩
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  exact h2 j

/-- A reader holds wherever its separator's first rung holds everywhere. -/
theorem force_xr_of (N : SubframeModel) (a : String)
    (h : ∀ u, N.force u (phiK (Base3.code a + 1 + 1))) (v : N.W) : N.force v (xr a) :=
  Or.inr fun u _ hu => hu u (N.refl u) (Or.inl (h u))

/-- Strings of large code: `"\x00"` prefixed `n` times. -/
def bigStr : Nat → String
  | 0 => ""
  | n + 1 => "\x00" ++ bigStr n

theorem code_cons0 (s : String) : Base3.code ("\x00" ++ s) = 1 + 257 * Base3.code s := by
  show Base3.encB (("\x00".toByteArray ++ s.toByteArray).data.toList) =
    1 + 257 * Base3.encB s.toByteArray.data.toList
  rw [ByteArray.toList_data_append]
  have h0 : "\x00".toByteArray.data.toList = [0] := by decide
  rw [h0]
  show (0 : UInt8).toNat + 1 + 257 * Base3.encB s.toByteArray.data.toList =
    1 + 257 * Base3.encB s.toByteArray.data.toList
  have hz : (0 : UInt8).toNat = 0 := rfl
  rw [hz]

theorem code_bigStr : ∀ n : Nat, n ≤ Base3.code (bigStr n)
  | 0 => Nat.zero_le _
  | n + 1 => by
      have ih := code_bigStr n
      show n + 1 ≤ Base3.code ("\x00" ++ bigStr n)
      rw [code_cons0]
      omega

/-- **Cell (All) PROVED**: no finite pointed model realizes `M₀` through `g`. -/
theorem cellAll : CellAll := by
  rintro ⟨N, iN, w, hw⟩
  obtain ⟨n, hn⟩ := phiK_eventually N
  have hc := code_bigStr n
  have hx : N.force w (xr (bigStr n)) := force_xr_of N (bigStr n) (hn _ (by omega)) w
  exact Bool.false_ne_true ((hw (.prop (bigStr n))).mp hx)

/-- **(D5), all formulas, REFUTED** at `g`, `M₀`. -/
theorem not_finRealizerOfFaithful : ¬ FinRealizerOfFaithful := fun h =>
  cellAll (h gR (fun A B => freeReaders A B) M0 r0)

/-! ### Cell (TwoAtoms) -/

/-- `K` with the valuation replaced by `V'`. -/
def revalue (K : SubframeModel) (V' : String → Set K.W)
    (hV : ∀ {a : String} {u v : K.W}, K.le u v → u ∈ V' a → v ∈ V' a) : SubframeModel where
  W := K.W
  le := K.le
  S := K.S
  V := V'
  refl := K.refl
  trans := K.trans
  hered := hV

/-- Valuations agreeing on `P` give the same forcing on the formulas over `P`. -/
theorem revalue_force (K : SubframeModel) (V' : String → Set K.W)
    (hV : ∀ {a : String} {u v : K.W}, K.le u v → u ∈ V' a → v ∈ V' a) (P : String → Bool)
    (hP : ∀ a, P a = true → ∀ k, k ∈ V' a ↔ k ∈ K.V a) :
    ∀ A : PLLFormula, atomsIn P A = true → ∀ k : K.W,
      ((revalue K V' hV).force k A ↔ K.force k A)
  | .prop a, h, k => hP a h k
  | .falsePLL, _, _ => Iff.rfl
  | .and A B, h, k =>
      have h' : (atomsIn P A && atomsIn P B) = true := h
      and_congr (revalue_force K V' hV P hP A (Bool.and_eq_true_iff.mp h').1 k)
        (revalue_force K V' hV P hP B (Bool.and_eq_true_iff.mp h').2 k)
  | .or A B, h, k =>
      have h' : (atomsIn P A && atomsIn P B) = true := h
      or_congr (revalue_force K V' hV P hP A (Bool.and_eq_true_iff.mp h').1 k)
        (revalue_force K V' hV P hP B (Bool.and_eq_true_iff.mp h').2 k)
  | .ifThen A B, h, k => by
      have h' : (atomsIn P A && atomsIn P B) = true := h
      have hA := revalue_force K V' hV P hP A (Bool.and_eq_true_iff.mp h').1
      have hB := revalue_force K V' hV P hP B (Bool.and_eq_true_iff.mp h').2
      exact ⟨fun hk v hv hAv => (hB v).mp (hk v hv ((hA v).mpr hAv)),
        fun hk v hv hAv => (hB v).mpr (hk v hv ((hA v).mp hAv))⟩
  | .somehow A, h, k => by
      have hA := revalue_force K V' hV P hP A h
      exact ⟨fun hk v hv hS => (hA v).mp (hk v hv hS), fun hk v hv hS => (hA v).mpr (hk v hv hS)⟩

/-- The readers' table over `M₀` (`f0FreePLL`'s `gadT K1`: the ten upper worlds and the
copy `10` of the world of `M₀`). -/
abbrev G1 : SubTab.SubCM := gadT FreePLL.K1

theorem g1_ok : G1.okB = true := by decide +kernel

/-- The finite model of the table. -/
abbrev MG : SubframeModel := G1.toModel g1_ok

/-- The copy of the world of `M₀`. -/
def w10 : MG.W := ⟨10, by decide⟩

/-- The facts of the table the transfer needs, by `decide` in the kernel. -/
theorem g1_facts : G1.forceB 10 b3 = false ∧ G1.forceB 10 (xr a0) = false ∧
    G1.forceB 10 (xr a1) = false ∧ G1.SB 10 = false ∧
    (List.range 11).all (fun j => !(G1.leB 10 j) || j == 10 || G1.forceB j b3) = true := by
  decide +kernel

theorem mg_not {φ : PLLFormula} (h : G1.forceB 10 φ = false) : ¬ MG.force w10 φ := fun hf =>
  Bool.noConfusion ((show G1.forceB 10 φ = true from
    (SubTab.SubCM.forceB_iff g1_ok φ w10).mpr hf).symm.trans h)

/-- `M₀` has one world, outside `S`, forcing no atom. -/
theorem m0_eq (k : M0.W) : k = r0 := by
  obtain ⟨i, hi⟩ := k
  have h1 : FreePLL.K1.n = 1 := rfl
  obtain rfl : i = 0 := by omega
  rfl

theorem m0_notS (k : M0.W) : k ∉ M0.S := by
  rw [m0_eq k]
  exact fun h => Bool.false_ne_true h

theorem m0_notV (a : String) (k : M0.W) : k ∉ M0.V a := by
  rw [m0_eq k]
  exact fun h => Bool.false_ne_true h

/-- `M₀` with the valuation read off the table at `w10`. -/
def K' : SubframeModel :=
  revalue M0 (fun a => {_k | MG.force w10 (xr a)}) (fun _ h => h)

/-- The transfer of `f0FreePLL` on the table: `w10 ⊩ g A ⟺ K', r₀ ⊩ A`. -/
theorem table_transfer : ∀ (A : PLLFormula) (k : K'.W),
    (MG.force w10 (relB b3 xr A) ↔ K'.force k A) :=
  relB_transferO MG b3 xr K' (fun _ => w10) (fun v a hv => b3_le_xr_sem MG v a hv)
    (fun _ => mg_not g1_facts.1) (fun _ => MG.refl _)
    (fun k v hv => by
      obtain ⟨j, hj⟩ := v
      have hb := List.all_eq_true.mp g1_facts.2.2.2.2 j (List.mem_range.mpr hj)
      rw [show G1.leB 10 j = true from hv] at hb
      simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq] at hb
      rcases hb with h10 | hf
      · exact Or.inr ⟨k, M0.refl k, Subtype.ext h10.symm⟩
      · exact Or.inl ((SubTab.SubCM.forceB_iff g1_ok b3 ⟨j, hj⟩).mp hf))
    (fun k => iff_of_false (mg_S) (m0_notS k))
    (fun _ _ => Iff.rfl)
where
  mg_S : w10 ∉ MG.S := fun h => Bool.noConfusion ((show G1.SB 10 = true from h).symm.trans g1_facts.2.2.2.1)

/-- **Cell (TwoAtoms) PROVED**: the finite table realizes `M₀` for the formulas over `{a0, a1}`. -/
theorem cellTwoAtoms : CellTwoAtoms := by
  refine ⟨MG, inferInstance, w10, fun A hA => (table_transfer A r0).trans
    (revalue_force M0 _ _ P01 (fun a ha k => ?_) A hA r0)⟩
  have ha' : (a == a0 || a == a1) = true := ha
  simp only [Bool.or_eq_true, beq_iff_eq] at ha'
  refine iff_of_false ?_ (m0_notV a k)
  rcases ha' with rfl | rfl
  · exact mg_not g1_facts.2.1
  · exact mg_not g1_facts.2.2.1

/-! ### The gate of Cell (TwoAtoms), watched failing: a third atom

The table does not realize `M₀` for the formulas over `{a0, a1, a2}`: at the copy it
forces the reader of `a2 = "\x01"` (code 2, reader `gen 3`), while `M₀ ⊮ a2`.  This is
the obstruction of Cell (All) on one finite table. -/

/-- The atom of code 2. -/
def a2 : String := "\x01"

set_option maxRecDepth 100000 in
theorem gate_third : G1.forceB 10 (xr a2) = true := by decide +kernel

theorem not_table_three :
    ¬ RealizesOn (fun a => a == a0 || a == a1 || a == a2) gR M0 r0 MG w10 := fun h =>
  m0_notV a2 r0 ((h (.prop a2) (by decide)).mp
    ((SubTab.SubCM.forceB_iff g1_ok (xr a2) w10).mp gate_third))

/-! ### D3 sanity cells: the table `extT K` realizes `K` on designed formulas -/

/-- Designed closed formulas. -/
def closedCells : List PLLFormula := [.falsePLL, e, ne, t3, t4, t5, t6, .somehow t3, Endpoints.g1]

/-- `σ` on `ext K2` (`K2`: `k₀ ∈ S` below `k₁ ∉ S`). -/
theorem sane_sig_K2 : closedCells.all (fun A =>
    (extT FreePLL.K2 []).forceB 0 (sig A) == FreePLL.K2.forceB 0 A) = true := by decide +kernel

/-- The truth values at the root of `K2`, so the sanity cell is not uniform. -/
theorem sane_K2_values : closedCells.map (FreePLL.K2.forceB 0) =
    [false, false, false, false, true, true, false, false, true] := by decide +kernel

/-- The truth values at the root of `K3`. -/
theorem sane_K3_values : [pA, qA, O1, O2, O3].map (FreePLL.K3.forceB 0) =
    [false, false, true, false, false] := by decide +kernel

/-- `aTr t3` and `τ_P` on `ext K3` (atoms `a0`, `a1` true at the tops). -/
theorem sane_aTr_K3 : [pA, qA, O1, O2, O3].all (fun A =>
    (extT FreePLL.K3 [a0, a1]).forceB 0 (aTr t3 A) == FreePLL.K3.forceB 0 A) = true := by
  decide +kernel

theorem sane_tauP_K3 : [pA, qA, O1, O2, O3].all (fun A =>
    (extT FreePLL.K3 [a0, a1]).forceB 0 (tauP A) == FreePLL.K3.forceB 0 A) = true := by
  decide +kernel

/-- `K` with ONE top above every world, in `S` iff `s`, no atoms: a defective `ext`. -/
def extOnly (K : SubTab.SubCM) (s : Bool) : SubTab.SubCM :=
  { n := K.n + 1, root := K.root,
    le := ((List.range K.n).map fun i => (List.range K.n).map (K.leB i) ++ [true]) ++
      [List.replicate K.n false ++ [true]],
    S := (List.range K.n).map K.SB ++ [s],
    val := (List.range K.n).map (fun i => K.val.getD i []) ++ [[]] }

/-- **Gates, watched failing**: with only the non-`S` top, or only the `S` top, `σ⊥ = t3`
holds at the root of `M₀`'s copy, so neither realizes `M₀` through `σ` (at `A = ⊥`);
the control `ext` does. -/
theorem gate_ext : ((extOnly FreePLL.K1 false).forceB 0 (sig .falsePLL) ==
      FreePLL.K1.forceB 0 .falsePLL) = false ∧
    ((extOnly FreePLL.K1 true).forceB 0 (sig .falsePLL) ==
      FreePLL.K1.forceB 0 .falsePLL) = false ∧
    ((extT FreePLL.K1 []).forceB 0 (sig .falsePLL) == FreePLL.K1.forceB 0 .falsePLL) = true := by
  decide +kernel

end Realize
end F0
end PLLND

/-! ## Axiom pins: Stage 2 -/

#axioms_within PLLND.F0.Realize.k1_ok [propext, Quot.sound]
#axioms_within PLLND.F0.Realize.realizes_comp [propext, Quot.sound]
#axioms_within PLLND.F0.Realize.meetRealizes [propext, Quot.sound]
#axioms_within PLLND.F0.Realize.congrRealizes [propext, Quot.sound]
#axioms_within PLLND.F0.Realize.realizerComp [propext, Quot.sound]
#axioms_within PLLND.F0.Realize.realizerInfComp [propext, Quot.sound]
#axioms_within PLLND.F0.Realize.realizerCComp [propext, Quot.sound]
#axioms_within PLLND.F0.Realize.extFinDec [propext, Quot.sound]
#axioms_within PLLND.F0.Realize.realizerSig [propext, Quot.sound]
#axioms_within PLLND.F0.Realize.realizer_sigN [propext, Quot.sound]
#axioms_within PLLND.F0.Realize.realizerInfReaders [propext, Quot.sound]
#axioms_within PLLND.F0.Realize.cellInf [propext, Quot.sound]
#axioms_within PLLND.F0.Realize.cellClosed [propext, Quot.sound]
#axioms_within PLLND.F0.Realize.stab_findec [propext, Quot.sound]
#axioms_within PLLND.F0.Realize.phiK_eventually [propext, Quot.sound]
#axioms_within PLLND.F0.Realize.code_bigStr [propext, Quot.sound]
#axioms_within PLLND.F0.Realize.cellAll [propext, Quot.sound]
#axioms_within PLLND.F0.Realize.not_finRealizerOfFaithful [propext, Quot.sound]
#axioms_within PLLND.F0.Realize.revalue_force [propext, Quot.sound]
#axioms_within PLLND.F0.Realize.g1_facts [propext, Quot.sound]
#axioms_within PLLND.F0.Realize.table_transfer [propext, Quot.sound]
#axioms_within PLLND.F0.Realize.cellTwoAtoms [propext, Quot.sound]
#axioms_within PLLND.F0.Realize.gate_third [propext, Quot.sound]
#axioms_within PLLND.F0.Realize.not_table_three [propext, Quot.sound]
#axioms_within PLLND.F0.Realize.sane_sig_K2 [propext, Quot.sound]
#axioms_within PLLND.F0.Realize.sane_aTr_K3 [propext, Quot.sound]
#axioms_within PLLND.F0.Realize.sane_tauP_K3 [propext, Quot.sound]
#axioms_within PLLND.F0.Realize.gate_ext [propext, Quot.sound]
