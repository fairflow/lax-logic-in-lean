# `wip/f0Realize.lean`: status

Spike study S1 of the category-theory programme (Matthew, 2026-11-02): can one
abstract lemma (faithfulness from realizing models) and composable realizers
replace the countermodel glue that every F0 faithfulness proof repeats?
Branch `f0-realizers`, local, from `origin/main` 4a1b755b.

## Stage 1 (2026-11-02 14:23 CET): statements committed

All statements are `Prop` definitions in `PLLND.F0.Realize`; no theorem about
them, no `sorry` (the only theorem, `k1_ok`, checks that the table `FreePLL.K1`
is a well-formed finite model).  Status of every statement: OPEN.  The
displayed forms are the module docstring.

Notions.  A translation is `h : PLLFormula → PLLFormula`; a pointed model is a
subframe model `M` with a world `r`, finite when `M` carries `FinDec`.

    Realizes h M r N w  :  ∀ A,  N, w ⊨ h A  ⟺  M, r ⊨ A      (RealizesC: closed A only)
    Realizer h          :  every finite (M, r) has a finite (N, w) with Realizes h M r N w
    RealizerInf h       :  the same, N not necessarily finite
    Preserves h / Faithful h :  [A] ⊢ B ⟹ / ⟺ [h A] ⊢ h B      (…C: closed A, B)

| name | statement |
|---|---|
| (D1) `FaithfulOfRealizer` | `Preserves h ∧ RealizerInf h ⟹ Faithful h` |
| (D1) `FaithfulCOfRealizer` | `PreservesC h ∧ RealizerInfC h ⟹ FaithfulC h` |
| (D2) `RealizerComp` | `Realizer h ∧ Realizer k ⟹ Realizer (h ∘ k)` |
| (D2) `RealizerInfComp` | `RealizerInf h ∧ Realizer k ⟹ RealizerInf (h ∘ k)` |
| (D2) `RealizerCComp` | `k` closed-to-closed, `RealizerC h ∧ RealizerC k ⟹ RealizerC (h ∘ k)` |
| (D3) `MeetRealizes` | `Realizes h M r N w`, `N, w ⊨ b` ⟹ `Realizes (A ↦ h A ∧ b) M r N w` |
| (D3) `CongrRealizes` | `∀ A, h A ⊣⊢ h' A` ⟹ (`Realizes h` ⟹ `Realizes h'`) |
| (D3) `RealizerSig` | `Realizer σ` (`ext M`) |
| (D3) `RealizerATrT3` | `Realizer (aTr t3)` (`ext M`) |
| (D3) `RealizerTauP`, `RealizerTauPN` | `Realizer τ_P`, `∀ d, Realizer τ_Pᵈ` |
| (D3) `RealizerCRelC` | `RealizerC (relC t3 t6)` |
| (D3) `RealizerInfReaders` | `RealizerInf g`, `g = relB σ³⊥ y` (`GadR.MS`, infinite) |
| (D3) `RealizerTwoSided` | `a` closed, `SideIn a`, `SideOut a` ⟹ `RealizerInf (aTr a)` (`TS`) |
| (D3) `SelfStepOfRealizer` | `[a] ⊢ b`, `RealizerInf (A ↦ aTr a A ∧ b)` ⟹ `SelfStep a b` |
| (D4) targets | `CopyT3T6`, `PLLSelf`, `PLLSelfTower`, `PLLTowerInF0` (`wip/f0MovingTop.lean`) |
| (D4) `BaseSufficiency` | `a` closed, `⊬ ◯a ↠ a`, `⊬ (◯a ↠ a) ↠ a` ⟹ `SelfStep a ⊤` |
| (D5) `FinRealizerOfFaithful` | CONJECTURE: `Faithful h ⟹ Realizer h` |
| (D5) `FinRealizerCOfFaithfulC` | CONJECTURE: `FaithfulC h ⟹ RealizerC h` |
| (D5) `FinRealizerOnOfFaithful` | CONJECTURE: the same over a finite set of atoms |

D5 cells, at `M₀` = one world, not in `S`, no atom true (`FreePLL.K1`), translation
`g` (faithful by `freeReaders`): `CellInf` (some pointed model realizes it),
`CellAll` (no finite one does), `CellClosed` (`RealizerC g`), `CellTwoAtoms` (a
finite one does for the formulas over `{a0, a1}`).

Build: `gtimeout 3600 lake build wip.f0Realize`, exit 0, 17 s.
