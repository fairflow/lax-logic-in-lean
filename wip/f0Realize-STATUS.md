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

## Stage 2 (2026-11-02 14:36 CET): the designed cells, kernel-checked

All cells at `M₀` = `FreePLL.K1` (one world, not in `S`, no atom true), translation
`g = relB σ³⊥ y` (faithful: `freeReaders`).  Pins `[propext, Quot.sound]`.

| cell | verdict | theorem | object |
|---|---|---|---|
| `CellInf` | PROVED | `cellInf` | the readers' gadget `GadR.MS M₀` (infinite) |
| `CellAll` | PROVED | `cellAll` | proof: no finite model realizes `M₀` through `g` |
| (D5) `FinRealizerOfFaithful` | **REFUTED** | `not_finRealizerOfFaithful` | `g` at `M₀` |
| `CellClosed` | PROVED (D5 closed passes at `g`) | `cellClosed` | `ext³ M` (`g = σ³` on closed formulas) |
| `CellTwoAtoms` | PROVED (D5 over `{a0, a1}` passes at `g`, `M₀`) | `cellTwoAtoms` | the table `gadT K1` (11 worlds), copy `w10` |
| gate: a third atom | the same table fails over `{a0, a1, a2}` | `gate_third`, `not_table_three` | `w10 ⊩ y(a2) = gen 3`, `M₀ ⊮ a2` |

The obstruction (`cellAll`).  In a finite model the odd Rieger–Nishimura rungs
`φ_k = relX(rn(2k+1))` eventually hold at every world (`phiK_eventually`): they
increase, a monotone sequence of subsets of a finite set stabilises in one step
(`stab_findec`, from `InsideOut.stabilise`), and once `φ_{n+1} ⊢ φ_n` holds pointwise,

    φ_{n+2} = φ_{n+1} ∨ (φ_{n+1} ↠ φ_n)          (phiK_two)

holds everywhere.  Then every separator `c_r = φ_{r+1} ∨ (φ_{r+2} ↠ σ²⊥)` of large
index holds everywhere, so every reader `y(a) = gen(code a + 1) = σ³⊥ ∨ ((c ↠ σ²⊥) ↠ σ²⊥)`
of large code holds everywhere (`force_xr_of`).  `M₀` refutes every atom, so a
realizing world must refute `y(a)` for every atom `a`, and atoms of every code exist
(`bigStr n = "\x00"ⁿ`, `n ≤ code (bigStr n)`, `code_bigStr`).  So a faithful
translation can need infinite realizing models: the shape is infinitely many atoms
read by closed formulas whose truth sets stabilise in finite models.

What stays OPEN: `FinRealizerCOfFaithfulC` (closed formulas) and
`FinRealizerOnOfFaithful` (finitely many atoms).  Both pass their cell at `g`; the
obstruction above needs unboundedly many atoms and does not apply to either.  Pen
(not mechanised): a faithful `h` that does not preserve `∧` or `∨` up to `⊣⊢` need
not pull prime theories back to prime theories, so even `RealizerInf` may fail for
such `h`; every translation of this development is a homomorphism up to a meet with
a top, where this does not arise.

D3 sanity cells (`decide` in the kernel): `sane_sig_K2` (σ on `ext K2`, nine closed
formulas, values `sane_K2_values` not uniform), `sane_aTr_K3`, `sane_tauP_K3`
(`aTr t3`, `τ_P` on `ext K3`, formulas `p, q, O1, O2, O3`, values `sane_K3_values`).
`gate_ext`: `K1` with only the non-`S` top, or only the `S` top, forces `σ⊥ = t3` at
the root, so neither realizes `K1` through `σ`; the control `ext K1` does.

Gates watched failing (`gatewatch2.lean` in the scratchpad, imports the built
module, `lake env lean`, exit 1 with exactly the six intended errors): the narrowed
pins `cellAll [propext]`, `cellTwoAtoms [Quot.sound]`,
`not_finRealizerOfFaithful []`, `stab_findec [propext]`; the corrupted table fact
`gadT K1, w10 ⊩ y(a0)` (decide: false); the defective one-top `ext` claimed to
realize at `⊥` (decide: false).

Stage 2 also proves the D2 statements and the D3 instances the cells need:
`realizerComp`, `realizerInfComp`, `realizerCComp`, `meetRealizes`,
`congrRealizes`, `realizerSig` (with the instance `extFinDec : FinDec (ext M)`),
`realizer_sigN`, `realizerInfReaders`.

Build: `gtimeout 3600 lake build wip.f0Realize -q`, exit 0, 24 s.  Probes (`lake
env lean`, 300 s caps): `probe_gen3` (the third reader on `gadT K1`, 12 s, exit 0),
`probe_vals` (root values, exit 0).  One draft run failed on the guessed values
of `sane_K2_values` (corrected from the evaluator).
