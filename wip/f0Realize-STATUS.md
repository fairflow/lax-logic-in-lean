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

## Stage 3 (2026-11-02 14:45 CET): proofs, and the progress test

Every theorem sorry-free, pinned by `#axioms_within … [propext, Quot.sound]`.

| statement | status | theorem |
|---|---|---|
| (D1) `FaithfulOfRealizer`, `FaithfulCOfRealizer` | PROVED | `faithfulOfRealizer` (core: `reflects_of_realizerInf`, 5 lines), `faithfulCOfRealizer` |
| (D2) `RealizerComp`, `RealizerInfComp`, `RealizerCComp` | PROVED (Stage 2) | `realizerComp`, `realizerInfComp`, `realizerCComp` |
| (D3) `MeetRealizes`, `CongrRealizes` | PROVED (Stage 2) | `meetRealizes`, `congrRealizes` |
| (D3) `RealizerSig`, `RealizerATrT3`, `RealizerTauP`, `RealizerTauPN`, `RealizerCRelC` | PROVED | `realizerSig`, `realizerATrT3`, `realizerTauP`, `realizerTauPN`, `realizerCRelC` |
| (D3) `RealizerInfReaders`, `RealizerTwoSided` | PROVED | `realizerInfReaders`, `realizerTwoSided` |
| (D3) `SelfStepOfRealizer` | PROVED | `selfStepOfRealizer` |
| (D4) `CopyT3T6`, `PLLSelf`, `PLLSelfTower`, `PLLTowerInF0` | PROVED again | `copyT3T6_r`, `pllSelf_r`, `pllSelfTower_r`, `pllTowerInF0_r` |
| (D4) `BaseSufficiency` | PROVED | `baseSufficiency_r` |
| (D5) `FinRealizerOfFaithful` | REFUTED (Stage 2) | `not_finRealizerOfFaithful` |
| (D5) `FinRealizerCOfFaithfulC`, `FinRealizerOnOfFaithful` | OPEN | cells `cellClosed`, `cellTwoAtoms` pass |

(D1) needs neither the subframe tableau nor `SubCM` tables: given `[h A] ⊢ h B` and a
finite `M, r ⊨ A`, a realizing `(N, w)` has `N, w ⊨ h A`, so `N, w ⊨ h B` by
soundness, so `M, r ⊨ B`; completeness for finite models (`Interval.deriv_of_sem`)
gives `[A] ⊢ B`.

Independence of the re-derivations (Stage 3 gate watch, `gatewatch3.lean` in the
scratchpad): a closure search over used constants (`#uses`, written there) reports
that none of `copyT3T6_r`, `pllSelf_r`, `pllSelfTower_r`, `pllTowerInF0_r`,
`baseSufficiency_r` uses its original (`copyT3T6`, `copyIffTopAvoid`, `sigAvoidT6`;
`pllSelf`, `pllSelfReduced`, `genIff`; `pllSelfTower`, `tauPN_faithful`;
`g_faithful`, `freeReaders_reflects`; `baseCriterion`, `twoSidedSelf`,
`reduced_of_realize`, `selfIffReduced`); four controls (dependences that exist) print
`true`.  `#axiom_path` of `Meta/Audit.lean` cannot answer this: its `dependsOn` is
`collectAxioms`, so it reported a dependence that exists (`ts_realizes`) as absent;
watched, and replaced by `#uses`.  Narrowed pins `faithfulOfRealizer [propext]`,
`pllSelf_r [Quot.sound]`, `pllTowerInF0_r []`, `baseSufficiency_r [propext]`,
`copyT3T6_r [Quot.sound]`: exit 1, exactly five errors.

### The progress test: lines

Counted by a script (`count.py` in the scratchpad): the declaration's signature and
body, without doc comments, comment lines or blank lines.  "Replaced" = on the
original proof path and not used by the new route; "excl." = used by nothing else in
the tree (so deletable), "shared" = still carries other results.  Lemmas both routes
use (the model constructions and forcing lemmas) are listed but counted in neither
total.

| target | original lines replaced | used by both routes (not counted) | new, target-specific |
|---|---|---|---|
| `CopyT3T6` | `copyT3T6` 1, `topAvoidT3T6` 1 (excl.); `copyIffTopAvoid` 17, `sigAvoidT6` 14 (shared) | `orig_sig` 20, `t6_ext` 10, `relC_interd` 3, `relC_mono` 8 | `copyT3T6_r` 3, `realizerCRelC` 4 = 7 |
| `PLLSelf` | `pllSelf` 6, `pllSelfReduced` 14, `relB_eq_aTr` 15 (excl.); `genIff` 24 (shared) | `orig_aTr` 20, `top_aTr` 8, `t6_ext`, `relGen` 9, `Endpoints.relB_aTr` 16 | `pllSelf_r` 3 |
| `PLLSelfTower` | `pllSelfTower` 11, `tauP_faithful` 1, `tauPN_faithful` 4, `tauPN_succ'` 3, `tauP_interd` 2, `tauPN_rel` 14 (excl.) | `deriv_iff_of_interd` 4, `Endpoints.tauSN_rel` 15 (in place of `tauPN_rel`) | `pllSelfTower_r` 10, `tauPN_rel_r` 4, `tauPN_eq` 3, `tauPN_faithful_r` 2, `tauPN_preserves` 3, `tauP_preserves` 1, `tauP_aTr` 2, `realizerTauP` 3, `realizerTauPN` 3, `extFinDec` 24 = 55 |
| `PLLTowerInF0` | `pllTowerInF0` 9 (excl.); `g_faithful` 1, `freeReaders_reflects` 10 (shared) | `b3_le_g` 3, `GadR.transfer`, `freeReaders_preserves` | `pllTowerInF0_r` 12, `gR_faithful_r` 2, `gTower_faithful_r` 3, `realizerInfReaders` 2 = 19 |
| `BaseSufficiency` | the sufficiency lines of `baseCriterion` 2, `twoSidedSelf` 5 (excl.); `reduced_of_realize` 17, `selfIffReduced` 9 (shared) | `sidesOfNd` 28, `ts_realizes` 26, `TS` and its bisimulations, `realize` 22, `bisim_force` | `baseSufficiency_r` 6, `realizerTwoSided` 4 = 10 |
| **totals** | **excl. 88; shared 92; replaced 180** | | **target-specific 94** |

General layer, counted once: the notions (`Tr`, `Preserves`, `Faithful`,
`PreservesC`, `FaithfulC`, `Realizes`, `RealizesC`, `Realizer`, `RealizerInf`,
`RealizerC`, `RealizerInfC`) 21; (D1) `reflects_of_realizerInf` 5,
`faithfulOfRealizer` 2, `faithfulCOfRealizer` 4, `realizerInf_of` 3,
`realizerInfC_of` 3; (D2) `realizes_comp` 3, `realizerComp` 5, `realizerInfComp` 5;
(D3) `meetRealizes` 2, `congrRealizes` 2, `preserves_congr` 2, `selfGen_interd` 5,
`aTrMeet_preserves` 6, `selfStepOfRealizer` 8.  Total **76**.  (Not counted, used by
no D4 target: `realizerCComp` 5, `realizes_id` 1, `realizerSig` 2, `realizer_sigN` 3,
`realizerATrT3` 2, the Stage-1 statement Props, the D5 cells.)

New total **170** lines against **88** deletable original lines (**180** on the
original proof paths, 92 of which stay because other results use them).

**Verdict: on these five targets the lemma does not pay for itself.**  It costs about
twice the lines it would let us delete, and only breaks even against the full proof
paths.  What the numbers show:

* (D1) itself is cheap and real: 5 lines replace the countermodel glue (subframe
  tableau → `SubCM` table → `toModel` → soundness → forcing lemma → `forceB_iff`),
  10–17 lines in each of `sig_reflects`, `sigAvoidT6`, `pllSelfReduced`,
  `reduced_of_realize`, `freeReaders_reflects`, `freeReadersIPC_reflects`.  With
  `selfStepOfRealizer` (21 lines with its helpers) a one-step A-translation result
  costs 3–10 lines (`pllSelf_r` 3, `copyT3T6_r` 7, `baseSufficiency_r` 10).
* The bulk of every original proof is the model construction and its forcing lemma
  (`orig_sig`, `orig_aTr`, `TS` with `realize` and the bisimulations, `GadR.transfer`):
  the abstraction does not touch it, and both routes carry it.
* (D2) bought nothing.  Composing realizers is as short as composing faithful maps
  (`realizerTauPN` 3 lines against `tauPN_faithful` 4), and the finite composition the
  tower needs costs a `FinDec (ext M)` instance (24 lines) that the original induction
  did not need.  `pllSelfTower_r` is short only because `Endpoints.tauSN_rel`
  already existed; that saving is not the realizers'.
* The finite realizer is a strictly stronger notion than faithfulness (Stage 2,
  `cellAll`), so (D1) must be, and is, stated with `RealizerInf`.

Where the layer would pay: as the standard route for NEW faithfulness results, and
as a retrofit of the six glue copies listed above (about 80 lines, against D1's 5).
A negative result on the five targets measured here.

Builds (every one `gtimeout 3600 lake build wip.f0Realize`, exit 0): Stage 1 17 s,
Stage 2 24 s (`-q`), Stage 3 18 s (`-q`), final 13 s (module 10 s).  Drafts checked
with `gtimeout 900 lake env lean` on scratch files (all exit 0 in the end; failed
drafts: Stage 2 three runs (`simp` on list membership, `code` resolved to another
namespace and an `omega` on `K1.n`, a leftover `omega` after `rw` closed the goal),
one run for guessed root values; Stage 3 none).  Probes: `probe_gen3` 12 s,
`probe_vals`.  Gate watches: `gatewatch2.lean` (six intended errors), `gatewatch3.lean`
(five intended errors; `#uses` controls `true`, independence `false`).  No decider run
(`pllfast`, `plldecide`, `SubTab.solve`), no `lake exe`, no cap hit, nothing skipped.
`df` before each build: 100 GB available.
