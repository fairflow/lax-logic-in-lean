# Proof-status ledger

Generated 2026-09-16 11:47 BST from `db9118b` by `scripts/ledger.lean`, which asks `Lean.collectAxioms` — the same function `#print axioms` uses, and by CLAUDE.md rule 1 the only sound oracle — about every declaration of every module listed in `docs/ledger-modules.txt`.

This file is generated.  Edit `scripts/ledger-report.py`, never the text below; `scripts/check-ledger.sh` fails if `docs/status-ledger.jsonl` no longer matches the build.

**17449 declarations** in **395 modules**: 8635 theorems, 8814 definitions and data. **81 carry `sorryAx`** and **2 are `native_decide`-tainted**; the rest are kernel-checked under the axioms shown below.

## What the columns mean

* **kernel-clean** — the declaration's axiom set is contained in `{propext, Classical.choice, Quot.sound}`: PROVED, in the sense of CLAUDE.md rule 1.
* **`sorryAx`** — the declaration ASSERTS something not proved. It is OPEN, whatever its statement says (`sorry-is-not-an-open-question`).
* **native** — checked by the compiler, not the kernel, so not PROVED. Two spellings count: the fixed `Lean.ofReduceBool` / `ofReduceNat` / `trustCompiler`, and the per-declaration axiom a `native_decide` call mints under Lean 4.31 (`X._native.native_decide.ax_1_1`), which a check against the three fixed names alone does not see.

## By area

| area | decls | theorems | kernel-clean | `sorryAx` | native |
|---|--:|--:|--:|--:|--:|
| `CLPPaper` | 85 | 9 | 85 |  |  |
| `FRJ.Basic` | 240 | 127 | 240 |  |  |
| `FRJ.Bridge` | 15 | 12 | 15 |  |  |
| `FRJ.Calculus` | 232 | 82 | 232 |  |  |
| `FRJ.CalculusV` | 167 | 70 | 167 |  |  |
| `FRJ.CalculusVLemmas` | 13 | 13 | 13 |  |  |
| `FRJ.CalculusW` | 153 | 62 | 153 |  |  |
| `FRJ.Complete` | 103 | 51 | 103 |  |  |
| `FRJ.Erase` | 22 | 20 | 22 |  |  |
| `FRJ.Extract` | 81 | 34 | 81 |  |  |
| `FRJ.ExtractV` | 16 | 9 | 16 |  |  |
| `FRJ.ExtractW` | 16 | 9 | 16 |  |  |
| `FRJ.Fallible` | 69 | 34 | 69 |  |  |
| `FRJ.Gbu` | 1106 | 566 | 1106 |  |  |
| `FRJ.Minimal` | 81 | 36 | 81 |  |  |
| `FRJ.Model` | 21 | 7 | 21 |  |  |
| `FRJ.RefAt` | 65 | 27 | 65 |  |  |
| `FRJ.Saturate` | 227 | 92 | 227 |  |  |
| `FRJ.Search` | 132 | 17 | 132 |  |  |
| `FRJ.Sound` | 38 | 38 | 38 |  |  |
| `FRJ.SoundV` | 14 | 14 | 14 |  |  |
| `FRJ.SoundW` | 15 | 15 | 15 |  |  |
| `FRJ.Step` | 223 | 58 | 223 |  |  |
| `FRJ.StepV` | 110 | 17 | 110 |  |  |
| `FRJ.StepW` | 183 | 39 | 183 |  |  |
| `LaxBlueprint` | 10 | 0 | 10 |  |  |
| `LaxLogic.Belief.BooleanIso` | 6 | 4 | 6 |  |  |
| `LaxLogic.Belief.Collapse` | 5 | 4 | 5 |  |  |
| `LaxLogic.Belief.Examples` | 9 | 8 | 7 |  | 2 |
| `LaxLogic.Belief.Falsum` | 4 | 2 | 4 |  |  |
| `LaxLogic.Belief.Idealisation` | 4 | 4 | 4 |  |  |
| `LaxLogic.Belief.Normality` | 2 | 2 | 2 |  |  |
| `LaxLogic.Belief.NucleusJoin` | 6 | 5 | 6 |  |  |
| `LaxLogic.Belief.OpenClosed` | 5 | 4 | 5 |  |  |
| `LaxLogic.Belief.Realisability` | 153 | 73 | 153 |  |  |
| `LaxLogic.ClosedFragmentLattice` | 18 | 5 | 18 |  |  |
| `LaxLogic.CubeEmbedding` | 8 | 7 | 8 |  |  |
| `LaxLogic.Deriv` | 15 | 14 | 15 |  |  |
| `LaxLogic.Focusing.IPCFocused` | 276 | 95 | 276 |  |  |
| `LaxLogic.Focusing.LJF` | 527 | 255 | 527 |  |  |
| `LaxLogic.Focusing.LJFComplete` | 45 | 27 | 45 |  |  |
| `LaxLogic.Interd` | 9 | 8 | 9 |  |  |
| `LaxLogic.Obligation.Adder` | 21 | 16 | 21 |  |  |
| `LaxLogic.Obligation.BeliefLink` | 5 | 5 | 5 |  |  |
| `LaxLogic.Obligation.Budget` | 12 | 9 | 12 |  |  |
| `LaxLogic.Obligation.Connectives` | 28 | 16 | 28 |  |  |
| `LaxLogic.Obligation.Conservativity` | 2 | 0 | 2 |  |  |
| `LaxLogic.Obligation.Examples` | 12 | 7 | 10 | 2 |  |
| `LaxLogic.Obligation.Latch` | 19 | 8 | 19 |  |  |
| `LaxLogic.Obligation.LatchSynth` | 7 | 5 | 7 |  |  |
| `LaxLogic.Obligation.Ledger` | 38 | 6 | 38 |  |  |
| `LaxLogic.Obligation.Mendler` | 9 | 8 | 9 |  |  |
| `LaxLogic.Obligation.Modality` | 43 | 28 | 43 |  |  |
| `LaxLogic.Obligation.Modular` | 19 | 13 | 19 |  |  |
| `LaxLogic.Obligation.PLLBridge` | 11 | 8 | 11 |  |  |
| `LaxLogic.Obligation.Postpone` | 9 | 0 | 9 |  |  |
| `LaxLogic.Obligation.Solve` | 9 | 3 | 9 |  |  |
| `LaxLogic.Obligation.StdCtxBridge` | 12 | 8 | 12 |  |  |
| `LaxLogic.Obligation.Tactics` | 5 | 0 | 5 |  |  |
| `LaxLogic.Obligation.Timing` | 6 | 5 | 6 |  |  |
| `LaxLogic.PLL.G4` | 567 | 252 | 567 |  |  |
| `LaxLogic.PLL.ND` | 546 | 211 | 546 |  |  |
| `LaxLogic.PLL.Normalisation` | 386 | 162 | 386 |  |  |
| `LaxLogic.PLL.Realisability` | 111 | 40 | 111 |  |  |
| `LaxLogic.PLL.Search` | 388 | 70 | 388 |  |  |
| `LaxLogic.PLL.SemUI` | 716 | 428 | 711 | 5 |  |
| `LaxLogic.PLL.Semantics` | 576 | 324 | 576 |  |  |
| `LaxLogic.PLL.Sequent` | 245 | 95 | 245 |  |  |
| `LaxLogic.PLL.Syntax` | 391 | 141 | 391 |  |  |
| `LaxLogic.PLL.Timing` | 130 | 42 | 130 |  |  |
| `LaxLogic.PLL.UI` | 289 | 196 | 289 |  |  |
| `LaxLogic.PLLInstanceBound` | 27 | 9 | 27 |  |  |
| `LaxLogic.PLLSubformulaSet` | 10 | 3 | 10 |  |  |
| `LaxLogic.QLL.Abstract` | 21 | 18 | 21 |  |  |
| `LaxLogic.QLL.BodyCirc` | 73 | 41 | 73 |  |  |
| `LaxLogic.QLL.Bridge` | 58 | 14 | 58 |  |  |
| `LaxLogic.QLL.CLP` | 20 | 14 | 20 |  |  |
| `LaxLogic.QLL.CLPAbstract` | 159 | 60 | 159 |  |  |
| `LaxLogic.QLL.CLPBench` | 5 | 0 | 5 |  |  |
| `LaxLogic.QLL.CLPCertify` | 6 | 0 | 6 |  |  |
| `LaxLogic.QLL.CLPCore` | 88 | 27 | 88 |  |  |
| `LaxLogic.QLL.CLPEngine` | 91 | 22 | 91 |  |  |
| `LaxLogic.QLL.CLPExamples` | 56 | 22 | 56 |  |  |
| `LaxLogic.QLL.CLPMachine` | 377 | 98 | 377 |  |  |
| `LaxLogic.QLL.CLPOper` | 70 | 23 | 70 |  |  |
| `LaxLogic.QLL.Certify` | 13 | 9 | 13 |  |  |
| `LaxLogic.QLL.CertifyTests` | 1 | 0 | 1 |  |  |
| `LaxLogic.QLL.Complete` | 94 | 64 | 94 |  |  |
| `LaxLogic.QLL.Complete1` | 45 | 27 | 45 |  |  |
| `LaxLogic.QLL.CompleteTests` | 21 | 11 | 21 |  |  |
| `LaxLogic.QLL.Countable` | 21 | 15 | 21 |  |  |
| `LaxLogic.QLL.Denote` | 31 | 9 | 31 |  |  |
| `LaxLogic.QLL.DenoteTests` | 15 | 11 | 15 |  |  |
| `LaxLogic.QLL.Deriv` | 131 | 65 | 131 |  |  |
| `LaxLogic.QLL.HeadFlatten` | 12 | 6 | 12 |  |  |
| `LaxLogic.QLL.Herbrand` | 90 | 49 | 90 |  |  |
| `LaxLogic.QLL.HerbrandCLP` | 67 | 37 | 67 |  |  |
| `LaxLogic.QLL.HerbrandFix` | 16 | 14 | 16 |  |  |
| `LaxLogic.QLL.HerbrandLLP` | 42 | 30 | 42 |  |  |
| `LaxLogic.QLL.Horn` | 111 | 44 | 111 |  |  |
| `LaxLogic.QLL.Interp` | 26 | 5 | 26 |  |  |
| `LaxLogic.QLL.InterpTests` | 4 | 0 | 4 |  |  |
| `LaxLogic.QLL.Judgement` | 41 | 0 | 41 |  |  |
| `LaxLogic.QLL.Kit` | 76 | 37 | 76 |  |  |
| `LaxLogic.QLL.Kripke` | 78 | 40 | 78 |  |  |
| `LaxLogic.QLL.LLP` | 67 | 11 | 67 |  |  |
| `LaxLogic.QLL.Lc` | 45 | 35 | 45 |  |  |
| `LaxLogic.QLL.LinQ` | 165 | 39 | 165 |  |  |
| `LaxLogic.QLL.ModalRelation` | 27 | 6 | 27 |  |  |
| `LaxLogic.QLL.Notation` | 34 | 0 | 34 |  |  |
| `LaxLogic.QLL.PaperSemantics` | 41 | 18 | 41 |  |  |
| `LaxLogic.QLL.Prov` | 49 | 7 | 49 |  |  |
| `LaxLogic.QLL.ProvFresh` | 6 | 6 | 6 |  |  |
| `LaxLogic.QLL.RefineIncomplete` | 2 | 2 | 2 |  |  |
| `LaxLogic.QLL.Rename` | 61 | 53 | 61 |  |  |
| `LaxLogic.QLL.Saturate` | 62 | 44 | 62 |  |  |
| `LaxLogic.QLL.Size` | 3 | 2 | 3 |  |  |
| `LaxLogic.QLL.Smoke` | 4 | 0 | 4 |  |  |
| `LaxLogic.QLL.Sound` | 47 | 36 | 47 |  |  |
| `LaxLogic.QLL.SoundTests` | 11 | 5 | 11 |  |  |
| `LaxLogic.QLL.Surface` | 288 | 82 | 288 |  |  |
| `LaxLogic.QLL.Syntax` | 285 | 95 | 285 |  |  |
| `LaxLogic.QLL.Weaken` | 13 | 9 | 13 |  |  |
| `LaxLogic.RN.Reps` | 18 | 1 | 18 |  |  |
| `LaxLogic.RN.Rho` | 8 | 0 | 8 |  |  |
| `LaxLogic.ToolkitTest.Challenge` | 4 | 4 | 0 | 4 |  |
| `LaxLogic.ToolkitTest.NewClaims` | 5 | 5 | 5 |  |  |
| `LaxLogic.ToolkitTest.Punched` | 169 | 63 | 169 |  |  |
| `LaxLogic.ToolkitTest.Solved` | 328 | 123 | 328 |  |  |
| `LaxLogic.Util.Connectives` | 38 | 3 | 38 |  |  |
| `LaxLogic.Util.FormattingUtils` | 3 | 0 | 3 |  |  |
| `LaxLogic.Util.GuardMsgsShow` | 1 | 0 | 1 |  |  |
| `LaxLogic.Util.KleeneBrouwer` | 7 | 4 | 7 |  |  |
| `LaxLogic.Util.Turnstile` | 122 | 8 | 122 |  |  |
| `LaxLogic.Util.TurnstileTests` | 1 | 1 | 1 |  |  |
| `LaxPaper` | 10 | 0 | 10 |  |  |
| `Meta` | 31 | 7 | 31 |  |  |
| `tools` | 249 | 33 | 249 |  |  |
| `wip.G4conf` | 51 | 7 | 49 | 2 |  |
| `wip.ascRefute` | 25 | 10 | 25 |  |  |
| `wip.atomForce` | 6 | 6 | 6 |  |  |
| `wip.bandM` | 13 | 11 | 13 |  |  |
| `wip.bandRefute` | 5 | 5 | 5 |  |  |
| `wip.bandStabilise` | 12 | 6 | 12 |  |  |
| `wip.bandW` | 8 | 7 | 8 |  |  |
| `wip.boxSnd` | 37 | 31 | 37 |  |  |
| `wip.boxSndTight` | 12 | 11 | 12 |  |  |
| `wip.boxTop` | 5 | 5 | 5 |  |  |
| `wip.boxedBranchS1` | 13 | 3 | 13 |  |  |
| `wip.boxedOnPath` | 8 | 2 | 8 |  |  |
| `wip.boxedS1b` | 14 | 7 | 14 |  |  |
| `wip.boxq11` | 14 | 13 | 14 |  |  |
| `wip.branchdia` | 60 | 48 | 60 |  |  |
| `wip.canonFinC` | 32 | 22 | 32 |  |  |
| `wip.cascadeBox` | 13 | 9 | 8 | 5 |  |
| `wip.chainOff` | 9 | 7 | 9 |  |  |
| `wip.chainStrict` | 9 | 8 | 9 |  |  |
| `wip.classical` | 73 | 38 | 73 |  |  |
| `wip.collapse` | 36 | 29 | 36 |  |  |
| `wip.confl_core` | 20 | 0 | 20 |  |  |
| `wip.connect` | 14 | 14 | 14 |  |  |
| `wip.coverfail` | 52 | 44 | 52 |  |  |
| `wip.crankC` | 6 | 5 | 6 |  |  |
| `wip.depth` | 50 | 48 | 50 |  |  |
| `wip.depth2` | 90 | 52 | 90 |  |  |
| `wip.depth3` | 49 | 33 | 49 |  |  |
| `wip.descent2` | 35 | 20 | 35 |  |  |
| `wip.embedNeg` | 21 | 14 | 21 |  |  |
| `wip.envDesc` | 12 | 11 | 12 |  |  |
| `wip.families` | 42 | 40 | 42 |  |  |
| `wip.fiveWorld` | 20 | 20 | 20 |  |  |
| `wip.floor` | 18 | 17 | 18 |  |  |
| `wip.floorGoals` | 7 | 3 | 7 |  |  |
| `wip.floorImp` | 7 | 2 | 7 |  |  |
| `wip.floorRefute` | 16 | 10 | 16 |  |  |
| `wip.freshAnt` | 10 | 4 | 10 |  |  |
| `wip.g4confGap` | 13 | 7 | 13 |  |  |
| `wip.gap2` | 24 | 23 | 24 |  |  |
| `wip.gapWidth` | 14 | 13 | 14 |  |  |
| `wip.gbu_search_circ` | 46 | 19 | 46 |  |  |
| `wip.gbu_weakening` | 10 | 8 | 10 |  |  |
| `wip.goalDesc` | 14 | 13 | 14 |  |  |
| `wip.guardstretch` | 42 | 32 | 42 |  |  |
| `wip.gzSchema` | 5 | 5 | 5 |  |  |
| `wip.hunts` | 17 | 16 | 17 |  |  |
| `wip.jumpPinned` | 12 | 4 | 12 |  |  |
| `wip.ladder8` | 19 | 14 | 19 |  |  |
| `wip.ladderdistr` | 5 | 3 | 5 |  |  |
| `wip.laxNeg` | 12 | 11 | 12 |  |  |
| `wip.linear` | 87 | 48 | 87 |  |  |
| `wip.mforth_probe` | 12 | 0 | 12 |  |  |
| `wip.mixedfail` | 45 | 38 | 45 |  |  |
| `wip.mwit_complete` | 94 | 10 | 94 |  |  |
| `wip.negFour` | 7 | 4 | 7 |  |  |
| `wip.negFourDistinct` | 15 | 10 | 15 |  |  |
| `wip.nfcorrect` | 18 | 17 | 18 |  |  |
| `wip.offImage` | 10 | 10 | 10 |  |  |
| `wip.omegaFix` | 1 | 0 | 1 |  |  |
| `wip.oracle2` | 64 | 8 | 64 |  |  |
| `wip.overlap` | 21 | 19 | 21 |  |  |
| `wip.paramfork` | 159 | 123 | 159 |  |  |
| `wip.phispade` | 108 | 68 | 108 |  |  |
| `wip.phistar` | 50 | 38 | 50 |  |  |
| `wip.pinnedFacts` | 15 | 2 | 15 |  |  |
| `wip.polarity` | 4 | 3 | 4 |  |  |
| `wip.postui` | 127 | 107 | 127 |  |  |
| `wip.rankGapPoint` | 19 | 16 | 19 |  |  |
| `wip.rankedM` | 12 | 9 | 12 |  |  |
| `wip.rankedResidue` | 3 | 2 | 3 |  |  |
| `wip.rbar` | 1 | 1 | 1 |  |  |
| `wip.residueGrowth` | 14 | 10 | 14 |  |  |
| `wip.rnClass` | 42 | 13 | 42 |  |  |
| `wip.rnClassify` | 31 | 28 | 31 |  |  |
| `wip.rnDict` | 238 | 236 | 238 |  |  |
| `wip.rnDict2` | 156 | 144 | 93 | 63 |  |
| `wip.rnDict2Hand` | 77 | 77 | 77 |  |  |
| `wip.rnDictBase` | 17 | 17 | 17 |  |  |
| `wip.rnDictRefute` | 4 | 4 | 4 |  |  |
| `wip.rnDictRefute2` | 58 | 58 | 58 |  |  |
| `wip.rnEmbed` | 91 | 67 | 91 |  |  |
| `wip.rnSep` | 169 | 165 | 169 |  |  |
| `wip.rnSepColl` | 18 | 16 | 18 |  |  |
| `wip.rnSpawnColl` | 8 | 8 | 8 |  |  |
| `wip.rncCells` | 347 | 346 | 347 |  |  |
| `wip.rncCert` | 207 | 207 | 207 |  |  |
| `wip.rncCertPos` | 35 | 24 | 35 |  |  |
| `wip.rnc_probe` | 90 | 9 | 90 |  |  |
| `wip.rungPinned` | 27 | 14 | 27 |  |  |
| `wip.rungbound` | 13 | 11 | 13 |  |  |
| `wip.samval_probe` | 19 | 0 | 19 |  |  |
| `wip.schemeext` | 68 | 60 | 68 |  |  |
| `wip.sealRefute` | 23 | 12 | 23 |  |  |
| `wip.secondgen` | 7 | 6 | 7 |  |  |
| `wip.seeds` | 14 | 13 | 14 |  |  |
| `wip.semSpecW` | 6 | 4 | 6 |  |  |
| `wip.semui_ctx_core` | 41 | 4 | 41 |  |  |
| `wip.stabilise` | 42 | 19 | 42 |  |  |
| `wip.starve` | 11 | 11 | 11 |  |  |
| `wip.toweratoms` | 6 | 5 | 6 |  |  |
| `wip.towercircle` | 8 | 8 | 8 |  |  |
| `wip.towerkit` | 40 | 4 | 40 |  |  |
| `wip.towerpin` | 19 | 19 | 19 |  |  |
| `wip.twogenStmt` | 4 | 1 | 4 |  |  |
| `wip.uiObstruct` | 15 | 12 | 15 |  |  |
| `wip.witOut` | 28 | 15 | 28 |  |  |
| `wip.witTripleC` | 51 | 27 | 51 |  |  |
| `wip.witness` | 16 | 14 | 16 |  |  |
| `wip.wlanding` | 19 | 17 | 19 |  |  |

## Axiom census

Every distinct axiom set in the estate, most common first.

| axioms | declarations |
|---|--:|
| *(none — axiom-free)* | 8370 |
| `propext` | 3699 |
| `propext`, `Quot.sound` | 3300 |
| `propext`, `Classical.choice`, `Quot.sound` | 1991 |
| `sorryAx` | 66 |
| `propext`, `sorryAx`, `Classical.choice`, `Quot.sound` | 9 |
| `propext`, `sorryAx`, `Quot.sound` | 6 |
| `propext`, `Classical.choice` | 4 |
| `Classical.choice` | 2 |
| `propext`, `Classical.choice`, `Quot.sound`, `BeliefLax.boolean22_card._native.native_decide.ax_1_1` | 1 |
| `propext`, `Classical.choice`, `Quot.sound`, `BeliefLax.chain4_card._native.native_decide.ax_1_1` | 1 |

## OPEN: every declaration carrying `sorryAx`

| declaration | module |
|---|---|
| `LaxLogic.Obligation.Examples.downstream` | `LaxLogic.Obligation.Examples` |
| `LaxLogic.Obligation.Examples.sorried` | `LaxLogic.Obligation.Examples` |
| `PLLND.SemUI.layered_of_frag_agree_W` | `LaxLogic.PLL.SemUI.SemUIChar` |
| `PLLND.SemUI.amalgamation_assembled` | `LaxLogic.PLL.SemUI.SemUIHenkin` |
| `PLLND.SemUI.wit_force` | `LaxLogic.PLL.SemUI.SemUIHenkin` |
| `PLLND.SemUI.wit_pbisim` | `LaxLogic.PLL.SemUI.SemUIHenkin` |
| `PLLND.SemUI.amalgamation` | `LaxLogic.PLL.SemUI.SemUILayered` |
| `PLLND.conservativity_IPL` | `LaxLogic.ToolkitTest.Challenge.conservativity_IPL` |
| `PLLND.isIPL_erase` | `LaxLogic.ToolkitTest.Challenge.isIPL_erase` |
| `LJFIPC.map_unNeg_negOf` | `LaxLogic.ToolkitTest.Challenge.map_unNeg_negOf` |
| `LJFIPC.pfreeCtx` | `LaxLogic.ToolkitTest.Challenge.pfreeCtx` |
| `PLLND.G4Conf.G4cf_distF` | `wip.G4conf` |
| `PLLND.G4Conf.G4cf_of_G4c` | `wip.G4conf` |
| `PLLND.ambGuardAscent_open` | `wip.cascadeBox` |
| `PLLND.cascade_box_unconditional` | `wip.cascadeBox` |
| `PLLND.gammaPairFloorA_open` | `wip.cascadeBox` |
| `PLLND.gammaPairFloorBox_open` | `wip.cascadeBox` |
| `PLLND.jumpPairFloor_open` | `wip.cascadeBox` |
| `PLLND.SemUI.RND2.and2_ok` | `wip.rnDict2` |
| `PLLND.SemUI.RND2.box2_ok` | `wip.rnDict2` |
| `PLLND.SemUI.RND2.cAnd_10_13` | `wip.rnDict2` |
| `PLLND.SemUI.RND2.cAnd_11_13` | `wip.rnDict2` |
| `PLLND.SemUI.RND2.cAnd_13_14` | `wip.rnDict2` |
| `PLLND.SemUI.RND2.cAnd_8_11` | `wip.rnDict2` |
| `PLLND.SemUI.RND2.cAnd_8_12` | `wip.rnDict2` |
| `PLLND.SemUI.RND2.cAnd_8_14` | `wip.rnDict2` |
| `PLLND.SemUI.RND2.cBox_11` | `wip.rnDict2` |
| `PLLND.SemUI.RND2.cBox_15` | `wip.rnDict2` |
| `PLLND.SemUI.RND2.cImp_10_13` | `wip.rnDict2` |
| `PLLND.SemUI.RND2.cImp_10_4` | `wip.rnDict2` |
| `PLLND.SemUI.RND2.cImp_10_7` | `wip.rnDict2` |
| `PLLND.SemUI.RND2.cImp_11_13` | `wip.rnDict2` |
| `PLLND.SemUI.RND2.cImp_11_7` | `wip.rnDict2` |
| `PLLND.SemUI.RND2.cImp_12_11` | `wip.rnDict2` |
| `PLLND.SemUI.RND2.cImp_12_7` | `wip.rnDict2` |
| `PLLND.SemUI.RND2.cImp_12_9` | `wip.rnDict2` |
| `PLLND.SemUI.RND2.cImp_13_11` | `wip.rnDict2` |
| `PLLND.SemUI.RND2.cImp_13_12` | `wip.rnDict2` |
| `PLLND.SemUI.RND2.cImp_13_14` | `wip.rnDict2` |
| `PLLND.SemUI.RND2.cImp_13_5` | `wip.rnDict2` |
| `PLLND.SemUI.RND2.cImp_13_9` | `wip.rnDict2` |
| `PLLND.SemUI.RND2.cImp_14_11` | `wip.rnDict2` |
| `PLLND.SemUI.RND2.cImp_14_12` | `wip.rnDict2` |
| `PLLND.SemUI.RND2.cImp_14_13` | `wip.rnDict2` |
| `PLLND.SemUI.RND2.cImp_14_7` | `wip.rnDict2` |
| `PLLND.SemUI.RND2.cImp_14_9` | `wip.rnDict2` |
| `PLLND.SemUI.RND2.cImp_15_12` | `wip.rnDict2` |
| `PLLND.SemUI.RND2.cImp_15_14` | `wip.rnDict2` |
| `PLLND.SemUI.RND2.cImp_15_4` | `wip.rnDict2` |
| `PLLND.SemUI.RND2.cImp_15_5` | `wip.rnDict2` |
| `PLLND.SemUI.RND2.cImp_15_7` | `wip.rnDict2` |
| `PLLND.SemUI.RND2.cImp_15_9` | `wip.rnDict2` |
| `PLLND.SemUI.RND2.cImp_8_11` | `wip.rnDict2` |
| `PLLND.SemUI.RND2.cImp_8_12` | `wip.rnDict2` |
| `PLLND.SemUI.RND2.cImp_8_14` | `wip.rnDict2` |
| `PLLND.SemUI.RND2.cImp_8_4` | `wip.rnDict2` |
| `PLLND.SemUI.RND2.cImp_8_5` | `wip.rnDict2` |
| `PLLND.SemUI.RND2.cImp_8_7` | `wip.rnDict2` |
| `PLLND.SemUI.RND2.cImp_8_9` | `wip.rnDict2` |
| `PLLND.SemUI.RND2.cOr_10_12` | `wip.rnDict2` |
| `PLLND.SemUI.RND2.cOr_10_13` | `wip.rnDict2` |
| `PLLND.SemUI.RND2.cOr_10_14` | `wip.rnDict2` |
| `PLLND.SemUI.RND2.cOr_11_12` | `wip.rnDict2` |
| `PLLND.SemUI.RND2.cOr_11_13` | `wip.rnDict2` |
| `PLLND.SemUI.RND2.cOr_11_14` | `wip.rnDict2` |
| `PLLND.SemUI.RND2.cOr_12_15` | `wip.rnDict2` |
| `PLLND.SemUI.RND2.cOr_13_14` | `wip.rnDict2` |
| `PLLND.SemUI.RND2.cOr_14_15` | `wip.rnDict2` |
| `PLLND.SemUI.RND2.cOr_5_15` | `wip.rnDict2` |
| `PLLND.SemUI.RND2.cOr_5_8` | `wip.rnDict2` |
| `PLLND.SemUI.RND2.cOr_6_15` | `wip.rnDict2` |
| `PLLND.SemUI.RND2.cOr_7_15` | `wip.rnDict2` |
| `PLLND.SemUI.RND2.cOr_8_10` | `wip.rnDict2` |
| `PLLND.SemUI.RND2.cOr_8_11` | `wip.rnDict2` |
| `PLLND.SemUI.RND2.cOr_8_12` | `wip.rnDict2` |
| `PLLND.SemUI.RND2.cOr_8_14` | `wip.rnDict2` |
| `PLLND.SemUI.RND2.cOr_8_9` | `wip.rnDict2` |
| `PLLND.SemUI.RND2.cOr_9_15` | `wip.rnDict2` |
| `PLLND.SemUI.RND2.imp2_ok` | `wip.rnDict2` |
| `PLLND.SemUI.RND2.or2_ok` | `wip.rnDict2` |
| `PLLND.SemUI.rnDict16` | `wip.rnDict2` |

## `native_decide`-tainted declarations

These are checked by the compiler, not the kernel; they may not be cited as PROVED.

| declaration | module |
|---|---|
| `BeliefLax.boolean22_card` | `LaxLogic.Belief.Examples` |
| `BeliefLax.chain4_card` | `LaxLogic.Belief.Examples` |

