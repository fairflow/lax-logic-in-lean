# The 180 dangling citations, triaged

2026-09-18/19, branch `worktree-agent-a6c1d9d9c54fb5303`, cut from `ledger`
at `d64965c`. `scripts/reconcile-claims.py` reports **180 DANGLING** rows —
the prose names a Lean declaration that is not in the estate. This document
classifies every one of the 180, with evidence, and records the repairs.

Companion documents: `docs/ledger-campaign-2026-09-16.md` (what the ledger is),
`docs/proof-simplification-plan-2026-09-16.md` §"2026-09-18: one import line was
hiding thirty modules" (the precedent), `docs/claim-reconciliation.md` (the
generated report), `docs/claims.tsv` (the raw scan).

## What was repaired, and what the estate gained

**One repair is a build, not a citation, and it is the finding of the day.**
`wip/minmodv.lean`, a module of the **declared estate**
(`docs/ledger-modules.txt:473`, 69 declarations recorded in
`docs/status-ledger.jsonl`), has not compiled since yesterday evening:

```
error: wip/minmodv.lean:585:73: Invalid field `toV`: The environment does not
contain `FRJ.IrrWitOf.toV`, so it is not possible to project the field `toV`
from an expression
```

Commit `249c935` ("FRJ: Saturate ↔ SaturateV, the other 34 — the family
abstracted through its constructors", 2026-09-18 20:42) parameterised the five
witness records, so `FRJ.IrrWit` became a reducible `abbrev` for
`IrrWitOf FRJr`. Dot notation resolves through the abbreviation to the head
constant `IrrWitOf`, and `wip/minmodv.lean:558` declares the projection under
the *old* head, `IrrWit.toV`. The call site at `:585` therefore stopped
resolving. **One token repaired**: `.toV` written as an explicit
`IrrWit.toV (…)`, which changes no declaration name and no statement.

```
$ lake env lean wip/minmodv.lean -o .lake/triage/wip/minmodv.olean
EXIT=0
```

The ledger over the repaired module returns **69 declarations, zero GONE,
zero added, zero changed** against the recorded rows. The module is restored
without moving the record by a line.

**Why no gate saw it.** The ledger reads `.olean` files. The cached
`wip/minmodv.olean` cloned into this worktree was stamped **Sep 16 15:37**, two
days before the rename, so every check was reading a record of a module that no
longer compiles. When the failing build finally ran, Lake deleted the stale
output, and `scripts/check-ledger.sh --built-only` would then have *skipped*
`wip.minmodv` as "not built" rather than reporting its 69 declarations GONE.
This is the 2026-09-18 `LJF.Complete` lesson from the other side: there the
static import sweep would have caught it in seconds, and `scripts/check-imports.py`
now does; **here every import resolves** (2,343 imports, 1,030 modules, clean),
because what broke was a *name*, not an import.

**Four citation repairs**, each a stale module path or a stale name, each
verified by re-running the scan:

| file | was | now | effect |
|---|---|---|---|
| `docs/chain-strictness.md:44` | `PLLKripke.soundness` | `PLLND.soundness` (`LaxLogic/PLL/Semantics/Kripke.lean`) | CONFIRMED |
| `docs/qll-herbrand-horn-plan.md:334` | `Kit.freshFor_notMem` | `LaxLogic.QLL.freshFor_notMem` (`LaxLogic/QLL/Kit.lean`) | CONFIRMED |
| `docs/frj-w3.md:48` | `not_provable_neg_circ_bot` | `FRJ.not_provable_barren_neg_circ_bot` | CONFIRMED |
| `docs/g4p-ladder.md:241` | `PLLG4HCut.selfAbsorb_aux` | `PLLND.G4c.selfAbsorb_aux` + the public `PLLND.G4c.selfAbsorb` | path fixed; the `_aux` name still dangles, because it is `private` (§4c) |

**DANGLING falls 180 → 177**, CONFIRMED rises 1,426 → 1,427, and the four names
that left the bucket are exactly the four repaired. `scripts/claim-scan.py`
gains this document in its `GENERATED` set, for the reason the script already
states: scanning it would read our own report back.

`docs/claims.tsv` and `docs/claim-reconciliation.md` were **deliberately not
regenerated**. The figures above were measured by re-running both scripts to a
scratch path; regenerating the tracked artefacts here would fold this
document's own HANDOFF summary into the corpus and move the numbers it
reports. The regeneration belongs to the campaign's next pass, together with
the ledger `--update`.

**What the estate would gain, if Matthew adopts the modules of §4a.** Seventeen
modules that no target names were built here, all green, and the declarations
they hold were fed through `scripts/ledger.lean`:

| modules | declarations | `sorryAx` | note |
|---|--:|--:|---|
| `Archive/FRJLax-parallel/` — `FRJLax.{Core,Model,Modal,Calculus,Circ,Paper}` | 587 | **0** | archived by decision, `2c18829` |
| `tools.A2Probe` (`lake build a2probe`) | 45 | 0 | an `lean_exe` root; the 2026-09-16 sweep covered libraries only |
| `wip.{absorb_base, sealLedger, round4Comp, round5core, round6core, round7core}` | 103 | 2 | the cascade chain |
| `wip.{ljfo_completeness, frj80_noprov, frjv_run, frjx_run}` | 55 | 1 | |
| total | **790** | 3 | |

Nothing was added to `lakefile.toml` or to `docs/ledger-modules.txt`: what the
estate *is* is Matthew's decision, and §4a below gives the evidence for each.

## The five buckets

| bucket | scan rows | distinct sites | distinct names |
|---|--:|--:|--:|
| **4** outside the estate (4a builds · 4b does not · 4c `private`) | **31** | **27** | **21** |
| **5** genuinely absent, needs a human | 14 | 10 | 10 |
| **3** renamed | 13 | 13 | 13 |
| **2** deleted on purpose | 9 | 8 | 4 |
| **1** not a declaration | 113 | 99 | 76 |
| total | 180 | 157 | 124 |

No bucket is empty. The bucket that matters, 4, is a fifth of the rows, and it
splits three ways, which is the report's main finding: only the first of the
three was anticipated.

### The sixth class the five buckets did not anticipate: `private`

`scripts/ledger.lean`'s `skip?` calls `Name.isInternal`, and Lean mangles a
private declaration to `_private.<module>.0.<name>`, whose first component
starts with `_`. **Every `private` declaration in this repository is therefore
invisible to the ledger**, built or not, and a sentence citing one dangles
however correct it is. Measured directly, in the built environment:

```
wip.absorb_base: 164 constants, 139 dropped by isInternal
  _private.wip.absorb_base.0.PLLND.cascade_main_bf
  _private.wip.absorb_base.0.PLLND.cascade_low_pos_boxfree
  _private.wip.absorb_base.0.PLLND.box_remap
  _private.wip.absorb_base.0.PLLND.box_reguard
```

`FRJ/Gbu/W/Search.lean` shows the same from inside the estate: 25 declarations
recorded for a module whose `totalityW` and `wgKeep` are both `private`. Seven
of the 180 citations are in this class, and *building the module does not fix
them*. Whether `skip?` should keep private declarations under their mangled
names is a change to the record's unit of account, so it is left to Matthew
beside the elaborator-plumbing question already open in
`docs/proof-simplification-plan-2026-09-16.md`.

### On `Archive/FRJLax-parallel/` — checked, and the supersession holds

The six FRJLax citations looked like the `FRJO` hole a third time: a whole
development, **587 declarations (208 theorems), zero `sorryAx`, zero
`native_decide`**, that every check is blind to. Its axiom profile is 290
axiom-free, 285 `[propext]`, 11 `[propext, Quot.sound]` and exactly one
touching `Classical.choice`, which is what its README's "effective and
choice-free from line one" asserts and nothing was verifying. It builds in ten
seconds once the files are given the
module names their own `import` lines assume (`FRJLax.Core`, …); they sit at
`Archive/FRJLax-parallel/`, so `import FRJLax.Core` cannot resolve in place and
no target names them.

It is **not** the `FRJO` hole, and the difference is worth recording. Commit
`2c18829` (Matthew, 2026-08-16) archives the line deliberately: "the definitions
of FRJ changed while this was being built … CANONICAL CONTEXTS supersede this
rule table", with the reassessment in `docs/frjlax-reassessment.md`. The two
documents whose claims dangle (`docs/frjlax-fidelity.md` and
`docs/frjlax-modal-rules.md`) are that archived line's own records, dated
2026-08-16 and branded with its branch. The supersession was checked rather
than assumed, and it holds. What remains for Matthew is only the narrower
question of whether an archived, sorry-free development should be under the
gate at all.


## What is left for a human

1. **Bucket 5, ten names.** Four are plan-table targets whose status column
   reads PROVED as an aim, not a record (`LaxND2`, `conservativity2_IPC2`,
   `rnDictP16`, `BiLaxSC`); three are design names from the halted UI search
   (`QBoundR`, `satE2RD_circFree`, `pll_ui_R_circFree`), and the prose itself
   calls the last two instances of a refuted type; `QD` and `GbuOps` name
   objects whose built counterparts are differently named; and
   `FRJ.V.WCounter.no_irregular_circ_imp_self` is the known FRJW/FRJX collision
   on `frjw-dev`, which is not this branch's to touch. None is a relabelling I
   may make.
2. **`private` and the ledger** (§4c). Seven citations, and the class is much
   larger than seven: the record silently omits every private declaration.
3. **Whether §4a's seventeen modules join the estate.** Two of them hold
   sorry-free theorems the prose calls kernel-checked
   (`LJFO.completeness_of_construction`, `FRJ80.not_CompletenessFRJ`), and
   nothing has been checking either.
4. **`wipshared` is red for a third reason now.** Besides the two recorded in
   `docs/ledger-campaign-2026-09-16.md` (`wip/frjw_gcc.lean:44`,
   `wipx/frjx_screen.lean`'s frozen `#guard_msgs` pins), `wip/minmodv.lean`
   was red until this branch repaired it.

## How to reproduce

```bash
scripts/check-imports.py                 # 2,343 imports, 1,030 modules, clean
python3 scripts/claim-scan.py            # docs/claims.tsv
python3 scripts/reconcile-claims.py      # docs/claim-reconciliation.md
```

A module outside every target is built by name and fed to the ledger directly:

```bash
lake env lean wip/round4Comp.lean -o .lake/build/lib/lean/wip/round4Comp.olean
printf 'wip.round4Comp\n' > mods.txt
lake env lean --run scripts/ledger.lean mods.txt out.jsonl
```

The archived FRJLax development builds only under the module names its own
imports assume, so the oleans go to `FRJLax/`, not to `Archive/`:

```bash
lake env lean Archive/FRJLax-parallel/Core.lean -o .lake/build/lib/lean/FRJLax/Core.olean
```

None of this touched `lakefile.toml`, `docs/ledger-modules.txt` or
`docs/status-ledger.jsonl`: the gate reads a fixed module list, so the triage
oleans are invisible to it, by design.

## The tables

All 180 scan rows are classified. The scan emits one row per verdict word, so
a line carrying two verdict words yields the same citation twice; the tables
list the **157 distinct `(line, name)` sites** those 180 rows cover, and each
table's header gives both counts. `where` is the citing line; `cited name` is
the declaration name the scan extracted. Where a name recurs, the evidence is
given once and later rows read *(as above)*.

### 4a — outside the estate, and it BUILDS



**17 scan rows · 14 distinct sites · 12 distinct names.**

| where | cited name | verdict | evidence |
|---|---|---|---|
| `HANDOFF.md:772` | `BoxDesc` | BUILDS | `wip/round4Comp.lean:101`. No target names it; `lake env lean` exit 0 in 12 s. Ledger over `wip.round4Comp` then reports `PLLND.Round4.BoxDesc`, `def`, sorry-free, `[propext, Quot.sound]`. |
| `HANDOFF.md:772` | `CompProd` | BUILDS | `wip/round7core.lean:69`, behind the chain `absorb_base → sealLedger → round4Comp → round5core → round6core`. All six exit 0. Ledger reports `PLLND.Round7.CompProd`, `def`, sorry-free, `[propext, Quot.sound]`. |
| `TOOLS.md:42` | `wsubB` | BUILDS | `tools/A2Probe.lean:418`. `lake build a2probe` exit 0 (6232 jobs, 10 s) — an `lean_exe` root, which the 2026-09-16 every-library sweep did not cover. Ledger reports `A2Probe.wsubB`, `def`, `[propext]` (45 declarations enter). |
| `TOOLS.md:46` | `sweepMain` | BUILDS | `wip/frjv_run.lean:94` and `wip/frjx_run.lean:144`; both exit 0. Ledger reports `FRJVRun.sweepMain` `[propext, Quot.sound]` and `FRJXRun.sweepMain` `[propext, Classical.choice, Quot.sound]`, both sorry-free. |
| `docs/disproof-handoff.md:1392` | `completeness_of_construction` | BUILDS | `wip/ljfo_completeness.lean:140`; exit 0 in 11 s. Ledger reports `LJFO.completeness_of_construction`, **theorem, sorry-free, `[propext, Quot.sound]`**. (The module's one `sorry` is `LJFO.okS_succs`, a different declaration.) |
| `docs/frjlax-fidelity.md:39` | `Form.size_pos` | BUILDS (archived by decision) | `Archive/FRJLax-parallel/Core.lean:68`. The whole archived development builds: see the FRJLax note below. Ledger reports `FRJLax.Form.size_pos`, theorem, `[propext, Quot.sound]`. |
| `docs/frjlax-fidelity.md:55` | `Model.force_mono` | BUILDS (archived by decision) | `Archive/FRJLax-parallel/Model.lean:133`. Ledger reports `FRJLax.Model.force_mono`, theorem, **axiom-free**. |
| `docs/frjlax-fidelity.md:57` | `Model.valid` | BUILDS (archived by decision) | `Archive/FRJLax-parallel/Model.lean:216`. Ledger reports `FRJLax.Model.valid`, `def`, **axiom-free**. |
| `docs/frjlax-modal-rules.md:31` | `Model.circ_intro` | BUILDS (archived by decision) | `Archive/FRJLax-parallel/Modal.lean:45`. Ledger reports `FRJLax.Model.circ_intro`, theorem, **axiom-free**. |
| `docs/frjlax-modal-rules.md:37` | `Model.not_force_circ` | BUILDS (archived by decision) | `Archive/FRJLax-parallel/Modal.lean:57`. Ledger reports `FRJLax.Model.not_force_circ`, theorem, **axiom-free**. |
| `docs/frjlax-modal-rules.md:123` | `Model.not_force_circ_of_no_promise` | BUILDS (archived by decision) | `Archive/FRJLax-parallel/Modal.lean:95`. Ledger reports `FRJLax.Model.not_force_circ_of_no_promise`, theorem, **axiom-free**. |
| `docs/frjlax-modal-rules.md:149` | `Model.circ_intro` | BUILDS (archived by decision) | *(as above)* |
| `docs/llm-formalisation-case-study.md:629` | `BoxDesc` | BUILDS | *(as above)* |
| `docs/refat-plan.md:27` | `FRJ80.not_CompletenessFRJ` | BUILDS | `wip/frj80_noprov.lean:198`; exit 0 in 12 s. Ledger reports `FRJ80.not_CompletenessFRJ`, **theorem, sorry-free, `[propext, Quot.sound]`** — the prose's "all kernel-checked" is right, and nothing was checking it. |

### 4b — outside the estate, and it does NOT build



**2 scan rows · 2 distinct sites · 2 distinct names.**

| where | cited name | verdict | evidence |
|---|---|---|---|
| `docs/frj-fidelity.md:561` | `FRJ.Gbu.X.saturated_and_liftClosed` | does NOT build | `wipx/frjx_screen.lean:70`. In `wipshared`'s globs, so it is named by a target, and `lake build wipshared` fails on it. First error: `wipx/frjx_screen.lean:75:0: ❌️ Docstring on `#guard_msgs` does not match generated message`. This is the frozen four-arm comparison's pins, as `docs/ledger-campaign-2026-09-16.md` records. |
| `docs/frjx-progress-2026-09-01.md:40` | `not_X14` | does NOT build | `wipa/`, `wipb/`, `wipc/`, `wipd/frjx_screen.lean:194` and `wipx/frjx_screen.lean:197`. The four `wipa…wipd` arms are named by no build target at all (deliberately frozen records); the `wipx` copy fails as above. |

### 4c — IN the estate, builds, and the ledger still cannot see it: `private`



**12 scan rows · 11 distinct sites · 7 distinct names.**

| where | cited name | verdict | evidence |
|---|---|---|---|
| `docs/descent-problem.md:84` | `cascade_main_bf` | builds, `private` | `private theorem`, `wip/absorb_base.lean:929`. The module builds (exit 0, 17 s) but is in no target; and even built, the ledger reports 15 of its 164 constants — `_private.wip.absorb_base.0.PLLND.cascade_main_bf` is one of the 139 `isInternal` names dropped. |
| `docs/frjw-compaction.md:90` | `totalityW` | `private` | `private def totalityW`, `FRJ/Gbu/W/Search.lean:281`. The module IS in the estate — but the ledger records only 25 of its declarations, because `scripts/ledger.lean`'s `skip?` calls `Name.isInternal`, and a private declaration is `_private.<module>.0.<name>`. |
| `docs/frjw-complexity-comparison.md:728` | `totalityW` | `private` | *(as above)* |
| `docs/frjw-recursion-explainer-plan.md:223` | `wgKeep` | `private` | `private theorem wgKeep`, `FRJ/Gbu/Search.lean:174` and `FRJ/Gbu/W/Search.lean:211`. Both modules are in the estate; both declarations are invisible to the ledger for the same reason. |
| `docs/frjw-recursion-explainer-plan.md:723` | `wgKeep` | `private` | *(as above)* |
| `docs/g4p-ladder.md:241` | `PLLG4HCut.selfAbsorb_aux` | REPAIRED path; still `private` | `private theorem selfAbsorb_aux`, `LaxLogic/PLL/G4/G4HCut.lean:864`, namespace `PLLND.G4c` — in the estate, invisible to the ledger. The citation named the pre-reorg flat module; **repaired** to `PLLND.G4c.selfAbsorb_aux`, and the public wrapper `PLLND.G4c.selfAbsorb` added, which does reconcile. |
| `docs/ui-attempts-table.md:72` | `cascade_low_pos_boxfree` | builds, `private` | `private theorem`, `wip/absorb_base.lean:2072`; present in the built environment as `_private.wip.absorb_base.0.PLLND.cascade_low_pos_boxfree`, dropped by `skip?`. |
| `docs/ui-attempts-table.md:72` | `cascade_main_bf` | builds, `private` | *(as above)* |
| `docs/ui-attempts-table.md:123` | `box_remap` | builds, `private` | `private theorem`, `wip/absorb_base.lean:255`; present as `_private.wip.absorb_base.0.PLLND.box_remap`, dropped by `skip?`. |
| `docs/ui-attempts-table.md:123` | `box_reguard` | builds, `private` | `private theorem`, `wip/absorb_base.lean:287`; present as `_private.wip.absorb_base.0.PLLND.box_reguard`, dropped by `skip?`. |
| `docs/ui-endgame.md:272` | `box_reguard` | builds, `private` | *(as above)* |

### 5 — genuinely absent



**14 scan rows · 10 distinct sites · 10 distinct names.**

| where | cited name | verdict | evidence |
|---|---|---|---|
| `LaxBlueprint/Chapters/FRJW.lean:70` | `FRJ.V.WCounter.no_irregular_circ_imp_self` | absent | `wip/frjw_gcc.lean:44:28: Unknown identifier `V.WCounter.no_irregular_circ_imp_self`` in today's `lake build wipshared`. Named in 15 files, defined in none. Already recorded in `docs/ledger-campaign-2026-09-16.md` as the FRJW/FRJX collision; `frjw-dev` is not this branch's to touch. |
| `docs/bilax-plan.md:220` | `BiLaxSC` | absent | No occurrence in any `.lean`; `git log -S` over `*.lean` empty. `BiLax/` holds `Hilbert`, `Labelled`, `Hintikka`, … and no sequent calculus module. A plan name in `docs/bilax-plan.md`. |
| `docs/frjw-compaction.md:69` | `QD` | absent | No occurrence in any `.lean`. `docs/frjw-compaction.md:69` names a `QD` decision and `findNotT QD`; neither is a declaration in the tree. |
| `docs/gbu-adoption-plan.md:140` | `GbuOps` | absent | No occurrence in any `.lean`; `git log -S` over `*.lean` empty. The built instance family is `vOps`/`wOps` (`FRJ/Search/Ops*.lean`). |
| `docs/pll2-plan.md:999` | `LaxND2` | absent | `git log -S LaxND2 --all -- '*.lean'` is empty; the only hits are `docs/pll2-plan.md` itself (`74836b4`). A second-order milestone name in a plan whose status column reads PROVED as a target, not a record. |
| `docs/pll2-plan.md:1001` | `conservativity2_IPC2` | absent | `git log -S conservativity2_IPC2 --all -- '*.lean'` is empty; introduced by `74836b4 docs: PLL2 plan + survey landed`. Same plan table as `LaxND2`. |
| `docs/rn-dictionary-plan.md:342` | `rnDictP16` | absent | `git log -S rnDictP16 --all -- '*.lean'` is empty; introduced by `ba9ae65 docs(RN): plan to rebuild the dictionary and operation tables`. A migration artefact that was never built. |
| `docs/ui-ljfo-clause-table.md:3438` | `satE2RD_circFree` | absent | No occurrence anywhere in the tree. `docs/ui-ljfo-clause-table.md:3438` names it as an *instance of a refuted type* — the sentence says the type is refuted, so the instance was never declared. |
| `docs/ui-ljfo-clause-table.md:3438` | `pll_ui_R_circFree` | absent | No occurrence anywhere in the tree; same sentence and same reason as `satE2RD_circFree`. |
| `docs/ui-routeB-blueprint.md:230` | `QBoundR` | absent | No occurrence in any `.lean` file in the tree, and `git log -S QBoundR --all -- '*.lean'` is empty. A design name from `docs/ui-routeB-blueprint.md` §4.32–4.34 that was never a declaration. |

### 3 — renamed



**13 scan rows · 13 distinct sites · 13 distinct names.**

| where | cited name | verdict | evidence |
|---|---|---|---|
| `HANDOFF.md:3929` | `List.mem_sublists` | renamed (not repaired: HANDOFF) | The three names are mathlib's, replaced by local choice-free copies: `Meta/Portable.lean:19` names them `List.memSublistsP`, `List.sublistsLenP`, `List.memSublistsLenP`, and all three are in the estate. |
| `HANDOFF.md:3929` | `sublistsLen` | renamed (not repaired: HANDOFF) | See `List.mem_sublists`: the local copy is `List.sublistsLenP` (`Meta/Portable.lean:130`). (`A2Probe.sublistsLen` at `tools/A2Probe.lean:63` is an unrelated coincidence of name.) |
| `HANDOFF.md:3929` | `mem_sublistsLen` | renamed (not repaired: HANDOFF) | See `List.mem_sublists`: the local copy is `List.memSublistsLenP` (`Meta/Portable.lean:135`). |
| `HANDOFF.md:4049` | `HerbrandCLP.p66_refuted` | renamed (not repaired: HANDOFF) | File-qualified: `LaxLogic/QLL/HerbrandCLP.lean:514` declares `p66_refuted` in namespace `LaxLogic.QLL`, so the estate name is `LaxLogic.QLL.p66_refuted`, `[propext, Quot.sound]`. In `HANDOFF.md`, which CLAUDE.md says to append to and never rewrite. |
| `docs/chain-strictness.md:44` | `PLLKripke.soundness` | REPAIRED | The pre-reorg flat module `PLLKripke.lean` is now `LaxLogic/PLL/Semantics/Kripke.lean` and the declaration is `PLLND.soundness` (`:102`), in the estate. **Repaired** at `docs/chain-strictness.md:44`; now CONFIRMED. |
| `docs/disproof-handoff.md:261` | `cImp_9_4` | renamed | `Rewrite/Catalogue.lean:19` shows `cImp_9_4 : Interd (q9 ⊃ q4) q0  -- FALSE AS STATED` inside the comment that records the four false candidates. The live declaration is its refutation, `PLLND.SemUI.RND.refute_cImp_9_4`. |
| `docs/frj-w3.md:48` | `not_provable_neg_circ_bot` | REPAIRED | The estate has `FRJ.not_provable_barren_neg_circ_bot`; the short form survives only in the docstring at `FRJ/Fallible.lean:216`, whose surrounding sentence ("the barren calculus of `FRJ/Calculus.lean` cannot reach these formulas") fixes the reading. **Repaired** at `docs/frj-w3.md:48`; now CONFIRMED. The docstring itself was left alone — editing it would force a rebuild of a default-target module for a comment. |
| `docs/ljfo-review-2026-08-11.md:59` | `satE2F` | renamed | The F-side saturation statement is `LJFO.SatE2F` (capitalised) in the estate, consumed by `LJFO.ecofinalF_of_satE2F`. The lower-case lemma name the review used is gone; the reconciler's index is case-sensitive. |
| `docs/ljfo-review-2026-08-11.md:59` | `satA2F` | renamed | As `satE2F`: `LJFO.SatA2F`, consumed by `LJFO.acofinalF_of_satA2F` and `LJFO.cimpAntF_of_satA2F`. |
| `docs/qll-herbrand-horn-plan.md:334` | `Kit.freshFor_notMem` | REPAIRED | File-qualified citation: `LaxLogic/QLL/Kit.lean:58` declares `freshFor_notMem` in namespace `LaxLogic.QLL`, so the estate name is `LaxLogic.QLL.freshFor_notMem`, `[propext, Quot.sound]`. **Repaired** at `docs/qll-herbrand-horn-plan.md:334`; now CONFIRMED. |
| `docs/rho-order.md:334` | `LJFOHeight` | renamed (a file) | The pre-split flat file `LJFOHeight.lean` is now `LJF/OHeight.lean` (`3884eeb feat(engine+db): … LJF split out`). A file citation, not a declaration. |
| `docs/semantic-ui-fresh-prompt.md:23` | `semEx_definable` | renamed | Was a `sorry` in `SemUI.lean` (`ca6971a`, `a33ebb8`, `d078f8f`). Today the estate has `PLLND.SemUI.SemExDefinable` (the statement), `PLLND.SemUI.semEx_definable_of_reconstruction` and `PLLND.SemUI.ofree_semEx_definable`. Three candidates, so no repair: which one the sentence means is a reading, not a mechanical fact. |
| `docs/semantic-ui-fresh-prompt.md:23` | `semAll_definable` | renamed | As `semEx_definable`: `PLLND.SemUI.SemAllDefinable`, `…semAll_definable_of_reconstruction`, `…ofree_semAll_definable`. |

### 2 — deleted on purpose



**9 scan rows · 8 distinct sites · 4 distinct names.**

| where | cited name | verdict | evidence |
|---|---|---|---|
| `HANDOFF.md:747` | `cascade_low_pos_box` | deleted 2026-08-05 | `ea3a755 feat(round4): THE ASSEMBLY LANDED — cascade_low_pos_box (the July holdout), cascade_low_pos and cascade_low DELETED`; `c834353 docs: retarget downstream prose at cascade_boxgoal_pos`. The file says so itself: `wip/absorb_base.lean:2189-2191` ("the old holdout DELETED") and `:2218` ("This replaces `cascade_low_pos_box` above"). The live holdout is `cascade_boxgoal_pos` (`:2269`), and the `private theorem cascade_low_pos_box` at `:2103` is inside the docstring that quotes the retired statement. |
| `docs/away-run-report.md:84` | `cascade_low_pos_box` | deleted 2026-08-05 | *(as above)* |
| `docs/frj-fidelity.md:305` | `exists_min_eta` | deleted | Existed: introduced by `0e9e004 feat(FRJ): Sec.6 groundwork — Lambda*, the closure lemma, height, minimal eta`, last seen in `edecc5b feat(FRJ): the whole library builds — Minimal.lean converted, Type-valued`, which removed it in the Type-valued conversion. |
| `docs/frj-fidelity.md:558` | `not_evalI_Gcc` | retired, kept as comment | `wip/gbu_search_circ.lean:1324-1330`: the statement stands inside a comment block whose own text reads "The statements are kept in the record rather than deleted." Its refutation, `evalI_Gcc`, is the live declaration. |
| `docs/ui-attempts-table.md:72` | `cascade_low_pos_box` | deleted 2026-08-05 | *(as above)* |
| `docs/ui-attempts-table.md:80` | `cascade_low_pos_box` | deleted 2026-08-05 | *(as above)* |
| `docs/ui-ljfo-clause-table.md:1824` | `DykAntP` | WITHDRAWN | `LJF/OFuelPFam.lean:61`: "A second obligation `DykAntP`, for the Dyckhoff shape alone, stood here"; `LaxBlueprint/Chapters/UI.lean:203`: "`DykAntP`, the hypothesis an earlier draft needed, was WITHDRAWN". `docs/ui-ljfo-clause-table.md:1824` is the record of the withdrawal. |
| `docs/ui-routeB-blueprint.md:53` | `DykAntP` | WITHDRAWN | *(as above)* |

### 1 — not a declaration



**113 scan rows · 99 distinct sites · 76 distinct names.**

| where | cited name | verdict | evidence |
|---|---|---|---|
| `HANDOFF.md:239` | `Cl` | notation in a displayed formula | the closure operator `Cl(Γ)`, written throughout the FRJ prose. |
| `HANDOFF.md:760` | `G3iLL` | a calculus, not a declaration | the repository's `SC`/`SCh` (`LaxLogic/PLL/G4/G4ipComplete.lean:62`). |
| `HANDOFF.md:760` | `G4iLL` | a calculus, not a declaration | Iemhoff's G4iLL; in Lean the family is `G4`, `G4h`, `G4c` (`LaxLogic/PLL/G4/`). |
| `HANDOFF.md:991` | `Finset.filter` | a Lean core / Mathlib name; the ledger covers this repository's modules only | Mathlib; the recurring sentence "only `Finset.filter` is clean". |
| `HANDOFF.md:2376` | `Wg` | notation in a displayed formula | the paper's weight, `Wg(τ) = ⟨…⟩` (`FRJ/Gbu/Base.lean:247`); the built measure is `FRJ/Gbu/Measure.lean`. |
| `HANDOFF.md:2532` | `hJ5` | a binder in a rule statement | `(hJ5 : ∀ Y : Form, …)` at `FRJ/Sound.lean:297`, `FRJ/SoundCore.lean:298` and 29 more. |
| `HANDOFF.md:4041` | `ModalRelation` | a Lean file | `LaxLogic/QLL/ModalRelation.lean`. |
| `HANDOFF.md:4116` | `CLPMachine` | a Lean file | `LaxLogic/QLL/CLPMachine.lean`. |
| `LaxBlueprint/Chapters/StrongNorm.lean:89` | `Counterexamples` | a `section` | `section Counterexamples` at `LJF/OFuelHeight.lean:496` and `LaxLogic/PLL/Normalisation/Reducibility.lean:1040`. |
| `METHOD.md:16` | `HANDOFF.md` | a documentation file, not a declaration | `HANDOFF.md` at the repository root. |
| `TOOLS.md:41` | `Core` | a Lean file | `FRJ/Search/Core.lean`, `Rewrite/Core.lean`. |
| `TOOLS.md:42` | `FRJW` | a calculus, not a declaration | the W-family; in Lean the constructors are `FRJWr`/`FRJWi` (`FRJ/CalculusW.lean`). |
| `TOOLS.md:77` | `sorryAx` | a Lean core / Mathlib name; the ledger covers this repository's modules only | Lean's `sorry` axiom; every sentence citing it is about the axiom, not a theorem. |
| `TOOLS.md:77` | `defaultTargets` | a `lakefile.toml` key | `lakefile.toml:4`, quoted at `Audit/Production.lean:10`. |
| `TOOLS.md:92` | `HANDOFF.md` | a documentation file, not a declaration | *(as above)* |
| `TOOLS.md:92` | `METHOD.md` | a documentation file, not a declaration | `METHOD.md` at the repository root. |
| `TOOLS.md:92` | `TOOLS.md` | a documentation file, not a declaration | `TOOLS.md` at the repository root. |
| `docs/belief-mechanisation-index.md:48` | `_em0` | a name SUFFIX, written as shorthand | the sentence reads ``varfree_exactly_four` (+`_em0`)`; the declaration is `varfree_exactly_four_em0`, and it is in the estate. |
| `docs/calculus-map.md:46` | `G4iLL` | a calculus, not a declaration | *(as above)* |
| `docs/cutinv-cases.md:269` | `IsEmpty` | a Lean core / Mathlib name; the ledger covers this repository's modules only | Lean core, paired with `not_nonempty_iff` at `LaxLogic/ToolkitTest/Punched/PLLNDCore.lean:86`. |
| `docs/decider-outputs-design.md:836` | `CLAUDE.md` | a documentation file, not a declaration | `CLAUDE.md` at the repository root. |
| `docs/frj-fidelity.md:370` | `Finset.filter` | a Lean core / Mathlib name; the ledger covers this repository's modules only | *(as above)* |
| `docs/frj-lax-handoff.md:12` | `CLAUDE.md` | a documentation file, not a declaration | *(as above)* |
| `docs/frj-lax-plan.md:284` | `Finset.filter` | a Lean core / Mathlib name; the ledger covers this repository's modules only | *(as above)* |
| `docs/frj-lax-plan.md:360` | `Classical.choice` | a Lean core / Mathlib name; the ledger covers this repository's modules only | Lean's choice axiom. |
| `docs/frj-ljfo-duality.md:168` | `PLLG4Dec` | a Lean file, pre-reorg spelling | no file of that name survives; the decision procedure is `decidablePLL` (`LaxLogic/PLL/Semantics/Countermodel.lean:20`), and `PLLG4Dec.lean` is how the docstrings still spell its old home. |
| `docs/frjo-search-design.md:435` | `Classical.choice` | a Lean core / Mathlib name; the ledger covers this repository's modules only | *(as above)* |
| `docs/frjw-complexity-comparison.md:43` | `Complete` | a Lean file | `FRJ/Complete.lean`, `FRJO/Complete.lean`, `Reject/Complete.lean`. |
| `docs/frjw-complexity-comparison.md:43` | `Minimal` | a Lean file | `FRJ/Minimal.lean`. |
| `docs/frjw-complexity-comparison.md:259` | `Finset.filter` | a Lean core / Mathlib name; the ledger covers this repository's modules only | *(as above)* |
| `docs/frjw-complexity-comparison.md:768` | `Calculus` | a Lean file | `FRJ/Calculus.lean`. |
| `docs/frjw-complexity-comparison.md:768` | `Extract` | a Lean file | `FRJ/Extract.lean`. |
| `docs/frjw-complexity-comparison.md:768` | `Sound` | a Lean file | `FRJ/Sound.lean`. |
| `docs/frjw-complexity-comparison.md:768` | `Complete` | a Lean file | *(as above)* |
| `docs/frjw-complexity-comparison.md:768` | `Minimal` | a Lean file | *(as above)* |
| `docs/frjw-complexity-comparison.md:768` | `Saturate` | a Lean file | `FRJ/Saturate.lean`, `FRJ/Gbu/W/Saturate.lean`. |
| `docs/frjw-complexity-comparison.md:768` | `Modal` | a Lean file | `FRJ/Modal.lean`-line naming in the same file list. |
| `docs/frjw-complexity-comparison.md:768` | `Fallible` | a Lean file | `FRJ/Fallible.lean`. |
| `docs/frjw-complexity-comparison.md:768` | `Erase` | a Lean file | `FRJ/Erase.lean`. |
| `docs/frjw-complexity-comparison.md:768` | `Profile` | a Lean file | `FRJ/Search/Profile.lean`. |
| `docs/frjw-complexity-comparison.md:768` | `Audit` | a Lean file | `FRJ/Audit.lean`, `Meta/Audit.lean`, `Reject/Audit.lean`. |
| `docs/frjw-complexity-comparison.md:768` | `Bridge` | a Lean file | `FRJ/Bridge.lean`. |
| `docs/frjw-complexity-comparison.md:768` | `WitnessKit` | a Lean file | `FRJ/WitnessKit.lean` (`FRJ/WitnessV1215.lean:56`). |
| `docs/frjw-complexity-comparison.md:769` | `CalculusV` | a Lean file | `FRJ/CalculusV.lean`. |
| `docs/frjw-complexity-comparison.md:769` | `CalculusVLemmas` | a Lean file | `FRJ/CalculusVLemmas.lean`. |
| `docs/frjw-complexity-comparison.md:769` | `StepV` | a Lean file | `FRJ/StepV.lean` (`FRJ/StepW.lean:2`). |
| `docs/frjw-complexity-comparison.md:769` | `ExtractV` | a Lean file | `FRJ/ExtractV.lean` (`FRJ/ExtractW.lean:2`). |
| `docs/frjw-complexity-comparison.md:769` | `SoundV` | a Lean file | `FRJ/SoundV.lean`. |
| `docs/frjw-complexity-comparison.md:769` | `SaturateV` | a Lean file | `FRJ/SaturateV.lean`. |
| `docs/frjw-complexity-comparison.md:769` | `CompleteV` | a Lean file | `FRJ/CompleteV.lean`. |
| `docs/frjw-complexity-comparison.md:769` | `CompleteV0` | a Lean file | `FRJ/CompleteV0.lean`. |
| `docs/frjw-complexity-comparison.md:769` | `AuditV` | a Lean file | `FRJ/AuditV.lean`. |
| `docs/frjw-complexity-comparison.md:769` | `BridgeV` | a Lean file | `FRJ/BridgeV.lean`. |
| `docs/frjw-complexity-comparison.md:769` | `CalculusW` | a Lean file | `FRJ/CalculusW.lean`. |
| `docs/frjw-complexity-comparison.md:769` | `gbu_search` | a Lean file | `wip/gbu_search_circ.lean` (and the retired `wip/gbu_search.lean` in `wipshared`'s globs). |
| `docs/frjw-explainer.md:355` | `hJ2` | a binder in a rule statement | `(hJ2 : ∀ A B : Form, …)` at `FRJ/Sound.lean:36`, `FRJ/Calculus.lean:388` and 27 more. |
| `docs/frjw-explainer.md:1644` | `hallK` | a local hypothesis | `hallK | ⟨Y₂, hY₂, hnK⟩` at `FRJ/Gbu/W/Search.lean:430`. |
| `docs/frjw-explainer.md:1767` | `B'` | a metavariable in a rule table | `| `A' ⊃ B'` | …` in the clause table at `docs/frjw-explainer.md:1767`. |
| `docs/frjw-plan.md:385` | `gbu_frjw_dichotomy` | a displayed statement in a docstring | `FRJ/Gbu/W/Dichotomy.lean:32` displays `gbu_frjw_dichotomy : … → ProvableGbuC G ∨ DisprovableW G` as the root corollary; the cited sentence itself says "no declarations". The built declaration is `FRJ.Gbu.W.dichotomyW`. |
| `docs/frjw-recursion-explainer-plan.md:135` | `Acc` | a Lean core / Mathlib name; the ledger covers this repository's modules only | Lean core's accessibility predicate, named in a prose description of a `decreasing_by` proof. |
| `docs/frjw-recursion-explainer-plan.md:286` | `decI` | a binder | `(decI : ∀ Ω C, Decidable (EvalI D Ω C))` at `FRJ/Gbu/Circ.lean:1154` and five more. |
| `docs/frjw-recursion-explainer-plan.md:572` | `heZ` | a local hypothesis | `refine byDec (decI Ψ Z) (fun heZ => ?_) …` at `FRJ/Gbu/W/Search.lean:418`. |
| `docs/frjw-recursion-explainer-plan.md:715` | `fromImp` | a `have` inside a proof | `have fromImp : ∀ Y : Form, …` at `FRJ/Gbu/W/Search.lean:561`. |
| `docs/frjw-recursion-explainer-plan.md:715` | `limpStep` | a `have` inside a proof | `have limpStep : ∀ A B : Form, …` at `FRJ/Gbu/Search.lean:326` and `FRJ/Gbu/W/Search.lean:542`. |
| `docs/gbu-adoption-plan.md:210` | `GJ` | a calculus from the source paper | `FRJ/Gbu/Base.lean:45`: "the paper maps `Gbu(G)`-derivations into `GJ`". |
| `docs/iel-justification-lit.md:126` | `IEL` | a logic from the literature | Artemov–Protopopescu's intuitionistic epistemic logic (`LaxLogic/Belief/Falsum.lean:20`); not mechanised here. |
| `docs/ledger-campaign-2026-09-16.md:99` | `sorryAx` | a Lean core / Mathlib name; the ledger covers this repository's modules only | *(as above)* |
| `docs/ledger-campaign-2026-09-16.md:207` | `TOOLS.md` | a documentation file, not a declaration | *(as above)* |
| `docs/ljfo-plan.md:598` | `cAnt` | a section `variable` | `variable (cAnt : CimpAnt p)` at `LJF/O.lean:920`. |
| `docs/llm-formalisation-case-study.md:554` | `boxSnd` | a Lean file | `wip/boxSnd.lean`. |
| `docs/llm-formalisation-case-study.md:554` | `boxSndTight` | a Lean file | `wip/boxSndTight.lean`. |
| `docs/llm-formalisation-case-study.md:554` | `floorGoals` | a Lean file | `wip/floorGoals.lean`. |
| `docs/llm-formalisation-case-study.md:1413` | `SHARING.md` | a documentation file, not a declaration | `tools/FrontierSampler/SHARING.md`. |
| `docs/llm-formalisation-case-study.md:1414` | `sorryAx` | a Lean core / Mathlib name; the ledger covers this repository's modules only | *(as above)* |
| `docs/pll-formalisation-ledger.md:207` | `G4iLL` | a calculus, not a declaration | *(as above)* |
| `docs/pll-formalisation-ledger.md:297` | `Classical.choice` | a Lean core / Mathlib name; the ledger covers this repository's modules only | *(as above)* |
| `docs/pll2-plan.md:19` | `G4iLL` | a calculus, not a declaration | *(as above)* |
| `docs/pll2-plan.md:1283` | `G4iLL` | a calculus, not a declaration | *(as above)* |
| `docs/proof-simplification-plan-2026-09-16.md:1036` | `sorryAx` | a Lean core / Mathlib name; the ledger covers this repository's modules only | *(as above)* |
| `docs/publication-plan.md:210` | `CLAUDE.md` | a documentation file, not a declaration | *(as above)* |
| `docs/qll-clp-review.md:184` | `CLPBench` | a Lean file | `LaxLogic/QLL/CLPBench.lean`. |
| `docs/searchw-architecture.md:205` | `WSaturated.2` | a projection, not a name | the second component of `WSaturated`; the structure is built, the `.2` is not a declaration. |
| `docs/searchw-architecture.md:254` | `_certs` | a name SUFFIX, written as shorthand | ``refutedCleanly_circ_kept` / `_certs` / `_axI``; `refutedCleanly_circ_certs` is in the estate. |
| `docs/searchw-architecture.md:254` | `_axI` | a name SUFFIX, written as shorthand | same sentence; `refutedCleanly_circ_axI` is in the estate. |
| `docs/semantic-ui-route.md:1024` | `_boxBot` | a name SUFFIX, written as shorthand | ``semEx_value_not_derives_negBoxBot` / `_boxBot``; the full name is `semEx_value_not_derives_boxBot`. |
| `docs/skill-proposal.md:189` | `Finset` | a Lean core / Mathlib name; the ledger covers this repository's modules only | Mathlib; the sentence is about `Finset` carrying choice. |
| `docs/skill-proposal.md:189` | `Finset.filter` | a Lean core / Mathlib name; the ledger covers this repository's modules only | *(as above)* |
| `docs/t1-join-rule-prompt.md:49` | `addTop` | a named design that was never declared | `6d6c498 feat(Reject): … addRoot (the safe constructor: adding a root below preserves forcing above, unlike addTop)`. The built constructor is `addRoot`; `addTop` names the refuted alternative. |
| `docs/transport-problem-brief.md:40` | `cast_cast` | a Lean core / Mathlib name; the ledger covers this repository's modules only | Mathlib's `cast_cast`, named as a coherence condition. |
| `docs/ui-attack.md:82` | `hU` | a local hypothesis | `rintro ⟨U, hRm, hU⟩` at `LaxLogic/PLL/UI/NoFall.lean:455` and 13 more files. |
| `docs/ui-ljfo-clause-table.md:9` | `CLAUDE.md` | a documentation file, not a declaration | *(as above)* |
| `docs/ui-ljfo-clause-table.md:1973` | `sorryAx` | a Lean core / Mathlib name; the ledger covers this repository's modules only | *(as above)* |
| `docs/ui-ljfo-clause-table.md:2372` | `A_f` | a metavariable in a displayed chain | `interpF`'s ascending chain, `LaxBlueprint/Chapters/UI.lean:123`. |
| `docs/ui-routeB-blueprint.md:36` | `A_f` | a metavariable in a displayed chain | *(as above)* |
| `docs/ui-routeB-blueprint.md:55` | `E_f` | a metavariable in a displayed chain | `interpF`'s descending chain, same line. |
| `docs/ui-routeB-blueprint.md:61` | `Nonempty` | a Lean core / Mathlib name; the ledger covers this repository's modules only | Lean core; used as `¬ Nonempty (LaxND Γ C)`, the repository's spelling of underivability. |
| `docs/ui-routeB-blueprint.md:119` | `OFuelPFam` | a Lean file | `LJF/OFuelPFam.lean`, named beside `LJF/OFuelPFamKit.lean` on the cited line. |
| `docs/ui-routeB-blueprint.md:230` | `BindCell` | a `namespace` | `namespace BindCell` at `wip/ui_routeB_r_bindcell.lean:69`. |
| `docs/why-chain.md:64` | `HANDOFF.md` | a documentation file, not a declaration | *(as above)* |


## Verification

`wip/minmodv.lean` is the only file Lean reads that this branch changes.

```
$ gtimeout 5400 lake build
LAKE BUILD EXIT=0
Build completed successfully (8748 jobs).
```

```
$ scripts/check-imports.py
check-imports: 2343 imports in 1030 modules, every one resolves
```

The gate was run twice, because the first run measured more than the change.
`scripts/ledger-run.py` folds in every **built** module it finds, not only the
ones `docs/ledger-modules.txt` names, so the triage builds of §4a entered the
comparison as additions:

```
ledger: 36 built module(s) not in the list, included anyway: …
ledger: 29373 declarations from 639 modules (78 loaded separately)
ledger: 203 addition(s)/improvement(s) — regenerate `docs/status-ledger.jsonl`
  NEW         A2Probe.P  (tools.A2Probe)
  …
  NEW         PLLND.itp_stab  (wip.absorb_base) [sorryAx]
  … and 153 more
gate exit 2
```

**203 additions, and not one REGRESSION line: no SORRY, no AXIOM, no NATIVE,
no GONE.** The 203 are exactly the triage builds (`tools.A2Probe` 45,
`wip.sealLedger` 39, `wip.round6core` 25, `wip.frj80_noprov` 16,
`wip.frjx_run` 16, `wip.absorb_base` 15, `wip.round4Comp` 13, `wip.frjv_run`
13, `wip.ljfo_completeness` 10, `wip.round7core` 6, `wip.round5core` 5).
`PLLND.itp_stab [sorryAx]` is a NEW row that carries a `sorry`, not a
declaration that acquired one: `wip/absorb_base.lean`'s holdout
`cascade_boxgoal_pos` has been there since 2026-08-05. The `FRJLax` oleans do
not appear, because that detection reads source paths and no `FRJLax/` source
directory exists.

The triage oleans were then deleted and the gate re-run, so that it measures
the committed source change and nothing else:

```
$ gtimeout 3600 scripts/check-ledger.sh --built-only
ledger: 29170 declarations from 628 modules (75 loaded separately)
ledger: clean — 29170 declarations, unchanged
gate exit 0
```

**Clean.** The estate is the same 628 modules and 29,170 declarations the
record already holds, with `wip.minmodv` among them again and its 69 rows
identical. A module that had fallen out of the build is back inside the gate,
and the record did not have to move to let it in.
