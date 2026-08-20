# Notes for developers

`README.md` is the reader's guided tour of what is finished. This file is the
other half: what is on the branch but outside the core, why, and what to do when
a parked campaign finishes. Nothing here is needed to read, build or check the
mathematics.

---

## 1. The gate

The criterion is **per campaign, not per file**. A module is admitted to `Core`
iff:

1. its campaign's terminal result is PROVED, or is a completed REFUTATION (as
   `PLLG4Gap` is), stated as a named theorem;
2. it is sorry-free — verified by the build emitting no `declaration uses
   'sorry'`, never by grep;
3. its headline theorems are `#guard_msgs`-pinned with axioms a subset of
   `[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no
   `Lean.ofReduceBool` (so no `native_decide`);
4. its transitive import closure touches no `wip.*` module and no trimmed
   module;
5. it carries a module docstring saying what it contains, which calculus it
   belongs to, what is PROVED, and whose the result is.

Criterion 3 is per *theorem*, discharged in `Core/Audit.lean` rather than by
requiring a pin in every file.

## 2. The standing rule, which overrides a naive reading of the gate

> **Do not make it harder to add material completed in the future.** (Matthew,
> 2026-08-20.)

A finished result is excluded **only** when its own import closure is
unfinished — never because the campaign around it stalled. Campaigns that miss
their goal still prove real theorems en route, and a campaign-shaped gate
silently discards them.

When the closure is unfinished *solely* through a shared definition stranded in
a parked file, **hoist the definition** into the core rather than exclude the
result. Two hoists were needed, and both were pure code motion:

| new file | moved out of | what it rescued |
|---|---|---|
| `LaxLogic/Bisim.lean` | `LaxLogic/PLLSemUI.lean` | `ABisim`, `force_iff_of_bisim`, `ABisim.id`, `PBisim` — four `Reject/` modules |
| `LaxLogic/Deriv.lean` | `LaxLogic/PLLSemUIFrag.lean` | `Deriv Γ φ := Nonempty (LaxND Γ φ)` and 14 rule wrappers — uniform interpolation for IPC |

Keep the original namespace on a hoist (`Deriv.lean` stays in `PLLND.SemUI`)
when renaming would ripple through `wip/`.

**Measure the closure before asserting coupling.** Compute which modules a
candidate actually adds and whether any carries a `sorry`; do not estimate from
directory size. I once claimed "~10k lines of shared machinery" for two results
that needed two clean modules and one hoist.

## 3. What is on the branch but outside `Core`

Everything in this table still builds — `lake build LaxLogic`, and each other
library by name — and nothing has been deleted from history or from the working
branches.

| out | modules | why |
|---|---|---|
| `PLLSemUI*` | 15 | semantic UI after Litak–Visser; carries the only `sorry`s on the branch |
| `PLLG4UI*`, `PLLG4Tower` | 5 | UI through the `G4c` tower; `PLLG4Tower` states its own open question |
| `PLLG4PInv`, `PLLG4PAdm`, `PLLG4PStr` | 3 | dead metatheory branch of the first repair, imported by nothing |
| the polarised programme | 8 | `IPCFocused`, `PLLFocused`, `PLLPolar`, `PLLJudgmental`, `PLLCand*`, `PLLUIChains` — step one of the polarised route to UI |
| `LaxLogic.LJFO` and its tail | 7 | the minimality tail: `LJFOAudit`, `LJFOFuel`, `LJFOHeight`, `LJFORows`, `LJFOSearch`, `LJFOUniverse`. **Sorry-free**, but `LJFO.lean` carries `CimpAnt`, an undischarged obligation on which E2/A2 are conditional |
| `BiLax/` | 11 | calculus, soundness and refutation pipeline proved; the duality bridge never attempted |
| `PLLExec` | 1 | imports `PLLG4UITrunc`, so it drags the UI tower in |
| `BeliefExamplesNative` | 1 | two `native_decide` enumerations, split out so the remaining six examples pin clean |

`LJF`, `LJFComplete`, `LJFOCore` and `LJFOBridge` **are** in the core:
focalization for PLL and uniform interpolation for IPC are finished. This is why
`scripts/core-audit.py` needs an exact-name `TRIMMED_MODULES` set beside
`TRIMMED_PREFIXES` — a `LaxLogic.LJFO` prefix would catch both halves of the
family.

### Removed from this branch entirely (2026-08-20)

The working record is no longer distributed. All of it remains on the
development branches and in history; nothing is lost.

| removed | size | note |
|---|---|---|
| `wip/` | 333 modules, ~130k lines | probes, screens and certificate banks — never results |
| ~95 probe `lean_exe` targets | — | every executable rooted in `wip.*` |
| `Rewrite/` | 4 modules | `Catalogue.lean` imports `wip.rnDict`, which has **91 `sorry` tokens and four refuted cells**. The mechanism is finished; the rule data is not, so this one cannot return until the dictionary does |
| `FRJO/` | 6 modules, 811 lines | superseded. See below |

Surviving targets: libraries `Core`, `LaxLogic`, `BiLax`, `Reject`, `Meta`,
`FRJ`, `proofstates`; executables `bilaxscreen`, `laxrun`, `pstates`.

### FRJ◯, and the folder that is not it

**`FRJ◯` is a calculus; `FRJO/` was a folder.** Note `◯ ≠ O`. The name
collision is unfortunate and the two must not be conflated: the live
development of the FRJ◯ calculus is written over `FRJ/`, and `FRJO/` is the
older attempt, now superseded and off this branch.

What is here, imported 2026-08-20 from `claude/frj-redevelopment-69005f` at
`ccb472c663d7988cf6ab9b72428cb9069294003f`:

| file | lines | what |
|---|---|---|
| `FRJ/Bridge.lean` | 165 | `ofPLL`/`toPLL` isomorphism, `Kripke.toConstraint`, and `not_derivable_of_countermodel : ¬ K.valid (ofPLL φ) → [] ⊬ φ` |
| `FRJ/Search/Engine.lean` | 657 | the forward-saturation engine, derivation-carrying (a hit IS a derivation) |
| `FRJ/Search/Fast.lean` | 308 | same closure, three exact cuts |
| `FRJ/Search/Pin.lean` | 227 | `Tab.toKripke?` and `minimise`: a discovery becomes a kernel-checkable countermodel |

All four are sorry-free and **unconditional**, and depend only on modules
already in `Core` (`FRJ.Sound`, `FRJ.Calculus`, `LaxLogic.PLLKripke`), so they
went straight into `Core` §13 rather than into any weaker tier. Seven pins were
added to `Core/Audit.lean` §13 — harvested from the build, not written from
memory, which is what the first passing build verifies.

**This is a snapshot, and the engine is still being built.** To re-sync, diff
the source branch against the recorded commit and take what is new:

```
git diff ccb472c663d7988cf6ab9b72428cb9069294003f..<newer> -- FRJ/
```

Then re-harvest the §13 pins (`lake env lean` on a scratch file importing
`Core`) rather than assuming they are unchanged, and update the commit recorded
above. If a later revision of the engine acquires a `sorry` or a hypothesis it
does not discharge, it does not belong in `Core`: that is the case a third tier
would exist for, and none of this material needs one yet.

`FRJ/Search/Engine.lean` is a port of `wip/frj_sat.lean`, which stays the frozen
differential oracle. That file is on the development branches, not here, and the
docstring says so.

**Known gap: the search cannot be invoked from a command line on this branch.**
The library came; the drivers did not. `rnfrj`, `rnpin`, `frjderive` and
`frjcert` — including the "sequent in, Lean-checked certificate out, one
command" path — are all rooted in `wip/`, and all four import
`wip/rnBank.lean`, a *generated* corpus produced from `wip/rnDict.lean`, which
is the unfinished dictionary that keeps `Rewrite/` out. So promoting a driver as
it stands would drag the unfinished rule data back in. The clean fix, for
whoever does the next re-sync: split `frjcert`'s sequent-driven path from its
bank-driven one, and promote only the former as `FRJ/Cert.lean` with a
`frjcert` executable. Until then the search is usable from Lean but not from a
shell.

## 4. Re-admitting a campaign

1. Finish its terminal result: sorry-free, `#guard_msgs`-pinned, axioms within
   `[propext, Classical.choice, Quot.sound]`.
2. Delete its entry from `TRIMMED_PREFIXES` / `TRIMMED_MODULES` in
   `scripts/core-audit.py`.
3. Add a `/- ## n. Title -/` group to `Core.lean` with its imports. **Plain
   comments, not `/-! -/` doc comments** — a doc comment between imports is a
   Lean error (`invalid 'import' command`).
4. Add the terminal theorem's pin to the matching section of `Core/Audit.lean`.
   Section numbers are kept parallel across `Core.lean`, `Core/Audit.lean` and
   `README.md` §4.
5. Add its step to the reading order in `README.md` §4, and remove any claim in
   §6 that it is not here.
6. `lake build && python3 scripts/core-audit.py --check`.

## 5. Build targets and checks

- `lake build` — the default target is `Core`, so a bare build builds the core
  and `Core/Audit.lean`. Green with **no** `declaration uses 'sorry'` warning is
  the only evidence that counts for criterion 2.
- `lake build LaxLogic` — the full working library, parked campaigns included.
  Keep this green: it is the proof that a hoist did not disturb a trimmed
  cluster. It warns on four `sorry`s, all in the `PLLSemUI*` cluster; those are
  the only ones on the branch.
- `lake build BiLax` / `Reject` / `Meta` / `FRJ` / `proofstates`, and the three
  executables `bilaxscreen`, `laxrun`, `pstates`. All green.
- `python3 scripts/core-audit.py` — recomputes the import closure from
  `Core.lean` and checks what Lean cannot see: closed boundary, module
  docstrings, no `sorry`. `--check` exits non-zero, which is what CI runs.
  Current state: 111 roots, 111 modules in the closure — the boundary is exactly
  closed.
- `.github/workflows/lean_action_ci.yml` runs all three. The `sorry` step
  rebuilds with the log captured, because Lean only *warns* on `sorry` and the
  build alone would not catch a reintroduced one.

Two traps worth writing down. A backgrounded `lake build … | tail` reports exit
code 0 because the *last* command in the pipeline succeeded — capture
`LAKE_EXIT=$?` into the log and grep for it. And in a fresh Claude worktree, run
`cp -Rc <repo-root>/.lake .lake` (APFS clone, instant) before building.

## 6. Where the rest of the record lives

- `docs/README.md` — what the `docs/` tree is, and the two cautions that apply
  to everything in it (paths may be stale; the build is the authority on
  status).
- `HANDOFF.md` — the standing handover. Append a dated section; never rewrite.
- `docs/next-session.md` — the live threads.
- `docs/calculus-map.md` — **the** provenance reference. Read it before
  asserting which proof system a result belongs to.
- `docs/rn-dictionary-status.md` — the state of the rewrite dictionary, and the
  controls that must be read before trusting `rnextend`'s verdicts. Both the
  dictionary and `rnextend` are off this branch; read it on a development
  branch.

## 7. Licence

**Settled.** Avi Craimer authored the initial commit and 458 surviving Lean
lines, concentrated in `PLLProof.lean`, `PLLFormula.lean`, `PLLAxiom.lean` and
`FormattingUtils.lean` (see `NOTICE`), so the Apache 2.0 grant needed his
agreement as well as Matthew Fairtlough's. He has given it — recorded
2026-08-20. The grant covers the whole work; publication is not blocked.

Anyone adding files should keep `NOTICE` accurate: it is not a licence
condition but it is the record of who wrote what, which results are someone
else's mathematics, and that the development was produced with machine
assistance under human review.

## 8. Open decisions

None outstanding. The residue of the removal — `CLAUDE.md`, `PROGRESS.md`,
`PROGRESS-POLAR.md` and the 50 files under `docs/` that referenced `wip/` — was
tidied on 2026-08-20: `CLAUDE.md` now marks each rule whose machinery is absent
and says what *is* runnable here, `docs/README.md` states the two standing
cautions once, and the four documents the root README links to carry a banner.
The 95 documents were not individually rewritten, deliberately: they are the
research record, and rewriting them would damage it.
