# The proof-status ledger — what it is, what it found

2026-09-16, branch `ledger`. After four lines merged into `main`, neither
Matthew nor I could say which of this repository's stated results are
machine-checked *in the merged tree*, under which axioms, and which are OPEN.
`docs/calculus-map.md` is the declared provenance reference and predates the
merge. This campaign closes that gap mechanically and keeps it closed.

## The parts

| file | what it is |
|---|---|
| `scripts/ledger.lean` | asks `Lean.collectAxioms` about every declaration of a list of modules; writes JSONL |
| `scripts/ledger-run.py` | drives it, partitioning the module list (see below) and merging the rows |
| `scripts/ledger-report.py` | turns the JSONL into `docs/status-ledger.md` |
| `scripts/ledger-diff.py` | classifies drift between two runs |
| `scripts/check-ledger.sh` | the gate: regenerate, compare, report |
| `docs/ledger-modules.txt` | the estate: the module list the ledger covers |
| `docs/status-ledger.jsonl` | the record, one line per declaration, sorted |
| `docs/status-ledger.md` | the page a human reads |

Run it:

```bash
lake build                       # the ledger reads .olean, it does not elaborate
scripts/check-ledger.sh          # 0 clean · 1 regression · 2 stale · 3 broken
scripts/check-ledger.sh --update # rewrite the record and the report
```

The gate distinguishes two kinds of drift, because they need different
responses. **REGRESSION** — a new `sorryAx`, a new axiom, a new `native_decide`
taint, or a declaration that vanished — means something got weaker, and it is
the failure the 2026-09-16 merge produced silently. **STALE** — additions, or a
declaration whose axioms shrank — means the development moved and the record
needs regenerating.

## Two things the mechanism had to learn

**`native_decide` does not cite `Lean.ofReduceBool` here.** Under Lean 4.31 a
`native_decide` call mints a fresh axiom named after the declaration,

    BeliefLax.chain4_card._native.native_decide.ax_1_1

so a taint check against the three fixed names — which is how the check is
described everywhere in this repo's prose — sees nothing. The ledger matches
both spellings, and `scripts/ledger-report.py` cross-checks the Lean tool's
flag against the axiom names, reporting a mismatch rather than trusting itself.
Two declarations in `LaxLogic/Belief/Examples.lean` are tainted this way; they
are the two `Audit/Production.lean` already holds out by name.

**The estate cannot be loaded into one environment.** The
`LaxLogic/ToolkitTest/` files are deliberate copies of the modules they test
(the toolkit's own punched fixtures) and re-declare their names, and several
roots each define `main`. Lean refuses such an import, so `ledger-run.py`
starts with the whole list, and on each refusal sets the offending module
*and everything that transitively imports it* aside for a batch of its own.
The partition is a function of the module list alone, so two runs of the same
list produce the same rows: 13 modules currently load separately.

## Watching it fail

A gate nobody has watched fail is not evidence. Two tests, both run:

**The classifier**, `scripts/test-ledger-diff.py`, mutates a copy of the record
one way at a time and checks the verdict — a proof becomes a `sorry`, gains an
axiom, becomes `native_decide`, disappears, drops an axiom, or a declaration is
added — including that it stays *silent* where it should. Writing it caught a
flaw in itself: the first clean theorem in this estate is axiom-free, so the
"dropped an axiom" case was passing vacuously.

**The whole path**, once, by hand. `Turnstile.generic_mono` in
`LaxLogic/Util/TurnstileTests.lean` was rewritten to `sorry`, the module
rebuilt, and the gate run:

```
ledger: 1 REGRESSION(S)
  SORRY       Turnstile.generic_mono  (LaxLogic.Util.TurnstileTests) — now depends on `sorryAx`
gate exit 1
```

The proof was then restored and the gate returned to `clean — 17449
declarations, unchanged`. The two clean runs also show the ledger is
deterministic: independent runs produce byte-identical records.

## What it says today

17,449 declarations in 395 modules — 8,635 theorems, 8,814 definitions and
data.

| | count |
|---|--:|
| axiom-free | 8,370 |
| `propext` only | 3,699 |
| `propext`, `Quot.sound` | 3,300 |
| `propext`, `Classical.choice`, `Quot.sound` | 1,991 |
| carrying `sorryAx` | 81 |
| `native_decide`-tainted | 2 |

The 81 `sorryAx` declarations are the OPEN list, named in
`docs/status-ledger.md`; 66 of them carry `sorryAx` and nothing else. Four are
the halted UI route in the library (`SemUILayered`, `SemUIHenkin` ×2,
`SemUIChar`); the rest are in `wip/`, where a `sorry` is permitted by CLAUDE.md
rule 1 and is the point of a blueprint file.

## What the ledger does NOT cover, and why that matters

The estate is what *builds*: 406 modules with an `.olean`. The repository holds
1,038 `.lean` files. Of the rest:

* **302 files are covered by no build target at all** — `batch/` (112
  generated per-cell snippets), `_probe/` (13 ad-hoc harnesses), `Archive/` (8,
  self-declared superseded), the four frozen `wipa…wipd` arms, and 146 `wip/`
  files.
* **64 `wip/` files carry bare imports** (`import rnEmbed` where the module is
  `wip.rnEmbed`), 79 import lines over 25 names, and for every one of the 25 the
  `wip.`-prefixed file exists. They cannot resolve, so none of them has ever
  built. This is pre-existing, not merge damage.
* **`lake build LJF` was broken by the 2026-09-16 merge**: `LJF.lean` and the
  lakefile still globbed `LJF.Base` and `LJF.Complete`, which the merge deleted
  in favour of `LaxLogic/Focusing/`. Fixed in this branch — the root now imports
  the kept modules.
* **`Tools/` versus `tools/`** is a case collision that builds on macOS only.
  13 files and 11 targets depend on the filesystem merging the two names; on a
  case-sensitive checkout (Linux CI) `lake build Tools` finds nothing. Known and
  documented in `tools/README.md` since 2026-08-21, still unresolved. It does
  not reach the default targets.

## The reconciliation corpus

The other half of the campaign: 3,338 claims of proof status in the prose
(`docs/`, `HANDOFF.md`, the three Verso documents, `METHOD.md`, `TOOLS.md`) —
PROVED 1,241, REFUTED 715, OPEN 422, plus the machine-checked / kernel-checked /
sorry-free variants. **Only 838 of them (25%) name a Lean declaration**; the
other 2,500 cannot be reconciled mechanically at all. Two findings to act on:

* `docs/disproof-handoff.md:1457` says FRJ◯ completeness is unconditional;
  `TOOLS.md` and `docs/calculus-map.md` say FRJV completeness is OPEN. Both are
  current. One of them is wrong.
* `docs/calculus-map.md`'s own cross-reference table still cites the flat
  pre-merge paths (`PLLNDCore.lean`, `PLLSequent.lean`, …) while its prose cites
  the new nested ones — the designated provenance reference is internally
  inconsistent about paths.

## Order of the remaining work

1. Reconcile the 838 claims that cite a declaration against the ledger,
   mechanically: every one either matches, or is relabelled with evidence.
2. Repair the paths in `docs/calculus-map.md` and settle the FRJ◯/FRJV
   contradiction from the ledger, not from memory.
3. The 2,500 claims with no citation: attach declarations where they exist,
   and mark the rest as prose, not record.
4. The mechanical repairs: the 64 bare-import `wip/` files, and a decision
   (Matthew's) on `batch/`, `_probe/` and `Archive/`.
5. Wire `scripts/check-ledger.sh` into CI on `main`.

Then the second campaign, `docs/proof-simplification-plan-2026-09-16.md`:
simplifying the proofs that do go through, with the ledger as the gate that
proves a refactor changed nothing.
