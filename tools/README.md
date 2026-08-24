# `tools/` — layer 2 of the RN(◯,{}) mapping

Created 2026-08-21: *aggregate the tools that have been shown to work and
that are the latest versions.*  Rewritten later the same day after the
review, to record which engine is canonical and why.

The dictionary is built in three layers.  Layer 1 is `Certified/`, the
register of every theorem the database may cite, each re-pinned there
under `#guard_msgs`.  **This** is layer 2: the engines and the harness
that checks their output and turns it into theorems.  Layer 3, the
database, does not exist yet.

---

## ⚠ This directory has two names

`tools/` and `Tools/` are **the same directory** on a case-insensitive
volume (verified 2026-08-21: same inode; writing through both spellings
produces one file).  git recorded every file here as lowercase
`tools/…`, while `lakefile.toml` declares the Lean library as `Tools`
with globs resolving to `Tools/Bank.lean`.  It builds on this machine
only because the filesystem merges the two names; on a case-sensitive
checkout lake would find nothing.

Nothing was lost to this — the aggregation commit was purely additive —
but the library does not build on a case-sensitive filesystem until
either the lakefile is lowercased or the directory's case is changed in
git.  `sh tools/check-twins.sh` section 4 reports it.  The CI workflow
does not catch it, because it runs bare and `defaultTargets` is
`["LaxLogic"]`.

---

## The two canonical engines

| question | engine | soundness | completeness |
|---|---|---|---|
| does `Γ ⊢ φ` hold? | **LJF◯ focused search**, `TwoSidedLink.searchProves` | `laxND_of_searchProves` | `searchProves_complete` — both choice-free |
| does `Γ ⊬ φ` hold? | **FRJ(◯)**, `FRJ/` | `FRJ.soundness`, `[propext, Quot.sound]` | **OPEN** (`docs/frj-w4.md` §9) |

Both are pinned in `Certified/Register.lean`.

**Why the incomplete engine is the right one for refutation, and what
that claim does NOT say.**  The argument is STRUCTURAL, not a speed
measurement, and the distinction matters because the speed claim has not
been made:

* FRJ(◯) **never enumerates MODELS.**  Given a refutation derivation `d`,
  `FRJ.modR d` CONSTRUCTS the Kripke countermodel directly — no
  candidates, no search.  A battery method instead filters a
  pre-generated set of models, so it can only ever find a countermodel
  the battery already contains.  That is the real difference and it is
  why enumeration is banned as a discovery method.
* FRJ(◯) **does enumerate premise families, eagerly.**  The join rules
  take families of arbitrary arity and `famsUpTo` materialises every
  sublist up to size `k` into a strict `List` — no laziness, no sharing.
  `jmax` / `pmax` exist BECAUSE it enumerates.  Measured on bank cell
  `cAnd_8_11`: 14748 families in one round from a 61-row database, with
  families capped at size 3.

An earlier version of this file said FRJ(◯) "never enumerates".  That was
too broad and is corrected above.

**The family enumeration is a REPRESENTATION artefact, not something the
calculus forces** — see `docs/frj-profile-search.md`.  Every join rule's
conclusion and side conditions factor through four aggregates
`(Σ, Θ, M, Υ)`, so families sharing a profile are interchangeable and can
be merged, turning enumeration into a monotone fixpoint whose cost is
bounded by the GOAL rather than by the database size.  That work comes
before any comprehensive re-measurement.

**NOT VERIFIED: that FRJ(◯) is the most efficient refutation engine.**
No head-to-head measurement against any other engine on a shared corpus
exists — that is `enginecmp`, which is NOT BUILT.  What has been measured
runs the other way on cost: FRJ(◯) took 265 s over 120 bank goals (worst
cell 41 s), and on eight small ◯-goals it took up to 217 ms where LJF◯
answered every one below timer resolution.  Treat the choice of FRJ(◯) as
resting on the constructive-vs-filtering argument alone until
`enginecmp` says otherwise.

**`--lamcap=0` means UNCAPPED, not zero.**  `lamCap` gates `lamCandidates` (`FRJ/Search/Engine.lean:202`): below the cap it enumerates the FULL power set of `Θ` (exponential), above it a 3-candidate approximation.  So `cap=0` would trigger the cheapest, MOST restrictive approximation almost always — the opposite of `jmax`/`pmax`, where `none` already means uncapped.  Every tool's `--lamcap=0` is a CLI convention translating to a large sentinel (1000000) instead, so the flag reads the same way across all three caps: 0 always means "take this cap off."

**Standing process rule: no discovery by battery enumeration.**
Generating all models of a given size and testing whether any refutes the
goal is banned as a DISCOVERY method.  It is structurally incapable of
beating a constructive engine, and it is essentially incomplete.
Enumeration survives only as an independent CHECK on a model some engine
already built.

`Reject/` is therefore registered in two roles, neither of them finder:

* `Reject.certifies` as an **independent second checker** — it re-derives
  the refutation through different code from FRJ(◯)'s, so it is a genuine
  cross-check on a model FRJ(◯) constructed;
* `Reject/Reduce.lean` (`not_laxND_iff_built`, `qModel`, `refineM`,
  `exists_reduced_countermodel`) as the **completeness theory** of the
  refutation side.  Note that `not_laxND_iff_built` carries
  `Classical.choice`: it says a countermodel EXISTS and hands back none.
  Theory, never evidence for a cell.

`TwoSidedLink.two_sided_disjoint` guarantees the two sides can never both
fire.

---

## What a negative result means

Two different things, and they must never share a spelling:

* **not found within bound** — the search did not find a (dis)proof
  inside the `Config` it was given.  A limitation of the run.  This is
  the ONLY negative outcome any engine here can currently produce, and
  the whole `Config` is printed with it so a re-run knows every dimension
  it can raise.
* **no (dis)proof exists** — a statement about the calculus, and a proof
  of incompleteness if the sequent is settled elsewhere.  **Nothing here
  produces this**, and no placeholder for it exists.  What would justify
  it is `Certified.SearchComplete`, which is OPEN.

WITHDRAWN 2026-08-21: `no-derivation-at-fixpoint`.  `Tools/Search.lean`
used to split the negative case, calling it a fixpoint when
`!lamCapped && !dbCapped && roundsUsed < rounds` — three of the five
things that can truncate a round.  `Config` also carries the join
arities `jmax` and `pmax`, which `Stats` did not record at all.
Measured after the repair, over **60 bank cells = 120 goals** at default
settings: `caps=jmax+pmax` on 119 of them (one also `lamCap`), one
refutation, and **`closed-no-cap-bound` fired zero times**.  So the old
label would have claimed rule-closure exhaustion on 119 of 119 negative
results.  It was not occasionally wrong; on this bank it was wrong every
single time.

**And the third outcome is not reachable on this bank in practice.**
`jmaxBinding` is `db.is.length > jmax`, and the bank's databases run to
`IS = 61` (cell `cAnd_8_11`) against a default `jmax = 3` — so FRJ(◯) is
forming premise families of size ≤ 3 out of 61 available rows.  Lifting
the cap far enough to close cap-free would mean enumerating subsets of a
61-element list.  The honest verdict on dictionary cells is therefore
always `not-found-within-bound`, and the incompleteness miner will not
get its witnesses here by cap-free closure; it gets them from cells
another engine settles.  `closed-no-cap-bound` is a small-goal
phenomenon: it fires on `p ⊃ ◯p` (RS=2, IS=2) and its kind.

The failure log is an asset, not exhaust.  A sequent FRJ(◯) cannot refute
that another engine settles by other means is a **machine-checked
incompleteness witness for FRJ(◯)** — exactly the object the W4
completeness campaign needs.

---

## The Lean toolchain

| module | exe | what it does |
|---|---|---|
| `tools/Cert.lean` | `frjcert` | sequent → FRJ(◯) search → minimised countermodel → emits `.lean` + `.svg` → **runs Lean on what it emitted** and reports that exit code and `#print axioms` |
| `tools/Pin.lean` | `rnpin` | route A: search, keep the model, pin it as a `Search.Tab` |
| `tools/Search.lean` | `rnfrj` | the FRJ(◯) search driver over a bank |
| `tools/Derive.lean` | `frjderive` | route B: keeps the *derivation*. **Partial** — the emitter is deliberately unbuilt |
| `tools/Bank.lean` | — | the corpus the drivers run over |

`frjcert` is the strongest of these precisely because it checks its own
output: nothing is reported as verified that the tool did not itself
verify.

### Scripts in the same directory

`check-twins.sh` (the twin/case gate), `pin-backfill.py` (turns bare
`#print axioms` into `#guard_msgs`-checked pins, using Lean's own output
and never an invented string), `rn-bank-gen.sh`, `rn-cert-gen.sh`,
`rn-cert-asm.py`, and the older `FrontierSampler/`, `catpart-ref/`,
`paper-skeleton/`, `proofstates/`.

---

## Every Lean file here is a COPY, and the gate now enforces what matters

The `wip/` originals are left in place so other branches still compile.
This is the maintained side; the twins are stale by construction.

Divergence between the copies is ALLOWED — it is the point of freezing
one.  What is not allowed is **maintained code importing a frozen twin**,
which is exactly "old tools get used for new results".  `sh
tools/check-twins.sh` gates that, and it caught a real offender on its
first run: `tools/rn-cert-asm.py` both read `wip/rnBank.lean` and emitted
`import wip.rnBank`, so repointing `wip/rnFRJCerts.lean` by hand would
have been undone the next time the assembler ran.

The gate also reports that `wip.frj_cert`, `wip.rnpin`, `wip.rnfrj` and
`wip.frj_derive` have **no lake target on this branch**, so they compile
nowhere and can rot unnoticed.

### Not aggregated, deliberately

* `wip/frj_sat.lean` — the FROZEN reference implementation and
  differential oracle for `FRJ/Search/Engine.lean`.  A second copy would
  defeat the point.
* the probes (`frjprobe`, `rejscreen`, `closedfrag`, `rncprobe`,
  `clscreen`) — one-off experiments, not tools.
* `wip/rnDict.lean`, `wip/rnDict2.lean`, `wip/rnDictGen.lean` — the
  dictionary, whose tags are withdrawn (below).

---

## The status tags in `tools/Bank.lean` are WITHDRAWN

`Bank.lean` tags every cell `proved` / `refuted` / `open`, generated from
`wip/rnDict.lean`, whose bookkeeping is withdrawn: a `sorry`ed cell
theorem typechecks, can be applied, and is indistinguishable *by name*
from a proved one, so "still to be determined" and "asserted without
proof" became the same object.  **Treat every tag as UNKNOWN** until
regenerated.  `rnfrj`'s `grade` reads those tags, so its `ENGINE-BUG?` /
`NEW-REFUTATION?` verdicts are currently claims about an unsound oracle;
read the per-goal outcomes instead.

Two things survive:

* the **mechanism** — status as three-valued *data* rather than as
  theorems is the right shape, and a rebuild should keep it;
* the **individual countermodels** in `wip/rnFRJCerts.lean`, because a
  countermodel is self-certifying.

What is withdrawn is the tags and the tallies, not the engine.

Round 1 is **not** dead, whatever `docs/rn-dictionary-plan.md` used to
say: round 2 restates none of round 1's 236 proved cells, and those 236
are exactly `Rewrite/Catalogue.lean`'s `rndSet`.  The relation is
extension.  The supersession table is in that document's §0.
