# LJF◯: a reviewer's note on the cost of the edit–compile loop

*Written 2026-08-10 by a second agent (Opus 5) at Matthew's request, from a
read-only review of branch `ljf-pll` at `3b04ab5` plus the two commits since
(`5d61116`, `263c0e5`) and `docs/ljfo-plan.md` at its newest. **Nothing was
edited**; no build was run, deliberately, because a `lake build LaxLogic.LJFO`
was in flight and would have been competing for the same cores. The reviewer's
branch is `claude/ljf-review`, add-only, and proposes nothing to `LJFO.lean`
itself.*

The mathematics is not in question here. The E-guards, the E-res conjunct, the
parkedness discipline and the three forced changes are the content, and this
note proposes no change to any of them. What follows is entirely about the
**cost per iteration**, which is where the elapsed time and the credit are
going.

---

## The measurements this is based on

| fact | source |
|---|---|
| clean `lake build LaxLogic.LJF`: 15 m 54 s → 13 m 52 s after simp round 1 | `docs/ljf-simp-round1.md` §Metrics |
| `LJFO.lean` is larger than `LJF.lean` (5,847 committed lines vs 4,462) and still growing | `git ls-files`, working copy at +194 net lines |
| Lean has no incremental compilation *within* a file; every iteration re-elaborates all of it | Lean 4 |
| `maxHeartbeats` set to `2000000`, `4000000`, **`12000000`**, `8000000` at four points | `LJFO.lean:751, 1152, 2377, 4803` |
| Parts 1–4 (through `aSound`, ~3,800 lines, including the 12 M block) are **finished and pinned** | the axiom audit at the file's end |
| the driving loop runs **two full builds per iteration** | see below |

The last one is the immediately actionable finding. The command observed
running was:

```text
lake build LaxLogic.LJFO 2>&1 | grep -E "^error:" | head -14; lake build LaxLogic.LJFO 2>&1 | sed -n '/Missing cases/,/^error/p' | head -14
```

Lake does not cache a *failed* build, and a failed build is the normal state
during a port, so the second invocation recompiles everything from scratch.
Every iteration is costing roughly double what it needs to.

---

## Recommendations, ordered by expected saving

### 1. One build per iteration, then grep the log twice

```bash
lake build LaxLogic.LJFO 2>&1 | tee /tmp/ljfo.log | grep -E "^error:" | head -14
```

and afterwards, at no compile cost:

```bash
sed -n '/Missing cases/,/^error/p' /tmp/ljfo.log | head -14
```

Expected saving: **~50% of every iteration**, from now until the campaign ends.
Cost to adopt: one line.

### 2. Split the file at the Part 4 / Part 5 boundary

Parts 1–4 — syntax, judgments, weights, `interp`, termination, `interp_pfree`,
the toolkit, `eSound`, `aSound` — are done, pinned, and unchanged since this
morning, and they include the 12 M-heartbeat block. They are re-elaborated on
every iteration for nothing.

```text
LaxLogic/LJFOCore.lean   -- Parts 1-4, frozen, its own axiom pins
LaxLogic/LJFOMin.lean    -- Parts 5-8, imports LJFOCore
```

Lake then caches the core and the loop pays only for the tail.

**This does not cost the auditability property.** "Zero imports" means *no
mathlib and no other calculus can be carrying any of the proof*. A file that
imports only its own frozen prefix still has exactly that property, and the
audit is arguably clearer, because the pins for E1/A1 then live in a module
that provably does not see the minimality machinery.

The mega-mutual (`LJFO.lean:4804–5741`) cannot be split internally. Everything
before it can.

### 3. Develop the current member outside the mutual

A single error anywhere in a ~940-line mutual block invalidates the whole
block, so every experiment on `cimpAntC` pays for all of `aMinF`, `URF`,
`UStab`, `ULF`, `UInvG` as well.

Take the member under construction out as a standalone definition
**parametrised by the recursion it needs** — precisely the style this
development already used successfully when `eMin`/`aMin` were parametrised by
`SatE2`/`SatA2` — in a scratch file that imports the frozen core:

```text
wip/ljfo_dev.lean     -- import LaxLogic.LJFOCore; develop cimpAntC alone
```

Splice into the mutual only once it compiles standalone. `boxClean` is the
next candidate after `cimpAntC`.

### 4. Build the executable oracle — the one that changes the *rate*, not the cost

`interp` is a **computable function**, and this repository already contains a
verified finite countermodel checker (`FinCM.checkB` with the certificate
theorem `FinCM.not_provable_of_check`, `LaxLogic/PLLCountermodelEmit.lean`) and
a complete decider for PLL over `G4c` (`LaxLogic/PLLG4Dec.lean`).

So a harness file — importing both `LJFO` and the decider, which taints
nothing because the dependency points *inwards* — can:

1. evaluate `interp p todo done g` on a bank of small stations;
2. translate the result to `PLLFormula` and **test** E1/A1/E2/A2 by `decide`
   or by the countermodel emitter;
3. print the first violating cell.

Seconds per run, against fifteen minutes for a proof failure.

The case for this is not theoretical. Of the three forced definition changes so
far, **the last two were statement bugs, and both are refutable by tiny
countermodels**:

* forced change #2 — the ◯-goal direct row must be a family, because `◯` does
  not distribute over `∨` and a lax right-focus reaches genuinely lax stable
  nodes;
* forced change #3 — the ◯-goal aggregate must be box-wrapped, and the note
  records the refutation itself as two lines: `done = []`, `Δ = [◯q]`, goal
  `↑q` at `lax`, where `◯q ⊢lax q` holds but `◯q ⊬tru q`.

Both were found by elaboration, at full-file cost, after downstream clauses had
been written against the wrong definition. An evaluator would have found each
in one run.

**Seed the bank with the degenerate end of every axis**, not the typical
middle: empty station, empty kept context, `∨`-shaped bodies, boxed kept
hypotheses, `⊥`, atoms equal to `p`. That is the lesson the G4c campaign in
this repository paid nine rounds for — its round-9 refutation needed empty
context *and* untied fuel *and* a missing frame simultaneously, and no sweep
had ever emptied a context.

### 5. Name the ◯-goal row family before writing more of the U-family

Forced change #2 turned one clause into **seven shape clauses**, and each shape
now needs an equation lemma, an `interp_pfree` block, an `aSound` clause and a
`U`-arm — seven shapes across four layers — while forced change #3 rewraps all
of them.

Define the family once as a top-level function outside the mutual, e.g.

```lean
def laxRows (p : String) (done : List Neg) (Q : Pos) : List Neg := …
```

so that each layer carries **one** clause about `laxRows`, discharged by
`cases Q` inside a single lemma, instead of seven parallel clauses in four
places.

`docs/ljf-simplification-pass.md` §2.6 already identified this ("name the
attack map") and deferred it as the deepest refactor. The modal round has made
it the dominant cost, and it is strictly cheaper to do **now**, before
`URF`/`UStab`/`ULF`/`UInvG` are written against seven inlined clauses, than
after.

### 6. Profile rather than raise ceilings

A `maxHeartbeats` of 12 000 000 is 60× the default and is a symptom, not a
setting. Two cheap measurements:

```lean
count_heartbeats in
theorem … -- the suspected declaration
```

```lean
set_option profiler true in
theorem … -- prints the elaboration breakdown
```

`docs/ljf-simp-round1.md` already names the likely culprits — "the mega-mutual's
WF-compilation and the farms' failing-alternative search". A `decreasing_by`
farm with ~50 alternatives pays its failing-alternative search on every
obligation of every build. Trimming it to the entries that actually fire (the
simplification note estimated about ten) pays on every build thereafter.

### 7. Land E2 fully before touching A2

The ∃p side is the smaller and less flag-entangled half. A fully pinned
`eMinF` is a checkpoint that survives any *further* forced change on the
A-side — and given that three have landed already, the probability of a fourth
is not negligible. It also makes the remaining budget legible to Matthew,
which the current all-or-nothing mutual does not.

---

## What NOT to change

* the E-guards and the E-res conjunct — all forced by the minimality
  induction; they are the mathematical content;
* the parkedness discipline and the lexicographic offset pattern;
* the flag-free `interp` (only traversals are flag-indexed) — this is
  load-bearing for the whole design;
* the persistent contexts, which are what dissolve the G4iLL contraction
  failure;
* the blocker as a standing test, and the axiom pins.

---

## Two risks worth stating to Matthew explicitly

**The forced-change rate is not falling.** Three definitional revisions, the
last two caught by the elaborator mid-port, each invalidating downstream
clauses. Nothing in the present process shortens that loop: the paper pass
catches some, the elaborator catches the rest at fifteen minutes a go.
Recommendation 4 is the only proposal here that changes the *rate* rather than
the *cost*.

**The endgame debt may exceed the current front.** When E2/A2 land, the honest
claim is **uniform interpolation for LJF◯**, not for PLL. Two bridges remain
owed: focalization completeness, and the `Deriv ↔ LJF◯` simulation for the
modal rules. The plan sketches the second via `SCh`-simulation and calls the
first "standard-but-unwritten" — but `PLLFocused` was found *incomplete* during
this very port (it missed `◯φ` for provable implicational `φ`, which is why
`laxOf` exists). Completeness of a focused calculus is exactly the kind of
hypothesis that has already bitten once here. Worth budgeting explicitly rather
than discovering its size at the end.

---

## Suggested order of operations

1. Adopt the single-build loop (**minutes to adopt, halves every iteration**).
2. Split at the Part 4/5 boundary; re-run the pins on the core once to confirm
   they are unchanged.
3. Stand up the evaluator bank with the degenerate cells, and re-check forced
   changes #2 and #3 against it — if it reproduces both known defects, it is
   calibrated and can be trusted going forward (live-fire calibration, as the
   frontier sampler did).
4. Name the ◯-goal row family.
5. Then resume the resume-list at `cimpAntC`, in the scratch file.

Steps 1–4 are, on the numbers above, likely to cost less than two of the
current iterations and to pay for themselves within a morning.
