# Publishing the tools outside `wip/`: a measured plan

**Status: PLAN — nothing here is built.** Written 2026-08-20 on branch
`claude/frj-redevelopment-69005f`, after the `RNReps` migration
(`b2f46f0`). Every number below is measured on that commit; the
commands that produced them are given so they can be re-run.

The target Matthew set: *a new branch with no sorried files, which also
contains all the very useful tools we have built, as well as an
RN(◯,{}) dictionary upon which countermodel/proof search is hoisted.*

That is three separate criteria. They are not equally hard, and the
audit below shows the difficulty is concentrated in one of them.

---

## 0. What the audit found

### 0.1 `lake build` does not verify this repo

    lakefile.toml:4   defaultTargets = ["LaxLogic"]

A bare `lake build` builds the `LaxLogic` library and nothing else — not
`FRJ/`, not `Reject/`, not `Rewrite/`, not `wipshared`, and none of the
**103** `lean_exe` targets. This was discovered the hard way during the
`RNReps` migration: a syntax error in `wip/rnDict.lean` survived a
"successful" 8676-job `lake build` and only surfaced when the module was
named explicitly.

**Consequence for this plan:** "the branch builds" is not a criterion
until there is a gate that enumerates targets (§4). Any claim of
sorry-freeness made against `lake build` alone is void.

### 0.2 Where the sorries actually are

Counted by a Python walk that strips block comments, line comments
**and string literals**, then looks for a `sorry` token — not by `grep`,
for the reason in §0.2a. Two `wip/` entries below are listed with their
raw counts and marked as false positives, because the raw number is what
a naive scan reports.

**Outside `wip/` — 5 real sorries in 3 files:**

| file | sorries | which |
|---|---|---|
| `LaxLogic/PLLSemUIChar.lean` | 2 | two `exact .inl (by sorry)` at 322, 327 |
| `LaxLogic/PLLSemUIHenkin.lean` | 2 | two named `sorry`s at 341, 352 |
| `LaxLogic/PLLSemUILayered.lean` | 1 | `amalgamation` at 827 |

That is the whole list. An earlier draft of this document added
`tools/proofstates/Recorder.lean` as a fourth file; that was wrong. It
contains the word twice, once in a docstring and once in the string
literal `containsStr m.text "sorry"`, and no `sorry` term. Corrected
after `lean-branch-review` challenged it.

`FRJ/` (17 files, 22 554 lines), `Reject/`, `Rewrite/`, `BiLax/`,
`Meta/`, `FRJO/` are **entirely sorry-free**.

### 0.2a `grep` silently skips one file in this repo

Worth knowing before trusting any audit here, including this one.
`grep` in these sessions is a shell function wrapping `ugrep -I`, which
skips files it judges binary. `tools/proofstates/Recorder.lean`
contains one NUL byte, so `file` reports it as `data` and every
`grep` over it returns **no matches and exit 1** — indistinguishable
from a clean file. It is the only such `.lean` file in the tree
(scanned: exactly 1 of them).

Both this session and `lean-branch-review` reached "Recorder.lean has no
`sorry`" through that silently-skipped grep. The conclusion is right,
but the evidence was not — the file does contain the string twice.

**Any sorry-scan used as a release gate must read bytes, not shell out
to `grep`.** A Python walk that strips comments *and* string literals
is what produced the counts above.

**Inside `wip/` — 159 real sorries in 9 files** (341 `.lean` files
total):

| file | sorries | note |
|---|---|---|
| `wip/rnDict.lean` | 87 | of 323 stated cell theorems |
| `wip/rnDict2.lean` | 58 | the enlarged 16-rep round |
| `wip/cascadeBox.lean` | 4 | |
| `wip/g4ill_ui.lean` | 3 | |
| `wip/G4conf.lean`, `wip/onevar_descent_dev.lean` | 2 each | |
| `wip/absorb_base.lean`, `wip/ljfo_completeness.lean`, `wip/onevar.lean` | 1 each | |
| `wip/rnDictGen.lean` | (9) | **false positive** — all inside emitted string literals |
| `wip/frj_cert.lean` | (1) | **false positive** — the word in a `VERDICT` message |

### 0.3 The tools are already clean

Transitive import closure per tool, with sorry counts (the closure
walker is `scratchpad/audit.py`):

| tool | root module | closure | sorries |
|---|---|---|---|
| `frjcert` | `wip.frj_cert` | 16 | **0** |
| `frjderive` | `wip.frj_derive` | 17 | **0** |
| `rnpin` | `wip.rnpin` | 17 | **0** |
| `rnfrj` | `wip.rnfrj` | 16 | **0** |
| `closedfrag` | `wip.closed_frag` | 31 | **0** |
| `rncprobe` | `wip.rnc_probe` | 31 | **0** |
| — | `wip.rnBank` | 13 | **0** |
| — | `LaxLogic.RN.Reps` | 4 | **0** |
| `rwscreen` | `wip.rw_screen` | 53 | 92 (via `wip.rnDict`) |
| `rnDictGen` | `wip.rnDictGen` | 51 | 92 (via `wip.rnDict`) |

So the FRJ◯ search-and-certificate stack — the part Matthew called the
useful tools — carries **no sorry at all**, and needs no repair before
publication. Only the dictionary-consuming tools are blocked, and they
are blocked by exactly one file.

### 0.4 The one structural blocker, and it is small

`Rewrite/Core.lean` imports `LaxLogic.PLLSemUILayered` (1 sorry). But:

- `LaxLogic/PLLSemUIFrag.lean` (682 lines, **sorry-free**, and the home
  of `Interd` and the ND combinators that `Rewrite/` actually uses)
  references **exactly one** name from `PLLSemUILayered`: `crank`.
- `crank` is a 7-line structural recursion on `PLLFormula`
  (`PLLSemUILayered.lean:87`) depending on nothing but the datatype.
- `amalgamation`, the sorry in that file, is referenced by **no other
  file in the repo**.

So the sorried module is load-bearing for nothing *at that edge*.
Cutting it is a file move, not a proof obligation.

**But it does not unblock `Rewrite/`, and an earlier draft of this
document claimed it did.** `Rewrite/Catalogue.lean:43` imports
`wip.rnDict` directly — 87 sorries. So `Rewrite/` is blocked on the
**dictionary**, not on `crank`; extracting `crank` clears
`Rewrite/Core.lean` and nothing more. Correction owed to
`lean-branch-review`, and it reorders this plan (§5).

---

## 1. Work item W1 — cut the sorried dependency (small)

Move `crank` from `LaxLogic/PLLSemUILayered.lean` into a new leaf module
(`LaxLogic/Crank.lean`, importing only the formula datatype), and have
both `PLLSemUILayered` and `PLLSemUIFrag` import it.

Result: `PLLSemUIFrag` and `Rewrite/Core.lean` no longer have a sorried
file in their import closure. `Rewrite/` as a whole does **not** clear
— see §0.4 — because `Rewrite/Catalogue.lean` imports the dictionary.

Verification: re-run `audit.py` on the `Rewrite.*` roots; the count must
go to 0. Re-run the `#guard_msgs` axiom pins in
`Rewrite/Catalogue.lean` — they read `[propext, Quot.sound]` for
`fullSet` today and must still read exactly that.

**Estimated size: one afternoon at most.** (My estimates here have run
~4× pessimistic; treat this as an upper bound.)

## 2. Work item W2 — decide the fate of the three sorried files

All three are the **shelved UI route** (`PLLSemUIChar`,
`PLLSemUIHenkin`, `PLLSemUILayered`), shelved 2026-08-07 after round 9.

A branch criterion of "no sorried files" admits three readings, and the
choice is Matthew's:

- **(a) Exclude.** The publication branch simply does not carry the
  shelved UI modules. Cheapest, and it loses nothing that is proved —
  their sorry-free content stays available on `main`.
- **(b) Demote.** Move them to a clearly-marked `open/` directory that
  the gate exempts by name, so OPEN work stays visible without
  contaminating the sorry-free claim.
- **(c) Discharge.** Prove them. Not in scope: the UI route is shelved
  precisely because the room-free statement was REFUTED and the
  room-carrying one is not `decide`-feasible.

**Recommendation: (a).** The three UI modules are the entire list;
there is no fourth file to decide about (§0.2).

## 3. Work item W3 — the dictionary layer (the substantive one)

This is where "search hoisted on the dictionary" has to be made precise,
because the dictionary is **not one artefact but three**, with different
proof status:

| layer | content | status |
|---|---|---|
| **L0 — representatives** | `q0 … q14` | PROVED-irrelevant: they are definitions. Sorry-free. **Already done** — `LaxLogic/RN/Reps.lean`, `9d8efea`. |
| **L1 — certified closure cells** | `Interd (qᵢ ⊙ qⱼ) qₖ` for ⊙ ∈ {∧,∨,⊃,◯} | 236 of 323 PROVED; **87 OPEN**, and **4 REFUTED** |
| **L2 — refutations** | the closure-failure witnesses | sorry-free in `wip/rnDictRefute2.lean`, but reached through `wip/rnDict2.lean` (58 sorries) |

The mistake to avoid is the one `rndSet` already made once: taking all
323 cells by name pulled `sorryAx` into the simpset and, worse, admitted
four rules rewriting a formula to a **non**-interderivable one. That is
recorded in `CLAUDE.md` as the standing "never harvest an unproved cell"
rule, and it is the design constraint here.

**The design move: make partiality explicit in the type.** Rather than
a total table with `sorry`ed entries, L1 should expose

    def cell? : Fin 15 → Fin 15 → Conn → Option (Σ k, Interd (op qᵢ qⱼ) qₖ)

so a missing cell is `none` — a value, not an axiom. A consumer that
needs totality must handle `none`; a consumer that does not, keeps its
proof. This makes the sorry-free branch achievable **without** proving
the 87 open cells, and it makes the four REFUTED cells expressible as
genuine refutations rather than as false collapses.

Search is then hoisted on `cell?`: the normaliser tries a cell, and
falls through to search when the cell is `none`. Effectiveness degrades
gracefully; soundness never depends on the table being complete.

### 3.1 RESOLVED — neither side is wrong, and neither may overwrite the other

Raised as OPEN in the first draft of this document and settled the same
day. **Which side is wrong? Neither.** Each is stale in a different
direction, and each holds something the other does not.

**Lean's own verdict**, both files built in place as `wip.rnDict`:

| | in-tree | regenerated |
|---|---|---|
| errors | 0 | 0 |
| `declaration uses 'sorry'` | **91** | **53** |
| cell theorems stated | 323 | 323 |
| cells left `sorry` | 87 | 49 |

The difference is exactly 38, and every one of the 38 runs the same way:

| direction | count |
|---|---|
| generator has a kernel-checked proof, tree has `sorry` | **38** |
| tree has a proof, generator has `sorry` | **0** |
| both carry a proof, of different targets | **0** |

That last row is the one that would have forced escalation. It is empty.

**The differing table entries assert nothing.** All 24 sit at cells the
tree marks `OPEN CELL … sorried at the first open candidate`. The
clearest case is `cBox_14`:

- tree — `theorem cBox_14 : Interd q14.somehow q9 := sorry`, docstring
  *"candidates [9, 12, 14] neither proved nor refuted … sorried at the
  first open candidate"*;
- regenerated — `theorem cBox_14 : Interd q14.somehow q14 := ⟨ofG4 …⟩`,
  the **third** candidate, with a proof term.

`q9` was a placeholder, not a claim. The generator found the answer.
(◯q14 ≡ q14 also matches the hand certificate recorded at `c5d9ddc`.)

**Why the tree is behind.** It was last *regenerated* at `d37f9c0`
(2026-07-26, +2199 lines). The bounded searcher
`LaxLogic/PLLG4Term.lean` was improved the **next day**, `3a7272f`
(2026-07-27) — *"budget × failure memo × canonical key in the bounded
searcher"*. Same fuel budget (`budget : Nat := 400000`), longer reach.
Every commit to `wip/rnDict.lean` since `d37f9c0` is docstring-only.

**Why the generator is behind.** The tree carries **20 refutation
records** — 13 `REFUTED CELL` and 7 `REFUTED AT THIS CANDIDATE` — and
**24 pointers** to kernel-checked FRJ◯ countermodels in
`wip/rnFRJCerts.lean`, added by hand on 2026-08-18 (`25679c4`,
`e85a7e1`). The regenerated file has **4** and **0**. The generator has
never heard of that campaign: it post-dates the generator's last source
change, and `main` computes its tables from search alone.

So `cp` in either direction destroys real content:

- overwrite the tree → lose 16 refutation records and all 24 certificate
  pointers, including the 13 cells where the 15-class closure is now
  known to FAIL;
- leave the tree → keep 38 cells marked OPEN that are in fact PROVED.

**The generator is deterministic**, so this is a version gap, not noise:
two independent runs are byte-identical (2151 lines; 321 s and 326 s).
No clock value feeds a decision — the `IO.monoMsNow` calls are reporting
only — and the bound is a fixed `Nat`.

**The fix, and it belongs in the generator, not in the file.** Teach
`wip/rnDictGen.lean` the FRJ◯ refutations as data (cell ↦ certificate
name in `wip/rnFRJCerts.lean`), and give the emitter the precedence
**PROOF > REFUTED > OPEN**. One run then produces both halves, and the
file stays reproducible instead of becoming hand-maintained. Expected
after that: 323 cells, 38 newly PROVED, 20 refutation records preserved,
~49 sorries.

**Not to be done blind, and not by me without a word from Matthew** — it
changes the dictionary that `Rewrite/Catalogue.lean` imports and that the
whole L1 layer rests on. Note also that the 13 `REFUTED CELL` entries
say the 15-class closure fails at **13** cells, not the 4 the generator
knows about.

## 4. Work item W4 — layout and the verification gate

### 4.1 Proposed layout

    LaxLogic/RN/Reps.lean        representatives           (exists)
    LaxLogic/RN/Dict.lean        the Option-valued L1 table (W3)
    LaxLogic/Crank.lean          the extracted measure      (W1)
    FRJ/                         the calculus + search       (exists, clean)
    Tools/Cert.lean              the frjcert pipeline      ← wip/frj_cert.lean
    Tools/Derive.lean            route-B scaffolding       ← wip/frj_derive.lean
    Tools/Pin.lean               ← wip/rnpin.lean
    Tools/Bank.lean              ← wip/rnBank.lean

as one new `[[lean_lib]] name = "Tools"`. The `lean_exe` entries keep
their names (`frjcert`, `frjderive`, `rnpin`) and change only their
`root`, so every command in the docs and in `HANDOFF.md` keeps working.

`wip/` is **not** deleted and **not** emptied. It stays as the probe
scratch space it is; the published modules simply no longer live there.
Where a probe needs a published tool, it imports it.

### 4.2 The gate

A script — `scripts/verify-branch.sh` — that fails on any of:

1. **Enumerated build.** `lake build` naming every `lean_lib` and every
   `lean_exe` in `lakefile.toml` (parsed from the file, so a new target
   cannot silently escape). Not the bare `lake build` — see §0.1.
2. **Sorry scan.** The `audit.py` walk over the branch's own modules,
   with string literals excluded so the two false positives in §0.2 do
   not fire, and with the §2 exemption list (if (b) is chosen) named
   explicitly rather than pattern-matched.
3. **Axiom pins.** The `#guard_msgs`-pinned `#print axioms` in
   `Rewrite/Catalogue.lean` and the FRJ soundness pin. `collectAxioms`
   is the only sound oracle; `native_decide` taints, and
   `LaxLogic/BeliefExamples.lean` already carries two
   `native_decide.ax` axioms that the gate must either exempt by name
   or exclude from the branch.
4. **Tool smoke test.** `lake exe frjcert "q10 ⊢ q10 ∧ q13" <tmp> 12`,
   asserting `lean exit 0` and `[propext, Quot.sound]` on both emitted
   theorems. This is end-to-end: search, minimise, emit, and Lean's own
   check of the emitted file.

Gate 4 is the one that catches what the others miss. It already earned
its place: it caught an illegal dot-notation chain in generated source
that no amount of grepping would have found.

---

## 5. Ordering

**Revised after §0.4 and §3.1: W2 → W4 gate → W3 → W1.**

The first draft put W1 first, on the mistaken belief that `crank`
unblocked `Rewrite/`. It does not — `Rewrite/Catalogue.lean` imports the
dictionary — so **W3 is on the critical path and W1 is not**. W1 drops
to last: it is worth doing, but it clears one file, not a subtree.

W2 alone makes the "no sorried files" claim true (exclude the three
shelved UI modules). W4 makes it checkable. W3 is what any `Rewrite/`
or dictionary-backed search on the branch waits for, and §3.1 now tells
it exactly what to do first: merge the two halves inside the generator.

**Coordinate with `publication/core`.** A parallel session has an
already-pushed sorry-free branch (`origin/publication/core`) that
removes `wip/`, `Rewrite/` and `FRJO/` outright and has taken
`LaxLogic/RN/Reps.lean` from here. Its `scripts/all-targets.py` already
implements §4.2 gate 1. Read that branch before building any of §4
here, or the two efforts converge on the same artefact from opposite
ends. It has also cut `LaxLogic/Deriv.lean` and `LaxLogic/Bisim.lean`
out of `PLLSemUIFrag`/`PLLSemUI` — so W1 should take that decomposition
rather than inventing a second one.

## 6. Explicitly not in scope

- The **route-B derivation emitter** — recorded PENDING in
  `docs/next-session.md`, and Matthew has said not to build it without
  asking first.
- Proving any of the 87 open dictionary cells.
- The shelved UI route.
- Renaming `FRJO/` (which is *not* FRJ◯ and has caused two
  misattributions this session). It touches a peer's tree, so it is
  Matthew's call, not a unilateral cleanup.
- Appending `q15` to `RNReps`. It is a genuine 16th class
  (`wip/rnDict2.lean:34`), and appending it is consistent with the
  append-only rule — but `rnDict2.lean` is a generated file, so the
  append must be done together with a generator change, and it should
  wait until §3.1 is settled.
