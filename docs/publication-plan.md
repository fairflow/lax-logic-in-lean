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

Counted with comments stripped (`grep` over the source with `/- -/` and
`--` removed). String literals are *not* stripped, so two entries below
are false positives and are marked as such.

**Outside `wip/` — 5 real sorries in 3 files:**

| file | sorries | which |
|---|---|---|
| `LaxLogic/PLLSemUIChar.lean` | 2 | two `exact .inl (by sorry)` at 322, 327 |
| `LaxLogic/PLLSemUIHenkin.lean` | 2 | two named `sorry`s at 341, 352 |
| `LaxLogic/PLLSemUILayered.lean` | 1 | `amalgamation` at 827 |
| `tools/proofstates/Recorder.lean` | 1 | |

`FRJ/` (17 files, 22 554 lines), `Reject/`, `Rewrite/`, `BiLax/`,
`Meta/`, `FRJO/` are **entirely sorry-free**.

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

So the sorried module is load-bearing for nothing. Cutting the
dependency is a file move, not a proof obligation.

---

## 1. Work item W1 — cut the sorried dependency (small)

Move `crank` from `LaxLogic/PLLSemUILayered.lean` into a new leaf module
(`LaxLogic/Crank.lean`, importing only the formula datatype), and have
both `PLLSemUILayered` and `PLLSemUIFrag` import it.

Result: `PLLSemUIFrag`, `Rewrite/`, and everything downstream of them no
longer have a sorried file anywhere in their import closure.

Verification: re-run `audit.py` on the `Rewrite.*` roots; the count must
go to 0. Re-run the `#guard_msgs` axiom pins in
`Rewrite/Catalogue.lean` — they read `[propext, Quot.sound]` for
`fullSet` today and must still read exactly that.

**Estimated size: one afternoon at most.** (My estimates here have run
~4× pessimistic; treat this as an upper bound.)

## 2. Work item W2 — decide the fate of the four remaining sorried files

Three of them are the **shelved UI route** (`PLLSemUIChar`,
`PLLSemUIHenkin`, `PLLSemUILayered`), shelved 2026-08-07 after round 9.
The fourth is `tools/proofstates/Recorder.lean`.

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

**Recommendation: (a) for the three UI modules, (c) for
`Recorder.lean`** — one sorry in a tooling file is worth a look before
it is written off, and it is the only sorry outside the shelved route.

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

### 3.1 OPEN — the generator and the checked-in file disagree

Discovered while patching `wip/rnDictGen.lean` during the migration, and
**not** caused by it:

    .lake/build/bin/rnDictGen > gen.lean        # 2151 lines, 53 sorry tokens
    diff gen.lean wip/rnDict.lean               # 1280 differing lines

The in-tree `wip/rnDict.lean` is 2237 lines with 107 sorry tokens (87
`:= sorry` cells). A fresh generator run resolves *more* cells and
produces **different closure-table entries** — e.g. row 12 of the ∧-table
ends `12, 12, 12` when generated and `12, 9, 9` in the tree.

I have not overwritten the checked-in file, and no one should until this
is understood: one of the two is wrong, and which one is a question
about the search, not about the file. **This must be resolved before L1
is hoisted anywhere.** It is the single highest-value open item in this
plan, because every downstream table consumer inherits whichever answer
is wrong.

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

W1 → W2 → W4 gate → W3.

W3 is last because §3.1 must be resolved first, and because the L1
design should be built against a gate that already works. W1 and W2
together are what make the "no sorried files" claim true; W4 is what
makes it *checkable*; W3 is what makes the branch useful rather than
merely clean.

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
