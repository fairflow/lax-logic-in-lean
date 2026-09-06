# HANDOVER — the PLL Verso blueprint

**Start here.** Written 2026-09-06 15:20 BST for a session picking this up cold.
Everything needed is in this file; you should not need to reconstruct anything
from a previous conversation. For the blueprint's own technical decisions and
traps, see `LaxBlueprint/HANDOFF.md` alongside this.

Published site: <https://fairflow.github.io/lax-logic-in-lean/>

---

## 0 · One decision is waiting for Matthew

Not a blueprint decision — a mathematical one, and it blocks the main result.
Raise it before doing anything else.

Since §4.24, **N4 is the only obligation between route (B) and `PLL_UI`**, and
§4.25–§4.28 have reduced it much further:

- `QBound` — **PROVED** (§4.26; `qBound`, measure `μ = κ·W + ν`, `[propext, Quot.sound]`)
- `PQEquiv` — the easy halves proved (§4.27, `pqEquiv_of_hard : PQHard p → PQEquiv p`)

so **`PLL_UI` now rests on `PQHard` alone.**

`PQHard` survives its designed refutation candidate at fuels 1–6. The naive
per-state simultaneous induction is REFUTED on *both* halves (§4.27–§4.28).
Fuel monotonicity of both recursions is PROVED (WP11). §4.28 states the
obstruction exactly and proposes a derivation-level route plus an
`(antecedent, station-set)` design. **The decision on which route to take is
Matthew's and is pending.** WP12 was launched on his decision as a
refute-first campaign; check `docs/ui-ljfo-clause-table.md` §4.28 onward for
where it stands now.

---

## 1 · Where everything is

| what | where |
|---|---|
| repo | `fairflow/lax-logic-in-lean` (public) |
| Matthew's checkout | `/Users/matthew/Lean/Sources/lax-logic-in-lean` — **his**, do not push to it |
| this work's worktree | `/Users/matthew/gtd/worktrees/lax-logic-in-lean/dev-chapter` |
| branch | `blueprint-dev-chapter` (local ref `claude/blueprint-dev-chapter`) |
| the blueprint | `LaxBlueprint/` — nine chapters under `LaxBlueprint/Chapters/` |
| the other agent's branch | `frjw-dev` — **not yours to merge into**; open a PR and ask |

Standing rule from Matthew: **never push to his working directory.** Work in the
worktree; he pulls.

```bash
cd /Users/matthew/gtd/worktrees/lax-logic-in-lean/dev-chapter && git fetch origin && git status
```

Build and render locally (only when you actually need to — see §5):

```bash
cd /Users/matthew/gtd/worktrees/lax-logic-in-lean/dev-chapter && lake build LaxBlueprint && ./scripts/ci-pages.sh
```

Publish (manual only; `pages.yml` has **no** push trigger, so pushing is safe):

```bash
gh workflow run pages.yml --ref blueprint-dev-chapter
```

---

## 2 · State as of 2026-09-06 15:20

- **Branch tip:** `6e74a21`. Clean worktree.
- **Last successful publish:** `27fca24`, Pages run 34002828801, 2026-09-06 01:01,
  11 minutes. All twelve pages verified live by content, not just status code.
- **Unpublished on the branch:** three handoff-recording commits only
  (`d732570`, `b83d30b`, `6e74a21`). No chapter text changed since `27fca24`.
- **`frjw-dev` is nine commits ahead** and has moved a long way (WP11, WP12,
  §4.24–§4.28).

The job below was set for 05:00 on 2026-09-06 and **did not run** — an outage
took the session out overnight. It is still the job, but it must be re-planned
against the current `frjw-dev`, not the state it was written for.

---

## 3 · The job

**Step 1 — merge `frjw-dev`.** The only commit touching `LaxBlueprint/` is
`58eba3f`, in which the FRJW agent wrote all sixteen `TO WRITE` paragraphs
across UI, Tools, RN, FRJW and Development (+184/−43, prose only: no node
status changed, no `(lean := "...")` added or altered, no new nodes).

That agent **cannot build `LaxBlueprint`** (it pulls verso), so **the Pages run
is the only gate on that prose.** Their standing instruction: if a paragraph
breaks the build, revert *that paragraph*, not the commit, and tell them which.

**Step 2 — bring the UI chapter's statuses up to date.** It is badly stale, and
one item is worse than stale. Details and sources in §4.

**Step 3 — republish**, and verify by *content*, not by HTTP status. Note the
chapter pages are split into per-section sub-pages: the nodes live under e.g.
`…/Towards-uniform-interpolation/The-chain-to-uniform-interpolation/`, not on
the chapter page itself. Checking only the chapter page will show false misses.

---

## 4 · What the UI chapter now gets wrong

All verified against source on `origin/frjw-dev`, not taken from any agent's
summary. Re-verify before writing — these move daily.

### 4a. A vacuous theorem is published as a result — fix this first

The chapter's N3 node presents `hasUI_of_stabEq` as *"PROVED outright from the
two cofinality variables, `[propext, Quot.sound]`, no cut needed"*, and
contrasts it favourably with the backward direction for needing no cut.

§4.23 refuted the **literal** form of N1 in the kernel by six designed cells.
The ∀p attack row of a parked `Q ⊃ N ∈ done` at goal `↑Q` reproduces the same
call one fuel down, so the chain is strictly size-ascending and
`EStabEq`/`AStabEq` have **no instances at any saturated station with a retained
compound implication**. `literal_N1_dividing_line` packages all six: the
dividing line is saturation with a retained compound implication, not weight —
**which is exactly `hasUI_of_stabEq`'s own hypothesis.**

So that theorem is true, kernel-checked, and **has no instances**. It must be
restated, with `hasUI_of_stabilises` (interderivable form, through `cutInv`) put
in its place as the live result.

Two consequences in the same chapter:

- `FuelIrrelevance` is **MOOT** — its consumer's hypothesis is unsatisfiable
  there. The chapter lists it as a live obligation.
- The *"termination of the recursion"* reading of N4 (§4.19) is **dead**: the
  fuel is essential. Do not repeat that framing.

### 4b. Statuses that have moved

| node | chapter says | actually (source) |
|---|---|---|
| N0k | *node does not exist* | **PROVED** (§4.22), `LJF/OPolInv.lean`. Must be **added**. |
| N1 | both forms proved | **STATED**; literal forms **REFUTED** (§4.23) |
| N2 | DRAFTED | **STATED**, axiom-free |
| N3 | backward relative to `CutInv` | **PROVED both ways** (§4.22–§4.23) |
| N4 | OPEN both ways | ◯-free **PROVED**; PLL open, and now reduced to `PQHard` alone (§4.25–§4.28) |
| N5 | carries a `sorry` | **PROVED relative to N4** (§4.24) |
| N6 | relative to `CutInv` and `CellsFor` | **PROVED on IPC formulas**; **PROVED relative to N4 alone** in general (§4.24) |

`cutInv` pins at `[propext, Classical.choice, Quot.sound]`; the supporting block
`polInvT`/`polInvL`/`cutInvNE` at `[propext, Quot.sound]`.

Note `cutInv`'s `Classical.choice` is the `Type` packaging of a `Nonempty`
result through the `Prop`-valued bridge — a **different** source from
`atomMem_of_mem`'s, so WP1d will not clear it.

### 4c. The chapter preamble

It says *two* things are genuinely open, N4 and `CutInv`. Both halves are now
wrong: `CutInv` is proved, and N4 has been reduced to `PQHard`. Worth rewriting
around the much sharper true statement — **`PLL_UI` rests on `PQHard` alone.**

Also worth advertising: N6 is proved on IPC formulas and *agrees with*
`uniform_interpolation_IPC` up to interderivability (`routeB_agrees_IPC`),
tested against every `p`-free PLL formula, `◯` included. That is a real result
and the chapter does not mention it.

---

## 5 · Traps that have already cost time

**`{uses "..."}` works only INSIDE a node.** In a chapter's preamble it fails
with `uses declaration outside an informal enviroment` (sic). This was hit
twice; the second cost a 10-minute CI failure. In preamble text, name the node
in words. The cheat sheet in `Development.lean` has been corrected at source.

**An `(lean := "...")` attachment costs its module's whole IMPORT CLOSURE.** One
import line put `LJF/OFuelPFam.lean` on the blueprint's critical path — §4.20
measures it at **1463 s**, not because it is large but because the 17-way
`mutual` goes through `WellFounded.fix`; the same bodies as an `unsafe def`
compile in 3.0 s. Matthew had it reverted. **N0c and N0d are deliberately
unattached — that is a decision, not an oversight. Do not "fix" it.** Revisit
only after the structural refounding lands.

**Read status from the ledger in the source file, not from a `docs/*.md` plan.**
A plan is intent and ages badly; this put a stale "open" status on FRJW
completeness that was in fact closed.

**`#axioms_within` (`Meta/Audit.lean`), not `#print axioms` alone, is the repo's
checker.** Seven files under `LJF/` use it. Grepping for the wrong one produced
a false report of missing pins.

**Do not quote line counts.** The node table itself says `OFuelHeight.lean` is
873 lines; it is 1182. Quote statuses and read them from source.

**Quoting a source accurately is not the same as saying something true.** A
sentence taken verbatim from a docstring was published and overstated what was
left; the docstring was wrong too. Check the signature, not the prose.

**Do not compile a stack another agent is already compiling.** Ask what they are
building and offer to take it. Two worktrees do *not* share lake state
(separate inodes) — the cost is CPU contention. GitHub Actions is free and
unmetered for this public repo, so CI is usually the cheaper check.

---

## 6 · Coordination

The FRJW agent works `frjw-dev` and is the owner of `LJF/`. It cannot build
`LaxBlueprint`; you are its build gate. It does not touch `LaxBlueprint/` files
except when Matthew asks it to.

`frjw-dev` is **not yours to merge into**. Open a PR and ask.

**`SendMessage` may be unavailable.** After the overnight outage the messaging
layer re-registered every session with new names, refs and sockets, and this
session lost `SendMessage` — a *deferred* tool that the resumed session was not
re-offered. `ListAgents` (a static tool) still worked, so the session could see
peers but not reach them. If that happens: a freshly started session gets the
full deferred set. Until then, write to `HANDOFF.md` on the shared branch, which
the other agents read — but note that is pull, not push, and nobody is notified.

---

## 7 · Scope note from Matthew

The blueprint is **not** the right format for writing papers. It is designed for
large proof efforts needing a map every contributor can work from. For a paper,
use plain Verso: a `Manual`-genre document omitting the blueprint directives and
the `{blueprint_graph}` / `{blueprint_summary}` pages. Same framework, same
build, no porting.

The audience for this blueprint is co-developers and collaborators — Avi among
them — and the aim is an accessible, enjoyable presentation of the theory
without an overwhelm of detail.
