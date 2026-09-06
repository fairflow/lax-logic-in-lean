# HANDOVER — the PLL Verso blueprint

**Start here.** Written 2026-09-06 for a session picking this up cold. Everything
needed is in this file; you should not need to reconstruct anything from a
previous conversation. For the blueprint's own technical decisions and traps,
see `LaxBlueprint/HANDOFF.md` alongside this.

Published site: <https://fairflow.github.io/lax-logic-in-lean/>

---

## 0 · What this session is for — read before anything else

**Your job is, almost exclusively, to document the frontier of this work —
currently on `frjw-dev` — as a Verso blueprint published to GitHub Pages.**

Matthew's instruction, 2026-09-06:

> You should not be trying to contribute to theorem proving here, unless asked
> to on a different branch or topic. Do not try to cross the boundary into
> FRJW's work any more.

That boundary is easy to blur, because doing this job well means reading a great
deal of live mathematics. The distinction that matters:

**In scope**

- Reading the ledgers and source files the FRJW agent maintains, and rendering
  what they say as blueprint nodes.
- Keeping node statuses, axiom pins and dependencies faithful to the source.
- Prose, structure, titles, links, the chapter set.
- Building and publishing the site, and being the build gate for chapter text
  (see §6).
- Reporting a **documentation defect** — a page claiming something its source
  does not support. That is a fault in your artefact, not a mathematical
  judgement.

**Out of scope**

- Proposing, drafting or evaluating proofs; suggesting how a lemma should be
  reproved; advocating a refactor of someone else's development.
- Owning, tracking or escalating mathematical decisions. Those are Matthew's,
  taken with the FRJW agent.
- Attaching declarations that pull expensive modules into the build (§5).

Status you read is **input to be rendered, not a claim to be adjudicated**. When
a source and a summary disagree, say so and let the owner resolve it.

---

## 1 · Where everything is

Standing rule from Matthew: **never push to his working directory.** Work in the
worktree; he pulls.

| what | where |
|---|---|
| repo | `fairflow/lax-logic-in-lean` (public) |
| Matthew's checkout | `/Users/matthew/Lean/Sources/lax-logic-in-lean` — **his**, do not push to it |
| this work's worktree | `/Users/matthew/gtd/worktrees/lax-logic-in-lean/dev-chapter` |
| branch | `blueprint-dev-chapter` (local ref `claude/blueprint-dev-chapter`) |
| the blueprint | `LaxBlueprint/` — nine chapters under `LaxBlueprint/Chapters/` |
| the frontier | `frjw-dev` — the FRJW agent's branch. **Not yours to merge into**; open a PR and ask. |

```bash
cd /Users/matthew/gtd/worktrees/lax-logic-in-lean/dev-chapter && git fetch origin && git status
```

Build and render locally — only when you actually need to; see §5 on contention:

```bash
lake build LaxBlueprint && ./scripts/ci-pages.sh
```

Publish. Manual only: `pages.yml` has **no** push trigger, so pushing is safe.

```bash
gh workflow run pages.yml --ref blueprint-dev-chapter
```

There is a second, separate blueprint effort for the prover toolkit
(`dolax-in-lean`), owned by the Lean prover-toolkit agent. It is not yours
either. One consequence worth remembering: two CI builds are independent and
parallel, whereas two local builds contend for the same cores.

---

## 2 · State as of 2026-09-06

- **Branch tip:** `92ab176`. Clean worktree.
- **Last successful publish:** `27fca24` — Pages run 34002828801, 11 minutes.
  All twelve pages verified by content, not just status code.
- **Unpublished:** record-keeping commits only. No chapter text has changed
  since the last publish.
- **`frjw-dev` is nine commits ahead** and moving fast (WP11, WP12, §4.24–§4.28).

A job set for 05:00 on 2026-09-06 did not run — an outage took the session out
overnight. It is still the job (§3), re-planned against the current `frjw-dev`.

**Cost, measured, so nobody guesses:** the pending merge changes **zero** files
in the blueprint's import closure — none in `LaxLogic/`, none in `FRJ/`, and
none of the six `wip/` files it imports. So there is nothing to rebuild below
the chapters, and a publish should run about **11 minutes**, as the last one
did. If a run looks like heading for 90, something has put `LJF/OFuelPFam.lean`
back in the closure; see §5.

---

## 3 · The job

**Step 1 — merge `frjw-dev`.** The only commit touching `LaxBlueprint/` is
`58eba3f`, in which the FRJW agent wrote all sixteen `TO WRITE` paragraphs
across UI, Tools, RN, FRJW and Development — prose only: no node status changed,
no `(lean := "…")` added or altered, no new nodes.

**Step 2 — bring the UI chapter's rendered statuses back into step with the
source.** It is stale, and one item is a documentation defect rather than
staleness. Details in §4.

**Step 3 — republish, and verify by content.** Not by HTTP status. Chapter pages
are split into per-section sub-pages: the nodes live under e.g.
`…/Towards-uniform-interpolation/The-chain-to-uniform-interpolation/`, not on the
chapter page itself. Checking only the chapter page shows false misses.

---

## 4 · Where the published chapter has drifted from its source

Read from the source on `origin/frjw-dev` and reported, not adjudicated.
Re-read before writing — these move daily, and the node table itself is
sometimes behind the files.

### 4a. A documentation defect, to fix first

The published N3 node presents `hasUI_of_stabEq` as *“PROVED outright from the
two cofinality variables, `[propext, Quot.sound]`, no cut needed”*, and contrasts
it favourably with the backward direction.

Per §4.23, the literal form of N1 is refuted and the dividing line —
saturation with a retained compound implication — **is exactly that theorem's own
hypothesis**, so it has no instances. The page therefore presents as an
achievement something the source does not support.

That is squarely a blueprint fault, and the one this artefact exists to prevent:
the whole claim of the thing is that status is *derived* rather than asserted.
Restate the node, and render `hasUI_of_stabilises` as the live result instead.

Two dependent renderings in the same chapter also need correcting: the page
lists `FuelIrrelevance` as a live obligation where the source marks it **MOOT**,
and it repeats a “termination of the recursion” reading of N4 that §4.19 has
withdrawn.

### 4b. Statuses that have moved

| node | page says | source says |
|---|---|---|
| N0k | *node does not exist* | PROVED (§4.22), `LJF/OPolInv.lean` — must be **added** |
| N1 | both forms proved | STATED; literal forms REFUTED (§4.23) |
| N2 | DRAFTED | STATED, axiom-free |
| N3 | backward relative to `CutInv` | PROVED both ways (§4.22–§4.23) |
| N4 | OPEN both ways | ◯-free PROVED; PLL open, reduced further at §4.25–§4.28 |
| N5 | carries a `sorry` | PROVED relative to N4 (§4.24) |
| N6 | relative to `CutInv` and `CellsFor` | PROVED on IPC formulas; PROVED relative to N4 alone (§4.24) |

`cutInv` pins at `[propext, Classical.choice, Quot.sound]`; the supporting block
`polInvT`/`polInvL`/`cutInvNE` at `[propext, Quot.sound]`.

### 4c. The chapter preamble

It says two things are genuinely open, N4 and `CutInv`. Both halves have moved:
`CutInv` is proved, and N4 has been reduced further since. **Read the current
reduction out of `docs/ui-routeB-blueprint.md` and the clause table at the time
of writing, and render that** — do not copy a chain of reasoning from here or
from any agent's message, and do not present the open question as something this
session tracks. It is the FRJW agent's, and the decisions about it are Matthew's.

Also currently unmentioned and worth rendering: N6 is proved on IPC formulas and
agrees with `uniform_interpolation_IPC` up to interderivability
(`routeB_agrees_IPC`), tested against every `p`-free PLL formula, `◯` included.

---

## 5 · Traps that have already cost time

**`{uses "…"}` works only inside a node.** In a chapter preamble it fails with
`uses declaration outside an informal enviroment` (sic). Hit twice; the second
cost a 10-minute CI failure. In preamble text, name the node in words. The cheat
sheet in `Development.lean` has been corrected at source.

**An `(lean := "…")` attachment costs its module's whole import closure.** One
import line put `LJF/OFuelPFam.lean` on the critical path and took a publish from
11 minutes to 90+. **N0c and N0d are deliberately unattached — a decision of
Matthew's, not an oversight. Do not “fix” it.** More generally: before attaching
anything, check what the import drags in, not merely that the build passes.

**Read status from the ledger in the source file, not from a `docs/*.md` plan.**
A plan is intent and ages badly; this put a stale “open” status on FRJW
completeness that was in fact closed.

**`#axioms_within` (`Meta/Audit.lean`) is the repo's checker, not `#print axioms`
alone.** Seven files under `LJF/` use it; grepping for the wrong one produced a
false report of missing pins.

**Do not quote line counts or other volatile figures.** The node table itself
says `OFuelHeight.lean` is 873 lines; it is 1182. Render statuses, and read them
from source.

**Quoting a source accurately is not the same as saying something true.** A
sentence taken verbatim from a docstring was published and overstated what
remained; the docstring was wrong too. Check the signature, not the prose.

**Do not compile a stack another agent is already compiling.** Ask what they are
building and offer to take it. Two worktrees do *not* share lake state (separate
inodes) — the cost is CPU contention. GitHub Actions is free and unmetered for
this public repo, so CI is usually both cheaper and less disruptive.

---

## 6 · Coordination, and the boundary in practice

The FRJW agent owns `frjw-dev` and `LJF/`. It **cannot build `LaxBlueprint`**
(that pulls verso), so **you are its build gate** for any chapter text it writes.
Its standing instruction: if a paragraph breaks the build, revert *that
paragraph*, not the commit, and tell it which.

`frjw-dev` is not yours to merge into. Open a PR and ask.

What crossing the boundary looked like in practice, so it is recognisable: this
session researched a lemma's proof and drafted a proposal for how to reprove it,
and headlined a handover with a pending mathematical decision as though it
tracked it. Both were over the line even though the second-hand material was
accurate. Report what the source says; leave what to do about it to its owner.

**`SendMessage` may be unavailable.** After an outage the messaging layer
re-registered every session with new names, refs and sockets, and this session
lost `SendMessage` — a *deferred* tool the resumed session was not re-offered.
`ListAgents`, a static tool, still worked, so the session could see peers but not
reach them. A freshly started session gets the full deferred set. Until then,
write to `HANDOFF.md` on the shared branch, which the other agents read — but
that is pull, not push, and nobody is notified.

---

## 7 · Scope note from Matthew

The blueprint is **not** the right format for writing papers. It is designed for
large proof efforts needing a map every contributor can work from. For a paper,
use plain Verso: a `Manual`-genre document omitting the blueprint directives and
the `{blueprint_graph}` / `{blueprint_summary}` pages. Same framework, same
build, no porting.

The audience is co-developers and collaborators — Avi among them — and the aim is
an accessible, enjoyable presentation of the theory without an overwhelm of
detail.
