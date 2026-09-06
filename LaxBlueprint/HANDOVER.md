# HANDOVER — the PLL Verso blueprint

**Start here.** Rewritten 2026-09-06 16:20 BST for a session picking this up
cold. You should not need to reconstruct anything from a previous conversation.
For the blueprint's own build decisions, see `LaxBlueprint/HANDOFF.md`.

Published site: <https://fairflow.github.io/lax-logic-in-lean/>

---

## 0 · What this session is for — read before anything else

**Your job is, almost exclusively, to document the frontier of this work —
currently on `frjw-dev` — as a Verso blueprint published to GitHub Pages.**

Matthew's instruction, 2026-09-06:

> You should not be trying to contribute to theorem proving here, unless asked
> to on a different branch or topic. Do not try to cross the boundary into
> FRJW's work any more.

The boundary blurs easily, because doing this job well means reading a great
deal of live mathematics. The distinction that matters:

**In scope** — reading the ledgers and source files the FRJW agent maintains and
rendering what they say as blueprint nodes; keeping statuses, axiom pins and
dependencies faithful; prose, structure, titles, links, chapter set; building
and publishing; being the build gate for chapter text (§6). Also in scope:
reporting a **documentation defect** — a page claiming something its source does
not support. That is a fault in your artefact, not a mathematical judgement.

**Out of scope** — proposing, drafting or evaluating proofs; suggesting how a
lemma should be reproved; advocating a refactor of someone else's development;
owning, tracking or escalating mathematical decisions; attaching declarations
that pull expensive modules into the build (§5).

Status you read is **input to be rendered, not a claim to adjudicate.** Where a
source and a summary disagree, say so and leave it with the owner.

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
| the blueprint | `LaxBlueprint/` — nine chapters under `Chapters/` |
| the frontier | `frjw-dev`, the FRJW agent's branch. **Not yours to merge into**; open a PR and ask. |

```bash
cd /Users/matthew/gtd/worktrees/lax-logic-in-lean/dev-chapter && git fetch origin && git status
```

```bash
lake build LaxBlueprint && ./scripts/ci-pages.sh
```

```bash
gh workflow run pages.yml --ref blueprint-dev-chapter
```

Publishing is manual only — `pages.yml` has **no** push trigger, so pushing is
always safe.

`verso` is pinned to **`fairflow/verso @ v4.31.0-declsig-fix`**, a one-commit
fork fixing a shadowed `declSigWithId` parser that silently disabled
`showNamespace`/`constantInfo` in `ppSignature`. The root-level `[[require]]`
sits *first*, ahead of `VersoBlueprint` and so ahead of `mathlib` — that order
is load-bearing (§5). It resolves and builds green. **It makes no visible
difference to this site**, because these chapters carry no `{docstring}` blocks;
attachments render through blueprint's own `bp_external_decl_*` classes, not
through `ppSignature`. Correct to carry, but do not expect it to change
anything here.

A second, separate blueprint effort exists for the prover toolkit
(`dolax-in-lean`), owned by the Lean prover-toolkit agent. Not yours. One
practical consequence: two CI builds are independent and parallel, whereas two
local builds contend for the same cores.

---

## 2 · State

- **Published and verified**, 2026-09-06 16:17. All twelve pages 200, contents
  checked by text and not merely by status code.
- **Zero `TO WRITE` markers** remain anywhere in the chapter set. 100 nodes, 68
  Lean-backed.
- **Nothing is pending.** No unpublished chapter text.

**Measured build costs, so nobody guesses.** With the import closure warm and
the lakefile unchanged, a publish is **11 minutes**; the run that also rebuilt
verso from the fork after a `lakefile.toml` change took **13m23s**. Locally, with
a warm closure, `lake build LaxBlueprint` is about **6 minutes** for 9050 jobs.
If a run looks like heading for 90 minutes, something has put
`LJF/OFuelPFam.lean` back in the import closure — see §5.

**The one fact that shapes this job:** `frjw-dev` moves several commits a day.
It went eleven commits ahead within hours of the last merge. Any list of
statuses written into a document is stale almost immediately — which is why §4
below is a procedure and not a table. The previous version of this file carried
such a table and it was obsolete inside four hours.

---

## 3 · The standing job

There is no one-off task list. The job is a loop:

1. `git fetch origin`, see how far `frjw-dev` has moved, merge it.
2. Re-derive current status from source (§4) and re-render the affected nodes.
3. Build locally if the machine is free — it catches markup errors that would
   otherwise cost a CI round trip — then push and publish.
4. Verify the live pages **by content**. Chapter pages split into per-section
   sub-pages: nodes live under e.g.
   `…/Towards-uniform-interpolation/The-chain-to-uniform-interpolation/`, not on
   the chapter page. Checking only the chapter page shows false misses.

---

## 4 · How to re-derive status — do this, don't trust a snapshot

**The sources of truth, in order:**

1. **The ledger comments in the Lean source file itself.** Highest authority.
2. **`#axioms_within` pins in the source** — the repo's checker, in
   `Meta/Audit.lean`. Not `#print axioms` alone (§5).
3. **`docs/ui-routeB-blueprint.md`** — the maintained node table. Good for the
   shape; it can lag the files, and it carries at least one stale figure.
4. **`docs/ui-ljfo-clause-table.md`** — the running record, §-numbered. The
   narrative and the reasoning.

**Never** take a status from a `docs/*.md` **plan**, or from an agent's message,
without checking it against 1–3.

Useful invocations:

```bash
grep -E '^\| N[0-9a-z]+ ' docs/ui-routeB-blueprint.md      # the node table rows
grep -n '^### 4\.' docs/ui-ljfo-clause-table.md | tail -20 # what has landed lately
grep -rE '^#axioms_within' LJF/ wip/                        # the pins, as measured
```

**Two checks that have caught real defects:**

*Is the theorem inhabited?* A node can be true, kernel-checked and **empty**. The
published N3 once presented `hasUI_of_stabEq` as a result when a refutation
elsewhere had made its hypothesis unsatisfiable — the dividing line was exactly
that theorem's own hypothesis. Pins being right does not make a statement
non-vacuous. When a status changes to REFUTED anywhere, ask which other nodes
quantify over what was just refuted.

*Does the signature match the prose?* A sentence quoted verbatim from a docstring
was published and overstated what remained, because the docstring was wrong too.
Read the signature, not the surrounding words.

---

## 5 · Traps that have already cost time

**`{uses "…"}` works only inside a node.** In a chapter preamble it fails with
`uses declaration outside an informal enviroment` (sic). Hit twice; the second
cost a 10-minute CI failure. In preamble text, name the node in words. The cheat
sheet in `Development.lean` has been corrected at source.

**An `(lean := "…")` attachment costs its module's whole import closure.** One
import line put `LJF/OFuelPFam.lean` on the critical path and took a publish from
11 minutes to 90+ — not because the module is large, but because a 17-way
`mutual` goes through `WellFounded.fix`; the same bodies as an `unsafe def`
compile in 3 seconds. **N0c and N0d are deliberately unattached — Matthew's
decision, not an oversight. Do not “fix” it.** Before attaching anything, check
what the import drags in, not merely that the build passes.

**`[[require]]` order in `lakefile.toml` is load-bearing.** `VersoBlueprint` must
precede `mathlib`, or lake refuses with `mathlib: failed to fetch cache`; the
`verso` fork require sits ahead of both. Editing `lakefile.toml` also misses the
CI cache key *and* the first restore-key, so it forces a rebuild.

**`#axioms_within` is the checker, not `#print axioms` alone.** It lives in
`Meta/Audit.lean`; seven files under `LJF/` use it. Grepping for the wrong one
produced a false report of missing pins.

**Do not quote line counts or other volatile figures.** The node table says
`OFuelHeight.lean` is 873 lines; it is 1182.

**Do not compile a stack another agent is already compiling.** Ask what they are
building and offer to take it. Two worktrees do *not* share lake state (separate
inodes) — the cost is CPU contention. Actions is free and unmetered for this
public repo, so CI is usually both cheaper and less disruptive. If a build in
Matthew's checkout is grinding, the usual cause is that it is behind: pull first.

**Re-fetch before pushing.** Matthew pushes to this branch himself. A push was
rejected non-fast-forward mid-job because his verso pin had landed in between.
Merge and re-push; do not force.

---

## 6 · Coordination

The FRJW agent owns `frjw-dev` and `LJF/`. It **cannot build `LaxBlueprint`**
(that pulls verso), so **you are its build gate** for chapter text it writes. Its
standing instruction: if a paragraph breaks the build, revert *that paragraph*,
not the commit, and tell it which.

`frjw-dev` is not yours to merge into. Open a PR and ask.

What crossing the boundary looked like, so it stays recognisable: this session
researched a lemma's proof and drafted a proposal for how to reprove it, and
headlined a handover with a pending mathematical decision as though it tracked
it. Both were over the line even though the material was accurate. Report what
the source says; leave what to do about it to its owner.

**`SendMessage` may be unavailable.** After an outage the messaging layer
re-registered every session with new names, refs and sockets, and this session
lost `SendMessage` — a *deferred* tool the resumed session was not re-offered.
`ListAgents`, a static tool, still worked, so peers were visible but not
reachable. A freshly started session gets the full deferred set. Until then,
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
