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
| **what you work in** | **whatever checkout your session has.** See below — you cannot inherit a previous session's worktree. |
| branch | `blueprint-dev-chapter` — this is the handover, not a path |
| the blueprint | `LaxBlueprint/` — nine chapters under `Chapters/` |
| the frontier | `frjw-dev`, the FRJW agent's branch. **Not yours to merge into**; open a PR and ask. |

**How a fresh session picks this up.** Not by finding a path. Claude Desktop
offers a worktree when a session starts: decline it and there is no worktree;
accept it and you get a *fresh* one, unrelated to any previous session's. Either
way you cannot take over the worktree the last session used, and taking one over
would not be a safe design even if it were possible.

So the handover is **the branch, on the remote** — which is why the previous
session's last duty is always to commit and push everything. Your first move:

```bash
git fetch origin && git checkout blueprint-dev-chapter && git pull --ff-only
```

and you are exactly where the last session left off.

```bash
lake build LaxBlueprint && ./scripts/ci-pages.sh
```

**Do not run that without asking.** Standing instruction from Matthew,
2026-09-06 17:00, given while stopping a build of exactly this kind:

> stop building. this is not needed. there's so much building on every agent
> going on, you now have to request permission to build.

Every agent on this machine compiles, and the contention is the cost he is
managing — not this build's own six minutes. So: no `lake build`, no
`ci-pages.sh`, no builds of any kind, without asking him first. That removes
the local check that used to catch markup errors, so the compensating
discipline is to review the markup statically before pushing:

```bash
awk '/^:::[a-z]/{o++} /^:::$/{c++} END{print o, c}' LaxBlueprint/Chapters/*.lean
grep -n '{uses' LaxBlueprint/Chapters/UI.lean   # every hit must be INSIDE a ::: node (§5)
```

and to check that every `{uses "x"}` names a node the file defines.

```bash
gh workflow run pages.yml --ref blueprint-dev-chapter
```

Publishing is manual only — `pages.yml` has **no** push trigger, so pushing is
always safe.

### The verso fork, and the fully-qualified names

`verso` is pinned to **`fairflow/verso @ v4.31.0-declsig-fix`**, a one-commit
fork fixing a shadowed `declSigWithId` parser that silently disabled
`showNamespace`/`constantInfo` in `Docstring.ppSignature`. The root-level
`[[require]]` sits *first*, ahead of `VersoBlueprint` and so ahead of `mathlib`
— that order is load-bearing (§5). It resolves and builds green.

**The site still renders fully-qualified names, and here is exactly why.** Trace
it once and it stays clear:

```
(lean := "FRJ.Gbu.W.gbuInv5")            in our chapter
  → VersoBlueprint/ExternalDeclRender.lean:523
        Verso.Genre.Manual.Signature.forName decl
  → verso/VersoManual/Docstring.lean:315
        Block.Docstring.ppSignature name (constantInfo := false)
  → ppSignature (c) (showNamespace : Bool := true) …        ← the default
```

So the signature block that a reader actually sees is produced by
`ppSignature` after all — the fork's fix **is** on our path, contrary to an
earlier note in this file. But the fix only makes `showNamespace` *work*;
`Signature.forName` never passes it, so it takes the default `true` and the
namespace is printed. The fork was **necessary and not sufficient**.

Completing it is a one-line change in *verso*, not verso-blueprint: have
`Signature.forName` pass `showNamespace := false`, or thread it through as a
parameter. That belongs to the prover-toolkit agent, who owns the fork.

Independently corroborated by that agent, 2026-09-06: *“the fork carries ONLY
the bug fix and not a `showNamespace` option. So declaration names stay fully
qualified.”* What the fork **did** change on this site, and it is real: a
declaration's own name in its own signature no longer carries a self-link
(`constantInfo := false` now works), and inductive constructors render
unqualified (`Docstring.lean:309` already passes `showNamespace := false`, which
now takes effect). So there *is* a call site passing the flag — just not the one
that prints the top-level declaration name.

A separate, smaller effect is already available to us with no fork change.
Verso-blueprint keeps two names per reference — `written` (the author's
spelling, displayed in the hover and summary panels) and `canonical` (resolved,
used for links), documented at `Data.lean:450`. Resolution goes through
`Lean.resolveGlobalName` under `MonadResolveName`, so it honours `open`.
**Measured on one node:** adding `open FRJ.Gbu.W` and writing
`(lean := "gbuInv5")` shortened four of six occurrences — all in the hover and
summary panels. The remaining ones are the rendered signature, which is the
`ppSignature` path above. Worth doing only if the signature is fixed too;
alone it makes the panels inconsistent with the signature beside them.

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

**Measured build costs.** A publish takes **11–13½ minutes**; locally, with a
warm closure, `lake build LaxBlueprint` is about **6–7 minutes** for 9050 jobs.
If a run looks like heading for 90 minutes, something has put
`LJF/OFuelPFam.lean` back in the import closure — see §5.

*Do not attribute variation inside that range to the CI cache.* An earlier
version of this file explained an 11 → 13½ minute difference as a cache miss
after a `lakefile.toml` edit. That was a guess dressed as a measurement. The
cache situation, checked against the API on 2026-09-06:

| cache | size | from |
|---|---|---|
| `lake-Linux-X64-…` ×4 | 2.59 GB each | `lean_action_ci.yml`, duplicated across two branches |
| `Linux-lake-packages-v1-…` | 2.68 GB | the Pages workflow |
| `Linux-lean-build-v1-…` | **0.07 GB** | the Pages workflow |

Total **13.11 GB against a 10 GB quota**, so eviction is continuous and the four
near-duplicate CI caches occupy 79% of it. The Pages caches do exist — the
prover-toolkit agent's report that they never persist is too strong — but the
Lean build cache is only 70 MB, because the cached paths (`.lake/build/lib`,
`.lake/build/ir`) cover the root package's own oleans and not `.lake/packages`.
So it carries far less than its name suggests. Treat CI timings as a range and
do not reason from warm-versus-cold.

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
3. **Do not build. Ask first.** See the standing instruction below. Push
   (always safe — `pages.yml` has no push trigger) and ask before publishing.
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
