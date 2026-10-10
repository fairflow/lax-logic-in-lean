# HANDOVER: the blueprint docs role

**Start here** if you hold the docs role for the Verso documents in this
repository. Rewritten 2026-10-10; earlier versions are in git.

Published site: <https://fairflow.github.io/lax-logic-in-lean/>. The Blueprint
is at the root; the papers are under `/clp-paper/` and `/lax-paper/`, each with
a one-page version at `…/single/`.

This file covers only what is particular to the role. Three other documents
hold the rest, and are not repeated here:

| for | read |
|---|---|
| branches, worktrees, pull requests, Pages, the draft-PR protocol, asking before any build | `docs/github-with-claude-tutorial.md` (§2, §4, §7, Appendix A) |
| workflows, `lakefile.toml`, the verso pin, build decisions, why chapter titles are URLs | `LaxBlueprint/HANDOFF.md`, the infrastructure record |
| which notation exists and where it prints | the Notation chapter, `LaxBlueprint/Chapters/Notation.lean` |

---

## 1 · The role and its boundary

Matthew, 2026-09-06: *"the docs session owns the chapters; you stick to
infrastructure."* The docs role owns `LaxBlueprint/Chapters/*.lean` and this
file: chapter text, node statuses, prose, structure. It does not own the
workflows, `lakefile.toml`, the scripts or the verso pin. The LaxLogic manager
session merges pull requests and dispatches Pages.

The outer boundary, also Matthew, 2026-09-06:

> You should not be trying to contribute to theorem proving here, unless asked
> to on a different branch or topic.

The boundary blurs easily, because the job means reading a great deal of
mathematics.

**In scope:** reading the sources and rendering what they say as nodes; keeping
statuses, axiom pins and dependencies faithful; prose, structure, titles, links;
verifying what is published; and reporting a **documentation defect**, a page
claiming something its source does not support. That is a fault in this
artefact, not a mathematical judgement.

**Out of scope:** proposing, drafting or evaluating proofs; advocating a
refactor of someone else's development; owning or escalating mathematical
decisions. A status you read is input to be rendered, not a claim to
adjudicate. Where a source and a summary disagree, say so and leave it with the
owner. Crossing the line has looked like this: researching how a lemma might be
reproved, and headlining a handover with a pending mathematical decision.

**Blueprint or paper.** The Blueprint is a map of a large proof effort for
co-developers and collaborators, and should be an accessible presentation
without an overwhelm of detail. It is not the format for a paper. A paper is
plain Verso: `CLPPaper/` uses no blueprint directives at all; `LaxPaper/` keeps
the nodes and the dependency graph, and has no summary page (Matthew,
2026-10-09).

---

## 2 · Working method

Every change goes to `main` through a draft pull request (tutorial, Appendix A).
A change under `LaxBlueprint/**`, even to this file, runs the Pages build on the
pull request, and that build is the test. Do not build locally without asking
Matthew.

With no local build, review the markup before pushing:

```bash
# block balance: the two numbers must match, and match main's (a chapter with no nodes prints "/")
for f in LaxBlueprint/Chapters/*.lean; do
  awk -v f="$f" '/^:::[a-z]/{o++} /^:::$/{c++} END{print o"/"c, f}' "$f"; done
# a bare { in prose opens a Verso role: every hit must be a role, or inside backticks
git diff -U0 origin/main -- LaxBlueprint/Chapters | grep '^+[^+]' | sed -E 's/`[^`]*`//g' | grep '{'
```

and check by eye that every `{uses "x"}` sits inside a `:::` node and names a
node the file defines. Outside a node it fails the build with
`uses declaration outside an informal enviroment`; in a chapter preamble, name
the node in words.

After the manager publishes, verify the live pages by content (§5).

---

## 3 · Deriving status: from source, never from a summary

In order of authority:

1. **The ledger comments in the Lean source file.**
2. **The `#axioms_within` pins in the source**, the repository's checker
   (`Meta/Audit.lean`). Not `#print axioms` alone.
3. **`docs/status-ledger.jsonl`**: one line per declaration, with its module,
   axioms and `sorry` flag. The quickest way to confirm that a name exists and
   what it rests on.
4. For the uniform-interpolation route: `docs/ui-routeB-blueprint.md`, the node
   table, and `docs/ui-ljfo-clause-table.md`, the §-numbered record.

Never take a status from a `docs/*.md` plan, a commit message or another
session's report without checking it against these.

The search for uniform interpolation was **halted by Matthew on 2026-09-06**.
The UI chapter records the state at the halt. It is a stopped campaign, not
work in flight, and nothing here implies a relaunch.

**Three checks, each of which has caught a published defect:**

- *Is the theorem inhabited?* A node can be true, kernel-checked and empty.
  `hasUI_of_stabEq` was published as a result after a refutation had made its
  hypothesis unsatisfiable; `pll_ui_R_escD` became vacuous the same way. When
  anything turns REFUTED, ask which other nodes quantify over it.
- *Does the signature match the prose?* A sentence quoted from a docstring
  overstated what remained, because the docstring was wrong too. The docstring
  of `irregular_circ_imp_self_lifts` says "is a lift of a regular one"; the
  statement says only that a regular disproof exists. Write from the signature.
- *Does the attachment still exist?* `duality_hole` named a theorem withdrawn
  on 2026-09-01 and sat silently unattached on the live site for five weeks.
  Strict resolution (§4) now makes that a build error.

---

## 4 · Names and attachments

Two mechanisms decide what a signature shows. Keep them apart.

1. **The declaration's own name** (`theorem maehara`, not
   `theorem PLLND.SC.maehara`): `weak.verso.docstring.showNamespace = false` in
   `lakefile.toml`.
2. **Every name inside its type, and the notation:** the chapter's own `open`
   lines. Lean hands the file's open namespaces to the pretty-printer. The PLL
   chapters open `PLLND`, which also switches on the PLL notation and makes a
   plain `⊢` print for `PLLND.LaxND`; the decision-procedure chapter opens
   `FRJ FRJ.Gbu FRJ.Gbu.W PLLND`.

**For a new chapter or a new attachment:**

- Open the namespace of the declarations it attaches, after `open Informal`. Do
  not open a type's own namespace (`Form`, `Tm`): `Tm.app` reads better than
  `app`, and sibling types share constructor names.
- Write `(lean := "…")` as the shortest name that denotes exactly the intended
  declaration in that scope. Node labels show the name as written. Check the
  short form against the status ledger, against Lean's and the packages'
  top-level names, and against verso's own: `PLLND.Ne` and `PLLND.Sub` keep
  their prefix because Lean has `Ne` and `Sub`, and `PLLND.erase` because verso
  has `erase`.
- Set `verso.blueprint.externalCode.strictResolve true` before `#doc`. Without
  it an unresolved or ambiguous name is only a warning: the build stays green
  and the node silently loses its attachment and its status.
- Check what the attached declaration's module imports. An attachment costs its
  module's whole import closure. **N0c and N0d are deliberately unattached**
  (Matthew): attaching them puts `LJF/OFuelPFam.lean` on the build's critical
  path.

**What cannot be shortened**, so do not spend time on it: the Blueprint-Summary
page, which lists each declaration's canonical name whatever the chapter wrote;
the "Constructor" and "Extends" lines of structures; private constants, which
print as `PLLND.A✝`; and names the printer keeps long to avoid a clash
(`PLLND.Ne`, `PLLND.Sub`, `FRJ.Tag` against verso's `Tag`). FRJ defines no
notation for its formulas, so `◯(◯Z ⊃ Z)` prints as `(Z.circ.imp Z).circ`.

---

## 5 · Verifying the published site

Check content, not status codes.

- **The front page carries the deployed commit hash.** Compare it with
  `origin/main` first.
- **Nodes live on per-section sub-pages**, for example
  `Towards-uniform-interpolation/The-chain-to-uniform-interpolation/`, not on
  the chapter page. Links are written relative to the site root.
- **Count visible text only.** Verso puts every full name in a `data-binding`
  attribute, so a search of the raw HTML over-counts by a large factor.
- **Names inside displayed formulas are LaTeX-escaped**: search for
  `pll\_ui\_R`, not `pll_ui_R`.
- **To audit attachments**, search a Pages build log for `could not be resolved`
  and `is ambiguous`. There should be none.

Reference point, 2026-10-09, commit `b77bbee`: 95 fully qualified names in the
visible text of the Blueprint's 45 pages (Summary and Graph excluded), all
accounted for by §4's list and by names written out in prose. Earlier the same
day, before the chapters opened their namespaces, the count was 1,191.
