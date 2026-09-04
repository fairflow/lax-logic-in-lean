# HANDOFF — the Verso Blueprint

Written 2026-09-04/05. Covers everything under `LaxBlueprint/`, the Pages
workflows, and the `lakefile.toml` change that supports them.

---

## What exists

**Published site:** https://fairflow.github.io/lax-logic-in-lean/
Three chapters, 29 nodes, 19 of them Lean-backed. Public repository, so the
site and its source links work for anyone.

**Branches**

| Branch | Contents |
|---|---|
| `main` | ONLY the lakefile require + the two Pages workflows. Landed low on purpose so every branch inherits rather than conflicts. |
| `blueprint-dev-chapter` | the blueprint itself. Currently the publishing branch. |
| `frjw-dev` | carries the earlier blueprint commits; does NOT have the Development chapter. |
| `verso-blueprint` | superseded. Stale workflow, older base. Delete it. |

**Open PRs:** #17 (portable recipe → `tooling`). #18 is closed.

**Files**

```
LaxBlueprint.lean                     root module
LaxBlueprint/Blueprint.lean           assembles chapters; {include} order sets chapter order
LaxBlueprint/Chapters/Overview.lean
LaxBlueprint/Chapters/FRJW.lean       the FRJW campaign, W1–W6
LaxBlueprint/Chapters/Development.lean  syntax → ND → semantics → completeness
LaxBlueprintMain.lean                 generator entry point
scripts/ci-pages.sh                   local render; publishes nothing
.github/workflows/pages.yml           manual-dispatch only
.github/workflows/blueprint-pages.yml reusable build+deploy
```

---

## The five decisions, and why

**1. `require VersoBlueprint` comes BEFORE `require mathlib`.** Reversed, lake
refuses with `mathlib: failed to fetch cache`, because verso pins
`proofwidgets` at `2db6054a4432` and mathlib at `24b0d9dc081c`. Putting
mathlib last makes mathlib's pins win. Adding the block *above* the mathlib
block is a pure insertion, which is why it merged across branches that touch
`lakefile.toml` in 117 commits without conflict.

**2. `LaxBlueprint` is NOT in `defaultTargets`.** A `[[require]]` is not an
import: lake builds targets, so verso is compiled only when a target that
imports it is built. Measured: `lake build LaxLogic` ran 49s from cache with
verso absent from the target graph, and `lake update` moved no existing pin.

**3. The import runs ONE WAY.** `LaxBlueprint/*` imports `LaxLogic.*` and
`FRJ.*`; no file of the development imports verso. This is the load-bearing
decision. The alternative, `@[blueprint "label"]` attributes on declarations,
would reverse the arrow — and on a *core* module that puts verso in the
import closure of everything downstream, so a verso version bump would
invalidate the whole development. `(lean := "...")` gets the same result with
the arrow pointing the safe way.

**4. Publishing is manual only.** `pages.yml` has no `push:` trigger at all.
No commit to any branch can deploy. `pull_request` is kept because it builds
without deploying (`github.event_name != 'pull_request'` guards the deploy
job), so a PR is a free check. Publishing is `gh workflow run pages.yml --ref
<branch>`. This was chosen over path filters because a merge would otherwise
be a publication act, which is a surprising property for a merge to have.

**5. Status is derived, never asserted.** Every node carries
`(lean := "Decl.Name")`. `effort` accepts only small/medium/large — there is
deliberately no `done`, because effort is the author's estimate and status is
the compiler's. A blueprint whose nodes carry no Lean attachment reports
`informal-only, completed: 0` while rendering authoritatively, which is worse
than no blueprint at all.

---

## Traps

**`{docstring X}` is almost always redundant.** `(lean := "X")` already
renders kind, file, status chip, signature, constructors/fields AND the
docstring. Twenty `{docstring}` commands were removed from
`Development.lean` for exactly this reason. Verified by experiment: removing
them left the rendering unchanged.

**Missing docstrings: error vs warning.**

    {docstring X}   on an undocumented X  ->  ERROR, build fails
    (lean := "X")   on an undocumented X  ->  warning, build passes

So `set_option verso.docstring.allowMissing` is only needed if you use
explicit `{docstring}` blocks. It is not in the source now.

**`lake exe vbp build` does not work here.** `vbp` derives its Lean target
from the PACKAGE name (`lax-logic`), not the blueprint library, and fails
with `unknown module [anonymous]`. `scripts/ci-pages.sh` runs the command vbp
runs internally.

**Chapter order comes from `{include 0 ...}`, not from import order.**
Reordering the imports changes nothing on the page.

**`gh` needs the right repo.** This clone has two remotes and `gh` picked
`AviCraimer/lax-logic-in-lean`. `gh repo set-default fairflow/lax-logic-in-lean`
fixes it; otherwise pass `-R fairflow/lax-logic-in-lean`.

**Pages needs two separate settings**, both already done: source = GitHub
Actions, and the `github-pages` environment's deployment-branch policy, which
defaults to the default branch only. Allowed branches are currently
`frjw-dev`, `main`, `publication/core`, `verso-blueprint`,
`blueprint-dev-chapter`.

**Fresh-worktree recipe.** `cp -Rc <root>/.lake .lake` needs
`VersoBlueprint`, `illuminate` and `verso-slides` present in the root's
`.lake/packages`. They were missing after the lakefile change and have been
copied in; if a fresh worktree starts cloning over the network, that is why.

---

## Measurements

| | |
|---|---|
| CI build, both caches cold | 8 min: 2m04 mathlib cache + 4m52 for 1324 jobs |
| Local build, offline | 127s, 1324 jobs |
| `lake build LaxLogic` for comparison | 8678 jobs |
| Cost to ordinary builds | none; verso not in `LaxLogic`'s target graph |

1324 not 8678, because the cost is the blueprint's **import closure**, not the
development. That is also the lever: the blueprint's build cost is exactly the
set of modules its chapters import, so it is a curation decision rather than a
technical limit.

---

## Undocumented declarations the build surfaces

All warnings, none blocking. Constructors and fields are deliberately left
undocumented — they are self-explanatory to a reader in the field.

| Declaration | Undocumented |
|---|---|
| `PLLProof` | the type, and all 3 constructors |
| `PLLND.LaxND` | all 12 constructors (the type is documented) |
| `PLLND.IPLND` | all 10 constructors (the type is documented) |
| `PLLND.ConstraintModel` | `W`, `refl_i`, `trans_i`, `refl_m`, `trans_m`, `hered_F`, `hered_V` |

`PLLFormula` was documented on 2026-09-04 and no longer appears here.

---

## What is NOT done

- **Every node body is a `TODO` stub.** The structure, labels and wiring are
  settled; the mathematics is not written.
- **The Development chapter is not on `frjw-dev`.** It is one commit on
  `blueprint-dev-chapter`, a clean merge whenever wanted.
- **Chapter order** is Overview → FRJW → Development. Swapping the last two
  `{include 0 ...}` lines in `Blueprint.lean` reorders them.
- **`verso-blueprint` branch** should be deleted.

---

## A scoping note (Matthew, 2026-09-05)

The blueprint is not the right format for writing papers. It is designed for
large proof efforts that need a map every contributor can work from. For a
paper, use plain Verso: a `Manual`-genre document that omits the blueprint
directives and the `{blueprint_graph}` / `{blueprint_summary}` pages. Same
framework, same build, no porting — a paper and a blueprint differ only in
which blocks they use.

Worth recording alongside that: an interactive object is more useful than a
static paper, and this is the first artefact in the repository where the
document's claims about proof status are checked rather than asserted.
