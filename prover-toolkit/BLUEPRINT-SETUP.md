# Adding a Verso Blueprint to an existing Lean + Mathlib development

Repository-independent, like the rest of `prover-toolkit/`: nothing here
depends on `lax-logic-in-lean`. It is a short list of the things that are
not in the upstream docs and that cost time to discover.

[Verso](https://verso.lean-lang.org/) is the Lean FRO's documentation
system; documents are Lean programs, so every code reference is checked by
the compiler. [`verso-blueprint`](https://github.com/leanprover/verso-blueprint)
layers proof-blueprint blocks, a dependency graph and a progress summary on
top of Verso's `Manual` genre. Upstream's `project_template/` is the right
starting point for a *new* project. This file is about grafting one onto a
development that already exists.

---

## 1. Match the toolchain before you consider bumping it

`verso-blueprint` keeps **one branch per Lean toolchain**: `v4.28.0`,
`v4.29.0`, … Check for a branch matching your `lean-toolchain` first.

```bash
curl -s https://api.github.com/repos/leanprover/verso-blueprint/branches?per_page=100 \
  | grep '"name"' | grep -E 'v4\.[0-9]+\.[0-9]+'
```

Only the newest two or so are release targets (see `branch-policy.json` on
the default branch); older ones are unmaintained but present and they build.
Taking the matching branch avoids a toolchain bump of the whole development,
which on a Mathlib project is a campaign in itself.

## 2. `require` order: VersoBlueprint BEFORE mathlib

This is the one that stops you dead. Adding VersoBlueprint after `require
mathlib` fails:

```
Warning: your project pins different versions of some dependencies than Mathlib.
This will cause `lake exe cache get` to compute wrong hashes.

  proofwidgets:
    project: 2db6054a4432
    mathlib: 24b0d9dc081c

error: mathlib: failed to fetch cache
```

Lake's own suggestion is the fix: **put `require mathlib` last so Mathlib's
pins win.** In `lakefile.toml` that means inserting the VersoBlueprint block
*above* the existing mathlib block, which is a pure insertion and therefore
merges cleanly across branches:

```toml
[[require]]
name = "VersoBlueprint"
git = "https://github.com/leanprover/verso-blueprint"
rev = "v4.31.0"          # the branch matching YOUR lean-toolchain

[[require]]
name = "mathlib"
scope = "leanprover-community"
rev = "v4.31.0"
```

Verso then compiles against Mathlib's `proofwidgets` rather than its own pin.
Verify after `lake update` that no existing pin moved:

```bash
git diff lake-manifest.json | grep '^[-+].*"rev"'
```

## 3. Keep verso out of the ordinary build

Declare the blueprint as its own `lean_lib` and leave it **out of
`defaultTargets`**:

```toml
[[lean_lib]]
name = "MyBlueprint"     # NOT added to defaultTargets
```

A `[[require]]` is not an import. Lake builds targets, so verso is compiled
only when a target that imports it is built. On a development of ~8900 Lake
jobs, adding the require changed the ordinary build not at all: `lake build`
of the main library still completed from cache without verso entering the
target graph.

## 4. Attach declarations, or the blueprint lies

A blueprint whose nodes carry no Lean attachment reports:

```
Total entries 13.  Informal-only entries 13.  completed: 0.
```

It still renders graphs, progress bars and numbered theorems, so it **looks**
authoritative while every status in it is asserted by the author. That is
worse than having no blueprint. Attaching six declarations on one development
moved it to `informal-only 7, completed 3, deps incomplete 3, no proof 3` —
with "deps incomplete" propagating upward from open nodes automatically,
which is the whole point of the tool.

## 5. Write the prose once, at the declaration, without importing verso

There are two ways to connect a node to Lean, and the difference that matters
is **which way the import points**.

```lean
-- In the blueprint chapter.  Import direction: blueprint -> development.
import MyProject.Sound          -- the development does NOT import verso

:::theorem "soundness" (lean := "MyProject.soundness")
The informal statement.
:::

{docstring MyProject.soundness}    -- the declaration's own docstring, verbatim
```

versus

```lean
-- In the development's own file.  Import direction: development -> verso.
import VersoBlueprint             -- now verso is in this file's import closure
@[blueprint "soundness" (autoDeps := true)]
theorem soundness : … := …
```

`{docstring Name}` is a `VersoManual` block command that reads the docstring
out of the *environment*, so the first form already gives you text written
once at the declaration, reproduced verbatim in the document, with pressure
to document properly (`verso.docstring.allowMissing := false` turns a missing
docstring into an error). It does this **without** putting verso into the
development's import graph.

`@[blueprint]` adds only that the node is Lean-owned (no informal block
needed) and `autoDeps` edge inference. Weigh that against the consequence:
imports propagate *downstream*, so tagging a **core** module puts verso in
the import closure of everything above it. The compiled artifacts are cached,
so this is not a recompile cost; the cost is that a verso version bump then
invalidates the whole development, and every downstream module loads verso's
environment. Tagging a leaf module contains both. If you use the attribute at
all, prefer leaves.

## 6. `vbp` derives its target from the PACKAGE name

`lake exe vbp build` assumes the package name is the blueprint library's root
module. On a project called something else it fails with:

```
error: unknown module `[anonymous]`
vbp build: package OLean build failed with exit code 1: lake build +<pkg>:olean
```

There is no flag to redirect it. Run the command `vbp` runs internally
(documented in upstream `doc/GETTING_STARTED.md`):

```bash
lake build MyBlueprint
lake lean MyBlueprintMain.lean -- --run MyBlueprintMain.lean --output _out/site
```

Add `--pdf` for `_out/site/pdf/main.pdf` (needs a `lualatex`-compatible
command on PATH). PDF is a static path: prose, math with your TeX preludes,
citations and bibliography render; blueprint chips, folding and hover are
static; the dependency graph and progress summary degrade to a notice
pointing at the HTML.

## 7. GitHub Pages

Two independent settings, both easy to miss:

* **Pages must be enabled with source "GitHub Actions"**, or the workflow
  fails at `actions/configure-pages` with `Get Pages site failed`. This
  happens at step two, before any Lean build, so a misconfigured repository
  costs nothing but a red tick.
* **The `github-pages` environment restricts deployment branches** to the
  default branch. To publish from another branch, change that policy under
  Settings → Environments → github-pages → Deployment branches and tags.

Scope the workflow triggers narrowly. If the blueprint imports development
modules, watching `**/*.lean` will fire it on nearly every commit; watch the
blueprint's own paths plus `workflow_dispatch` and re-run by hand after a
merge that changes proof status.

## 8. Editing

Verso documents are ordinary `.lean` files, so the Lean extension works with
no special setup: the `#doc` block is elaborated, and malformed markup or an
unresolved label is an inline error. Two things the linter enforces that are
easy to get wrong: bold is `*text*`, not `**text**`, and `effort` accepts only
`small` / `medium` / `large` — there is deliberately no `done`, because status
is derived from the code, not claimed by the author.

Labels are the only real commitment. Upstream's advice is right: choose them
early and treat them as stable project identifiers. Prose, chapters, groups
and ordering are all cheap to change afterwards. Labels are a flat namespace,
independent of module paths, so depth in the directory tree is not a
constraint; the constraint is the blueprint document's import closure, which
is also its build cost.
