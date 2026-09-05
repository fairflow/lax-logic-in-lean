# HANDOFF — the Verso Blueprint

Written 2026-09-04/05. Covers everything under `LaxBlueprint/`, the Pages
workflows, and the `lakefile.toml` change that supports them.

---

## What exists

**Published site:** https://fairflow.github.io/lax-logic-in-lean/
Nine chapters, 98 nodes, 68 of them Lean-backed. Public repository, so the
site and its source links work for anyone.

**Branches**

| Branch | Contents |
|---|---|
| `main` | ONLY the lakefile require + the two Pages workflows. Landed low on purpose so every branch inherits rather than conflicts. |
| `blueprint-dev-chapter` | the blueprint itself. Currently the publishing branch. |
| `frjw-dev` | merged in during the assembly pass; does NOT yet have the assembled chapters back. |
| `verso-blueprint` | superseded. Stale workflow, older base. Delete it. |

**Open PRs:** #17 (portable recipe → `tooling`). #18 is closed.

**Files**

```
LaxBlueprint.lean                         root module
LaxBlueprint/Blueprint.lean               assembles chapters; {include} order sets chapter order
LaxBlueprint/Chapters/Overview.lean       the map, and how to read it
LaxBlueprint/Chapters/Development.lean    syntax → ND → semantics → completeness
LaxBlueprint/Chapters/Terms.lean          the proof-term calculus, Tm
LaxBlueprint/Chapters/Normalisation.lean  normal forms and confluence
LaxBlueprint/Chapters/StrongNorm.lean     strong normalisation
LaxBlueprint/Chapters/FRJW.lean           "The decision procedure" — Gbu◯ and FRJW as one object
LaxBlueprint/Chapters/UI.lean             towards uniform interpolation, Route (B)
LaxBlueprint/Chapters/RN.lean             "The variable-free fragment" — RN(◯,∅)
LaxBlueprint/Chapters/Tools.lean          the instruments
LaxBlueprintMain.lean                     generator entry point
scripts/ci-pages.sh                       local render; publishes nothing
.github/workflows/pages.yml               manual-dispatch only
.github/workflows/blueprint-pages.yml     reusable build+deploy
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

- **15 `TO WRITE` markers remain**, down from 64. Each is a judgement call
  that is Matthew's, not an agent's: whether to inline the Hasse diagram,
  which worked example to show whole, how much of a proof to reproduce.
  `TODO` was renamed to `TO WRITE` throughout so a marker is unambiguously a
  writing task and never a programming one.
- **The `#print axioms` pins in the UI chapter are asserted, not verified.**
  N0a and N0h are recorded as `[propext, Quot.sound]` in the node table, but
  neither declaration carries a pin and none was found elsewhere. Under the
  standing rule that `#print axioms` is the only recognised checker, those two
  statuses are hearsay. Another agent is sweeping the results; the pins will
  come out of that.
- **The chapter is not on `frjw-dev`.** It lives on `blueprint-dev-chapter`
  and is intended to merge there.

---

## Two corrections worth not repeating

Both were mine, both cost a rebuild, and both have the same shape: a source
that *looked* authoritative was not.

**1. Status read from a plan, not from the source.** The first FRJW chapter
recorded completeness as open because it took W4–W6 from `docs/frjw-plan.md`
— a plan written *before* the work landed. The authoritative ledger is the
comment block in `FRJ/Gbu/Circ.lean`, which records Theorems 8, 9 and 10 as
CLOSED. Rule: **for status, read the ledger in the source file; a `docs/*.md`
plan is a statement of intent and ages badly.**

**2. A chapter written from the name rather than the object.** The RN chapter
opened by describing a finite drawable lattice on a single variable. Matthew:
*"complete nonsense. It's infinite, doesn't fit on any page. Computations
generally infinite too. There is no single variable, that's what ∅ in
RN(◯,∅) means."*

The facts, now in the chapter:

- `RN(◯,∅)` is the **variable-free** fragment — `∅` is the empty set of
  variables. Formulas from `⊥`, the connectives and `◯`, up to
  interderivability.
- It is **infinite in three independent ways**: height, depth and width. Pure
  RN is the *one-variable* fragment of IPC — a ladder, infinite in height but
  of width ≤ 2, and drawable. That contrast is the whole interest of the
  object, and inheriting the name obscures it.
- What is finite is the **ρ-catalogue** (462 cells, 22 representatives, 37
  cover edges). Catalogue and fragment must be kept apart; the section
  headings now enforce it.
- Against the infinitudes, one sharp bound: `neg_exactly_four` — the
  booleanization has exactly four elements, over an arbitrary axiom set.

Notation: **`RN(◯,∅)`**, not `RN(◯)` and not `RN(◯,{})`. The repository
writes `RN(◯,{})` 294 times against `RN(◯,∅)` 12; the blueprint standardises
on `∅`, so a sweep of the repository would be a separate, larger job.

---

## Chapter titles are URLs

Slugs are derived from titles, so a parenthesised title produces `_LPAR_` and
`___` in the path — and any link written by hand against the old title 404s
after a retitle. Two were renamed for this reason:

| was | is |
|---|---|
| `Completeness for FRJ◯/FRJW` | **The decision procedure** |
| `The RN(◯,∅) lattice` | **The variable-free fragment** |

Retitling is therefore a breaking change to the published site. Cheap to do,
but do it deliberately.

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
