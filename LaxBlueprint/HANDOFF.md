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

**Open PRs:** #19 (this blueprint → `frjw-dev`, for the FRJW agent to merge).
#17 (portable recipe → `tooling`). #18 is closed.

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

**`#axioms_within`, not `#print axioms`, is the checker to grep for.** I wrote
a `CHECK OUTSTANDING` note against N0a claiming its pins were missing. They
were not: `LJF/OFuelSound.lean` ends with `#axioms_within eSoundF [propext,
Quot.sound]` and three more. `#axioms_within` is defined in `Meta/Audit.lean`,
is built on `collectAxioms`, bounds ONE declaration, and is what seven files
under `LJF/` use. Searching only for `#print axioms` misses them. Repo-wide
both idioms are in use, so **check for both before recording anything as
unpinned.** (Caught by the FRJW agent, 2026-09-05.)

**A `{uses "..."}` role only works inside a node.** Putting one in a chapter's
prose preamble fails the build with `uses declaration outside an informal
enviroment` (sic). In preamble text, name the node in plain words.


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

## THE NEXT JOB — Matthew, 2026-09-06 02:20, for 05:00

Three steps, in order. Everything needed is here; nothing needs re-deriving.

**1. Merge `frjw-dev`.** It brings `58eba3f`: the FRJW agent has written all
sixteen `TO WRITE` paragraphs across UI, Tools, RN, FRJW and Development
(+184/-43, prose only — no node status changed, no `(lean := "...")` added or
altered, no new nodes). They cannot build `LaxBlueprint` on their side, so
**the Pages run is the only gate on that prose.** If a paragraph breaks the
build, their instruction is to revert *that paragraph*, not the commit, and
tell them which.

**2. Add an N0k node to the UI chapter.** `CutInv` is PROVED (§4.22, WP6, by
polarisation invariance). Verified against `LJF/OPolInv.lean` directly:

```
#axioms_within LJFO.polInvT   [propext, Quot.sound]
#axioms_within LJFO.polInvL   [propext, Quot.sound]
#axioms_within LJFO.cutInvNE  [propext, Quot.sound]
#axioms_within LJFO.cutInv    [propext, Classical.choice, Quot.sound]
```

The node table row is `docs/ui-routeB-blueprint.md:57`. Note the choice in
`cutInv` is *not* the `atomMem_of_mem` one — it is the `Type` packaging of a
`Nonempty` result through the `Prop`-valued bridge, so WP1d will not clear
it. The ◯-free block `polInvT_circFree`/`cutInv_circFree` landed first.

**Careful:** the FRJW agent wrote "the N0k node in your UI chapter". There is
no such node — it must be ADDED, not updated.

**Consequential edits in the same chapter, which will otherwise contradict
the new node:**

- N3 becomes PROVED BOTH WAYS. It currently says the backward direction is
  "PROVED *relative to* `CutInv`".
- N6 becomes relative to `CellsFor` alone. It currently lists `CutInv` as
  one of three things standing between the file and `PLL_UI`; that drops to
  two.
- The chapter preamble says "*Two* things are genuinely open — N4 … and
  `CutInv`". **N4 is now the only open thing.** This sentence is wrong the
  moment the merge lands.

**2b. §4.23 landed at 02:30 and it is the most important part of this job —
the published chapter now presents a VACUOUS theorem as a result.** Verified
against `wip/ui_routeB_n4_lit.lean` and §4.23, not taken on report.

*The literal form of N1 is REFUTED*, in the kernel, by six designed cells.
The ∀p attack row of a parked `Q ⊃ N ∈ done` at goal `↑Q` is
`A_f(done ⇒ ↑Q) ∧ A_f(N :: rest ⇒ ↑Q)` — the same call one fuel down — so
`A_{f+1}` contains `A_f` as a proper subterm and the chain is strictly
size-ascending. Hence `EStabEq`/`AStabEq` have **no instances at any
saturated station with a retained compound implication**. Growth ratios at
fuels 0–5: 2.2x, 2.1x, 1.8x, 1.8x, 3.3x. The control (v), unsaturated, *is*
literally constant from fuel 3, and `literal_N1_dividing_line` packages all
six: the dividing line is saturation with a retained compound implication,
not weight.

Three consequences, each contradicting the live chapter:

- **`hasUI_of_stabEq` has no instances.** The dividing line is *exactly that
  theorem's own hypothesis*. The chapter's N3 node presents it as "PROVED
  outright from the two cofinality variables, no cut needed" — true and
  vacuous. It must be restated, and replaced as the live result by
  `hasUI_of_stabilises` (interderivable form, through `cutInv`,
  `[propext, Classical.choice, Quot.sound]`, `wip/ui_routeB_n4.lean`).
- **`FuelIrrelevance` is moot** — its consumer's hypothesis is unsatisfiable
  there. The chapter's N1 node lists it as a live obligation.
- **The "termination of the recursion" reading of N4 (§4.19) is DEAD.** The
  fuel is essential. Do not repeat that framing.

*N4's ◯-free instance is PROVED*: `n4_circFree_uncond`,
`[propext, Classical.choice, Quot.sound]`, by transport from
`LJFIPC.uniform_interpolation_IPC`. The bounded form for PLL is OPEN. So N4
is no longer flatly "open both ways" — it is open for PLL with its ◯-free
instance settled, which is a better and more interesting statement.

**Net effect on the preamble:** it currently says two things are open, N4 and
`CutInv`. After §4.22 and §4.23 that is one — N4 for PLL itself.

**3. Republish** — `gh workflow run pages.yml --ref blueprint-dev-chapter`.
Expect ~11 minutes, as at 27fca24. If it is heading for 90, something has put
`LJF/OFuelPFam.lean` back in the import closure.

Do NOT attach anything under `LJF/` while doing this; see the N0c/N0d decision
below.

---

## What is NOT done

- **15 `TO WRITE` markers remain**, down from 64. Each is a judgement call
  that is Matthew's, not an agent's: whether to inline the Hasse diagram,
  which worked example to show whole, how much of a proof to reproduce.
  `TODO` was renamed to `TO WRITE` throughout so a marker is unambiguously a
  writing task and never a programming one.
- **N0c and N0d are deliberately NOT attached, and should stay that way for
  now.** Matthew's decision, 2026-09-06. They are PROVED and pinned, and the
  attachment was made and then reverted, so this is a settled decision rather
  than an oversight — do not "fix" it.

  Attaching them means `import LJF.OFuelPCofinal`, which chains to
  `LJF/OFuelPFam.lean`. §4.20 measures that module at **1463 s on a clean
  build** — not because it is large, but because the 17-way `mutual` goes
  through `WellFounded.fix`: the same bodies as an `unsafe def` compile in
  3.0 s. So one import line put a 25-minute module on the blueprint's
  critical path, and every publish paid it.

  §4.20 also records the design that removes it: outer `Nat.rec` on the
  height budget, inner `Nat.rec` on the station budget, structural recursion
  on the derivation. Tying this chapter's build to a founding that is being
  replaced is not worth a 25-minute publish.

  **When to revisit:** after the structural refounding lands. Then the import
  is cheap and the attachment is worth having. The recipe, if so — one import
  covers all nine, since `LJF.OFuelPCofinal` imports `LJF.OFuelPFam` itself:

  ```
  import LJF.OFuelPCofinal
  -- N0c
  (lean := "LJFO.tinvP, LJFO.uentryP, LJFO.parkAntP, LJFO.satE2P, LJFO.satA2P")
  -- N0d
  (lean := "LJFO.ECofinalP, LJFO.ACofinalP, LJFO.ecofinalP, LJFO.acofinalP")
  ```

  Re-read the pins from the file at that point rather than copying them from
  here: WP1d bundles a choice-free reproof of `atomMem_of_mem`, which should
  take these from `[propext, Classical.choice, Quot.sound]` to
  `[propext, Quot.sound]`.

  **The general lesson**, which is the reusable part: an `(lean := "...")`
  attachment costs whatever its module's *import closure* costs. Before
  attaching, check what the import drags in — not just that the build passes.

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
