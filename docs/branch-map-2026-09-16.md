# Branches, agents, and a merge plan — 2026-09-16

Every number here comes from `git` on `origin` as fetched on 2026-09-16, and
every conflict is **predicted**, not produced: `git merge-tree --write-tree`
merges in memory, and the staged orders below were simulated by committing each
predicted tree as a dangling object and merging again.  No branch, index or
working tree was touched.

## 1. The short answer

* **Four independent lines of work**, plus the toolkit, plus four orphans.
  Every other branch is contained in one of them.
* **Each line merges into `main` cleanly on its own.**  Conflicts appear only
  when the second and third lines land, and they total **29 files**.
* **QLL is not spread.**  The QLL/CLP development (`LaxLogic/QLL`,
  `CLPPaper`, `LaxLogic/Obligation`) is touched by the `syntax-reorg` line
  alone: 84 commits, 90 files.  The other lines touch none of it.
* **No agent is running.**  Of the 50 most recent Claude sessions, 35 are in
  this repository and all are dormant; 35 of the 45 worktrees hold uncommitted
  files (272 in total).
* **Two open pull requests**, 20 and 21, are the same one-commit CI change
  (`ci/lean-action-branch-filter`); merging that branch closes both.

## 2. The lines

| line | tip | ahead of `main` | what it carries | it already contains |
|---|---|---|---|---|
| `syntax-reorg` | `1a5b277` 2026-09-15 | 101 | QLL/CLP, the TPHOLs paper, the new notation, the `LaxLogic/` reorganisation | `lax-obligations`, `tphols` |
| `blueprint-dev-chapter` | `067457c` 2026-09-06 | 825 | FRJW/GBUW dichotomy, decidability, the blueprint site | `frjw-dev`, `blueprint-assembled`, `blueprint-on-frjw`, `verso-blueprint`, `meta-tools` |
| `FRJX` | `993ea74` 2026-09-01 | 515 | the FRJ/FRJV refutation line | `frj-dev`, `frj-choicefree`, `frj-deslime`, `frj-ipc`, `frj-lax`, `ljf-pll`, `meta-tools` |
| `publication/core` | `2400d87` 2026-08-21 | 302 | an August restructuring (`Core.lean`, `FRJ/`, `FRJO/` at the root) | `meta-tools` |
| `tooling` | `da9ac86` 2026-09-05 | 37 | the prover toolkit — **kept separate** | `blueprint-recipe` |

`tphols` is your review branch and is local to this clone; it is contained in
`lax-obligations`, which is contained in `syntax-reorg`.

**Orphans**, each a handful of commits that no line carries:

| branch | ahead | what |
|---|---|---|
| `ci/lean-action-branch-filter` | 1 | CI push filter for `frjw-dev` |
| `ljfo-dev` | 12 | the LJF◯ E2/A2 port, stopped mid-way (2026-08-10) |
| `paper/closed-fragment-ladder` | 1 | second-order candidates, both hunts armed (2026-08-08) |
| `toolchain-main` | 1 | the v4.31.0 migration of `main`, superseded by the merged `toolchain-bump` |

**Already in `main`, safe to delete:** `FablePLL`, `discovery-toolkit`,
`g4ip-complete`, `integration-1`, `ljf-focalization`, `ljf-simp-1`,
`matthew-v1`, `toolchain-bump`, `ui-confluence`, `worktree-g4ill`.

## 3. Predicted conflicts, line against line

Files that would conflict, by pair (`git merge-tree`, no merge performed):

| | syntax-reorg | blueprint-dev-chapter | FRJX | publication/core | tooling |
|---|---|---|---|---|---|
| **main** | 0 | 0 | 0 | 2 | 0 |
| **syntax-reorg** | — | 25 | 14 | 151 | 2 |
| **blueprint-dev-chapter** | | — | 4 | 203 | 6 |
| **FRJX** | | | — | 112 | 11 |
| **publication/core** | | | | — | 4 |

`publication/core` conflicts with everything because it restructured the
repository a different way in August; it has 13 commits that the blueprint line
does not carry.  Treat it as an archive to extract from, not as a merge.

## 4. The merge plan

Recommended order, **blueprint → FRJX → syntax-reorg**: 29 conflicted files in
total, and the 25 awkward ones land in a single merge with a mechanical recipe.
Merging `syntax-reorg` first costs 30 and splits the rename conflicts across two
merges, which is worse.

    git checkout main
    git merge origin/ci/lean-action-branch-filter     # 1 commit, clean
    git merge origin/blueprint-dev-chapter            # clean
    git merge origin/FRJX                             # 4 files
    git merge origin/syntax-reorg                     # 25 files

Build after each step, not only at the end: `lake build`, then the QLL and test
modules by name (they sit outside the default target), then the `wip/` targets
that compiled at baseline.

### Stage 2 — `FRJX`, 4 files

`.gitignore`, `lakefile.toml`, `prover-toolkit/README.md`,
`prover-toolkit/toolkit.json`.  All four are union merges: keep both sides'
entries, take the later toolkit description.

### Stage 3 — `syntax-reorg`, 25 files

Three kinds, each with one recipe:

1. **Two rename/rename pairs.**  `LaxLogic/Focusing/LJF.lean` went to
   `LaxLogic/Focusing/LJF.lean` here and to `LJF/Base.lean` on the other line;
   likewise `LJFComplete`.  Keep the `LaxLogic/Focusing/` location, apply the
   other side's content edits into it, delete `LJF/Base.lean` and
   `LJF/Complete.lean`.
2. **Eight PLL files edited on both sides** (`PLL/ND/NDCore.lean`,
   `PLL/Semantics/Kripke.lean`, `PLL/Syntax/Formula.lean`, `Proof.lean`,
   `FinsetKit.lean`, `PLL/SemUI/SemUIFrag.lean`, `PLL/Timing/Constraints.lean`,
   `TimingLookahead.lean`, `PLL/UI/CandOr.lean`): the other line edited the old
   path, this line moved and re-notated the file.  Take their edits into the new
   path, then convert the glyphs they bring: `⊢-` → `⊢`, `⊨-` → `⊨`, `⊃` → `↠`
   in Lean code.
3. **Text files** (`.gitignore`, `HANDOFF.md`, `docs/next-session.md`,
   `lakefile.toml`, `LaxLogic.lean`, `LaxLogic/ToolkitTest/Challenge/README.md`,
   four `wip/` probes): union merges.  `HANDOFF.md` is append-only dated
   sections, so keep both sequences in date order.

Then re-apply the path rewrite across anything the merge brought in at old
paths:

    python3 scripts/reorg-2026-09-15.py --rewrite
    python3 scripts/reorg-2026-09-15.py --check

### `tooling` stays separate

Matthew's decision, to keep the dependency weak.  For the record, merging it in
would cost 11 files against `FRJX` and 6 against the blueprint line, all under
`prover-toolkit/`.  Continue to merge one-way **from** `tooling` into a campaign
branch when a campaign needs it.

### `publication/core`

Do not merge.  Extract the 13 commits the blueprint line does not carry, or
declare the branch archived.  A merge would cost 203 files against the blueprint
line alone.

## 5. Agents and worktrees

No session was running when this map was made.  35 of the 50 most recent
sessions are in this repository; the ones with work of their own, most recent
first (all dormant):

| session | branch | last active |
|---|---|---|
| Make `Kit.freshFor` linear in binder depth | `claude/practical-euclid-a10fc3` | 2026-09-11 |
| FRJW completeness, decidability and engine | `claude/frjw-w1-w2-lean-5aabff` | 2026-09-11 |
| LaxLogic Blueprint documentation | `claude/laxlogic-blueprint-docs-91bf6a` | 2026-09-11 |
| Replace deprecated `push_neg` in PLLG4UIAdq | `claude/bold-sutherland-82add8` | 2026-09-05 |
| FRJV completeness campaign | `claude/frjv-completeness-693c52` | 2026-09-03 |
| FRJ◯ re-development | `claude/frj-redevelopment-69005f` | 2026-08-30 |
| Belief in lax logic (PR 6 open) | `claude/belief-lax-logic-handover-f331bf` | 2026-08-21 |

45 worktrees exist; 35 hold uncommitted files, 272 in total.  Most are
`worktree-agent-*` scratch trees from subagent runs, but some hold real work:
`agent-a17915a14d30780dd` (122 files, edits to `LaxLogic.lean`,
`PLLFormula.lean`, `PLLSearchDemo.lean` at the **old** paths),
`agent-a2e5d8f793b858d9d` (LJF◯ theta probes),
`/Users/matthew/gtd/worktrees/lax-logic-in-lean/blueprint-on-frjw` (six
uncommitted blueprint chapters).  Worktrees are never removed by an agent
(standing instruction); these are listed so you can decide what to keep.

## 6. The merges as executed — 2026-09-16

Done in the order above, `publication/core` left out by Matthew's instruction.
`main` was 966 commits behind; every merge is committed locally and **not
pushed**.

| stage | commit | conflicts | notes |
|---|---|---|---|
| `ci/lean-action-branch-filter` | fast-forward to `1b6a763` | — | as predicted |
| `blueprint-dev-chapter` | `7762096` | 1 (902 files changed) | a CI-comment clash; took theirs |
| `FRJX` | `5b89507` | 4 | the predicted union merges |
| `syntax-reorg` | `2b67671` | 25 | exactly the predicted set |
| post-merge repairs | `b55c55e` | — | four semantic conflicts, below |

The prediction was accurate as a *file* count, and that is its limit: a
conflict-free textual merge is not a building tree.  Four defects survived it,
each a collision between two lines that edited **different** files, so git saw
nothing to report:

1. **A second `⊬` parser.**  The union resolution in `PLL/ND/NDCore.lean`
   restored `Underivable` and its `infix:70 " ⊬ "`, which `syntax-reorg` had
   deleted in favour of the turnstile framework.  With two parsers in scope
   every underivability statement became a `choice` node — `Ambiguous term …
   [] ⊬ ⊥`, readings `PLLND.Underivable [] ⊥` and `¬ Nonempty (LaxND [] ⊥)` —
   and five modules failed.  Deleted; nothing outside comments used the name.
2. **Precedence.**  The blueprint line's new `stabCard` material writes
   `[] ⊬ φ` under `∧`, which parsed at `infix:70` but not at the framework's
   sequent precedence 26.  Three sites parenthesised.
3. **A constructor added on one line, matched on the other.**  `FRJX` added
   `FRJVi.liftI`; `FRJ/CalculusW.lean`, which `FRJX` does not carry, left
   `toWi` non-exhaustive.  `FRJWi.lift` has the same signature, so the case is
   forced.
4. **A rename carrying divergent names.**  Git applied `FRJX`'s `liftI` hunks
   to `FRJ/Gbu/Circ.lean` across the `wip/gbu_circ.lean` → `FRJ/Gbu/Circ.lean`
   promotion.  The wip copy calls the zone `Th`, the promoted file `Θ`; two
   ported lines named an unbound `Th`.

Lesson for the next merge of this kind: predict conflicts with `merge-tree`, but
budget for a build-and-repair pass of the same order — the damage is in the
files git did **not** flag.

**Verification.**  `lake build` (defaults `LaxLogic`, `FRJGbu`): 8746 jobs,
exit 0.  Four `sorry` warnings, all the halted UI route (`SemUILayered`,
`SemUIHenkin` ×2, `SemUIChar`), unchanged from baseline; every `#guard_msgs`
axiom pin passes.
