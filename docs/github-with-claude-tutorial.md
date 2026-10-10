# GitHub with Claude, Lean, Verso and Pages: a working guide

2026-10-10, written by the LaxLogic manager session for Matthew, from what
happened in this repository on 2026-10-09 and from the record (HANDOFF.md,
docs/branch-map-2026-09-16.md, the memory notes). It is meant for any of
Matthew's Lean repositories, with `fairflow/lax-logic-in-lean` as the worked
example. Dated incidents are cited so a rule can be traced to its cause.

Contents

1. The setup
2. Branches, worktrees and pull requests: the discipline
3. Merging: fast-forward, merge commits, squash, rebase, cherry-pick
4. GitHub Pages for a Lean and Verso project
5. Permissions in Claude Code
6. Safety, visibility, and creating repositories
7. Lean-specific practice
8. Gotchas, with dates
- Appendix A. Overlapping builds, lost caches, and the draft-PR protocol

---

## 1. The setup

- **The clone.** `~/Lean/Sources/lax-logic-in-lean`, with two remotes:
  `origin` = `fairflow/lax-logic-in-lean` (ours) and `upstream` =
  `AviCraimer/lax-logic-in-lean` (the repository it was forked from).
- **The default branch** is `main`. Everything published comes from `main`.
- **CI** is `.github/workflows/lean_action_ci.yml`: it runs on pull requests
  targeting `main` and on pushes to `main`.
- **Pages** is `.github/workflows/pages.yml` (calling `blueprint-pages.yml`):
  it builds the Blueprint, the two papers and the explorers into one site,
  https://fairflow.github.io/lax-logic-in-lean/. It deploys only when
  dispatched by hand; on a pull request it builds without deploying.
- **Who merges.** Since 2026-10-09 every change reaches `main` through a pull
  request, and the LaxLogic manager session merges them one at a time
  (Matthew: "Merges to lax-logic main go through the LaxLogic manager from now
  on").

## 2. Branches, worktrees and pull requests: the discipline

**One agent, one branch, one worktree.** Each piece of work (a session, or a
subagent it starts) gets its own git worktree on its own branch. Two agents
sharing a working directory overwrite each other's files and each other's
build outputs (`.lake/build`), and neither notices. This discipline was broken
recently and is the root of several of the problems below.

- A worktree is a second checkout of the same repository, in its own
  directory, sharing one object store. `git worktree add <dir> -b <branch>
  origin/main`. Claude Code's isolation mode creates them under
  `.claude/worktrees/`.
- Add `.claude/worktrees/` to `.git/info/exclude` once per clone, or VS Code
  shows every worktree's files as untracked changes.
- **Seed a new worktree's build with an APFS clone**, before any `lake`
  command: `cp -Rc <source>/.lake <worktree>/.lake`. It is instant and uses
  no extra space until files change. Clone from a worktree that is current on
  `main`, never from a worktree on an old branch.
- **Branch names.** `claude/<slug>-<hash>` branches are local and never pushed
  (a pre-push hook in `scripts/hooks/` refuses them). A branch that is to be
  pushed gets a plain name without a hash: `checkderiv`, `blueprint-notation`.
- **Push with an explicit refspec**: `git push origin HEAD:refs/heads/<name>`.
  See §8 for why a bare `git push` is dangerous on this machine.
- **Work reaches `main` only through a pull request.** No direct pushes to
  `main`, by any session.
- **No agent writes tracked files in the main checkout** (Matthew,
  2026-10-10), apart from his direct instruction. The main checkout is his;
  agents work in worktrees. `scripts/guard-main-checkout.sh` enforces this for
  the file tools as a pre-tool hook (`.claude/settings.json`): it refuses a
  write to a tracked or un-ignored file there and allows ignored paths such as
  `.beads/`. It does not see shell commands, so the rule still binds where the
  hook cannot reach.
- **Finishing.** The session that created a worktree removes it once its work
  has landed. Removal is allowed only for finished worktrees, and only after
  their uncommitted files are archived (Matthew, 2026-10-09, lifting the
  2026-07-20 veto with that condition). Never remove a worktree another
  session is using.
- **Size.** `du` counts each APFS clone at full size, so worktree sizes
  mislead. On 2026-10-09 removing worktrees worth 62 GB, 113 GB and ~100 GB
  by `du` freed 2.6, 8 and 3.4 GB. Measure `df` before and after.

### Per-branch instructions, without merge conflicts

Rules that hold on every branch live in `CLAUDE.md`, identical everywhere.
Rules for one branch (a prototype that relaxes the refutation stage, say) must
not be a file of the same name on each branch: merging would conflict, or
silently carry one branch's rules onto another. They go in Beads (`bd`)
instead. Its database is one per repository, shared by every branch and
worktree, kept outside the working tree (`.beads/embeddeddolt/`, git-ignored)
and synchronised by `bd dolt push` / `bd dolt pull` under `refs/dolt/data`,
so it is never part of a code merge.

- An issue for one branch carries the label `branch:<branch name>`; an
  instruction rather than a task also carries `brief`.
- `scripts/branch-brief.sh` runs as a session-start hook
  (`.claude/settings.json`) and prints the current branch's issues into the
  new session, so no agent has to remember to look.
- When a branch is deleted, the manager closes its `branch:` issues in the same
  step.
- The script is silent where there is no Beads database; this repository has
  none until `bd init` is run, which is Matthew's decision.

## 3. Merging: fast-forward, merge commits, squash, rebase, cherry-pick

A branch is a pointer to a commit; merging decides how `main`'s pointer moves.

**Fast-forward (ff).** If `main` has not moved since the branch was cut, the
branch's commits sit directly on top of `main`, and merging just moves the
`main` pointer forward. No new commit is created; history stays a straight
line. `git merge --ff-only <branch>` does this and refuses otherwise, which is
the safe default for an automated merge.

**Merge commit.** If `main` has moved, a fast-forward is impossible, and a
merge creates a new commit with two parents that joins both lines. This is
what GitHub's "Create a merge commit" button does (our default). Both lines'
history is kept.

**Squash.** All the branch's commits become one new commit on `main`. Tidy,
but the branch's individual commits are no longer in `main`'s history, so
tools that compare by commit (`git branch --merged`) no longer see the branch
as merged.

**Rebase.** Replays the branch's commits on top of the current `main`, creating
new commits with new hashes, after which a fast-forward is possible. Rewrites
the branch, so never rebase a branch someone else is using.

**Cherry-pick.** Copies one chosen commit from another branch onto the current
one, as a new commit. Use it when two lines must stay independent and only
specific fixes should cross between them.

When to use which, in this estate:

- **Ordinary work branch to `main`**: a pull request with a merge commit, or a
  fast-forward if the branch is current.
- **`tooling` ↔ `main`: cherry-pick only, in both directions** (Matthew,
  2026-10-05). `tooling` carries the prover toolkit and branched before the
  four lines merged; `main → tooling` would be 1,381 files and 294,543
  deletions. Merging either way is wrong. Each pick is checked by content.
- **lean-certify: neither.** It is a separate repository, used here as a Lake
  dependency pinned to a release tag (`rev = "v0.1.2"` in `lakefile.toml`).
  Moving to a new version is a small pull request that changes the tag and
  the manifest entry; nothing is merged or picked. A patch release (0.1.x)
  promises no signature changes; a minor release (0.2.0) can change them and
  comes with a migration note.

Two tools that mislead:

- **`git cherry` compares by patch id, not by content.** On 2026-10-05 it
  marked 13 commits as missing from `main`; checking by content, one of them
  was already there by another route and one would have regressed `main`.
  Decide picks by comparing file contents.
- **`git merge-tree` predicts textual conflicts, not semantic ones.** The
  2026-09-16 merge of four lines was predicted clean on files and produced
  four semantic collisions afterwards. Build and run CI after any large merge.

## 4. GitHub Pages for a Lean and Verso project

- **One site per repository, and every deploy replaces all of it.** To publish
  several things (Blueprint, papers, explorers), build them into one artifact
  under different paths and deploy once (`scripts/ci-papers.sh`).
- **A dispatch publishes the branch you name.** `gh workflow run pages.yml
  --ref main` builds `main` and deploys it over the whole site. Dispatching
  with any other branch publishes that branch's build in place of the site,
  including whatever that branch contains that `main` does not. Dispatch only
  with `--ref main`, after the merge.
- **A pull request is the build test.** `pages.yml` builds on pull requests
  that touch the Blueprint or the papers, and skips the deploy job. It also
  uploads the built site as a downloadable artifact, so a change can be
  inspected before anything is published. The order is always: pull request
  check, merge, then dispatch on `main`.
- **Batch the dispatch.** Merge a group of pull requests, then dispatch once.
  Each deploy takes 10–15 minutes.
- **Verso gotchas.**
  - A bare `{` in prose or link text opens a Verso role and breaks parsing of
    the following lines (2026-10-09, fixed by putting `RN(◯,{})` in code).
  - Signatures are printed by Lean's printer with the namespaces the
    *document* has opened. A document that opens nothing prints every name
    fully qualified. Each paper section and Blueprint chapter now opens its
    namespaces (`open PLLND`, `open LaxLogic.QLL …`), which also switches on
    the library's notation in signatures (PRs #24–#26, #31).
  - `{docstring X}` on an undocumented `X` is an error; a `(lean := "X")`
    node on an undocumented `X` is a warning.
  - The PDFs need a TeX installation and are built locally
    (`scripts/clp-paper.sh`); the site carries HTML only.
- **Private repositories.** Pages for a private repository needs a paid plan,
  and the site it serves is still public.

## 5. Permissions in Claude Code

**Modes**, chosen per session in the mode selector:

- *default*: asks before edits and before commands not on an allow list;
- *acceptEdits*: file edits go through, commands still ask;
- *auto*: a safety classifier decides, and asks when unsure (it refused the
  bulk worktree removal on 2026-10-09);
- *bypass permissions* ("dangerously skip permissions"): nothing asks, except
  what rules force.

**Rules**, in `settings.json` files, each a list of patterns such as
`"Bash(gh pr view *)"`:

- `allow` lets a matching command run without asking;
- `ask` makes it ask, **even in bypass mode**;
- `deny` blocks it, in every mode.

**Where rules live**, and they combine: `~/.claude/settings.json` (all
projects), `<repo>/.claude/settings.json` (shared, committed), and
`<repo>/.claude/settings.local.json` (this clone only, not committed). A
`defaultMode` key in any of them sets the mode a session starts in.

What went wrong on 2026-10-09, and the fixes:

- The repository's `settings.local.json` had acquired `"ask": ["Bash(gh *)"]`
  and `"defaultMode": "auto"`. The first made every `gh` command ask even in
  bypass mode; the second put the session back in auto mode after a restart.
  Both removed; the deny rules kept, and `gh repo delete` added to them.
- The user-level rules for `gh` named its full path (`/opt/local/bin/gh …`),
  so they never matched commands written as plain `gh`. Rules match the
  command text as written.
- A command beginning `cd <dir>; …` asks by itself. Use `git -C <dir>` and
  absolute file paths instead. Call tools by a relative path or plain name,
  not an absolute executable path, so one allow rule covers every machine.
- Turning bypass off returns the session to its default mode: on 2026-10-09 that was auto, because of the `defaultMode` key.

**Messages between sessions** are held, and can expire undelivered, when the
two sessions run in different permission modes. A held message says so; the
fix is to approve it in the receiving session or match the modes.

Our working position: bypass mode for trusted sessions, a few `deny` rules for
the irreversible (`git push --force`, `git push -f`, `rm -rf /`, `gh repo
delete`), and no `ask` rules on `gh`, since merging and publishing are governed
by the rules in §2 and §4 rather than by prompts.

## 6. Safety, visibility, and creating repositories

- **What agents do and do not do.** Agents prepare: branches, commits, pull
  requests, drafts of mail and issues. Matthew decides anything outward or
  irreversible: publishing, merging outside an agreed protocol, deleting,
  creating repositories, contacting anyone.
- **Pushing is publishing.** Anything pushed to a public repository can be
  cached and indexed even if deleted later. Check what a commit contains
  before pushing it, and never push secrets (`.env`, tokens, keys).
- **Public and private.** QKCD lives in a private sibling repository
  (`~/Lean/Sources/qkcd`); material moves only outward from it, never back,
  and nothing private is copied into a public repository.
- **Creating a repository, delegated.** An agent may create one when Matthew
  asks and states the owner, name and visibility:
  `gh repo create fairflow/<name> --private` (or `--public`). Then, at once:
  `git config --local push.default simple` (see §8), add `origin`, and push
  `main` by explicit refspec. Visibility is never inferred: a missing word
  means ask. Turning a private repository public is Matthew's act.
- **Deleting a repository** is denied to agents by rule.

## 7. Lean-specific practice

- **Never rebuild Mathlib.** Seed each worktree's `.lake` by APFS clone (§2).
- **Ask before any `lake build`** in this repository (machine-wide build
  contention). CI is free of that contention, which is why a pull request is
  the preferred build test.
- **Run built binaries under a deadline**, never `lake exe`, and report every
  timeout or cap.
- **Stale build outputs.** An `.olean` built against an older version of an
  environment extension can crash Lean (exit 139) rather than report an
  error. When in doubt, clean the affected module's outputs.
- **What CI builds.** `lake build` covers only `defaultTargets` (`LaxLogic`,
  `FRJGbu`). Anything else needs naming: the LJF◯ step builds
  `LJF.OSearch LJF.OBridge LJF.OCheckDeriv` on pull requests; `CertifyAdoption`
  and `wip/` modules are not built by CI at all.
- **Axiom pins.** A result counts as PROVED only with a pinned axiom set,
  checked by `collectAxioms` (`#axioms_within`). Automation can widen it
  silently: five `tauto` calls made four Craig interpolation theorems depend
  on `Classical.choice` (2026-10-08, reverted).

## 8. Gotchas, with dates

- **`push.default = upstream` is set globally on this machine.** A branch
  created from `origin/main` tracks `main`, so `git push origin <branch>`
  pushes to `main` (2026-07-11: a commit landed on `main` without review).
  Always push `HEAD:refs/heads/<name>`; set `push.default simple` in new
  repositories.
- **`gh` defaults to the fork's parent.** `gh pr create` without `--repo`
  targets `AviCraimer/lax-logic-in-lean`, a third party's repository
  (2026-07-11, closed with an apology). Always pass
  `--repo fairflow/lax-logic-in-lean`.
- **A dispatch from a branch publishes that branch** over the whole site (§4).
- **Merging without waiting for CI.** The certify-adoption merge (2026-10-09)
  turned `main` red: `scripts/check-imports.py` did not know the new
  dependency `LeanCertify`. Merge only on green checks.
- **A ledger update and the README figures travel together.**
  `scripts/readme-figures.py --check` dates the figures by the ledger's last
  commit; splitting them across pull requests fails CI for no real reason. CI
  also needs full history (`fetch-depth: 0`) for that check.
- **The root checkout can fall behind.** On 2026-10-09 the main checkout was
  206 commits behind `origin/main`, and a survey that read it as "main" cited
  stale paths. Pull before reading.
- **Timestamps come from `date`,** not from memory: footers drifted by up to
  an hour on 2026-10-09.

---

## Appendix A. Overlapping builds, lost caches, and the draft-PR protocol

### What happened

On 2026-10-09 CI runs on `main` overlapped (three within six minutes), pull
request runs and Pages runs ran alongside them, and builds that took 5–9
minutes earlier in the day took 35–41 minutes by evening.

### Why overlap costs time

- **Caches are per branch.** GitHub Actions caches are scoped to the branch
  that saved them; a run can read its own branch's caches and those of the
  default branch (for a pull request, also its base branch). Sibling branches
  cannot share.
- **A cache key is written once.** If two runs build the same commit and both
  try to save the same key, one save wins and the other is discarded; the
  work of the second run is lost.
- **The repository has a 10 GB cache quota,** with least-recently-used
  eviction. `leanprover/lean-action` saves roughly 2.6 GB per branch, and the
  Pages workflow saves its own build caches. A day with many branches and
  many runs pushes useful caches out, and the next run starts cold: Mathlib's
  outputs are downloaded again and every project module is rebuilt. That is
  the jump from minutes to tens of minutes.
- **Expensive steps multiply it.** The LJF◯ step adds 9–35 minutes depending
  on what is cached.

### What is now in place

- `lean_action_ci.yml`: `concurrency: ci-<ref>`, cancel in progress. One CI
  run per branch or pull request; a newer push cancels the older run, whose
  commit it contains (PR #32).
- `blueprint-pages.yml`: the deploy job is in one global concurrency group and
  is never cancelled half-way, so two deploys cannot overlap (PR #32).
- The LJF◯ step runs on pull requests only (PR #29).
- Merges are serialised through the manager, and Pages is dispatched once per
  batch (§1, §4).

### The draft-PR protocol

A pull request is how a branch gets a CI build, but a pull request that is not
yet known to build should not look ready. So:

1. **Open every pull request as a draft**: `gh pr create --draft …`. CI runs on
   drafts exactly as on ready pull requests; the draft status says "not ready,
   being tested".
2. **The manager watches the checks.** When every check has passed, the
   manager marks it ready: `gh pr ready <n>`. Only a ready pull request is
   merged.
3. **If any check fails, the pull request goes back to draft**: `gh pr ready
   <n> --undo`, and the manager sends the error to the session that owns the
   branch. The owner fixes it on the same branch; the next push re-runs the
   checks.
4. **No pull request is presented as ready, and none is merged, until all its
   builds have completed.** A pending check counts as not passed.
5. **One heavy build at a time where possible.** Before opening a pull request
   that triggers the Pages build or the LJF◯ step, check whether one is
   already running; if so, open it as a draft and let the queue clear.
6. **After merging a batch, dispatch Pages once**, with `--ref main`.

Optional further step, not yet adopted: make the expensive workflows skip
draft pull requests (`if: github.event.pull_request.draft == false`) and run
only when a pull request is marked ready. That trades a later test for fewer
runs; it suits large batches.
