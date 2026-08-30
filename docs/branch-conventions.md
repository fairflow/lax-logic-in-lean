# Branch conventions

Written 2026-08-30, after `frj-dev` and `tools-dev` drifted apart and syncing
them by hand meant sorting a 465-file diff into "theory" and "tooling" one file
at a time.

## The three kinds of branch

**Durable campaign branches** — human-chosen names, no hash: `frj-dev`,
`ljfo-dev`, `tools-dev`, `publication/core`. One per line of work, living
across many sessions and many worktrees. The branch *is* the archive: its own
`HANDOFF.md` sections are the record. Sessions commit onto these.

**`tooling`** — the shared branch, described below.

**Ephemeral worktree branches** — `claude/<slug>-<hex>`, `worktree-*`,
`agent-*`. Created automatically, die with the worktree, and are never a
**destination** on the remote. `scripts/hooks/pre-push` refuses to create or
update one; deleting them from the remote is always allowed, since tidying up
is the point.

**You do not have to leave your worktree branch to push.** The hook tests the
*remote* ref, not the local one, so working on `claude/<slug>-<hex>` and
pushing with an explicit refspec is the normal way to do this and is allowed:

```bash
git push origin HEAD:refs/heads/tools-dev     # fine from any local branch
```

Two notes on the hook's second arm, which refuses any ref ending in `-` plus
six hex digits as a generated suffix: it sits on the catch-all, so it also
applies to **tags** (`refs/tags/v1-abc123` would be refused), and it would
refuse a legitimate branch that happened to end that way. Nothing collides
today; the net is wider than the comment suggests.

```bash
scripts/install-hooks.sh      # once per clone; worktrees share the git dir
```

## `tooling`: the branch both campaigns merge *from*

The problem it solves: general tooling used to land on whichever campaign
branch happened to be active, so every sync needed a human judgement about
which side of the theory/tooling line each file fell on.

The flow is **one-way**. Tooling changes go on `tooling`; campaign branches
merge it in. Nothing merges back the other way.

```
        tooling
       /   |   \
      /    |    \
 frj-dev  tools-dev  (future campaigns)
```

### What belongs on `tooling`

Anything a *different* repository could use, or that is about running the
repository rather than about its mathematics:

- `scripts/hooks/`, `scripts/install-hooks.sh`, `scripts/campaign-push.sh`,
  `scripts/all-targets.py` — branch management and CI plumbing
- `prover-toolkit/` — the corpus index, the checker, the skills
- generic `.gitignore` rules (`__pycache__/`, `*.pyc`)
- documentation of the above

### What does not

Anything bound to the development's own content, even if it is called a tool:

- `tools/*.lean` (`Bank`, `Cert`, `Cover`, `RCFuel`, `RCellsGen`, …) — these
  are RN-dictionary and FRJ machinery, and the `lakefile.toml` targets that
  declare them. Moving the lakefile hunk without the Lean sources breaks
  `lake build`.
- `tools/paper-skeleton/`, the RN/ρ shell and Python drivers
- build-product ignores for a particular paper
- benchmark *fixtures* that mention the development's own theorems —
  `LaxLogic/ToolkitTest/` is toolkit-adjacent but LaxLogic-specific, so it
  lives on `tools-dev`, not here

The test: would this still make sense in a repository that had never heard of
lax logic? If yes, `tooling`. If no, the campaign branch.

**The rule governs what a `tooling` commit may CHANGE, not what the branch
contains.** A branch carries a whole tree, so `tooling` also holds all of
`LaxLogic/` — including `LaxLogic/ToolkitTest/`, which the list above says
belongs elsewhere. That is not a contradiction but it is a trap: those files
came free with the branch's base, and a merge moves the delta from the merge
base, not the tree. They are therefore invisible to any campaign that shares
that base, and delivered to any campaign that does not. See the limits below.

### The exception: shared files at the root

`.gitignore` and `lakefile.toml` are single files that every branch edits, so
they cannot be split by path and the rule above does not apply to them.

- **`.gitignore`: `tooling` carries the union.** Two branches appending
  different blocks to the end of the same file conflict on every merge — this
  is not hypothetical, it happened on the first `tooling` merge attempt. So
  `tooling` holds every branch's ignore rules, campaign-specific ones
  included, and `.gitignore` is edited *there*.

  **The union makes the conflict trivial to resolve; it does not prevent
  it.** The conflict is positional, not semantic: both sides appended a
  different block at the same end of the file, and git cannot know the result
  is the same set of rules. `tooling` genuinely contains every rule from all
  four campaigns — verified rule by rule — and `publication/core` still
  conflicts on the file. When it does, take either side and move on.
- **`lakefile.toml`: `tooling` does not touch it.** Its target declarations
  are inseparable from the Lean sources they name, so a campaign's lakefile
  hunk belongs with that campaign's sources. If tooling ever needs a target of
  its own, that is the moment to reconsider.

## Doing it

Add tooling, on the `tooling` branch:

```bash
git switch tooling
# ... edit, commit ...
scripts/campaign-push.sh tooling
```

Take tooling into a campaign branch:

```bash
git switch frj-dev
git merge tooling
scripts/campaign-push.sh frj-dev
```

`campaign-push.sh` refuses unless the push fast-forwards, which is the guard
against clobbering someone else's commits — the failure mode that matters when
several agents share a remote.

Check before merging, without touching anything:

```bash
git diff --stat tooling..frj-dev -- .       # what the campaign has that tooling lacks
git merge-tree --write-tree frj-dev tooling # non-destructive conflict check
```

## Why `tooling` is a normal branch and not an orphan

A branch carries a whole tree, not a path subset, so `tooling` contains all of
`LaxLogic/` too — it is based at the last commit both campaigns share. That is
deliberate. What a merge brings across is the delta *from the merge base*, not
the branch's whole content, so merging `tooling` into `frj-dev` moves exactly
the tooling commits and nothing else.

An orphan branch holding only the tooling paths would look tidier and merge
worse: unrelated histories, and every campaign merge fighting over paths the
orphan does not have.

### The limit of that argument

The clean-delta property holds **only for campaigns whose base is at or after
`tooling`'s own**, which is `ace04e0` (2026-08-30). Measured on the day this
was written:

| campaign | merge-base | files a merge would touch | result |
|---|---|---|---|
| `tools-dev` | `ace04e0` 08-30 | 6 | clean |
| `frj-dev` | `ace04e0` 08-30 | 7 | clean |
| `ljfo-dev` | `78a985c` 08-09 | 34 | clean, but 34 files is not "the tooling commits" |
| `publication/core` | `78a985c` 08-09 | 729 | **conflicts**: `.gitignore`, `HANDOFF.md`, `README.md`, `scripts/all-targets.py` |

For the two older lines the delta from the merge base is most of the summer's
work on `main`, not the tooling commits — and it is those two, not the ones I
checked first, that would receive `LaxLogic/ToolkitTest/`, `HANDOFF.md` and
`README.md` along with the tooling.

**Before merging `tooling` into a campaign that predates `ace04e0`, bring the
campaign current with `main` first**, then merge `tooling`; the delta is small
again. A stale branch is the cause here, and no branch topology fixes it —
`tooling` cannot be rooted below the point where `prover-toolkit/` exists.

The available hardening, if this bites: re-root `tooling` at `main` rather
than `ace04e0`. That would drop `LaxLogic/ToolkitTest/` and the challenge
proofs from its tree, so no campaign could ever receive them from a tooling
merge. It costs a rebase and a force-push, and it still does nothing for a
campaign that has not merged `main`.

*(This section exists because a peer session checked `ljfo-dev` and
`publication/core` after I had checked only `frj-dev` and `tools-dev`, and
found all three claims above to be wrong as first written.)*

## If two agents touch the same branch

They will, and the remote is the only thing that arbitrates. The rules that
have actually prevented damage here:

- push with an **explicit refspec** (`HEAD:refs/heads/tools-dev`); this repo's
  `push.default` is `upstream`, so a bare `git push` on a new branch can aim
  at `main`
- `gh` defaults to the **AviCraimer** parent repo, not `fairflow` — always
  pass `--repo fairflow/lax-logic-in-lean`
- never `git stash` bare: the stash stack is shared across all worktrees of a
  clone, so `git stash pop` can pop another session's work. Use a WIP commit,
  or `git stash push -u -m "<tag>"` and `apply` by SHA
- never remove a worktree to tidy up — it kills the agent session using it
