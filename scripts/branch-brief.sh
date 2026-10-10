#!/usr/bin/env bash
# SessionStart hook: print the current branch's standing instructions and open
# work from Beads (`bd`), so an agent gets them without having to remember.
#
# Convention: an issue that applies to one branch carries the label
# `branch:<branch name>`; one that is an instruction rather than a task also
# carries `brief`.  The Beads database is one per repository, shared by every
# branch and worktree and never merged with code, so nothing here can conflict.
#
# Prints nothing and exits 0 when `bd`, a Beads database, or a matching issue is
# missing: it can never block a session.  Tested from a worktree on miolingo
# (bd 1.0.5, 0.9 s), 2026-10-10.
command -v bd >/dev/null 2>&1 || exit 0
branch=$(git branch --show-current 2>/dev/null) || exit 0
[ -n "$branch" ] || exit 0
label="${BRIEF_LABEL:-branch:$branch}"
out=$(bd list --label "$label" --limit 20 2>/dev/null) || exit 0
[ -n "$out" ] || exit 0
case "$out" in *"No issues found"*) exit 0 ;; esac
printf 'Beads brief for branch %s (label %s). Run `bd show <id>` for the text of each.\n%s\n' \
  "$branch" "$label" "$out"
