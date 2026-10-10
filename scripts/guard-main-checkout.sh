#!/usr/bin/env bash
# PreToolUse hook (Edit | Write | NotebookEdit): refuse a write to a tracked
# file in the MAIN checkout of this repository.
#
# Rule (Matthew, 2026-10-10): apart from his direct instruction, no agent writes
# to tracked files in the main checkout.  Agents work in their own worktrees and
# changes reach `main` through pull requests.
#
# A file is in the main checkout when the git work tree that contains it IS the
# directory holding the shared `.git` (a linked worktree has a different top
# level, wherever it sits on disk).  Refused: a tracked file there, or a new file
# there that git would not ignore.  Allowed: ignored paths (`.beads/`, `.lake/`),
# anything in a worktree, anything outside the repository.
#
# Override, for a write Matthew has directly asked for: start the session with
# LAXLOGIC_MAIN_WRITE_OK=1 in its environment.
#
# Limit: this sees the file tools only.  A shell command (`sed -i`, a redirect,
# `git commit`) is not checked here.
[ "${LAXLOGIC_MAIN_WRITE_OK:-}" = 1 ] && exit 0
path=$(python3 -c 'import json,sys
d=json.load(sys.stdin).get("tool_input",{})
print(d.get("file_path") or d.get("notebook_path") or "")' 2>/dev/null) || exit 0
[ -n "$path" ] || exit 0
dir=$(dirname "$path")
while [ ! -d "$dir" ] && [ "$dir" != / ]; do dir=$(dirname "$dir"); done
top=$(git -C "$dir" rev-parse --show-toplevel 2>/dev/null) || exit 0
common=$(git -C "$dir" rev-parse --path-format=absolute --git-common-dir 2>/dev/null) || exit 0
main=$(dirname "$common")
[ "$top" = "$main" ] || exit 0                      # a linked worktree: allowed
git -C "$main" check-ignore -q -- "$path" 2>/dev/null && exit 0   # ignored: allowed
echo "Refused: $path is in the main checkout ($main). Agents do not write tracked files there; work in your own worktree and open a pull request. (Matthew's rule, 2026-10-10; override only on his direct instruction with LAXLOGIC_MAIN_WRITE_OK=1.)" >&2
exit 2
