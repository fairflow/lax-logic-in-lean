#!/usr/bin/env bash
# Sync a review worktree to the QLL development branch and rebuild it.
#
# `git pull` moves source only.  Lean's language server elaborates the file you
# have open but never builds its *imports* — it loads their .olean files — so
# any module whose source moved has no valid olean and every file importing it
# reports "object file ... does not exist".  That is the ocean of red; it is a
# missing build, not damage.  This rebuilds it.
#
#   scripts/qll-sync.sh [branch]      default branch: lax-obligations
#
# The whole QLL library, tests included, builds from scratch in about five
# seconds: 13 small modules, and mathlib is already cached.
set -euo pipefail

BRANCH="${1:-lax-obligations}"
cd "$(git rev-parse --show-toplevel)"

if ! git diff --quiet || ! git diff --cached --quiet; then
  echo "Uncommitted changes here; not merging.  Commit or set them aside first." >&2
  git status --short >&2
  exit 1
fi

echo "== $(git rev-parse --abbrev-ref HEAD)  ←  $BRANCH"
git merge --ff-only "$BRANCH"
echo
echo "== changed files"
git diff --name-only 'HEAD@{1}' HEAD || true
echo
lake build LaxLogic.QLL.Tests
echo
echo "Built.  If a file is still red in VS Code: Cmd+Shift+X on it (Lean 4:"
echo "Restart File), or 'Lean 4: Restart Server' from the command palette."
