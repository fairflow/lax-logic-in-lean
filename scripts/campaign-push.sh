#!/bin/sh
# Push the current worktree's commits to a DURABLE campaign branch.
#   scripts/campaign-push.sh frj-dev
# Refuses unless the push is a fast-forward of the campaign branch.
set -e
[ -n "$1" ] || { echo "usage: $0 <campaign-branch>" >&2; exit 2; }
c=$1
git fetch -q origin "$c" 2>/dev/null || true
if git rev-parse -q --verify "origin/$c" >/dev/null; then
  behind=$(git rev-list --count "HEAD..origin/$c")
  if [ "$behind" -ne 0 ]; then
    echo "refusing: HEAD is $behind commit(s) behind origin/$c; rebase first:" >&2
    echo "    git rebase origin/$c" >&2
    exit 1
  fi
  ahead=$(git rev-list --count "origin/$c..HEAD")
  echo "fast-forward: $ahead commit(s) onto origin/$c"
else
  echo "creating new campaign branch origin/$c"
fi
git push origin "HEAD:refs/heads/$c"
