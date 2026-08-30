#!/bin/sh
# Install the repo's git hooks into this clone.  Run once per clone; worktrees
# share the common git dir, so one install covers them all.
set -e
dir=$(git rev-parse --git-common-dir)
for h in scripts/hooks/*; do
  cp "$h" "$dir/hooks/$(basename "$h")"
  chmod +x "$dir/hooks/$(basename "$h")"
  echo "installed $(basename "$h") -> $dir/hooks/"
done
