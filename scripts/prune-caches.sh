#!/usr/bin/env bash
# Delete the Actions caches on `main` whose key starts with PREFIX, except KEEP.
#
#   scripts/prune-caches.sh <key-prefix> <key-to-keep>
#
# Run by the workflows after they save a cache, so `main` holds one cache per
# kind and the repository stays inside its 10 GB quota.  Needs `GH_TOKEN` with
# `actions: write`.  Never fails the run: a cache left behind costs space, not
# correctness.  If KEEP is not among the caches (the save did not happen),
# nothing is deleted.
set -uo pipefail
prefix=$1 keep=$2
repo=${GITHUB_REPOSITORY:?}
list=$(gh cache list --repo "$repo" --ref refs/heads/main --key "$prefix" \
         --limit 100 --json id,key -q '.[] | [.id, .key] | @tsv') || { echo "prune: cannot list caches"; exit 0; }
if ! printf '%s\n' "$list" | cut -f2 | grep -qxF "$keep"; then
  echo "prune: $keep is not saved; deleting nothing"; exit 0
fi
printf '%s\n' "$list" | while IFS=$'\t' read -r id key; do
  [ -z "$id" ] || [ "$key" = "$keep" ] && continue
  echo "prune: deleting $key"
  gh cache delete "$id" --repo "$repo" || true
done
exit 0
