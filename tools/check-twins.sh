#!/bin/sh
# Tools/check-twins.sh — make the Tools/ <-> wip/ split CHECKABLE.
#
# Tools/README.md says every file in Tools/ is a COPY, that the wip/
# originals are frozen, and that Tools/ is the maintained side.  Until
# 2026-08-21 nothing enforced any of that: `wip/rnFRJCerts.lean` — the
# 135-theorem certificate corpus, the actual product — still imported
# `wip.rnBank` rather than `Tools.Bank`.  Identical that day, free to
# diverge the next, with nothing to notice.
#
# The invariant this gates is the one that matters: MAINTAINED CODE MUST
# NOT IMPORT A STALE TWIN.  That is exactly "old tools get used for new
# results".  Divergence between the two copies is allowed — it is the
# point of freezing one — so divergence is REPORTED, never failed on.
#
# Exit 0 = invariant holds.  Exit 1 = a stale twin is being imported.

set -u
cd "$(dirname "$0")/.." || exit 2
fail=0

# maintained module : frozen twin
TWINS="Tools.Cert:wip.frj_cert
Tools.Pin:wip.rnpin
Tools.Search:wip.rnfrj
Tools.Derive:wip.frj_derive
Tools.Bank:wip.rnBank"

echo "=== 1. no maintained file may import a frozen twin ==="
for pair in $TWINS; do
  new=${pair%%:*}; old=${pair##*:}
  oldpath="$(echo "$old" | tr '.' '/').lean"
  # who imports the twin, other than the twin's own siblings under wip/?
  hits=$(grep -rln "^import ${old}\$" --exclude-dir=.lake --exclude-dir=.git . 2>/dev/null \
         | sed 's|^\./||' | grep -v '^wip/')
  if [ -n "$hits" ]; then
    echo "  FAIL  ${old} (frozen) is imported by, outside wip/:"
    echo "$hits" | sed 's/^/          /'
    echo "        -> import ${new} instead"
    fail=1
  else
    echo "  ok    ${old} not imported outside wip/  (maintained: ${new})"
  fi
  [ -f "$oldpath" ] || echo "        note: twin file ${oldpath} is gone"
done

echo
echo "=== 2. which frozen twins are still COMPILED at all? ==="
echo "    (README: 'left in place so any other branch still compiles' —"
echo "     on THIS branch a twin with no lake target compiles nowhere,"
echo "     so it can rot without the build noticing.)"
for pair in $TWINS; do
  old=${pair##*:}
  if grep -q "\"${old}\"" lakefile.toml 2>/dev/null; then
    echo "  built     ${old}"
  else
    echo "  UNBUILT   ${old}  — no lake target"
  fi
done

echo
echo "=== 3. divergence report (informational, never a failure) ==="
for pair in $TWINS; do
  new=${pair%%:*}; old=${pair##*:}
  a="$(echo "$new" | tr '.' '/').lean"; b="$(echo "$old" | tr '.' '/').lean"
  if [ -f "$a" ] && [ -f "$b" ]; then
    n=$(diff "$b" "$a" | grep -c '^[<>]')
    echo "  ${old} -> ${new}: ${n} differing lines"
  fi
done

echo
echo "=== 4. lakefile module paths must match git's recorded CASE ==="
echo "    (found 2026-08-21 by section 1: this clone is on case-insensitive"
echo "     APFS, where Tools/ and tools/ are ONE directory — same inode."
echo "     git recorded every file as lowercase tools/..., but lakefile"
echo "     declares the library as Tools with globs Tools.Bank etc, which"
echo "     lake resolves to Tools/Bank.lean.  On a case-SENSITIVE checkout"
echo "     — Linux CI, or a case-sensitive volume — those files land at"
echo "     tools/Bank.lean and lake finds nothing.)"
tracked=$(git ls-files)
for m in $(grep -o '"[A-Za-z][A-Za-z0-9_]*\(\.[A-Za-z][A-Za-z0-9_]*\)*"' lakefile.toml \
           | tr -d '"' | grep '\.' | sort -u); do
  path="$(echo "$m" | tr '.' '/').lean"
  # grep -x is case-SENSITIVE; `git ls-files <pathspec>` is not, under
  # core.ignorecase=true, so it cannot be used for this test.
  if [ -f "$path" ] && ! printf '%s\n' "$tracked" | grep -qx "$path"; then
    actual=$(printf '%s\n' "$tracked" | grep -ix "$path")
    if [ -n "$actual" ]; then
      echo "  CASE MISMATCH  lakefile wants ${path}"
      echo "                 git has        ${actual}"
      fail=1
    fi
  fi
done
[ "$fail" -eq 0 ] && echo "  ok    every lakefile module path matches git's case"

echo
if [ "$fail" -eq 0 ]; then
  echo "PASS: no frozen twin imported; no lakefile/git case mismatch."
else
  echo "FAIL: see the FAIL / CASE MISMATCH lines above."
fi
exit $fail
