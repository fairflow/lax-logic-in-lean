#!/usr/bin/env bash
# Scaffold a Verso Blueprint into an existing Lean + Mathlib project.
# Repository-independent.  See BLUEPRINT-SETUP.md for why each step is
# the way it is.
#
#   usage: blueprint-scaffold.sh [--lib NAME] [--dry-run] [PROJECT_ROOT]
#
# Does four things and nothing else:
#   1. checks that verso-blueprint has a branch matching your lean-toolchain
#   2. inserts `require VersoBlueprint` ABOVE `require mathlib` in
#      lakefile.toml (order matters; see §2 of BLUEPRINT-SETUP.md)
#   3. declares a lean_lib that is NOT in defaultTargets
#   4. writes the library skeleton, generator entry point and build script
#
# It does not run `lake update` and does not commit.  Review, then run
# `lake update` yourself.
set -euo pipefail

LIB="Blueprint"; DRY=0; ROOT="."
while [ $# -gt 0 ]; do
  case "$1" in
    --lib) LIB="$2"; shift 2 ;;
    --dry-run) DRY=1; shift ;;
    -h|--help) sed -n '2,20p' "$0"; exit 0 ;;
    *) ROOT="$1"; shift ;;
  esac
done
cd "$ROOT"

say() { printf '%s\n' "$*" >&2; }
write() {
  if [ "$DRY" = 1 ]; then say "would write $1"; else
    mkdir -p "$(dirname "$1")"; cat > "$1"; say "wrote $1"; fi
}

[ -f lean-toolchain ] || { say "no lean-toolchain here: $(pwd)"; exit 2; }
[ -f lakefile.toml ]  || { say "this script only handles lakefile.toml"; exit 2; }

TC=$(sed 's|.*:||' lean-toolchain | tr -d '[:space:]')
say "project toolchain: $TC"

if command -v curl >/dev/null; then
  if curl -sfL --max-time 20 \
       "https://raw.githubusercontent.com/leanprover/verso-blueprint/$TC/lean-toolchain" \
       >/dev/null 2>&1; then
    say "verso-blueprint has a matching branch: $TC  (no toolchain bump needed)"
  else
    say "WARNING: no verso-blueprint branch '$TC'."
    say "  List them:  curl -s https://api.github.com/repos/leanprover/verso-blueprint/branches?per_page=100 | grep '\"name\"'"
    say "  Pick the nearest and expect to reconcile toolchains."
  fi
fi

# --- lakefile: require VersoBlueprint ABOVE require mathlib -----------------
if grep -q 'name = "VersoBlueprint"' lakefile.toml; then
  say "lakefile.toml already requires VersoBlueprint; leaving it alone"
elif [ "$DRY" = 1 ]; then
  say "would insert require VersoBlueprint above require mathlib"
else
  python3 - "$TC" "$LIB" <<'PY'
import re, sys
tc, lib = sys.argv[1], sys.argv[2]
s = open("lakefile.toml").read()
req = ('[[require]]\nname = "VersoBlueprint"\n'
       'git = "https://github.com/leanprover/verso-blueprint"\n'
       f'rev = "{tc}"\n\n')
m = re.search(r'^\[\[require\]\]\nname = "mathlib"', s, re.M)
if m:
    s = s[:m.start()] + req + s[m.start():]
else:                       # no mathlib: append at the end of the requires
    s = s.rstrip() + "\n\n" + req
lean_lib = (f'# {lib}: the Verso Blueprint.  Deliberately NOT in defaultTargets:\n'
            f'# it is the only target that pulls verso into the import graph.\n'
            f'[[lean_lib]]\nname = "{lib}"\n\n')
if f'name = "{lib}"' not in s:
    m2 = re.search(r'^\[\[lean_lib\]\]', s, re.M)
    s = (s[:m2.start()] + lean_lib + s[m2.start():]) if m2 else s.rstrip() + "\n\n" + lean_lib
open("lakefile.toml", "w").write(s)
PY
  say "patched lakefile.toml (VersoBlueprint above mathlib; lean_lib $LIB)"
fi

# --- skeleton ---------------------------------------------------------------
write "$LIB.lean" <<EOF
import $LIB.Document
EOF

write "$LIB/Document.lean" <<EOF
import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
-- Import the development HERE.  The arrow points this way on purpose: your
-- own files must not import verso.  See BLUEPRINT-SETUP.md §5.

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Blueprint" =>

:::group "core"
Replace this.  Labels are the commitment; everything else is cheap to change.
:::

:::theorem "first_result" (parent := "core")
State it informally here, then attach the declaration with
\`(lean := "Your.Declaration")\` so the status comes from the compiler
rather than from you.
:::

{blueprint_graph}
{blueprint_summary}
EOF

write "${LIB}Main.lean" <<EOF
import VersoManual
import VersoBlueprint.PreviewManifest
import $LIB.Document

open Verso Doc
open Verso.Genre Manual

def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.blueprintMainWithPreviewData
    (%doc $LIB.Document)
    args
    (extensionImpls := by exact extension_impls%)
EOF

write scripts/blueprint-build.sh <<EOF
#!/usr/bin/env bash
# Build the blueprint site.  We do NOT use \`lake exe vbp build\`: vbp derives
# its Lean target from the PACKAGE name, not the blueprint library, and fails
# with "unknown module [anonymous]" when they differ.  This is the command it
# runs internally.
set -euo pipefail
lake build $LIB
lake lean ${LIB}Main.lean -- --run ${LIB}Main.lean --output _out/site "\$@"
test -f _out/site/html-multi/index.html
echo "site: _out/site/html-multi/index.html"
EOF
[ "$DRY" = 1 ] || chmod +x scripts/blueprint-build.sh

say ""
say "next:"
say "  1. lake update           # check no existing pin moved"
say "  2. ./scripts/blueprint-build.sh"
say "  3. attach declarations with (lean := \"...\") — see BLUEPRINT-SETUP.md §4"
