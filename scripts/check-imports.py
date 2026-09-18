#!/usr/bin/env python3
"""Every `import` in the tree names a module that exists.

    scripts/check-imports.py [--quiet]

Exit 0 if every import resolves, 1 otherwise, naming each unresolvable module
and the files that import it.

WHY THIS EXISTS.  The 2026-09-16 merge deleted `LJF/Complete.lean` in favour of
`LaxLogic/Focusing/LJFComplete.lean` and left one file importing the old name:
`wip/ui_routeB_n4.lean`.  That file stopped compiling, and with it thirty
`wip/ui_routeB_*` modules — the whole halted `interpR` line — none of which is
in `defaultTargets`, so nothing noticed.  The consequence was not a build
failure but a SILENT HOLE IN THE ESTATE: the proof-status ledger reads what
builds, so a documented PROVED result (`hasUI_of_stabilises`, N3) sat outside
every check for two days, and a sorried blueprint stub of the same name made
the reconciliation report it as CONTRADICTED rather than absent.

The check is static and takes a second.  It is the cheapest possible guard on
the thing that actually goes wrong after a merge, and it does not need a build.

WHAT IT DOES NOT CHECK: that a module builds.  An import can resolve to a file
that does not compile.  `scripts/check-ledger.sh` is the check for that, and it
is the expensive one.
"""
import os
import re
import sys

# package roots that live outside this repository, plus Lean's own
EXTERNAL = {
    "Mathlib", "Batteries", "Std", "Lean", "Init", "Plausible", "ImportGraph",
    "Qq", "Aesop", "ProofWidgets", "Cli", "LeanSearchClient", "Verso",
    "SubVerso", "MD4Lean", "VersoManual", "VersoBlog", "VersoBlueprint",
    # the Lean–Wolfram bridge: the sibling repository `mathematica-in-lean`,
    # put on LEAN_PATH by `scripts/clp-wolfram.sh` rather than made a Lake
    # dependency, and imported by exactly one file that nothing imports
    # (`LaxLogic/QLL/CLPWolfram.lean`, whose header says so).
    "Mathematica",
}

# sub-trees with their own module layout, or self-declared superseded
SKIP_DIRS = ("./.lake", "./.git", "./Archive", "./tools/FrontierSampler")

IMPORT = re.compile(r"^import\s+([A-Za-z0-9_.]+)\s*$")


def header_imports(text):
    """The module names imported by a file.

    Lean puts the whole import block at the top, before anything but comments,
    so the imports are the prefix of the file — and scanning the WHOLE file
    instead reads prose: `wip/towerpin.lean` has a docstring line beginning
    "import both, and checks …", and `LaxLogic/PLLSubformulaSet.lean` one
    beginning "import closure of `lake exe pll`".  Both are English.
    """
    depth = 0
    for line in text.splitlines():
        s = line.strip()
        if depth:
            depth += s.count("/-") - s.count("-/")
            continue
        if not s or s.startswith("--"):
            continue
        if s.startswith("/-"):
            depth = 1 + s.count("/-") - s.count("-/") - 1
            continue
        m = IMPORT.match(s)
        if m:
            yield m.group(1)
            continue
        return


def lean_files(root="."):
    for dirpath, dirnames, filenames in os.walk(root):
        if any(dirpath == d or dirpath.startswith(d + "/") for d in SKIP_DIRS):
            dirnames[:] = []
            continue
        for f in filenames:
            if f.endswith(".lean"):
                yield os.path.join(dirpath, f)


def main(argv):
    quiet = "--quiet" in argv
    here = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    os.chdir(here)

    modules = set()
    for p in lean_files():
        modules.add(os.path.relpath(p, ".")[:-5].replace("/", "."))

    bad = {}
    n_imports = 0
    for p in lean_files():
        try:
            text = open(p, encoding="utf-8", errors="replace").read()
        except OSError as e:
            print(f"check-imports: cannot read {p}: {e}")
            return 1
        for name in header_imports(text):
            n_imports += 1
            if name in modules or name.split(".")[0] in EXTERNAL:
                continue
            bad.setdefault(name, []).append(os.path.relpath(p, "."))

    if not bad:
        if not quiet:
            print(f"check-imports: {n_imports} imports in {len(modules)} modules, "
                  "every one resolves")
        return 0

    print(f"check-imports: {len(bad)} unresolvable import name(s)")
    for name in sorted(bad):
        print(f"  {name}")
        for f in sorted(bad[name]):
            print(f"      imported by {f}")
    return 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
