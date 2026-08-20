#!/usr/bin/env python3
"""Structural audit of the publishable core.

The Lean build already checks what Lean can see: every module elaborates,
every `#guard_msgs` axiom pin matches, and no declaration uses `sorry`.
This script checks what Lean cannot see, namely the *boundary* of the core:

  1. no module reachable from `Core.lean` imports a `wip.*` module;
  2. no module reachable from `Core.lean` imports a module belonging to a
     trimmed campaign (a campaign whose terminal result is OPEN);
  3. every module reachable from `Core.lean` carries a module docstring;
  4. no module reachable from `Core.lean` contains a `sorry`.

Run `scripts/core-audit.py` for a report, `--check` to exit non-zero on
any failure (this is what CI runs).
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# Campaigns trimmed from the core because their terminal result is OPEN.
# A module matching any of these prefixes must not be reachable from Core.
TRIMMED_PREFIXES = (
    "LaxLogic.PLLSemUI",     # semantic uniform interpolation (Litak-Visser)
    "LaxLogic.PLLG4UI",      # uniform interpolation via the G4c tower
    "LaxLogic.PLLG4Tower",   # ditto; states its own open question
    "LaxLogic.PLLG4PInv",    # dead metatheory branch of the first repair
    "LaxLogic.PLLG4PAdm",
    "LaxLogic.PLLG4PStr",
    "LaxLogic.IPCFocused",
    "LaxLogic.PLLFocused",
    "LaxLogic.PLLPolar",
    "LaxLogic.PLLJudgmental",
    "LaxLogic.PLLCandidate",
    "LaxLogic.PLLCandOr",
    "LaxLogic.PLLCandLeast",
    "LaxLogic.PLLUIChains",
    "LaxLogic.PLLExec",      # drags the UI tower in
    "LaxLogic.BeliefExamplesNative",
    "FRJO.",                 # FRJ-circle completeness PAUSED
    "BiLax.",                # duality bridge never attempted
    "Rewrite.",              # mechanism finished, rule data is not
    "wip.",                  # campaign material by construction
)

# The `LJF` family needs exact names, not a prefix: `LaxLogic.LJF`,
# `LJFComplete`, `LJFOCore` and `LJFOBridge` ARE in the core — focalization
# for PLL and uniform interpolation for IPC are finished, sorry-free
# results — while the tail below pursues uniform interpolation for PLL,
# which is OPEN.  A prefix would catch both halves.
TRIMMED_MODULES = frozenset({
    "LaxLogic.LJFO",         # the minimality tail; carries `CimpAnt`
    "LaxLogic.LJFOAudit",
    "LaxLogic.LJFOFuel",
    "LaxLogic.LJFOHeight",
    "LaxLogic.LJFORows",
    "LaxLogic.LJFOSearch",
    "LaxLogic.LJFOUniverse",
})

IMPORT_RE = re.compile(r"^import\s+([A-Za-z0-9_.]+)", re.M)
# `sorry` as a term, not as part of a longer identifier and not in a string.
SORRY_RE = re.compile(r"(?<![A-Za-z0-9_.])sorry(?![A-Za-z0-9_])")


def module_path(mod: str) -> Path | None:
    """Repo file for a module name, or None if the module is external."""
    p = ROOT / (mod.replace(".", "/") + ".lean")
    return p if p.is_file() else None


def imports_of(path: Path) -> list[str]:
    return IMPORT_RE.findall(path.read_text(encoding="utf-8"))


def closure(roots: list[str]) -> dict[str, Path]:
    """Transitive import closure, restricted to modules that are repo files."""
    seen: dict[str, Path] = {}
    stack = list(roots)
    while stack:
        mod = stack.pop()
        if mod in seen:
            continue
        p = module_path(mod)
        if p is None:          # Mathlib, Batteries, core: not ours to audit
            continue
        seen[mod] = p
        stack.extend(imports_of(p))
    return seen


def has_module_docstring(path: Path) -> bool:
    """True if the file opens with a `/-! ... -/` module docstring or a
    `/- ... -/` header comment, before or just after the import block."""
    text = path.read_text(encoding="utf-8")
    # Strip the import block and any blank lines, then look at what starts the file.
    stripped = re.sub(r"^(?:import [^\n]*\n|\s*\n)+", "", text, count=1)
    head = stripped[:400]
    return head.startswith("/-!") or head.startswith("/-\n") or head.startswith("/- ")


def strip_comments_and_strings(text: str) -> str:
    """Crude but adequate: remove block comments, line comments and string
    literals, so `sorry` inside prose does not count as a `sorry`."""
    text = re.sub(r"/-.*?-/", " ", text, flags=re.S)
    text = re.sub(r"--[^\n]*", " ", text)
    text = re.sub(r'"(?:[^"\\]|\\.)*"', '""', text, flags=re.S)
    return text


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--check", action="store_true",
                    help="exit non-zero on any failure (for CI)")
    args = ap.parse_args()

    core = ROOT / "Core.lean"
    if not core.is_file():
        print("core-audit: Core.lean not found", file=sys.stderr)
        return 2

    roots = imports_of(core)
    mods = closure(roots)

    failures: list[str] = []

    # 1 + 2. Boundary: nothing trimmed, nothing from wip/, is reachable.
    for mod, path in sorted(mods.items()):
        for imp in imports_of(path):
            if imp.startswith(TRIMMED_PREFIXES) or imp in TRIMMED_MODULES:
                failures.append(
                    f"boundary: {mod} ({path.relative_to(ROOT)}) imports "
                    f"trimmed/wip module {imp}")

    # 3. Documentation.
    undocumented = [mod for mod, path in sorted(mods.items())
                    if not has_module_docstring(path)]
    for mod in undocumented:
        failures.append(f"docstring: {mod} has no module docstring")

    # 4. No sorry.
    for mod, path in sorted(mods.items()):
        code = strip_comments_and_strings(path.read_text(encoding="utf-8"))
        if SORRY_RE.search(code):
            failures.append(f"sorry: {mod} ({path.relative_to(ROOT)}) contains a sorry")

    print(f"core-audit: {len(roots)} roots in Core.lean, "
          f"{len(mods)} modules in the closure")
    if failures:
        print(f"core-audit: {len(failures)} FAILURE(S)")
        for f in failures:
            print(f"  {f}")
    else:
        print("core-audit: clean — closed boundary, all documented, no sorry")

    return 1 if (failures and args.check) else 0


if __name__ == "__main__":
    sys.exit(main())
