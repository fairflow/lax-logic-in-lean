#!/usr/bin/env python3
"""Repair the bare imports in `wip/`.

    scripts/fix-wip-imports.py --report   # what would change (default)
    scripts/fix-wip-imports.py --write    # change it

64 files under `wip/` import a sibling by its bare name — `import rnEmbed`
where the module is `wip.rnEmbed`. Lean cannot resolve those, so none of those
files has ever elaborated; the defect predates the 2026-09-16 merge.

A line is rewritten only when all three hold: the imported name has no dot, no
`<name>.lean` exists at the repository root, and `wip/<name>.lean` does. That
last condition is what makes the edit safe — the rewrite points at a file that
is there.
"""
import os, re, sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
IMPORT = re.compile(r"^(\s*import\s+)([A-Za-z_][A-Za-z0-9_']*)\s*$")


def main(write: bool) -> int:
    wipdir = os.path.join(REPO, "wip")
    changes, touched = 0, []
    for root, _dirs, files in os.walk(wipdir):
        for fn in sorted(files):
            if not fn.endswith(".lean"):
                continue
            path = os.path.join(root, fn)
            with open(path, encoding="utf-8") as f:
                lines = f.readlines()
            out, n = [], 0
            for line in lines:
                m = IMPORT.match(line.rstrip("\n"))
                if m:
                    name = m.group(2)
                    at_root = os.path.exists(os.path.join(REPO, name + ".lean"))
                    in_wip = os.path.exists(os.path.join(wipdir, name + ".lean"))
                    if not at_root and in_wip:
                        out.append(f"{m.group(1)}wip.{name}\n")
                        n += 1
                        continue
                out.append(line)
            if n:
                changes += n
                touched.append((os.path.relpath(path, REPO), n))
                if write:
                    with open(path, "w", encoding="utf-8") as f:
                        f.writelines(out)
    for p, n in touched:
        print(f"{'rewrote' if write else 'would rewrite'} {n:2d} import(s) in {p}")
    print(f"{len(touched)} file(s), {changes} import line(s)"
          + ("" if write else " — pass --write to apply"))
    return 0


if __name__ == "__main__":
    sys.exit(main(write="--write" in sys.argv))
