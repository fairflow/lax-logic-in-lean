#!/usr/bin/env python3
"""Run `scripts/ledger.lean` over a module list, partitioning it as needed.

    scripts/ledger-run.py docs/ledger-modules.txt out.jsonl

The estate cannot be loaded into one environment: the `LaxLogic/ToolkitTest/`
copies re-declare the names of the modules they are copies of, and several
executable roots each define `main`.  Lean refuses such an import with

    import M failed, environment already contains 'c' from M'

so this driver starts with the whole list, and on each such refusal moves the
named module out into its own batch and retries.  The partition is therefore a
function of the module list alone — same list, same batches, same output — which
is what `scripts/check-ledger.sh` needs.

Rows from every batch are merged and sorted here (by module, then declaration,
as plain strings), so the result does not depend on how the batches fell.
"""
import json, os, re, subprocess, sys, tempfile

CLASH = re.compile(r"import (\S+) failed, environment already contains '([^']+)' from (\S+)")
IMPORT = re.compile(r"^\s*(?:public\s+|meta\s+)*import\s+([A-Za-z_][\w.]*)", re.M)


def import_graph(mods):
    """Direct imports of each module, read from its source file."""
    g = {}
    for m in mods:
        path = m.replace(".", "/") + ".lean"
        try:
            src = open(path, encoding="utf-8", errors="replace").read()
        except OSError:
            g[m] = set()
            continue
        g[m] = set(IMPORT.findall(src))
    return g


def pullers_of(target, mods, g):
    """Every module in `mods` whose transitive imports reach `target`, plus
    `target` itself: dropping just `target` is not enough, because anything
    importing it drags it back in."""
    reaches, changed = {target}, True
    while changed:
        changed = False
        for m in mods:
            if m not in reaches and (g.get(m, set()) & reaches):
                reaches.add(m)
                changed = True
    return reaches


def run_batch(mods, tmpdir, tag):
    """Run the Lean tool on `mods`. Returns (rows, clashing_module_or_None)."""
    mfile = os.path.join(tmpdir, f"mods-{tag}.txt")
    ofile = os.path.join(tmpdir, f"rows-{tag}.jsonl")
    with open(mfile, "w", encoding="utf-8") as f:
        f.write("\n".join(mods) + "\n")
    p = subprocess.run(["lake", "env", "lean", "--run", "scripts/ledger.lean", mfile, ofile],
                       capture_output=True, text=True)
    if p.returncode != 0:
        m = CLASH.search(p.stderr) or CLASH.search(p.stdout)
        if m:
            return None, m.group(1)
        sys.stderr.write(p.stdout + p.stderr)
        raise SystemExit(f"ledger: batch {tag} failed and it is not a name clash")
    rows = [json.loads(l) for l in open(ofile, encoding="utf-8")]
    return rows, None


def main(mods_file, out_file):
    mods = [l.strip() for l in open(mods_file, encoding="utf-8")
            if l.strip() and not l.startswith("#")]
    tmpdir = tempfile.mkdtemp(prefix="ledger-")
    graph = import_graph(mods)
    rows, pending, batch = [], list(mods), 0
    solo = []

    while pending:
        batch += 1
        got, clash = run_batch(pending, tmpdir, f"{batch}")
        if clash is None:
            print(f"ledger: batch {batch}: {len(pending)} modules, {len(got)} declarations")
            rows += got
            break
        drop = pullers_of(clash, pending, graph)
        print(f"ledger: batch {batch}: {clash} clashes; setting aside "
              f"{len(drop)} module(s): {', '.join(sorted(drop))}")
        pending = [m for m in pending if m not in drop]
        solo += sorted(drop)

    for i, m in enumerate(solo, start=1):
        got, clash = run_batch([m], tmpdir, f"solo{i}")
        if clash is not None:
            raise SystemExit(f"ledger: {m} still clashes when loaded alone "
                             f"(with {clash}) — its own imports conflict")
        print(f"ledger: solo {i}/{len(solo)}: {m}, {len(got)} declarations")
        rows += got

    rows.sort(key=lambda r: (r["module"], r["decl"]))
    with open(out_file, "w", encoding="utf-8") as f:
        for r in rows:
            f.write(json.dumps(r, ensure_ascii=False, separators=(",", ":"),
                               sort_keys=True) + "\n")
    print(f"ledger: {len(rows)} declarations from {len(mods)} modules "
          f"({len(solo)} loaded separately) -> {out_file}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1], sys.argv[2]))
