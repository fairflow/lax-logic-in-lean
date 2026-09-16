#!/usr/bin/env python3
"""Turn the ledger JSONL into `docs/status-ledger.md`.

    scripts/ledger-report.py docs/status-ledger.jsonl docs/status-ledger.md

The JSONL is the record (one line per declaration, sorted, diffable); this is
the page a human reads.  Nothing here interprets: every number is a count of
rows, and every OPEN item is a row with `"sorry": true`.
"""
import json, subprocess, sys
from collections import Counter, defaultdict

KERNEL = {"propext", "Classical.choice", "Quot.sound"}
def is_native(ax: str) -> bool:
    """Both spellings: the three fixed axioms, and the per-declaration axiom a
    `native_decide` call mints (`X._native.native_decide.ax_1_1`)."""
    return ax in {"Lean.ofReduceBool", "Lean.ofReduceNat", "Lean.trustCompiler"} \
        or "native_decide" in ax


def area(module: str) -> str:
    """The group a module is reported under: two levels for `LaxLogic.X.Y`,
    one for everything else, so the table has ~20 rows, not 400."""
    parts = module.split(".")
    if parts[0] == "LaxLogic":
        return ".".join(parts[:3]) if len(parts) > 2 else module
    if parts[0] in ("FRJ", "wip"):
        return ".".join(parts[:2]) if len(parts) > 1 else module
    return parts[0]


def main(inp: str, outp: str) -> int:
    rows = [json.loads(l) for l in open(inp, encoding="utf-8")]
    head = subprocess.run(["git", "rev-parse", "--short", "HEAD"],
                          capture_output=True, text=True).stdout.strip()
    date = subprocess.run(["date", "+%Y-%m-%d %H:%M %Z"],
                          capture_output=True, text=True).stdout.strip()

    by_area = defaultdict(list)
    for r in rows:
        by_area[area(r["module"])].append(r)

    sorried = [r for r in rows if r["sorry"]]
    # the Lean tool's flag, cross-checked against the axiom names here: if the
    # two ever disagree the detector has drifted, and the report says so
    native = [r for r in rows if r["native"] or any(is_native(a) for a in r["axioms"])]
    disagree = [r for r in native if not r["native"]]
    thms = [r for r in rows if r["kind"] == "theorem"]
    modules = sorted({r["module"] for r in rows})

    out = []
    w = out.append
    w("# Proof-status ledger")
    w("")
    w(f"Generated {date} from `{head}` by `scripts/ledger.lean`, which asks "
      "`Lean.collectAxioms` — the same function `#print axioms` uses, and by "
      "CLAUDE.md rule 1 the only sound oracle — about every declaration of "
      "every module listed in `docs/ledger-modules.txt`.")
    w("")
    w("This file is generated.  Edit `scripts/ledger-report.py`, never the "
      "text below; `scripts/check-ledger.sh` fails if `docs/status-ledger.jsonl` "
      "no longer matches the build.")
    w("")
    w(f"**{len(rows)} declarations** in **{len(modules)} modules**: "
      f"{len(thms)} theorems, {len(rows) - len(thms)} definitions and data. "
      f"**{len(sorried)} carry `sorryAx`** and **{len(native)} are "
      "`native_decide`-tainted**; the rest are kernel-checked under the axioms "
      "shown below.")
    w("")
    w("## What the columns mean")
    w("")
    w("* **kernel-clean** — the declaration's axiom set is contained in "
      "`{propext, Classical.choice, Quot.sound}`: PROVED, in the sense of "
      "CLAUDE.md rule 1.")
    w("* **`sorryAx`** — the declaration ASSERTS something not proved. It is "
      "OPEN, whatever its statement says (`sorry-is-not-an-open-question`).")
    w("* **native** — checked by the compiler, not the kernel, so not PROVED. "
      "Two spellings count: the fixed `Lean.ofReduceBool` / `ofReduceNat` / "
      "`trustCompiler`, and the per-declaration axiom a `native_decide` call "
      "mints under Lean 4.31 (`X._native.native_decide.ax_1_1`), which a check "
      "against the three fixed names alone does not see.")
    w("")
    w("## By area")
    w("")
    w("| area | decls | theorems | kernel-clean | `sorryAx` | native |")
    w("|---|--:|--:|--:|--:|--:|")
    for a in sorted(by_area):
        rs = by_area[a]
        t = sum(1 for r in rs if r["kind"] == "theorem")
        s = sum(1 for r in rs if r["sorry"])
        n = sum(1 for r in rs if r["native"])
        clean = sum(1 for r in rs if set(r["axioms"]) <= KERNEL)
        w(f"| `{a}` | {len(rs)} | {t} | {clean} | {s or ''} | {n or ''} |")
    w("")

    w("## Axiom census")
    w("")
    w("Every distinct axiom set in the estate, most common first.")
    w("")
    w("| axioms | declarations |")
    w("|---|--:|")
    for axs, k in Counter(tuple(r["axioms"]) for r in rows).most_common():
        label = ", ".join(f"`{a}`" for a in axs) if axs else "*(none — axiom-free)*"
        w(f"| {label} | {k} |")
    w("")

    w("## OPEN: every declaration carrying `sorryAx`")
    w("")
    if not sorried:
        w("None.")
    else:
        w("| declaration | module |")
        w("|---|---|")
        for r in sorried:
            w(f"| `{r['decl']}` | `{r['module']}` |")
    w("")

    w("## `native_decide`-tainted declarations")
    w("")
    if disagree:
        w(f"**{len(disagree)} of these were missed by the tool's own flag** — "
          "`scripts/ledger.lean`'s `nativeAxiom?` needs updating.")
        w("")
    if not native:
        w("None.")
    else:
        w("These are checked by the compiler, not the kernel; they may not be "
          "cited as PROVED.")
        w("")
        w("| declaration | module |")
        w("|---|---|")
        for r in native:
            w(f"| `{r['decl']}` | `{r['module']}` |")
    w("")

    with open(outp, "w", encoding="utf-8") as f:
        f.write("\n".join(out) + "\n")
    print(f"{outp}: {len(rows)} rows, {len(sorried)} sorried, {len(native)} native")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1], sys.argv[2]))
