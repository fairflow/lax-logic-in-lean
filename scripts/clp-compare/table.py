#!/usr/bin/env python3
"""Tabulate scripts/clp-compare/results.jsonl for the CLP paper's Section 12.

    scripts/clp-compare/table.py results.jsonl [--verso]

Per duration D: (a) the compiled untrusted producer (search, then the
arithmetic certificates), (b) the compiled checkers, (c) the kernel checks
(answer soundness through lean-certify; the arithmetic outside it), (d)
SWI-Prolog clpq, and the ratios of (a) and of (b) to (d).  Each stage's median,
in milliseconds unless marked, (a) and (b) being sums of their stages'
medians; a missing figure was not run.  With
--verso, the table is printed as the paper's `:::wtable` markup.  Also checks
that both systems found the same P.
"""
import json, sys

rows = [json.loads(l) for l in open(sys.argv[1], encoding="utf-8")]
verso = "--verso" in sys.argv
swi = {r["D"]: r for r in rows if r.get("layer") == "swi" and "median_s" in r}
lean = {r["D"]: r for r in rows if r.get("layer") == "lean" and "search_ms" in r}
kern = {}
for r in rows:
    if r.get("layer") == "kernel" and "median_ms" in r:
        kern[(r["D"], r["check"])] = r["median_ms"]


def same_p(d):
    if d not in swi or d not in lean:
        return None
    return swi[d]["P"].replace("r", "/") == lean[d]["P"]


def f(x):
    if x is None:
        return "—"
    if x >= 100000:
        return "%.0f s" % (x / 1000)
    if x >= 10000:
        return "%.1f s" % (x / 1000)
    if x >= 1000:
        return "%.2f s" % (x / 1000)
    if x >= 100:
        return "%.0f" % x
    if x >= 10:
        return "%.1f" % x
    return "%.2f" % x


def ratio(x, y):
    return "—" if x is None or y is None else "%.0f" % (x / y)


out = []
for d in sorted(set(swi) | set(lean)):
    L = lean.get(d)
    a = L["search_ms"] + L["arith_ms"] if L else None
    b = (L["check_tree_ms"] + L["check_sat_ms"] + L["check_below_ms"] + L["check_above_ms"]) if L else None
    s = swi[d]["median_s"] * 1000 if d in swi else None
    rb = "—" if b is None or s is None else "%.1f" % (b / s)
    out.append((d, L["tree_nodes"] if L else None, a, b, kern.get((d, "answerK")), kern.get((d, "arith")),
                s, ratio(a, s), rb, same_p(d), L["reps"] if L else None))

head = ["D", "tree nodes", "(a) search + arithmetic", "(b) compiled checks", "(c) kernel: answer",
        "(c) kernel: arithmetic", "(d) SWI clpq", "(a)/(d)", "(b)/(d)"]
if verso:
    print(':::wtable (widths := "0.07 0.09 0.15 0.12 0.12 0.13 0.11 0.10 0.11") +header')
    print("*")
    for h in ["$`D`"] + head[1:]:
        print("  * " + h)
    for (d, n, a, b, ka, kr, s, r1, r2, same, reps) in out:
        print("*")
        for c in [str(d), "—" if n is None else str(n), f(a), f(b), f(ka), f(kr), f(s), r1, r2]:
            print("  * " + c)
    print(":::")
else:
    print("\t".join(head + ["same P", "Lean reps"]))
    for row in out:
        print("\t".join("—" if x is None else (f(x) if isinstance(x, float) else str(x)) for x in row))
