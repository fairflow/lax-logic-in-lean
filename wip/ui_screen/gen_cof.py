#!/usr/bin/env python3
"""Cofinality instances at a candidate station from a `uifs cand` run.

usage: gen_cof.py <uifs-cand.txt> <station tag> <outdir> <Δ-name=Δ-formula> ...
For each eval fuel n present: cof_<Δ>_<n> : (E_n ∧ Δ) ⊃ A_n,
and the diagnostic A_le_<Δ>_<n> : A_n ⊃ Δ  (fails only if Δ is not the ∀p).
"""
import os, re, sys
src, tag, out = sys.argv[1], sys.argv[2], sys.argv[3]
deltas = dict(a.split("=", 1) for a in sys.argv[4:])
os.makedirs(out, exist_ok=True)
E, A = {}, {}
for line in open(src, encoding="utf-8"):
    m = re.match(rf"^{tag}_([EA]) fuel=(\d+) .*?absorbsBoxBot=\w+  (.*)$", line.rstrip("\n"))
    if m:
        (E if m.group(1) == "E" else A)[int(m.group(2))] = m.group(3)
n = 0
for f in sorted(E):
    if f not in A: continue
    for dn, d in deltas.items():
        with open(f"{out}/cof_{dn}_{f}.tsv", "w") as h:
            h.write(f"cof_{dn}_{f}\tcof\t({E[f]} ∧ {d}) ⊃ {A[f]}\n"); n += 1
        with open(f"{out}/Ale_{dn}_{f}.tsv", "w") as h:
            h.write(f"Ale_{dn}_{f}\tcof\t{A[f]} ⊃ {d}\n"); n += 1
print(f"{n} cells; fuels {sorted(E)}")
