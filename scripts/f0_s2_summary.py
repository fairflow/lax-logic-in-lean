#!/usr/bin/env python3
"""Summarise the spike S2 measurement (`.lake/build/bin/f0s2`), 2026-10-21.

    python3 -I scripts/f0_s2_summary.py _out/f0s2-cells.jsonl [--json _out/f0s2-summary.json]

Reads the per-cell rows the measurement wrote and reports, per test set and
run:

* the cumulative fraction of cells settled by key lookup (K), by lookup plus
  union-find over `interd` (U), by order facts (O), by the decider at the
  default budget (D), at the raised node budget (D2) and at the raised emit
  cap (D3), and the cells left unknown, with times;
* for the ρ-matrix: whether the decided order is a partial order on the 22
  classes (a failure is an ALARM: two ρ would be one class); its covers
  (transitive reduction); the smallest set of ⊬ facts from which, with the
  order, every ⊬ cell follows by
      [a] ⊬ b,  a ≤ x,  y ≤ b   ⟹   [x] ⊬ y;
  and a check that covers plus that basis regenerate all 462 cells;
* the closure: every verdict of the run (T1 and the final T2 run) taken as
  a base fact and closed under the rules of the proposal's §4 (cut, and the
  propagation above).  It reports a clash as an ALARM (invariant O1), and
  lists the unknown T2 cells that the closure settles.  This is the
  "bank every decider answer as it comes" design, computed here on the
  measured verdicts, not by the Lean store;
* for each designed formula X: its place against the 22 ρ (a class ρj, ∉R,
  or unknown) and the ρ below and above it, before and after the closure.

Exit status 2 on an ALARM.
"""
import argparse
import collections
import json
import re
import statistics
import sys

TIERS = ["K", "U", "O", "D", "D2", "D3", "none"]


def load(path):
    with open(path, encoding="utf-8") as fh:
        return [json.loads(line) for line in fh if line.strip()]


def tier_table(cells):
    n = len(cells)
    by = collections.Counter(c["tier"] for c in cells)
    cum, rows = 0, []
    for t in TIERS:
        cum += by[t] if t != "none" else 0
        rows.append((t, by[t], cum))
    store_ns = [c["store_ns"] for c in cells]
    # a fresh decider call: a decided cell, or an unknown one the decider was
    # asked about (store-only runs leave `detail` empty), not a memo hit
    asked = lambda c: c["tier"] in ("D", "D2", "D3") or (c["tier"] == "none" and c["detail"])
    dec = [c["decider_ms"] for c in cells if asked(c) and not c.get("decider_reused")]
    dec_settled = [c["decider_ms"] for c in cells if c["tier"] in ("D", "D2", "D3")]
    reasons = collections.Counter(re.sub(r"[0-9]+", "N", c["detail"])[:60]
                                  for c in cells if c["tier"] == "none" and c["detail"])
    return dict(
        n=n,
        tiers={t: by[t] for t in TIERS},
        cumulative={t: (cum_, round(100 * cum_ / n, 1) if n else 0.0) for t, _, cum_ in rows if t != "none"},
        unknown=by["none"],
        unknown_reasons=dict(reasons),
        store_us_median=round(statistics.median(store_ns) / 1000, 1) if store_ns else None,
        store_us_max=round(max(store_ns) / 1000, 1) if store_ns else None,
        decider_ms_total=sum(dec),
        decider_calls_fresh=len(dec),
        decider_ms_median=statistics.median(dec_settled) if dec_settled else None,
        decider_ms_max=max(dec_settled) if dec_settled else None,
        verdicts=dict(collections.Counter(c["ans"] for c in cells)),
    )


def show(label, t):
    cum = ", ".join(f"{k} {v[0]} ({v[1]}%)" for k, v in t["cumulative"].items())
    print(f"{label}: {t['n']} cells; cumulative settled: {cum}; unknown {t['unknown']}")
    print(f"    tiers {t['tiers']}; verdicts {t['verdicts']}")
    print(f"    store tiers: median {t['store_us_median']} µs, max {t['store_us_max']} µs per cell;"
          f" decider: {t['decider_calls_fresh']} fresh calls, {t['decider_ms_total']} ms total, median {t['decider_ms_median']} ms,"
          f" max {t['decider_ms_max']} ms per decided cell")
    if t["unknown_reasons"]:
        print(f"    unknown, by reason: {t['unknown_reasons']}")


def rho_matrix(cells):
    n = 22
    le = [[i == j for j in range(n)] for i in range(n)]
    nle = set()
    unknown = []
    for c in cells:
        m = re.match(r"ρ(\d+) ⊢\? ρ(\d+)", c["name"])
        i, j = int(m.group(1)), int(m.group(2))
        if c["ans"] == "le":
            le[i][j] = True
        elif c["ans"] == "nle":
            nle.add((i, j))
        else:
            unknown.append((i, j))
    alarms = []
    for i in range(n):
        for j in range(n):
            if i != j and le[i][j] and le[j][i]:
                alarms.append(f"ρ{i} and ρ{j} are interderivable")
            if le[i][j] and (i, j) in nle:
                alarms.append(f"ρ{i}: both ⊢ and ⊬ for ρ{j}")
    # transitivity of the decided ⊢ (a failure would be an engine defect)
    for i in range(n):
        for j in range(n):
            if le[i][j]:
                for k in range(n):
                    if le[j][k] and not le[i][k]:
                        alarms.append(f"⊢ not transitive at ρ{i} ρ{j} ρ{k}")
    strict = {(i, j) for i in range(n) for j in range(n) if i != j and le[i][j]}
    covers = {(i, j) for (i, j) in strict
              if not any((i, k) in strict and (k, j) in strict for k in range(n))}
    leq = lambda a, b: a == b or le[a][b]
    basis = {(a, b) for (a, b) in nle
             if not any((a2, b2) != (a, b) and leq(a2, a) and leq(b, b2) for (a2, b2) in nle)}
    # regenerate: reflexive-transitive closure of the covers, then propagate the basis
    gen = [[i == j for j in range(n)] for i in range(n)]
    for (i, j) in covers:
        gen[i][j] = True
    for k in range(n):
        for i in range(n):
            if gen[i][k]:
                for j in range(n):
                    if gen[k][j]:
                        gen[i][j] = True
    gen_nle = {(x, y) for x in range(n) for y in range(n)
               if any(gen[a][x] and gen[y][b] for (a, b) in basis)}
    regenerated = all(gen[i][j] == le[i][j] for i in range(n) for j in range(n)) and gen_nle == nle
    return dict(le_cells=len(strict), nle_cells=len(nle), unknown=unknown,
                covers=sorted(covers), n_covers=len(covers),
                basis=sorted(basis), n_basis=len(basis),
                regenerated=regenerated, alarms=alarms)


def closure(cells):
    """Close the decided verdicts under cut and propagation (proposal §4).

    Nodes are printed formulas.  Returns the derived verdict for every
    asked cell, and the clashes (a pair with both a derived ⊢ and a
    derived ⊬)."""
    nodes = sorted({c["lhs"] for c in cells} | {c["rhs"] for c in cells})
    ix = {f: k for k, f in enumerate(nodes)}
    n = len(nodes)
    le = [[i == j for j in range(n)] for i in range(n)]
    nle = set()
    for c in cells:
        a, b = ix[c["lhs"]], ix[c["rhs"]]
        if c["ans"] == "le":
            le[a][b] = True
        elif c["ans"] == "nle":
            nle.add((a, b))
    for k in range(n):
        for i in range(n):
            if le[i][k]:
                row_k = le[k]
                row_i = le[i]
                for j in range(n):
                    if row_k[j]:
                        row_i[j] = True
    below = [[x for x in range(n) if le[x][a]] for a in range(n)]  # x ≤ a
    above = [[y for y in range(n) if le[a][y]] for a in range(n)]  # a ≤ y
    dnle = set()
    for (a, b) in nle:
        for x in above[a]:          # a ≤ x
            for y in below[b]:      # y ≤ b
                dnle.add((x, y))
    clashes = [(nodes[a], nodes[b]) for (a, b) in dnle if le[a][b]]

    def verdict(lhs, rhs):
        a, b = ix[lhs], ix[rhs]
        if le[a][b]:
            return "le"
        if (a, b) in dnle:
            return "nle"
        return "unknown"
    return verdict, clashes


def placements(cells, ans=None):
    ans = ans or (lambda c: c["ans"])
    out = {}
    groups = collections.OrderedDict()
    for c in cells:
        groups.setdefault(c["group"], []).append(c)
    for g, cs in groups.items():
        up, down = {}, {}
        for c in cs:
            m = re.match(r"X ⊢\? ρ(\d+)", c["name"])
            if m:
                up[int(m.group(1))] = ans(c)
            m = re.match(r"ρ(\d+) ⊢\? X", c["name"])
            if m:
                down[int(m.group(1))] = ans(c)
        same = [j for j in range(22) if up.get(j) == "le" and down.get(j) == "le"]
        # X and ρj are separated (not interderivable) when EITHER direction is ⊬;
        # "∉R" needs a separation from every ρ (OutsideAll, proposal §5)
        separated = [j for j in range(22) if up.get(j) == "nle" or down.get(j) == "nle"]
        undecided = [j for j in range(22) if j not in same and j not in separated]
        if same:
            place = "class " + ", ".join(f"ρ{j}" for j in same)
        elif not undecided:
            place = "∉R (separated from all 22)"
        else:
            place = "unknown"
        out[g] = dict(place=place,
                      above=[j for j in range(22) if up.get(j) == "le"],
                      below=[j for j in range(22) if down.get(j) == "le"],
                      undecided=undecided,
                      undecided_cells=[c["name"] for c in cs if ans(c) == "unknown"],
                      formula=cs[0]["lhs"] if cs[0]["name"].startswith("X") else cs[0]["rhs"])
    return out


def show_placements(pl):
    for g, p in pl.items():
        print(f"  {g}: {p['place']}; X ⊢ ρ{p['above']}; ρ ⊢ X: {p['below']};"
              f" not yet separated from ρ{p['undecided']}; open cells {p['undecided_cells']}")


def selftest(cells):
    """The gates must fail on planted faults.  Returns the number missed."""
    t1 = [c for c in cells if c["run"] == "old" and c["set"] == "T1"]
    t2 = [c for c in cells if c["set"] == "T2" and c["run"] == "old"]
    missed = 0

    def flipped(rows, pred, new):
        out, done = [], False
        for c in rows:
            if not done and pred(c):
                c = dict(c, ans=new)
                done = True
            out.append(c)
        return out, done

    def check(label, ok):
        nonlocal missed
        print(f"  selftest {label}: {'caught' if ok else 'MISSED'}")
        missed += 0 if ok else 1

    # 1. a ⊬ cell of the ρ-matrix turned into ⊢ must break the partial order
    bad, done = flipped(t1, lambda c: c["ans"] == "nle", "le")
    check("ρ-matrix ⊬ → ⊢", done and bool(rho_matrix(bad)["alarms"]))
    # 2. a ⊢ cell that is NOT a cover (it follows by transitivity) turned into
    #    ⊬ must break transitivity.  (A cover turned into ⊬ leaves another
    #    consistent partial order, which no check on the matrix alone can see.)
    covers = set(rho_matrix(t1)["covers"])
    pair = lambda c: (lambda m: (int(m.group(1)), int(m.group(2))))(re.match(r"ρ(\d+) ⊢\? ρ(\d+)", c["name"]))
    bad, done = flipped(t1, lambda c: c["ans"] == "le" and pair(c) not in covers
                        and pair(c)[0] != 0 and pair(c)[1] != 1, "nle")
    check("ρ-matrix transitive ⊢ → ⊬", done and bool(rho_matrix(bad)["alarms"]))
    # 3. a decided T2 ⊬ turned into ⊢ must give a closure clash or contradiction
    caught = False
    for k, c in enumerate(t2):
        if c["ans"] != "nle":
            continue
        bad = t2[:k] + [dict(c, ans="le")] + t2[k + 1:]
        verdict, clashes = closure(t1 + bad)
        if clashes or any(x["ans"] != "unknown" and verdict(x["lhs"], x["rhs"]) != x["ans"] for x in t1 + bad):
            caught = True
        break
    check("T2 ⊬ → ⊢ under the closure", caught)
    return missed


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("cells")
    ap.add_argument("--json", default=None)
    ap.add_argument("--selftest", action="store_true",
                    help="plant faults in the measured verdicts and require every gate to catch them")
    a = ap.parse_args()
    cells = load(a.cells)
    if a.selftest:
        missed = selftest(cells)
        print(f"selftest: {3 - missed}/3 planted faults caught")
        return 1 if missed else 0
    S = {}
    runs = collections.OrderedDict()
    for c in cells:
        runs.setdefault((c["run"], c["set"]), []).append(c)
    for (run, st), cs in runs.items():
        t = tier_table(cs)
        S[f"{run}:{st}"] = t
        show(f"[{run}] {st}", t)
    print()
    rm = rho_matrix(runs[("old", "T1")])
    S["rho_matrix"] = rm
    print(f"ρ-matrix (decided): {rm['le_cells']} ⊢, {rm['nle_cells']} ⊬, unknown {len(rm['unknown'])}")
    print(f"    covers (transitive reduction of ⊢): {rm['n_covers']}")
    print(f"    ⊬ basis (no ⊬ cell follows from another by the order): {rm['n_basis']}")
    print(f"    covers + basis regenerate all cells: {rm['regenerated']}")
    print(f"    covers: {' '.join(f'ρ{i}<ρ{j}' for i, j in rm['covers'])}")
    print(f"    ⊬ basis: {' '.join(f'[ρ{i}]⊬ρ{j}' for i, j in rm['basis'])}")
    print(f"    ALARMS: {rm['alarms'] or 'none'}")
    print()
    final_key = ("banked+D", "T2") if ("banked+D", "T2") in runs else ("old", "T2")
    final = runs.get(final_key, [])
    print(f"placements, as decided ([{final_key[0]}] T2):")
    pl = placements(final)
    S["placements"] = pl
    show_placements(pl)
    print()
    verdict, clashes = closure(runs[("old", "T1")] + final)
    settled = [c for c in final if c["ans"] == "unknown" and verdict(c["lhs"], c["rhs"]) != "unknown"]
    changed = [c for c in final if c["ans"] != "unknown" and verdict(c["lhs"], c["rhs"]) != c["ans"]]
    S["closure"] = dict(clashes=clashes, settled=len(settled),
                        settled_cells=[(c["group"], c["name"], verdict(c["lhs"], c["rhs"])) for c in settled],
                        changed=len(changed))
    print(f"closure of all decided verdicts (T1 + [{final_key[0]}] T2) under cut and propagation:")
    print(f"    clashes (O1): {len(clashes)}; decided cells it contradicts: {len(changed)}")
    print(f"    unknown T2 cells it settles: {len(settled)} of {sum(1 for c in final if c['ans'] == 'unknown')}")
    pl2 = placements(final, ans=lambda c: c["ans"] if c["ans"] != "unknown" else verdict(c["lhs"], c["rhs"]))
    S["placements_after_closure"] = pl2
    print("placements after the closure:")
    show_placements(pl2)
    if a.json:
        with open(a.json, "w", encoding="utf-8") as fh:
            json.dump(S, fh, ensure_ascii=False, indent=1)
    return 2 if rm["alarms"] or clashes or changed else 0


if __name__ == "__main__":
    sys.exit(main())
