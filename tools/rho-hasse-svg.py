#!/usr/bin/env python3
"""Draw the scoped PLL Hasse diagram from `lake exe rhocover` output.

Usage:  tools/rho-hasse-svg.py <rhocover-output.txt> <out.svg>

Everything is data-driven from the run output — cover edges (`HASSE`),
open cells (`OPEN CELL`), class labels and discovery stars (`LABEL`) —
so the drawing can never go stale against the sweep.  The script
REFUSES to draw a run whose control failed, and refuses a run with no
`RHOCOVER-DONE` marker (a killed run is not a diagram).

Layout: longest-path layering from the unique minimum, then barycenter
ordering (8 sweeps).  Open cells are drawn dashed with a `?`: each is
a cell whose POSITIVE resolution would add that strict pair (the sweep
guarantees the converse direction is settled ⊬, else it would have
been an OPEN edge, which the sweep reports separately and this script
draws in red).
"""
import sys, re, collections, statistics

def main():
    if len(sys.argv) != 3:
        sys.exit(__doc__)
    text = open(sys.argv[1], encoding="utf-8").read()
    if "RHOCOVER-DONE" not in text:
        sys.exit("REFUSED: no RHOCOVER-DONE marker — incomplete run")
    if "CONTROL FAILED" in text:
        sys.exit("REFUSED: the run's control failed — do not draw it")

    edges = [(int(a), int(b)) for a, b in re.findall(r"HASSE ρ(\d+) ⋖ ρ(\d+)", text)]
    open_cells = [(int(a), int(b)) for a, b in re.findall(r"OPEN CELL ρ(\d+) ⊢\? ρ(\d+)", text)]
    open_edges = [(int(a), int(b)) for a, b in re.findall(r"OPEN    ρ(\d+) <⋖\? ρ(\d+)", text)]
    label, new = {}, set()
    for m in re.finditer(r"^LABEL ρ(\d+)(\*?) (.+)$", text, re.M):
        i = int(m.group(1))
        label[i] = m.group(3)
        if m.group(2):
            new.add(i)
    if not edges:
        sys.exit("REFUSED: no HASSE edges found")
    nodes = sorted({v for e in edges for v in e} | set(label))

    succ, pred = collections.defaultdict(list), collections.defaultdict(list)
    for a, b in edges:
        succ[a].append(b)
        pred[b].append(a)
    roots = [v for v in nodes if not pred[v]]
    layer = {v: 0 for v in roots}
    changed = True
    while changed:
        changed = False
        for a, b in edges:
            if a in layer and layer.get(b, -1) < layer[a] + 1:
                layer[b] = layer[a] + 1
                changed = True
    L = collections.defaultdict(list)
    for v in nodes:
        L[layer.get(v, 0)].append(v)
    maxl = max(L)
    order = {l: sorted(L[l]) for l in L}
    for _ in range(8):
        for l in range(1, maxl + 1):
            pos = {v: i for i, v in enumerate(order[l - 1])}
            mid = len(order[l - 1]) / 2
            order[l].sort(key=lambda v: statistics.mean([pos.get(p, mid) for p in pred[v]]) if pred[v] else 0)
        for l in range(maxl - 1, -1, -1):
            if l + 1 > maxl:
                continue
            pos = {v: i for i, v in enumerate(order[l + 1])}
            mid = len(order[l + 1]) / 2
            order[l].sort(key=lambda v: statistics.mean([pos.get(s, mid) for s in succ[v]]) if succ[v] else 0)

    W, LH, TOP = 1240, 110, 60
    xy = {}
    for l in range(maxl + 1):
        row = order[l]
        for i, v in enumerate(row):
            xy[v] = ((i + 1) * W / (len(row) + 1), TOP + (maxl - l) * LH)
    H = TOP + maxl * LH + 70
    out = [f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {W} {H}" font-family="Helvetica, Arial, sans-serif">',
           f'<rect width="{W}" height="{H}" fill="#ffffff"/>',
           f'<text x="20" y="30" font-size="17" fill="#111">RN(◯,∅) catalogue — PLL Hasse diagram, scoped covers '
           f'({len(edges)} edges{", " + str(len(open_edges)) + " OPEN edges" if open_edges else ""})</text>',
           f'<text x="20" y="{H-18}" font-size="12" fill="#666">solid: a ⋖[catalogue] b, every interposer excluded '
           f'by settled cells · dashed grey ?: open cell — a positive resolution would add that edge'
           f'{" · red: OPEN cover edge" if open_edges else ""}</text>']
    for a, b in edges:
        (x1, y1), (x2, y2) = xy[a], xy[b]
        out.append(f'<line x1="{x1:.0f}" y1="{y1-26:.0f}" x2="{x2:.0f}" y2="{y2+14:.0f}" stroke="#3556a8" stroke-width="1.4"/>')
    for a, b in open_edges:
        (x1, y1), (x2, y2) = xy[a], xy[b]
        out.append(f'<line x1="{x1:.0f}" y1="{y1-26:.0f}" x2="{x2:.0f}" y2="{y2+14:.0f}" stroke="#c03030" stroke-width="1.6" stroke-dasharray="7,4"/>')
    for a, b in open_cells:
        if a in xy and b in xy:
            (x1, y1), (x2, y2) = xy[a], xy[b]
            out.append(f'<line x1="{x1:.0f}" y1="{y1-26:.0f}" x2="{x2:.0f}" y2="{y2+14:.0f}" stroke="#999" stroke-width="1.3" stroke-dasharray="5,4"/>')
            out.append(f'<text x="{(x1+x2)/2+4:.0f}" y="{(y1+y2)/2:.0f}" font-size="12" fill="#888">?</text>')
    for v, (x, y) in xy.items():
        star = ""
        out.append(f'<circle cx="{x:.0f}" cy="{y:.0f}" r="4" fill="#16305e"/>')
        out.append(f'<text x="{x:.0f}" y="{y-12:.0f}" font-size="14" font-weight="bold" fill="#16305e" text-anchor="middle">ρ{v}{star}</text>')
        out.append(f'<text x="{x:.0f}" y="{y+20:.0f}" font-size="11.5" fill="#333" text-anchor="middle">{label.get(v, "")}</text>')
    out.append('</svg>')
    open(sys.argv[2], "w", encoding="utf-8").write("\n".join(out))
    print(f"wrote {sys.argv[2]}: {len(nodes)} nodes, {len(edges)} cover edges, "
          f"{len(open_edges)} open edges, {len(open_cells)} open cells, layers {maxl+1}")

if __name__ == "__main__":
    main()
