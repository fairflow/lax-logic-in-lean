#!/usr/bin/env python3
"""The figures of the F0 paper, generated from data that Lean computed.

    scripts/f0-figures.py            (run by scripts/f0-paper.sh before the paper)

1. `lake env lean tools/F0/FigureData.lean` prints `F0FIGURES <json>`: the
   rung covers decided by `rungCovers`/`rungLe` (wip/ladder8.lean), the
   elements of `D5_list` and the cover theorems of wip/f0Covers.lean read off
   their types, the formula trees of the rungs, and two decided identities of
   the substitution sigma.
2. Every theorem or definition a figure cites is `#check`ed: the script writes
   docs/f0-paper-figures/check.lean and runs Lean on it; one failure stops it.
3. Graphviz lays out each figure: docs/f0-paper-figures/<name>.svg (text as
   paths, inlined in the HTML) and <name>.pdf (included in the PDF).  The
   ladders are laid out by `dot`; the self-similarity figure places the
   ladder `dot` computed twice, side by side, and draws its regions around
   them (`neato -n2`, fixed positions).

Nothing is drawn that the data does not give: every edge is a covering pair
decided by `rungCovers`, a cover theorem, or a sigma theorem named in the
figure or its caption; the regions of the self-similarity figure are
schematic (positions not to scale).  Written 2026-10-23 for v0.3 of the paper.

v0.4 (2026-10-24): the PDF includes each figure at its natural size, so a
label prints at the size set in scripts/paperfig.py, FS points, the size of
the body text.  A figure wider than the text block (MAXW) stops the script:
content is reduced (fewer rungs, the key moved to the caption, the copies
panel placed below the ladders when the two do not fit side by side), never
the type.  The reading, checking and drawing are shared with Paper I
(scripts/paperfig.py, since 2026-10-24).
"""
import os
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import paperfig  # noqa: E402  (the helpers shared with scripts/sem-figures.py)
from paperfig import (FONT, FS, MAXW, SUB, GREY, BLUE, GREEN,  # noqa: E402
                      lab, header, text_width, box)

OUT = "docs/f0-paper-figures"
TAG = "f0-figures"


def t(k):
    return "t" + str(k).translate(SUB)


def render(tree, named, k):
    """One-step label of formula k: subformulas equal to an earlier rung are named."""
    def name(x):
        for j in range(k):
            if named[j] == x:
                return full(x) if len(full(x)) <= 3 else t(j)
        return full(x)

    def full(x):
        op = x["op"]
        if op == "bot":
            return "⊥"
        if op == "atom":
            return x["name"]
        a = x["args"]
        if op == "box":
            return "◯" + full(a[0])
        if op == "imp" and a[1]["op"] == "bot":
            return "¬" + full(a[0])
        sym = {"and": " ∧ ", "or": " ∨ ", "imp": " ↠ "}[op]
        return "(" + full(a[0]) + sym + full(a[1]) + ")"

    op = tree["op"]
    if op == "bot":
        return "⊥"
    a = tree.get("args", [])
    if op == "box":
        return "◯" + name(a[0])
    if op == "imp" and a[1]["op"] == "bot":
        return "¬" + name(a[0])
    sym = {"and": " ∧ ", "or": " ∨ ", "imp": " ↠ "}[op]
    return name(a[0]) + sym + name(a[1])


def bottom(d):
    nodes = d["bottomNodes"]
    assert d["bottomListLength"] == len(nodes), "every element of D5_list must be a rung"
    s = header("bottom")
    for k in nodes:
        s += f'  n{k} [label={lab(t(k) + " = " + render(d["formulas"][k], d["formulas"], k))}];\n'
    for c in d["covers"]:
        assert c["lo"] in nodes and c["hi"] in nodes
        s += f'  n{c["lo"]} -- n{c["hi"]};\n'
    s += "}\n"
    names = [c["theorem"] for c in d["covers"]] + ["PLLND.F0.D5_list", "PLLND.F0.D5_table"]
    return s, names, "dot"


def rungs(d):
    # left to right: a long chain lies better across the page
    s = header("rungs").replace("rankdir=BT", "rankdir=LR", 1)
    for k in range(12):
        s += f'  n{k} [label="{t(k)}"];\n'
    for i, j in d["rungs12"]:
        s += f'  n{i} -- n{j};\n'
    s += "}\n"
    return s, ["PLLND.RNEmbed.rungLe", "PLLND.RNEmbed.rungCovers",
               "PLLND.RNEmbed.rnSub_order"], "dot"


def sigma_label(k):
    if k == 0:
        return "σ(t₀) = t₃"
    if k == 3:
        return "σ(t₃) = ◯t₃ ∨ g₁"
    return f"σ({t(k)})"


def ladder_layout(pairs, n):
    """`dot`'s layout of the rung order on t₀ … t_{n-1}, with the wider labels
    of the second ladder: {k: (x, y, width)} in points."""
    s = header("L")
    for k in range(n):
        s += f'  n{k} [label={lab(sigma_label(k))}];\n'
    for i, j in pairs:
        s += f'  n{i} -- n{j};\n'
    s += "}\n"
    p = subprocess.run(["dot", "-Tplain"], input=s, capture_output=True, text=True,
                       errors="replace")
    if p.returncode != 0:
        sys.exit(f"{TAG}: dot -Tplain failed:\n" + p.stderr)
    pos = {}
    for line in p.stdout.splitlines():
        f = line.split()
        if f and f[0] == "node":
            pos[int(f[1][1:])] = (float(f[2]) * 72, float(f[3]) * 72, float(f[4]) * 72)
    return pos


def selfsim(d):
    assert d["sigBotIsT3"] and d["sigT3IsC1OrG1"]
    # six rungs: t₀ … t₅ hold the two decided images, σ(t₀) and σ(t₃)
    n = 6
    pairs = d["rungs6"]
    pos = ladder_layout(pairs, n)
    xs = [x for (x, _, _) in pos.values()]
    ys = [y for (_, y, _) in pos.values()]
    half = max(w for (_, _, w) in pos.values()) / 2
    x0, x1 = min(xs) - half - 8, max(xs) + half + 8
    y0, y1 = min(ys) - 2.6 * FS, max(ys) + 1.6 * FS
    gap = 44
    dx = (x1 - x0) + gap
    s = (f'graph selfsim {{\n  splines=line; outputorder=nodesfirst; margin=0; pad=0.06;\n'
         f'  node [shape=plaintext, fontname="{FONT}", fontsize={FS}, margin="0.04,0.03", width=0.1, height=0.1];\n'
         f'  edge [fontname="{FONT}", fontsize={FS}];\n')
    # panel 1: the ladder in F0 and its image under sigma in [t3, top]
    s += box("boxA", x0, y0, x1, y1, GREY, "F₀")
    s += box("boxB", x0 + dx, y0, x1 + dx, y1, BLUE, "σ(F₀) ⊆ [t₃, ⊤]")
    for k, (x, y, _) in pos.items():
        s += f'  a{k} [label={lab(t(k))}, pos="{x:.1f},{y:.1f}!"];\n'
        s += f'  b{k} [label={lab(sigma_label(k), BLUE)}, pos="{x + dx:.1f},{y:.1f}!"];\n'
    for i, j in pairs:
        s += f'  a{i} -- a{j};\n'
        s += f'  b{i} -- b{j} [color="{BLUE}"];\n'
    # sigma, drawn once, as the map from the first ladder to the second
    ym = (y0 + y1) / 2
    s += f'  p1 [shape=point, width=0.01, style=invis, pos="{x1 + 4:.1f},{ym:.1f}!"];\n'
    s += f'  p2 [shape=point, width=0.01, style=invis, pos="{x0 + dx - 4:.1f},{ym:.1f}!"];\n'
    s += (f'  p1 -- p2 [dir=forward, color="{BLUE}", penwidth=1.2, arrowsize=0.8];\n'
          f'  sigl [label={lab("σ", BLUE, FS + 3)}, pos="{(x1 + x0 + dx) / 2:.1f},{ym + FS:.1f}!"];\n')
    right1 = x1 + dx
    # panel 2: the nested copies sigma^n(F0) and their bases; the theorems
    # behind it are named in the caption
    bases = ["⊥", "σ(⊥) = t₃", "σ²(⊥)"]
    regions = ["F₀", "σ(F₀)", "σ²(F₀)"]
    colours = [GREY, BLUE, GREEN]
    inset, step = 16, 3.8 * FS
    # the innermost box holds its name at the left and its base in the middle
    w_in = 2 * (text_width(regions[-1]) + 8) + text_width(bases[1]) + 8
    widths = [w_in + 2 * inset * (len(regions) - 1 - i) for i in range(len(regions))]
    w2 = widths[0]
    # beside the ladders when the whole fits the text block, else below them
    side = (right1 - x0) + 30 + w2 <= MAXW
    # local heights: the bases from 0 up, the tops of the boxes above the last
    loc = [step * i for i in range(len(regions) + 1)]
    loc_top = loc[-1] + 1.4 * FS + 6 * (len(regions) - 1)
    loc_bot = -1.6 * FS
    if side:
        cx = right1 + 30 + w2 / 2
        oy = (y0 + y1) / 2 - (loc_top + loc_bot) / 2
    else:
        cx = (x0 + right1) / 2
        oy = y0 - 20 - loc_top
    by = [oy + v for v in loc]
    top = by[-1] + 1.4 * FS
    for i in range(len(regions)):
        w = widths[i]
        s += box(f"r{i}", cx - w / 2, by[i] - 1.6 * FS, cx + w / 2, top + 6 * (len(regions) - 1 - i),
                 colours[i], regions[i])
        s += f'  c{i} [label={lab(bases[i], colours[i])}, pos="{cx:.1f},{by[i]:.1f}!"];\n'
    s += f'  c{len(regions)} [label="⋮", pos="{cx:.1f},{by[-1]:.1f}!"];\n'
    for i in range(len(regions)):
        s += f'  c{i} -- c{i + 1};\n'
    s += "}\n"
    names = ["PLLND.F0.Sig.sig", "PLLND.F0.Sig.sigN", "PLLND.F0.Sig.sig_t3",
             "PLLND.F0.Sig.sigN_faithful", "PLLND.F0.Sig.sigN_bot_le",
             "PLLND.F0.Sig.sigN_bot_strict", "PLLND.F0.Sig.copies_strict",
             "PLLND.RNEmbed.rungCovers", "PLLND.RNEmbed.rnSub_order"]
    return s, names, "neato"


def main():
    os.chdir(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
    d = paperfig.lean_data("tools/F0/FigureData.lean", "F0FIGURES", TAG)
    figs = {"bottom": bottom(d), "rungs": rungs(d), "selfsim": selfsim(d)}
    paperfig.run(figs, OUT, ["wip.f0Covers", "wip.ladder8", "wip.f0SelfSim"], TAG)


if __name__ == "__main__":
    main()
