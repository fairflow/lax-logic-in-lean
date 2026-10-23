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
"""
import json
import os
import re
import subprocess
import sys

OUT = "docs/f0-paper-figures"
FONT = "STIX Two Math"
SUB = str.maketrans("0123456789", "₀₁₂₃₄₅₆₇₈₉")
GREY, BLUE, GREEN, BROWN = "#888888", "#3060a0", "#2a8a5a", "#a05a20"


def t(k):
    return "t" + str(k).translate(SUB)


def lean_data():
    p = subprocess.run(["lake", "env", "lean", "tools/F0/FigureData.lean"],
                       capture_output=True, text=True)
    if p.returncode != 0:
        sys.exit("f0-figures: the data emitter failed:\n" + p.stdout + p.stderr)
    for line in p.stdout.splitlines():
        if line.startswith("F0FIGURES "):
            return json.loads(line[len("F0FIGURES "):])
    sys.exit("f0-figures: no F0FIGURES line in the emitter's output")


def check_names(names):
    """#check every cited declaration in the compiled library."""
    os.makedirs(OUT, exist_ok=True)
    path = os.path.join(OUT, "check.lean")
    with open(path, "w") as f:
        f.write("import wip.f0Covers\nimport wip.ladder8\nimport wip.f0SelfSim\n\n")
        for n in names:
            f.write("#check @" + n + "\n")
    p = subprocess.run(["lake", "env", "lean", path], capture_output=True, text=True)
    out = p.stdout + p.stderr
    if p.returncode != 0 or "error" in out:
        sys.exit("f0-figures: a cited name does not resolve:\n" + out)
    print(f"  f0-figures: {len(names)} cited names resolve")


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


def lab(text, colour=None, size=None):
    """A graphviz HTML-like label: the circle of the modality (U+25EF, a large
    circle in STIX) set smaller, so that it sits at letter height."""
    s = text.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")
    s = s.replace("◯", '<FONT POINT-SIZE="8">◯</FONT>')
    if colour:
        s = f'<FONT COLOR="{colour}">{s}</FONT>'
    if size:
        s = f'<FONT POINT-SIZE="{size}">{s}</FONT>'
    return "<" + s + ">"


def header(name, extra=""):
    return (f'graph {name} {{\n  rankdir=BT; nodesep=0.35; ranksep=0.42; {extra}\n'
            f'  node [shape=plaintext, fontname="{FONT}", fontsize=13];\n'
            f'  edge [fontname="{FONT}", fontsize=11];\n')


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
        sys.exit("f0-figures: dot -Tplain failed:\n" + p.stderr)
    pos = {}
    for line in p.stdout.splitlines():
        f = line.split()
        if f and f[0] == "node":
            pos[int(f[1][1:])] = (float(f[2]) * 72, float(f[3]) * 72, float(f[4]) * 72)
    return pos


def box(name, x0, y0, x1, y1, colour, text, text_colour=None, size=11):
    """A region: a rectangle node at fixed position, its name at the lower left."""
    w, h = (x1 - x0) / 72, (y1 - y0) / 72
    s = (f'  {name} [shape=box, label="", fixedsize=true, width={w:.3f}, height={h:.3f}, '
         f'color="{colour}", pos="{(x0 + x1) / 2:.1f},{(y0 + y1) / 2:.1f}!"];\n')
    tw = 6.5 * len(text)
    s += (f'  {name}_l [label={lab(text, text_colour or colour, size)}, '
          f'pos="{x0 + 6 + tw / 2:.1f},{y0 + 10:.1f}!"];\n')
    return s


def selfsim(d):
    assert d["sigBotIsT3"] and d["sigT3IsC1OrG1"]
    pairs = d["rungs8"]
    pos = ladder_layout(pairs, 8)
    xs = [x for (x, _, _) in pos.values()]
    ys = [y for (_, y, _) in pos.values()]
    half = max(w for (_, _, w) in pos.values()) / 2
    x0, x1 = min(xs) - half - 10, max(xs) + half + 10
    y0, y1 = min(ys) - 34, max(ys) + 20
    gap = 56
    dx = (x1 - x0) + gap
    s = (f'graph selfsim {{\n  splines=line; outputorder=nodesfirst;\n'
         f'  node [shape=plaintext, fontname="{FONT}", fontsize=13];\n'
         f'  edge [fontname="{FONT}", fontsize=11];\n')
    # panel 1: the first ladder in F0 and its image under sigma in [t3, top]
    s += box("boxA", x0, y0, x1, y1, GREY, "F₀", size=13)
    s += box("boxB", x0 + dx, y0, x1 + dx, y1, BLUE, "σ(F₀) ⊆ [t₃, ⊤]", size=13)
    for k, (x, y, _) in pos.items():
        s += f'  a{k} [label={lab(t(k))}, pos="{x:.1f},{y:.1f}!"];\n'
        s += f'  b{k} [label={lab(sigma_label(k), BLUE)}, pos="{x + dx:.1f},{y:.1f}!"];\n'
    for i, j in pairs:
        s += f'  a{i} -- a{j};\n'
        s += f'  b{i} -- b{j} [color="{BLUE}"];\n'
    # sigma, drawn once, as the map from the first ladder to the second
    ym = (y0 + y1) / 2
    s += f'  p1 [shape=point, width=0.01, style=invis, pos="{x1 + 6:.1f},{ym:.1f}!"];\n'
    s += f'  p2 [shape=point, width=0.01, style=invis, pos="{x0 + dx - 6:.1f},{ym:.1f}!"];\n'
    s += (f'  p1 -- p2 [dir=forward, color="{BLUE}", penwidth=1.4, arrowsize=0.9];\n'
          f'  sigl [label={lab("σ", BLUE, 18)}, pos="{(x1 + x0 + dx) / 2:.1f},{ym + 14:.1f}!"];\n')
    # panel 2: the nested copies sigma^n(F0) and their bases
    cx = x1 + dx + 130
    step = 58
    bases = ["⊥", "t₃ = σ(⊥)", "σ²(⊥) = σ(t₃)", "σ³(⊥)"]
    regions = ["F₀", "σ(F₀)", "σ²(F₀)", "σ³(F₀)"]
    colours = [GREY, BLUE, GREEN, BROWN]
    by = [y0 + 30 + step * i for i in range(5)]
    top = by[4] + 26
    for i in range(4):
        w = 200 - 24 * i
        s += box(f"r{i}", cx - w / 2, by[i] - 22, cx + w / 2, top + 8 * (3 - i), colours[i], regions[i])
        s += f'  c{i} [label={lab(bases[i], colours[i])}, pos="{cx:.1f},{by[i]:.1f}!"];\n'
    s += f'  c4 [label="⋮", pos="{cx:.1f},{by[4]:.1f}!"];\n'
    for i in range(3):
        s += f'  c{i} -- c{i + 1};\n'
    # the theorems behind panel 2
    rows = [("σⁿ(F₀) is a faithful copy of F₀", "sigN_faithful"),
            ("σⁿ(F₀) ⊆ [σⁿ(⊥), ⊤]", "sigN_bot_le"),
            ("σⁿ(⊥) < σⁿ⁺¹(⊥)", "sigN_bot_strict"),
            ("σⁿ(⊥) ∉ σⁿ⁺¹(F₀)", "copies_strict")]
    cells = "".join(
        f'<TR><TD ALIGN="LEFT">{lab(a)[1:-1]}</TD><TD ALIGN="LEFT">'
        f'<FONT FACE="Menlo" POINT-SIZE="9">{b}</FONT></TD></TR>'
        for a, b in rows)
    s += (f'  legend [label=<<TABLE BORDER="0" CELLSPACING="0" CELLPADDING="2">{cells}</TABLE>>, '
          f'fontsize=11, pos="{cx:.1f},{top + 70:.1f}!"];\n')
    s += "}\n"
    names = ["PLLND.F0.Sig.sig", "PLLND.F0.Sig.sigN", "PLLND.F0.Sig.sig_t3",
             "PLLND.F0.Sig.sigN_faithful", "PLLND.F0.Sig.sigN_bot_le",
             "PLLND.F0.Sig.sigN_bot_strict", "PLLND.F0.Sig.copies_strict",
             "PLLND.RNEmbed.rungCovers", "PLLND.RNEmbed.rnSub_order"]
    return s, names, "neato"


def draw(name, src, engine):
    path = os.path.join(OUT, name + ".dot")
    with open(path, "w") as f:
        f.write(src)
    args = [engine] + (["-n2"] if engine == "neato" else [])
    for fmt, ext in (("svg:cairo", "svg"), ("pdf", "pdf")):
        p = subprocess.run(args + ["-T" + fmt, path, "-o", os.path.join(OUT, f"{name}.{ext}")],
                           capture_output=True, text=True, errors="replace")
        if p.returncode != 0:
            sys.exit(f"f0-figures: {engine} -T{fmt} failed on {name}:\n" + p.stderr)
    # the SVGs are inlined in one HTML page: cairo's ids (glyph-0-1, ...) would
    # collide between figures, so each figure's ids get its name as a prefix
    svg = os.path.join(OUT, name + ".svg")
    with open(svg) as f:
        s = f.read()
    s = re.sub(r'id="([^"]+)"', lambda m: f'id="{name}-{m.group(1)}"', s)
    s = re.sub(r'href="#([^"]+)"', lambda m: f'href="#{name}-{m.group(1)}"', s)
    s = re.sub(r'url\(#([^)]+)\)', lambda m: f'url(#{name}-{m.group(1)})', s)
    with open(svg, "w") as f:
        f.write(s)


def main():
    os.chdir(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
    d = lean_data()
    figs = {"bottom": bottom(d), "rungs": rungs(d), "selfsim": selfsim(d)}
    names = []
    for _, (_, ns, _) in figs.items():
        for n in ns:
            if n not in names:
                names.append(n)
    check_names(names)
    for name, (src, _, engine) in figs.items():
        draw(name, src, engine)
    print(f"  f0-figures: wrote {', '.join(figs)} to {OUT}/ (.svg, .pdf)")


if __name__ == "__main__":
    main()
