"""The figure pipeline shared by the Verso papers on this development
(scripts/f0-figures.py, scripts/sem-figures.py): read the data a Lean emitter
prints, `#check` every name a figure cites, and lay the figures out with
Graphviz at the size they print.  Factored out of scripts/f0-figures.py on
2026-10-24 without changing the F0 paper's figures.

The PDF includes each figure at its natural size, so a label prints at FS
points, the size of the body text.  A figure wider than the text block (MAXW)
stops the script: content is reduced, never the type.
"""
import json
import os
import re
import subprocess
import sys

FONT = "STIX Two Math"
FS = 10          # label size in points, as printed (the body text is 10 pt)
CIRC = 7         # the modality's circle, set smaller to sit at letter height
MAXW = 455       # the text block: A4 less 2 x 24 mm is 459 pt
SUB = str.maketrans("0123456789", "₀₁₂₃₄₅₆₇₈₉")
GREY, BLUE, GREEN, BROWN = "#888888", "#3060a0", "#2a8a5a", "#a05a20"


def lean_data(emitter, marker, tag):
    """Run the Lean emitter and parse its `<marker> <json>` line."""
    p = subprocess.run(["lake", "env", "lean", emitter], capture_output=True, text=True)
    if p.returncode != 0:
        sys.exit(f"{tag}: the data emitter failed:\n" + p.stdout + p.stderr)
    for line in p.stdout.splitlines():
        if line.startswith(marker + " "):
            return json.loads(line[len(marker) + 1:])
    sys.exit(f"{tag}: no {marker} line in the emitter's output")


def check_names(names, out, imports, tag):
    """#check every cited declaration in the compiled library."""
    os.makedirs(out, exist_ok=True)
    path = os.path.join(out, "check.lean")
    with open(path, "w") as f:
        f.write("".join(f"import {m}\n" for m in imports) + "\n")
        for n in names:
            f.write("#check @" + n + "\n")
    p = subprocess.run(["lake", "env", "lean", path], capture_output=True, text=True)
    res = p.stdout + p.stderr
    if p.returncode != 0 or "error" in res:
        sys.exit(f"{tag}: a cited name does not resolve:\n" + res)
    print(f"  {tag}: {len(names)} cited names resolve")


def lab(text, colour=None, size=None):
    """A graphviz HTML-like label: the circle of the modality (U+25EF, a large
    circle in STIX) set smaller, so that it sits at letter height."""
    s = text.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")
    s = s.replace("◯", f'<FONT POINT-SIZE="{CIRC}">◯</FONT>')
    if colour:
        s = f'<FONT COLOR="{colour}">{s}</FONT>'
    if size:
        s = f'<FONT POINT-SIZE="{size}">{s}</FONT>'
    return "<" + s + ">"


def header(name, extra=""):
    return (f'graph {name} {{\n  rankdir=BT; nodesep=0.3; ranksep=0.32; margin=0; pad=0.06; {extra}\n'
            f'  node [shape=plaintext, fontname="{FONT}", fontsize={FS}, margin="0.04,0.03", width=0.1, height=0.1];\n'
            f'  edge [fontname="{FONT}", fontsize={FS}];\n')


def text_width(text, size=FS):
    """A label's width in points, estimated (STIX averages about 0.55 em)."""
    return 0.55 * size * len(text)


def box(name, x0, y0, x1, y1, colour, text, text_colour=None, size=FS):
    """A region: a rectangle node at fixed position, its name at the lower left."""
    w, h = (x1 - x0) / 72, (y1 - y0) / 72
    s = (f'  {name} [shape=box, label="", fixedsize=true, width={w:.3f}, height={h:.3f}, '
         f'color="{colour}", pos="{(x0 + x1) / 2:.1f},{(y0 + y1) / 2:.1f}!"];\n')
    tw = text_width(text, size)
    s += (f'  {name}_l [label={lab(text, text_colour or colour, size)}, '
          f'pos="{x0 + 5 + tw / 2:.1f},{y0 + size:.1f}!"];\n')
    return s


def draw(name, src, engine, out, tag):
    path = os.path.join(out, name + ".dot")
    with open(path, "w") as f:
        f.write(src)
    args = [engine] + (["-n2"] if engine == "neato" else [])
    for fmt, ext in (("svg:cairo", "svg"), ("pdf", "pdf")):
        p = subprocess.run(args + ["-T" + fmt, path, "-o", os.path.join(out, f"{name}.{ext}")],
                           capture_output=True, text=True, errors="replace")
        if p.returncode != 0:
            sys.exit(f"{tag}: {engine} -T{fmt} failed on {name}:\n" + p.stderr)
    # the SVGs are inlined in one HTML page: cairo's ids (glyph-0-1, ...) would
    # collide between figures, so each figure's ids get its name as a prefix
    svg = os.path.join(out, name + ".svg")
    with open(svg) as f:
        s = f.read()
    # the PDF is printed at its natural size: one wider than the text block is
    # an error (graphviz's default PDF margin of 36 pt is set to 0 above)
    p = subprocess.run(["pdfinfo", os.path.join(out, name + ".pdf")],
                       capture_output=True, text=True, errors="replace")
    m = re.search(r'Page size:\s*([0-9.]+) x ([0-9.]+) pts', p.stdout)
    if not m:
        sys.exit(f"{tag}: pdfinfo gives no page size for {name}.pdf\n" + p.stdout + p.stderr)
    w, h = float(m.group(1)), float(m.group(2))
    if w > MAXW:
        sys.exit(f"{tag}: {name} is {w:.0f} pt wide, more than the text block "
                 f"({MAXW} pt); reduce its content")
    print(f"  {tag}: {name}: {w:.0f} x {h:.0f} pt, labels at {FS} pt")
    s = re.sub(r'id="([^"]+)"', lambda m: f'id="{name}-{m.group(1)}"', s)
    s = re.sub(r'href="#([^"]+)"', lambda m: f'href="#{name}-{m.group(1)}"', s)
    s = re.sub(r'url\(#([^)]+)\)', lambda m: f'url(#{name}-{m.group(1)})', s)
    with open(svg, "w") as f:
        f.write(s)


def run(figs, out, imports, tag):
    """Check every cited name, then draw each figure: `figs` maps a name to
    (dot source, cited names, engine)."""
    names = []
    for _, (_, ns, _) in figs.items():
        for n in ns:
            if n not in names:
                names.append(n)
    check_names(names, out, imports, tag)
    for name, (src, _, engine) in figs.items():
        draw(name, src, engine, out, tag)
    print(f"  {tag}: wrote {', '.join(figs)} to {out}/ (.svg, .pdf)")
