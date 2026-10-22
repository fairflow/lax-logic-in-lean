#!/usr/bin/env python3
"""Build the F0 explorer page from the certified explorer data.

    python3 scripts/f0explorer/build.py --data <f0-explorer-data.json> [--out docs/f0-explorer.html] [--check]

2026-10-22.  The data file is produced by `explorergen` (tools/F0/ExplorerGen.lean)
and is the only source of what the page states: names, Lean terms, family
definitions, weights, minimal forms, memberships, the order, the covers, the
operation tables, the named classes outside R and every status come from it.
This script reads it (never writes it), and does only two things:

* lays out the order diagram: layers by longest path over the data's `covers`;
  columns by family: ⊥, ⊤ and odd t on a spine, even t to its left (the RN
  ladder); c g s r w drawn between their family column to the right and the
  mean of their neighbours; unnamed classes at the mean of their neighbours;
* embeds the data, the layout and the page code (template.html, explorer.css,
  explorer.js beside this file) into one self-contained HTML file.

It computes no mathematics: it parses no formula, decides no relation, and
derives no fact.  The page (explorer.js) is under the same rule: it sorts,
filters, counts data rows and lays out.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parent.parent

# Layout constants (SVG user units).
ROW_H = 58          # vertical distance between layers
UNIT = 74           # horizontal distance between family columns
GAP = 10            # minimum horizontal gap between two nodes of one layer
MARGIN_X = 18
MARGIN_TOP = 34     # room for the frame label
MARGIN_BOTTOM = 18

# Family columns of the diagram (layout only).  None: placed by neighbours.
COLUMN = {"⊥": 0, "⊤": 0, "t_odd": 0, "t_even": -1, "c": 1, "g": 2, "s": 3, "r": 4, "w": 5}

NAME_RE = re.compile(r"^([a-z]+)\s*(\d+)$")


def fail(msg: str) -> None:
    print(f"build.py: {msg}", file=sys.stderr)
    sys.exit(1)


def column_of(name: str | None) -> int | None:
    """The diagram column of a class name (layout only)."""
    if name is None:
        return None
    if name in COLUMN:
        return COLUMN[name]
    m = NAME_RE.match(name)
    if not m:
        return None
    fam, idx = m.group(1), int(m.group(2))
    if fam == "t":
        return COLUMN["t_odd"] if idx % 2 == 1 else COLUMN["t_even"]
    return COLUMN.get(fam)


def pinned(name: str | None) -> bool:
    """⊥, ⊤ and the t rungs keep their column exactly (the ladder spine)."""
    if name is None:
        return False
    m = NAME_RE.match(name)
    return name in ("⊥", "⊤") or (m is not None and m.group(1) == "t")


def node_width(name: str | None) -> int:
    if name is None:
        return 58  # the muted label "unnamed"
    return max(30, 9 * len(name) + 16)


def layout(classes: list[dict], covers: list[list[int]]) -> dict:
    """Layered drawing of the cover graph.  Keys are positions in `classes`."""
    n = len(classes)
    pos_of_index = {c["index"]: k for k, c in enumerate(classes)}
    up: list[list[int]] = [[] for _ in range(n)]
    down: list[list[int]] = [[] for _ in range(n)]
    for pair in covers:
        a, b = pos_of_index[pair[0]], pos_of_index[pair[1]]
        up[a].append(b)
        down[b].append(a)

    # Longest-path layering (Kahn's order).
    indeg = [len(down[k]) for k in range(n)]
    queue = [k for k in range(n) if indeg[k] == 0]
    layer = [0] * n
    seen = 0
    while queue:
        a = queue.pop(0)
        seen += 1
        for b in up[a]:
            layer[b] = max(layer[b], layer[a] + 1)
            indeg[b] -= 1
            if indeg[b] == 0:
                queue.append(b)
    if seen != n:
        fail("the covers in the data contain a cycle; cannot lay out")

    names = [c.get("name") for c in classes]
    width = [node_width(nm) for nm in names]
    x = [0.0] * n
    top = max(layer) if n else 0
    layers = [[k for k in range(n) if layer[k] == L] for L in range(top + 1)]

    def place(L: int, use_up: bool) -> None:
        nodes = layers[L]
        if not nodes:
            return
        desired = {}
        for k in nodes:
            col = column_of(names[k])
            nbrs = down[k] + (up[k] if use_up else [])
            if col is not None and (pinned(names[k]) or not nbrs):
                desired[k] = col * UNIT
            elif col is not None:
                # other families: between their column and their neighbours
                desired[k] = 0.35 * col * UNIT + 0.65 * sum(x[m] for m in nbrs) / len(nbrs)
            elif nbrs:
                desired[k] = sum(x[m] for m in nbrs) / len(nbrs)
            else:
                desired[k] = 0.0
        order = sorted(nodes, key=lambda k: (desired[k], classes[k]["index"]))
        placed: list[float] = []
        for i, k in enumerate(order):
            if i == 0:
                placed.append(desired[k])
            else:
                prev = order[i - 1]
                lo = placed[-1] + (width[prev] + width[k]) / 2 + GAP
                placed.append(max(desired[k], lo))
        shift = sum(desired[k] for k in order) / len(order) - sum(placed) / len(placed)
        for k, px in zip(order, placed):
            x[k] = px + shift

    for L in range(top + 1):
        place(L, use_up=False)
    for L in range(top, -1, -1):
        place(L, use_up=True)
    for L in range(top + 1):
        place(L, use_up=True)

    min_x = min(x[k] - width[k] / 2 for k in range(n))
    max_x = max(x[k] + width[k] / 2 for k in range(n))
    W = (max_x - min_x) + 2 * MARGIN_X
    H = top * ROW_H + MARGIN_TOP + MARGIN_BOTTOM + 28
    nodes = []
    for k in range(n):
        nodes.append({
            "x": round(x[k] - min_x + MARGIN_X, 1),
            "y": round(MARGIN_TOP + 14 + (top - layer[k]) * ROW_H, 1),
            "w": width[k],
            "layer": layer[k],
        })
    return {"width": round(W, 1), "height": round(H, 1), "nodes": nodes}


def check_schema(d: dict) -> None:
    for key in ("generated", "commit", "meta", "classes", "order", "covers", "ops", "boundary", "family_defs"):
        if key not in d:
            fail(f"data has no `{key}`")
    idx = [c.get("index") for c in d["classes"]]
    if len(set(idx)) != len(idx) or None in idx:
        fail("class `index` values are missing or repeated")
    ids = {c.get("id") for c in d["classes"]}
    for c in d["ops"]:
        r = c.get("result")
        if r not in ("notR", "unknown") and r not in ids:
            fail(f"op cell result {r!r} is not a class id")


def script_json(obj) -> str:
    """JSON safe inside <script type="application/json">."""
    s = json.dumps(obj, ensure_ascii=False, separators=(",", ":"))
    return s.replace("</", "<\\/").replace("<!--", "<\\!--")


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--data", required=True, help="f0-explorer-data.json (read only)")
    ap.add_argument("--out", default=str(REPO / "docs" / "f0-explorer.html"))
    ap.add_argument("--check", action="store_true",
                    help="write nothing; exit 1 if --out differs from a fresh build")
    args = ap.parse_args()

    data_path = Path(args.data)
    d = json.loads(data_path.read_text(encoding="utf-8"))
    check_schema(d)

    lay = layout(d["classes"], d["covers"])

    template = (HERE / "template.html").read_text(encoding="utf-8")
    css = (HERE / "explorer.css").read_text(encoding="utf-8")
    js = (HERE / "explorer.js").read_text(encoding="utf-8")
    html = (template
            .replace("/*@CSS@*/", css)
            .replace("/*@JS@*/", js)
            .replace("@LAYOUT@", script_json(lay))
            .replace("@DATA@", script_json(d)))

    out = Path(args.out)
    if args.check:
        same = out.exists() and out.read_text(encoding="utf-8") == html
        print(f"{out}: {'up to date' if same else 'DIFFERS from a fresh build'} "
              f"(data generated {d['generated']}, commit {d['commit']})")
        sys.exit(0 if same else 1)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(html, encoding="utf-8")
    print(f"wrote {out} ({out.stat().st_size} bytes) from {data_path} "
          f"(generated {d['generated']}, commit {d['commit']}; "
          f"{len(d['classes'])} classes, {len(d['order'])} order cells, {len(d['covers'])} covers, "
          f"{len(d['ops'])} op cells, {len(d.get('outside_named') or [])} named outside R)")


if __name__ == "__main__":
    main()
