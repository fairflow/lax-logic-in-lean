#!/usr/bin/env python3
"""The figure of the semantics paper, "Semantics and decision for PLL", generated from
data that Lean computed.

    scripts/sem-figures.py           (run by scripts/sem-paper.sh before the paper)

1. `lake env lean tools/SemPaper/FigureData.lean` prints `SEMFIGURES <json>`:
   the countermodel inside the kernel-checked proof of `fact_24`
   (`⊬ ◯(p ∨ q) ↠ ◯p ∨ ◯q`, LaxLogic/PLL/SubTab/Facts.lean), its covering
   pairs, and the forcing of the atoms and `◯`-subformulas at each world,
   computed by `SubCM.forceB`.
2. Every name the figure cites is `#check`ed (docs/sem-paper-figures/check.lean).
3. Graphviz lays the figure out (`dot`); docs/sem-paper-figures/<name>.svg is
   inlined in the HTML, <name>.pdf included in the PDF at its natural size, so
   that the labels print at the body-text size.

The reading, checking and drawing are those of the F0 paper's figures
(scripts/paperfig.py).  Nothing is drawn that the data does not give.
Written 2026-10-24 for v0.1 of the semantics paper.
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import paperfig  # noqa: E402
from paperfig import SUB, BLUE, lab, header  # noqa: E402

OUT = "docs/sem-paper-figures"
TAG = "sem-figures"


def show(x, top=True):
    """A formula: binary connectives bracketed inside one another."""
    op = x["op"]
    if op == "bot":
        return "⊥"
    if op == "atom":
        return x["name"]
    a = x["args"]
    if op == "box":
        return "◯" + show(a[0], False)
    if op == "imp" and a[1]["op"] == "bot":
        return "¬" + show(a[0], False)
    sym = {"and": " ∧ ", "or": " ∨ ", "imp": " ↠ "}[op]
    s = show(a[0], False) + sym + show(a[1], False)
    return s if top else "(" + s + ")"


def w(i):
    return "w" + str(i).translate(SUB)


def countermodel(d):
    assert d["refutes"] and not d["rootForcesFormula"], "the model must refute the formula"
    shown = d["shown"]
    boxes = [k for k, f in enumerate(shown) if f["op"] == "box"]
    s = header("countermodel", "ranksep=0.5; nodesep=0.6;")
    for i, wd in enumerate(d["worlds"]):
        name = w(i) + (" ∈ S" if wd["S"] else "") + (" (root)" if i == d["root"] else "")
        atoms = ", ".join(wd["val"]) if wd["val"] else "no atom"
        yes = [show(shown[k]) for k in boxes if wd["forced"][k]]
        no = [show(shown[k]) for k in boxes if not wd["forced"][k]]
        lines = [lab(name, BLUE if wd["S"] else None)[1:-1], lab(atoms)[1:-1]]
        if yes:
            lines.append(lab("⊩ " + ", ".join(yes))[1:-1])
        if no:
            lines.append(lab("⊮ " + ", ".join(no))[1:-1])
        cells = "".join(f"<TR><TD>{t}</TD></TR>" for t in lines)
        border = ' COLOR="' + BLUE + '"' if wd["S"] else ""
        s += (f'  n{i} [label=<<TABLE BORDER="1" CELLBORDER="0" CELLSPACING="0" '
              f'CELLPADDING="1"{border}>{cells}</TABLE>>];\n')
    for i, j in d["covers"]:
        s += f'  n{i} -- n{j};\n'
    s += "}\n"
    names = [d["theorem"], "PLLND.SubTab.SubCM.forceB", "PLLND.SubTab.SubCM.refutes",
             "PLLND.SubTab.no"]
    return s, names, "dot"


def main():
    os.chdir(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
    d = paperfig.lean_data("tools/SemPaper/FigureData.lean", "SEMFIGURES", TAG)
    figs = {"countermodel": countermodel(d)}
    paperfig.run(figs, OUT, ["LaxLogic.PLL.SubTab.Facts"], TAG)


if __name__ == "__main__":
    main()
