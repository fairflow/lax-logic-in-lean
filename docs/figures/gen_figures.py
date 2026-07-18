#!/usr/bin/env python3
"""Generate SVG (and TikZ, for the small models) diagrams of the
constraint countermodels emitted by the Lean artefact.

Conventions: nodes layered by belief-set size (Hasse style, Ri
transitively reduced, reflexive edges omitted); an edge is drawn SOLID
if the pair is also in Rm (a constraint step) and DASHED if it is
Ri-only (an information step along which promises lapse); fallible
worlds are filled dark; the refuting world carries a ring; promises are
printed beneath the belief set. Prototype for a Lean-side
FinCM → TikZ/SVG exporter."""

import json, itertools, html

def preorder_le(worlds, key):
    n = len(worlds)
    le = [[False]*n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            le[i][j] = key(worlds[i]) <= key(worlds[j])
    return le

def hasse(le):
    n = len(le)
    edges = []
    for i in range(n):
        for j in range(n):
            if i != j and le[i][j] and not le[j][i]:
                if not any(k not in (i, j) and le[i][k] and le[k][j]
                           and not le[k][i] and not le[j][k] for k in range(n)):
                    edges.append((i, j))
    return edges

def svg_model(name, worlds, pos, fall, refut, width, height, node_r=26):
    """worlds: list of dicts {T:set,P:set,labelT:str,labelP:str}"""
    leT = preorder_le(worlds, lambda w: w["T"])
    ri_edges = hasse(leT)
    def rm_pair(i, j):
        return worlds[i]["T"] <= worlds[j]["T"] and worlds[i]["P"] <= worlds[j]["P"]
    out = []
    out.append(f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {width} {height}" font-family="Georgia, serif">')
    out.append('<defs>'
      '<marker id="arr" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse">'
      '<path d="M0 0 L10 5 L0 10 z" fill="#5b7c99"/></marker>'
      '<marker id="arrg" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse">'
      '<path d="M0 0 L10 5 L0 10 z" fill="#b0b0b0"/></marker></defs>')
    # edges
    for (i, j) in ri_edges:
        x1, y1 = pos[i]; x2, y2 = pos[j]
        # shrink toward node borders
        import math
        dx, dy = x2-x1, y2-y1; L = math.hypot(dx, dy)
        ux, uy = dx/L, dy/L
        x1s, y1s = x1+ux*node_r, y1+uy*node_r
        x2s, y2s = x2-ux*(node_r+6), y2-uy*(node_r+6)
        if rm_pair(i, j):
            out.append(f'<line x1="{x1s:.1f}" y1="{y1s:.1f}" x2="{x2s:.1f}" y2="{y2s:.1f}" stroke="#5b7c99" stroke-width="2" marker-end="url(#arr)"/>')
        else:
            out.append(f'<line x1="{x1s:.1f}" y1="{y1s:.1f}" x2="{x2s:.1f}" y2="{y2s:.1f}" stroke="#b0b0b0" stroke-width="1.6" stroke-dasharray="5 4" marker-end="url(#arrg)"/>')
    # mutual Ri pairs (equivalence links)
    n = len(worlds)
    for i in range(n):
        for j in range(i+1, n):
            if leT[i][j] and leT[j][i] and worlds[i] is not worlds[j]:
                x1, y1 = pos[i]; x2, y2 = pos[j]
                out.append(f'<line x1="{x1}" y1="{y1}" x2="{x2}" y2="{y2}" stroke="#d8c9a3" stroke-width="1.2"/>')
    # nodes
    for i, w in enumerate(worlds):
        x, y = pos[i]
        filled = i in fall
        ring = i == refut
        fill = "#3a3a3a" if filled else "#f7f4ec"
        stroke = "#3a3a3a"
        out.append(f'<circle cx="{x}" cy="{y}" r="{node_r}" fill="{fill}" stroke="{stroke}" stroke-width="1.5"/>')
        if ring:
            out.append(f'<circle cx="{x}" cy="{y}" r="{node_r+5}" fill="none" stroke="#c0392b" stroke-width="2.5"/>')
        tcol = "#f7f4ec" if filled else "#1a1a1a"
        out.append(f'<text x="{x}" y="{y+5}" text-anchor="middle" font-size="15" fill="{tcol}">w{i}</text>')
        lt = html.escape(w["labelT"]); lp = html.escape(w["labelP"])
        out.append(f'<text x="{x}" y="{y+node_r+16}" text-anchor="middle" font-size="11.5" fill="#333">{lt}</text>')
        if lp:
            out.append(f'<text x="{x}" y="{y+node_r+30}" text-anchor="middle" font-size="11" fill="#a03030">⊘ {lp}</text>')
        title = f'w{i}: believes {{{w["labelT"] or "∅"}}}' + (f', promises-false {{{w["labelP"]}}}' if lp else '') + (', fallible' if filled else '')
        out.append(f'<title>{html.escape(title)}</title>')
    out.append('</svg>')
    return "\n".join(out)

def W(T, P, lt, lp=""):
    return {"T": frozenset(T), "P": frozenset(P), "labelT": lt, "labelP": lp}

# ---- (a) the obstruction frame obsM ----
obs = [W([], [], "∅"),
       W(["p","t"], [], "p, t"),
       W(["q","t"], [], "q, t")]
obs_pos = {0: (210, 240), 1: (100, 90), 2: (320, 90)}
svg_obs = svg_model("obsM", obs, obs_pos, fall=set(), refut=None, width=420, height=320)

# ---- (b) demoM (◯p ⊬ p), 5 worlds ----
# w0: T=∅ P=∅ ; w1: T=∅ P={p,◯p}; w2: {◯p}; w3: {◯p,p}; w4 fallible full
demo = [W([], [], "∅"),
        W([], ["p","◯p"], "∅", "p, ◯p"),
        W(["◯p"], [], "◯p"),
        W(["◯p","p"], [], "◯p, p"),
        W(["⊥","◯p","p"], [], "⊥ (fallible)")]
demo_pos = {0: (140, 380), 1: (330, 380), 2: (235, 255), 3: (235, 130), 4: (235, 20)}
svg_demo = svg_model("demoM", demo, demo_pos, fall={4}, refut=2, width=470, height=470)

# ---- (c) the ∨-distribution model, 20 worlds ----
raw = [
 ([], []), ([], ["◯p","p"]), ([], ["◯q","q"]),
 ([], ["◯p∨◯q","◯p","◯q","◯(p∨q)","p∨q","p","q"]),
 (["◯(p∨q)"], []), (["◯(p∨q)"], ["◯p","p"]), (["◯(p∨q)"], ["◯q","q"]),
 (["◯p∨◯q","◯p","◯(p∨q)"], []), (["◯p∨◯q","◯p","◯(p∨q)"], ["◯q","q"]),
 (["◯p∨◯q","◯q","◯(p∨q)"], []), (["◯p∨◯q","◯q","◯(p∨q)"], ["◯p","p"]),
 (["◯p∨◯q","◯p","◯q","◯(p∨q)"], []),
 (["◯p∨◯q","◯p","◯(p∨q)","p∨q","p"], []),
 (["◯p∨◯q","◯p","◯(p∨q)","p∨q","p"], ["◯q","q"]),
 (["◯p∨◯q","◯p","◯q","◯(p∨q)","p∨q","p"], []),
 (["◯p∨◯q","◯q","◯(p∨q)","p∨q","q"], []),
 (["◯p∨◯q","◯q","◯(p∨q)","p∨q","q"], ["◯p","p"]),
 (["◯p∨◯q","◯p","◯q","◯(p∨q)","p∨q","q"], []),
 (["◯p∨◯q","◯p","◯q","◯(p∨q)","p∨q","p","q"], []),
 (["⊥","◯p∨◯q","◯p","◯q","◯(p∨q)","p∨q","p","q"], []),
]
def short(T):
    # characteristic label: the most informative members
    if "⊥" in T: return "⊥ (fallible)"
    keys = [k for k in ["p","q","◯p","◯q","◯(p∨q)"] if k in T]
    return ", ".join(keys) if keys else "∅"
ordist = [W(T, P, short(set(T)), ", ".join(P) if P else "") for (T, P) in raw]
ordist_pos = {
  0:(430,900), 1:(240,900), 2:(620,900), 3:(430,980),
  4:(430,760), 5:(250,760), 6:(610,760),
  7:(260,610), 8:(120,610), 9:(600,610), 10:(740,610),
  11:(430,540),
  12:(240,420), 13:(100,420), 15:(620,420), 16:(760,420),
  14:(310,290), 17:(550,290),
  18:(430,170), 19:(430,50),
}
svg_ordist = svg_model("ordist", ordist, ordist_pos, fall={19}, refut=4, width=880, height=1040)

for nm, s in [("obsM", svg_obs), ("demoM", svg_demo), ("ordist20", svg_ordist)]:
    with open(f"docs/figures/{nm}.svg", "w") as f:
        f.write(s)
    print(nm, "written,", s.count("<line"), "edges")

# ---- TikZ for the two small models (paper figures) ----
def tikz_model(worlds, pos, fall, refut, scale=0.02):
    leT = preorder_le(worlds, lambda w: w["T"])
    edges = hasse(leT)
    def rm_pair(i,j):
        return worlds[i]["T"] <= worlds[j]["T"] and worlds[i]["P"] <= worlds[j]["P"]
    L = ["\\begin{tikzpicture}[every node/.style={circle,draw,minimum size=9mm,inner sep=1pt}]"]
    ymax = max(y for (_,y) in pos.values())
    for i,w in enumerate(worlds):
        x,y = pos[i]
        opts = []
        if i in fall: opts.append("fill=black,text=white")
        if i == refut: opts.append("double,double distance=1.5pt,draw=red!70!black")
        lp = f", label=below:{{\\scriptsize $\\oslash\\,{w['labelP']}$}}" if w["labelP"] else ""
        lt = f", label=above:{{\\scriptsize ${w['labelT']}$}}" if w["labelT"] and i not in fall else ""
        L.append(f"  \\node[{','.join(opts)}] (w{i}) at ({x*scale:.2f},{(ymax-y)*scale:.2f}) {{$w_{{{i}}}$}};".replace("[]","").replace("{,","{"))
    for (i,j) in edges:
        style = "-{Stealth}" if rm_pair(i,j) else "-{Stealth},dashed,gray"
        L.append(f"  \\draw[{style}] (w{i}) -- (w{j});")
    L.append("\\end{tikzpicture}")
    return "\n".join(L)

with open("docs/figures/obsM.tikz","w") as f: f.write(tikz_model(obs, obs_pos, set(), None))
with open("docs/figures/demoM.tikz","w") as f: f.write(tikz_model(demo, demo_pos, {4}, 2))
print("tikz written")
