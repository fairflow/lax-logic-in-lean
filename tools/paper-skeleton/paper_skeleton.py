#!/usr/bin/env python3
"""
paper-skeleton — turn a paper's LaTeX source into a fidelity-table skeleton.

Stage 1 of a calculus-adoption campaign is "list the numbered results to
be reproduced, in the paper's own numbering".  Doing that by hand from a
PDF is slow and lossy; doing it from the arXiv LaTeX source is neither,
and the source is what the campaign should be reading anyway.

    paper_skeleton.py --arxiv 1804.06689 -o skeleton.md
    paper_skeleton.py --src path/to/main.tex -o skeleton.md
    paper_skeleton.py --src main.tex --json items.json

What it does
    * resolves \\input / \\include, strips comments
    * finds theorem-like environments, including those a document class
      predefines rather than declaring with \\newtheorem
    * SIMULATES THE COUNTERS, so items come out as "Lemma 3.4" rather
      than "the 17th lemma" -- see --numbering
    * flags \\appendix, because proof detail hides there and reading it
      is a standing rule of this workflow
    * emits a Markdown fidelity table, the full statements, and an empty
      divergence log

Numbering is INFERRED and printed in the header.  Spot-check two items
against the PDF before trusting a whole table; override with
--numbering if the class does something unusual.
"""

import argparse, io, json, os, re, sys, tarfile, gzip, shutil, tempfile
import urllib.request

# --- theorem environments predefined by common document classes -------------
# (shared: all theorem-like envs share one counter; within: reset per section)
CLASS_DEFAULTS = {
    "llncs":       dict(shared=True,  within="section"),
    "acmart":      dict(shared=True,  within="section"),
    "acmsmall":    dict(shared=True,  within="section"),
    "lipics":      dict(shared=True,  within="section"),
    "elsarticle":  dict(shared=True,  within="section"),
    "article":     dict(shared=False, within="section"),
    "amsart":      dict(shared=False, within="section"),
}
DEFAULT_KINDS = ["theorem", "lemma", "corollary", "proposition", "definition",
                 "example", "remark", "claim", "fact", "observation", "conjecture",
                 "notation", "convention", "problem", "assumption"]

def strip_comments(tex: str) -> str:
    out = []
    for line in tex.split("\n"):
        i, esc = 0, False
        cut = None
        while i < len(line):
            c = line[i]
            if esc:
                esc = False
            elif c == "\\":
                esc = True
            elif c == "%":
                cut = i
                break
            i += 1
        out.append(line if cut is None else line[:cut])
    return "\n".join(out)

def resolve_inputs(path: str, seen=None) -> str:
    """Inline \\input and \\include, depth-first."""
    seen = seen or set()
    path = os.path.abspath(path)
    if path in seen or not os.path.exists(path):
        return ""
    seen.add(path)
    base = os.path.dirname(path)
    tex = strip_comments(io.open(path, encoding="utf-8", errors="replace").read())
    def sub(m):
        name = m.group(2).strip()
        for cand in (name, name + ".tex"):
            p = os.path.join(base, cand)
            if os.path.exists(p):
                return "\n" + resolve_inputs(p, seen) + "\n"
        return ""
    return re.sub(r"\\(input|include)\s*\{([^}]*)\}", sub, tex)

def find_main(root: str) -> str:
    """The .tex file carrying \\documentclass; fall back to the largest."""
    cands = []
    for dirpath, _, files in os.walk(root):
        for f in files:
            if f.endswith(".tex"):
                p = os.path.join(dirpath, f)
                try:
                    head = io.open(p, encoding="utf-8", errors="replace").read()
                except OSError:
                    continue
                if re.search(r"^\s*\\documentclass", strip_comments(head), re.M):
                    cands.append((os.path.getsize(p), p))
    if cands:
        return max(cands)[1]
    allt = [(os.path.getsize(os.path.join(d, f)), os.path.join(d, f))
            for d, _, fs in os.walk(root) for f in fs if f.endswith(".tex")]
    if not allt:
        sys.exit("no .tex found")
    return max(allt)[1]

def fetch_arxiv(arxiv_id: str, dest: str) -> str:
    url = f"https://arxiv.org/e-print/{arxiv_id}"
    req = urllib.request.Request(url, headers={"User-Agent": "paper-skeleton/1.0"})
    with urllib.request.urlopen(req, timeout=60) as r:
        blob = r.read()
    os.makedirs(dest, exist_ok=True)
    try:
        with tarfile.open(fileobj=io.BytesIO(blob)) as tf:
            tf.extractall(dest)
        return dest
    except tarfile.TarError:
        pass
    out = os.path.join(dest, "main.tex")
    try:
        data = gzip.decompress(blob)
    except OSError:
        data = blob
    io.open(out, "wb").write(data)
    return dest

def theorem_config(tex: str, override: str | None):
    """Which environments are theorem-like, and how are they numbered?"""
    kinds, notes = {}, []
    # explicit declarations win
    for m in re.finditer(
            r"\\(?:sp)?newtheorem\*?\s*\{(\w+)\}\s*(?:\[(\w+)\])?\s*\{([^}]*)\}"
            r"\s*(?:\[(\w+)\])?", tex):
        env, shares, display, within = m.groups()
        kinds[env] = dict(display=display.strip(), shares=shares, within=within)
    if kinds:
        notes.append(f"from {len(kinds)} \\newtheorem declaration(s) in the source")
        return kinds, notes, False
    cls = None
    m = re.search(r"\\documentclass\s*(?:\[[^\]]*\])?\s*\{([^}]*)\}", tex)
    if m:
        cls = m.group(1).strip()
    cfg = CLASS_DEFAULTS.get(cls, dict(shared=True, within="section"))
    if override:
        cfg = dict(shared=(override.split(",")[0] == "shared"),
                   within=(override.split(",")[1] if "," in override else "section"))
        notes.append(f"numbering forced by --numbering {override}")
    else:
        notes.append(f"no \\newtheorem in source; inferred from "
                     f"\\documentclass{{{cls}}}"
                     + ("" if cls in CLASS_DEFAULTS else " (class unknown, guessed)"))
    for k in DEFAULT_KINDS:
        kinds[k] = dict(display=k.capitalize(),
                        shares=("__shared__" if cfg["shared"] else None),
                        within=cfg["within"])
    return kinds, notes, (cls not in CLASS_DEFAULTS)

def balanced(tex: str, i: int, op="{", cl="}"):
    """Content of the group starting at tex[i]==op; returns (content, end)."""
    if i >= len(tex) or tex[i] != op:
        return None, i
    depth, j = 0, i
    while j < len(tex):
        if tex[j] == op and (j == 0 or tex[j-1] != "\\"):
            depth += 1
        elif tex[j] == cl and tex[j-1] != "\\":
            depth -= 1
            if depth == 0:
                return tex[i+1:j], j + 1
        j += 1
    return None, i

def clean(s: str, limit=None) -> str:
    s = re.sub(r"\\label\s*\{[^}]*\}", "", s)
    s = re.sub(r"\s+", " ", s).strip()
    if limit and len(s) > limit:
        s = s[:limit].rstrip() + " …"
    return s

def extract(tex: str, kinds: dict):
    """Walk the document, numbering sections and theorem-like environments."""
    items, sec, sub, in_appendix = [], 0, 0, False
    counters = {}
    def bump(env):
        cfg = kinds[env]
        key = cfg.get("shares") or ("__shared__" if cfg.get("shares") == "__shared__" else env)
        if cfg.get("shares") == "__shared__":
            key = "__shared__"
        elif cfg.get("shares"):
            key = cfg["shares"]
        else:
            key = env
        scope = (sec if cfg.get("within") else None)
        counters.setdefault((key, scope), 0)
        counters[(key, scope)] += 1
        n = counters[(key, scope)]
        if cfg.get("within"):
            label = f"{chr(64+sec) if in_appendix else sec}.{n}"
        else:
            label = str(n)
        return label
    env_names = "|".join(sorted(kinds, key=len, reverse=True))
    pat = re.compile(
        r"\\(appendix)\b|\\(section|subsection)(\*?)\s*\{|"
        rf"\\begin\{{({env_names})\}}")
    pos = 0
    while True:
        m = pat.search(tex, pos)
        if not m:
            break
        if m.group(1):
            in_appendix, sec, pos = True, 0, m.end()
            counters.clear()
            continue
        if m.group(2):
            starred = m.group(3) == "*"
            title, end = balanced(tex, m.end() - 1)
            if m.group(2) == "section" and not starred:
                sec, sub = sec + 1, 0
                counters.clear()
                items.append(dict(kind="§", number=(chr(64+sec) if in_appendix else str(sec)),
                                  title=clean(title or ""), label=None, body="",
                                  appendix=in_appendix))
            pos = end
            continue
        env = m.group(4)
        i = m.end()
        title = ""
        if i < len(tex) and tex[i] == "[":
            t, i = balanced(tex, i, "[", "]")
            title = clean(t or "")
        depth, j = 1, i
        endpat = re.compile(rf"\\(begin|end)\{{{env}\}}")
        body_end = len(tex)
        for mm in endpat.finditer(tex, i):
            depth += 1 if mm.group(1) == "begin" else -1
            if depth == 0:
                body_end = mm.start()
                break
        body = tex[i:body_end]
        lab = re.search(r"\\label\s*\{([^}]*)\}", body)
        items.append(dict(kind=kinds[env]["display"], number=bump(env), title=title,
                          label=lab.group(1) if lab else None,
                          body=clean(body), appendix=in_appendix))
        pos = body_end
    return items

def emit_markdown(items, notes, src, uncertain):
    res = [i for i in items if i["kind"] != "§"]
    app = [i for i in res if i["appendix"]]
    L = []
    L.append("# Fidelity skeleton\n")
    L.append(f"*Generated by `paper-skeleton` from `{src}`. "
             f"{len(res)} numbered items across "
             f"{len([i for i in items if i['kind']=='§'])} sections"
             + (f", {len(app)} of them in an appendix" if app else "") + ".*\n")
    L.append("**Numbering** — " + "; ".join(notes) + ".")
    L.append("\n> **Numbers are INFERRED; labels are exact.** A LaTeX source never "
             "contains the printed numbers — every one is a `\\ref`, computed at "
             "compile time — so this tool simulates the counters instead. The "
             "`\\label` under each name *is* in the source and is reliable, so key "
             "your fidelity table on labels and treat numbers as a convenience.\n"
             ">\n"
             "> Check the model on two items against the PDF. A good check: pick a "
             "result the paper's own prose cites, and one item late in a long "
             "section — an off-by-one from an unnumbered or uncounted environment "
             "shows up there and nowhere else.\n")
    if uncertain:
        L.append("> ⚠ The document class was not recognised, so the model is a "
                 "guess. Re-run with `--numbering shared,section` or "
                 "`--numbering perkind,section` if it is wrong.\n")
    if app:
        L.append(f"**There is an appendix, carrying {len(app)} numbered items.** "
                 "Read it before scoping any proof: page limits push load-bearing "
                 "detail there.\n")
    L.append("## Results to be reproduced\n")
    L.append("| Paper item | Statement | Lean name | Status |")
    L.append("|---|---|---|---|")
    cur = None
    for it in items:
        if it["kind"] == "§":
            L.append(f"| **§{it['number']} {it['title']}** | | | |")
            continue
        name = f"{it['kind']} {it['number']}"
        if it["title"]:
            name += f" ({it['title']})"
        if it["label"]:
            name += f"<br/>`{it['label']}`"
        L.append(f"| {name} | {it['body'][:160].replace('|','\\|')}"
                 f"{' …' if len(it['body'])>160 else ''} | | OPEN |")
    L.append("\nStatus is one of **PROVED** (sorry-free with a pinned "
             "`#print axioms`), **REFUTED** (kernel-checked countermodel), "
             "**OPEN**, or *out of scope* — kept rigidly distinct.\n")
    L.append("## Divergence log\n")
    L.append("*A divergence is recorded when it is made, not afterwards. "
             "Number them; cite the paper item; say what the paper states, "
             "what is proved here instead, and why.*\n")
    L.append("| # | Paper item | What the paper says | What is proved here | Why |")
    L.append("|---|---|---|---|---|\n")
    L.append("## Full statements\n")
    for it in res:
        head = f"### {it['kind']} {it['number']}"
        if it["title"]:
            head += f" ({it['title']})"
        L.append(head)
        if it["label"]:
            L.append(f"`\\label{{{it['label']}}}`" +
                     ("  ·  **appendix**" if it["appendix"] else ""))
        L.append("\n```tex\n" + it["body"][:1500] +
                 ("\n… (truncated)" if len(it["body"]) > 1500 else "") + "\n```\n")
    return "\n".join(L)

def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--arxiv", help="arXiv id, e.g. 1804.06689")
    g.add_argument("--src", help="path to the main .tex")
    g.add_argument("--dir", help="directory of an already-extracted source")
    ap.add_argument("-o", "--out", help="write Markdown here (default: stdout)")
    ap.add_argument("--json", help="also write the items as JSON")
    ap.add_argument("--numbering", help="shared,section | perkind,section | shared,none")
    ap.add_argument("--keep", help="where to keep a downloaded source")
    a = ap.parse_args()

    if a.arxiv:
        dest = a.keep or tempfile.mkdtemp(prefix="arxiv-")
        fetch_arxiv(a.arxiv, dest)
        main_tex = find_main(dest)
        src = f"arXiv:{a.arxiv} ({os.path.basename(main_tex)})"
    elif a.dir:
        main_tex = find_main(a.dir)
        src = main_tex
    else:
        main_tex = a.src
        src = main_tex

    tex = resolve_inputs(main_tex)
    kinds, notes, uncertain = theorem_config(tex, a.numbering)
    items = extract(tex, kinds)
    md = emit_markdown(items, notes, src, uncertain)
    if a.out:
        io.open(a.out, "w", encoding="utf-8").write(md)
        res = [i for i in items if i["kind"] != "§"]
        print(f"{len(res)} numbered items -> {a.out}")
    else:
        print(md)
    if a.json:
        io.open(a.json, "w", encoding="utf-8").write(json.dumps(items, indent=2))

if __name__ == "__main__":
    main()
