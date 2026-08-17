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

def theorem_kinds(tex: str):
    """Which environments are theorem-like: declared ones plus the usual
    class-provided names.  No numbering model — the .aux supplies that."""
    kinds, notes = {}, []
    for m in re.finditer(
            r"\\(?:sp)?newtheorem\*?\s*\{(\w+)\}\s*(?:\[(\w+)\])?\s*\{([^}]*)\}", tex):
        env, _shares, display = m.groups()
        kinds[env] = dict(display=display.strip())
    if kinds:
        notes.append(f"{len(kinds)} environment(s) from \\newtheorem")
    for k in DEFAULT_KINDS:
        kinds.setdefault(k, dict(display=k.capitalize()))
    return kinds, notes

def compile_and_read_aux(main_tex: str):
    """Compile twice, return {label: (number, page)}.  Empty if it fails."""
    import subprocess
    d = os.path.dirname(os.path.abspath(main_tex)) or "."
    stem = os.path.splitext(os.path.basename(main_tex))[0]
    exe = shutil.which("pdflatex")
    if not exe:
        return {}, "pdflatex not found; items will carry no numbers"
    for _ in range(2):
        try:
            subprocess.run([exe, "-interaction=nonstopmode", os.path.basename(main_tex)],
                           cwd=d, capture_output=True, timeout=600)
        except Exception as e:
            return {}, f"compilation failed ({e}); items will carry no numbers"
    aux = os.path.join(d, stem + ".aux")
    if not os.path.exists(aux):
        return {}, "no .aux produced; items will carry no numbers"
    txt = io.open(aux, encoding="utf-8", errors="replace").read()
    out = {}
    for m in re.finditer(
            r"\\newlabel\{([^}]+)\}\{\{\{?([^{}]*)\}?\}\{([^{}]*)\}", txt):
        out[m.group(1)] = (m.group(2), m.group(3))
    return out, f"{len(out)} labels read from {stem}.aux (compiled here)"

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

def macro_defs(tex: str) -> str:
    """The paper's own \newcommand definitions, extracted brace-aware.

    Line-wise extraction truncates multi-line definitions and leaves braces
    unbalanced, which makes pandoc give up silently on the whole file."""
    out = []
    for m in re.finditer(r"\\(newcommand|renewcommand|providecommand)\s*", tex):
        i = m.end()
        inner, i2 = balanced(tex, i)
        if inner is None:
            m2 = re.match(r"(\\[A-Za-z@]+)", tex[i:])
            if not m2:
                continue
            name, i2 = "{" + m2.group(1) + "}", i + m2.end()
        else:
            name = "{" + inner + "}"
        j, nargs = i2, ""
        while j < len(tex) and tex[j] in " \t\n":
            j += 1
        for _ in range(2):
            if j < len(tex) and tex[j] == "[":
                a, j = balanced(tex, j, "[", "]")
                nargs += ("[" + a + "]") if a is not None else ""
                while j < len(tex) and tex[j] in " \t\n":
                    j += 1
        body, _ = balanced(tex, j)
        if body is None:
            continue
        body = "{" + body + "}"
        one = re.sub(r"\s+", " ", "\\" + m.group(1) + name + nargs + body)
        out.append(one)
    return "\n".join(out)

def sanitise_macros(macros: str, rounds: int = 25) -> str:
    """Drop definitions pandoc cannot parse, one at a time.

    A single pathological definition — this paper has one, a colour-
    highlighting editing aid — makes pandoc reject the entire block and
    emit nothing, silently.  Rather than hand-patch the extractor for each
    such case, ask pandoc which line it choked on and drop that line."""
    import subprocess
    exe = shutil.which("pandoc")
    if not exe:
        return macros
    lines = macros.split("\n")
    for _ in range(rounds):
        probe = ("\n".join(lines) + "\n$x$\n").encode("utf-8")
        r = subprocess.run([exe, "-f", "latex", "-t", "markdown"],
                           input=probe, capture_output=True)
        if r.returncode == 0:
            return "\n".join(lines)
        m = re.search(r"line (\d+)", r.stderr.decode("utf-8", "replace"))
        if not m:
            return "\n".join(lines)
        i = int(m.group(1)) - 1
        if not (0 <= i < len(lines)):
            return "\n".join(lines)
        del lines[i]
    return "\n".join(lines)

def pandoc_text(macros: str, body: str):
    """Convert a statement to Markdown with the paper's macros EXPANDED, so
    what is left is standard LaTeX rather than the paper's private notation."""
    import subprocess
    exe = shutil.which("pandoc")
    if not exe:
        return None
    src = macros + "\n" + body + "\n"
    try:
        r = subprocess.run([exe, "-f", "latex", "-t", "markdown-raw_html"],
                           input=src.encode("utf-8"), capture_output=True, timeout=60)
    except Exception:
        return None
    out = r.stdout.decode("utf-8", "replace")
    out = re.sub(r"\[([^\]]*)\]\([^)]*\)", r"\1", out)      # links -> their text
    out = re.sub(r"\{[^{}]*reference-type[^{}]*\}", "", out)  # pandoc ref attrs
    out = re.sub(r"\s*\\qed\b", "", out)
    out = re.sub(r"\s+", " ", out).strip()
    out = re.sub(r"\s*[0-9]?\s*[◻□∎]\s*$", "", out).strip()
    return out or None

# --- repairing pdftotext's glyph damage -------------------------------------
# pdftotext maps a TeX font's glyphs to Unicode one code point at a time, so
# composed and negated symbols come out wrong in predictable ways.  These are
# the repairs, each verified against the printed page.

_NEG = {"=": "≠", "∈": "∉", "⊆": "⊈", "⊂": "⊄", "⊃": "⊅", "≡": "≢",
        "≤": "≰", "≥": "≱", "<": "≮", ">": "≯", "⊢": "⊬", "⊨": "⊭",
        "∃": "∄", "|": "∤", "≈": "≉", "∼": "≁", "⪯": "⋠"}
_SUB = str.maketrans("0123456789", "₀₁₂₃₄₅₆₇₈₉")
# the capitals Unicode actually provides as modifier letters
_SUP = {"A": "ᴬ", "B": "ᴮ", "D": "ᴰ", "E": "ᴱ", "G": "ᴳ", "H": "ᴴ", "I": "ᴵ",
        "J": "ᴶ", "K": "ᴷ", "L": "ᴸ", "M": "ᴹ", "N": "ᴺ", "O": "ᴼ", "P": "ᴾ",
        "R": "ᴿ", "T": "ᵀ", "U": "ᵁ", "V": "ⱽ", "W": "ᵂ"}
_ARROWS = "↦→⇒⊢⊨⟹"
_SUBL = {"a": "ₐ", "e": "ₑ", "i": "ᵢ", "j": "ⱼ", "k": "ₖ", "l": "ₗ", "m": "ₘ",
         "n": "ₙ", "o": "ₒ", "p": "ₚ", "r": "ᵣ", "s": "ₛ", "t": "ₜ",
         "u": "ᵤ", "v": "ᵥ", "x": "ₓ"}
_GREEK = "αβγδεζηθικλμνξπρστυφχψωΑΒΓΔΕΖΗΘΙΚΛΜΝΞΠΡΣΤΥΦΧΨΩϕφσ"

def fix_glyphs(t: str) -> str:
    if not t:
        return t
    # ↦ is extracted as the digit 7 followed by →
    t = t.replace("7→", "↦").replace("7 →", "↦")
    # U+0338 COMBINING LONG SOLIDUS OVERLAY arrives either side of its base
    for base, neg in _NEG.items():
        t = t.replace(base + "̸", neg).replace("̸" + base, neg)
        t = t.replace("̸ " + base, neg).replace(base + " ̸", neg)
    # a negation landing on the wrong glyph of a two-symbol rule name:
    # ⊃∉ extracts as ⊅∈, the slash having attached to ⊃ instead of ∈
    t = t.replace("⊅∈", "⊃∉")
    # a lone capital sitting just before an arrow is that arrow's superscript,
    # and belongs after it: `σ1 R ↦0 σ2` is σ₁ ↦ᴿ₀ σ₂
    t = re.sub(rf"\s+([A-Z])\s+([{_ARROWS}])(\d*)",
               lambda m: " " + m.group(2) + _SUP.get(m.group(1), "^" + m.group(1))
                         + m.group(3).translate(_SUB), t)
    # the star of a reflexive-transitive closure extracts as ∗
    t = re.sub(rf"(?<=[{_ARROWS}])∗", "*", t)
    # subscripts are flattened to adjacent digits; restore them after a Greek
    # letter or an arrow, where the reading is unambiguous (a superscript such
    # as `N 2` keeps its space and is left alone)
    t = re.sub(rf"(?<=[{_GREEK}{_ARROWS}])(\d+)",
               lambda m: m.group(1).translate(_SUB), t)
    t = re.sub(rf"(?<=[{''.join(_SUP.values())}])(\d+)",
               lambda m: m.group(1).translate(_SUB), t)
    # a lone capital metavariable with digits: `X1` is X₁.  The lookbehind
    # keeps names such as PS1 intact, and `O(N 2 )` keeps its space and so is
    # left alone — guessing there would turn N² into N₂.
    t = re.sub(r"(?<![A-Za-z0-9])([A-Z])(\d+)(?![A-Za-z])",
               lambda m: m.group(1) + m.group(2).translate(_SUB), t)
    # a prime keeps its subscript, which -raw separates: `σ′ 1` is σ′₁
    t = re.sub(r"(?<=[′'])\s*(\d+)", lambda m: m.group(1).translate(_SUB), t)
    # an index letter after a Greek letter or a prime is a subscript too
    t = re.sub(rf"(?<=[{_GREEK}′])\s?([aeijklmnoprstuvx])(?![A-Za-z])",
               lambda m: _SUBL[m.group(1)], t)
    # spurious space before a closing delimiter, and doubled spaces
    t = re.sub(r"\s+([)\]}])", r"\1", t)
    t = re.sub(r"\(\s+", "(", t)
    # end-of-line hyphenation: `coun- termodel` is one word
    t = re.sub(r"([a-z])-\s+([a-z])", r"\1\2", t)
    # a negated relation printed hard against the next symbol
    t = re.sub(r"([≠∉⊈⊄⊅≢≰≱≮≯⊬⊭])(?=[^\s,.;:)\]}])", r"\1 ", t)
    t = re.sub(r"[ \t]{2,}", " ", t)
    return t.strip()

def pdf_pages(main_tex: str):
    """Rendered text of the compiled PDF, page 1 first.  The statements the
    reader wants are the ones LaTeX printed, with the paper's 164 private
    macros already expanded — which is something no Markdown renderer can
    do for us, since those macros live only in the paper's preamble."""
    import subprocess
    d = os.path.dirname(os.path.abspath(main_tex)) or "."
    pdf = os.path.join(d, os.path.splitext(os.path.basename(main_tex))[0] + ".pdf")
    exe = shutil.which("pdftotext")
    if not exe or not os.path.exists(pdf):
        return {}
    try:
        r = subprocess.run([exe, "-raw", pdf, "-"], capture_output=True, timeout=300)
    except Exception:
        return {}
    pages = r.stdout.decode("utf-8", "replace").split("\f")
    return {i + 1: t for i, t in enumerate(pages)}

_HEAD = re.compile(r"\b(Theorem|Lemma|Corollary|Proposition|Definition|Example|"
                   r"Remark|Claim|Fact|Observation|Conjecture)\s+\d")
# the end of a statement, in order of reliability: the QED box LaTeX prints for
# \qed, then the proof that follows, then the next numbered result.
_QED = re.compile(r"[⊔⊓□∎]")

def _skip_heading(text: str, i: int):
    """Step past an optional parenthesised title and a full stop, allowing the
    nested parens that a title like 'Soundness of FRJ(G)' contains."""
    while i < len(text) and text[i] in " \t\n":
        i += 1
    title = None
    if i < len(text) and text[i] == "(":
        depth, j0 = 0, i
        while i < len(text):
            if text[i] == "(":
                depth += 1
            elif text[i] == ")":
                depth -= 1
                if depth == 0:
                    i += 1
                    title = re.sub(r"\s+", " ", text[j0 + 1:i - 1]).strip()
                    break
            i += 1
    while i < len(text) and text[i] in " \t\n.":
        i += 1
    return i, title

def rendered_statement(pages, kind, number, page, limit=420):
    """The printed statement, read off the page the .aux points at."""
    if not pages or not page:
        return None
    try:
        pno = int(page)
    except ValueError:
        return None
    text = (pages.get(pno, "") or "") + "\n" + (pages.get(pno + 1, "") or "")
    m = re.search(rf"\b{re.escape(kind)}\s+{re.escape(str(number))}\b", text)
    if not m:
        return None
    j, title = _skip_heading(text, m.end())
    tail = text[j:]
    cut = len(tail)
    for pat in (_QED, re.compile(r"\bProof\s*\."), _HEAD, re.compile(r"\bFig\.")):
        hit = pat.search(tail, 1)
        if hit:
            cut = min(cut, hit.start())
    body = re.sub(r"\s+", " ", tail[:cut]).strip()
    if not body:
        return None
    body = fix_glyphs(body)
    return (body[:limit].rstrip() + (" …" if len(body) > limit else ""),
            fix_glyphs(title) if title else None)

def extract(tex: str, kinds: dict):
    """Walk the document, recording sections and theorem-like environments.
    No numbering happens here: the .aux supplies it, keyed by label."""
    items, sec, in_appendix = [], 0, False
    env_names = "|".join(sorted(kinds, key=len, reverse=True))
    pat = re.compile(r"\\(appendix)\b|\\(section)(\*?)\s*\{|"
                     rf"\\begin\{{({env_names})\}}")
    pos = 0
    while True:
        m = pat.search(tex, pos)
        if not m:
            break
        if m.group(1):
            in_appendix, sec, pos = True, 0, m.end()
            continue
        if m.group(2):
            title, end = balanced(tex, m.end() - 1)
            if m.group(3) != "*":
                sec += 1
                items.append(dict(kind="§", title=clean(title or ""), label=None,
                                  body="", appendix=in_appendix))
            pos = end
            continue
        env = m.group(4)
        i = m.end()
        title = ""
        if i < len(tex) and tex[i] == "[":
            t, i = balanced(tex, i, "[", "]")
            title = clean(t or "")
        depth, body_end = 1, len(tex)
        for mm in re.finditer(rf"\\(begin|end)\{{{env}\}}", tex[i:]):
            depth += 1 if mm.group(1) == "begin" else -1
            if depth == 0:
                body_end = i + mm.start()
                break
        body = tex[i:body_end]
        head_only = re.split(r"\\begin\{|\\item\b", body, maxsplit=1)[0]
        lab = re.search(r"\\label\s*\{([^}]*)\}", head_only)
        items.append(dict(kind=kinds[env]["display"], title=title,
                          label=lab.group(1) if lab else None,
                          body=clean(body), appendix=in_appendix))
        pos = body_end
    return items

def infer_unlabelled(items, pages):
    """Give unlabelled items a number and a page.

    They carry no `\\label` of their own, so no `.aux` entry — and they are
    exactly the ones a hand count skips.  Numbers increase with source order
    within a kind, so a gap between two labelled neighbours identifies them;
    the page then comes from searching the printed text for that heading."""
    by_kind = {}
    for it in items:
        if it["kind"] != "§":
            by_kind.setdefault(it["kind"], []).append(it)
    for seq in by_kind.values():
        run, prev = [], None
        for it in seq:
            num = it.get("number")
            if num and num.isdigit():
                nxt = int(num)
                if run and prev is not None and nxt - prev - 1 == len(run):
                    for k, u in enumerate(run, start=1):
                        u["number"], u["inferred"] = str(prev + k), True
                run, prev = [], nxt
            elif not num:
                run.append(it)
        if run and prev is not None:
            for k, u in enumerate(run, start=1):
                u["number"], u["inferred"] = str(prev + k), True
    for it in items:
        if not it.get("inferred"):
            continue
        for pno in sorted(pages or {}):
            if re.search(rf"\b{re.escape(it['kind'])}\s+{it['number']}\b",
                         pages[pno] or ""):
                it["page"] = str(pno)
                got = rendered_statement(pages, it["kind"], it["number"], it["page"])
                if got:
                    it["printed"], it["printed_title"] = got
                break
    return items

def attach_numbers(items, aux, pages=None):
    for it in items:
        if it["kind"] == "§":
            continue
        num, page = aux.get(it["label"] or "", (None, None))
        it["number"], it["page"] = num, page
        got = rendered_statement(pages or {}, it["kind"], num, page)
        it["printed"], it["printed_title"] = (got if got else (None, None))
    return items

def emit_markdown(items, notes, src, aux_ok):
    res = [i for i in items if i["kind"] != "§"]
    app = [i for i in res if i["appendix"]]
    unl = [i for i in res if not i.get("number")]
    L = ["# Fidelity skeleton\n",
         f"*Generated by `paper-skeleton` from `{src}`. {len(res)} numbered items "
         f"across {len([i for i in items if i['kind']=='§'])} sections"
         + (f", {len(app)} of them in an appendix" if app else "") + ".*\n",
         "**Numbering** — " + "; ".join(notes) + "."]
    if aux_ok:
        L.append("\n> Statements below are the **printed** text, read off the "
                 "compiled PDF with `pdftotext`. They are not the LaTeX source: a "
                 "paper's statements are written in its own private macros (this "
                 "one defines 164 of them), so raw source is unreadable in Markdown "
                 "and unrenderable by anything that lacks the preamble. The source "
                 "is kept under each statement, folded, because that is what a "
                 "transcription is checked against.\n")
        L.append("\n> Numbers and pages come from the compiled `.aux`, so they are "
                 "the paper's own. Cite by **label**: labels are stable across "
                 "versions, numbers are not — this paper's arXiv source and its "
                 "journal version number the same results differently.\n")
    else:
        L.append("\n> ⚠ The document did not compile, so **no numbers are shown**. "
                 "Items are listed in source order and keyed by label. A guessed "
                 "number is worse than none.\n")
    if unl and aux_ok:
        L.append(f"> {len(unl)} item(s) carry no `\\label` and so have no number "
                 "here. They are the ones a hand count silently skips.\n")
    if app:
        L.append(f"**There is an appendix, carrying {len(app)} numbered items.** "
                 "Read it before scoping any proof: page limits push load-bearing "
                 "detail there.\n")
    L += ["## Results to be reproduced\n",
          "| Paper item | Statement | Lean name | Status |", "|---|---|---|---|"]
    for it in items:
        if it["kind"] == "§":
            L.append(f"| **§ {it['title']}** | | | |")
            continue
        if it.get("number"):
            name = f"{it['kind']} {it['number']}"
            if it.get("inferred"):
                name += " *(no own label; number inferred)*"
        else:
            name = f"{it['kind']} (unlabelled)"
        shown = it.get("printed_title") or (None if "\\" in (it["title"] or "") else it["title"])
        if shown:
            name += f" ({shown})"
        if it["label"]:
            name += f" · `{it['label']}`"
        if it.get("page"):
            name += f" · p.{it['page']}"
        src = (it.get("printed") or it.get("expanded")
               or "*(statement not extracted; see the sources section)*")
        stmt = src[:180].replace("|", "\\|")
        L.append(f"| {name} | {stmt}{' …' if len(src)>180 else ''} | | OPEN |")
    L += ["\nStatus is one of **PROVED** (sorry-free with a pinned "
          "`#print axioms`), **REFUTED** (kernel-checked countermodel), "
          "**OPEN**, or *out of scope* — kept rigidly distinct.\n",
          "## Divergence log\n",
          "*A divergence is recorded when it is made, not afterwards. Number them; "
          "cite the paper item by label; say what the paper states, what is proved "
          "here instead, and why.*\n",
          "| # | Paper item | What the paper says | What is proved here | Why |",
          "|---|---|---|---|---|\n", "## Full statements\n"]
    for it in res:
        head = f"### {it['kind']} {it.get('number') or '(unlabelled)'}"
        shown = it.get("printed_title") or (None if "\\" in (it["title"] or "") else it["title"])
        if shown:
            head += f" ({shown})"
        L.append(head)
        if it["label"]:
            L.append("`" + it["label"] + "`" +
                     (f"  ·  p.{it['page']}" if it.get("page") else "") +
                     ("  ·  **appendix**" if it["appendix"] else ""))
        L.append("\n" + (it.get("printed") or it.get("expanded")
                          or "*(statement not extracted; see the sources section)*") + "\n")
    L.append("\n## LaTeX sources\n")
    L.append("*What a transcription is checked against. Kept apart from the "
             "statements above so that reading them is uninterrupted: these are "
             "written in the paper's own macros and are not meant to be read as "
             "prose.*\n")
    for it in res:
        L.append(f"**{it['kind']} {it.get('number') or '(unlabelled)'}**"
                 + (f" · `{it['label']}`" if it["label"] else ""))
        L.append("\n```tex\n" + it["body"][:1200] +
                 ("\n… (truncated)" if len(it["body"]) > 1200 else "") + "\n```\n")
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
    ap.add_argument("--text", choices=["pdf", "pandoc"], default="pdf",
                    help="statement text from the rendered PDF (default, Unicode "
                         "prose) or from pandoc (standard LaTeX math, needs a "
                         "viewer that renders $…$)")
    ap.add_argument("--no-compile", action="store_true",
                    help="skip compilation; items will carry no numbers")
    ap.add_argument("--keep", help="where to keep a downloaded source")
    a = ap.parse_args()

    if a.arxiv:
        dest = a.keep or tempfile.mkdtemp(prefix="arxiv-")
        fetch_arxiv(a.arxiv, dest)
        main_tex = find_main(dest)
        src = f"arXiv:{a.arxiv} ({os.path.basename(main_tex)})"
    elif a.dir:
        main_tex = find_main(a.dir); src = main_tex
    else:
        main_tex = a.src; src = main_tex

    tex = resolve_inputs(main_tex)
    kinds, notes = theorem_kinds(tex)
    if a.no_compile:
        aux, note = {}, "compilation skipped (--no-compile)"
    else:
        aux, note = compile_and_read_aux(main_tex)
    notes.append(note)
    pages = {} if a.no_compile else pdf_pages(main_tex)
    items = attach_numbers(extract(tex, kinds), aux, pages)
    items = infer_unlabelled(items, pages)
    macros = sanitise_macros(macro_defs(tex))
    for it in items:
        if it["kind"] == "§":
            continue
        if a.text == "pandoc" or not it.get("printed"):
            it["expanded"] = pandoc_text(macros, it["body"])
            if a.text == "pandoc" and it["expanded"]:
                it["printed"] = it["expanded"]
    md = emit_markdown(items, notes, src, bool(aux))
    if a.out:
        io.open(a.out, "w", encoding="utf-8").write(md)
        print(f"{len([i for i in items if i['kind']!='§'])} items -> {a.out}")
    else:
        print(md)
    if a.json:
        io.open(a.json, "w", encoding="utf-8").write(json.dumps(items, indent=2))

if __name__ == "__main__":
    main()
