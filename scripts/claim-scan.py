#!/usr/bin/env python3
"""Scan the prose for claims of proof status.

    scripts/claim-scan.py [out.tsv]        (default: docs/claims.tsv)

Emits `file, line, verdict, decls, quote` for every sentence in `docs/*.md`,
`HANDOFF.md`, the three Verso documents and the root method files that asserts
a verdict word (PROVED / REFUTED / OPEN / machine-checked / …).  `decls` holds
the backticked identifiers on the line that look like Lean declaration names —
the citation, when there is one.  `scripts/reconcile-claims.py` then checks
each citation against `docs/status-ledger.jsonl`.

The verdict words and the identifier shape are heuristics over prose: this
finds claims to CHECK, it does not decide anything.
"""
import re, os, sys, csv

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = sys.argv[1] if len(sys.argv) > 1 else os.path.join(REPO, "docs", "claims.tsv")

def rel(p):
    return os.path.relpath(p, REPO)

# ---- file set ----
files = []

files.append(os.path.join(REPO, "docs", "calculus-map.md"))
for fn in sorted(os.listdir(os.path.join(REPO, "docs"))):
    if fn.endswith(".md"):
        p = os.path.join(REPO, "docs", fn)
        if p not in files:
            files.append(p)

files.append(os.path.join(REPO, "HANDOFF.md"))

for base in ("LaxPaper", "CLPPaper", "LaxBlueprint"):
    for root, dirs, fnames in os.walk(os.path.join(REPO, base)):
        for fn in sorted(fnames):
            if fn.endswith(".lean"):
                files.append(os.path.join(root, fn))

for fn in ("README.md", "METHOD.md", "TOOLS.md"):
    p = os.path.join(REPO, fn)
    if os.path.exists(p):
        files.append(p)

# dedupe preserving order
seen = set()
uniq_files = []
for f in files:
    if f not in seen:
        seen.add(f)
        uniq_files.append(f)
files = uniq_files

# ---- verdict word patterns ----
# Each entry: (regex, description). We search case-sensitively for the literal
# forms actually used in this corpus's convention (ALLCAPS verdict words,
# lowercase "proved"/"refuted" as ordinary claims, hyphenated compounds).
VERDICT_RE = re.compile(r"""
    \b(?:
        PROVED|Proved|proved|PROVABLE|provable|
        UNPROVED|unproved|
        REFUTED|Refuted|refuted|
        DISPROVED|Disproved|disproved|disprove[sd]?|
        OPEN|
        sorry-free|sorry\ free|SORRY-FREE|
        machine-checked|MACHINE-CHECKED|Machine-checked|
        kernel-checked|KERNEL-CHECKED|Kernel-checked|
        kernel-\`decide\`-checkable|
        conjecture[sd]?|Conjecture[sd]?|CONJECTURE[SD]?|
        UNVERIFIED|unverified
    )\b
""", re.VERBOSE)

# Identifier-like backtick spans that look like Lean declaration names.
IDENT_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_'.]*$")

STOPWORDS = {
    "sorry", "rfl", "decide", "simp", "omega", "native_decide", "exact",
    "apply", "cases", "induction", "constructor", "trivial", "by", "fun",
    "let", "have", "show", "from", "where", "then", "else", "if", "match",
    "with", "do", "def", "theorem", "lemma", "instance", "class",
    "structure", "inductive", "namespace", "open", "import", "variable",
    "section", "end", "true", "false", "none", "some", "type", "prop",
    "sort", "unit", "nat", "int", "string", "list", "array", "option",
}

BACKTICK_RE = re.compile(r"`([^`]+)`")

VERDICT_TOKENS = {
    "PROVED", "PROVABLE", "UNPROVED", "REFUTED", "DISPROVED", "DISPROVE",
    "DISPROVES", "OPEN", "SORRY-FREE", "SORRYFREE", "MACHINE-CHECKED",
    "KERNEL-CHECKED", "CONJECTURE", "CONJECTURES", "CONJECTURED",
    "UNVERIFIED", "REFUTED!", "PROVED!",
}

def looks_like_decl(tok):
    tok = tok.strip()
    if not tok:
        return False
    if ".lean" in tok:
        return False
    if "/" in tok or " " in tok:
        return False
    if tok.lower() in STOPWORDS:
        return False
    # single-letter tokens in this corpus are formula/context metavariables
    # (`G`, `Z`, `A`, ...), not declaration names.
    if len(tok) <= 1:
        return False
    if tok.upper().rstrip("!") in VERDICT_TOKENS:
        return False
    if not IDENT_RE.match(tok):
        return False
    # require at least one uppercase letter, underscore or dot -- filters
    # out generic prose words accidentally in backticks (e.g. `and`, `the`)
    if not any(c.isupper() or c in "_." for c in tok):
        return False
    # filter out pure numbers-with-dots (unlikely) and single stray symbols
    if tok.count(".") and tok.replace(".", "").isdigit():
        return False
    return True

def decls_on_line(line):
    out = []
    for m in BACKTICK_RE.finditer(line):
        tok = m.group(1)
        if looks_like_decl(tok):
            if tok not in out:
                out.append(tok)
    return out

def decls_nearby(lines, idx, max_ahead=6):
    """When a claim line ends with ':' (or is immediately followed by an
    indented signature block), pull declaration names off the following
    lines, e.g. calculus-map.md's

        completeness for PLL PROVED (2026-08-31):

            gbuC_complete : Nonempty (LaxND [] phi) -> ProvableGbuC (ofPLL phi)
    """
    out = []
    line = lines[idx].rstrip("\n")
    stripped = line.strip()
    if not stripped.endswith(":"):
        return out
    j = idx + 1
    steps = 0
    while j < len(lines) and steps < max_ahead:
        nxt = lines[j].rstrip("\n")
        if nxt.strip() == "":
            j += 1
            steps += 1
            continue
        # indented code-signature line: leading whitespace, then an
        # identifier, then ':' or ':=' etc.
        m = re.match(r"^\s{2,}([A-Za-z_][A-Za-z0-9_'.]*)\s*:", nxt)
        if m:
            tok = m.group(1)
            if looks_like_decl(tok) and tok not in out:
                out.append(tok)
            j += 1
            steps += 1
            continue
        break
    return out

def make_quote(line, matchspan):
    text = line.strip()
    text = re.sub(r"^[\*\-\s]+", "", text)
    words = text.split()
    if not words:
        return ""
    if len(words) <= 20:
        return " ".join(words)
    # centre a 20-word window on the match if possible
    start_char = matchspan[0]
    # approximate word index of match start
    running = 0
    match_word_idx = 0
    for i, w in enumerate(text.split(" ")):
        running += len(w) + 1
        if running >= start_char:
            match_word_idx = i
            break
    wlist = text.split()
    half = 10
    lo = max(0, match_word_idx - half)
    hi = min(len(wlist), lo + 20)
    lo = max(0, hi - 20)
    snippet = " ".join(wlist[lo:hi])
    prefix = "... " if lo > 0 else ""
    suffix = " ..." if hi < len(wlist) else ""
    return prefix + snippet + suffix

rows = []

# ---- rule 1: verdict-word scan over every target file ----
for path in files:
    try:
        with open(path, "r", encoding="utf-8", errors="replace") as fh:
            lines = fh.readlines()
    except OSError:
        continue
    for i, line in enumerate(lines):
        seen_verdicts_this_line = set()
        for m in VERDICT_RE.finditer(line):
            word = m.group(0)
            key = word
            if key in seen_verdicts_this_line:
                continue
            seen_verdicts_this_line.add(key)
            decls = decls_on_line(line)
            if not decls:
                decls = decls_nearby(lines, i)
            quote = make_quote(line, m.span())
            rows.append({
                "file": rel(path),
                "line": i + 1,
                "verdict": word,
                "decls": ",".join(decls),
                "quote": quote,
            })

# ---- rule 2: Verso theorem/lemma/proposition/corollary blocks with (lean := ...) ----
VERSO_BLOCK_RE = re.compile(
    r':::(theorem|lemma|proposition|corollary)\s+"([^"]+)"(.*)$'
)
LEAN_ATTR_RE = re.compile(r'\(lean\s*:=\s*"([^"]*)"\)')

for path in files:
    if not (path.endswith(".lean") and (
        "/LaxPaper/" in path or "/CLPPaper/" in path or "/LaxBlueprint/" in path
    )):
        continue
    try:
        with open(path, "r", encoding="utf-8", errors="replace") as fh:
            lines = fh.readlines()
    except OSError:
        continue
    for i, line in enumerate(lines):
        m = VERSO_BLOCK_RE.search(line)
        if not m:
            continue
        blockkind, blockid, rest = m.groups()
        lm = LEAN_ATTR_RE.search(rest)
        if not lm:
            continue  # no cited declaration -- a pending/blueprint node, not a claim
        decl_field = lm.group(1).strip()
        decls = [d.strip() for d in decl_field.split(",") if d.strip()]
        decls = [d for d in decls if looks_like_decl(d)]
        if not decls:
            continue
        quote = f'{blockkind} "{blockid}"'
        rows.append({
            "file": rel(path),
            "line": i + 1,
            "verdict": blockkind,
            "decls": ",".join(decls),
            "quote": quote,
        })

rows.sort(key=lambda r: (r["file"], r["line"]))

with open(OUT, "w", newline="", encoding="utf-8") as fh:
    w = csv.writer(fh, delimiter="\t", lineterminator="\n")
    w.writerow(["file", "line", "verdict", "decls", "quote"])
    for r in rows:
        w.writerow([r["file"], r["line"], r["verdict"], r["decls"], r["quote"]])

print(f"wrote {len(rows)} rows to {OUT}")
print(f"scanned {len(files)} files")
