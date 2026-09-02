#!/usr/bin/env python3
"""Build a LeanSearch-compatible index over the projects named in toolkit.json.

Declarations are extracted at **source level** — the statement as the author
wrote it, with its doc comment — rather than from Lean's elaborated
environment.  That is deliberate.  The failure this index exists to fix is a
model not knowing that `⋏` is an object-level constructor of `Form` and that
`Deriv Φ Γ _` is an inductively defined relation.  The surface syntax carries
exactly that information; an elaborated type would desugar the notation away
and lose it.

Notation declarations are indexed as first-class entries for the same reason:
`⊟` is meaningless to a model trained on Mathlib until it can look it up.

    python3 build_index.py -o index.jsonl
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from extract import strip_comments_for_scan, TOPLEVEL_RE  # noqa: E402

DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?"
    r"(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+|nonrec\s+|scoped\s+)*"
    r"(theorem|lemma|def|abbrev|instance|structure|inductive|class|opaque|axiom)\s+"
    r"([A-Za-z_À-￿][A-Za-z0-9_'!?.À-￿]*)"
)

NOTATION_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:scoped\s+|local\s+)*"
    r"(notation|infixl|infixr|infix|prefix|postfix|macro_rules|syntax)\b"
)

DOC_OPEN = ("/--",)

SKIP_DIRS = {".lake", ".git", ".claude", "wipx", "Archive", "archive"}
# `wip` is now INDEXED (the campaigns live there); `wipx` holds the files a
# campaign is currently working from and must stay OUT of the corpus, or the
# answer is in the index.


def iter_lean_files(root: Path, skip_extra: set[str]) -> list[Path]:
    out = []
    for p in root.rglob("*.lean"):
        parts = set(p.relative_to(root).parts)
        if parts & (SKIP_DIRS | skip_extra):
            continue
        out.append(p)
    return sorted(out)


def module_name(root: Path, path: Path) -> str:
    rel = path.relative_to(root).with_suffix("")
    return ".".join(rel.parts)


def split_chunks(lines: list[str]) -> list[tuple[int, int]]:
    starts = [i for i, l in enumerate(lines) if l[:1].strip() and TOPLEVEL_RE.match(l)]
    return [
        (s, starts[k + 1] if k + 1 < len(starts) else len(lines))
        for k, s in enumerate(starts)
    ]


def find_sig_end(decl_text: str) -> int:
    """Index of the top-level `:=` (or `where`), else the whole text."""
    scan = strip_comments_for_scan(decl_text)
    depth = 0
    for i, c in enumerate(scan):
        if c in "([{⟨⦃«":
            depth += 1
        elif c in ")]}⟩⦄»":
            depth -= 1
        elif depth == 0 and scan.startswith(":=", i):
            return i
        elif depth == 0 and scan.startswith("\nwhere", i):
            return i
    return len(decl_text)


SORRY_RE = re.compile(r"\bsorry\b")

# A type is only usable if you can see what CONSTRUCTS it.  Retrieval returns
# presences and never absences, so "no rule of this shape exists" -- the
# question a stuck campaign turns on -- is answerable only from a COMPLETE
# constructor list.  Inductives, structures and classes are therefore indexed
# whole, never truncated at the signature, and their constructor names are
# lifted into their own field so a query can hit them directly.
WHOLE_KINDS = {"inductive", "structure", "class"}
# The chunker starts a new chunk at ANY column-0 line, so a `--` comment
# between constructors truncates the type and its constructor list is lost
# (`PLLAxiom` lost all 13 that way).  For a type we therefore re-derive the
# extent ourselves, stopping only at something that really begins a new
# declaration -- a doc comment or a keyword, never a line comment.
NEXT_DECL_RE = re.compile(
    r"^(?:/--|/-!|@\[|theorem\b|lemma\b|def\b|abbrev\b|inductive\b|structure\b|"
    r"class\b|instance\b|opaque\b|axiom\b|example\b|noncomputable\b|private\b|"
    r"protected\b|partial\b|unsafe\b|namespace\b|end\b|section\b|open\b|"
    r"variable\b|universe\b|macro\b|notation\b|syntax\b|elab\b|deriving\b|"
    r"#[a-z]|attribute\b|set_option\b|import\b)")


def type_extent(lines: list[str], start: int, chunk_end: int) -> int:
    """Where a type declaration really ends."""
    j = start + 1
    while j < len(lines) and not NEXT_DECL_RE.match(lines[j]):
        j += 1
    return max(j, chunk_end)
CTOR_RE = re.compile(r"\|\s*([A-Za-z_\u03b1-\u03c9][A-Za-z0-9_'\u2080-\u2089]*)")
FIELD_RE = re.compile(r"^\s{2,}([a-zA-Z_][A-Za-z0-9_'!?]*)\s*:", re.M)


def constructors_of(kind: str, body: str) -> list[str]:
    """Constructor names for an inductive, field names for a structure."""
    names = [m.group(1) for m in CTOR_RE.finditer(strip_comments_for_scan(body))]
    if not names and kind in ("structure", "class"):
        names = [m.group(1) for m in FIELD_RE.finditer(strip_comments_for_scan(body))]
    seen, out = set(), []
    for n in names:
        if n not in seen:
            seen.add(n); out.append(n)
    return out
BLOCK_COMMENT_RE = re.compile(r"/-.*?-/", re.S)
LINE_COMMENT_RE = re.compile(r"--[^\n]*")


def is_sorried(body: str) -> bool:
    """Does the declaration's CODE contain `sorry`?

    Comments are stripped first: a proved lemma whose docstring says
    "sorry-free" must stay in the corpus, and dropping it would degrade
    exactly the retrieval this index exists to provide.
    """
    code = BLOCK_COMMENT_RE.sub(" ", body)
    code = LINE_COMMENT_RE.sub(" ", code)
    return SORRY_RE.search(code) is not None


def harvest(root: Path, repo_label: str, skip_extra: set[str]) -> list[dict]:
    entries: list[dict] = []
    skipped_sorry: list[str] = []
    for path in iter_lean_files(root, skip_extra):
        try:
            text = path.read_text(encoding="utf-8")
        except (UnicodeDecodeError, OSError):
            continue
        lines = text.splitlines(keepends=True)
        # Column-0 prose inside a block comment ("class because the fallible
        # join builds a model...") was being read as a declaration and indexed
        # as one.  Mask the comment interior before chunking.
        in_comment: list[bool] = []
        depth = 0
        for l in lines:
            in_comment.append(depth > 0)
            depth += l.count("/-") - l.count("-/")
            depth = max(depth, 0)
        chunks = [(a, b) for (a, b) in split_chunks(lines) if not in_comment[a]]
        chunks = [(a, chunks[k + 1][0] if k + 1 < len(chunks) else len(lines))
                  for k, (a, _b) in enumerate(chunks)]
        mod = module_name(root, path)
        rel = str(path.relative_to(root))

        # namespace stack, so names can be reported fully qualified
        ns: list[str] = []
        ns_at_line: dict[int, list[str]] = {}
        for i, l in enumerate(lines):
            m = re.match(r"^namespace\s+([A-Za-z_][\w'.]*)", l)
            if m:
                ns.append(m.group(1))
            elif re.match(r"^end\s+[A-Za-z_][\w'.]*", l) and ns:
                ns.pop()
            ns_at_line[i] = list(ns)

        for ci, (s, e) in enumerate(chunks):
            # doc comment immediately above
            doc = ""
            if ci > 0:
                ps, pe = chunks[ci - 1]
                if pe == s and lines[ps].lstrip().startswith(DOC_OPEN):
                    raw = "".join(lines[ps:pe])
                    doc = re.sub(r"^\s*/--|-/\s*$", "", raw, flags=re.S).strip()

            head = lines[s]
            body = "".join(lines[s:e])

            m = DECL_RE.match(head)
            if m:
                # A `sorry`ed declaration ASSERTS its statement and proves
                # nothing.  Retrieval that offers one presents an OPEN
                # conjecture as an available lemma, so drop it from the corpus
                # rather than index it indistinguishably from a proved one.
                # The count is reported, never silently dropped.
                if is_sorried(body):
                    skipped_sorry.append(m.group(2))
                    continue
                kind, name = m.group(1), m.group(2)
                if kind in WHOLE_KINDS:
                    # never truncate a type: the constructor list IS the content
                    body = "".join(lines[s:type_extent(lines, s, e)])
                    sig = body.rstrip()
                else:
                    sig = body[: find_sig_end(body)].rstrip()
                    sig = re.sub(r"\n\s*\n.*", "", sig, flags=re.S).strip()
                ctors = constructors_of(kind, body) if kind in WHOLE_KINDS else []
                prefix = ".".join(ns_at_line.get(s, []))
                full = f"{prefix}.{name}" if prefix else name
                entries.append({
                    "name": full,
                    "short": name,
                    "kind": kind,
                    "signature": sig,
                    "constructors": ctors,
                    "docstring": doc,
                    "module": mod,
                    "repo": repo_label,
                    "file": rel,
                    "line": s + 1,
                })
                continue

            if NOTATION_RE.match(head):
                sig = body.strip().split("\n\n")[0].strip()
                entries.append({
                    "name": f"{mod} (notation)",
                    "short": "notation",
                    "kind": "notation",
                    "signature": sig,
                    "docstring": doc,
                    "module": mod,
                    "repo": repo_label,
                    "file": rel,
                    "line": s + 1,
                })
    if skipped_sorry:
        print(f"  {root}: dropped {len(skipped_sorry)} `sorry`ed declaration(s)",
              file=sys.stderr)
    return entries


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--config", default=None,
                    help="toolkit.json (default: discovered upwards from cwd)")
    ap.add_argument("-o", "--out", type=Path, default=None)
    args = ap.parse_args()

    sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
    from toolkit_config import find_config
    cfg = find_config(args.config)

    out = args.out or (Path(__file__).parent / "index.jsonl")
    entries: list[dict] = []
    skip = set(cfg.exclude)
    # `exclude` entries are matched as single PATH COMPONENTS (see
    # iter_lean_files), so a path-shaped entry like "LaxLogic/ToolkitTest"
    # matches nothing and does so silently. Say so.
    for e in sorted(skip):
        if "/" in e or "\\" in e:
            print(f"warning: exclude entry {e!r} contains a path separator; "
                  f"entries are matched as single path components, so this "
                  f"will never match. Use {e.replace(chr(92), '/').split('/')[-1]!r}.",
                  file=sys.stderr)
    for root in cfg.index_roots:
        rp = Path(root["path"]).expanduser()
        if not rp.is_dir():
            print(f"warning: {rp} not found, skipping", file=sys.stderr)
            continue
        got = harvest(rp, root.get("label", rp.name), skip)
        print(f"{root.get('label', rp.name)}: {len(got)} declarations", file=sys.stderr)
        entries.extend(got)

    with out.open("w") as fh:
        for e in entries:
            fh.write(json.dumps(e) + "\n")
    kinds: dict[str, int] = {}
    for e in entries:
        kinds[e["kind"]] = kinds.get(e["kind"], 0) + 1
    print(f"\ntotal {len(entries)} -> {out}", file=sys.stderr)
    print("  " + ", ".join(f"{k}={v}" for k, v in
                           sorted(kinds.items(), key=lambda x: -x[1])), file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
