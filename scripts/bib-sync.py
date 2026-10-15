#!/usr/bin/env python3
"""Keep a master bibliography in step with the documents that cite things.

    scripts/bib-sync.py BIB [--repo DIR] [--ref REF] [--exclude OTHER.bib] [--dry-run]

Scans the Markdown files (and the Verso paper sources) committed at REF
(default origin/main) in the git repository DIR (default .) for DOIs and arXiv
identifiers, and adds to BIB every one that is not already in BIB or in
OTHER.bib.  BibTeX comes from doi.org and arxiv.org; each added entry gets an
author-year key (surnames of up to three authors, else FirstEtAl) and a
`citedin` field naming the files that cite it.  An identifier whose title
duplicates an existing entry is skipped.  Entries already in BIB are never
touched, so hand corrections and notes survive; the file stays sorted by key,
with its header comment kept.

Written 2026-10-15 for docs/references.bib (public) and, with --exclude
pointing at the public list, for the private repository's
docs/references-private.bib.  Fetched entries are not checked against the
works themselves.
"""
import json
import os
import re
import subprocess
import sys
import time
import unicodedata

SOURCES = ("CLPPaper/", "LaxPaper/", "CurryPaper/", "LaxBlueprint/")
ORDER = ["author", "editor", "title", "journal", "booktitle", "publisher", "series",
         "volume", "number", "pages", "year", "doi", "eprint", "archiveprefix",
         "primaryclass", "url", "note", "citedin"]


def entries(s):
    out = []
    for m in re.finditer(r'^[ \t]*@(\w+)\s*\{', s, re.M):
        j, d = m.end(), 1
        while d and j < len(s):
            d += {'{': 1, '}': -1}.get(s[j], 0)
            j += 1
        out.append(s[m.start():j].strip())
    return out


def key_of(e):
    return re.match(r'@\w+\s*\{\s*([^,]+),', e).group(1)


def fields(e):
    body = e[e.index(',') + 1:e.rindex('}')]
    out, i = {}, 0
    while i < len(body):
        m = re.match(r'\s*,?\s*([A-Za-z]+)\s*=\s*', body[i:])
        if not m:
            break
        name, j = m.group(1).lower(), i + m.end()
        if body[j] == '{':
            d, k = 1, j + 1
            while d and k < len(body):
                d += {'{': 1, '}': -1}.get(body[k], 0)
                k += 1
            val, i = body[j + 1:k - 1], k
        elif body[j] == '"':
            k = body.index('"', j + 1)
            val, i = body[j + 1:k], k + 1
        else:
            m2 = re.match(r'[^,}\s]+', body[j:])
            val, i = m2.group(0), j + m2.end()
        out[name] = re.sub(r'\s+', ' ', val).strip()
    return out


def norm(x):
    return re.sub(r'[^a-z0-9]', '', unicodedata.normalize('NFKD', x).lower())


def clean_doi(x):
    x = re.sub(r'\.pdf$', '', x).rstrip('.')
    while x.endswith(')') and x.count('(') < x.count(')'):
        x = x[:-1]
    return x.rstrip('.')


def fetch(url, accept=None):
    cmd = ["curl", "-sL", "-m", "20", url]
    if accept:
        cmd[1:1] = ["-H", "Accept: " + accept]
    for attempt in range(3):
        r = subprocess.run(cmd, capture_output=True, text=True)
        if r.stdout.strip().startswith("@"):
            return r.stdout
        time.sleep(2 * (attempt + 1))
    return ""


def main():
    args = sys.argv[1:]
    if not args:
        print(__doc__)
        return 2
    bib = args[0]

    def opt(name, default):
        return args[args.index(name) + 1] if name in args else default
    repo, ref, exclude = opt("--repo", "."), opt("--ref", "origin/main"), opt("--exclude", None)
    dry = "--dry-run" in args

    text = open(bib, encoding="utf-8").read() if os.path.exists(bib) else ""
    header = text[:text.index("@")] if "@" in text else text
    have = entries(text)
    known = text + (open(exclude, encoding="utf-8").read() if exclude else "")
    have_doi = {x.lower() for x in re.findall(r'doi\s*=\s*\{([^}]*)\}', known, re.I)}
    have_arx = set(re.findall(r'(\d{4}\.\d{4,5})', known))
    titles = {norm(fields(e).get("title", "")) for e in entries(known)}
    keys = {key_of(e) for e in entries(known)}

    files = subprocess.run(["git", "-C", repo, "ls-tree", "-r", "--name-only", ref],
                           capture_output=True, text=True, check=True).stdout.split()
    files = [f for f in files if f.endswith(".md") or f.startswith(SOURCES)]
    dois, arx = {}, {}
    for f in files:
        t = subprocess.run(["git", "-C", repo, "show", ref + ":" + f],
                           capture_output=True, text=True).stdout
        for x in re.findall(r'\b(10\.\d{4,9}/[^\s>\]`,;"\'*]+)', t):
            x = clean_doi(x)
            if x.lower() not in have_doi:
                dois.setdefault(x, set()).add(f)
        for x in (re.findall(r'arXiv[:\s]*(\d{4}\.\d{4,5})', t, re.I)
                  + re.findall(r'arxiv\.org/(?:abs|pdf)/(\d{4}\.\d{4,5})', t)):
            if x not in have_arx:
                arx.setdefault(x, set()).add(f)
    print("bib-sync: %d new DOIs, %d new arXiv identifiers" % (len(dois), len(arx)))
    if dry:
        print(json.dumps({"doi": {k: sorted(v) for k, v in dois.items()},
                          "arxiv": {k: sorted(v) for k, v in arx.items()}}, indent=1))
        return 0

    added, skipped, failed = [], [], []
    todo = [("https://doi.org/" + d, "application/x-bibtex; charset=utf-8", d, s, 0.3)
            for d, s in dois.items()]
    todo += [("https://arxiv.org/bibtex/" + a, None, a, s, 1.0) for a, s in arx.items()]
    for url, acc, ident, src, pause in todo:
        raw = fetch(url, acc)
        time.sleep(pause)
        es = entries(raw)
        if not es:
            failed.append(ident)
            continue
        f = fields(es[0])
        if "doi" in f:
            f["doi"] = re.sub(r'^https?://(dx\.)?doi\.org/', '', f["doi"])
        if norm(f.get("title", "")) in titles:
            skipped.append(ident)
            continue
        names = [a.strip() for a in re.split(r'\s+and\s+', f.get("author", "")) if a.strip()]
        sur = [re.sub(r'[^A-Za-z]', '', unicodedata.normalize('NFKD',
               n.split(',')[0] if ',' in n else n.split()[-1])) for n in names]
        base = ("".join(sur) if len(sur) <= 3 else sur[0] + "EtAl") or "Anon"
        base += f.get("year", "nd")
        k, c = base, ord('a')
        while k in keys:
            k, c = base + chr(c), c + 1
        keys.add(k)
        titles.add(norm(f.get("title", "")))
        f["citedin"] = ", ".join(sorted(src))
        typ = re.match(r'@(\w+)', es[0]).group(1).lower()
        lines = ["@%s{%s," % (typ, k)] + ["  %s = {%s}," % (n, f[n].replace("–", "--"))
                                           for n in ORDER if n in f]
        lines[-1] = lines[-1].rstrip(",")
        added.append("\n".join(lines) + "\n}")
        if "year" not in f:
            print("bib-sync: %s has no year; fix its key and year by hand" % k)
    allE = sorted(have + added, key=lambda e: key_of(e).lower())
    open(bib, "w", encoding="utf-8").write(header + "\n\n".join(allE) + "\n")
    print("bib-sync: added %d, skipped %d as duplicates by title, failed %d %s"
          % (len(added), len(skipped), len(failed), failed))
    return 0


if __name__ == "__main__":
    sys.exit(main())
