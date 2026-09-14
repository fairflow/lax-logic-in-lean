#!/usr/bin/env python3
"""Convert a VersoBlueprint paper to vanilla Verso (Manual genre).

Each `:::theorem`/`:::definition` node becomes its body followed by the three
generated lines `{stmt}`Name`` (the statement as mathematics),
`{docstring Name +allowMissing}` (the Lean statement, printed by Verso) and
`{srcLink}`Name`` (path:line → the repository at the build commit);
`:::group` blocks are dropped; blueprint imports and `open Informal` are
removed and `CLPPaper.Src`/`CLPPaper.Math` (the roles) imported.  A declaration referenced by several nodes is
documented once (the docstring domain rejects duplicates).

    scripts/blueprint-to-vanilla.py CLPPaper/Sections/*.lean
"""
import re, sys

NODE = re.compile(r'^:::(theorem|definition) "([^"]+)"([^\n]*)\n(.*?)^:::[ \t]*$\n?', re.S | re.M)
GROUP = re.compile(r'^:::group "[^"]+"\n.*?^:::[ \t]*$\n?', re.S | re.M)
seen = set()

def convert(src: str) -> str:
    src = re.sub(r'^import VersoBlueprint[^\n]*\n', '', src, flags=re.M)
    src = re.sub(r'^open Informal[^\n]*\n', '', src, flags=re.M)
    if 'import CLPPaper.Src' not in src:
        src = re.sub(r'^(import LaxLogic\.QLL[^\n]*\n)', r'\1import CLPPaper.Src\nimport CLPPaper.Math\n', src, count=1, flags=re.M)
        src = src.replace('open Verso.Genre.Manual\n', 'open Verso.Genre.Manual\nopen CLPPaper CLPPaper.Math\n', 1)
    src = GROUP.sub('', src)
    def node(m):
        attrs, body = m.group(3), m.group(4).strip()
        lean = re.search(r'lean := "([^"]+)"', attrs)
        out = body + '\n'
        if lean and lean.group(1) not in seen:
            seen.add(lean.group(1))
            n = lean.group(1)
            out += f'\n{{stmt}}`{n}`\n\n{{docstring {n} +allowMissing}}\n\n{{srcLink}}`{n}`\n'
        return out + '\n'
    src = NODE.sub(node, src)
    src = re.sub(r'\n{3,}', '\n\n', src)
    return src

for path in sys.argv[1:]:
    text = open(path, encoding='utf-8').read()
    new = convert(text)
    if new != text:
        open(path, 'w', encoding='utf-8').write(new)
        print(f'converted {path}')
