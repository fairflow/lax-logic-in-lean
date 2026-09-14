#!/usr/bin/env python3
"""Convert a VersoBlueprint paper to vanilla Verso (Manual genre).

Each `:::theorem`/`:::definition` node becomes its body followed by a
`{docstring Name +allowMissing}` block, so the Lean statement is printed by
Verso itself (HTML and TeX); `:::group` blocks are dropped; blueprint imports
and `open Informal` are removed.  A declaration referenced by several nodes is
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
    src = GROUP.sub('', src)
    def node(m):
        attrs, body = m.group(3), m.group(4).strip()
        lean = re.search(r'lean := "([^"]+)"', attrs)
        out = body + '\n'
        if lean and lean.group(1) not in seen:
            seen.add(lean.group(1))
            out += f'\n{{docstring {lean.group(1)} +allowMissing}}\n'
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
