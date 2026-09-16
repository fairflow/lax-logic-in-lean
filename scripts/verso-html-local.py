#!/usr/bin/env python3
"""Make Verso's one-page HTML readable from file:// as well as over HTTP.

Verso emits <base href="./">, section and docstring permalinks through
find/?domain=…&name=…, and a local table of contents whose links are "";
opened directly, every one of those resolves to a directory listing.  Anchors
survive both ways, so: drop the base tag, turn permalinks into #id (a
section's name is its heading id; a docstring box's id is on its div), and
match contents entries to headings by section number.

    scripts/verso-html-local.py <out-dir>/html-single/index.html
"""
import re, sys

p = sys.argv[1]
s = open(p, encoding='utf-8').read()
s = s.replace('<base href="./">', '')
s = re.sub(r'href="find/\?domain=Verso\.Genre\.Manual\.section&amp;name=([^"]+)"', r'href="#\1"', s)
s = re.sub(r'(<div class="namedocs" id="([^"]+)">\s*<span class="permalink-widget block">\s*<a href=")'
           r'find/\?domain=Verso\.Genre\.Manual\.doc&amp;name=[^"]+"', r'\1#\2"', s)
ids = {m.group(2): m.group(1) for m in re.finditer(r'<h[1-6] id="([^"]+)">\s*(\d+(?:\.\d+)*)\.', s)}
s = re.sub(r'<a href=""><span class="number">(\d+(?:\.\d+)*)\.</span>',
           lambda m: '<a href="#%s"><span class="number">%s.</span>' % (ids.get(m.group(1), ''), m.group(1)), s)
s = s.replace('<a href="" class="header-title">', '<a href="#" class="header-title">')
s = s.replace('<a href="" class="toc-title">', '<a href="#" class="toc-title">')
open(p, 'w', encoding='utf-8').write(s)
print('  html-single: links made file://-safe; unresolved: %d empty, %d find/'
      % (s.count('href=""'), s.count('href="find/')))
