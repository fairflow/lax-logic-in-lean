#!/usr/bin/env bash
# Produce a PDF of the CLP paper (CLPPaper/) from Verso's TeX output.
#
#   scripts/clp-paper-pdf.sh            # → _out/clp-paper/pdf/clp-paper.pdf
#
# Requires: the CLPPaper library built (`lake build CLPPaper`), a TeX Live
# with xelatex, memoir, fontspec, tcolorbox, newunicodechar, the Source
# Serif/Sans/Code Pro packages and the DejaVu fonts (all in a full TeX Live).
#
# Verso's TeX template asks for the system font "DejaVu Sans Mono", which a
# Mac does not have; we point fontspec at TeX Live's copy by filename, and
# use DejaVu Sans for the glyphs Source Serif/Sans and DejaVu Sans Mono lack.
# The TeX backend prints each blueprint node's statement only (no Lean name,
# no status): the HTML render (scripts/clp-paper-render.sh) is the reference.
# The output is not committed (`_out/` is gitignored).
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH=/Library/TeX/texbin:$PATH

out=_out/clp-paper
lake lean CLPPaperMain.lean -- --run CLPPaperMain.lean --output "$out" --with-tex \
  2>&1 | grep -v "not documented\|allowMissing\|^$" | tail -3

rm -rf "$out/pdf"; mkdir -p "$out/pdf"; cp "$out/tex/main.tex" "$out/pdf/main.tex"
python3 - "$out/pdf/main.tex" <<'EOF'
import sys
p = sys.argv[1]; s = open(p, encoding='utf-8').read()
s = s.replace(r'\setmonofont{DejaVu Sans Mono}',
  r'\setmonofont{DejaVuSansMono}[Extension=.ttf, UprightFont=*, BoldFont=*-Bold, '
  r'ItalicFont=*-Oblique, BoldItalicFont=*-BoldOblique]')
extra = (r'\newfontfamily\symbolfont{DejaVuSans}[Extension=.ttf, UprightFont=*, BoldFont=*-Bold]' '\n'
  + ''.join('\\newunicodechar{%s}{{\\symbolfont %s}}\n' % (c, c) for c in '◯ℚ⊨⊫⋃⋂⋁⊬')
  + r'\usepackage[a4paper,margin=24mm]{geometry}' '\n'
  + r'\fvset{fontsize=\small,breaklines=true}' '\n'
  # Verso emits code blocks as plain `verbatim`; route them through fancyvrb so
  # the wide tables get the smaller face and line breaking.
  + r'\RecustomVerbatimEnvironment{verbatim}{Verbatim}{fontsize=\small,breaklines=true}' '\n')
s = s.replace('\\begin{document}', extra + '\\begin{document}', 1)
open(p, 'w', encoding='utf-8').write(s)
EOF

( cd "$out/pdf"
  for i in 1 2 3; do xelatex -interaction=nonstopmode main.tex > "xelatex$i.out" 2>&1 || true; done
  mv main.pdf clp-paper.pdf
  echo "errors:  $(grep -c '^!' main.log || true)"
  echo "missing: $(grep -c 'Missing character' main.log || true) glyphs"
  pdfinfo clp-paper.pdf | grep -E 'Pages|Page size' )
echo "→ $out/pdf/clp-paper.pdf"
