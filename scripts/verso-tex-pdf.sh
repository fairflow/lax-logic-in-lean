#!/usr/bin/env bash
# Compile Verso's TeX output (main.tex) to a PDF with xelatex.
#
#   scripts/verso-tex-pdf.sh <tex-dir> <out.pdf>
#
# Verso's TeX template asks for the system font "DejaVu Sans Mono" and uses
# Source Serif/Sans Pro for text.  On a Mac the mono font is absent and the
# text fonts lack the logical symbols, so we point fontspec at TeX Live's copy
# of DejaVu by file name and use DejaVu Sans for the glyphs the text fonts
# lack; code blocks (plain `verbatim` in Verso's output) are routed through
# fancyvrb so wide lines break.  Needs a full TeX Live (memoir, fontspec,
# tcolorbox, newunicodechar, sourceserifpro/sourcesanspro/sourcecodepro, the
# DejaVu fonts).
set -euo pipefail
texdir=$1; out=$2
export PATH=/Library/TeX/texbin:$PATH
work=$texdir/build; mkdir -p "$work"; cp "$texdir/main.tex" "$work/main.tex"
python3 - "$work/main.tex" <<'PY'
import sys
p = sys.argv[1]; s = open(p, encoding='utf-8').read()
s = s.replace(r'\setmonofont{DejaVu Sans Mono}',
  r'\setmonofont{DejaVuSansMono}[Extension=.ttf, UprightFont=*, BoldFont=*-Bold, '
  r'ItalicFont=*-Oblique, BoldItalicFont=*-BoldOblique]')
fallback = '◯ℚ⊨⊫⋃⋂⋁⊬⊢⊣⊤⊥∧∨⊃≥≤∀∃⟹⟺⇝⋆'
extra = (r'\newfontfamily\symbolfont{DejaVuSans}[Extension=.ttf, UprightFont=*, BoldFont=*-Bold]' '\n'
  + ''.join('\\newunicodechar{%s}{{\\symbolfont %s}}\n' % (c, c) for c in fallback)
  + r'\usepackage{amsmath,amssymb}' '\n'                      # \Vdash, \nvdash, \square, \rightsquigarrow (KaTeX has them too)
  + r'\usepackage[a4paper,margin=24mm]{geometry}' '\n'
  + r'\hypersetup{colorlinks=true, urlcolor=blue!55!black, linkcolor=black, citecolor=black}' '\n'   # no link boxes
  + r'\fvset{fontsize=\small,breaklines=true}' '\n'
  + r'\RecustomVerbatimEnvironment{verbatim}{Verbatim}{fontsize=\small,breaklines=true}' '\n')
s = s.replace('\\begin{document}', extra + '\\begin{document}', 1)
open(p, 'w', encoding='utf-8').write(s)
PY
( cd "$work"
  for i in 1 2 3; do xelatex -interaction=nonstopmode main.tex > "xelatex$i.out" 2>&1 || true; done
  echo "tex errors:      $(grep -c '^!' main.log || true)"
  echo "missing glyphs:  $(grep -c 'Missing character' main.log || true)"
  grep 'Missing character' main.log | sed -E 's/.*There is no (.) .*/\1/' | sort | uniq -c | sort -rn | head -5 || true )
test -f "$work/main.pdf"
mkdir -p "$(dirname "$out")"; cp "$work/main.pdf" "$out"
pdfinfo "$out" | grep -E 'Pages|Page size' || true
echo "→ $out"
