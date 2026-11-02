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
import sys, os
p = sys.argv[1]; s = open(p, encoding='utf-8').read()
s = s.replace(r'\setmonofont{DejaVu Sans Mono}',
  r'\setmonofont{DejaVuSansMono}[Extension=.ttf, UprightFont=*, BoldFont=*-Bold, '
  r'ItalicFont=*-Oblique, BoldItalicFont=*-BoldOblique]')
fallback = '◯ℚ⊨⊫⋃⋂⋁⊬⊢⊣⊤⊥∧∨⊃≥≤∀∃⟹⟺⇝⋆⋖⋀ℕ∈⊓⊔'   # ⋖⋀ℕ∈⊓: the F0 paper (2026-10-22); ⊔: the semantics paper (2026-10-25)
fallback2 = '⨅'   # not in DejaVu Sans; STIX Two Math has it (the F0 paper, 2026-10-22)
extra = (r'\newfontfamily\symbolfont{DejaVuSans}[Extension=.ttf, UprightFont=*, BoldFont=*-Bold]' '\n'
  + r'\newfontfamily\symbolfontb{STIXTwoMath-Regular}[Extension=.otf]' '\n'
  + ''.join('\\newunicodechar{%s}{{\\symbolfont %s}}\n' % (c, c) for c in fallback)
  + ''.join('\\newunicodechar{%s}{{\\symbolfontb %s}}\n' % (c, c) for c in fallback2)
  + r'\usepackage{amsmath,amssymb}' '\n'                      # \Vdash, \nvdash, \square, \rightsquigarrow (KaTeX has them too)
  + r'\usepackage[a4paper,margin=24mm,headheight=26pt,headsep=14pt]{geometry}' '\n'
  + r'\hypersetup{colorlinks=true, urlcolor=blue!55!black, linkcolor=black, citecolor=black}' '\n'   # no link boxes
  # a line centred above the running heads (the header gets two lines): the
  # paper's running head \versoRunningHead, `III:F0Lattice 0.5 · 25 Oct 2026`,
  # when it declares one with PaperKit's {paperStamp} (2026-10-25); otherwise
  # the build stamp \versoBuildStamp of {buildStamp} (the CLP paper)
  + r'\newcommand{\versoHeadText}{\ifdefined\versoRunningHead{\footnotesize\versoRunningHead}\else{\scriptsize\versoBuildStamp}\fi}' '\n'
  + r'\newcommand{\versoStampText}{\ifdefined\versoBuildStamp{\sffamily\versoHeadText}\fi}' '\n'
  + r'\newcommand{\versoStampLine}{\ifdefined\versoBuildStamp{\sffamily\versoHeadText}\\[2pt]\fi}' '\n'
  + r'\makeoddhead{headings}{}{\parbox{\textwidth}{\centering\versoStampLine\makebox[\textwidth]{{\slshape\rightmark}\hfill\thepage}}}{}' '\n'
  + r'\makeevenhead{headings}{}{\parbox{\textwidth}{\centering\versoStampLine\makebox[\textwidth]{\thepage\hfill{\slshape\leftmark}}}}{}' '\n'
  + r'\makeoddhead{plain}{}{\versoStampText}{}' '\n'
  + r'\makeevenhead{plain}{}{\versoStampText}{}' '\n'
  # the title page (memoir's titlingpage style is an alias of empty)
  + r'\makepagestyle{titlingpage}\makeoddhead{titlingpage}{}{\versoStampText}{}\makeevenhead{titlingpage}{}{\versoStampText}{}' '\n'
  # an optional per-paper addition to the preamble (e.g. no blank recto pages)
  + os.environ.get('VERSO_TEX_EXTRA', '') + '\n')
# the stamp is defined where {buildStamp} is rendered, after the title page and
# the contents; a copy in the preamble puts it in those pages' headers too
# (2026-10-22, the F0 paper)
import re
m = re.search(r'\\gdef\\versoBuildStamp\{[^{}]*\}', s)
if m:
  extra += m.group(0) + '\n'
# a paper with a running head ({paperStamp}): its definition too, and the
# build stamp moves to the title block, the date line of the title page, in
# small type (2026-10-25); the \date given here, after the stamp's definition,
# replaces the template's empty one
m = re.search(r'\\gdef\\versoRunningHead\{[^{}]*\}', s)
if m:
  extra += m.group(0) + '\n'
  extra += r'\date{\sffamily\footnotesize\versoBuildStamp}' '\n'
s = s.replace('\\begin{document}', extra + '\\begin{document}', 1)
# a lettered appendix ({letteredAppendix} of PaperKit/Blocks.lean, the F0 paper
# v0.7, 2026-10-29): the block's marker sits just after the heading of the
# chapter that opens the appendices; \appendix, and a heading that reads
# "Appendix A" above the title, go before that heading.  Verso puts a trailing
# unnumbered part (`number := false`, so that the HTML does not number it
# after the References) in \backmatter, where memoir numbers no chapter:
# memoir's \mainmatter* numbers chapters again without restarting the page
# numbers
mk = '%PaperKit:appendix'
if mk in s:
  i = s.index(mk)
  j = s.rfind('\\chapter{', 0, i)
  s = s[:i] + s[i + len(mk):]
  if j >= 0:
    app = (r'\mainmatter*' '\n' + '\\appendix\n'
      + r'\renewcommand*{\chapnamefont}{\sffamily\Large}' '\n'
      + r'\renewcommand*{\printchaptername}{\chapnamefont\appendixname}' '\n'
      + r'\renewcommand*{\chapternamenum}{\space}' '\n'
      + r'\renewcommand*{\printchapternum}{\chapnamefont\thechapter}' '\n'
      + r'\renewcommand*{\afterchapternum}{\par\nobreak\vskip 8pt}' '\n')
    s = s[:j] + app + s[j:]
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
