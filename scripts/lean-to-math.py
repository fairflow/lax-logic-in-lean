#!/usr/bin/env python3
"""First pass of the transcription step of the verso-paper workflow.

Rewrites the code spans of a Verso section that are formulas (they contain a
logical symbol and no Lean-only token) into Verso math: a paragraph that is
one formula becomes display math ($$`…`), a formula inside prose becomes
inline math ($`…`).  Fenced code blocks and `{docstring …}` lines are left
alone.  The output is a draft: read the diff and fix by hand.

    scripts/lean-to-math.py CLPPaper/Sections/*.lean
"""
import re, sys

SYMS = {
  '⊣⊢': r'\dashv\vdash', '◯': r'\bigcirc', '⊢': r'\vdash', '⊬': r'\nvdash', '⊨': r'\models',
  '⊫': r'\Vdash', '∧': r'\land', '∨': r'\lor', '⊃': r'\supset', '⊂': r'\subset', '∀': r'\forall',
  '∃': r'\exists', '⊤': r'\top', '⊥': r'\bot', '≥': r'\ge', '≤': r'\le', '→': r'\to',
  '⟹': r'\Rightarrow', '⟺': r'\iff', '⇝': r'\rightsquigarrow', '∈': r'\in', '∉': r'\notin',
  '⊆': r'\subseteq', '∘': r'\circ', '×': r'\times', '≠': r'\ne', '·': r'\cdot', '¬': r'\lnot',
  '∅': r'\emptyset', '⋆': r'\star', '♯': r'^\sharp', '□': r'\square', 'ε': r'\varepsilon',
  'π': r'\pi', 'λ': r'\lambda', 'Σ': r'\Sigma', 'Γ': r'\Gamma', 'Δ': r'\Delta', 'Θ': r'\Theta',
  'θ': r'\theta', 'σ': r'\sigma', 'ι': r'\iota', 'ρ': r'\rho', 'α': r'\alpha', 'β': r'\beta',
  '∞': r'\infty', '↦': r'\mapsto', '⟨': r'\langle', '⟩': r'\rangle', '≡': r'\equiv', '⋃': r'\bigcup',
  '⋂': r'\bigcap', '⋁': r'\bigvee', 'φ': r'\varphi', 'ψ': r'\psi', 'χ': r'\chi', 'μ': r'\mu',
  'ν': r'\nu', 'ω': r'\omega', 'Ω': r'\Omega', 'τ': r'\tau', 'κ': r'\kappa', 'γ': r'\gamma',
  'δ': r'\delta', 'η': r'\eta', 'ζ': r'\zeta', 'ξ': r'\xi', 'Φ': r'\Phi', 'Ψ': r'\Psi',
  'Λ': r'\Lambda', 'Π': r'\Pi', 'ũ': r'\tilde{u}', 'ã': r'\tilde{a}', 'ñ': r'\tilde{n}',
  'õ': r'\tilde{o}', 'ỹ': r'\tilde{y}', '′': "'",
}
SUB = dict(zip('₀₁₂₃₄₅₆₇₈₉ₙₘᵢⱼ', ['_0','_1','_2','_3','_4','_5','_6','_7','_8','_9','_n','_m','_i','_j']))
SUP = {'⁰': '^0', '¹': '^1', '²': '^2', '³': '^3', '⁺': '^+'}
LOGICAL = set('◯⊢⊬⊨⊫∧∨⊃∀∃⊤⊥≥≤⟹⟺⇝⊣∈⊆∘×≠⊂')
LEANISH = re.compile(r':=|=>|\|>|::|\.\w|fun |\bmatch\b|\bdo\b|<-|←|\bwith\b|"')
WORD = re.compile(r'(?<![\\A-Za-z])([A-Za-z][A-Za-z]+)(?![A-Za-z])')

def formula_like(s: str) -> bool:
    return any(c in LOGICAL for c in s) and not LEANISH.search(s)

def to_tex(s: str) -> str:
    s = s.replace('\\', r'\backslash ')
    for a, b in (('{', r'\{'), ('}', r'\}'), ('#', r'\#'), ('%', r'\%'), ('&', r'\&'), ('$', r'\$'), ('_', r'\_'), ('~', r'\sim ')):
        s = s.replace(a, b)
    s = re.sub(r'(\w)\u0303', r'\\tilde{\1}', s)          # t̃
    # words (≥2 letters) become upright identifiers, but not TeX commands
    s = WORD.sub(lambda m: r'\mathit{%s}' % m.group(1), s)
    for k in sorted(SYMS, key=len, reverse=True):
        s = s.replace(k, SYMS[k] + ' ')
    for k, v in {**SUB, **SUP}.items():
        s = s.replace(k, v)
    s = re.sub(r'\\_(\w)', r'_\1', s)                        # R_∀ style subscripts back
    s = re.sub(r'([A-Za-z])(\d)\b', r'\1_\2', s)            # w0 → w_0
    s = re.sub(r' +', ' ', s).strip()
    s = re.sub(r'(\\[A-Za-z]+) ([,.;:)\]])', r'\1\2', s)
    return s

CODE = re.compile(r'`([^`\n]+)`')
MATH = re.compile(r'(\$\$?`)([^`\n]+)`')

def fix_math(m):
    body = m.group(2)
    for k in sorted(SYMS, key=len, reverse=True):
        if k in body:
            body = body.replace(k, SYMS[k] + ' ')
    for k, v in {**SUB, **SUP}.items():
        body = body.replace(k, v)
    body = re.sub(r' +', ' ', body).strip()
    return m.group(1) + body + '`'
DISPLAY = re.compile(r'^`([^`\n]+)`([.:])?$')

def convert(text: str) -> str:
    out, fence = [], False
    for line in text.split('\n'):
        if line.startswith('```'):
            fence = not fence; out.append(line); continue
        if fence or line.startswith(('{docstring', '#', 'import', 'open')):   # headings stay plain text
            out.append(line); continue
        m = DISPLAY.match(line.strip())
        if m and formula_like(m.group(1)):
            out.append('$$`' + to_tex(m.group(1)) + '`'); continue
        line = CODE.sub(lambda m: ('$`' + to_tex(m.group(1)) + '`') if formula_like(m.group(1)) else m.group(0), line)
        line = MATH.sub(fix_math, line)   # stray Unicode inside math already written
        out.append(line)
    return '\n'.join(out)

for path in sys.argv[1:]:
    text = open(path, encoding='utf-8').read()
    new = convert(text)
    if new != text:
        open(path, 'w', encoding='utf-8').write(new)
        print('rewrote', path)
