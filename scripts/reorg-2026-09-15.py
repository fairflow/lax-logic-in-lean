#!/usr/bin/env python3
"""The 2026-09-15 reorganisation of LaxLogic/: old module -> new module.

    scripts/reorg-2026-09-15.py --moves     git mv every file
    scripts/reorg-2026-09-15.py --rewrite   rewrite imports and path references
    scripts/reorg-2026-09-15.py --table     print the mapping as a Markdown table

Declaration names and namespaces are unchanged; only module names and paths
move.  A new name is the old one with the `PLL`/`Belief` prefix dropped, under a
topic directory, so the old name can always be recovered from the new.
"""
import os, re, subprocess, sys

AREAS = {
  'PLL/Syntax':        ['Formula', 'Axiom', 'Proof', 'Polar', 'FinsetKit'],
  'PLL/ND':            ['NDCore', 'Terms', 'Subst', 'Hilbert', 'Theorems', 'Consequence',
                        'Idempotency', 'Judgmental', 'Tactics'],
  'PLL/Normalisation': ['Normal', 'StrongNorm', 'Reducibility', 'TopTop', 'Confluence'],
  'PLL/Semantics':     ['Kripke', 'Frames', 'Completeness', 'CtxCompleteness', 'FinComp',
                        'FiniteModel', 'ConfluentComplete', 'Countermodel', 'CountermodelEmit',
                        'LaxInfinite'],
  'PLL/Realisability': ['Evidence', 'RealCompleteness'],
  'PLL/Sequent':       ['Sequent', 'Focused', 'Craig'],
  'PLL/G4':            ['G4', 'G4Adm', 'G4Dec', 'G4Gap', 'G4Inv', 'G4Set', 'G4Space', 'G4Term',
                        'G4Tower', 'G4ipComplete', 'G4P', 'G4PAdm', 'G4PInv', 'G4PStr', 'G4H',
                        'G4HAdm', 'G4HComp', 'G4HCtr', 'G4HCut', 'G4HInv', 'G4HStr'],
  'PLL/UI':            ['G4UI', 'G4UIAdq', 'G4UIStab', 'G4UITrunc', 'UIChains', 'Candidate',
                        'CandLeast', 'CandOr', 'NoFall', 'NoFallNF', 'NoFallSep'],
  'PLL/SemUI':         ['SemUI', 'SemUIAdjoin', 'SemUIAmalg', 'SemUIBox', 'SemUIChar', 'SemUICtx',
                        'SemUIDesc', 'SemUIFrag', 'SemUIHenkin', 'SemUILaw', 'SemUILayered',
                        'SemUIOFree', 'SemUIRes', 'SemUISplit', 'SemUITrace'],
  'PLL/Search':        ['Search', 'SearchCmd', 'SearchConf', 'SearchDemo', 'SearchEx',
                        'SearchNoFall', 'SearchPin', 'Decide', 'Diagram', 'DiagramCmd', 'Demos',
                        'Exec', 'Run'],
  'PLL/Timing':        ['Timing', 'TimingAdder', 'TimingLookahead', 'TimingRipple', 'Async',
                        'Constraints'],
}
BELIEF = ['BooleanIso', 'Collapse', 'Examples', 'Falsum', 'Idealisation', 'Normality',
          'OpenClosed', 'Realisability']
OTHER = {
  'NucleusJoin': 'Belief/NucleusJoin',
  'LJF': 'Focusing/LJF', 'LJFComplete': 'Focusing/LJFComplete', 'IPCFocused': 'Focusing/IPCFocused',
  'FormattingUtils': 'Util/FormattingUtils', 'GuardMsgsShow': 'Util/GuardMsgsShow',
  'KleeneBrouwer': 'Util/KleeneBrouwer',
}

def mapping():
    m = {}
    for area, names in AREAS.items():
        for n in names:
            m['PLL' + n] = f'{area}/{n}'
    for n in BELIEF:
        m['Belief' + n] = f'Belief/{n}'
    m.update(OTHER)
    return m

M = mapping()

def check():
    top = sorted(f[:-5] for f in os.listdir('LaxLogic') if f.endswith('.lean'))
    stay = {'Obligation', 'QLL'}
    missing = [t for t in top if t not in M and t not in stay]
    extra = [k for k in M if k not in top]
    if missing or extra:
        sys.exit(f'mapping incomplete: unmapped {missing}, unknown {extra}')

def moves():
    check()
    for old, new in M.items():
        os.makedirs(os.path.dirname(f'LaxLogic/{new}.lean'), exist_ok=True)
        subprocess.run(['git', 'mv', f'LaxLogic/{old}.lean', f'LaxLogic/{new}.lean'], check=True)
    print(f'{len(M)} files moved')

def rewrite_text(s):
    # longest names first; a boundary after the name keeps PLLG4H from matching PLLG4HAdm
    for old in sorted(M, key=len, reverse=True):
        new = M[old]
        s = re.sub(r'LaxLogic\.' + re.escape(old) + r'(?![A-Za-z0-9_])', 'LaxLogic.' + new.replace('/', '.'), s)
        s = re.sub(r'LaxLogic/' + re.escape(old) + r'\.lean', 'LaxLogic/' + new + '.lean', s)
    return s

SKIP_DIRS = {'.lake', '.git', '_out', 'node_modules', '.claude'}
SKIP_FILES = {'HANDOFF.md'}          # append-only record: a mapping section is added instead
TEXT_EXT = {'.lean', '.md', '.py', '.sh', '.toml', '.json', '.yml', '.yaml', '.txt', '.html', '.tex', '.jsonl'}

def rewrite():
    changed = 0
    for root, dirs, files in os.walk('.'):
        dirs[:] = [d for d in dirs if d not in SKIP_DIRS and not (root == './docs' and d == 'clp-paper')]
        for f in files:
            p = os.path.join(root, f)
            if f in SKIP_FILES or os.path.splitext(f)[1] not in TEXT_EXT or p.endswith('reorg-2026-09-15.py'):
                continue
            try:
                s = open(p, encoding='utf-8').read()
            except (UnicodeDecodeError, OSError):
                continue
            t = rewrite_text(s)
            if t != s:
                open(p, 'w', encoding='utf-8').write(t)
                changed += 1
    print(f'{changed} files rewritten')

def table():
    print('| old module | new module |\n|---|---|')
    for old, new in sorted(M.items()):
        print(f'| `LaxLogic.{old}` | `LaxLogic.{new.replace("/", ".")}` |')

if __name__ == '__main__':
    {'--moves': moves, '--rewrite': rewrite, '--table': table, '--check': check}[sys.argv[1]]()
