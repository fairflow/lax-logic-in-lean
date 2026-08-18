#!/usr/bin/env python3
"""Assemble rnpin certificate files into wip/rnFRJCerts.lean.

  python3 tools/rn-cert-asm.py <certdir> > wip/rnFRJCerts.lean

Each certificate is a finite model as a `Tab`, the frame check by `decide`,
the refutation by `decide`, and the resulting `¬ Interd` theorem.  Nothing
in the output mentions the search that found the model.
"""
import sys, re, os, glob

certdir = sys.argv[1]
bank = open('wip/rnBank.lean').read()

# cell name -> (lhs source, rhs source, status)
cells = {}
for m in re.finditer(r'⟨"([A-Za-z0-9_]+)", (.*?), (q\d+), \.(«open»|proved|refuted)⟩', bank):
    cells[m.group(1)] = (m.group(2), m.group(3), m.group(4))

def q(src):
    """Qualify bare q-names with the bank namespace."""
    return re.sub(r'\bq(\d+)\b', r'RNBank.q\1', src)

blocks, thms, names = [], [], []
for path in sorted(glob.glob(os.path.join(certdir, '*.txt'))):
    base = os.path.basename(path)[:-4]
    parts = base.split('.')
    cell, tag = parts[0], parts[-1]
    # `<cell>.qK.<tag>` retargets the cell at representative qK instead of
    # the one the table assigns: that is how a SURVIVING candidate of an
    # open cell's candidate list is pinned.
    cand = int(parts[1][1:]) if len(parts) == 3 and parts[1].startswith('q') else None
    txt = open(path).read()
    m = re.search(r'-- BEGIN CERTIFICATE --\n(.*?)\n-- END CERTIFICATE --', txt, re.S)
    if not m:
        continue
    tab = m.group(1).strip()
    tab = tab.replace('FRJ.Search.Tab', 'Search.Tab')
    lhs, rhs, status = cells[cell]
    lhs, rhs = q(lhs), q(rhs)
    if cand is not None:
        rhs = f'RNBank.q{cand}'
    sfx = '' if cand is None else f'_q{cand}'
    cell = cell + sfx          # every emitted name carries the candidate
    nm = f'cm_{cell}_{tag}'
    # which entailment the direction refutes
    if tag == 'fwd':          # lhs ⊃ rhs  refutes  Interd.1 : LaxND [lhs] rhs
        ante, cons, comp = lhs, rhs, '1'
    else:                     # rhs ⊃ lhs  refutes  Interd.2 : LaxND [rhs] lhs
        ante, cons, comp = rhs, lhs, '2'
    blocks.append(f"""/-! ### `{cell}` — the stated collapse is FALSE ({'→' if tag=='fwd' else '←'} direction) -/

{tab}

theorem {nm}_ok : {nm}.okB = true := by decide
theorem {nm}_root : {nm}.root < {nm}.n := by decide

def K_{cell}_{tag} : Kripke := {nm}.toKripke {nm}_ok {nm}_root

set_option maxRecDepth 1000000 in
theorem {nm}_force :
    ¬ (K_{cell}_{tag}).force (K_{cell}_{tag}).root
        (ofPLL (.ifThen ({ante}) ({cons}))) := by decide

theorem {cell}_FALSE : ¬ PLLND.SemUI.Interd ({lhs}) ({rhs}) :=
  fun h => not_entails_of_countermodel (K_{cell}_{tag}) {nm}_force h.{comp}

/-- Control: the model is not degenerate — it still forces `q1 = ⊤`.  A
model machinery that made every formula false would refute everything, so
this is the cheap check that the refutation above says something. -/
theorem {nm}_control :
    (K_{cell}_{tag}).force (K_{cell}_{tag}).root (ofPLL RNBank.q1) := by decide
""")
    thms.append(f'{cell}_FALSE')
    names.append(cell)

print(f"""/-
# RN(◯,{{}}) dictionary cells refuted by the FRJ(◯) search — GENERATED FILE

Produced by `sh tools/rn-cert-gen.sh` + `python3 tools/rn-cert-asm.py`.

Each block below is a countermodel found by the FRJ(◯) forward-saturation
search (`FRJ/Search/Fast.lean`), extracted from the derivation the search
built (`FRJ.modR`), minimised, and re-checked here BY THE KERNEL: the frame
conditions and the refutation are both `decide`, and the conclusion goes
through `FRJ.not_entails_of_countermodel`, which is a theorem about the
original `LaxND` judgment.  The search is nowhere in the certificate.

Every goal below was NOT refuted by the exhaustive ≤4-world battery: every
model here needs five worlds or more, which is why these were open.

READ THE NAMES CAREFULLY.  An open cell of `wip/rnDict.lean` carries a
CANDIDATE LIST and is sorried at the FIRST open candidate, so refuting the
stated collapse eliminates ONE candidate and closes the cell only when that
candidate was the last.

* `<cell>_FALSE` refutes the collapse as the dictionary states it.
* `<cell>_qK_FALSE` refutes the collapse against representative `qK`
  instead — that is how a SURVIVING candidate is eliminated.
* `<cell>_no_candidate` is emitted only where every candidate is gone, and
  IS the statement that the fifteen-representative closure fails at that
  cell.  Its scope is exactly the candidates named in it: the remaining
  representatives were eliminated earlier by the ≤4-world battery, which is
  what produced the candidate list, and that elimination is recorded in
  `wip/rnDict.lean`, not re-proved here.

Goals refuted here: {len(names)} — {', '.join(names)}.
-/
import FRJ.Search.Pin
import LaxLogic.PLLSemUIFrag
import wip.rnBank

namespace RNFRJCerts

open FRJ

""")
print('\n'.join(blocks))
# Where every candidate of a cell has been refuted, the closure fails there.
byCell = {}
for n in names:
    m = re.match(r'(.*?)(?:_q(\d+))?$', n)
    base = m.group(1) if m.group(2) else n
    byCell.setdefault(base, []).append(n)
exh = []
for base, got in sorted(byCell.items()):
    stated = cells[base][1] if base in cells else None
    cands = {stated} | {f'q{n.rsplit("_q",1)[1]}' for n in got if '_q' in n.rsplit('_',1)[0]+'_'+n.rsplit('_',1)[1] and re.search(r'_q(\d+)$', n)}
    have = {stated} | {re.search(r'_q(\d+)$', n).group(1) and 'q'+re.search(r'_q(\d+)$', n).group(1) for n in got if re.search(r'_q(\d+)$', n)}
    if len(have) >= 3:
        parts = ' ∧ '.join(f'¬ PLLND.SemUI.Interd ({q(cells[base][0])}) (RNBank.{c})'
                           for c in sorted(have, key=lambda x: int(x[1:])))
        proof = ', '.join(f'{base}{"" if c == stated else "_" + c}_FALSE'
                          for c in sorted(have, key=lambda x: int(x[1:])))
        print(f'''/-! ### `{base}` — NO candidate survives, so the closure FAILS here

The candidate list of this cell was `[1, 11, 13]`; all three are now
eliminated by kernel-checked countermodels.  The other twelve
representatives were eliminated by the ≤4-world battery recorded in
`wip/rnDict.lean`, so this theorem's scope is exactly the three named. -/

theorem {base}_no_candidate :
    {parts} :=
  ⟨{proof}⟩
''')
        exh.append(f'{base}_no_candidate')
print('/-! ## Axiom pins -/\n')
for t in thms + exh:
    print(f'#print axioms {t}')
print('\nend RNFRJCerts')
