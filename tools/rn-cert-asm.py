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
    cell, tag = base.rsplit('.', 1)
    txt = open(path).read()
    m = re.search(r'-- BEGIN CERTIFICATE --\n(.*?)\n-- END CERTIFICATE --', txt, re.S)
    if not m:
        continue
    tab = m.group(1).strip()
    tab = tab.replace('FRJ.Search.Tab', 'Search.Tab')
    lhs, rhs, status = cells[cell]
    lhs, rhs = q(lhs), q(rhs)
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

Every cell listed here is stated as `sorry` in `wip/rnDict.lean` and was NOT
refuted by the exhaustive ≤4-world battery — every model below needs five
worlds or more, which is why they were open.  Each one is a cell where the
fifteen-representative closure of the variable-free fragment FAILS, so each
adds to the four already recorded in `docs/rn-dictionary-status.md`.

Cells refuted here: {len(names)} — {', '.join(names)}.
-/
import FRJ.Search.Pin
import LaxLogic.PLLSemUIFrag
import wip.rnBank

namespace RNFRJCerts

open FRJ

""")
print('\n'.join(blocks))
print('/-! ## Axiom pins -/\n')
for t in thms:
    print(f'#print axioms {t}')
print('\nend RNFRJCerts')
