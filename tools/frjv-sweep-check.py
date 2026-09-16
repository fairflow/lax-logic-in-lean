#!/usr/bin/env python3
"""Join `lake exe frjvrun sweep` output against the RNDB banked ρ-order.

Ground truth: every `sepEntry`/`nleEntry`/`frjCertEntry`/`escEntry` in
RNDB/ is a kernel-checked `¬ Deriv [ρi] ρj` — a PLL-level refutation.
FRJV is sound (`soundnessV`), so:

  MISS on a banked ⊬ cell  ->  candidate FRJV incompleteness witness
  HIT  on a banked ⊢ cell  ->  soundness alarm (must be empty)

A MISS on an unbanked cell is not a verdict either way.
"""
import re, glob, sys, json

nle = set()
for f in glob.glob('RNDB/*.lean'):
    s = open(f).read()
    for m in re.finditer(r'\b(sepEntry|nleEntry|frjCertEntry|escEntry)\s+"[^"]*"\s+(\d+)\s+(\d+)', s):
        nle.add((int(m.group(2)), int(m.group(3))))

hit, miss = set(), set()
for line in open(sys.argv[1] if len(sys.argv) > 1 else '/tmp/vsweep.txt'):
    m = re.match(r'VCELL (\d+) (\d+) (HIT|MISS)', line)
    if m:
        (hit if m.group(3) == 'HIT' else miss).add((int(m.group(1)), int(m.group(2))))

done = hit | miss
banked_done = nle & done
print(f"cells run          : {len(done)} / 462")
print(f"banked ⊬ among them: {len(banked_done)}")
print(f"  FRJV HIT         : {len(banked_done & hit)}")
print(f"  FRJV MISS        : {len(banked_done & miss)}   <- incompleteness candidates")
for (i, j) in sorted(banked_done & miss):
    print(f"    rho{i} -> rho{j}")
unbanked = done - nle
print(f"unbanked cells run : {len(unbanked)}  (HIT {len(unbanked & hit)}, MISS {len(unbanked & miss)})")
print("  HITs on unbanked cells (check these against the ⊢ side):")
for (i, j) in sorted(unbanked & hit)[:40]:
    print(f"    rho{i} -> rho{j}")
