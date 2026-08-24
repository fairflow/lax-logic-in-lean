#!/usr/bin/env python3
"""Turn decorative `#print axioms` into checked pins.

A bare `#print axioms foo` prints into the build log and CHECKS NOTHING.
Only `/-- info: ... -/` + `#guard_msgs in` + `#print axioms foo` fails the
build when the axiom set drifts.  A repo-wide byte scan on 2026-08-21
found 1457 pins, of which 142 were bare — the largest block being the 39
in `wip/rnFRJCerts.lean`, the certificate corpus itself.

Usage:
    lake env lean <file.lean> 2>&1 | python3 tools/pin-backfill.py <file.lean>

Reads Lean's own `info:` output on stdin and rewrites each bare
`#print axioms X` in the file into the guarded triple, using the string
Lean actually emitted.  Never invents a string: a pin with no matching
info line is left bare and reported, so a silent miss is impossible.
"""
import sys, re, io

if len(sys.argv) != 2:
    sys.exit("usage: ... | pin-backfill.py <file.lean>")
path = sys.argv[1]

# Lean emits e.g.
#   file.lean:850:0: info: 'Foo.bar' depends on axioms: [propext, Quot.sound]
#   file.lean:851:0: info: 'Foo.baz' does not depend on any axioms
info = {}
for line in sys.stdin:
    # `lake build` prefixes these with `file:line:col: info: `; a bare
    # `lake env lean file.lean` does not.  Accept both.
    m = re.search(r"'([^']+)' (depends on axioms: \[.*\]|does not depend on any axioms)", line)
    if m:
        info[m.group(1)] = "'%s' %s" % (m.group(1), m.group(2))

src = io.open(path, encoding="utf-8").read().split("\n")
out, done, missed = [], 0, []
for i, l in enumerate(src):
    st = l.strip()
    if st.startswith("#print axioms "):
        name = st[len("#print axioms "):].strip()
        # a pin is guarded iff the immediately preceding non-blank line is
        # `#guard_msgs in`; scanning a 4-line window misclassified a bare
        # pin sitting directly under a DIFFERENT pin's guard (2026-08-24)
        prev = [x.strip() for x in src[max(0, i-4):i] if x.strip()]
        already = bool(prev) and prev[-1].startswith("#guard_msgs")
        # the printed name may be fully qualified while the source is not
        hit = info.get(name) or next(
            (v for k, v in info.items() if k == name or k.endswith("." + name)), None)
        if not already and hit:
            out.append("/-- info: %s -/" % hit)
            out.append("#guard_msgs in")
            out.append(l)
            done += 1
            continue
        if not already and not hit:
            missed.append(name)
    out.append(l)

io.open(path, "w", encoding="utf-8").write("\n".join(out))
print("guarded %d pin(s) in %s" % (done, path))
if missed:
    print("LEFT BARE (no info line seen — nothing invented): %d" % len(missed))
    for m in missed:
        print("   ", m)
