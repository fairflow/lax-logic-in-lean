#!/usr/bin/env python3
"""Watch the ledger gate fail, on purpose.

    scripts/test-ledger-diff.py [docs/status-ledger.jsonl]

`scripts/ledger-diff.py` is the part of the gate that decides whether drift is
a REGRESSION or merely STALE, and a gate nobody has watched fail is not
evidence (CLAUDE.md discipline).  This mutates a copy of the recorded ledger in
a temp directory — one mutation per case — and checks that the classifier says
what it should, including that it stays SILENT on the cases that are not
regressions.

Exits 0 if every case behaves, 1 otherwise, naming the case that did not.
"""
import json, os, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
DIFF = os.path.join(HERE, "ledger-diff.py")


def run(a, b):
    p = subprocess.run([sys.executable, DIFF, a, b], capture_output=True, text=True)
    return p.returncode, p.stdout


def write(path, rows):
    with open(path, "w", encoding="utf-8") as f:
        for r in rows:
            f.write(json.dumps(r, ensure_ascii=False, separators=(",", ":"),
                               sort_keys=True) + "\n")


def main(record):
    rows = [json.loads(l) for l in open(record, encoding="utf-8")]
    # a clean theorem to break.  The "dropped an axiom" case needs one that
    # HAS an axiom to drop — the first clean theorem in this estate is
    # axiom-free, so mutating its axiom list would be a no-op and the case
    # would pass vacuously.
    victims = [r for r in rows if r["kind"] == "theorem" and not r["sorry"]
               and not r["native"]]
    with_axioms = [r for r in victims if r["axioms"]]
    if not victims or not with_axioms:
        sys.exit("test-ledger-diff: the record has no clean theorem to mutate")
    v, v_ax = victims[0], with_axioms[0]

    def mutate(fn, target=None):
        target = target or v
        out = []
        for r in rows:
            r = dict(r)
            if (r["module"], r["decl"]) == (target["module"], target["decl"]):
                r = fn(r)
                if r is None:
                    continue
            out.append(r)
        return out

    cases = [
        ("identical", lambda r: r, 0, None),
        ("a proof becomes a sorry", lambda r: {**r, "sorry": True,
            "axioms": sorted(set(r["axioms"]) | {"sorryAx"})}, 1, "SORRY"),
        ("a proof gains an axiom", lambda r: {**r,
            "axioms": sorted(set(r["axioms"]) | {"Classical.choice"})}, 1, "AXIOM"),
        ("a proof becomes native_decide", lambda r: {**r, "native": True,
            "axioms": sorted(set(r["axioms"]) | {"Lean.ofReduceBool"})}, 1, "NATIVE"),
        ("a declaration disappears", lambda r: None, 1, "GONE"),
    ]
    axiom_cases = [
        ("a proof drops an axiom", lambda r: {**r, "axioms": []}, 2, "STRONGER"),
    ]

    tmp = tempfile.mkdtemp(prefix="ledger-test-")
    fresh = os.path.join(tmp, "fresh.jsonl")
    bad = []
    for name, fn, want_rc, want_tag in cases + axiom_cases:
        write(fresh, mutate(fn, v_ax if (name, fn, want_rc, want_tag) in axiom_cases else v))
        rc, out = run(record, fresh)
        ok = rc == want_rc and (want_tag is None or want_tag in out)
        print(f"  [{'ok ' if ok else 'BAD'}] {name}: exit {rc}"
              + (f", said {want_tag}" if want_tag and want_tag in out else ""))
        if not ok:
            bad.append((name, rc, want_rc, out.strip().splitlines()[:3]))

    # a declaration that changes module, keeping its axioms, is a MOVE
    moved_rows = [dict(r, module=r["module"] + ".Moved") if
                  (r["module"], r["decl"]) == (v["module"], v["decl"]) else r
                  for r in rows]
    write(fresh, moved_rows)
    rc, out = run(record, fresh)
    ok = rc == 2 and "MOVED" in out and "GONE" not in out
    print(f"  [{'ok ' if ok else 'BAD'}] a declaration moves module: exit {rc}")
    if not ok:
        bad.append(("move", rc, 2, out.strip().splitlines()[:3]))

    # the same move, but the axioms changed too, IS a regression
    moved_worse = [dict(r, module=r["module"] + ".Moved",
                        sorry=True, axioms=sorted(set(r["axioms"]) | {"sorryAx"})) if
                   (r["module"], r["decl"]) == (v["module"], v["decl"]) else r
                   for r in rows]
    write(fresh, moved_worse)
    rc, out = run(record, fresh)
    ok = rc == 1 and "MOVED*" in out
    print(f"  [{'ok ' if ok else 'BAD'}] a move that changes the axioms: exit {rc}")
    if not ok:
        bad.append(("move+regress", rc, 1, out.strip().splitlines()[:3]))

    # one addition must NOT be reported as a regression
    added = dict(v, decl=v["decl"] + "._ledger_test_addition")
    write(fresh, rows + [added])
    rc, out = run(record, fresh)
    ok = rc == 2 and "NEW" in out
    print(f"  [{'ok ' if ok else 'BAD'}] a new declaration is STALE, not a regression: exit {rc}")
    if not ok:
        bad.append(("addition", rc, 2, out.strip().splitlines()[:3]))

    if bad:
        print("\ntest-ledger-diff: FAILED")
        for name, rc, want, head in bad:
            print(f"  {name}: exit {rc}, wanted {want}; output {head}")
        return 1
    print("\ntest-ledger-diff: every case behaved, including the silent ones")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1] if len(sys.argv) > 1
                  else os.path.join(HERE, "..", "docs", "status-ledger.jsonl")))
