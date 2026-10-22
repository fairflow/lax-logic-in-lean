"""Cheap test for METHOD-F0 §1 C / invariant 5: is each ρ-representative
minimal in its known class under the order (◯-depth, size), with a fixed
syntactic order as the last tie-break?

    python3 -I scripts/f0_min_forms.py EXPORT.jsonl F0S2CELLS.jsonl
    python3 -I scripts/f0_min_forms.py --selftest

EXPORT.jsonl is the RNDB export (`lake build rndbexport`, then
`.lake/build/bin/rndbexport <out>`); F0S2CELLS.jsonl is spike S2's per-cell
output (`f0s2`, branch `f0-forms-s2`).  Results of 2026-10-22:
`docs/f0-minimal-forms-test-2026-10-22.md`.

Known members of a class, two sources, kept apart:
  K  kernel-checked: RNDB `interd` entries (union-find), plus equal one-pass
     `Rewrite.canon` forms (a theorem, `canon_interd`, pinned with choice).
  C  computed only: spike S2's decider verdicts (G4c terms / FinCM models, not
     re-checked by the kernel), a T2 formula X with [X] ⊢ ρ and [ρ] ⊢ X.

Formulas are parsed from the library printer: `¬A` is `A ↠ ⊥`, `⊤` is `⊥ ↠ ⊥`,
∧ binds tighter than ∨, ∨ tighter than ↠, ◯ and ¬ are prefix.  Size counts
the nodes of the unabbreviated tree (so `⊤` has size 3).
"""
import json
import sys


# ---------- parsing the printer's output into trees ----------

class P:
    def __init__(self, s):
        self.t = [c for c in s if not c.isspace()]
        self.i = 0

    def peek(self):
        return self.t[self.i] if self.i < len(self.t) else None

    def eat(self, c):
        assert self.peek() == c, (c, self.peek(), "".join(self.t))
        self.i += 1

    def imp(self):
        a = self.disj()
        if self.peek() == "↠":
            self.eat("↠")
            return ("imp", a, self.imp())
        return a

    def disj(self):
        a = self.conj()
        while self.peek() == "∨":
            self.eat("∨")
            a = ("or", a, self.conj())
        return a

    def conj(self):
        a = self.unary()
        while self.peek() == "∧":
            self.eat("∧")
            a = ("and", a, self.unary())
        return a

    def unary(self):
        c = self.peek()
        if c == "¬":
            self.eat("¬")
            return ("imp", self.unary(), ("bot",))
        if c == "◯":
            self.eat("◯")
            return ("box", self.unary())
        if c == "⊥":
            self.eat("⊥")
            return ("bot",)
        if c == "⊤":
            self.eat("⊤")
            return ("imp", ("bot",), ("bot",))
        if c == "(":
            self.eat("(")
            a = self.imp()
            self.eat(")")
            return a
        raise ValueError(f"unexpected {c!r} in {''.join(self.t)}")


def parse(s):
    p = P(s)
    a = p.imp()
    assert p.peek() is None, s
    return a


def size(f):
    return 1 + sum(size(x) for x in f[1:])


def depth(f):
    d = max((depth(x) for x in f[1:]), default=0)
    return d + 1 if f[0] == "box" else d


RANK = {"bot": 0, "and": 1, "or": 2, "imp": 3, "box": 4}


def syn_key(f):
    """A fixed total order on syntax: constructor rank, then children left to right."""
    return (RANK[f[0]],) + tuple(syn_key(x) for x in f[1:])


def weight(f):
    return (depth(f), size(f), syn_key(f))


# ---------- union-find ----------

class UF:
    def __init__(self):
        self.p = {}

    def find(self, x):
        self.p.setdefault(x, x)
        while self.p[x] != x:
            self.p[x] = self.p[self.p[x]]
            x = self.p[x]
        return x

    def union(self, a, b):
        self.p[self.find(a)] = self.find(b)


def main(export, cells):
    reps, uf = {}, UF()
    for line in open(export, encoding="utf-8"):
        r = json.loads(line)
        if r["kind"] == "rep" and r["family"] == "rho":
            reps[r["index"]] = r["formula"]
            uf.union(r["formula"], r["canon"])
        elif r["kind"] == "entry":
            uf.union(r["lhs"], r["lhs_canon"])
            uf.union(r["rhs"], r["rhs_canon"])
            if r["rel"] == "interd":
                uf.union(r["lhs"], r["rhs"])
    # computed memberships from S2 (run "old", decider included)
    le = set()
    for line in open(cells, encoding="utf-8"):
        r = json.loads(line)
        if r.get("run") == "old" and r.get("ans") == "le":
            le.add((r["lhs"], r["rhs"]))
    rho_set = set(reps.values())
    computed = {}
    for (a, b) in le:
        if b in rho_set and (b, a) in le and a not in rho_set:
            computed.setdefault(b, set()).add(a)

    members = {}
    for x in list(uf.p):
        members.setdefault(uf.find(x), set()).add(x)

    rows = []
    for i in sorted(reps):
        rf = reps[i]
        k = members.get(uf.find(rf), {rf})
        c = computed.get(rf, set()) - k
        wr = weight(parse(rf))
        better_k = sorted((x for x in k if weight(parse(x)) < wr), key=lambda x: weight(parse(x)))
        better_c = sorted((x for x in c if weight(parse(x)) < wr), key=lambda x: weight(parse(x)))
        ties = [x for x in k | c if x != rf and weight(parse(x))[:2] == wr[:2]]
        rows.append((i, rf, wr[:2], len(k), len(c), better_k, better_c, ties))
    return rows


def report(rows):
    print("per ρ: weight (◯-depth, size); known members K (kernel-checked) and C (computed only)")
    for i, rf, w, nk, nc, bk, bc, ties in rows:
        print(f"ρ{i} {rf}\n    weight {w}; members K={nk}, C={nc}; "
              f"before it in the full order: K={len(bk)}, C={len(bc)}; equal (depth, size): {len(ties)}")
        for x in bk[:3]:
            print(f"      K before: {x}  {weight(parse(x))[:2]}")
        for x in bc[:3]:
            print(f"      C before: {x}  {weight(parse(x))[:2]}")
        for x in ties[:3]:
            print(f"      tie:      {x}  syntactic order {'before' if weight(parse(x)) < weight(parse(rf)) else 'after'} ρ{i}")

    def strictly(xs, w):
        return [x for x in xs if weight(parse(x))[:2] < w]
    beaten_k = [r[0] for r in rows if strictly(r[5], r[2])]
    beaten_c = [r[0] for r in rows if not strictly(r[5], r[2]) and strictly(r[6], r[2])]
    tied = [r[0] for r in rows if not strictly(r[5], r[2]) and not strictly(r[6], r[2]) and r[7]]
    unique = [r[0] for r in rows if not strictly(r[5], r[2]) and not strictly(r[6], r[2]) and not r[7]]
    print(f"\nbeaten on (◯-depth, size) by a kernel-checked member: {['ρ%d' % i for i in beaten_k]}")
    print(f"beaten on (◯-depth, size) by a computed member only:  {['ρ%d' % i for i in beaten_c]}")
    print(f"minimal on (◯-depth, size), with another member of equal weight: {['ρ%d' % i for i in tied]}")
    print(f"the unique minimum among known members: {['ρ%d' % i for i in unique]}")


def selftest():
    # parser and measures against hand values
    cases = {
        "⊥": (0, 1), "⊤": (0, 3), "◯⊥": (1, 2), "¬◯⊥": (1, 4),
        "◯⊥ ∨ ¬◯⊥": (1, 7), "◯¬◯⊥": (2, 5), "◯(◯¬◯⊥ ↠ ◯⊥ ∨ ¬◯⊥)": (3, 14),
    }
    bad = 0
    for s, (d, n) in cases.items():
        f = parse(s)
        if (depth(f), size(f)) != (d, n):
            print("FAIL", s, depth(f), size(f), "expected", d, n)
            bad += 1
    # the order is ◯-depth first: ◯◯⊥ (depth 2, size 3) comes after ¬¬◯⊥ (depth 1, size 6)
    a, b = parse("◯◯⊥"), parse("¬¬◯⊥")
    if not weight(b) < weight(a):
        print("FAIL depth-first order")
        bad += 1
    if not size(a) < size(b):
        print("FAIL control: by size alone the order flips")
        bad += 1
    print("selftest:", "PASS" if bad == 0 else f"{bad} FAIL")
    return bad


if __name__ == "__main__":
    if "--selftest" in sys.argv:
        sys.exit(selftest())
    report(main(sys.argv[1], sys.argv[2]))
