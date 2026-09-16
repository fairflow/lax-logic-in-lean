#!/usr/bin/env python3
"""Classify the drift between two ledger runs.

    scripts/ledger-diff.py <recorded.jsonl> <fresh.jsonl>

Exit codes, so a caller can tell the two kinds of drift apart:

    0   identical
    1   REGRESSION — something got weaker: a new `sorryAx`, a new axiom, a new
        `native_decide` taint, or a declaration that has disappeared
    2   STALE — only additions, or a declaration that got *stronger* (axioms
        dropped).  Nothing is wrong with the development; the recorded ledger
        needs regenerating and committing.

A regression is reported per declaration, with the axioms that appeared, because
the point of the gate is to name what changed, not to say "diff".
"""
import json, sys

KERNEL = {"propext", "Classical.choice", "Quot.sound"}


def load(path):
    out = {}
    with open(path, encoding="utf-8") as f:
        for line in f:
            r = json.loads(line)
            out[(r["module"], r["decl"])] = r
    return out


def main(recorded_path, fresh_path, scope_fresh=False):
    old, new = load(recorded_path), load(fresh_path)
    if scope_fresh:
        # the fresh run covered only part of the estate (CI builds the default
        # targets, not the papers or `wip/`): compare within those modules and
        # say nothing about the rest, rather than calling them all GONE
        mods = {m for (m, _) in new}
        dropped = {k for k in old if k[0] not in mods}
        old = {k: v for k, v in old.items() if k[0] in mods}
        if dropped:
            print(f"ledger: scoped to {len(mods)} built module(s); "
                  f"{len(dropped)} recorded declaration(s) outside that scope "
                  "are not checked")
    regressions, stale = [], []

    for key in sorted(old.keys() - new.keys()):
        regressions.append(f"GONE        {key[1]}  ({key[0]}) — declaration no longer in the build")

    for key in sorted(new.keys() - old.keys()):
        r = new[key]
        mark = " [sorryAx]" if r["sorry"] else (" [native]" if r["native"] else "")
        stale.append(f"NEW         {key[1]}  ({key[0]}){mark}")

    for key in sorted(old.keys() & new.keys()):
        o, n = old[key], new[key]
        gained = sorted(set(n["axioms"]) - set(o["axioms"]))
        lost = sorted(set(o["axioms"]) - set(n["axioms"]))
        if n["sorry"] and not o["sorry"]:
            regressions.append(f"SORRY       {key[1]}  ({key[0]}) — now depends on `sorryAx`")
        elif n["native"] and not o["native"]:
            regressions.append(f"NATIVE      {key[1]}  ({key[0]}) — now compiler-checked, not kernel-checked")
        elif gained:
            regressions.append(f"AXIOM       {key[1]}  ({key[0]}) — gained {', '.join(gained)}")
        elif lost:
            stale.append(f"STRONGER    {key[1]}  ({key[0]}) — dropped {', '.join(lost)}")
        elif o["kind"] != n["kind"]:
            stale.append(f"KIND        {key[1]}  ({key[0]}) — {o['kind']} became {n['kind']}")

    if not regressions and not stale:
        print(f"ledger: clean — {len(new)} declarations, unchanged")
        return 0

    if regressions:
        print(f"ledger: {len(regressions)} REGRESSION(S)")
        for line in regressions[:200]:
            print("  " + line)
        if len(regressions) > 200:
            print(f"  … and {len(regressions) - 200} more")
    if stale:
        print(f"ledger: {len(stale)} addition(s)/improvement(s) — "
              "regenerate `docs/status-ledger.jsonl`")
        for line in stale[:50]:
            print("  " + line)
        if len(stale) > 50:
            print(f"  … and {len(stale) - 50} more")

    return 1 if regressions else 2


if __name__ == "__main__":
    pos = [a for a in sys.argv[1:] if not a.startswith("--")]
    sys.exit(main(pos[0], pos[1], scope_fresh="--scope-fresh" in sys.argv))
