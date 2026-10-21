#!/usr/bin/env python3
"""Read-only audit of RNDB, the database of F0 = RN(◯,∅) (spike S1, 2026-10-21).

Input: the JSON Lines written by `.lake/build/bin/rndbexport`
(tools/RNDBExport.lean), plus the repository's own sources (header claims,
the import closure, generator scripts).  Output: a plain-text report on stdout
and a JSON summary.  Nothing is written except the --summary file.

    python3 -I scripts/rndb_audit.py --export _out/rndb-export.jsonl \
        --repo . --summary _out/rndb-audit-summary.json
    python3 -I scripts/rndb_audit.py --export _out/rndb-export.jsonl \
        --repo . --selftest          # the gate watch: injected faults must fire

Exit status: 2 if a contradiction ALARM fires, 3 if --selftest finds a gate
that did not fire, else 0.

Keys.  RAW = the injective printed form of the syntax tree (the exporter checks
injectivity against Rewrite.keyF).  CANON = the printed form of
`Rewrite.canon φ`, a certified normaliser (`Rewrite.canon_interd : Interd φ
(canon φ)`), so equal CANON keys imply interderivability, not conversely.
CANONFIX = CANON iterated to a fixpoint, using the exporter's list of the
formulas on which `canon` is not idempotent.
"""
import argparse
import collections
import contextlib
import copy
import io
import json
import os
import re
import sys


# ----------------------------------------------------------------------------
# helpers
# ----------------------------------------------------------------------------

def load(path):
    rows = collections.defaultdict(list)
    with open(path, encoding="utf-8") as fh:
        for line in fh:
            line = line.strip()
            if line:
                r = json.loads(line)
                rows[r["kind"]].append(r)
    return rows


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
        ra, rb = self.find(a), self.find(b)
        if ra != rb:
            self.p[ra] = rb


def out(*a):
    print(*a)


def head(title):
    out()
    out("=" * 78)
    out(title)
    out("=" * 78)


REL_SYM = {"le": "⊢", "interd": "⊣⊢", "nle": "⊬"}


def strip_lean_comments(src):
    """Remove `--` line comments and nested `/- … -/` block comments (doc
    comments included) and string literals, so a `sorry` token count sees
    code only."""
    res, i, n, depth = [], 0, len(src), 0
    while i < n:
        if depth == 0 and src.startswith("--", i):
            j = src.find("\n", i)
            i = n if j < 0 else j
            continue
        if src.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if depth > 0 and src.startswith("-/", i):
            depth -= 1
            i += 2
            continue
        if depth > 0:
            i += 1
            continue
        if src[i] == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            i = j + 1
            continue
        res.append(src[i])
        i += 1
    return "".join(res)


# ----------------------------------------------------------------------------
# header and documentation claims:
#   (file, exact text that must still occur, quantity, claimed value)
# ----------------------------------------------------------------------------

HEADER_CLAIMS = [
    ("RNDB/DB.lean", "single definition is 1,874 kernel-checked facts", "total", 1874),
    ("RNDB/DB.lean", "| `RhoEntries`      |  185 |", "rho", 185),
    ("RNDB/DB.lean", "| `DictEntries`     |  236 |", "dictR1", 236),
    ("RNDB/DB.lean", "| `Dict2Entries`    |   82 |", "dictR2", 82),
    ("RNDB/DB.lean", "| `FRJCertEntries`  |   24 |", "frjCert", 24),
    ("RNDB/DB.lean", "| `DerivedEntries`  |  321 |", "derived", 321),
    ("RNDB/DB.lean", "| `EscEntries`      |  928 |", "esc", 928),
    ("RNDB/DB.lean", "| `Order`           |    3 |", "order", 3),
    ("RNDB/DB.lean", "| `SepEntries`      |   95 |", "sep", 95),
    ("RNDB/DB.lean", "theorem allEntries_length : allEntries.length = 1874", "total", 1874),
    ("README.md", "1,874 kernel-checked facts", "total", 1874),
    ("docs/certified-computation-findings-2026-10-09.md", "1,776 kernel-checked facts as one object", "total", 1776),
    # ^ a dated record: not rewritten, so STALE by design (it carries a dated note)
    ("TOOLS.md", "re-measured 2026-10-21: 1874 entries", "total", 1874),
    ("docs/rn-catalogue.html", "<b>1874</b><span>RNDB entries</span>", "total", 1874),
    ("RNDB/RhoEntries.lean", "each of the 185 kernel-checked refutation", "rho", 185),
    ("RNDB/DictEntries.lean", "the 236 cells the pin-guarded", "dictR1", 236),
    ("RNDB/DerivedEntries.lean", "The SYMM closure of every interd entry (318)", "derived:symm", 318),
    ("RNDB/DerivedEntries.lean", "theorem derivedEntries_length : derivedEntries.length = 321", "derived", 321),
    ("RNDB/EscEntries.lean", "928 `nle` entries", "esc", 928),
    ("RNDB/EscEntries.lean", "for each of the\n58 refuted round-2 cells", "esc:cells", 58),
    ("RNDB/SepEntries.lean", "# The 95 battery-separation entries", "sep", 95),
    ("RNDB/Order.lean", "theorem orderEntries_length : orderEntries.length = 3", "order", 3),
    ("RNDB/Order.lean", "the 158 ⊢ engine-certified, all 304 ⊬ kernel-pinned", "rho_matrix_nle", 304),
    ("RNDB/Frontier79.lean", "theorem frontier79_length : frontier79.length = 79", "frontier79", 79),
    ("RNDB/Frontier79.lean", "all 79 members are BANKED", "frontier79_backed", 79),
    ("RNDB/Types.lean", "the file now contains\nno `sorry`", "rnDict_sorry_tokens", 0),
]


def check_headers(repo, actual):
    head("1. COUNTS PER SOURCE AGAINST THE HEADERS AND DOCUMENTS")
    out("actual:", json.dumps({k: actual[k] for k in sorted(actual)}, ensure_ascii=False))
    results = []
    for f, quote, what, n in HEADER_CLAIMS:
        p = os.path.join(repo, f)
        txt = open(p, encoding="utf-8").read() if os.path.exists(p) else ""
        present = quote in txt
        verdict = ("OK" if n == actual.get(what) else "STALE") if present else "TEXT-GONE"
        results.append(dict(file=f, quote=quote.replace("\n", " "), what=what, claimed=n,
                            actual=actual.get(what), verdict=verdict))
        out(f"  [{verdict:9}] {f}: {what} claimed {n}, actual {actual.get(what)}"
            f"   «{quote.replace(chr(10), ' ')[:70]}»")
    return results


# ----------------------------------------------------------------------------
# the analysis
# ----------------------------------------------------------------------------

def analyse(rows, repo):
    entries = rows["entry"]
    frontier = rows["frontier"]
    reps = rows["rep"]
    meta = rows["meta"][0]
    examples = rows.get("example_entry", [])
    S = {}

    head("0. EXPORT SELF-CHECKS (tools/RNDBExport.lean)")
    out(f"entries {len(entries)}, allEntries_length {meta['allEntries_length']}, "
        f"walk_equals_allEntries {meta['walk_equals_allEntries']}")
    out(f"source_counts {meta['source_counts']}")
    out(f"distinct printed formulas {meta['distinct_printed_formulas']}, "
        f"pp collisions {len(meta['pp_collisions'])}")
    out(f"canon not idempotent on {meta['canon_non_idempotent_distinct']} distinct formula(s):")
    fix = {}
    for x in meta["canon_non_idempotent_examples"]:
        out("   ", x)
        parts = x.split("  =canon=>  ")
        if len(parts) == 3:
            fix[parts[1]] = parts[2]
    S["meta"] = meta

    def canonfix(c):
        seen = set()
        while c in fix and c not in seen:
            seen.add(c)
            c = fix[c]
        return c

    for e in entries:
        e["lhs_cfix"] = canonfix(e["lhs_canon"])
        e["rhs_cfix"] = canonfix(e["rhs_canon"])
    for c in frontier:
        c["lhs_cfix"] = canonfix(c["lhs_canon"])
        c["rhs_cfix"] = canonfix(c["rhs_canon"])
    cfix_changed = [e["id"] for e in entries
                    if (e["lhs_cfix"], e["rhs_cfix"]) != (e["lhs_canon"], e["rhs_canon"])]
    out(f"entries whose key changes from CANON to CANONFIX: {len(cfix_changed)} {cfix_changed}")
    S["cfix_changed"] = cfix_changed

    KEYS = (("raw", "lhs", "rhs"), ("canon", "lhs_canon", "rhs_canon"),
            ("canonfix", "lhs_cfix", "rhs_cfix"))

    rho = {r["index"]: r for r in reps if r["family"] == "rho"}
    qrep = {r["index"]: r for r in reps if r["family"] == "q"}
    raw2rep = collections.defaultdict(list)
    canon2rep = collections.defaultdict(list)
    for r in reps:
        tag = ("ρ" if r["family"] == "rho" else "q") + str(r["index"])
        raw2rep[r["formula"]].append(tag)
        canon2rep[r["canon"]].append(tag)
    qset_raw = {r["formula"] for r in qrep.values()}
    rho_raw = {r["formula"] for r in rho.values()}
    for e in entries:
        if e["source"] in ("esc", "frjCert"):
            e["_compound"] = e["lhs"] if e["lhs"] not in qset_raw else e["rhs"]
            e["_partner"] = e["rhs"] if e["_compound"] == e["lhs"] else e["lhs"]

    # ------------------------------------------------------------------
    head("2. SHAPE OF THE DATA")
    src_rel = collections.Counter((e["source"], e["rel"]) for e in entries)
    src_ev = collections.Counter((e["source"], e["ev"], e["engine"] or e["rule"]) for e in entries)
    src_scope = collections.Counter((e["source"], e["scope"], e["scope_size"]) for e in entries)
    out("source x rel:", dict(sorted((f"{s}/{r}", n) for (s, r), n in src_rel.items())))
    out("source x evidence:", dict(sorted((f"{s}/{k}/{g}", n) for (s, k, g), n in src_ev.items())))
    out("source x scope:", dict(sorted((f"{s}/{c}/{z}", n) for (s, c, z), n in src_scope.items())))
    rels = collections.Counter(e["rel"] for e in entries)
    out("relations overall:", dict(rels))
    worlds = collections.Counter(e["worlds"] for e in entries if e["ev"] == "countermodel")
    out("countermodel worlds:", dict(sorted(worlds.items())))
    id_shapes = collections.Counter((e["source"], re.sub(r"\d+", "N", e["id"])) for e in entries)
    out("id shapes:", dict(sorted((f"{s}:{k}", n) for (s, k), n in id_shapes.items())))
    ids = collections.Counter(e["id"] for e in entries)
    dup_ids = {k: v for k, v in ids.items() if v > 1}
    out(f"duplicate ids: {len(dup_ids)} {list(dup_ids)[:10]}")
    sz = [e["lhs_size"] for e in entries] + [e["rhs_size"] for e in entries]
    out(f"formula size (constructor nodes): min {min(sz)}, max {max(sz)}, mean {sum(sz)/len(sz):.1f}")
    # escape decomposition: every compound has all q partners, one direction each
    esc_by = collections.defaultdict(list)
    for e in entries:
        if e["source"] == "esc":
            esc_by[e["_compound"]].append(e)
    incomplete = {c: len(v) for c, v in esc_by.items()
                  if {x["_partner"] for x in v} != qset_raw or len(v) != len(qset_raw)}
    out(f"escape compounds: {len(esc_by)}; with a row for each of the {len(qset_raw)} q partners, "
        f"exactly once: {len(esc_by) - len(incomplete)}; incomplete: {incomplete}")
    # provenance vs certificate: the `worlds` recorded on an escape entry
    # against the size of the inline model its `ok` proof checks
    esc_src = open(os.path.join(repo, "RNDB", "EscEntries.lean"), encoding="utf-8").read()
    w_mismatch, w_seen = [], 0
    for mm in re.finditer(r'escEntry "([^"]+)".*?\s(\d+) \(by decide\)\s*\(fun hd => '
                          r'FinCM\.not_provable_of_check \(M := ⟨(\d+),', esc_src, re.S):
        w_seen += 1
        if mm.group(2) != mm.group(3):
            w_mismatch.append((mm.group(1), int(mm.group(2)), int(mm.group(3))))
    out(f"escape entries whose recorded `worlds` differs from the inline model size: "
        f"{len(w_mismatch)} of {w_seen} parsed {w_mismatch[:5]}")
    S["esc_worlds_mismatch"] = dict(parsed=w_seen, mismatches=w_mismatch)
    S["shape"] = dict(rels=dict(rels), dup_ids=dup_ids, worlds=dict(worlds),
                      id_shapes={f"{s}:{k}": n for (s, k), n in id_shapes.items()},
                      esc_compounds=len(esc_by), esc_incomplete=incomplete)

    # ------------------------------------------------------------------
    head("3. CONTRADICTIONS (must be none)")
    alarms = []
    for keyname, L, R in KEYS:
        pos_pairs = collections.defaultdict(list)
        neg_pairs = collections.defaultdict(list)
        for e in entries:
            k = (e[L], e[R])
            if e["rel"] == "nle":
                neg_pairs[k].append(e["id"])
            else:
                pos_pairs[k].append(e["id"])
                if e["rel"] == "interd":
                    pos_pairs[(k[1], k[0])].append(e["id"])
        for k in neg_pairs:
            if k in pos_pairs:
                alarms.append(dict(key=keyname, kind="positive and nle on the same ordered pair",
                                   lhs=k[0], rhs=k[1], pos=pos_pairs[k], neg=neg_pairs[k]))
    for e in entries:
        if e["rel"] == "nle":
            if e["lhs_cfix"] == e["rhs_cfix"]:
                alarms.append(dict(key="canonfix", kind="nle between canon-equal formulas",
                                   id=e["id"], lhs=e["lhs"], rhs=e["rhs"]))
            if e["lhs_cfix"] == "⊥" or e["rhs_cfix"] == "⊤":
                alarms.append(dict(key="canonfix", kind="nle from ⊥ or into ⊤",
                                   id=e["id"], lhs=e["lhs"], rhs=e["rhs"]))
    uf = UF()
    for e in entries:
        if e["rel"] == "interd":
            uf.union(e["lhs_cfix"], e["rhs_cfix"])
    for e in entries:
        if e["rel"] == "nle" and uf.find(e["lhs_cfix"]) == uf.find(e["rhs_cfix"]):
            alarms.append(dict(key="class", kind="nle inside one interd class",
                               id=e["id"], lhs=e["lhs"], rhs=e["rhs"]))
    # an nle a ⊬ b with a ≡ a', b ≡ b' and a positive a' ⊢ b' is caught by the
    # class test above only for interd; with `le` entries present, close it too:
    le_edges = [(uf.find(e["lhs_cfix"]), uf.find(e["rhs_cfix"])) for e in entries if e["rel"] == "le"]
    if le_edges:
        succ = collections.defaultdict(set)
        for a, b in le_edges:
            succ[a].add(b)
        for e in entries:
            if e["rel"] != "nle":
                continue
            a, b = uf.find(e["lhs_cfix"]), uf.find(e["rhs_cfix"])
            stack, seen = [a], {a}
            while stack:
                x = stack.pop()
                for y in succ[x]:
                    if y not in seen:
                        seen.add(y)
                        stack.append(y)
            if b in seen:
                alarms.append(dict(key="class", kind="nle refuted by a chain of le/interd entries",
                                   id=e["id"], lhs=e["lhs"], rhs=e["rhs"]))
    if alarms:
        out(f"*** ALARM: {len(alarms)} contradiction(s) ***")
        for x in alarms[:20]:
            out("   ", json.dumps(x, ensure_ascii=False))
    else:
        out("none, under RAW, CANON and CANONFIX keys: no ordered pair carries both a positive")
        out("and an nle entry; no nle relates canon-equal formulas, starts at ⊥ or ends at ⊤;")
        out("no nle lies inside one interd class (union-find over all interd entries);")
        out(f"le entries: {len(le_edges)} (so no le-chain test was needed).")
    S["alarms"] = alarms

    # ------------------------------------------------------------------
    head("4. DUPLICATE CLUSTERS")
    dup = {}
    for keyname, L, R in KEYS:
        cl = collections.defaultdict(list)
        for e in entries:
            cl[(e[L], e[R], e["rel"])].append(e)
        multi = {k: v for k, v in cl.items() if len(v) > 1}
        surplus = sum(len(v) - 1 for v in multi.values())
        cross = {k: v for k, v in multi.items() if len({x["source"] for x in v}) > 1}
        intra = {k: v for k, v in multi.items() if len({x["source"] for x in v}) == 1}
        combos = collections.Counter("+".join(sorted({x["source"] for x in v})) for v in multi.values())
        out(f"[{keyname}] distinct (lhs, rhs, rel): {len(cl)}; clusters with >1 entry: {len(multi)} "
            f"(surplus entries {surplus}); cross-source {len(cross)}, intra-source {len(intra)}")
        out(f"   source combinations: {dict(combos)}")
        for k, v in list(multi.items())[:3]:
            out(f"   e.g. {k[0]}  {REL_SYM[k[2]]}  {k[1]}   ids {[x['id'] for x in v]}")
        intra_ex = [[(x["id"], x["lhs"], x["rhs"]) for x in v] for v in intra.values()]
        for v in intra_ex[:6]:
            out(f"   intra-source: {v}")
        un = collections.defaultdict(list)
        for e in entries:
            if e["rel"] == "interd":
                un[frozenset((e[L], e[R]))].append(e["id"])
        out(f"   interd: {sum(1 for e in entries if e['rel'] == 'interd')} entries over "
            f"{len(un)} unordered pairs; pairs with >2 entries: {sum(1 for v in un.values() if len(v) > 2)}")
        dup[keyname] = dict(distinct=len(cl), clusters=len(multi), surplus=surplus,
                            cross=len(cross), intra=len(intra), combos=dict(combos),
                            intra_examples=intra_ex[:30],
                            examples=[dict(rel=k[2], lhs=k[0], rhs=k[1], ids=[x["id"] for x in v])
                                      for k, v in list(multi.items())[:30]],
                            interd_unordered_pairs=len(un))
        if keyname == "canon":
            canon_only = [v for v in multi.values() if len({(x["lhs"], x["rhs"]) for x in v}) > 1]
            out(f"   clusters that merge DIFFERENT raw claims: {len(canon_only)}")
            for v in canon_only[:4]:
                out("     ", [(x["id"], x["lhs"], x["rhs"]) for x in v])
            dup[keyname]["canon_merges_raw"] = len(canon_only)
    S["duplicates"] = dup

    # ------------------------------------------------------------------
    head("5. REFERENTIAL INTEGRITY OF DERIVED ENTRIES")
    byid = {e["id"]: e for e in entries}
    arity = {"symm": 1, "trans": 2}
    ri = dict(derived=0, missing_parent=[], bad_arity=[], parent_not_interd=[],
              shape_mismatch=[], parent_after_child=[])
    for e in entries:
        if e["ev"] != "derived":
            continue
        ri["derived"] += 1
        ps = e["parents"]
        if len(ps) != arity.get(e["rule"], -1):
            ri["bad_arity"].append(e["id"])
        if any(p not in byid for p in ps):
            ri["missing_parent"].append((e["id"], [p for p in ps if p not in byid]))
            continue
        P = [byid[p] for p in ps]
        if any(p["rel"] != "interd" for p in P):
            ri["parent_not_interd"].append(e["id"])
        if any(p["pos"] >= e["pos"] for p in P):
            ri["parent_after_child"].append(e["id"])
        if e["rule"] == "symm" and len(P) == 1:
            ok = (P[0]["lhs"], P[0]["rhs"]) == (e["rhs"], e["lhs"])
        elif e["rule"] == "trans" and len(P) == 2:
            ok = (P[0]["lhs"] == e["lhs"] and P[0]["rhs"] == P[1]["lhs"] and P[1]["rhs"] == e["rhs"])
        else:
            ok = False
        if not ok:
            ri["shape_mismatch"].append(dict(id=e["id"], rule=e["rule"], child=(e["lhs"], e["rhs"]),
                                             parents=[(p["id"], p["lhs"], p["rhs"]) for p in P]))
    symm_children = collections.Counter(e["parents"][0] for e in entries
                                        if e["ev"] == "derived" and e["rule"] == "symm" and e["parents"])
    dict_interd = [e["id"] for e in entries if e["source"] in ("dictR1", "dictR2")]
    ri["dict_without_symm_child"] = [i for i in dict_interd if symm_children[i] == 0]
    ri["dict_with_multiple_symm_children"] = [i for i in dict_interd if symm_children[i] > 1]
    for k, v in ri.items():
        out(f"  {k}: {v if isinstance(v, int) else (len(v), v[:6])}")
    S["referential"] = ri

    # ------------------------------------------------------------------
    head("6. FRONTIER CLAIMS ALREADY SETTLED BY A BANKED ENTRY")
    fr = {}
    for keyname, L, R in KEYS:
        nle_ix = collections.defaultdict(list)
        pos_ix = collections.defaultdict(list)
        for e in entries:
            k = (e[L], e[R])
            if e["rel"] == "nle":
                nle_ix[k].append(e["id"])
            else:
                pos_ix[k].append(e["id"])
                if e["rel"] == "interd":
                    pos_ix[(k[1], k[0])].append(e["id"])
        for lst in sorted({c["list"] for c in frontier} | {"frontierOrder"}):
            cs = [c for c in frontier if c["list"] == lst]
            confirmed, refuted, open_ = [], [], []
            for c in cs:
                k = (c[L], c[R])
                rk = (k[1], k[0])
                if c["rel"] == "nle":
                    if nle_ix.get(k):
                        confirmed.append((c, nle_ix[k]))
                    elif pos_ix.get(k):
                        refuted.append((c, pos_ix[k]))
                    else:
                        open_.append((c, []))
                elif c["rel"] == "le":
                    if pos_ix.get(k):
                        confirmed.append((c, pos_ix[k]))
                    elif nle_ix.get(k):
                        refuted.append((c, nle_ix[k]))
                    else:
                        open_.append((c, []))
                else:  # interd
                    if pos_ix.get(k) and pos_ix.get(rk):
                        confirmed.append((c, sorted(set(pos_ix[k] + pos_ix[rk]))))
                    elif nle_ix.get(k) or nle_ix.get(rk):
                        refuted.append((c, nle_ix.get(k, []) + nle_ix.get(rk, [])))
                    else:
                        open_.append((c, []))
            out(f"[{keyname}] {lst}: {len(cs)} claims; settled AS CLAIMED {len(confirmed)}; "
                f"settled AGAINST {len(refuted)}; not banked {len(open_)}")
            first_src = collections.Counter(byid[ids[0]]["source"] for _, ids in confirmed)
            any_src = collections.Counter("+".join(sorted({byid[i]["source"] for i in ids}))
                                          for _, ids in confirmed)
            if confirmed:
                out(f"     settling sources: {dict(any_src)}")
            for c, ids in confirmed[:2]:
                out(f"     e.g. #{c['index']}  {c['lhs']}  {REL_SYM[c['rel']]}  {c['rhs']}   banked as {ids}")
            for c, ids in refuted:
                out(f"     AGAINST #{c['index']}  {c['lhs']}  {REL_SYM[c['rel']]}?  {c['rhs']}   banked {ids}")
            fr[f"{keyname}:{lst}"] = dict(
                total=len(cs), confirmed=len(confirmed), refuted=len(refuted), open=len(open_),
                settling_sources=dict(any_src), first_source=dict(first_src),
                confirmed_detail=[(c["index"], c["lhs"], c["rel"], c["rhs"], ids) for c, ids in confirmed],
                refuted_detail=[(c["index"], c["lhs"], c["rel"], c["rhs"], ids) for c, ids in refuted])
    rho_pairs = {(e["lhs"], e["rhs"]) for e in entries if e["source"] == "rho"}
    f79_in_rho = [c["index"] for c in frontier
                  if c["list"] == "frontier79" and (c["lhs"], c["rhs"]) in rho_pairs]
    out(f"Frontier79's generation-time check 'none of the 79 among the 185 ρ-refutations': "
        f"{'still holds' if not f79_in_rho else 'FAILS ' + str(f79_in_rho)}")
    esc_at_gen = sorted(c["index"] for c in frontier if c["list"] == "frontier79"
                        and any(byid[i]["source"] == "esc" for i in
                                [e["id"] for e in entries if e["rel"] == "nle"
                                 and (e["lhs"], e["rhs"]) == (c["lhs"], c["rhs"])]))
    out(f"frontier79 members banked by an esc entry (raw key): {len(esc_at_gen)} {esc_at_gen}")
    S["frontier"] = fr
    S["frontier79_in_rho"] = f79_in_rho
    S["frontier79_banked_by_esc"] = esc_at_gen

    # ------------------------------------------------------------------
    head("7. SCOPE (wellScoped)")
    nle_noscope = [e["id"] for e in entries if e["rel"] == "nle" and e["scope"] == "none"]
    not_ws = [e["id"] for e in entries if not e["well_scoped"]]
    out(f"nle entries with scope none: {len(nle_noscope)}; entries with wellScopedB = false: {len(not_ws)}")
    sc = collections.Counter((e["rel"], e["scope"], e["scope_size"]) for e in entries)
    out("rel x scope:", {f"{r}/{s}/{z}": n for (r, s, z), n in sorted(sc.items(), key=str)})
    scope_sets = {"rhoScope": rho_raw, "RNReps.reps": qset_raw}
    sides = collections.Counter()
    for e in entries:
        if e["rel"] == "nle" and e["scope"] in scope_sets:
            s = scope_sets[e["scope"]]
            sides[(e["source"], e["scope"], (e["lhs"] in s) + (e["rhs"] in s))] += 1
    out("nle: how many of the two sides are members of the recorded scope (source/scope/#):",
        {f"{a}/{b}/{c}": n for (a, b, c), n in sorted(sides.items())})
    S["scope"] = dict(nle_noscope=nle_noscope, not_well_scoped=not_ws,
                      rel_scope={f"{r}/{s}/{z}": n for (r, s, z), n in sc.items()},
                      sides_in_scope={f"{a}/{b}/{c}": n for (a, b, c), n in sides.items()})

    # ------------------------------------------------------------------
    head("8. THE ρ-MATRIX: COVERAGE BY BANKED ENTRIES")
    rho_by = {"raw": {r["formula"]: i for i, r in rho.items()},
              "canon": {r["canon"]: i for i, r in rho.items()}}
    out(f"ρ representatives: {len(rho)}; distinct canonical forms among them: {len(rho_by['canon'])}")
    n = len(rho)
    cells = n * (n - 1)
    cover = {}
    for keyname, L, R in KEYS[:2]:
        m = rho_by[keyname]
        cov = {}
        for e in entries:
            if e["rel"] != "nle":
                continue
            i, j = m.get(e[L]), m.get(e[R])
            if i is not None and j is not None:
                cov.setdefault((i, j), []).append(e)
        cover[keyname] = cov
    cov = cover["raw"]
    srcs = collections.Counter("+".join(sorted({x["source"] for x in v})) for v in cov.values())
    scoped = collections.Counter("+".join(sorted({x["scope"] for x in v})) for v in cov.values())
    out(f"directed off-diagonal cells: {cells}")
    out(f"cells with a banked nle: raw {len(cover['raw'])}, canonical {len(cover['canon'])}")
    out(f"   covering sources: {dict(srcs)}")
    out(f"   recorded scope of the covering entries: {dict(scoped)}")
    only_q = sorted(k for k, v in cov.items() if all(x["scope"] != "rhoScope" for x in v))
    out(f"   cells covered ONLY by entries scoped to RNReps.reps: {len(only_q)} "
        f"{['ρ%d⊬ρ%d' % k for k in only_q]}")
    out(f"   cells reached only through canon: {sorted(set(cover['canon']) - set(cover['raw']))}")
    multi_cov = {k: v for k, v in cov.items() if len(v) > 1}
    out(f"   cells banked more than once: {len(multi_cov)}")
    pos_rho = sum(1 for e in entries if e["rel"] != "nle" and e["lhs"] in rho_by["raw"]
                  and e["rhs"] in rho_by["raw"] and e["lhs"] != e["rhs"])
    le_entries = sum(1 for e in entries if e["rel"] == "le")
    out(f"positive entries between two distinct ρ: {pos_rho}; `le` entries in the whole DB: {le_entries}")
    out(f"   => of the {cells} cells the DB holds {len(cov)} (all ⊬); the ⊢ cells are not entries")
    # tools/frjv-sweep-check.py's own reading of the banked ⊬ set (regex over RNDB/*.lean)
    nle_re = set()
    for f in sorted(os.listdir(os.path.join(repo, "RNDB"))):
        if f.endswith(".lean"):
            s = open(os.path.join(repo, "RNDB", f), encoding="utf-8").read()
            for mm in re.finditer(r'\b(sepEntry|nleEntry|frjCertEntry|escEntry)\s+"[^"]*"\s+(\d+)\s+(\d+)', s):
                nle_re.add((int(mm.group(2)), int(mm.group(3))))
    missed = sorted(set(cov) - nle_re)
    out(f"tools/frjv-sweep-check.py regex sees {len(nle_re)} banked ⊬ ρ-cells; it misses "
        f"{len(missed)}: {['ρ%d⊬ρ%d' % k for k in missed]}")
    S["rho_matrix"] = dict(cells=cells, nle_raw=len(cover["raw"]), nle_canon=len(cover["canon"]),
                           sources=dict(srcs), scopes=dict(scoped),
                           only_reps_scoped=[list(k) for k in only_q],
                           multiply_banked=len(multi_cov), positive_rho_entries=pos_rho,
                           le_entries=le_entries, frjv_sweep_check_sees=len(nle_re),
                           frjv_sweep_check_misses=[list(k) for k in missed])

    # ------------------------------------------------------------------
    head("9. FORMULAS IN THE DB THAT ARE NOT ρ OR q REPRESENTATIVES")
    forms = {}
    for e in entries:
        for side in ("lhs", "rhs"):
            forms.setdefault(e[side], e[side + "_cfix"])
    out(f"distinct raw formulas in entries: {len(forms)}; distinct CANONFIX forms: {len(set(forms.values()))}")
    ufr = UF()
    for e in entries:
        if e["rel"] == "interd":
            ufr.union(e["lhs"], e["rhs"])
    for f, c in forms.items():  # canon-equal formulas are interderivable
        ufr.union(f, "§" + c)
    for r in reps:
        ufr.union(r["formula"], "§" + canonfix(r["canon"]))
    cls_reps = collections.defaultdict(set)
    for r in reps:
        cls_reps[ufr.find(r["formula"])].add(("ρ" if r["family"] == "rho" else "q") + str(r["index"]))
    cats = collections.Counter()
    unlinked, linked_q_only = [], []
    for f in forms:
        tags = cls_reps.get(ufr.find(f), set())
        if f in raw2rep:
            cats["a representative (raw)"] += 1
        elif any(t.startswith("ρ") for t in tags):
            cats["linked to a ρ class (canon or interd entries)"] += 1
        elif tags:
            cats["linked only to a q representative without ρ twin"] += 1
            linked_q_only.append((f, sorted(tags)))
        else:
            cats["no link to any representative"] += 1
            unlinked.append(f)
    for k, v in cats.items():
        out(f"   {k}: {v}")
    for f, t in linked_q_only[:6]:
        out(f"     q-only: {f}  ~  {t}")
    occ = collections.defaultdict(set)
    for e in entries:
        for side in ("lhs", "rhs"):
            occ[e[side]].add(e["source"])
    unl_src = collections.Counter("+".join(sorted(occ[f])) for f in unlinked)
    out(f"   unlinked formulas by the sources they occur in: {dict(unl_src)}")
    for f in unlinked[:8]:
        out(f"     {f}")
    esc_cpd = sorted(esc_by)
    esc_rho = {f: sorted(cls_reps.get(ufr.find(f), set())) for f in esc_cpd if cls_reps.get(ufr.find(f))}
    out(f"   escape compounds: {len(esc_cpd)}; of these linked to a representative: {len(esc_rho)}")
    for f, t in esc_rho.items():
        raw_eq = f in raw2rep
        out(f"     {f}  ≡  {t}  ({'syntactically equal' if raw_eq else 'canon-equal'})")
    # q representatives without a ρ twin
    for k, r in sorted(qrep.items()):
        if r["twin"] is None:
            out(f"   q{k} = {r['formula']} has no ρ twin; its DB class contains: "
                f"{sorted(cls_reps.get(ufr.find(r['formula']), set()))}")
    S["formulas"] = dict(distinct_raw=len(forms), distinct_cfix=len(set(forms.values())),
                         categories=dict(cats), unlinked_by_source=dict(unl_src),
                         unlinked=unlinked, linked_q_only=linked_q_only,
                         esc_compounds=len(esc_cpd), esc_linked=esc_rho)

    # ------------------------------------------------------------------
    head("10. IS `canon` A USABLE KEY?")
    res_keys = {}
    for keyname, L, R in KEYS[1:]:
        relsets = collections.defaultdict(set)
        for e in entries:
            relsets[(e[L], e[R])].add(e["rel"])
        mixed = {k: v for k, v in relsets.items() if len(v) > 1}
        interd = [e for e in entries if e["rel"] == "interd"]
        same = [e for e in interd if e[L] == e[R]]
        diff = [e for e in interd if e[L] != e[R]]
        un_all = {frozenset((e[L], e[R])) for e in interd}
        un_diff = {frozenset((e[L], e[R])) for e in diff}
        dict_pairs = [e for e in interd if e["source"] in ("dictR1", "dictR2")]
        dict_same = sum(1 for e in dict_pairs if e[L] == e[R])
        out(f"[{keyname}] (a) ordered pairs carrying more than one relation: {len(mixed)}")
        out(f"[{keyname}] (b) interd entries {len(interd)}: sides equal {len(same)}, "
            f"DIFFERENT {len(diff)} ({100*len(diff)/max(1, len(interd)):.1f}%); "
            f"unordered pairs {len(un_all)}, different {len(un_diff)}; "
            f"dictionary cells closed by the key alone: {dict_same}/{len(dict_pairs)}")
        ufc = UF()
        allc = set()
        for e in entries:
            allc.update((e[L], e[R]))
        for e in interd:
            ufc.union(e[L], e[R])
        classes = collections.defaultdict(set)
        for c in allc:
            classes[ufc.find(c)].add(c)
        multi = {r: v for r, v in classes.items() if len(v) > 1}
        sizes = collections.Counter(len(v) for v in classes.values())
        out(f"[{keyname}] (c) interd classes over key values: {len(classes)} "
            f"({len(multi)} with more than one key value); key values per class: {dict(sorted(sizes.items()))}")
        res_keys[keyname] = dict(mixed=len(mixed), interd=len(interd), equal=len(same),
                                 different=len(diff), unordered=len(un_all),
                                 unordered_different=len(un_diff),
                                 dict_closed=dict_same, dict_total=len(dict_pairs),
                                 classes=len(classes), classes_multi=len(multi),
                                 values_per_class=dict(sizes))
        if keyname == "canon":
            for e in diff[:5]:
                out(f"     {e['id']}: {e['lhs']}  ⊣⊢  {e['rhs']}")
                out(f"         keys {e[L]}   vs   {e[R]}")
            for e in same[:3]:
                out(f"     closed by the key, {e['id']}: {e['lhs']}  ⊣⊢  {e['rhs']}   key {e[L]}")
    raw_by_canon = collections.defaultdict(set)
    for f, c in forms.items():
        raw_by_canon[c].add(f)
    merged = {c: v for c, v in raw_by_canon.items() if len(v) > 1}
    out(f"(d) CANONFIX values shared by >1 raw formula: {len(merged)} "
        f"(raw formulas involved {sum(len(v) for v in merged.values())})")
    for c, v in list(merged.items())[:5]:
        out(f"     {c}  ⟵  {sorted(v)}")
    rep_dups = {c: v for c, v in canon2rep.items() if len(v) > 1 and
                not (len(v) == 2 and v[0].startswith("ρ") != v[1].startswith("ρ"))}
    out(f"(e) two distinct representatives OF ONE FAMILY with one canonical form: {rep_dups or 'none'}")
    res_keys["merged_values"] = len(merged)
    res_keys["merged_raw"] = sum(len(v) for v in merged.values())
    res_keys["rep_canon_collisions"] = rep_dups
    S["keys"] = res_keys

    # ------------------------------------------------------------------
    head("11. IMPORT CLOSURE (static, from the sources)")

    def path_of(mod):
        p = os.path.join(repo, *mod.split(".")) + ".lean"
        return p if os.path.exists(p) else None

    def closure(root):
        seen, stack = set(), [root]
        while stack:
            m = stack.pop()
            if m in seen:
                continue
            p = path_of(m)
            if p is None:
                continue
            seen.add(m)
            with open(p, encoding="utf-8", errors="replace") as fh:
                for line in fh:
                    mm = re.match(r"^\s*import\s+(.+)$", line)
                    if mm:
                        for tok in mm.group(1).split():
                            if tok.startswith("--"):
                                break
                            stack.append(tok)
        return seen

    sorry_cache = {}

    def sorry_tokens(m):
        if m not in sorry_cache:
            b = open(path_of(m), encoding="utf-8", errors="replace").read()
            sorry_cache[m] = len(re.findall(r"\bsorry\b", strip_lean_comments(b)))
        return sorry_cache[m]

    roots = ["RNDB.DB", "RNDB.Types", "RNDB.RhoEntries", "RNDB.DictEntries", "RNDB.Dict2Entries",
             "RNDB.FRJCertEntries", "RNDB.DerivedEntries", "RNDB.EscEntries", "RNDB.Order",
             "RNDB.SepEntries", "RNDB.Frontier79", "RNDB.Examples", "RNDB.Diamond",
             "Rewrite.Canon", "tools.RNDBExport"]
    clos = {}
    for r in roots:
        c = closure(r)
        w = sorted(m for m in c if m.startswith("wip."))
        so = {m: sorry_tokens(m) for m in sorted(c) if sorry_tokens(m)}
        clos[r] = dict(modules=len(c), wip=w, sorry_modules=so)
        out(f"  {r}: {len(c)} repo modules; wip/: {len(w)}; modules with `sorry` in code: {so}")
    out(f"  RNDB.DB wip/ modules: {clos['RNDB.DB']['wip']}")
    out("  (reachability only; whether any ENTRY depends on sorryAx is what the #guard_msgs pins on")
    out("   allEntries check, and the build of RNDB.DB passed them)")
    # who imports each RNDB module (inside the repo)
    importers = collections.defaultdict(list)
    for dp, dns, fns in os.walk(repo):
        dns[:] = [d for d in dns if d not in {".lake", ".git", "_out"} and not d.startswith(".")]
        for fn in fns:
            if fn.endswith(".lean"):
                p = os.path.join(dp, fn)
                mod = os.path.relpath(p, repo)[:-5].replace(os.sep, ".")
                for line in open(p, encoding="utf-8", errors="replace"):
                    mm = re.match(r"^\s*import\s+(RNDB\.\S+)", line)
                    if mm:
                        importers[mm.group(1)].append(mod)
    for m in ("RNDB.Frontier79", "RNDB.Examples", "RNDB.Diamond", "RNDB.DB"):
        out(f"  imported by: {m} <- {sorted(importers.get(m, []))}")
    S["imports"] = dict(closures=clos, importers={k: sorted(v) for k, v in importers.items()})

    # ------------------------------------------------------------------
    head("12. GENERATORS")
    ctor = {"RNDB/RhoEntries.lean": r"nleEntry \\\"rho-|nleEntry \"rho-",
            "RNDB/DictEntries.lean": r"interdEntryR1 \\\"|interdEntryR1 \"",
            "RNDB/Dict2Entries.lean": r"interdEntryR2 \\\"|interdEntryR2 \"",
            "RNDB/FRJCertEntries.lean": r"frjCertEntry \\\"|frjCertEntry \"",
            "RNDB/DerivedEntries.lean": r"symmEntry \\\"|symmEntry \"|transEntry \\\"|transEntry \"",
            "RNDB/EscEntries.lean": r"escEntry \\\"|escEntry \"",
            "RNDB/SepEntries.lean": r"sepEntry \\\"|sepEntry \"",
            "RNDB/Frontier79.lean": r"Rel\.nle, some rhoScope",
            "RNDB/Order.lean": r"ord-000"}
    hits = collections.defaultdict(list)
    for dp, dns, fns in os.walk(repo):
        dns[:] = [d for d in dns if d not in {".lake", ".git", "RNDB", "_out"} and not d.startswith(".")]
        for fn in fns:
            if not fn.endswith((".lean", ".py", ".sh")):
                continue
            p = os.path.join(dp, fn)
            if os.path.basename(p) == "rndb_audit.py":
                continue
            t = open(p, encoding="utf-8", errors="replace").read()
            for f, c in ctor.items():
                for mm in re.finditer(c, t):
                    hits[f].append(f"{os.path.relpath(p, repo)}:{t.count(chr(10), 0, mm.start()) + 1}")
    gens = {}
    for f in ctor:
        txt = open(os.path.join(repo, f), encoding="utf-8").read()
        gens[f] = dict(header_says_generated="GENERATED" in txt,
                       says_regenerate="regenerate" in txt,
                       emitters=sorted(set(hits.get(f, []))))
        out(f"  {f}: header GENERATED {gens[f]['header_says_generated']}, "
            f"'regenerate' {gens[f]['says_regenerate']}; emitters in repo: {gens[f]['emitters']}")
    S["generators"] = gens

    # ------------------------------------------------------------------
    head("13. REPRESENTATIVES AND THE ρ ↔ q CROSS-MAP")
    for i in sorted(rho):
        r = rho[i]
        tw = f"q{r['twin']}" if r["twin"] is not None else "-"
        out(f"  ρ{i:<2} = {r['formula']:<46} twin {tw:<4} canon {r['canon']}")
    for k in sorted(qrep):
        r = qrep[k]
        tw = f"ρ{r['twin']}" if r["twin"] is not None else "-"
        out(f"  q{k:<2} = {r['formula']:<46} twin {tw}")
    S["reps"] = dict(rho={i: dict(formula=r["formula"], canon=r["canon"], twin=r["twin"]) for i, r in rho.items()},
                     q={k: dict(formula=r["formula"], twin=r["twin"]) for k, r in qrep.items()})

    head("14. WORKED EXAMPLES (RNDB/Examples.lean, not in allEntries)")
    for e in examples:
        same = [x["id"] for x in entries if x["lhs"] == e["lhs"] and x["rhs"] == e["rhs"]]
        out(f"  {e['id']} {e['rel']}: {e['lhs']}  {REL_SYM[e['rel']]}  {e['rhs']}   same pair in DB: {same}")

    # ------------------------------------------------------------------
    actual = dict(meta["source_counts"])
    actual["total"] = len(entries)
    actual["derived:symm"] = sum(1 for e in entries if e["source"] == "derived" and e["rule"] == "symm")
    actual["esc:cells"] = len(esc_by)
    actual["frontier79"] = sum(1 for c in frontier if c["list"] == "frontier79")
    actual["frontier79_backed"] = fr["raw:frontier79"]["confirmed"] + fr["raw:frontier79"]["refuted"]
    actual["rho_matrix_nle"] = len(cover["raw"])
    actual["rho_matrix_le_entries"] = le_entries
    actual["rnDict_sorry_tokens"] = sorry_tokens("wip.rnDict") if path_of("wip.rnDict") else None
    S["headers"] = check_headers(repo, actual)
    return S, alarms


# ----------------------------------------------------------------------------
# the gate watch: every check above must FAIL on a planted fault
# ----------------------------------------------------------------------------

def selftest(rows, repo):
    def run(r):
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf):
            S, alarms = analyse(r, repo)
        return S, alarms

    results = []
    base_S, base_alarms = run(copy.deepcopy(rows))
    results.append(("baseline has no alarm", not base_alarms))

    # 1. an nle on the reverse of an interd pair (canon-different sides)
    r = copy.deepcopy(rows)
    d = next(e for e in r["entry"] if e["source"] == "dictR1" and e["lhs_canon"] != e["rhs_canon"])
    bad = dict(d, id="planted-1", rel="nle", source="planted", ev="countermodel",
               engine="finCM", worlds=1, parents=[], rule=None, pos=10 ** 6)
    bad["lhs"], bad["rhs"] = d["rhs"], d["lhs"]
    bad["lhs_canon"], bad["rhs_canon"] = d["rhs_canon"], d["lhs_canon"]
    r["entry"].append(bad)
    _, al = run(r)
    results.append(("planted nle against an interd pair raises an ALARM", bool(al)))

    # 2. an nle between two formulas only linked through a CHAIN of interd entries
    r = copy.deepcopy(rows)
    t = next(e for e in r["entry"] if e["rule"] == "trans")
    p1 = next(e for e in r["entry"] if e["id"] == t["parents"][0])
    bad = dict(p1, id="planted-2", rel="nle", source="planted", ev="countermodel",
               engine="finCM", worlds=1, parents=[], rule=None, pos=10 ** 6)
    bad["lhs"], bad["lhs_canon"] = t["lhs"], t["lhs_canon"]
    bad["rhs"], bad["rhs_canon"] = t["rhs"], t["rhs_canon"]
    r["entry"] = [e for e in r["entry"] if e["id"] != t["id"]] + [bad]
    _, al = run(r)
    results.append(("planted nle inside an interd class (via a chain) raises an ALARM",
                    any(a["kind"] == "nle inside one interd class" for a in al)))

    # 3. a derived entry with a missing parent and wrong arity
    r = copy.deepcopy(rows)
    s = next(e for e in r["entry"] if e["rule"] == "symm")
    s["parents"] = ["no-such-id", "another"]
    S, _ = run(r)
    results.append(("missing parent detected", bool(S["referential"]["missing_parent"])))
    results.append(("bad arity detected", bool(S["referential"]["bad_arity"])))

    # 4. a symm entry whose claim is not the parent's reversed
    r = copy.deepcopy(rows)
    s = next(e for e in r["entry"] if e["rule"] == "symm")
    s["lhs"], s["rhs"] = s["rhs"], s["lhs"]
    S, _ = run(r)
    results.append(("symm shape mismatch detected", bool(S["referential"]["shape_mismatch"])))

    # 5. a frontier claim with no banked entry stays open; one with an entry is stale
    r = copy.deepcopy(rows)
    f0 = next(c for c in r["frontier"] if c["list"] == "frontier79")
    r["entry"] = [e for e in r["entry"] if not (e["rel"] == "nle" and e["lhs"] == f0["lhs"]
                                               and e["rhs"] == f0["rhs"])]
    S, _ = run(r)
    results.append(("unbanked frontier claim reported open",
                    S["frontier"]["raw:frontier79"]["open"] == 1))
    results.append(("banked frontier claims reported stale",
                    base_S["frontier"]["raw:frontier79"]["confirmed"] > 0))

    # 6. a scopeless nle is counted
    r = copy.deepcopy(rows)
    x = next(e for e in r["entry"] if e["rel"] == "nle")
    x["scope"], x["well_scoped"] = "none", False
    S, _ = run(r)
    results.append(("scopeless nle counted", len(S["scope"]["nle_noscope"]) == 1))

    # 7. a duplicate id is counted
    r = copy.deepcopy(rows)
    r["entry"][1]["id"] = r["entry"][0]["id"]
    S, _ = run(r)
    results.append(("duplicate id counted", bool(S["shape"]["dup_ids"])))

    print("SELFTEST (gate watch): each planted fault must be detected")
    ok = True
    for name, passed in results:
        print(f"  [{'ok' if passed else 'MISSED'}] {name}")
        ok &= passed
    return ok


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--export", default="_out/rndb-export.jsonl")
    ap.add_argument("--repo", default=".")
    ap.add_argument("--summary", default="_out/rndb-audit-summary.json")
    ap.add_argument("--selftest", action="store_true")
    a = ap.parse_args()
    rows = load(a.export)
    if a.selftest:
        return 0 if selftest(rows, a.repo) else 3
    S, alarms = analyse(rows, a.repo)
    with open(a.summary, "w", encoding="utf-8") as fh:
        json.dump(S, fh, ensure_ascii=False, indent=1,
                  default=lambda o: sorted(o) if isinstance(o, (set, frozenset)) else str(o))
    out()
    out(f"summary written to {a.summary}")
    return 2 if alarms else 0


if __name__ == "__main__":
    sys.exit(main())
