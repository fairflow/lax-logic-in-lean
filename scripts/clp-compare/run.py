#!/usr/bin/env python3
"""The CLP paper's comparison with SWI-Prolog (Section 12): the mortgage program.

    scripts/clp-compare/run.py OUT.jsonl LAYER [D ...]

LAYER is one of
  info     machine and versions
  swi      SWI-Prolog clpq:      swipl scripts/clp-compare/mortgage.pl D 11
  lean     compiled Lean:        .lake/build/bin/clpcompare time D REPS
  kernel   kernel checks:        clpcompare emit D, then `lake env lean` on the
           files it writes (answerK's verdict; the arithmetic, outside lean-certify),
           reading the profiler's "type checking took" lines; repeated KREPS times
Every run is bounded by gtimeout; one run at a time; each result is appended
to OUT.jsonl as one JSON line.  Build first: `lake build clpcompare` (the build
is not timed).  Run from the repository root.

Records written after 2026-10-17 23:30 also carry, for lean and kernel, the
process's
wall time and `max_rss_so_far_bytes`, the largest resident set of any process
this invocation has run so far (getrusage of the children); run one D per
invocation for a per-run figure.
"""
import json, os, re, resource, subprocess, sys, time

OUT, LAYER, DS = sys.argv[1], sys.argv[2], [int(x) for x in sys.argv[3:]]
BIN = ".lake/build/bin/clpcompare"
KDIR = "_out/clp-compare-kernel"


def emit(rec):
    rec["recorded"] = time.strftime("%Y-%m-%d %H:%M:%S %Z")
    with open(OUT, "a", encoding="utf-8") as f:
        f.write(json.dumps(rec) + "\n")
    print(json.dumps(rec)[:300], flush=True)


def run(cmd, limit):
    t0 = time.monotonic()
    r = subprocess.run(["gtimeout", str(limit)] + cmd, capture_output=True, text=True)
    return r, time.monotonic() - t0


def max_rss():
    return resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss  # bytes on macOS


def lean_reps(d):
    return 5 if d <= 240 else (3 if d <= 480 else 1)


def kernel_reps(d):
    return 3 if d <= 120 else 1


def ms_of(s):
    m = re.match(r"([\d.]+)(ms|s)", s)
    return float(m.group(1)) * (1 if m.group(2) == "ms" else 1000)


if LAYER == "info":
    def sh(*c):
        return subprocess.run(list(c), capture_output=True, text=True).stdout.strip()
    emit({"layer": "info", "cpu": sh("sysctl", "-n", "machdep.cpu.brand_string"),
          "cores": sh("sysctl", "-n", "hw.ncpu"), "memory_bytes": sh("sysctl", "-n", "hw.memsize"),
          "os": sh("sw_vers", "-productVersion"), "lean": sh("lean", "--version"),
          "swipl": sh("swipl", "--version"), "git": sh("git", "rev-parse", "--short", "HEAD")})
elif LAYER == "swi":
    for d in DS:
        r, wall = run(["swipl", "scripts/clp-compare/mortgage.pl", str(d), "11"], 600)
        if r.returncode == 0:
            rec = json.loads(r.stdout.strip().splitlines()[-1])
            rec["layer"] = "swi"
            emit(rec)
        else:
            emit({"layer": "swi", "D": d, "error": "exit %d" % r.returncode, "wall_s": wall})
elif LAYER == "lean":
    for d in DS:
        reps = lean_reps(d)
        r, wall = run([BIN, "time", str(d), str(reps)], 3600)
        if r.returncode == 0:
            rec = json.loads(r.stdout.strip().splitlines()[-1])
            rec["layer"] = "lean"
            rec["wall_s"] = round(wall, 2)
            rec["max_rss_so_far_bytes"] = max_rss()
            emit(rec)
        else:
            emit({"layer": "lean", "D": d, "error": "exit %d (124 = timeout)" % r.returncode, "wall_s": wall,
                  "max_rss_so_far_bytes": max_rss()})
elif LAYER == "kernel":
    os.makedirs(KDIR, exist_ok=True)
    for d in DS:
        r, _ = run([BIN, "emit", str(d), KDIR], 3600)
        if r.returncode != 0:
            emit({"layer": "kernel", "D": d, "error": "emit failed"})
            continue
        for which, fn in (("answerK", "%d.lean" % d), ("arith", "%d_arith.lean" % d)):
            times, errs = [], []
            for _ in range(kernel_reps(d)):
                r, wall = run(["lake", "env", "lean", os.path.join(KDIR, fn)], 3600)
                tc = [ms_of(x) for x in re.findall(r"type checking took ([\d.]+(?:ms|s))", r.stdout)]
                if r.returncode != 0 or not tc:
                    errs.append("exit %d (124 = timeout) after %.0f s: %s" % (r.returncode, wall, r.stdout[-300:] + r.stderr[-300:]))
                    break
                ax = re.findall(r"depends on axioms: \[([^\]]*)\]", r.stdout)
                times.append({"type_checking_ms": tc, "total_ms": sum(tc), "wall_s": round(wall, 2), "axioms": ax,
                              "max_rss_so_far_bytes": max_rss()})
            rec = {"layer": "kernel", "check": which, "D": d, "runs": times}
            if times:
                tot = sorted(t["total_ms"] for t in times)
                rec["median_ms"] = tot[len(tot) // 2]
            if errs:
                rec["error"] = errs[0]
            emit(rec)
else:
    sys.exit(__doc__)
