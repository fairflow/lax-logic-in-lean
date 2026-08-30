# Challenge set

Five proved theorems from the development, re-stated with `sorry`. Generated
by `prover-toolkit/challenge.py`, which applies the acceptance filters of
`docs/toolkit-test-design.md` §4 rather than truncating blindly.

**Do not consult the original proof before attempting one.** Provenance is in
`../challenge-manifest.json`, which deliberately holds no ground-truth proofs.

## What the filters guarantee

| filter | what it rules out |
|---|---|
| **external citation** | a target whose proof and statement need nothing the challenge file already contains — it would test reading, not retrieval |
| **no visible twin** | a target whose proof is near-identical to a sibling already proved above the cut. This caught `conservativity`, whose twin `conservativity_prop` sat proved 60 lines above it, at 0.92 overlap |
| **one target per source file** | two prefix-truncated targets from one file always leak: the later one's prefix contains the earlier one's proof |
| **compiles** | every file elaborates with zero errors and exactly one `sorry`, checked at generation |
| **blind header** | no source file, no source line, no proof length, no difficulty |

Regenerate with:

```bash
python3 prover-toolkit/challenge.py report          # verdicts, no files written
python3 prover-toolkit/challenge.py build -o LaxLogic/ToolkitTest/Challenge -n 7
```

## What they do not guarantee

The set is still **prefix-truncated**, so each file is the source module up to
the target. That is better than the retired set but not clean: everything the
original author had in scope is still there, and only the *cross-file*
dependency is guaranteed absent. `subHeadOut.lean` shows the cost plainly at
2736 lines — a challenge file that large is not something a reader can hold.

Hole-punching (proposal §4) is what removes both problems: it would let the
challenge file be four lines, and would lift the one-target-per-file rule.
It is not built.

`FRJ/Erase.lean` contributes nothing here. Its targets pass the content
filters and then fail to compile, because `FRJ/` is not present on this
branch — the compile filter catches it, which is what it is for.

## The retired set

`../Solved/` holds the first four challenge files with the proofs that closed
them (2026-08-30). They are kept as a record and are **not** a benchmark: that
set was contaminated by construction, `conservativity_prop`'s answer is
written out inside `Solved/conservativity.lean`, and three of the four needed
nothing their own file did not already contain. `conservativity_prop` is on
`challenge.py`'s deny-list for exactly that reason.
