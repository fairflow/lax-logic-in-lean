# FRJX toolkit run 1 — pass@1 over the port surface

**Date** 2026-09-01. **Branch** `FRJX`. **Model** Claude Code (Opus 5) in the
seat of a hosted prover, via `prover-toolkit/claude_shim.py`.
**Items** `prover-toolkit/frjx_items.jsonl` — the 8 open ports of
`wip/frjx_ports.lean`, prefix blinded of every already-proved sibling port.
That file is **derived data and is not committed**: it carried absolute paths
to the worktree that generated it, so it was dropped before this record
reached `tooling`. Regenerate it with `extract.py` against
`wip/frjx_ports.lean` on a branch that has it; the numbers below were taken
against the generated copy described here.
**Command**

    harness.py --items prover-toolkit/frjx_items.jsonl --out runs/frjx-pass1.jsonl \
      --model claude-code-opus-5 --url http://127.0.0.1:8088 --now -k 1 \
      --leansearch-url http://localhost:8081

## The denominator

**0 of 8 verified.**  Not 0 of 8 with an excuse: 0 of 8, and the reasons are
below.  Samples: 8 (pass@1; the k=4 arm was NOT run — see "why it stopped").

| lemma | verdict | where it broke |
|---|---|---|
| `gbuInv8'` | lean_error | `tauto` failed at the `⊃`-clause |
| `gbuInv10'` | lean_error | `aesop` made no progress |
| `gbuInv14'` | lean_error | applied `h : ∃ St Th, …` as a function |
| `gbuSuccCirc'` | lean_error | `hz : EvalI D Ω Z` supplied where `D (.irr …)` was wanted |
| `refutedCleanly_at'` | lean_error | unsolved goals, case `h` |
| `refutedCleanly_or'` | lean_error | unsolved goals |
| `refutedCleanly_circ'` | lean_error | unsolved goals |
| `unrefutedBelow_step'` | **rejected on axioms** | compiled, but `[propext, sorryAx, Quot.sound]` |

The last row is the important one: that sample COMPILED and was rejected
because `sorryAx` reached its axioms.  The per-declaration `check` gate the
toolkit added is doing exactly what it was built for, on live data.

## Cost, measured

8 samples, **~65k tokens and ~95 s each** — about 520k tokens for the run.
The k=4 arm would have been ~2.1M.

## Three findings, in order of importance

**1. The corpus excludes the campaign.**  `build_index.py:43` has
`SKIP_DIRS = {…, "wip", …}` and `toolkit.json`'s roots are `LaxLogic`, `FRJ`,
`FRJO`, `BiLax`, `Reject`, `Rewrite`.  Every FRJX target lives in `wip/`, and
so does nearly everything it is built from:

    EvalI, EvalR, RefutedCleanly, Saturated, FSeq, FDerivable,
    Subsumes, UnrefutedBelow, GbuRC, GbuIC          — none indexed
    gAt, gImp, gHat                                 — indexed

So retrieval CANNOT serve this item set, and the `--leansearch-url` ablation
would have measured nothing.  All eight blind samples reported the prompt
insufficient and named the missing definitions; the diagnosis was unanimous
and unprompted.  This is the same shape as the peer session's finding that
recall was capped by off-corpus dependencies — except the off-corpus tree
here is the project's own `wip/`.

**2. The harness could not match a primed Lean name.**  `find_decl_start` in
`verify.py` ended its pattern with `\b`; after `foo'` the next character is a
space, and `'` is a non-word character, so there is no boundary and the match
silently fails.  The first run scored 0/8 with reason `target_decl_absent` —
i.e. it never tested a proof at all.  Fixed here to a negative lookahead
`(?!['\w])`, negative-tested so that `gbuInv1` still does not match
`gbuInv10`.  **This should go upstream to `tooling`.**  Primed names are
ubiquitous in Lean and the benchmark fixtures evidently had none.

**3. Four of the eight items are, as stated, probably unprovable** — and a
blind sample found it.  Reasoning from the argument list alone, the
`gbuInv8'` sample observed that the port takes no `IsLiftClosed` argument,
which the lifted branch of `satExtractI` needs in order to close via
`relift`.  `gbuInv7'`, closed by hand earlier, needed exactly that hypothesis.
The port signatures were generated mechanically and inherited the omission.
Statement failures rather than proof failures, again.

## Search calls, and whether retrieval was used

Search calls made by hand during the campaign: **1**.  Search results used in
a proof that worked: **0**.  Retrieval failures reported by the harness: 0 —
the augmentation ran, it simply had nothing relevant to return (finding 1).

## Why it stopped

The k=4 arm was not run.  With `wip/` outside the corpus the retrieval arm is
structurally incapable of signal, so 24 further samples (~1.5M tokens) would
have bought a second null.  The next run should index `wip/` first, and fix
the four port statements, then repeat these same 8 items — which makes run 1
the control for exactly the question the toolkit README lists as unresolved.
