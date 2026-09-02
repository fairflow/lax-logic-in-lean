# FRJX toolkit run 2 — the same 8 items, against a corpus that covers them

Run 1 is the control (`docs/frjx-toolkit-run-1.md`).  The only things that
changed: `wip/` is now indexed, sorried declarations are dropped from the
corpus, the campaign's own files moved to the unindexed `wipx/`, and all 8
port statements gained the `IsLiftClosed` hypothesis a blind sample found
missing.  Same items, same k=1, same harness, same verifier.

|  | run 1 | run 2 |
|---|---|---|
| corpus entries | 4 220 | 13 433 |
| FRJX dependencies covered | 3 of 13 | 13 of 13 |
| prompt size | 5.7k – 16.6k chars | 5.3k – 6.1k chars |
| retrieved declarations USED | **0 of 8 samples** | **8 of 8 samples** |
| verified | **0 / 8** | **0 / 8** |
| failure character | scattered | uniform |
| tokens | ~520k | ~527k |

## The result: the score did not move, the failure did

Run 1 failed eight different ways — `tauto` failed, `aesop` made no
progress, unsolved goals, a `∃` applied as a function, and one proof that
elaborated and was rejected because `sorryAx` reached its axioms.  That is
what flailing looks like.

Run 2 failed eight times in the SAME way: every sample located the port's one
real obstruction and broke there.  Five of the eight lean errors name the
mismatch explicitly —

    hsat : SaturatedOver (LiftClosure G) D    where    Saturated G D    is wanted

— and every one of the eight reported, unprompted, the same diagnosis: the
extraction half of `Saturated` needs `D s → FDerivable G s`, while `hsat.1`
yields only `D s → LiftClosure G s`, and *that gap at irregular rows is the
content of the port*.  One sample re-derived this campaign's own screening
theorem `not_saturated_liftClosed` from signatures alone, observing that
`(Lift)` adds exactly the irregular rows `Saturated` forbids.

So: **retrieval bought diagnosis, not completion.**  On this item set it
moved every sample from "I do not know what this is about" to "I know
exactly which step I cannot take, and why".  That is a real effect and the
run measures it; it is not the effect a pass@k number would show.

## Why completion was structurally out of reach

The index stores `name, short, kind, signature, docstring, module, file,
line` — **no proof bodies**.  A PORT task is precisely one whose answer is
the original's *proof* with two substitutions.  Signature-level retrieval
cannot supply that, however complete the coverage.  Every sample said so:
"the prompt supplies only the statement of `gbuInv8`, not its body".

That is the sharpest finding of the two runs, and it is actionable: for
port-like work the corpus would have to carry bodies, or the harness would
have to fetch the twin's source.  Neither is a large change; both are
decisions for whoever owns `tooling`.

## Search-call accounting, as asked

Hand `search` calls across the campaign: **1** (run 1).  Search results used
in a proof that WORKED: **0**.  Retrieved declarations used in an attempt:
0 of 8 samples in run 1, **8 of 8 in run 2**.  Harness-reported retrieval
failures: 0 in both.

## Fixes made to the toolkit along the way

1. `verify.py` — `find_decl_start` ended with `\b`, so it could not match a
   Lean name ending in a prime; run 1 first scored 0/8 as
   `target_decl_absent`, never testing a proof.  Fixed to a negative
   lookahead, negative-tested against `gbuInv1` vs `gbuInv10`.
2. `build_index.py` — no `sorry` filter existed and the index records no
   proved/sorried flag, so 25 sorried declarations (20 in `wip/`) were
   indexed indistinguishably from proved ones.  Dropped at harvest, count
   reported.  The filter strips comments first, so a proved lemma whose
   docstring says "sorry-free" is not lost.
3. `claude_shim.py` — new: an OpenAI-compatible endpoint whose model is
   Claude Code, with hard caps on requests and bytes plus a killswitch, so a
   runaway cannot spend.

Items 1 and 2 should go upstream to `tooling`.

## Honesty caveats

* Samples came from subagents INSTRUCTED to use no tool beyond reading their
  prompt and writing their answer; each declared compliance, but the sandbox
  did not enforce it.
* k=1, not k=4.  The k=4 arm was not run: with the failure this uniform, three
  more samples per item would buy the same diagnosis three more times.
* `wip/frjx.lean` (an older saturation probe) shares a name with this
  campaign.  Not a leak — it is unrelated — but a rename would avoid trouble.
