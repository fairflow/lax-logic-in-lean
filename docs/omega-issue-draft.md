# Draft issue for leanprover/lean4

*Prepared 2026-08-03. Not yet filed. Suggested title below; body follows the
lean4 bug-report template. The MWE is self-contained (no imports) and lives
in this repo as `wip/omegaFix.lean`, where the failure is pinned with
`fail_if_success` so a repaired toolchain will announce itself.*

---

**Title:** `omega` silently drops hypotheses of the form `p → False` (the unfolding of `¬p`)

### Prerequisites

- [x] Checked that the issue reproduces on the latest stable release (4.32.2).
- [x] Searched open and closed issues; found no report of this. Closest
  related: #3848 (`omega` recognises atoms syntactically rather than up to
  definitional equality) — same flavour, different site.
- [x] Minimised: the MWE below has no imports.

### Description

`omega` uses a hypothesis written `¬ p` but silently ignores the same
hypothesis written `p → False`, although `Not p` is *by definition*
`p → False` and the two are definitionally equal at reducible transparency.
The dropped hypothesis leaves no trace: the "possible counterexample"
constraint list in the error message simply does not mention it, so the
failure looks like an incompleteness of the decision procedure rather than a
parsing gap.

Genuine implications between linear atoms **are** consumed, and implications
in the goal are handled, which makes the gap surprising: the one implication
shape that is *not* consumed is the one that is definitionally a negation.

### Steps to reproduce

```lean
-- (1) the ¬ spelling: works
example (a w : Nat) (h : ¬ (w ≤ a)) : a + 1 ≤ w := by omega

-- (2) the definitionally equal spelling: FAILS, h is silently dropped
example (a w : Nat) (h : w ≤ a → False) : a + 1 ≤ w := by omega

-- (3) implications between linear atoms: works
example (a w : Nat) (h : w ≤ a → w ≤ 3) (h2 : w ≤ a) : w ≤ 3 := by omega

-- (4) implication in the goal: works
example (a w : Nat) : w ≤ a → w ≤ a + 1 := by omega
```

Error at (2):

```
error: omega could not prove the goal:
a possible counterexample may satisfy the constraints
  c ≥ 0
  b ≥ 0
  b - c ≥ 0
where
 b := ↑a
 c := ↑w
```

Note the constraint list contains only the goal's negation and
non-negativity; `h` is absent.

### Expected behavior

Either of:

1. (preferred) `omega` treats `p → False` as `¬ p` — e.g. by normalising
   hypotheses with `imp_false` during fact collection, or by matching
   `→ False` alongside `Not`;
2. failing that, the error message reports that a hypothesis was not
   recognised, instead of dropping it silently.

### Actual behavior

The hypothesis is ignored with no diagnostic, and the tactic fails.

### Where this bites in practice

The `p → False` spelling arises whenever `simp only [someDef]` unfolds a
`Prop`-valued function with a `False` branch. In our development
(a mechanised classification over Kripke truth sets), a membership predicate
`memC : Code → Nat → Prop` has `memC .bot w = False`, so hypotheses of the
form `memC c t → memC d t` routinely unfold to `⋯ → False`, and a page of
`omega`-driven case analysis failed for no visible reason. Since `Not` is
*defined* as `a → False`, users have no reason to expect the two spellings
to behave differently.

Workaround we use:

```lean
macro "omega!" : tactic =>
  `(tactic| ((try simp only [imp_false] at *); all_goals omega))
```

### Versions

Reproduced identically on:

- `Lean (version 4.31.0, arm64-apple-darwin24.6.0, commit 68218e876d2a, Release)`
- `Lean (version 4.32.1, arm64-apple-darwin24.6.0, commit f054605aea4b, Release)`
- `Lean (version 4.32.2, arm64-apple-darwin24.6.0, commit f3b06c705e6c, Release)` (latest stable at time of writing)

macOS 15 (Darwin 24.6.0), Apple Silicon.

### Impact

Low severity (workaround is a one-lemma `simp` normalisation) but
confusing to diagnose, because the failure mode is a *silent* drop: the
counterexample report looks like genuine incompleteness. Related to the
general theme of #3848 (`omega` matching syntactically where users expect
definitional transparency).
