---
name: calculus-adoption
description: Adopt a proof system from the literature and mechanise it in Lean end to end — find the paper, plan, transcribe the rules sorry-free, prove the paper's own results, extract a runnable procedure, verify what it finds, test it on a corpus. Use when a proof-theoretic capability is missing and somebody has already built the calculus for it, or when asked to formalise, port, transcribe or extend a calculus, rule table, sequent system, tableau system, natural-deduction system or refutation calculus from a paper.
---

# Adopting a calculus from the literature

Steps 0–3 buy correctness from the literature. Steps 4–6 buy performance
back. Do not reorder them, and do not start step 5 of an extension before
step 3 of its base is finished — that inversion is what produced an
unsound calculus in this repo, described in `reference/failure-modes.md`.

## The governing habit

**Ask the tool; do not reimplement it.** Every avoidable hour in the
campaign this skill is distilled from went on rebuilding something that
was already installed:

| Wanted | Wrong instinct | Right answer |
|---|---|---|
| a paper's item numbers | simulate LaTeX's counters | compile it; read the `.aux` |
| a statement's text | parse the source | read the compiled PDF |
| where an axiom enters | guess from the proof | `#choice_path` |
| whether a rule matches the paper | read the Lean and squint | `#rules` |
| whether a judgment is slimed | eyeball the constructors | `#deslime` |

And the corollary: **your own success check can lie.** A run reporting
"0 items unextracted" sat beside two rows of raw LaTeX, because the check
counted a marker string instead of inspecting the cells. Look at the
output as a reader would, or get a human to.

## Stages

| | Do | Tool | Cannot end until |
|---|---|---|---|
| **0** | Find the paper. State the requirement as a *capability*, not a shape. Get the source, not the PDF. **Read the appendix** — page limits push load-bearing detail there. | `tools/paper-skeleton` | the architectures that exist are reported, not just the first hit |
| **1** | The plan document. Numbered results to reproduce, scope and non-scope, fidelity skeleton, empty divergence log, which existing repo results may be consumed read-only. | `paper-skeleton -o plan` + `templates/plan.md` | **Matthew has reviewed it.** No Lean before this. |
| **2** | Transcribe the rules: one indexed inductive family, one constructor per published rule, side conditions as fields, indices the sequent. **No computed index in any conclusion.** | `#rules` vs the paper's figure; `#deslime` | every constructor cites a line of the original, and `#deslime` reports 0 |
| **3** | Prove the paper's results — **screen soundness before proving completeness** (see below). | `#choice_path`, `#axiom_pin` | sorry-free, pins `#guard_msgs`-guarded in an `Audit.lean` |
| **4** | Extract the procedure. The proofs' termination bounds are routinely unrunnable and are not needed to search. | | a searcher that runs, timed |
| **5** | A decidable checker for what it finds, with a soundness theorem. | | kernel exemplars replay by `decide` |
| **6** | Replay the corpus; then push past it. | | results and the named frontier recorded |

A stage ends when its deliverable is **written down and pushed**, not when
the build goes green: the next session reads the document, not the build.

## Five constraints, always

1. **Machine-checked.** PROVED means sorry-free with a pinned
   `#print axioms`. `collectAxioms` is the only sound oracle;
   `native_decide` taints. PROVED / REFUTED / OPEN stay rigidly distinct,
   and a `sorry` means OPEN. Trap: *a false statement compiles the whole
   stack and passes every pin*, because it is a `sorry`.
2. **Choice-free** — the target is a decision procedure, and choice blocks
   extraction. A design constraint from the first definition, not a
   property to report afterwards. → `reference/choice-free.md`
3. **Counterexample-first.** Screen the *statements* before scoping any
   proof. → `reference/counterexample-first.md`
4. **Fidelity.** Transcribe clause by clause. A rule that cannot cite a
   line of the original is invented. Record every divergence *when you
   make it*. → `templates/fidelity.md`
5. **Slime-free** — no computed index in a constructor's return type.
   Applies to *every* Lean development, not just calculi. Fix it at
   transcription time; retrofitting means redoing every proof over the
   family. Slime does not make a development unsound — it makes the
   *statements* bend to whatever can be case-analysed, which is worse,
   because a green build with clean pins cannot show it.
   → `reference/green-slime.md`

## Screen soundness before proving completeness

Completeness against an over-permissive rule table is nearly free — extra
rules only make derivation easier. The content of a calculus is in
soundness. A completeness theorem obtained before soundness was screened
is worth very little, and in this repo one was: three certified cells
refuted the soundness of a calculus whose completeness had already been
proved.

## Before step 2, decide what kind of result you are reproducing

Soundness-and-completeness-against-a-semantics is *one* possibility, and
assuming it is the only one is this skill's known blind spot. Cut
elimination, termination, interpolation, conservativity and focalisation
each need a different encoding and each fail differently.
→ **`reference/result-kinds.md`**

## Reference

* `reference/tools.md` — the three tools, and exactly when to run each
* `reference/result-kinds.md` — result-kind triage, per-kind pitfalls
* `reference/green-slime.md` — computed indices, why they bend statements
* `reference/choice-free.md` — the checklist, and how to bisect
* `reference/counterexample-first.md` — screening statements
* `reference/failure-modes.md` — what went wrong before, and why
* `templates/` — plan, fidelity table, `Audit.lean`

Background, not needed to run the stages: `docs/calculus-formalisation-method.md`
is the original six-step note this skill operationalises, and
`docs/why-chain.md` records the goal chain a campaign like this sits in —
worth reading if it is ever unclear why a local task exists.

## Tools live in this repository

`Meta/Audit.lean`, `Meta/Rules.lean` and `Meta/Deslime.lean` import
nothing but `Lean`, so they can be copied into any Lean project unchanged
— and `#deslime` is worth copying even where no calculus is involved;
`tools/paper-skeleton/paper_skeleton.py` needs only the standard library,
plus `pdflatex` and `pdftotext` on the path. To use this skill outside
`lax-logic-in-lean`, copy those four and adjust the paths in
`reference/tools.md`.
