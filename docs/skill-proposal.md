# Proposal: turn calculus adoption into a Claude Code skill

> **STATUS: this was the design. It is implemented, and the
> implementation — not this document — is what runs.**
>
> The skill lives at `.claude/skills/calculus-adoption/`
> (`SKILL.md`, five `reference/` files, three `templates/`). It is
> registered and active in this repository. This document is kept as the
> record of how the design was arrived at; where the two disagree, the
> skill is right.
>
> **What the implementation changed.**
>
> * **Shape.** This proposal reported "no bundled reference files" as the
>   local convention, inferred from the single existing example. That was
>   wrong: bundled resources are normal practice. `SKILL.md` now carries
>   only judgment — the stage gates, the constraints, what each stage
>   cannot end without — and the depth is loaded on demand, because
>   `SKILL.md` pays a context cost on every trigger.
> * **Three tools now exist that did not when this was written**, each
>   because its absence had cost real time: `#choice_path` /
>   `#axiom_pin` (`Meta/Audit.lean`), `#rules` (`Meta/Rules.lean`), and
>   `tools/paper-skeleton`. The stage table names which to run where, and
>   `reference/tools.md` documents them. This proposal's Stage 0 and
>   Stage 1 are largely automated by `paper-skeleton` as a result.
> * **`reference/result-kinds.md` is new.** This proposal assumed
>   throughout that the results to reproduce are soundness and
>   completeness against a semantics. That is one kind among seven, and
>   cut elimination, termination, interpolation, conservativity and
>   focalisation each need a different encoding and fail differently.
>   That gap was the main thing wrong with the design.
> * **The choice checklist grew**, and one of its claims was corrected:
>   the diagnosis "`simp` pins `Classical.choice`" was wrong. `simp` was
>   the route; the source is Mathlib's `lt_or_eq_of_le`. Also added:
>   `List.argmax_mem`, `List.le_of_mem_argmax` and
>   `List.eq_nil_iff_forall_not_mem` are tainted, and the replacements are
>   in `FRJ/Basic.lean`.
> * **Two new standing rules** the design did not contain: *ask the tool,
>   do not reimplement it* (four instances tabulated in `SKILL.md`), and
>   its corollary, *your own success check can lie* — earned by a
>   generator reporting "0 items unextracted" beside two rows of raw
>   LaTeX.
> * **Placement.** In the repo, not `~/.claude/skills/`, so that it is
>   version controlled and travels with the tools it drives.
>
> The four prohibitions and the exit-criteria table below survive into
> `reference/failure-modes.md` and `SKILL.md` respectively, with five more
> failure modes added from the campaign that followed.


*2026-08-16. The six-step method is already written up in
`docs/calculus-formalisation-method.md`, dated today, after the LJF◯
campaign (succeeded) and the FRJ◯ campaign (failed at step 2). This
proposal neither restates nor contradicts those steps. It adds the two
things they do not yet cover operationally, Stage 0 (finding the papers)
and the plan document, and turns the route into an executable skill with
per-stage exit criteria.*

The six steps: (1) search the literature for a matching calculus;
(2) implement it sorry-free, following the existing informal but rigorous
proofs as closely as possible; (3) prove the existing results, soundness
and completeness being the essential pair; (4) extract efficient
algorithms from the formal proofs, whose termination bounds are routinely
infeasible to run; (5) provide a verification step for discovered proofs
and disproofs; (6) test on the existing corpus, then past its limits.
One-line version: steps 1–3 buy correctness from the literature, steps
4–6 buy performance back.

## The skill's shape

**Local conventions found.** The only skill on this machine is
`~/.claude/skills/email-draft/SKILL.md`: a single `SKILL.md`, YAML
frontmatter carrying exactly `name` and `description`, no bundled
reference files, prose in Markdown, written as instructions with the
observed failure modes named. There is no `.claude/skills/` in the
repository. So the standard shape applies, matching email-draft's.

    ---
    name: calculus-adoption
    description: Adopt a proof system from the literature and mechanise
      it in Lean, end to end: find the paper, plan, implement the rules
      sorry-free, prove the paper's own soundness and completeness,
      extract a runnable procedure, verify what it discovers, test it on
      the corpus. Use when a proof-theoretic capability is missing and
      somebody has already built the calculus for it, or when asked to
      formalise, port or transcribe a calculus, rule table, sequent
      system, tableau system or refutation calculus from a paper.
    ---

**What it loads.** `SKILL.md` carries the stage gates and the standing
constraints, and points at, without duplicating,
`docs/calculus-formalisation-method.md`, `docs/calculus-map.md`
(provenance), `CLAUDE.md` §"Testing for counterexamples", and the two
worked fidelity tables `docs/frj-fidelity.md` and `docs/ljfo-fidelity.md`.
One bundled file earns its place, `reference/fidelity-table-template.md`:
*paper item | Lean name | status (done / PROVED / OPEN / REFUTED)*, plus
a numbered divergence log.

## Stage 0 — find the papers

The six-step note says "state the requirement as a capability, not as a
shape" and "prefer the version with the most detail". Operationally:

1. **Write the requirement as one sentence naming a capability.** The
   disproof campaign's was: *find a refutation calculus that yields a
   procedure for constructing countermodels directly from a possibly
   unprovable sequent.* Not "a rejection calculus" and not "a dual
   sequent calculus": committing to a shape early is what produced the
   labelled dead end.
2. **Search on the capability, and report the architectures that exist,
   not just the first hit.** The 2026-08-13 round is the model: it killed
   Skura-style rejection systems as non-analytic (model search hidden
   inside a side condition), established that no refutation calculus
   exists for any intuitionistic modal logic, and identified FRJ(G) plus
   Fiorentini's RS4 method as the template.
3. **Obtain the source, not the PDF.** Prefer the arXiv LaTeX source: the
   FRJ work used arXiv:1804.06689 (`frj-corr.tex`, 6682 lines), giving
   exact rule tables, exact side conditions, no OCR loss and greppable
   numbering. Journal version over conference version. Record what was
   read in full and what was not.
4. **Always check for an appendix and read it before proceeding.** Page
   limits push proof detail there, and that is where the load-bearing
   side conditions end up: FRJ(G)'s zones and Lemmas 3–5 live in the
   TABLEAUX 2017 appendix. *(Matthew's standing rule, given in this
   session; the repo record shows an appendix used as a source but does
   not state the rule.)*
5. **Note where the paper proves the same theorem twice**, and cost the
   routes. FRJ(G)'s completeness has a journal route through a second
   calculus, a saturated-database layer and a search procedure, and a §6
   route by direct construction on the countermodel. The direct route is
   a fraction of the work and equally published.

## Stage 1 — the plan document, before any Lean

Reviewable without opening any code, and containing:

* the calculus named, the papers, what was read at source;
* **the numbered results to be reproduced**, in the paper's own
  numbering, with scope and non-scope stated explicitly;
* **the fidelity mapping skeleton**: every paper item that will become a
  Lean definition or theorem, with its intended Lean name;
* **the divergence log**, opened empty, with the rule that a divergence
  is recorded when it is made, not afterwards;
* **which existing repo results may be consumed, read-only.** FRJ's plan
  settled this by noting that the paper defines IPL semantically, so no
  in-repo IPC development is consumed at all, and with it goes the risk
  that a borrowed notion means something subtly different.

## Stages 2–6 — implement the existing results before extending them

**The standing rule: implement and verify the published base before
building any extension of it.** The evidence is this session's. `FRJO/`
(the modal extension FRJ◯) begins at commit `8a01cf8`, 2026-08-15 23:00;
the base `FRJ/` at `0045773`, 2026-08-16 12:24, thirteen hours later. In
between, `4730e30` records "ExtractForces (W3b) is REFUTED for worldOK v3
— three certified cells", and `bdb46bd` records "Reconstruction PROVED,
ExtractForces REFUTED, v4 specified". So the extension's completeness was
proved while its soundness was false, twice over (v2's goal conjunct read
a bounded searcher, so budget failure admitted bad nodes; v3 constrained
the stable zone only by membership in the universe, never by closure).
Stepping back to IPC alone produced, in a single day, soundness,
completeness and `frj_iff_not_IPL`, sorry-free.

Two rules follow.

* **Screen or prove soundness first.** Completeness against an
  over-permissive rule table is nearly free, since extra rules only make
  derivation easier. The content of a refutation calculus is in
  soundness, so a completeness theorem obtained before soundness has been
  screened is worth very little.
* **Extension is a separate campaign with its own Stage 0**, starting
  only when the base's fidelity table is complete and its theorems
  pinned.

## Standing constraints to bake in

* **(a) Machine-checked mandate.** PROVED means sorry-free with a pinned
  `#print axioms`; `collectAxioms` is the only sound oracle;
  `native_decide` taints. PROVED, REFUTED and OPEN stay rigidly distinct,
  and a `sorry` means OPEN. The standing trap: a false statement compiles
  the whole stack and passes every axiom pin, because it is a `sorry`.
* **(b) Choice is deprecated for final results**, because the target is a
  decision procedure and choice blocks extraction. A design constraint,
  not a property to report afterwards. The reusable checklist item from
  this session: **Mathlib's `Finset` union, erase and image are
  choice-tainted at the definition level** (`Finset.instUnion`,
  `Finset.erase`, `Finset.image`, `Multiset.ndunion` each report
  `Classical.choice`), so a term that merely mentions `s ∪ t` on a
  `Finset` carries choice however it is proved; only `Finset.filter` is
  clean. The `List` API is axiom-free at definition level (`List.union`,
  `List.inter`, `List.filter`, `List.map`, `List.flatMap`,
  `List.finRange`, `List.instMembership`), with `List.dedup` and
  `List.erase` the exceptions to avoid. `tauto` reasons classically; so
  do `choose` and `Nonempty.some`, so an existence proof of a derivation
  must become a construction returning one. Two structural consequences:
  shape predicates become `Bool`, and a finite model carries a
  constructive enumeration rather than a `Finite` instance, since
  `Fintype.ofFinite` costs choice.
* **(c) Counterexample-first.** `CLAUDE.md`'s testing discipline runs on
  the *statements* before any proof is scoped: corpus replay, boundary
  cells, frontier extension, branch coverage; normalise through
  `Rewrite.simplifyWith Rewrite.fullSetC` first; three-valued verdicts,
  `fail` only on a certificate. Three certified cells refuted FRJ◯'s
  soundness in minutes; that screen belonged before the proof effort.
* **(d) Fidelity.** Transcribe clause by clause from the original. If a
  rule cannot cite a line of the original, that rule is invented. The
  paper's definitions are definitions here and its lemmas are theorems
  here. Record every divergence as a divergence.

## Exit criteria and banking, per stage

| Stage | Exit criterion | Banked |
|---|---|---|
| 0 Literature | Requirement sentence fixed; source obtained in full, appendices included; architectures reported | Plan document, commit + push |
| 1 Plan | Numbered results, scope, fidelity skeleton, divergence log, read-only decision | Reviewed by Matthew before any Lean |
| 2 Implement | Indexed inductive family, one constructor per rule, indices the sequent; zero sorries | Fidelity rows marked `done`; commit + push |
| 3 Results | Soundness screened, then soundness and completeness proved, `#print axioms` transcribed verbatim | Dated section in the fidelity document; push |
| 4 Extract | A searcher that runs, complexity understood, separate from the theorem | Timings recorded |
| 5 Verify | Decidable checker with a soundness theorem; kernel exemplars replay by `decide` | Pins transcribed |
| 6 Test | Corpus replayed; comparison against the incumbent engine; named frontier | Dated retrospective in `HANDOFF.md` |

A stage does not end on a green build. It ends when its deliverable is
written down and pushed, because that is what the next session reads.

## What the skill must not do

Four failure modes observed in this session, stated as prohibitions.

1. **Do not extend before the base is verified.** FRJ◯ before FRJ, above.
2. **Do not transcribe a rule table from the figure alone.** The prose
   carries the side conditions and the proof-search restrictions, and
   these are not interchangeable: FRJ(G)'s PS1–PS4 are search
   restrictions, so completeness does not need the paper's minimal `Λ`
   or maximal `Θ`, while the rank bounds of Lemma 6.4 serve minimality
   and are out of scope. Neither fact is visible in the figure. Equally
   binding: **do not formalise from an in-repo paraphrase.** FRJ◯'s rule
   table came from `docs/frj-lifting.md`, an orientation summary, and its
   `world` rule corresponded to no published calculus.
3. **Do not bundle part of a conclusion into a definition as a field.**
   An earlier FRJ design carried `forces_lhs` as an invariant of the
   model construction, but `forces_lhs` *is* Lemma 3.9(i). That is a
   restructuring of the proof, not the proof, and it was removed
   (`777ffa6`). The same test catches a certificate format wearing the
   word "calculus": a plain tree plus an external validity checker cannot
   be inducted on, and its soundness lives outside the data.
4. **Do not treat choice as something to report in the axiom pin.** It is
   a constraint to design against from the first definition: the fix is a
   substitution at definition level, and for completeness a redesign
   making the construction Type-valued.
