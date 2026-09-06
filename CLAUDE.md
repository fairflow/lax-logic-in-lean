# lax-logic-in-lean — instructions for Claude Code

Keep this file SHORT and stable. Detail lives in `HANDOFF.md` (standing
handover, append dated §s, never rewrite), `docs/next-session.md` (live
threads), `docs/calculus-map.md` (THE provenance reference: read it before
asserting which proof system a result belongs to), `TOOLS.md` (the tool
register, rule 4) and `METHOD.md` (the conjecture → statement → test →
proof pipeline, rule 7).

## Core rules

1. **Machine-checked mandate.** PROVED = sorry-free in Lean with a pinned
   axiom set (`#axioms_within`, built on `collectAxioms`, the only sound
   oracle; `native_decide` taints; pins in `docs/pins.md`). Everything
   else is REFUTED (kernel-checked countermodel) or OPEN; keep the three
   rigidly distinct. A `sorry` ASSERTS: an open case is a typed obligation
   passed as a parameter, never a sorried theorem; `sorry` bodies only in
   `wip/` blueprint files by explicit direction.
2. **Register.** Standard proof-theoretic language; lemmas as displayed
   formulas; no invented jargon.
3. **The reference set is R.** The open-ended ρ-catalogue is the only
   reference set for classes, tables and presentation; a cell outside
   every known class is written ∉R.
4. **Tools.** `TOOLS.md` is the register of the recommended tools, each
   with a version cell; consult it before reaching for one and update it
   in the same commit as any behavioural change. Never drive discovery
   through the decidability theorem (`decideFuel`): its bounds are
   infeasible.
5. **Worktrees and branches.** Fresh worktree: `cp -Rc <repo-root>/.lake
   .lake` first. Never remove a worktree to tidy up. `claude/…` branches
   are LOCAL ONLY, never pushed; a campaign pushes with
   `scripts/campaign-push.sh <branch>` (explicit refspec; the pre-push
   hook in `scripts/hooks/` enforces it, install with
   `scripts/install-hooks.sh`).
6. **Delivery.** Matthew cannot open worktree paths, often not repo
   paths: inline short content in full. Every document delivered is
   tracked in git and pushed. Publish it as an Artifact ONLY if the same
   document is tracked in git; otherwise deliver a link to the pushed
   file, with a reminder to pull before viewing.
7. **Proof requests** follow `METHOD.md`: formal statement first; a
   refutation stage by rule 9; only a surviving statement gets a proof
   build; a disproof is a result and starts the next refinement cycle.
8. **Fragment first.** Every result of a modal route is proved for the
   ◯-free fragment FIRST (the IPC instance, where the theorem is textbook
   and design faults show at a tenth of the cost), then for PLL.
9. **No brute-force refutation campaigns.** A refutation stage is
   answered from the structure of the rules with a few DESIGNED witness
   cells (two or three per case), never by enumerating a formula space or
   replaying a corpus against a new design. Extensional sweeps exist only
   for cell-level campaigns over a statement already fixed (the tables
   and databases), per `METHOD.md` §2.

## Discipline

- Verdicts are three-valued, `pass`/`fail`/`flag`; `fail` only on a
  certificate; a `flag` is re-run at a raised budget, never dropped.
- Never build a simpset or table from an unproved cell (`RwRule.ok`, the
  DB's `ok`; keep their pins).
- Never ship a gate you have not watched fail.
- Every run is bounded: exec the built binary under a deadline, never
  `lake exe`; no unbounded waits; report every skip and cap. Builds of
  the family module cost 25 minutes: test bodies on an `unsafe` copy and
  edges on the bench before paying for one.
