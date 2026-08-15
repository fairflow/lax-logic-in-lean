# lax-logic-in-lean — instructions for Claude Code

Created 2026-08-11 (no repo CLAUDE.md existed before this). Keep this
file SHORT: project detail lives in `HANDOFF.md` (standing handover,
append dated §s, never rewrite), `docs/next-session.md` (the live
threads), `docs/calculus-map.md` (**the** provenance reference — read it
before asserting which proof system a result belongs to).

## Core rules

1. **Machine-checked mandate.** A claim is PROVED only when it is
   sorry-free in Lean with a pinned `#print axioms` (the only sound
   oracle is `collectAxioms`; `native_decide` taints). Everything else
   is REFUTED (kernel-checked countermodel) or OPEN — keep the three
   distinct. UI for PLL is OPEN.
2. **Register.** Standard proof-theoretic language only; state lemmas as
   displayed formulas, not invented jargon.
3. **Search engines.** All proof/countermodel discovery runs on the
   certificate engines (`PLLND.Search.prove?Bounded` / `refute?` —
   untrusted-but-safe, discover-then-pin). NEVER drive discovery through
   the decidability theorem (`decideFuel`): its fuel bounds are
   infeasible and it will hang. Since 2026-08-15 there is also the
   TWO-SIDED engine (`lean_exe twosided`; certified layer
   `wip/ljfo_link.lean`): `TwoSidedLink.searchProves` proves via LJF◯
   focused search (sound AND complete for PLL, choice-free) and
   `Reject.certifies` refutes via Built-tree countermodels — on the
   closed corpus it settles proofs ~10³× cheaper than the G4c oracle
   and its certificates are kernel-`decide`-checkable. Prefer it for
   PLL sequent questions; the G4c engines remain the tool for
   premise-loaded (e.g. PCLL/`DerivU`) work.
4. **Worktrees.** Before building in a fresh Claude worktree:
   `cp -Rc <repo-root>/.lake .lake` (APFS clone). Never remove a
   worktree to tidy up.
5. **Delivery.** Matthew cannot open worktree paths (and often not repo
   paths) from the session UI: inline short content in full; publish
   documents as Artifacts; `open <path>` commands for local HTML.

## Testing for counterexamples

Statement failures are a testing problem, not a proving problem — every
definitional defect in this development was refutable by a small
countermodel *before* a proof build could fail opaquely. So: **every
quantified candidate statement gets an extensional attack before a proof
build is scoped**, and each attack covers four directions, in order of
observed yield:

1. **Corpus replay.** Translate the repo's own hard instances into the
   new statement's cells first: the G4iLL blocker
   (`◯((◯p→r)→◯p), ◯p→r ⇒ r`), the g4ill gap sequent, the UI-room
   refuters, the φ★/φ♦ escalation ladder. These carry known duplication/
   financing content that random and degenerate cells miss.
2. **Boundary cells.** The degenerate end of every axis — empty
   contexts, `⊥`, the eliminated atom `p` itself and p-carrying twins of
   each p-free shape, and every NO-CASE corner of the definition (a
   clause family with a missing row is a prime defect site).
3. **Frontier extension.** One step beyond every passing stratum:
   size+1, nesting depth+1, a second interacting member (e.g. two modal
   implications), position permutations. Never re-run only the strata
   that passed last time; the standing rule is that each round's residue
   shape defines the next stratum, run before any proof is scoped.
4. **Branch coverage** (catpart-style category partition): every match
   arm of the definition under test is exercised by at least one
   admissible cell. Pairwise interaction is not enough — the round-9
   defect needed a 3-way interaction (empty context × untied fuel ×
   missing frame).

**Normalise before you search (standing, 2026-08-14).** Every fresh
probe pipes its cells through the CERTIFIED simpset first:

    Rewrite.simplifyWith Rewrite.fullSetC fuel φ

237 rules — 236 kernel-checked cells of the dictionary operation table
(`wip/rnDict.lean`) plus the modal laws. **Use `simplifyWith` against
`fullSetC`, not `simplify`/`norm` and not `fullSet`**: `fullSetC` is
the canonicalised set, computed once, and the rules must be
canonicalised or the canonicaliser sorts goals out of their reach —
that mistake cost a factor of five and was caught only by a control
(`docs/rn-dictionary-status.md`). Correctness is UNCONDITIONAL either
way (`simplifyWith_interd`), so this is a question of effectiveness,
never of soundness.

Measured (`lean_exe rwscreen`): on 330 flat cells, `norm` alone
rewrites 13% for a 6% crank cut, while the pipeline rewrites **89% for
34%**, collapsing 319 distinct forms to **28**. On a NESTED corpus
(3,996 ∧/∨ trees, both associations and both argument orders) the
collapse is **3,996 → 25 distinct forms** — against a floor of 15, the
number of dictionary classes — with crank down 40%. That collapse is
the payoff for a probe: far fewer distinct cells to attack, and cache
hits across a sweep. The canonicaliser carries constant folding,
idempotence, commutativity, ASSOCIATIVITY and FLATTENING (sorted
right-nested chains), `◯◯φ = ◯φ` and `◯⊤ = ⊤`, each law certified;
`simpIter` alternates rewriting and re-canonicalising to a fixpoint.

**Never harvest an unproved cell.** `wip/rnDict.lean` states 323 cell
theorems and proves 236; 87 are `sorry` and FOUR ARE REFUTED. The
first cut of the simpset took all 323 by name, so `rndSet` carried
`sorryAx` and four rules that rewrote a formula to a NON-interderivable
one — `RwRule.ok` is exactly what makes `norm_interd` unconditional,
so a `sorry`ed `ok` voids the guarantee silently. `#print axioms
rndSet`/`fullSet` are now `#guard_msgs`-pinned in
`Rewrite/Catalogue.lean` as the standing guard; keep them pinned.

**Standing item — bank, then re-run the loop.** Every NEW certified
interderivability a probe establishes gets banked into `Rewrite/`, and
banking is not finished until: (1) `lean_exe rwscreen` re-measures
effectiveness; (2) `lean_exe rnextend` re-tests whether the new
material closes any of the 83 open dictionary cells (it carries a
control and two adversarial checks — read `docs/rn-dictionary-status.md`
before trusting either verdict); (3) anything that closes is promoted
to a kernel-pinned theorem, the `sorry` deleted, and the catalogue and
RN explorer updated; (4) the axiom pins are re-transcribed verbatim.
Each campaign then makes the next one cheaper. Keep the PLL set and
any PCLL-only set separate: `RwRule` carries its `Interd` proof, so a
PCLL-only equation cannot enter a PLL set by construction.

Discipline: three-valued verdicts (`pass`/`fail`/`flag`) with `fail`
only ever on a certificate; `flag` (hypothesis certified, conclusion
unsettled at budget) is a frontier marker — re-run it at a raised
budget, never drop it silently. Gate cells by the statement's own side
conditions (saturation, parkedness, p-freeness) so a fail is a genuine
counterexample; record gate failures as such, never as passes. Run
banks COMPILED (a `lean_exe`, the repo's oracle pattern), not by
interpreted `#eval`; stream one appended line per cell so a killed run
loses nothing and hits are replayable without re-running the search.
Gate expensive cells by CONSTRUCTED value size and report every skip
(no silent caps). Escalate certified fails to kernel level (pin the
countermodel; it becomes a forced change or a refutation). Tools:
`tools/FrontierSampler` (stratified generation), `tools/catpart-ref`
(category partition; Lean port designed in `docs/catpart-lean-design.md`),
Plausible for random-only generation. Worked examples:
`wip/ljfo_eval.lean` (calibrated bank), `wip/ljfo_attack.lean` (the
four directions applied to `CimpAnt`).
