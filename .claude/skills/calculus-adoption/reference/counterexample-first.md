# Screening statements before proving them

Statement failures, not proof failures, are the recurring fault. Every
definitional defect in this development was refutable by a small
countermodel *before* a proof build could fail opaquely.

**Every quantified candidate statement gets an extensional attack before a
proof is scoped.** Four directions, in order of observed yield:

1. **Corpus replay.** Translate the repo's own hard instances into the new
   statement's cells first — they carry known duplication and financing
   content that random and degenerate cells miss.
2. **Boundary cells.** The degenerate end of every axis: empty contexts,
   `⊥`, the eliminated atom itself, and every NO-CASE corner of the
   definition. A clause family with a missing row is a prime defect site.
3. **Frontier extension.** One step beyond every passing stratum: size+1,
   depth+1, a second interacting member, position permutations. Never
   re-run only the strata that passed.
4. **Branch coverage.** Every match arm exercised by an admissible cell.
   Pairwise is not enough — one defect here needed a 3-way interaction.

Discipline: three-valued verdicts, `fail` only ever on a certificate,
`flag` (hypothesis certified, conclusion unsettled at budget) is a
frontier marker to re-run at a raised budget, never dropped silently. Gate
cells by the statement's own side conditions so a fail is a genuine
counterexample. Run banks **compiled** as a `lean_exe`, not by interpreted
`#eval`, streaming one line per cell so a killed run loses nothing.

See the repo `CLAUDE.md` for the normalisation step and the measured
effect of the certified simpset.

## Why this is a hard gate

A calculus whose completeness had already been proved was refuted at
soundness by **three certified cells**, found in minutes. The screen
belonged before the proof effort, and the proof effort was large.

The same applies to a rule you are *designing* rather than transcribing:
surface it with `#rules`, screen it, and get the statement signed off
before anything is built on it.
