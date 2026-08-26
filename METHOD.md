# METHOD.md — from conjecture to proof

How to respond to a request for a proof. The pipeline is

    Conjecture → Formal statement → Test strategy (refutation AND
    validation) → Proof build (or disproof → refinement cycle)

and its governing economics: **statements are cheap, proof builds are
expensive, and disproof falls out sooner** — so the attack always runs
before the build is scoped. `CLAUDE.md`'s "Testing for counterexamples"
is the cell-level stage of this pipeline; this file is the level above:
what to do when the statement is not yet a set of decidable cells.

## 0 · Search the record

Before treating the conjecture as new: memory, `HANDOFF.md`,
`docs/calculus-map.md`, the banked certificate corpus. Re-derivation
without checking is the recurring waste (a settled cell once sat open
while its kernel-checked verdict existed under another numbering).

## 1 · Formal statement

Write the statement as a displayed formula with every quantifier
explicit and every side condition inside the statement, never in prose.
The statement — not the proof — is the artefact under test: every
definitional defect in this development was refutable at statement
level before any proof build could fail opaquely. Classify it:

- **concrete** — quantifiers range over decidable cells (specific
  sequents, finite frames): go straight to the four-direction attack;
- **high-level** — quantifier alternation over an infinite or
  higher-order domain (∃ an interpolant, ∀ statements of a scheme,
  completeness of a calculus): a harness must be *manufactured* (§2).

## 2 · Refutation strategy

Concrete statements: the four directions of `CLAUDE.md` (corpus replay,
boundary cells, frontier extension, branch coverage), normalised through
the certified simpset first (`TOOLS.md` §1).

High-level statements are not directly testable — the harness is built
by **descent**, using whichever of these moves applies:

1. **Bound the witness space by a certified theorem.** An unbounded
   "∃ ψ" or "∀ ψ" becomes finite only on the strength of a proved
   classification. Where the R-catalogue applies, "∀ known classes"
   is 22 cells — but R is open-ended and the closed fragment is PROVED
   infinite, so exhaustion over R refutes *relative to known classes*
   and must be reported with that scope. A genuine bound (degree,
   subformula, normal form) is itself a lemma to prove first.
2. **Replace the statement by a certified equivalent with witnessable
   failure.** The direct refutation of "PLL has UI" needs "no p-free ψ
   works" — a universal over an infinite set. The workable route is an
   equivalence (semantic characterisation, amalgamation-style) whose
   failure is exhibited by a *finite object* (a model pair); then
   countermodel search applies. If no such equivalence is certified
   yet, that equivalence is the first sub-goal, not the test.
3. **Refute schemes, not the theorem.** A high-level claim decomposes
   into candidate statement schemes / proof strategies, each concretely
   testable. The UI campaign's rounds worked exactly this way: the
   Mixed and GuardedMixed schemes were REFUTED at φ♦ while the guarded
   stretch survived and delivered `∃p.φ★ = ¬¬◯⊥` PROVED. Killing a
   scheme is progress even when the theorem stays open.
4. **Escalate along a financed ladder.** Instantiate the outer
   universals with the smallest instances carrying the feature that
   finances difficulty (duplication, modal nesting): the escalation
   ladder `p ∨ ¬p → φ★ → φ♦` is the model. The first failure is
   expected at the smallest instance with the right feature, not at
   random cells.
5. **Mine cross-engine disagreement** (completeness-type claims). Run
   one sound prover and one sound refuter independently; an instance
   where their verdicts contradict the claim is a kernel-checkable
   witness. Paper-FRJ◯ completeness fell to exactly this (#80/#81).
6. **Name the untestable residue.** What the harness cannot reach is a
   finding, not a gap to hide: UI round 9 established that the
   room-carrying statement is not decide-feasible and *must be built* —
   that discovery re-scoped the campaign and is recorded as such.

## 3 · Validation strategy

Absence of a counterexample is not support. Before a build is scoped:

- **realise the existentials**: produce nontrivial instances where the
  statement's ∃ is actually witnessed (the first cover inhabitants
  ⊥ ⋖ ◯⊥ and ⊥ ⋖ ¬◯⊥ validated the in-fragment covers notion before
  the cube theorem was attempted);
- **check non-vacuity**: confirm something satisfies the hypotheses at
  all — a statement passing on an empty domain has been tested on
  nothing;
- **bank what validates**: validated instances join the corpus and
  become the replay material for the next statement.

A total validation *failure* is itself a signal to invert the
conjecture: the search for a bare cover in full PLL failing everywhere
led directly to the density theorem — the order is dense, so bare ⋖ is
empty, PROVABLE rather than testable.

## 4 · Proof build, disproof, and the refinement cycle

Scope the proof build only when the statement has survived the attack
AND carries nontrivial validations. On a technical disproof:

1. the refuter is a RESULT — pin it to kernel level and bank it; it
   joins the corpus for every later cycle;
2. localise the false clause and restate;
3. the new statement inherits NOTHING: the full attack re-runs (a pass
   record does not transfer across a restatement);
4. record the cycle in the campaign doc: statement version, its
   refuter, the repair.

Worked instance of the cycle, from this branch: the covers conjecture
C2 was first stated over a finite scope K and refuted on cardinality
grounds; restated over genuine covers it became a distributive-lattice
THEOREM (the Boolean-cube embedding). The FRJ campaign ran the same
loop one level up: paper completeness REFUTED (#80/#81) → RefAt repair
→ `soundnessV` PROVED, completeness re-opened as OPEN — the disproof
was the trigger for the calculus refinement, not the end of the line.

## Stop rules

- A refuted statement ends its cycle immediately; do not continue a
  build "to see how far it gets".
- OPEN never gets a sorried declaration; the frontier lists are the
  record of the unsettled.
- A cycle is closed only when its statement, refuters, and validations
  are banked — the next cycle starts from the enlarged record, which is
  what makes each campaign cheaper than the last.
