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

## Appendix A · The model-to-tree recipe (hand witnesses in a refutation calculus)

A refutation calculus with a model extractor has two directions, and
knowing which one you are running prevents a provenance error:

- **Native (derivation → model).**  The calculus's constructive content:
  `FRJ.V.modR` extracts a Kripke countermodel FROM a refutation
  derivation — this is `soundnessV`'s computational heart, and it is how
  FRJ◯ *discovers* countermodels when its engine finds the derivation
  first (ρ12⊬ρ15's 11-world model came this way).
- **Reverse (model → tree), the hand-witness practice.**  When the
  countermodel is already banked (battery sweep, streamed Tab
  generation — NOT the refutation calculus), the model becomes the
  DESIGN for a hand derivation.  The 2026-08-26 witnesses
  (`FRJ/WitnessV{1918,2018,2013,2012}.lean`, each first-pass) ran this
  direction; `wip/frjv_extract_demo.lean` then closes the circle by
  running `modR` on a finished hand term and checking the extracted
  model refutes the goal (it does — 14 worlds, the tree unfolded).

The recipe, in order:

1. **Probe before designing.**  Compute the goal's `sfR` (admissible
   conclusions), `gHat` (the Θ-vocabulary), and `Clo` closures of the
   candidate contexts — one probe caught `b ∉ sfR(G2013)` and steered
   that design away from any `b`-concluding row.  Never guess a side
   condition the checker can compute.
2. **Match the alphabet.**  Look for an existing witness over the same
   subformula alphabet; the 1918 tree's bottom half is WitnessV1215's
   verbatim under `β,ν,σ,δ ↦ a,¬a,b,¬¬a`.
3. **One world per join, bottom-up.**  Fallible top ↦ `Ax^I ⊥`; a world
   assuming an antecedent ↦ `⊃∈ⁱ` with that `Λ`; an interior world whose
   `◯`-content survives via `Rm` ↦ a PROMISE join carrying the modal
   kept zone; a world forcing content only vacuously (its cone ends
   fallible) ↦ `Ax^I◯`/blocked joins; the root ↦ the barren V-join whose
   `RefAt` disjunct/body conditions the premise rhs's (Υ) must supply.
4. **Two levers when the hypothesis must reach the root context**:
   the KeptChain (a link is adoptable when its ANTECEDENT is
   RefAt-refuted over base + earlier links — stratification lets a
   second link ride the first, as ρ8 rode ¬a), and Υ-ENRICHMENT (merge
   rows with `orI`, stabilise with `⊃∈ⁱ Λ`, so a needed antecedent
   becomes a premise right formula — how ρ11 entered Υ for ρ20).
5. **`decide` referees; it never designs.**  Every side condition is
   discharged by `decide` against the probed design; a `decide` failure
   is a design error to rethink, not a nudge to weaken the statement.
   The one hand proof in four files was an ∃ under a free variable
   (a nonempty stable modal zone's (J5)).

Cost calibration: four witnesses ≈ one session, ~200 lines each; the
engine alternative was ~2 h/cell at the raised join arity and returns a
log line, not a kernel object.
