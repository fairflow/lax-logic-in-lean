# PCLL and PICLL against the UI proof arc — the report

*2026-08-12, at Matthew's direction: "re-run that search keeping the
entire proof arc in mind." No prior arc-indexed report existed; what
did exist, and is built on here rather than re-derived: the semantic
confluent plan (`docs/confluent-ui-plan.md` §3), the G4cf gap
(`wip/g4confGap.lean`, kernel), the RNC quotient results (PROGRESS
§§40–44), the one-variable PCLL semantic UI state (PROGRESS §§34–39),
and the calculi `DerivU` (PCLL) and `DerivUNoFall` (PCLL + ¬◯⊥) in
`docs/calculus-map.md`. PICLL = propositional infallible confluent lax
logic = PLL + ◯(A∨B) ⊢ ◯A∨◯B + ¬◯⊥.*

## 0. The two headline facts inherited from July

1. **The semantic one-variable PCLL UI was ONE obligation from done
   when the campaign pivoted** (PROGRESS §39): pillar 3 fully paid,
   the mforth residue PAID via the constant variable-free-agreement
   link (`vfB_mforthResidue`), `restricted_amalgamation_oneVar`
   PROVED; the sole remainder is the pair VfMforth/VfMback (pillar 2's
   m-clauses for the constant link) plus the Thm 5.1 wrapper. This is
   the genuinely cut-short investigation, and it is the cheapest
   unconditional UI theorem available anywhere in the family.
2. **Distribution does NOT tame the value tower** (PROGRESS §§40–44,
   certified): the RNC quotient merges 19 → 15 variable-free classes
   (q9 ≡ q12; the witness class fuses, `distF q3 q6`) but the closure
   sweep spawns 26 new classes — *"the tower continues past
   distribution"*, no plateau at any observed crank. So the hope that
   PCLL makes the p-free lattice finite enough for stabilisation to
   come free is REFUTED at the variable-free level already. W is not
   free in PCLL.

## 1. Where distribution helps, stage by stage along the LJF◯ arc

**(a) The calculus.** LJF◯ + distribution inherits a machine-checked
landmine: `G4cf` (G4c + the analytic `distL` rule) has its
completeness-without-cut AND its cut admissibility kernel-refuted
(`g4cf_complete_refuted`, the `NoObOr` invariant collapsing `G4cf` to
`G4c` on the cut-necessity sequent's cone). A focused PCLL calculus
therefore cannot simply add a distribution rule; the options are
distribution as an axiom schema held in the context (persistent, so
LJF◯'s membership discipline carries it, at the price of polluting
every station with schema instances) or a genuine redesign. This is a
real, unpaid proof-theory cost specific to the focused route — the
semantic route does not pay it.

**(b) The interp rows — forced change #2 largely dissolves.** The
goal-inversion row FAMILY exists because ◯ does not distribute over ∨:
the or-shape carries three rows (`A(⇒◯P₁)`, `A(⇒◯P₂)`, `A(⇒↑(P₁∨P₂))`).
Under distribution `◯(P₁∨P₂) ⟛ ◯P₁ ∨ ◯P₂`, so the ◯-or-goal
decomposes at the ∨-level and the or-arm moves from the ESSENTIAL to
the INCIDENTAL column of the round-2 retrospective's map (item 12).
The sevenfold shape analysis shrinks; the aggregates carry fewer rows;
the fixpoint equation system is smaller. These are the gains Matthew
predicted would "accrue over the other lemmas" — real, but peripheral.

**(c) Forced change #3 (the box wrapper) survives.** Its countermodel
(`done = []`, `Δ = [◯q]`, goal `↑q` at lax) contains no ∨ and is
confluent-friendly; distribution neither removes the need for the
wrapper nor obstructs it (with distribution the wrapper may be pushed
per-row, `◯(↓r₁ ∨ ↓r₂) ⟛ ◯↓r₁ ∨ ◯↓r₂` — cosmetic).

**(d) E1/A1** port with an extra schema case and simpler or-clauses;
nothing structural.

**(e) E2/A2 and CimpAnt — the central blocker is expected to
SURVIVE.** The ①/② duplication is implication-driven, not ∨-driven:
the blocker sequent `◯((◯p→r)→◯p), ◯p→r ⇒ r` is ∨-FREE, so
distribution instances give it nothing directly, and the crossed-
station χ-reuse mechanism is untouched. No reason was found, at any
stage of the walk, to expect `CimpAnt` easier in PCLL. The fuel/
retention route (layer 4) and its W remain the discharge plan there.

**(f) W and the stabilisation picture.** Smaller equation system
(fewer rows) but, per headline fact 2, no lattice collapse — the
chains still live in an infinite p-free lattice and stabilisation
still needs proving per cell. One measurable hope remains: the class
MERGES (19 → 15 at variable-free level) may lower individual
stabilisation fuels; the candidate-cell machinery can measure this
directly (probe P2 below). The per-instance strengthening of §§40–44
also transfers: the gap-row value `∀p.◯(◯p⊃p) = ◯⊥` stands certified
against the entire enlargement in BOTH quotients, and
`not_derivU_of_checkConf` (confluent countermodel ⇒ PCLL-
underivability) is the reusable refutation instrument.

## 2. PICLL: what ¬◯⊥ adds and what it takes away

**What it gives the prover.** `◯⊥ ⟛ ⊥`, so all ◯⊥-content collapses:
the candidate cell's interpolant `θmax = ((◯⊥⊃r) ∧ ◯q) ⊃ ◯⊥` becomes
`¬(r-guard ∧ ◯q)`-shaped; the closed fragment of PLL + ¬◯⊥ is exactly
2 elements (the ladder results), and with confluence on top the
variable-free landscape is trivial. Every ⊥-instance argument
simplifies. The 1-pv fragment of PICLL is plausibly the tamest
nontrivial setting in the family — unproven, but everything known
points that way.

**What it takes from the refuter — Matthew's point, CONFIRMED.**
Refutation in PICLL demands countermodels that are confluent AND
infallible, and the fallible-world device carries a large share of the
existing corpus: the stabilisation probe's strict-step family M₂ has
`fallible = [2]`; one of the two converse-K countermodels needs its
fallible world; the battery's fallible frames certify many RNC rows.
Under PICLL those certificates die — losing a witness is not
derivability, but the refutation ROUTE thins exactly as stated, and
the two-pronged method tilts prove-first there. Engine support is one
config away (`accept := infallible ∧ confluent`, the `RNC.confB`
pattern extended); the model CLASS, not the tooling, is the
constraint. A corollary worth testing: the candidate cell's strict
steps may not be strict in PICLL — infallibility may buy EARLIER
stabilisation (probe P3).

## 3. The recommendation, ranked

1. **Finish the semantic one-variable PCLL UI** (VfMforth/VfMback +
   the Thm 5.1 wrapper). It was one obligation from done; it yields
   the family's first unconditional UI theorem; and its 1-pv scope
   matches U/V, giving the route-4 comparison a proved instance to
   anchor on. PICLL-1pv should then follow on the infallible subclass.
2. **Run the PCLL/PICLL probes on the LJF◯ cells** (P1–P3 below) —
   cheap, and they price the peripheral gains honestly before any
   focused-calculus commitment.
3. **Do NOT start a focused PCLL calculus** until the G4cf landmine
   has a design answer (axiom-schema-in-context is the only currently
   safe form) — and given (e), the focused arc's hard core would not
   get easier anyway.

## 4. Probe designs (specified, not run — this worktree currently has
no build cache; run after round 3 or in the fresh session)

* **P1 (PCLL-prove/refute kit):** prove = the certificate engines with
  the distribution schema instances over the sequent's subformula
  universe added to Γ; refute = `Config.accept := RNC.confB` (exists).
  PICLL: extend the accept filter with infallibility; prove side adds
  ¬◯⊥.
* **P2 (the arc cells under PCLL):** re-run the stabilisation chains
  (`stabrun`) and the candidate cell under P1's kit; measure whether
  per-cell f₀ drops and whether the or-family strata change verdicts.
* **P3 (PICLL early-stabilisation):** the certified strict steps
  (M₁/M₂-refuted) re-tested under the infallible filter; if the steps
  lose all witnesses AND the prover closes them, the chain stabilises
  earlier in PICLL — quantifying §2's corollary.
* **P4 (the sole open matrix cell):** `[q14] ⊢ q13` is open in both
  logics (PROGRESS §43); an infallibility pass may decide it in PICLL.

Claim discipline: UI is OPEN for PLL, PCLL and PICLL at every variable
count; the nearest closed result on this map is item 1 of §3.
