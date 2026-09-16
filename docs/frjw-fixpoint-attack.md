# The fixpoint stage: the disproving attack force

2026-09-01, on Matthew's directive: designed attackers, not brute
sweeps.  Targets are the candidate statements of the `decideGbuW`
instantiation stage (`WSaturated.2` for a computed closure, plus its
deciders).  Each attacker names its target, the structural weak point
it aims at, the designed seed family, and the verdict criterion.
Order = expected yield per token.

## The target statements

    T-A (keptOf dominance)
        KeptChain Υ base pool kept → ∀ Y ∈ kept, Y ∈ keptOf Υ base pool

    T-B (per-rule subsumption monotonicity), join form
        rows subsuming a join's premises yield a join whose conclusion
        subsumes the original's — so the closure need only join stored
        rows.

    T-C (closure completeness = WSaturated.2 for the computed fixpoint)
        every WDerivable row is subsumed by a stored row.

    T-D (canonicalisation invariance)
        query answers are invariant under `≐`-variants of stored rows.

## The attackers

### A3 — the foreign-derivation injector  ← FIRST (architecture value)

Target: T-C.  Weak point: **the engine still generates only
strict-(J2) joins**, while `WDerivable` is the RELAXED calculus — a
relaxed-only-derivable row that no strict-generated row subsumes
refutes T-C for the current engine and forces the engine extension
BEFORE any closure proof is scoped.

Analysis narrowing the seed: relaxed beats strict only at a
Σ-zone implication with a NON-ATOMIC antecedent (on atoms,
`RefAt`-descent is `.ups`, so relaxed = strict).  Σ-zones arise only
from `impInI` (`Lam` absorption), so the seed shape is

    a family row refuting ((◯d ⊃ b) ⊃ c)  — Σ ∋ ◯d ⊃ b —
    joined where Υ ∋ d but no ◯d-row is in the family.

The strict workaround (adding a `lift`-row for `◯d` to the family)
SHRINKS the `interAll`-Θ zone, so its conclusion may fail to subsume
the relaxed one.  Attack: hand-derive the relaxed join for a seed
formula around this shape; check subsumption against the engine DB.
Verdict: counterexample ⟹ extend `OpsW`'s join gate to `refAtB`
(generation-side of the 2026-09-01 calculus change) before the
closure proof; no counterexample after a genuine search ⟹ record why
strict generation stays subsumption-complete (a conservativity
lemma candidate).

### A1 — the chain saboteur  ← CHEAP, FOUNDATIONAL

Target: T-A.  Weak point: **order sensitivity** — `keptOf` is greedy;
a chain whose links certify only in a specific order could be missed.
Sequentiality already rules out mutual dependency; the residual risks
are `Clo`-mediated support (a link's antecedent certificate needs
ANOTHER link present in the context through the `imp`-clause) and
duplicate links.  Designed seeds, pools of size ≤ 4, ALL chains
enumerated exhaustively per seed (orderings of subsets — exhaustive
at the boundary, not brute over formulas):

    (i)   linear dependency  a ← b ← c   (RefAt of each antecedent
          needs the previous link in ctx via Clo)
    (ii)  diamond dependency
    (iii) Clo-mediated: antecedent reachable only through an
          imp-clause citing another pool member
    (iv)  ◯-towers in antecedents (circ-descent chains)
    (v)   ups-vs-ctx mixed bottoming, plus duplicated links

Verdict: any enumerated chain with a link outside `keptOf` refutes
T-A; then the closure must enumerate chains (finite but heavy) or
`keptOf` must be strengthened.

### A2 — the premise swapper

Target: T-B.  Weak point: the Θ-zones of a join **shrink** as the
family grows (`interAll`), and the tag order interacts with `Covers`
in the P-joins — monotonicity could fail at the pledged variants.
Attack: on SMALL designed formulas (|Ĝ| ≤ 6), run the engine
UNCAPPED; enumerate all 1- and 2-element families of stored irregular
rows; compute the `⋈^◯`/`⋈^At`/`⋈^∨` conclusions with `keptOf`
directly (all computable); check each conclusion is subsumed by a
stored row.  Verdict: a violation on an uncapped run is a closure
counterexample (cap artifacts excluded by design); localise which
rule and which zone broke.

### A4 — the unknown-28

Target: T-C reachability at the ρ-frontier.  The 28 FLAG cells of the
stopped ρ-run are a DESIGNED subset now: they are exactly where the
default-budget oracle could not settle.  Re-adjudicate them against
the RNDB bank verdicts (kernel-checked, already banked — the
`rncCert` lookup discipline); any truly-invalid cell with no engine
hit at a raised budget is a reachability-failure candidate: then
hand-derive its row or find the missing rule application.

### A5 — the ≐-mangler

Target: T-D.  Weak point: rows are LISTS; the fixpoint needs
canonical representatives, and hidden `≐`-transport bugs live in the
query layer.  Attack: permute/duplicate the zones of stored rows on a
small DB; all `WEvalI`/`WEvalR`/`WEvalRP` answers must be invariant.

## Standing discipline

Every attacker's gate is watched failing first (inject a defect,
confirm red, restore).  `fail` only on a certificate; `flag` is a
frontier marker re-run at a raised budget.  Compiled runners, one
line per cell, no silent caps.  The release-stratum corpus is retired
in its oversized form; its T1–T12 shapes re-enter here as A2/A3 seed
material at |Ĝ| ≤ 6.
