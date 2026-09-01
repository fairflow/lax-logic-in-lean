# The `searchW` architecture — running notes for Matthew

Started 2026-09-01 on Matthew's instruction: "keep notes as to how
you'll explain the architecture and the innovation in it to me, either
when complete or when I need to review what went wrong."  Maintained
alongside the build; every claim below is labelled PROVED / OPEN, and
the section "Where the quicksand would be" is kept current.

## 1. What is being proved

The cell-level dichotomy behind `decideGbuW`:

    WSearchOk G D (reg, Ψ, C):
      reg-clause:  well-formed cell → ¬ WEvalR D Ψ C → GbuRC G Ψ C
      irr-clause:  well-formed cell → WUnrefutedBelow G D Ψ C → GbuIC G Ψ C

over any `WSaturated` database `D`, with deciders for the row queries
as the only supplies.  Type-valued: the positive side RETURNS the
Gbu◯ derivation.  The FRJW side never proves; a row is a DISPROOF,
and the exclusion half (both directions) is already banked.

## 2. The skeleton: a lexicographic search with no naive measure

Naive backward Gbu◯ search has NO termination measure
(`not_wf_stepC`, kernel-checked).  `searchW` instead recurses on

    wgW (reg, Ψ, C, V) = (unclosed G Ψ,  |Sf^R × Sf^R ∖ V|,  tpC,  seqSize)

* `unclosed` — how much of the finite `≐`-universe the context has
  not yet `Clo`-captured; every `R⊃ₙ`-step (adding a genuinely new
  antecedent) strictly drops it, and everything else may reset below.
* the VISITED-PAIR count — the innovation that pays for the `Υ`-chase
  (§4).
* `tpC` — the mode/goal-shape rank (irregular ◯-free < irregular
  modal < regular).
* `seqSize` — plain sequent size for the structural descents.

## 3. The corner: why `◯`-goals are the whole problem

At an irregular CRITICAL cell (`Ψ ⊆ Ĝ_at ∪ Ĝ_imp`) with goal `◯Z`,
the searcher must either derive `◯Z` or manufacture a `◯Z`-row.  A
constructor sweep (PROVED, by cases on `FRJWi`) shows the only row
manufacture left after the direct rules are exhausted is the barren
`⋈^◯` join followed by `lift`.  A join retains a context implication
in exactly one of three ways:

  (i)   its antecedent has a row — the row joins the family and the
        implication is kept by `.ups`;
  (ii)  its antecedent has a `RefAt` certificate — a syntactic descent
        through ◯/∧/⊃-structure bottoming in the family's goals, in
        `⊥`, or in `Clo`-side conditions;
  (iii) its CONSEQUENT is `Clo`-available in the join context, so
        `Clo`'s imp-clause covers the implication with no retention.

Derivation-side, the only route through a critical `◯Z`-cell is
modus ponens on a context implication (`L⊃ᵢ`), which needs the
antecedent DERIVED first — the chase.

## 4. Innovation 1: the (antecedent, goal) visited-pair chase

The chase recurses from goal `◯Z` into an antecedent `A` whose size
the goal does not bound.  What pays is the visited set `V` of PAIRS
`(A, ◯Z)`: a chase strictly shrinks `Sf^R × Sf^R ∖ V`, and — the
point of pairs rather than antecedents — re-chasing the same `A`
under a DIFFERENT goal is still measure-payable.  Only the exact
`(A, ◯Z)` revisit is blocked.  Chases are confined to
`unclosed`-constant segments; `R⊃ₙ` resets `V` for free.

Consequence (analysis, load-bearing): a revisit means the search sits
INSIDE the pending chase of that very pair — resolved chases pop off
with their `limpLI`, so `V`-membership at a cell certifies an open
ancestor frame, not a stale record.

## 5. Innovation 2: the RefAt-relaxed barren (J2)

Approved by Matthew 2026-09-01.  `⋈^◯`'s stable-zone condition

    hJ2 : A⊃B ∈ ⋃ⱼ Σⱼ^⊃ → A ∈ Υ    became
    hJ2': A⊃B ∈ ⋃ⱼ Σⱼ^⊃ → RefAt true Υ (base ++ kept) A

— the same relaxation the body condition `hZ` already carried.
`soundnessW` re-proved (PROVED, pins `[propext, Quot.sound]`): the
base and kept implications now share ONE size-mutual induction,
founded by the Round-3 subformula bounds (`refAt_refutes_sf`): both
the `ups`- and the `Clo`-leaves of a certificate are subformulas of
its target.  This is what dissolves the Σ-zone contamination (old
K3): any stable-zone implication discharges by the same
refuted-or-certified split as the kept chain.

## 6. Innovation 3: the level-by-level kept chain (old K2)

A `KeptChain` certifies each link over the base plus the EARLIER
links, so retention looks order-sensitive, and stuck implications'
certificates cite `Clo Ψ`-facts that may pass through OTHER stuck
implications.  The escape (`refutedCleanly_circ_certs`, PROVED): a
certificate's `Clo`-leaves are SUBFORMULAS of its target
(`clo_sf_support`), hence strictly smaller than its implication — so
building the chain level by level on link SIZE (strong induction on a
bound, no sorting) always finds every leaf already in place.

## 7. Innovation 4: the goal-set invariant (K1)

One certificate per visited pair, relative to the CURRENT cell:

    RefAtG Ψ C P A  —  goal : bottoms at the current goal C
                       pend : bottoms at a pending form in P
                       bot / imp (Clo Ψ) / circ / or / andL / andR

Threaded through every recursion site (~30): structural goal-descents
substitute at the `goal`-leaves (the `R⊃` branch's `Clo`-guard is
exactly the imp-clause); an `∨`-descent records the abandoned sibling
as a PENDING leaf — no refutedness test at descent time, because
refutedness is context-relative and the corner re-tests at corner
time (this is what dissolves the both-unrefuted-`∨` case, the old
K1); a chase entry freezes the old goal into `P` and gives the new
pair the pure `.goal` certificate; context growth is absorbed by
`Clo`-monotonicity (every `unclosed`-constant step grows `Clo(Ψ)`).
The regular mode instead carries `V = []` — its only entry point
drops `unclosed`.

At the corner the invariant is CONSUMED: a stuck antecedent failing
the decidable manufacture test hands over its certificate; if every
pending leaf is refuted-now-or-the-goal, the certificate converts
(`refAtG_to_refAt`) and CONTRADICTS the failed test.  So the corner
survives only with a LIVE pending leaf.

## 8. Innovation 5: TOTALITY — the closure (2026-09-01, late)

The corner fell to a lemma found by refuting my own constructions.
Trying to BUILD a reachable corner instance, every attempt died on the
same dilemma: a stuck antecedent's `RefAt` test dies only at an atom
PRESENT in the context — but an atom present in the context makes the
corresponding subgoal derivable by `ax`, so the antecedent's chase
resolves; while an atom ABSENT from the context is always refuted
(`evalI_axI_gHat`: the `axI` row covers every critical cell the atom
is not in), so the `RefAt` test passes.  Pushed through every
connective, the dilemma is a theorem:

    totalityW : at a critical cell, every X ∈ Sf^R(G) satisfies
        RefAt true (Z :: R₀) Ψ X  ⊕'  GbuIC G Ψ X

with `R₀` the (decidable) list of ALL refuted `Sf^R`-forms — by
STRUCTURAL induction on `X`, because `RefAt`'s clauses and the
irregular introduction rules are De Morgan duals:

    ∧ : one side refuted        vs   both sides derivable
    ∨ : both sides refuted      vs   one side derivable
    ◯ : body refuted (cone)     vs   body derivable (`R◯ᵢ`)
    ⊃ : `Clo`-antecedent + refuted body   vs   `R⊃`/`R⊃ₙ`
    atom : absent (refuted)     vs   present (`ax`)

Each case totalises: children that fail one side supply the other.
The one non-structural step is the `¬Clo`-antecedent implication: it
is either refuted AS A FORM (`gbuInv9` reflects a regular
`B`-stratum row into an irregular `A⊃B`-row, so `.ups` catches it) or
its `¬WEvalR` precondition is exactly what the regular stratum's
clause needs — and that recursion drops `unclosed`, so it is paid by
the measure's first component, not by structure.

At the corner: the antecedent failing the `RefAt` test cannot be
refuted (`.ups` would have passed it), so totality hands over its
DERIVATION, and `L⊃ᵢ` steps through the implication; the consequent
recursion pays by size.  No invariant needed.  `searchW` is
**PROVED**, sorry-free, pinned `[propext, Quot.sound]` —
`Classical.choice`-free after constructivising the countermodel finder
(`Decidable.of_not_not`).  The root corollary:

    dichotomyW : DisprovableW G ⊕' GbuRC G [] G

over any saturated database with deciders, same pin.

## 9. The honest arc — what each layer bought

The final proof uses: the relaxed (J2) (soundness side), the
kept-chain manufactures (the all-tests-pass branch), the pair-V chase
(termination), and totality (the corner).  The goal-set invariant
(§7) is VESTIGIAL in the final proof: its threading remains in the
file, consumed only by a now-redundant certificate test.  It was the
scaffolding that produced the closure — the freeze/pending analysis
is what surfaced the atom dilemma — but a cleanup pass can strip
roughly 200 lines (the motive's two invariant components and ~30
per-site transfers) without touching the mathematics.  Likewise the
prime-body `axI`-`keptOf` escape and the certificate-conversion
branch are now redundant decidable fast-paths.  Recorded here so the
exposition can tell the true story: the invariant was a ladder, and
the theorem kicked it away.

## 10. What remains for `decideGbuW` (OPEN)

`searchW`/`dichotomyW` are parameterised by a `WSaturated` database
with deciders.  The concrete instantiation — for each `G`, a
saturated database (the engine's fixpoint or a by-construction
closure) with `Decidable` row queries — is the remaining stage.
`WSaturated.2` (every derivable row subsumed) is the substantive
half: a fixpoint/closure argument over the finite `≐`-universe.
Then: `decideGbuW : ∀ G, ProvableGbuC G ⊕ DisprovableW G` via
`dichotomyW` + the banked exclusion, and FRJW completeness reads off.

## 11. Ledger of the day (2026-09-01)

* (J2) relaxed on `⋈^◯`; `soundnessW` re-proved, one axiom lighter.
* `refutedCleanly_circ_kept` / `_certs` / `_axI` proved and pinned.
* Pair-V measure; goal-set invariant threaded end-to-end.
* **`totalityW` → `searchW` COMPLETE → `dichotomyW`, all pinned
  `[propext, Quot.sound]`.**
* Full project rebuild green; wscreen 18/18; separation Gbu◯ ↔ FRJW
  verified both ways (import graph + diff surface).
* Testing pivot on Matthew's directive: the release stratum
  (12 curated cells around the residue shape) replaced blind
  sweeping; its analysis produced the dilemma that became totality.
