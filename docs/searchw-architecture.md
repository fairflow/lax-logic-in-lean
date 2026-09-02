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

## 4. Innovation 1 (HISTORICAL since stage 2 of the compaction, 2026-09-02 — the chase is gone; see docs/frjw-compaction.md): the (antecedent, goal) visited-pair chase

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

## 10. The instantiation stage (CLOSED, 1 September evening)

`searchW`/`dichotomyW` are parameterised by a `WSaturated` database
with deciders.  The chosen instantiation (wip/gbu_frjw_closure.lean):

    D := (· ∈ db G)   for a COMPUTED closure db,

so the deciders are finite scans and the whole weight sits in
`WSaturated.2` — every derivable row subsumed by a stored one — proved
by induction on the derivation.  Each rule case rides its MONOTONICITY
lemma (T-B): the rule applied to stored subsumers of its premises
yields a conclusion subsuming the original's.

PROVED so far (all pinned `[propext, Quot.sound]` or lighter):

* **T-A, kept-chain dominance** — every `KeptChain` link lands in the
  greedy `keptOf` (via `keptOf_saturated` + `RefAt`-monotonicity), with
  the parameter-growth form absorbing zone growth.  The A1 attacker had
  survived 5/5 designed seeds first.
* **T-B, all 21 rules** — the three barren joins (canonical `keptOf`
  chain; the relaxed (J2) certificates lift by `refAt_mono` through the
  context inclusion), the two fallible joins, the three promise joins
  (double family swap; pledges ride `pledge_of_le` up the retention
  order `tagLeB`; the restriction filters are monotone in list AND
  predicate), `⊃∈ᵢ` (the second-zone re-split by membership in the
  original `Λ`), `Lift`/`◯∉` at the maximal retained zone
  `maxTh G Γ₂ = Ĝ ∩ Cl(Γ₂)`, and `◯∈`.  Leaf rules inline.
* **Wellformedness for the universe** — `wfR`/`wfI` (contexts ⊆ `Ĝ`,
  already banked) plus the new `goalWr`/`goalWi` (goals ∈ `Sf^R`) and
  `tagWr` (pledges ∈ `Sf^R`): every derivable row lives in a finite
  canonical universe.

OPEN (the remaining build, design locked):

* DONE since: `WRow` (rows as data), the deciders as finite scans,
  `decideGbuW_of` (decision modulo `WSaturated.2`), the closedness
  contract `DBClosed` (one clause per rule over STORED premise
  sequents), choice-free family skolemisation (`findSub`/`IrrPick`/
  `RegPick`), and the full T-C induction `tCr`/`tCi` — so

      decideGbuW_of_dbClosed :
        (db : List (WRow G)) → DBClosed G db →
        ProvableGbuC G ⊕' DisprovableW G

  is PROVED, pinned `[propext, Quot.sound]`.
* the ONE remaining obligation: per `G`, CONSTRUCT `(db, DBClosed)` —
  the saturation computation.  Its parts: join extensionality (a join
  depends on its family only through zone membership, so the `∀ n`
  clauses reduce to nodup sublists of the store), the rule enumerator
  with the T-B `_mono` defs carrying the row derivations, and
  termination by the finite canonical universe (`wfR`/`wfI` +
  `goalWr`/`goalWi`/`tagWr`).  Then GBUW and FRJW completeness read
  off simultaneously, plus a certified PLL decision procedure.

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
* 2 September (continuation): the Ledger reverted to its 31-Aug state
  on Matthew's instruction (campaign status lives in the session report,
  not the reference ledger) and its HTML source checked into git
  (docs/pll-calculus-ledger.html).  `#cf_search` added to `Meta/Audit`
  (TOOLS.md §5): choice-free lemma search at reach time, after
  `List.eq_nil_iff_forall_not_mem` leaked choice into three closure
  defs.  Closure stage Parts I–III: T-A proved, T-B proved for all 21
  rules, universe wellformedness (`goalWr`/`goalWi`/`tagWr`) proved.
  A2/A3 attackers running in the background.

## 12. The goal closed (1 September, evening)

`wip/gbu_frjw_saturate.lean`: for EVERY PLL formula `G`, the saturated
derivation-carrying database exists and is closed —

    closureDB G, closureDB_closed : DBClosed G (closureDB G)

by: canonical keying (`canonSeq` through the deduplicated `Ĝ` pool),
the 19 rule emitters guarded by their own decidable hypotheses, the
prepend-only saturation with the pigeonhole over the finite wellformed
universe, and the coverage layer (arbitrary families reindexed to
stored sublists through the membership-determined aggregates; promise
blocked branches subsumed by the fallible joins).  Composed with the
T-C induction and `dichotomyW`:

    decideGbuW G : ProvableGbuC G ⊕' DisprovableW G      (data)
    frjw_complete : ¬ ProvableGbuC G → DisprovableW G
    gbuw_complete : ¬ DisprovableW G → ProvableGbuC G
    provableGbuC_iff_pll : ProvableGbuC G ↔ PLL G
    disprovableW_iff_not_pll : DisprovableW G ↔ ¬ PLL G
    decidePLL G : Decidable (PLL G)

All PROVED, sorry-free, `[propext, Quot.sound]`, `#guard_msgs`-pinned.
Choice leaks were driven out with `#choice_path` (three sources: the
`finRange` `Ord` chain in the Fin deciders, mathlib's `mem_dedup`, a
`simpa` through `Order.lt_add_one_iff`).

Matthew's observation on banking (recorded for the compaction pass):
the closure stage is a completeness-shaped argument of its own, and
the development now carries deliberate redundancy — the searchW
goal-set invariant (~200 lines, vestigial), the T-B `_mono` defs
(design scaffolding; the emitters fire constructors directly and the
T-C induction uses the `_of_swap` transfer lemmas), and two
independent GBUW completeness routes (LJF◯ translation vs the
dichotomy).  A compaction can strip the vestiges and possibly fuse
searchW's manufacture layer with the closure's emitters; the
mathematics will not change.
* 2 September: compaction stage 2 — the corner chase apparatus stripped
  (totality makes it redundant), `decRP` dropped from the chain,
  search file 1189 → 939 lines; stage 3 (retire the pair-V measure,
  `V` is never pushed) proposed for review.
