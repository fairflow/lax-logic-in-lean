# The arity question (A2): bounded join arity does not suffice

*2026-09-02, evening.  The first question of the practical
decision-procedure campaign, answered by the shape of the join rule and
confirmed on one designed family of cells.  Matthew's correction that
day governs the method: "design design design rather than brute
force"; a corpus sweep launched earlier the same evening was stopped
and is not evidence here.*

## 1. The question

The verified decider `decideGbuW` (`FRJ/Gbu/W/Saturate.lean`) rests on
`decideGbuW_of_dbClosed db (h : DBClosed G db)` (`FRJ/Gbu/W/Closure.lean`).
`DBClosed` has eight join clauses, each quantifying over families of
stored irregular rows of EVERY arity (`Ξs Θs : Fin (n + 1) → List Form`,
`n` free).  The planned efficient route (untrusted engine, verified
Boolean checker `checkClosed`, the verified consumer) needs the
checker to decide those clauses.  The engine already caps the family
arity (`Config.jmax = 3`, `pmax = 2`, `FRJ/Search/Engine.lean`).  So:

    A2.  Is there a k such that, for every G, a store closed under the
         non-join rules and under the join clauses at families of
         arity ≤ k is closed under the join clauses at every arity?

Equivalently: is every higher-arity join conclusion subsumed
(`WSubsumes`, `FRJ/Gbu/W/Dichotomy.lean`) by a row of the k-bounded
closure?

## 2. The answer from the rule

Take the barren `⋈^At` (`FRJWr.joinAt`, `FRJ/CalculusW.lean`).  From
premises `Ξⱼ ; Θⱼ → Cⱼ` (j = 0..n) with

    (J1)  Ξᵢ ⊆ Ξⱼ ++ Θⱼ            for i ≠ j
    (J2)  A ⊃ B ∈ ⋃ⱼ Ξⱼ^⊃  ⟹  A ∈ Υ,   Υ = {C₀, …, Cₙ}
    (J3)  ⋃ⱼ Ξⱼ^◯ = ∅,   F prime,  F ∉ ⋃ⱼ Ξⱼ^at,  F ∈ Sf^R G

it concludes

    barren :  ⋃ⱼ Ξⱼ^at,  ⋂ⱼ Θⱼ^at ∖ F,  ⋃ⱼ Ξⱼ^⊃,  kept(Υ, base, ⋂ⱼ Θⱼ^⊃)  ⇒  F

where `kept` (`keptOf`, `FRJ/RefAt.lean`) retains an implication
`Y ⊃ Z` of the pool exactly when `Y` is `RefAt`-refuted relative to `Υ`
and the context, and for an ATOM `Y` the only `RefAt` clause is
`ups : Y ∈ Υ`.

So an implication `pⱼ ⊃ q` with atomic antecedent enters a join
conclusion in one of two ways, through `⋃Ξ^⊃` under (J2) or through
`kept` under `RefAt.ups`, and both require `pⱼ ∈ Υ`: some premise has
goal `pⱼ`.  A premise has one goal.  Hence:

    a join whose conclusion context contains p₁ ⊃ q, …, pₙ ⊃ q with
    distinct atoms pⱼ has at least n premises.

In the `◯`-free fragment the context of a regular row is created only
by a join (`Ax^R` gives atoms only; `∧R`, `⊃∈`, `∨`-rules and the
promise rules keep or restrict the context).  Now let

    Gₙ  :=  (⋀_{j=1}^{n} (pⱼ ⊃ q)) ⊃ q .

`Gₙ` is not intuitionistically valid (all atoms false).  Its FRJW
disproof ends with `⊃∈` at the root, `barren : Γ ⇒ Gₙ` from
`barren : Γ ⇒ q` with `Clo Γ (⋀ⱼ (pⱼ ⊃ q))`, and `Cl(Γ)` contains an
implication `pⱼ ⊃ q` only if `Γ` does (`cloB`, `FRJ/Basic.lean`: the
`imp` case is membership or `Cl(Γ) ∋ q`, and `q` is refuted).  So `Γ`
holds all n implications and comes from a join of arity ≥ n.  The
premises that do it are the n seeds `Ax^I`: `[] ; Θⱼ → pⱼ` with
`Θⱼ = gAt ∖ pⱼ ++ gImp`.

Therefore the bound k of A2 does not exist: **A2 is REFUTED** by the
family `Gₙ` with witness arity n.  This is a fact about the paper's
IPC calculus FRJ(G) (Fiorentini–Ferrari, TOCL 2020), not about the
`◯` extension: the restriction `Θ^⊃/Υ` of their `⋈^At` is exactly the
mechanism.

## 3. The designed check

`tools/A2Probe.lean` (`lake exe a2probe <cell> --K= --M= --budget=
--nopromise= --dropjoins=`): per bound k it saturates the store with
the CORE non-join emitters and verbatim copies of the eight join
emitters restricted to families of size ≤ k (every row still carries
its `FRJW` derivation), then fires the join emitters at families of
exact size k+1..M over that store and reports the rows no stored row
subsumes; the full check (all arities, the core `stepAll`) runs when
its family count is within the budget.  `--nopromise=1` drops the
promise joins, exact for `◯`-free `G` (their `chain`-tagged rows
subsume no `barren` row and are consumed only by `◯∈` and by
themselves).  The gate was watched failing first: with `--dropjoins=1`
(join-built rows removed from the store) three cells report
unsubsumed rows and FAIL.  Transcript: `wip/a2probe_out.txt`.

The designed cells are `Gₙ` for n = 2, 3, 4 (probe indices 19–21).

| n | bound k | root disproof `Γ ⇒ Gₙ` stored? | smallest unsubsumed join over the k-store | verdict at k |
|---|---|---|---|---|
| 2 | 1 | no  | arity 2: `⋈At` `[q, q, p₂⊃q, p₁⊃q] ⇒ p₁` | not closed |
| 2 | 2 | yes | none; full check 2¹⁴ families, 0 unsubsumed | CLOSED (all arities) |
| 3 | 1 | no  | arity 2 | not closed |
| 3 | 2 | no  | arity 3: `⋈At` `[q, q, q, p₃⊃q, p₂⊃q, p₁⊃q] ⇒ p₁` | not closed |
| 3 | 3 | yes | none at arity 4 (C(34,4) families); full check 2³⁴ infeasible | root present, closedness FLAG |
| 4 | 1 | no  | arity 2 | not closed |
| 4 | 2 | no  | arity 3 | not closed |
| 4 | 3 | no  | arity 4: `⋈At` `[q, q, q, q, p₄⊃q, …, p₁⊃q] ⇒ p₁` | not closed |

The root disproof appears exactly at k = n (n = 2, 3; absent through
k = 3 for n = 4), and at every k < n the store lacks an arity-(k+1)
join, as §2 predicts.  (The duplicated `q`s are former-shaped
contexts: `gAt` lists `q` once per occurrence in `Sf^L`.)

Consequence for the engine as it stands: with `jmax = 3` the W-engine
cannot refute `G₄`, and `Stats.jmaxBinding` flags it (the flag fires
whenever the irregular store exceeds `jmax`, so it is a FLAG, never a
verdict).

## 4. Two side findings

* **The engine matches the verified bounded closure.**  At every
  (cell, k) above, `wOps` at `jmax = pmax = k` with the other caps
  lifted and the verified k-bounded saturation subsume each other
  row for row (`engine-rows-unsubsumed-by-probe = 0`,
  `probe-rows-unsubsumed-by-engine = 0`).  On these cells the
  strict-vs-relaxed gap (A3) is empty.  Not a general result.
* **The verified emitters are not an engine.**  At n = 4, k = 3 the
  saturation stores 299 canonical keys in 149 s where the engine keeps
  26 subsumption-reduced rows in 2 rounds; the cost is the `Λ`-sublist
  enumeration of `⊃∈ᵢ` and the key-not-subsumption retention.  A
  checker should run against the engine's reduced store.

## 5. What replaces A2: the designed cells (2026-09-02, later)

The bound is not absolute but it need not be: the argument of §2
bounds the USEFUL arity by the number of distinct goals.  The join
conclusion contexts are pure list functions of the family
(`joinCtxAtVBase`, `keptOf`, `joinCtxAtP`, …), so a designed cell is an
explicit family and the kernel decides it: `wip/b1b2_cells.lean`, ten
cells and two controls, every claim `decide`d, pins
`[propext, Quot.sound]`.

    (B1)  A family with two premises of the same goal is subsumed by
          the sub-family dropping either of them, and the sub-family
          satisfies the side conditions.

Argument: same `Υ`; by (J1) the dropped premise's `Ξ^at`, `Ξ^⊃` lie in
`Ξⱼ ∪ Θⱼ` of every kept premise, so the atom part is covered by
`⋃Ξ^at ∪ ⋂Θ^at` of the sub-family and the implication part by
`⋃Ξ^⊃ ∪ kept` (`refAt_mono`, and `keptOf` is closed under its own
rule with the sub-family's larger pool).  Cell B1-a (barren `⋈^At`,
goals c₁, c₁, c₂, the kept chain exercised through `RefAt.imp`):
dropping either duplicate subsumes (`b1a_drop1`, `b1a_drop0`); the
control, dropping the unique-goal premise, does not (`b1a_control`),
and the lost formula is exactly the kept implication `c₂ ⊃ w`
(`b1a_control_witness`).  Cell B1-b, the same family under a promise
world in the promise `⋈^At` with a live modal part: both drops subsume
(`b1b_drop1`, `b1b_drop0`).  Hence join families can be taken with
pairwise distinct goals: arity ≤ number of distinct goals of stored
irregular rows ≤ |Sf^R G|.  (B1) SURVIVES its cells; the general
lemma is the next build.

    (B2, as first sketched)  A promise family can be cut to a hitting
          set for ⋃Ξ^◯ alone.   REFUTED.

The modal part of a promise conclusion is `⋃Ξ^◯ ++ restrictC (⋂Θ^◯) Δs`
under `restrictP`, and `restrictC` keeps `◯Y ∈ ⋂Θ^◯` only with a
witness world `Y ∈ Cl(Δᵢ)`; a hitting set for `⋃Ξ^◯` may drop that
witness.  Cell B2-refute: `[◯m₁] ; [◯m₂, a₁] → c₁` under
`Δ₀ = [m₁, m₂, ◯m₂]`, `Δ₁ = [m₁, ◯m₂]`: the full family keeps `◯m₂`;
the hitting set `{Δ₁}` for `⋃Ξ^◯ = {◯m₁}` loses it
(`b2_naive_refuted`, `b2_naive_witness`).

    (B2′) A promise family can be cut to a hitting set for the modal
          formulas of ⋃Ξ^◯ and of ⋂Θ^◯ that the full family
          witnesses: arity ≤ number of distinct modal formulas of Ĝ.

Argument: (J5′) and `restrictC` need one witness per modal formula;
`restrictP` and (J6), (J7) only weaken with fewer worlds; the pledge
`D` is common to all.  Cell B2′: the hitting set `{Δ₀}` subsumes
(`b2_corrected`).  SURVIVES its cell.

**Both PROVED as general lemmas (2026-09-02, night)**,
`wip/b1b2_lemmas.lean`, pins `[propext, Quot.sound]`, no choice (the
one Mathlib lemma that carried choice, `Fin.succAbove_ne`, is replaced
by a hand proof).  The statements are about the conclusion-context
functions under a reindexing `e : Fin (m+1) → Fin (n+1)` of the family:

    ctxAt_sub, ctxOr_sub, joinCtxAtF_sub, joinCtxOrF_sub,
    joinCtxAtP_sub, joinCtxOrP_sub
      : e injective away from the dropped index p, surjective onto the
        rest, goal-covering (∀ j, ∃ k, rhs (e k) = rhs j), and the family
        satisfying (J1), (J2) (and F ∉ ⋃Ξ^at, (J5′) where the rule has
        them)  ⟹  the family's conclusion context ⊆ the sub-family's;
    j1_comp, j2_comp, j3_comp, fNot_comp, j5_comp, j6_comp
      : the side conditions transfer to the sub-family;
    b1_joinAt : the package for a duplicated goal, e = Fin.succAbove p;
    b1_joinAt_subsumes, b1_joinAtP_subsumes : the WSubsumes forms;

    joinCtxAtP_cut, joinCtxOrP_cut
      : e : Fin (m+1) → Fin (k+1) hitting every witnessed modal formula
        of ⋃Ξ^◯ ++ ⋂Θ^◯  ⟹  the promise conclusion context ⊆ the cut
        family's;
    j5_cut, j6_cut, j7_cut : the promise side conditions transfer;
    b2_joinAtP_subsumes : the WSubsumes form.

The proof is the monotonicity of the aggregates plus the (J1) cover
(`cover_of_j1`, through a constructive finite case split
`exists_or_forall`), with kept implications transferred by
`keptOf_mono` (itself `keptOf_saturated` + `refAt_mono` along the
kept chain).

With (B1)/(B2′) the checker's join clauses become a G-dependent
bounded enumeration: irregular families = cliques of the
(J1)-compatibility graph with distinct goals (`famsUpToC` in
`FRJ/Search/Fast.lean` already enumerates cliques), promise families
= hitting sets over at most |Ĝ^◯| modal formulas.  Whether the
resulting check is polynomial in the store is a separate question;
the `Gₙ` family shows the arity itself grows with the formula.

## 6. Not claimed

* The lower bound of §2 is a hand argument about the rules plus the
  probe's evidence at n ≤ 4.  The kernel-level statement, "every
  FRJW disproof of `Gₙ` contains a join of arity ≥ n", is OPEN and no
  declaration asserts it.
* (B1), (B2′) are PROVED at the level of the join-context functions
  and side conditions (`wip/b1b2_lemmas.lean`); what is NOT yet
  stated is the checker-level corollary, "the join clauses of
  `DBClosed` hold iff they hold on distinct-goal, witness-minimal
  families", which needs the reindexing pack of `W/Saturate.lean` and
  is the next build.  (B2) as first sketched is REFUTED.
* Closedness of the k = n store for n ≥ 3 is unverified (the full
  check is infeasible at 2³⁴ families); only n = 2 is CLOSED.
* The engine agreement of §4 holds on the cells run, nothing more.
