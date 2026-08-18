# A fast countermodel search on FRJ◯ — review and design

*Written 2026-08-18 (session hello-8a60f1, branch `frj-lax` @ 8ca80ac) at
Matthew's request: review what exists, then say how to build a fast
countermodel search on the FRJ◯ calculus. Shareable; no code written yet.*

---

## 1. Why FRJ◯ is the right basis, independently of completeness

FRJ◯ soundness is PROVED (`FRJ/Sound.lean`, kernel-checked): from a
derivation `D` of `Γ ⇒ G` the extraction `Mod(D)` (`FRJ/Extract.lean`,
`preR`/`preI` → `toKripke`) builds a finite Kripke model whose root
refutes `G`, and `modR_countermodel` proves it does. So:

> **a derivation IS a countermodel, with its own certificate.**

That makes search on FRJ◯ *untrusted-but-safe* in the repo's standing
sense: every row carries its typed `FRJr`/`FRJi` term, so a hit
type-checks in the kernel and no trust is placed in the searcher. A bug
in the search can lose completeness (a miss), never soundness (a wrong
countermodel). Completeness of the calculus is a separate question and
does not gate this work — the OPEN half only bounds what the search can
be *expected* to find, and §15 has just widened that considerably.

The contrast with the present countermodel route matters:

| | how the model is found | cost driver |
|---|---|---|
| `PLLSearch.refute?` | fixed **frame battery** × valuation enumeration, then `CounterEmit.emit` over the subformula closure | frames × 2^atoms; `emitClosureCap = 12` because emit is exponential |
| FRJ◯ | the model is **built from the goal's own subformulas** by the rules | size of the derivation |

FRJ◯ never enumerates frames or valuations: worlds come from `⊃∉`/`◯∉`
cells and promise components, labels are subsets of `Ĝ`. The model is as
big as the refutation needs and no bigger.

## 2. What already exists (and what to reuse)

- **`wip/frj_sat.lean`** (859 lines, `lean_exe frjsat`) — the FRJ◯ engine:
  forward saturation, derivation-carrying rows (`RS`/`IS`), decidable
  side conditions at insertion, subsumption by tag-and-context dominance,
  caps reported not silent. **This is the semantic core to keep**; §3
  is about its cost model, not its faithfulness.
- **`LaxLogic/PLLG4Term.lean`** — the house pattern for exactly the kind
  of searcher proposed below: `partial def proveM` with
  `FailMemo := Std.HashMap (List PLLFormula × PLLFormula) Bool`, plus a
  budgeted twin `proveBounded`. Copy this shape, do not reinvent it.
- **`LaxLogic/PLLSearch.lean`** — two-sided `verdict`/`countermodel`;
  the differential-testing oracle for §6.
- **`Reject/`** — `Reject.certifies`: Built-tree countermodels as a
  `Bool` check; the independent model-side checker.
- **`LaxLogic/PLLDecide.lean`** (`decideG4`) — the decision procedure.
  Standing rule (CLAUDE.md): **never drive discovery through it**; its
  fuel bounds are infeasible. Oracle of last resort only.
- **`FRJ/Extract.lean`** — derivation → `PreModel` → `Kripke`. The output
  stage of the new tool is already written and proved.

## 3. Measured diagnosis: the space is tiny, the work is not

Zone sizes for the largest corpus goals (computed, not estimated):

| goal | `|Ĝ|` | `|Sf^R|` | `|Ĝ_at|` |
|---|---|---|---|
| `corner_taut_body` | 6 | 14 | 4 |
| `g4ill_blocker` | 8 | 7 | 3 |
| `corner_residue_poisoned` | 5 | 12 | 3 |

Every regular sequent is `(tag, Γ ⊆ Ĝ, C ∈ Sf^R(G))`, so the **entire**
regular state space of the worst corpus goal is bounded by
`3 · 2^8 · 7 ≈ 5·10^3`; irregular sequents `(Σ, Θ ⊆ Ĝ, C)` by
`3^8 · 7 ≈ 4·10^4`. These are trivial spaces.

Against that, one `frjsat` run reaches `RS ≈ 16`, `IS ≈ 34` rows — and
the current `roundStep` considers, per round:

    famsUpTo IS jmax   ≈ 19,000 irregular families   (jmax = 3)
    famsUpTo RS pmax   ≈    256 promise families     (pmax = 2)
    product            ≈  4.9 · 10^6 join candidates

and at the raised budget (`jmax = 4`, `pmax = 3`) ≈ `4·10^8`, ×16 rounds,
**recomputed from scratch each round** — `roundStep` re-forms every
family every time. Measured consequence: the 37-cell corpus takes
**87 s** on formulas whose state space is ~10^4.

> The engine is not slow because the problem is big. It is slow because
> it enumerates rule *instances* (10^6–10^8) instead of visiting *states*
> (10^4), and repeats that work every round.

Three cost centres, in order of size:

1. **Join families by subset enumeration** (`famsUpTo`), then filtering
   by (J1)/(J2). The filters are cheap; the enumeration is not.
2. **No incrementality**: no given-clause discipline, so round `n+1`
   redoes round `n`'s combinations.
3. **`List Form` contexts**: every `⊆`, `∩`, `∪`, membership is a list
   walk with structural `Form` equality, inside those 10^6 loops.

## 4. The design

### 4.1 Representation — index once per goal

Compute `Ĝ = Ĝ_at ++ Ĝ_imp ++ Ĝ_◯` and `Sf^R(G)` once; store as arrays;
represent every context/zone as a **bitmask** (`UInt64`, with a `Nat`
fallback above 64 — no corpus goal is near it). Then `⊆`, `∩`, `∪`,
membership, and the `Θ ∩ Λ = ∅` disjointness of `⊃∈` are single word
operations, and rows become hashable keys for free.

Precompute per goal:

- `sub[i]` — the subformula/polarity tables already in `FRJ/Basic.lean`;
- `clo[m]` — the `Cl`-closure of context bitmask `m`, as a bitmask over
  `Ĝ ∪ Sf^R`, memoised lazily (`Clo` is monotone, so this is a cache, not
  a table to fill);
- `impAnte[i]`, `circBody[i]` — antecedent/body indices, for (J2)/(J5);
- `classForce` valuations as bitmasks over `Ĝ_at`, for `Ax^I◯`
  (currently `(gAt G).sublists`, capped at 4 atoms and **not** reported
  in `Stats` — a silent cap, to be fixed).

### 4.2 The core algorithmic change: demand-driven joins

Replace subset enumeration with construction from demands. For a prime
goal `F` the join `⋈^At` needs premises `σ_j = Σ_j ; Θ_j → A_j` with

    (J1)  Σ_i ⊆ Σ_j ∪ Θ_j   (i ≠ j),
    (J2)  Y ⊃ Z ∈ Σ^imp  ⟹  Y ∈ Υ = {A_1, …, A_n}.

So (J2) is a *demand on `Υ`*, and `Υ` is exactly the multiset of premise
right-formulas. That gives a worklist algorithm instead of a power set:

1. start from the cell(s) that carry the content the parent needs
   (the `F`-refuting cell, or the cells supplying the retained
   implications);
2. read off the unmet demands: every stable `Y ⊃ Z` whose `Y ∉ Υ`;
3. **look up** cells with `rhs = Y` in an index keyed by right formula,
   add one, recheck (J1) by bitmask containment;
4. iterate to fixpoint or to a bound; fail fast when a demand has no
   supplier.

Each join is then built in time proportional to the number of demands,
and the number of *constructed* joins is bounded by the number of
distinct conclusion contexts — i.e. by the state space, not by
`C(|IS|, k)`. The same repair loop covers `⋈^∨` (`C₁, C₂ ∈ Υ`), `⋈^◯`
(`Z ∈ Υ`), and the promise variants (add (J5): body `Y ∈ Cl(Δ_i)` for
some component, so index components by `Cl`-closure bitmask).

This is not a heuristic: it is the same reasoning the completeness
construction performs when it takes `U := C :: upsPrime` in
`metR_prime` (`FRJ/Saturate.lean`). The construction knows which cells a
join needs; the engine currently guesses.

### 4.3 Two layers, and where `partial def` is forced

**Layer 1 — cell library, forward, incremental.** Keep saturation for
the irregular cells, but as a *given-clause* loop: a queue of unprocessed
cells; pick one; combine it only with already-processed cells, through
the indexes of §4.2; insert with subsumption; never recompute a
combination. Bounded by the (small) irregular state space, cached per
goal `G`.

**Layer 2 — goal-directed backward search.** For the actual question
`Provable G`, recurse on the goal:

    refute? : Budget → Tag → Ctx → Form → Option (FRJr G t Γ C)

with the last-rule cases: `axR`; `andR1/2`; `impIn` (side condition
`A ∈ Cl(Γ)`, a bitmask test); `circIn` (tag test); and the joins, built
by §4.2 from Layer 1's library. Memoise on `(rhs index, ctx bitmask,
tag)` with **dominance**: a hit at `Γ' ⊆ Γ` serves `Γ` (contexts are
monotone in the calculus — this is the existing `rsLe`), and a *failure*
at budget is recorded separately from a failure at fixpoint, because
only the latter is informative.

`partial def` is not laziness here, it is forced, and for a reason worth
stating: the demand graph has genuine cycles — the same
irregular↔regular cycle that refutes a structural completeness induction
(`docs/frj-w4.md` §9, the measure dichotomy). There is no lexicographic
measure to recurse on, so the searcher is a fuelled `partial def` whose
*results* are typed derivations. Soundness survives exactly because the
return type is the derivation, as in `PLLG4Term.proveM`.

**Recommended split:** Layer 1 + §4.2 first (it is a rewrite of the cost
model inside the existing, faithful engine, with the corpus as its
regression test), Layer 2 second (it changes the interface to
goal-directed and is where the big constant-factor win for *hard* goals
lands).

### 4.4 Module layout and API

    FRJ/Search/Index.lean    -- zones as bitmasks, per-goal tables, Cl cache
    FRJ/Search/Cells.lean    -- Layer 1: given-clause irregular library
    FRJ/Search/Join.lean     -- demand-driven join construction (§4.2)
    FRJ/Search/Find.lean     -- Layer 2: partial def refute?, memo + budget
    FRJ/Search/Report.lean   -- verdicts, caps, counters, model round-trip
    wip/frjfind.lean         -- lean_exe frjfind: corpus, bench, differential

Entry points, mirroring the repo's existing shapes:

    def find?        (G : Form) : Option ((t : Tag) × (Γ : List Form) × FRJr G t Γ G)
    def findBounded  (budget : Nat) (G : Form) : Option (…) × Nat   -- remaining fuel
    def countermodel (G : Form) : Option Kripke                     -- via FRJ/Extract
    def verdict      (G : Form) : Verdict                           -- with reasons + caps

`findBounded` returning the *remaining* budget is the `PLLSearch`
convention that lets a caller distinguish "exhausted" from "searched
out" — the distinction the verdict discipline (§6) turns on.

## 5. What §15 changes for testing

`docs/frj-w4.md` §15 (branch `frj-deslime`, merged) closes the ◯-corner
kernel on cone-grounded frames and proves, unconditionally,

    completeness_of_rmFull_of_circFreeL :
        (∀ a b, a ≤ b → Rm a b) → (∀ X ∈ Sf^L(G), X.isCirc = false) →
        ¬ K.valid G → Provable G

That is a **new oracle class for the test harness**: on `Rm = ≤` models,
every goal with no negative-polarity subformula headed by `◯` that has a
countermodel *must* be found. 21 of the 32 corpus cells qualify (against
3 that are wholly ◯-free), so a miss there is an ENGINE BUG, provably —
not a frontier flag. This is what makes serious differential testing
possible for the first time.

## 6. Test scaffolding

**Verdict vocabulary** (Matthew's standing correction, 2026-08-17;
`wip/frj_sat.lean` still prints the old one at line 814): no `CERTAIN`
category. A rule-closure fixpoint is `no-derivation-at-fixpoint`, never
"underivable" — it is only as strong as the instantiation enumeration.
Where a theorem decides the question, use the theorem and print
**ENGINE-BUG** on a fixpoint without derivation.

**Four oracles, in increasing strength:**

1. **◯-free goals** — `FRJ.completeness` (`FRJ/Minimal.lean`) decides:
   IPL-refutable ⟹ must be found. Build the standing regression corpus
   here (IPL-refutable formulas from small countermodels); this is the
   oracle that would have caught the `⊃∉` zone-enumeration gap without a
   hand trace.
2. **`Sf^L`-circ-free goals** — §15's theorem, as above.
3. **Differential vs `PLLSearch.verdict`** — a hit ⟹ PLL-underivable, so
   the two-sided engine must *not* prove it; conversely every
   PLL-derivable control must never be hit (soundness is a theorem, so
   this tests the implementation, not the logic).
4. **Model round-trip** — for every hit, run `FRJ/Extract` to `Mod(D)`,
   evaluate the goal at the root, and check the refutation by `decide`
   (and cross-check with `Reject.certifies` where the shapes align). An
   independent audit of every reported countermodel.

**Generation:** stratified frontier sampling (`tools/FrontierSampler`,
the standing four directions of CLAUDE.md — corpus replay, boundary
cells, frontier extension, branch coverage), plus Plausible for
random-only. Normalise cells through `Rewrite.simplifyWith
Rewrite.fullSetC` before searching, per the standing rule.

**Measurement:** per cell report time, states visited, rule instances
attempted, memo hit rate, peak library size, and **every cap that
bound** (no silent caps — including `seedsIC`'s 4-atom cap, which is
currently unreported). Bench mode compares against the current `frjsat`
on the same corpus: the acceptance criterion for the rewrite is
order-of-magnitude, not percentage.

## 7. Milestones

1. **Index + bitmask contexts** inside the existing engine; corpus must
   stay 31 pass / 5 control-ok, wall clock drops. (Half a day.)
2. **Demand-driven joins** (§4.2) replacing `famsUpTo`; same corpus,
   plus the ◯-free regression corpus from §6.1. This is the change that
   matters. (A day.)
3. **Given-clause loop** (Layer 1 incremental). (Half a day.)
4. **`partial def` backward searcher** (Layer 2) with memo + budget, and
   `findBounded`'s remaining-fuel convention. (A day.)
5. **Harness**: four oracles, differential runner, bench, cap reporting,
   verdict vocabulary fixed. (A day, overlappable with 1–4.)

## 8. Risks

- **Search incompleteness is invisible without oracles.** Mitigated by
  §6.1/§6.2, which is why the oracle work is not optional extra.
- **Unbounded promise arity.** PLL needs arbitrary `k`
  (`docs/frj-lifting.md` §3); iterative deepening on arity, with the
  bound reported per cell.
- **Dominance subsumption must stay sound for the `⊃∉` `hAnot` gate** —
  the one non-monotone consumer, already noted in the engine's header.
  Any new indexing must preserve that exception.
- **The calculus is still moving** (§15's frame conditions; the pledge
  encoding under review per the canonical-model comparison). Keep the
  search layer thin over `FRJ/Calculus.lean` so a rule change is a local
  edit, and keep every row derivation-carrying so a rule change cannot
  silently invalidate results.
