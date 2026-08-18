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

### 4.3 One layer: relevance-restricted FORWARD saturation

*(Revised 2026-08-18 after Matthew's comment A.  The first draft of this
section proposed a second, goal-directed BACKWARD layer.  That was wrong,
and the reasons are worth recording because they are structural, not
stylistic.)*

FRJ(G) is a forward calculus and the search has to stay forward.

1. **The joins compute their conclusion's context from the premises.**
   `joinCtxAt` and its siblings are unions, intersections and restrictions
   over the whole premise family.  Read backwards, a join asks for a family
   of unknown size whose union-and-intersection equals a given context:
   inverting an intersection means guessing supersets.  Forwards the
   context is computed; backwards it is an inverse image.

2. **The question does not fix the context.**  `Provable G` is
   `∃ t Γ, FRJr G t Γ G`: tag and context are existentially quantified
   OUTPUTS.  A recursion keyed on `(t, Γ, C)` solves a strictly harder
   problem than the one asked.

3. **The only goal-directed recursion in the development is driven by a
   model.**  `visit` in `FRJ/Saturate.lean` knows, at every step, which
   world refutes what, and that is what selects the premise family.  In a
   search there is no model in hand, so nothing drives the recursion.

What survives is the useful half, under its proper name: **relevance
restriction**, the set-of-support strategy.  Every inference stays forward
(premises → conclusion, derivations built bottom-up); the goal is used only
to decide which forward inferences are worth performing, through the
indexes of §4.2, and a given-clause queue orders the work.  §4.2's
demand-driven join construction already carried this content; only the
control structure around it was wrong.

**Consequently `partial def` is NOT forced by the §9 measure dichotomy.**
That argument belonged to the backward reading.  A saturation loop needs
`partial def` (or fuel, which is what the current engine uses) for the
ordinary reason: its termination measure is "rows not yet produced, modulo
subsumption", which Lean cannot see.  The implemented engine keeps the
existing fuelled-rounds shape, so it is not `partial` at all — the
`partial def` question can be deferred until iterative deepening on join
arity needs it.

**What was implemented** (`FRJ/Search/Fast.lean`) is three exact cuts, none
of which changes the fixpoint:

* **J1 is pairwise, so admissible families are cliques.**  The side
  condition `∀ i j, i ≠ j → Σᵢ ⊆ Σⱼ ∪ Θⱼ` is a conjunction over ordered
  pairs, so a family passes iff every two-element subfamily does.
  `famsUpToC` enumerates cliques of the compatibility digraph instead of
  enumerating all `C(|Σ|, ≤ jmax)` subsets and rejecting most afterwards.
* **`J1`/`J2` do not mention the promise family.**  `mkJoinP` re-ran
  `j1j2Check` once per promise family; `mkJoinPFam` runs it once per
  premise family and then loops.
* **A family with no new member was already tried.**  Given-clause
  incrementality, sound because subsumption is transitive: anything
  subsumed at insertion stays subsumed.

Measured on the RN(◯,{}) bank: **10.3× on the hardest cell** (164 s → 16 s,
`cAnd_10_13`), 6× on the four known-false cells, with identical verdicts,
identical round counts and identical database sizes against the frozen
reference engine.

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

## 5. What §15 changes for testing — and what it does not

*(Revised 2026-08-18 after Matthew's comment B.)*

§15's new unconditional row is `Rm = ≤` with `Sf^L(G)` circ-free.  It is a
usable regression oracle, but it must not be sold as modal reach, because
on that frame class the modality is not primitive.  Machine-checked
(`FRJ.circ_iff_nn`, checks against `FRJ.Basic`): on an infallible model
with `Rm = ≤`,

    a ⊩ ◯A   ↔   a ⊩ ¬¬A

so a goal with no negative-polarity `◯` is equivalent to its
double-negation translation and plain FRJ handles it.  The sharper way to
say what is settled: **every settled row of the completeness map is a row
where `◯` is definable from the intuitionistic connectives** — `Rm = id`
gives `◯A ≡ A` (route (E), `FRJ/Erase.lean`), `Rm = ≤` gives `◯A ≡ ¬¬A`
(§15) — and `discrete_of_transparent_of_coneGrounded` says the two meet
only in the discrete case.  What is open is exactly `id ⊊ Rm ⊊ ≤`.

Every test of REACH therefore has to live strictly between the two
collapses.  The RN(◯,{}) bank does, and provably so: closed IPC formulas
are each provable or refutable, so under `◯ := ¬¬` the whole variable-free
fragment collapses to two classes, while RN(◯,{}) has at least sixteen.
Every RN separation needs `Rm ⊊ ≤`.

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

## 7. Milestones — reordered per comment C, with status

Generation first, aimed at the RN(◯,{}) ladder, because that is where the
engine does mathematics rather than regression.

1. **The bridge** `FRJ/Bridge.lean` — `PLLFormula ≅ Form`, every
   `FRJ.Kripke` is a `PLLND.ConstraintModel`, and hence an FRJ(◯)
   derivation refutes the ORIGINAL judgment
   (`not_derivable_of_provable`, `not_entails_of_countermodel`).
   Choice-free; `force_toConstraint` is axiom-free.  **DONE.**
2. **The oracle bank** `wip/rnBank.lean`, generated from the certified
   dictionary by `tools/rn-bank-gen.sh`: 323 cells tagged `proved` (236),
   `refuted` (4), `open` (83), two search goals each.  **DONE.**
3. **The harness** `lake exe rnfrj`, grading every cell against what the
   repository already knows, with the standing verdict vocabulary and an
   `--engine=fast|ref` differential switch.  **DONE.**
4. **The fast engine** `FRJ/Search/Fast.lean` (§4.3).  **DONE**, 6–10×,
   verdicts identical to the frozen reference.
5. **Pinning** `FRJ/Search/Pin.lean` + `lake exe rnpin`: extract the model
   the derivation builds, minimise it greedily, emit it as Lean source, and
   re-check by `decide`.  **DONE** — 13-world extractions minimise to 5–8
   worlds, which is what makes the kernel check affordable.
6. **Run the bank; pin every hit.**  IN PROGRESS — see §9.
7. Iterative deepening on join arity for the cells still open at budget;
   `partial def` if the arity loop needs it.
8. Stratified frontier generation beyond the dictionary (the standing four
   directions), once the ladder work is banked.

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

## 9. Results — the stack, end to end, on the oracle bank

Built and run 2026-08-18.  Every number below is measured, not projected.

### 9.1 The stack

    PLLFormula ─ FRJ/Bridge.lean ──────────→ FRJ.Form, FRJ.Kripke
      (original)   ofPLL / toPLL, isomorphic       (the calculus's own)
                   Kripke.toConstraint, force agrees
                   ⟹ a derivation refutes the ORIGINAL judgment

    wip/rnDict.lean ─ tools/rn-bank-gen.sh ─→ wip/rnBank.lean
      (certified dictionary)                    323 cells, tagged

    wip/rnBank.lean ─ lake exe rnfrj ────────→ graded verdicts
      --engine=fast|ref, four oracles, standing verdict vocabulary

    FRJ/Search/Engine.lean  (frozen reference, ported from wip/frj_sat.lean)
    FRJ/Search/Fast.lean    (cliques + hoisting + incrementality)

    hit ─ lake exe rnpin ───────────────────→ model, minimised, as source
    FRJ/Search/Pin.lean: Tab, okB, toKripke, restrict, minimise, render

    tools/rn-cert-asm.py ──────────────────→ wip/rnFRJCerts.lean
      decide the frame, decide the refutation, ¬ Interd by the bridge

### 9.2 Speed

| goal | reference | fast | ratio |
|---|---|---|---|
| the four known-false cells (8 goals) | 16.3 s | 2.7 s | 6.0× |
| `cAnd_10_13` (the first new refutation) | 164 s | 15.9 s | **10.3×** |

Identical verdicts, identical round counts, identical database sizes.

### 9.3 The oracles

Full bank, fast engine, base budget (`rounds=10 jmax=3 pmax=2 lamCap=10
maxRS=maxIS=800`), 323/323 cells, 2081 s wall:

    ENGINE-BUG=0  control-ok=236  pass=4  miss=0
    NEW-REFUTATION=16  open-still=67

* **Must-not-refute** (236 `proved` cells, kernel-checked `Interd`):
  **zero** ENGINE-BUGs.  The engine never produced a typed derivation
  against a cell the kernel has already proved.
* **Must-refute** (4 cells known FALSE at ≤4 worlds): **4/4**, no misses.
* **Differential** (fast vs frozen reference): **77 cells / 154 goals,
  zero disagreements**, at cell-verdict and per-goal level.
* **Degeneracy control**: each emitted model must still force `q1 = ⊤`
  (`decide`), so a machinery that made everything false would fail here.
  16/16.
* **Retarget control**: `--cand=1` reproduces all eleven hits whose
  stated candidate is `q1`, so the candidate-override path agrees with
  the stated goals.

Of the 67 still open, 24 stopped at budget rather than at a fixpoint.
Re-run at `lamCap=16` (§9.6) all 24 reach a fixpoint and none is refuted,
so no verdict on this bank now rests on a budget.  A fixpoint means no
FRJ(◯) derivation exists within the relevance restriction: evidence for
the cell, not a proof of it.

### 9.4 The mathematics

Sixteen `open` cells of the RN(◯,{}) dictionary are now **kernel-checked
FALSE**, sorry-free, `[propext, Quot.sound]` — no `Classical.choice`, no
`native_decide`:

    cAnd_10_13  cAnd_11_13
    cOr_8_10   cOr_8_11   cOr_8_12   cOr_8_14
    cOr_10_12  cOr_10_14  cOr_11_12  cOr_11_14
    cImp_8_4   cImp_8_5   cImp_10_7  cImp_11_7  cImp_12_11
    cBox_11

The extracted models have up to 13 worlds; minimised, **twelve have 5
worlds and four have 8**.  That is why these cells were open: the
exhaustive ≤4-world battery cannot reach them, and FRJ(◯)'s model size
is bounded by the derivation, not by an enumeration bound.  This is the claim "more efficient than brute force"
discharged on a workload where brute force had already stopped.

Consequence for the dictionary — stated carefully, because the cells are
not all of one kind.  Each open cell of `wip/rnDict.lean` carries a
CANDIDATE LIST and is sorried at the first open candidate, so refuting
the stated collapse eliminates ONE candidate and closes the cell only
when that candidate was the last.  Five of the sixteen were sorried at
their last candidate and so close immediately: `cAnd_10_13` [10],
`cImp_8_4` [5], `cImp_8_5` [5], `cImp_10_7` [7], `cImp_11_7` [7].  The
other eleven all had candidates [1, 11, 13] and were refuted at `q1`
only, which is what §9.5 goes after.

### 9.5 Walking the candidate list — `--cand=K`

`lake exe rnfrj --cand=K` retargets a cell at representative `qK` instead
of the one the table assigns; `lake exe rnpin … K` pins the result.  The
control is that `--cand=1` reproduces all eleven `q1` hits.  Running the
eleven narrowed cells against their two survivors:

| cell | `q1` | `q11` | `q13` | outcome |
|---|---|---|---|---|
| `cOr_10_12`  | ✗ | ✗ | ✗ | **closure FAILS** |
| `cOr_11_12`  | ✗ | ✗ | ✗ | **closure FAILS** |
| `cImp_12_11` | ✗ | ✗ | ✗ | **closure FAILS** |
| `cBox_11`    | ✗ | ✗ | ✗ | **closure FAILS** |
| `cOr_8_10`   | ✗ | survives (fixpoint) | ✗ | `q11` only |
| `cOr_8_11`   | ✗ | survives (budget) | ✗ | `q11` only |
| `cOr_10_14`  | ✗ | survives (budget) | ✗ | `q11` only |
| `cOr_11_14`  | ✗ | survives (budget) | ✗ | `q11` only |
| `cAnd_11_13` | ✗ | ✗ | survives (budget) | `q13` only |
| `cOr_8_12`   | ✗ | ✗ | survives (budget) | `q13` only |
| `cOr_8_14`   | ✗ | survives (budget) | survives (budget) | `q11`, `q13` |

Four more cells therefore have NO surviving candidate, each recorded as a
single kernel-checked conjunction

    <cell>_no_candidate :
      ¬ Interd lhs q1 ∧ ¬ Interd lhs q11 ∧ ¬ Interd lhs q13

`[propext, Quot.sound]`.  Its scope is exactly the three candidates it
names: the other twelve representatives were eliminated by the ≤4-world
battery that produced the candidate list in the first place, and that
elimination is recorded in `wip/rnDict.lean`, not re-proved here.

**Running total: the fifteen-representative closure fails at THIRTEEN
cells** — the four already known, the five of §9.4, and these four.

The seven cells with a survivor are narrowed, not settled, and six of
those seven survivals are at budget rather than at a fixpoint.

### 9.6 The frontier, and where the budget actually binds

Twenty-four of the 67 still-open cells stopped at budget, not at a
fixpoint.  The first escalation guess — raise `jmax` to 4 — was wrong,
and measurably so: those cells stopped at rounds 6–8 out of 10, with
|RS| ≤ 37 and |IS| ≤ 86 against caps of 800.  Neither the round limit
nor the database caps were binding; `lamCap` was.  Raising `lamCap` from
10 to 16 and changing nothing else, **all 24 convert from
"no-derivation-at-budget" to a genuine fixpoint, with zero new
refutations** (729 s).  So the frontier on this bank is now clear: every
one of the 67 open cells reaches a fixpoint, and no cell's verdict rests
on a budget.  That is the difference between a frontier marker and a
settled cell, and it is why the vocabulary keeps them apart.

Also on the record, per the no-silent-caps rule: `seedsIC` enumerates the
full valuation lattice only while |Ĝ_at| ≤ 4 and tries three valuations
above that.  The harness now prints which case it is in.  On RN(◯,{}) it
prints |Ĝ_at| = 0 — the fragment is variable-free, so the cap never bit
on this campaign.

### 9.7 What this does not show

The engine is SOUND, not known complete: `no-derivation-at-fixpoint`
means no FRJ(◯) derivation exists within the relevance restriction, which
is evidence about a cell and not a proof of it.  Completeness — statement
(A) — remains OPEN, and nothing here bears on it.  What the campaign does
establish is the weaker and still useful claim the design set out to
test: used purely as a countermodel finder, FRJ(◯) reaches models that
the exhaustive small-model battery cannot, on a workload where that
battery had already stopped.
