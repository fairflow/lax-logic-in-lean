# The subset blowup in FRJ(◯) search is a REPRESENTATION artefact

**Status: BOTH LEMMAS PROVED, ENGINE BUILT AND DIFFERENTIALLY TESTED
(2026-08-21).**  `FRJ/Profile.lean`: 43 theorems, 0 sorries, choice-free
(`[propext, Quot.sound]`, and `[propext]` alone for the two `restrict`
congruences).  Engine: `FRJ/Search/Profile.lean`, alongside `Fast` and the
frozen oracle, neither of which changed.  Results at the foot of this
file.  The factorisation below was originally read off the definitions in
`FRJ/Calculus.lean` and stated as an obligation; it is now discharged.  Written 2026-08-21 in answer to:
*is the blowup inevitable in FRJ(◯) as a calculus, or is it a consequence
of how the subsets are represented in Lean?*

## The measurement that provoked the question

`lake exe rnfrj --limit=60` (120 goals) at default settings:

| | |
|---|---|
| goals where the arity caps bound the search | **119 / 119** negatives |
| worst cell `cAnd_8_11` | `IS=61 fam=14748 pfam=406`, 41 s |
| default arity caps | `jmax = 3`, `pmax = 2` |

FRJ(◯) is forming premise families of size ≤ 3 out of 61 available rows,
materialising 14748 of them per round into a strict `List`.  Nothing
about the search is lazy or shared.

## What the calculus actually depends on

Every join rule (`joinAt`, `joinAtF`, `joinAtP`, `joinOr`, `joinOrF`,
`joinOrP`, `joinCirc`, `joinCircP`) takes a premise family

    prem : ∀ j : Fin (n+1), FRJi G (stab j) (th j) (rhs j)

and its conclusion context is built ONLY from unions and intersections
over that family.  `FRJ/Calculus.lean:125`:

    joinCtxAt stab th rhs F  =  ⋃ⱼ atPart(stab j)
                             ++ rm (⋂ⱼ atPart(th j)) F
                             ++ ⋃ⱼ impPart(stab j)
                             ++ restrict (⋂ⱼ impPart(th j)) (upsilon rhs)

and likewise `joinCtxOr` (:133), `joinCtxCircP` (:143), `joinCtxCircF`
(:150); the P- and F- variants are these composed with the filters
`restrictP` / `restrictC`, which are per-formula and do not touch the
family structure.

The side conditions factor the same way:

| condition | depends on |
|---|---|
| `hJ1 : ∀ i≠j, stab i ⊆ stab j ++ th j` | PAIRWISE — the family is a clique |
| `hJ2 : imp A B ∈ ⋃ⱼ impPart(stab j) → A ∈ upsilon rhs` | ⋃ stab, Υ |
| `hcirc : ⋃ⱼ circPart(stab j) = []` | ⋃ stab |
| `hFnot : F ∉ ⋃ⱼ atPart(stab j)` | ⋃ stab |
| `hJ5 : circ Y ∈ ⋃ⱼ circPart(stab j) → ∃i, Clo (Δs i) Y` | ⋃ stab, Δ⃗ |
| `hJ7s : ∀ i j, ∀ X ∈ stab j, Clo (Δs i) X` | ⋃ stab, Δ⃗ |
| `hC : C₁, C₂ ∈ upsilon rhs` | Υ |

Since `atPart` / `impPart` / `circPart` are filters by a predicate on the
formula alone, they commute with ⋃ and ⋂.  So the six zone aggregates
collapse to three sets, and everything above is a function of

    Σ := ⋃ⱼ stab j        Θ := ⋂ⱼ th j        Υ := { rhs j }

## The Profile Lemma (TO BE PROVED)

Add one more aggregate to capture J1-extendability:

    M := ⋂ⱼ (stab j ++ th j)

Then for a candidate row `b` and a J1-clique `K`:

    K ∪ {b} is a J1-clique   ⟺   b.stab ⊆ M  ∧  Σ ⊆ b.stab ++ b.th

*(⊆ M is `∀k∈K, b.stab ⊆ k.stab ++ k.th`; the second conjunct is
`∀k∈K, k.stab ⊆ b.stab ++ b.th`, i.e. `⋃ₖ k.stab ⊆ b.stab ++ b.th`.)*

Define the **profile** of a family to be

    P := (Σ, Θ, M, Υ)

**Lemma (to prove).**  For each join rule R there is a function `conclR`
with

    conclusion-row of R on family 𝔉  =  conclR (P(𝔉), F)

and R's side conditions hold of 𝔉 iff they hold of `P(𝔉)`.  Hence two
families with the same profile
(a) produce the SAME conclusion row, and
(b) admit exactly the SAME extensions.

(b) is the part that makes merging safe.  Without it, discarding a family
could discard the only one extendable by some later row.

## The algorithm this licenses

Replace clique enumeration with a **monotone worklist fixpoint over the
profile lattice**, hash-consed on P:

1. Seed: one node per row `a ∈ db.is`, with `P = (a.stab, a.th,
   a.stab ++ a.th, {a.rhs})` and witness family `[a]`.
2. Step: for node `(P, K)` and row `b` with `b.stab ⊆ M` and
   `Σ ⊆ b.stab ++ b.th`, form
   `P' = (Σ ∪ b.stab, Θ ∩ b.th, M ∩ (b.stab ++ b.th), Υ ∪ {b.rhs})`.
3. **If `P'` is already in the table, discard** — keep the first witness.
   Otherwise add `(P', b :: K)` to the worklist.
4. Iterate to fixpoint; emit one conclusion row per reachable profile.

Every component is monotone along an edge: Σ and Υ grow, Θ and M shrink.

### Why this is the BDD analogy made precise

The sharing is the same idea: many syntactically distinct objects (here,
families; there, sub-formulas) collapse onto one canonical node, and the
node is reached once and reused.  What plays the role of the variable
order is the monotone direction of the lattice.

### What it buys

* **Cost is bounded by the number of reachable PROFILES, not by the
  number of subsets.**  Σ, Θ, M, Υ are all sublists of the goal's
  subformula universe `sf(G)`, so the bound is a function of the GOAL,
  independent of the database size `n`.  Today the cost is `O(n^jmax)`
  with `n = 61`.
* **`jmax` disappears.**  The fixpoint terminates because the lattice is
  finite, not because arity was capped.  That removes the truncation
  measured above at 119/119, and would make `closed-no-cap-bound` a
  reachable outcome on dictionary cells, which it currently is not.
* **It is a strict generalisation**: unbounded arity, which
  `docs/frj-lifting.md` §3 says full PLL needs.

### Why it stays sound and faithful

Soundness is `FRJ.soundness`, a theorem about DERIVATIONS.  This changes
only which derivations are constructed: every emitted row still comes
from a real family satisfying the real side conditions, and the witness
family builds the actual rule term.  Nothing is weakened, and nothing new
is asserted.

The one thing merging discards is ALTERNATIVE DERIVATIONS of the same
row.  That is safe for search because every later rule consumes a row —
its tag, context and rhs — and never the derivation term.  It is not
neutral for EXTRACTION: different derivations give different countermodels
via `modR`, so keeping the first witness may not give the smallest model.
`Tools/Cert.lean` already minimises afterwards, so this is a quality
question, not a soundness one.

## What is already done, and what is new

`FRJ/Search/Fast.lean` has two of the moves already:

* `cliquesLe` / `famsUpToC` (:72, :83) enumerate J1-CLIQUES rather than
  all subsets, checking each candidate against the whole committed clique
  — the pairwise reading of J1;
* `pfamsOf` (:274) filters `db.rs` by J7 BEFORE enumerating promise
  families, rather than enumerating and rejecting.

Neither shares work between families.  The new ingredient is (b) of the
Profile Lemma: extendability depends only on `(Σ, M)`, which is what
turns clique enumeration into a fixpoint with merging.

## Obligations before any of this is believed

1. **Prove the Profile Lemma in Lean**, per rule.  The zone-filter
   commutation (`atPart (⋂ⱼ f j) = ⋂ⱼ atPart (f j)` and the ⋃ dual) should
   be `simp`-level; the J1-extendability equivalence is the real content.
2. **Differential test against the frozen oracle.**  `wip/frj_sat.lean`
   is the frozen reference implementation and exists for exactly this.
   The new engine must agree with `saturate` row-for-row on the corpus
   before it replaces anything.
3. **Re-measure.**  `enginecmp` is deferred but MUST be revisited; this
   is the change that would date any measurement taken before it.


---

# RESULTS (2026-08-21)

## Differential test — the correctness question

`lake exe frjdiff --bank --limit=120`, every goal run three ways: `Fast`,
the profile engine at MATCHED arity (`jmax-1` / `pmax-1` layers), and the
profile engine UNCAPPED.

    120 ⇒ agree        DEFECTS=0        profile-finds-more=0

Both engines found the same single refutation across the 120 goals, so
nothing was lost.  Matched arity isolates the MERGING from the extra
reach; it agrees too, which is what says the merging itself is sound in
practice and not merely licensed on paper.

## Cost — the bank

| | Lemma 1 only | Lemma 1 + Lemma 2 |
|---|---|---|
| `Fast` | 836.8 s | 856.9 s (same run, ±2% noise) |
| matched arity | 70.9 s | **45.0 s** |
| profile, uncapped | 127.6 s | **63.8 s** |
| families (irregular) | 321530 → 17278 | unchanged (Lemma 2 acts on `pfams`) |

**13.4x over `Fast` overall**, 18.6x fewer irregular families.  Lemma 2
was worth doing: it doubled the engine, even though it also RAISED
promise arity from 2 to unbounded.  That was not predictable in advance
and was measured, not guessed.

Worst bank cells, `Fast` -> `Profile`:

| cell | `Fast` | `Profile` |
|---|---|---|
| `cAnd_8_11←` | 133 s, 14748 families | 10.0 s, 983 |
| `cAnd_8_11→` | 104 s, 2010 | 6.2 s, 339 |
| `cAnd_7_8←` | 101 s, 9478 | 18.5 s, 833 |

## Cost — past the bank

`lake exe frjhard`, an escalation ladder built to exceed the bank's
hardest cell.  One engine per invocation, process-level timeout
(Lean cannot interrupt a pure computation).  **Uncontended measurements**
— an earlier set was contaminated by a concurrent run and read ~4x slow.

| goal | \|G\| | `Fast` | `Profile` | |
|---|---|---|---|---|
| H1 `(q8∧q11) ⊃ q15` | 51 | 51.8 s, 2397 fams | **0.87 s**, 356 fams | **59x** |
| H2 `(q8∧q11∧q13) ⊃ q15` | 66 | 191.8 s, 5243 fams | **2.69 s**, 551 fams | **71x** |
| H3 `(q8∧q11∧q13∧q14) ⊃ q15` | 82 | TIMEOUT > 180 s | **6.54 s**, 1036 fams | **> 27x** |
| H4 `((q8∧q11) ⊃ (q13∧q14)) ⊃ q15` | 82 | TIMEOUT > 180 s | TIMEOUT > 60 s | — |
| H6 `(q8∧…∧q15) ⊃ q10` | 92 | not run | **1.75 s**, 87 fams | — |

Both engines reach the SAME database on H1 and H2 (`RS=25 IS=29` and
`RS=25 IS=37`, `r=8/10`) and return the same verdict.  H6 is the LARGEST
goal and among the fastest: size is not what drives the cost, structure
is.

`TwoSidedLink.searchProves` (the proof engine) times out at 180 s on
H1-H3 — the known expensive-failure mode, since an LJF◯ `false` certifies
nothing and the fuel ladder must be walked to the end.  On this ladder
the profile engine is the only tool that reaches.

## What is now the binding cap

Not arity.  With `jmax` and `pmax` both eliminated, the profile engine
reports `caps=lamCap` on every rung of the ladder — the `⊃∈I` cap inside
`stepImpInI`, default 10.  `rounds` never exhausted (`r=8/10`) and
`maxRS`/`maxIS` were never approached (25-54 against 800).

So a `closed-no-cap-bound` outcome is still NOT reachable on goals of this
size, and the reason has moved: it used to be the arity caps, it is now
`lamCap` alone.  That is the next thing to attack for anyone who wants
`Certified.SearchComplete` or the `none_ex` verdict to become inhabitable.

## What is still NOT claimed

That the engine is complete, or that FRJ(◯) is.  `Certified.CompletenessFRJ`
and `Certified.SearchComplete` are both OPEN, and `FRJ/Saturate.lean` —
the W4 completeness campaign — does not import the search at all, so none
of this bears on them.  What changed is cost and the honesty of the
bound, not the logic.


---

# NOTES FOR FUTURE WORK (Matthew, 2026-08-22)

## 1. Unify the Kripke-constraint-model definitions; do not bridge them

There are two definitions of the same concept — `FRJ.Kripke` (`FRJ/Basic.lean`)
and `FinCM` / `ConstraintModel` (`LaxLogic/`).  Checked 2026-08-22: **no
`FinCM → FRJ.Kripke` map exists.**  What exists runs the other way,
`FRJ.Bridge.Kripke.toConstraint` (`FRJ/Bridge.lean:78`), plus
`P.toKripke` in `FRJ/Sound.lean` which converts a PRE-MODEL, not a
`FinCM`.

Matthew's instruction: there is little point in multiple definitions of
one concept, so the fix is UNIFICATION, not another bridge.  Deferred.

**Why it matters now.**  On 2026-08-22 the incompleteness miner produced
its first candidate:

* `H1 := (q8 ∧ q11) ⊃ q15` is PLL-UNDERIVABLE — G4c returns a checked
  3-world `FinCM`, and `PLLND.Search.refuted_sound` turns that into
  `[] ⊬ H1` in the kernel.
* FRJ(◯)'s saturation CLOSES on `ofPLL H1` with every cap slack
  (`lamCap=40` and `lamCap=200` give the identical `IS=89 fams=518`,
  `r=8/10`, `RS=25`, no arity cap) and constructs no countermodel.

Those two together refute `Certified.CompletenessFRJ` — EXCEPT that
`CompletenessFRJ` is stated as `¬ FRJ.PLL G → FRJ.Provable G`, and
turning `[] ⊬ H1` into `¬ FRJ.PLL (ofPLL H1)` needs exactly the missing
direction.  Unifying the two model definitions would supply it, and would
convert a measurement into a machine-checked incompleteness witness for
the W4 campaign.

Residual caveat even then: a cap-free closure depends on the subsumption
in `insertAllR`/`insertAllI` not over-subsuming, which is unproved.

## 2. There is no reliable `≺`, so the database must not store covers

A cover `a ≺ b` asserts that NOTHING lies strictly between `a` and `b`.
That quantifies over all classes, and RN(◯,{}) is PROVED INFINITE
(`closed_lax_infinite`) while the record holds only discovered
representatives.  So a cover can never be certified from this data.

`docs/rho-order.md`'s "37 cover edges" are covers RELATIVE TO the 22
known classes — a provisional judgement, not a theorem, and it is already
known that adding classes destroys covers: that document records seven of
the old 21 covers ceasing to be covers once eight new classes were placed.

Consequence for the database (Phase 3): store `<` as the fact, and expose
cover-ness only as a DERIVED VIEW relative to a named representative set
— the same discipline `Claim.scope` already imposes on negative claims.
Never write a cover down as an entry.
