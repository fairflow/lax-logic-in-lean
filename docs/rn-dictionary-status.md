# The RN(◯,{}) dictionary — what is certified, what is not

*2026-08-14. Written after the certified simpset was screened against
the dictionary it was harvested from, which turned up a defect in the
simpset and a misreading of the dictionary's own status.*

## The dictionary is PARTIAL, and says so

`wip/rnDict.lean` builds `rnDict15 : RNDict` — fifteen variable-free
representatives `q0…q14` with closure tables `andT`, `orT`, `impT`,
`boxT` and a per-cell `Interd` certificate. Of its **690 closure
cells, 603 are certified**; of the **323 stated cell theorems, 87 are
`sorry`**. The file's own doc comment is accurate about this; nothing
downstream had read it.

The 87 split two ways, and the distinction matters:

* **4 REFUTED** — certified ≤4-world countermodels eliminate *every*
  candidate representative, so the combination is a genuinely NEW
  class and the 15-representative closure **fails**. The stated
  collapse is FALSE; the `sorry` records where:

  | cell | claim | status |
  |---|---|---|
  | `cAnd_8_10` | `q8 ∧ q10 ⊣⊢ q0` | FALSE |
  | `cImp_9_4`  | `q9 ⊃ q4 ⊣⊢ q0`  | FALSE |
  | `cImp_12_4` | `q12 ⊃ q4 ⊣⊢ q0` | FALSE |
  | `cImp_14_4` | `q14 ⊃ q4 ⊣⊢ q0` | FALSE |

* **83 OPEN** — neither proved by either searcher nor refuted by the
  exhaustive ≤4-world battery. These are the target list.

The four refutations are the reason `rnDict15` is **not completable at
these fifteen representatives**, and they are consistent with the
closed-fragment catalogue: the variable-free fragment does not
collapse at any crank ≤ 7 (`docs/pcll-closed-fragment-catalogue.md`),
so no *finite* dictionary closes it. A 15-class closure table was
always going to break somewhere; these four cells are where.

## The defect this exposed in the simpset

`Rewrite/Catalogue.lean` (first cut, commit `8bb7ef4`) harvested all
323 cell theorems by name. That pulled in all 87 unproved ones,
including the four false ones. Consequences, both real:

* `#print axioms Rewrite.rndSet` reported **`sorryAx`**, and so did
  `fullSet` and everything normalised with it;
* four rules rewrote a formula to one **not interderivable with it**,
  so `norm`'s unconditional correctness theorem no longer applied to
  the set actually in use. `norm_interd` is unconditional *given* that
  each `RwRule.ok` is a proof — a `sorry`ed `ok` voids exactly the
  guarantee the design rests on.

**Fixed**: `rndSet` now carries the 236 proved cells only
(∧ 64, ∨ 46, ⊃ 121, ◯ 5), and `#print axioms rndSet` / `fullSet` are
pinned with `#guard_msgs` as a standing guard — a future harvest that
picks up an unproved cell now fails the build here rather than
silently in the results.

## The second defect: the canonicaliser was fighting its own rules

Screening the repaired set against the cells it *provably* closes gave
the control **47 / 237**. The pipeline was not firing on five sixths
of the facts it owned. Cause: `canon` sorts ∧/∨ arguments by `keyF`,
while the harvested rules were stated in the dictionary's argument
order, so canonicalising a goal moved it out of reach of the very
rules meant to fire on it. Two further sources of loss: a rewrite
inside an ∧-chain can leave the chain unsorted, and flattening can
expose new conjuncts, neither of which a single `norm` pass revisits.

**Fixed** in `Rewrite/Canon.lean`:

* `canonRule` / `canonSet` — put the rules through the same
  canonicaliser. Sound for free: `canon lhs ⊣⊢ lhs ⊣⊢ rhs ⊣⊢ canon rhs`.
* `simpIter` — alternate `norm` and `canon` to a fixpoint (4 rounds,
  stopping early when stable) instead of one pass of each.
* `simplifyWith rs n φ` against an already-canonicalised set, with
  `fullSetC := canonSet fullSet` computed once at top level.
  `simplify` remains as the convenience form but recomputes
  `canonSet` per call — do not use it in a sweep.

Control after the repair: **237 / 237**.

## Measured effect (`lean_exe rwscreen`)

| corpus | metric | before | after |
|---|---|---|---|
| flat, 330 cells | rewritten | 68% | **89%** |
| | crank reduction | 21% | **34%** |
| | distinct forms (from 319 raw) | 96 | **28** |
| nested, 3,996 ∧/∨ trees | distinct forms (from 3,996 raw) | 167 | **25** |
| | crank reduction | 23% | **40%** |

The nested figure is the one that matters for a sweep: 3,996
syntactically distinct trees, in both associations and both argument
orders, reduce to 25 forms to attack. The floor is 15 (the
dictionary's classes, which the ∧/∨ closure cannot leave), so the
pipeline is within 10 forms of the best a rewriter with these facts
could do.

## Can the method EXTEND the dictionary? No — and the negative is informative

`lean_exe rnextend` asks the natural question: does `simplifyWith`
close any of the 87 unproved cells for free? The test is syntactic
and therefore certifying — if `simplifyWith fullSetC n (qi ⊙ qj)` and
`simplifyWith fullSetC n qk` are the same formula, then
`Interd (qi ⊙ qj) qk` follows from `simplifyWith_interd` on both
sides with `Interd.symm`/`trans`, no search and no new axiom.

**Result: 0 of 87 settled**, with the control at 237/237 in the same
run — so the negative is a real measurement, not a broken pipeline.

Two checks make it trustworthy:

* the fifteen representatives stay **pairwise distinct** under the
  normaliser (15/15); a simpset that collapsed two of them would be
  reporting a defect, not a result;
* the four REFUTED cells are **not** matched to `q0`. Had the
  normaliser "settled" one of them it would have proved something
  false, and the run would be a soundness report.

Why the negative was predictable in hindsight: rewriting is
congruence closure over the banked equations, and the open cells are
by construction outside it — they are exactly the combinations no
chain of certified equations reaches. **Recombination cannot settle
them; only a new proof search or a ≥5-world countermodel can.** The
simpset's value is throughput on cells that *are* in the closure, and
there the gain is 5-fold.

## The standing item

Adopted 2026-08-14, at Matthew's direction: **whenever new certified
equations are banked, re-run this loop** —

1. `lake build rwscreen && .lake/build/bin/rwscreen` — effectiveness;
2. `lake build rnextend && .lake/build/bin/rnextend` — does the new
   material close any open dictionary cell, with the control and the
   two adversarial checks;
3. if any cell closes, promote it to a kernel-pinned theorem in
   `wip/rnDict.lean`, delete the corresponding `sorry`, re-harvest,
   and update `docs/pcll-closed-fragment-catalogue.md` and the RN
   explorer;
4. re-pin `#print axioms rndSet` / `fullSet` verbatim.

## The 83 open cells, as a target list

Distribution by table: ⊃ 43, ∨ 28, ∧ 14, ◯ 2 — the implication table
is where the dictionary is weakest, which is where a refutation
calculus (the `Reject/` thread) would bite. Every open cell is a
concrete, small, closed-fragment question with a known candidate
answer; each needs either a proof term or a ≥5-world confluent
countermodel. `wip/rn_extend.lean` holds them as machine-readable
data (`RnExtend.openCells`).

## Replay

    lake build rwscreen && .lake/build/bin/rwscreen
    lake build rnextend && .lake/build/bin/rnextend
    lake env lean Rewrite/Catalogue.lean     # the axiom pins
