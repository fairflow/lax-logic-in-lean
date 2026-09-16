# The order on the 22 closed-fragment classes

*2026-08-14. Computed by `lean_exe rhoorder` (`wip/rho_order.lean`),
engine comparison by `lean_exe rhoengines` (`wip/rho_engines.lean`).
Both are NEW files; nothing existing was edited, and the whole `LJF*`
tree was read-only throughout.*

`docs/pcll-closed-fragment-catalogue.md` certified 22 pairwise-distinct
`DerivU`-classes and then said, in terms:

> their identity against the k ≥ 2 members of the infinite families is
> UNCHARTED … so the PLL dictionary's Hasse diagram is not redrawn
> here — placing the new nodes needs their order cells, not yet
> computed.

This is those cells. **All 462 of them**, of which 460 are settled by
a certificate.

## Headline

The eight sweep discoveries are not appendages hanging off the known
lattice. They interleave with it: **7 of the 21 covering relations
among the old classes are no longer covers** once the new classes are
placed, and **two of the lattice's three co-atoms are new classes**.

| | old 14 classes alone | full 22 |
|---|---|---|
| cover edges | 21 | **37** |
| of which survive from the old diagram | — | 14 |
| atoms (upper covers of ⊥) | 2 | 2 |
| co-atoms (lower covers of ⊤) | 2 | **3** |

## Method and verdicts

For each ordered pair, `ρi ⊢ ρj` in `ConfluentU.DerivU`:

* **⊬** — separation on the battery (ALL well-formed mutually
  confluent frames on ≤ 4 worlds plus the canonical rooted 5-world
  orbits: 10,534 frames), i.e. a world forcing `ρi` and not `ρj`.
  That is exactly what `RNC.not_derivU_of_checkConf` consumes, so each
  is kernel-escalatable; `rhoorder pin` emits the pin lines.
* **⊢** — the positive tier ladder `decidePosT`, then `escalate`.
  Sound for `DerivU` by `RNC.derivU_of_proved`.
* **flag** — neither, at budget.

Separation is tried FIRST, so no search is spent on a cell the
battery already settles. That ordering is why the run costs 14
seconds rather than hours: 302 of 462 cells never reach a searcher.

**Result: 158 ⊢, 302 ⊬, 2 flags.**

## The matrix

Row `⊢` column; `1` certified derivable, `.` certified not (with a
countermodel), `?` flag.

```
        0123456789012345678901
ρ0      1111111111111111111111
ρ1      .1....................
ρ2      .11.111111111111111111
ρ3      .1.11.1111111111111111
ρ4      .1..1.1111111111111111
ρ5      .1...11..11111.1.11.11
ρ6      .1....1..11111.1.11.11
ρ7      .1.....1111.1..11.1111
ρ8      .1......1.1...........
ρ9      .1.......11.1..1..1.11
ρ10     .1........1...........
ρ11     .1.........1...1......
ρ12     .1..........1..?.....1
ρ13     .1.........111.1.....1
ρ14     .1......1.11..11111...
ρ15     .1.............1......
ρ16     .1......1.1....11.1...
ρ17     .1........11...1.11...
ρ18     .1........1....1..1...
ρ19     .1......1.1........111
ρ20     .1........?.........11
ρ21     .1...................1
```

## The covering relation (37 edges)

New classes marked ★.

| class | lower covers | upper covers |
|---|---|---|
| ρ0 = ⊥ | — | ρ2, ρ3 |
| ρ2 = ◯⊥ | ρ0 | ρ4, ρ5 |
| ρ3 = ¬◯⊥ | ρ0 | ρ4 |
| ρ4 = ¬◯⊥ ∨ ◯⊥ | ρ2, ρ3 | ρ6, ρ7, ρ14 |
| ρ5 = ¬¬◯⊥ | ρ2 | ρ6 |
| ρ6 = ¬¬◯⊥ ∨ ¬◯⊥ | ρ4, ρ5 | ρ9, ρ13★, ρ17★ |
| ρ7 = ◯¬◯⊥ | ρ4 | ρ9, ρ16★, ρ19★ |
| ρ8 = ¬¬◯⊥ ⊃ ◯⊥ | ρ16★, ρ19★ | ρ10 |
| ρ9 = ¬¬◯⊥ ∨ ◯¬◯⊥ | ρ6, ρ7 | ρ12, ρ18★, ρ20★ |
| ρ10 = (¬¬◯⊥ ⊃ ◯⊥) ∨ ¬¬◯⊥ | ρ8, ρ18★ | ⊤ |
| ρ11 = ◯¬◯⊥ ⊃ (¬◯⊥ ∨ ◯⊥) | ρ13★, ρ17★ | ρ15★ |
| ρ12 = (¬¬◯⊥ ⊃ ◯⊥) ⊃ ◯¬◯⊥ | ρ9, ρ13★ | ρ21★ |
| ρ13★ | ρ6 | ρ11, ρ12 |
| ρ14 = w1 | ρ4 | ρ16★, ρ17★ |
| ρ15★ = ρ11 ∨ ρ7 | ρ11, ρ18★ | ⊤ |
| ρ16★ = ρ14 ∨ ρ7 | ρ7, ρ14 | ρ8, ρ18★ |
| ρ17★ = ρ5 ∨ ρ14 | ρ6, ρ14 | ρ11, ρ18★ |
| ρ18★ = ρ14 ∨ ρ9 | ρ9, ρ16★, ρ17★ | ρ10, ρ15★ |
| ρ19★ = ρ11 ⊃ ρ7 | ρ7 | ρ8, ρ20★ |
| ρ20★ = ρ11 ⊃ ρ6 | ρ9, ρ19★ | ρ21★ |
| ρ21★ = ρ14 ⊃ ρ7 | ρ12, ρ20★ | ⊤ |
| ρ1 = ⊤ | ρ10, ρ15★, ρ21★ | — |

23 of the 37 cover edges touch a new class; 5 join two new classes.

## What the discoveries do to the old diagram

Seven covering relations among the fourteen old classes are **not**
covers in the full order — a new class sits strictly between:

| old edge | broken by |
|---|---|
| ρ6 < ρ11 | ρ13★, ρ17★ |
| ρ7 < ρ8 | ρ16★, ρ19★ |
| ρ9 < ρ10 | ρ18★ |
| ρ11 < ⊤ | ρ15★ |
| ρ12 < ⊤ | ρ21★ |
| ρ14 < ρ8 | ρ16★ |
| ρ14 < ρ11 | ρ17★ |

So any Hasse diagram drawn for the dictionary alone shows seven edges
that are not covers of the real order. That is the concrete correction
to the explorer's dictionary tab.

**The top of the lattice is where the new material lives.** ⊤ has
exactly three lower covers — ρ10, ρ15★, ρ21★ — two of them new. The
bottom is unchanged: ⊥ has exactly two upper covers, ◯⊥ and ¬◯⊥.

This also explains an observation the catalogue recorded without
accounting for it: its 109 flags cluster at ⊤ (21), ρ10 (21) and ρ21
(20). Those three are precisely the co-atoms. Flags cluster at the
top because the top is where the classes are hardest to separate,
which is the same reason the new classes are found there.

## The two flags

| cell | status |
|---|---|
| ρ12 ⊢ ρ15 | flagged; not proved at budget 1,000,000 (11.9 s) |
| ρ20 ⊢ ρ10 | flagged; not proved at budget 1,000,000 (14.4 s) |

Both are vector-identical on the whole ≤5-world confluent battery, so
neither is refutable there; settling either needs a ≥6-world confluent
countermodel or a positive search beyond the ladder. Escalated at
200,000 / 500,000 / 1,000,000 and reported, not dropped.

**The diagram is insensitive to them beyond their own edges.** Read
both as derivable and the cover set gains exactly the two edges
ρ12 < ρ15 and ρ20 < ρ10 — nothing else is added and nothing is
removed. So all 37 edges above are certified, and the only uncertainty
is whether two more exist.

## Part A — the sweep and the repaired pipeline

On the sweep's own closure cells generated from the 22
representatives (1,474 cells):

| | distinct cells | total crank |
|---|---|---|
| raw | 1,474 | 9,088 |
| after `nfc` (what the sweep uses) | 801 | 8,361 |
| after `simplifyWith fullSetC` | **590** | 7,847 |

**211 of 801 cells — 26% — would not have to be classified at all.**
Each avoided cell is a battery pass over 10,534 frames plus, where
that fails, a tier ladder. And the check that matters: the 22
representatives stay pairwise distinct under the pipeline (22/22), so
the stronger quotient loses no class.

### The full sweep, actually re-run

`rhoorder sweep` re-runs the whole crank-stratified sweep with
`simplifyWith fullSetC` substituted for `nfc` and nothing else
changed. Against the original stream (`wip/closed_frag_out.txt`):

| | original (`nfc`) | re-run (simpset) |
|---|---|---|
| classification cells | 680 | **469** (−31%) |
| NEW / MEM / FLAG | 22 / 492 / 166 | 22 / 286 / **161** |
| generation + classification | 714.9 s | **596.3 s** (−17%) |
| classes per stratum (cranks 0–7) | 1,2,3,5,7,11,19,22 | **identical** |
| flag-free strata | 0–5 | **identical** |

**The same 22 classes, at the same cranks, from a third fewer cells.**

Two details worth recording, because both look like discrepancies and
neither is one.

* **One representative is printed differently.** The original's `r18`
  is `w16 ∨ (¬¬◯⊥ ∨ ◯¬◯⊥)`; the re-run's is
  `¬¬◯⊥ ∨ (w16 ∨ ◯¬◯⊥)`. These are the same three-element ∨-chain in
  a different association and order, and `canon` maps them to the same
  formula — so `canon_interd` certifies they are interderivable. It is
  the flattening doing exactly its job, not a different class. All 21
  other representatives are character-for-character identical.
* **Raised flags fall at crank ≤ 6 but rise overall** — 21 against 26
  at stratum 6, yet 161 against 166 in total only because the totals
  nearly cancel. The mechanism is that `crank` is measured AFTER
  normalisation, and the simpset lowers crank further than `nfc` does,
  so formulas that the original sweep pushed past the cap now fall
  inside it. The pipeline removes duplicate work and simultaneously
  widens coverage at a fixed cap. Anyone reading flag counts as a
  quality measure across the two runs is comparing different corpora.

The escalation and pivot phases of `mainSweep` were not transcribed,
so the re-run reports RAISED flags; the original's 109 *final* flags
have no counterpart here.

## Engine comparison — the G4c oracle and the LJF◯ focused searcher

Same 462 cells, both engines.

|  | oracle (`Search.decide`, G4c) | LJF◯ (`LSeq.search`) |
|---|---|---|
| proves | 158 | 110 of those 158, at depth ≤ 32 |
| refutes | 302 (countermodels) | **cannot refute** |
| flags | 2 | — |
| wall clock | 14.0 s over all 462 | 7.2 s over the 158 |
| verdict transfers to PLL | **yes** | **not yet** |

Three things worth recording.

**1. The fuels are not the same currency.** LJF◯'s fuel is derivation
DEPTH; the oracle's budget counts nodes. Comparing "fuel 16" with
"budget 20,000" is a category error. It cost a first, wrong run to
notice: `ρ3 ⊢ ρ4` is a single ∨-introduction and still needs **fuel
20**, because each inversion phase before the focus consumes a level.
Any future comparison must fix wall clock, not fuel.

**2. Zero conflicts.** Over the 302 cells carrying a certified
confluent countermodel, LJF◯ derives **none** of them at any depth in
the ladder. That is a real cross-validation: it checks the
polarisation (`erN_polN`, proved: erasing the polarised form returns
the formula on the nose, pin `[propext]`), the oracle's countermodels,
and LJF◯'s rules against each other. A single conflict would have
meant one of the three was wrong.

**3. LJF◯ verdicts do not transfer to PLL, and that is the live
gap.** `LJFO.search_sound` yields a derivation in LJF◯. Getting from
there to `PLLND.LaxND` needs focalization for PLL, recorded as **OPEN**
in `docs/ljfo-fidelity.md` §5 — the erasure bridge exists for the
◯-free calculus `LJF` (`LaxLogic/LJFComplete.lean`: `sound`,
`focalization`) but not for LJF◯. Until that lands, LJF◯ is a
cross-check and a speed comparator here, never a source of PLL
results.

### Status of the LJF◯ bridge, checked 2026-08-14 evening

Confirmed by two independent routes (this session, and the T1/T2
session on `claude/t1-lax-logic-refutation-37c0bf` at my request):

    git log --all -S "LaxND"      --pickaxe-regex -- 'LaxLogic/LJFO*'   → empty
    git log --all -S "PLLND.Deriv" --pickaxe-regex -- 'LaxLogic/LJFO*'  → empty

**No commit had ever added a reference to PLL derivability inside an
LJF◯ file, on any branch in this clone.** That was true when checked
and **was overtaken the same night**: commits `70c5fda` / `7838429` on
`claude/t1-lax-logic-refutation-37c0bf` add `LaxLogic/LJFOBridge.lean`,
which supplies the soundness half. Verified here independently — the
branch built and the axiom audit run from this session:

    'LJFO.laxND_of_ljfo'  depends on axioms: [propext, Quot.sound]
    'LJFO.erase_polarise' depends on axioms: [propext]
    'LJFO.bridge_iff'     depends on axioms: [propext, Quot.sound]

The construction erases polarity and reads the judgment flag as the
modality — `Γ ⊢tru P ↦ ⌊Γ⌋ ⊢ ⌊P⌋`, `Γ ⊢lax P ↦ ⌊Γ⌋ ⊢ ◯⌊P⌋` — with
`laxOf ↦ laxIntro`, `circL ↦ laxElim`, and every structural move a
`LaxND.rename`, so no cut and no admissibility lemma. It carries its
own ◯-preserving polarisation `posOfO`/`negOfO` (`LJFComplete`'s
`posOf`/`negOf` discard `◯`) with the round trip proved.

**Both arrows now hold.** Commit `8f0b731` completes it:

    bridge_iff : Nonempty (LaxND Γ φ) ↔
                 Nonempty (Inv (Γ.map negOfO) [] .tru (negOfO φ))

Verified here independently — own build, own audit:

    'LJFO.bridge_iff'       depends on axioms: [propext, Quot.sound]
    'LJFO.FocalizationPLL'  depends on axioms: [propext, Quot.sound]
    'LJFO.focalizeSCO'      depends on axioms: [propext, Quot.sound]
    'PLLND.ND_to_SC'        depends on axioms: [propext, Quot.sound]

`focalizeSCO` ports `LJFComplete.focalizeSC`, riding on the repo's
cut elimination (`SCh`, `ND_to_SC`) exactly as the IPC version does.
Its only genuinely new content is the two modal cases — `laxR ↦ circR`
over `laxOf`, `laxL ↦ circR` over `lfoc`/`circL` — which are trivial
in `LJFComplete` only because `negOf` erases `◯` there. `LJFOCore` and
`LJFOSearch` are untouched; the new imports of `PLLNDCore` and
`PLLSequent` are confined to the new file, so `LJFOCore`'s zero-import
auditability is preserved.

**Consequences.** The 110 order cells LJF◯ reached are now PLL
certificates. And an LJF◯ FAILURE now transfers too — so Route A's
missing arrow is supplied.

What DOES exist, and is easy to mistake for it:

| arrow | status |
|---|---|
| LJF◯ search ↔ LJF◯ calculus | **PROVED** — `search_sound`, `search_complete`, both `[propext, Quot.sound]` |
| `LJF` calculus ↔ IPC (◯-free) | **PROVED** — `LJFComplete.lean`, `sound`/`focalization` |
| LJF◯ calculus → PLL | **PROVED, 2026-08-14 night** — `LJFO.laxND_of_ljfo`, `[propext, Quot.sound]`, no choice (`LaxLogic/LJFOBridge.lean`, a NEW file; no existing LJF module edited) |
| PLL → LJF◯ calculus | **PROVED, hours later** — `FocalizationPLL` / `focalizeSCO`, `[propext, Quot.sound]`, commit `8f0b731` |

Both of the first two are real, unconditional results, and either can
be reported as "soundness and completeness". Neither licenses moving
an LJF◯ verdict to PLL.

`Reject/` (T1, T2) neither supplies nor needs the bridge: its entire
import closure is `PLLKripke`, `PLLFrames`, `PLLConfluentComplete`,
`PLLCountermodelEmit`, `PLLSemUI`, `Mathlib.Data.Set.Card`, and
`grep "LJF" Reject/*.lean` is empty. The only point where PLL
derivability enters is `not_laxND_of_root`, which consumes PLL's own
Kripke soundness.

### Two routes to replacing battery enumeration, and what each needs

The aim is to decide `⊬` without generating every model of a fixed
size and testing against all of them.

* **Route A — LJF◯ exhaustion.** (i) the calculus↔PLL bridge —
  **PROVED**, `bridge_iff`. (ii) a computable, FEASIBLE depth bound
  turning `search_complete`'s existential `∃n` into a decision —
  **OPEN**; this is what `LJFOHeight`'s "pigeonhole/collapse layer" is
  for. Precedent worth respecting: `decideFuel` is a genuine
  decidability theorem for PLL whose bounds are infeasible, which is
  why `CLAUDE.md` bans driving discovery through it.
* **Route B — forward construction.** `Reject/` searches for a
  CONSTRUCTION rather than for a proof, so a success is a countermodel
  and needs no enumeration at all. T2 (`built_countermodel_of_reduced`)
  gives the completeness half. Route B does not involve LJF◯ anywhere.

Route B is the nearer of the two, and its single named obstacle —

> **(R)** every underivable sequent has a finite REDUCED countermodel

— was **PROVED the same night** (`Reject/Reduce.lean`, commit
`059cea0`). Verified here independently:

    'Reject.exists_reduced_countermodel' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Reject.not_laxND_iff_built'         depends on axioms: [propext, Classical.choice, Quot.sound]
    'PLLND.FinComp.emitter_completeness' depends on axioms: [propext, Quot.sound]

The route is: quotient by `Rₘ`-equivalence (a bisimulation, which also
kills the `Rₘ`-cycles), then refine `Rᵢ` by `Fm`-inclusion +
`Rₘ`-rank + injective key; the load-bearing lemma is
`exists_refined_witness` — shrinking `Rᵢ` cannot make `◯A` true,
because a witness pushes up to a world of maximal `Rₘ`-rank whose only
`Rₘ`-successor is itself.

**So T2 is now unconditional**, as a biconditional:

    not_laxND_iff_built : ¬ Nonempty (LaxND Γ ψ) ↔
      ∃ M r, Built M ∧ (∀ χ ∈ Γ, M.force r χ) ∧ ¬ M.force r ψ

Underivability and constructibility coincide, with no side condition.
That is the theorem Route B needed, and it is the formal statement of
"battery enumeration is replaceable".

**The residue is effectivity, not truth.** `not_laxND_iff_built` is an
EXISTENCE statement, and `exists_reduced_countermodel` pins
`Classical.choice`, so it cannot yet be run: it says a certificate
exists, not how to compute one. Making the chain constructive — a
`Sort`-valued height recursion so the induction returns data,
`Fintype` for `Finite`, decidable membership for the `by_cases`, and a
computable height — would turn it into a function taking any finite
countermodel to a certificate `certifies` accepts. That is the one
step between the theorem and the process.

`built_countermodel_of_reduced` assumes it, and neither of the repo's
two finite-countermodel sources supplies it: the filtration
(`PLLFiniteModel`) and the emitter's `canonCMof` both order worlds by
inclusion on theories while distinguishing them by a modal component,
which is exactly what breaks antisymmetry. The T1/T2 session's
`rscreen` found a two-step route — quotient by `Rm`-equivalence, then
refine `Rᵢ` by `Fm`-inclusion + `Rm`-rank + index — passing 1444/1444
on the `Rm`-acyclic stratum of the ≤3-world battery. Support, not
proof.

### Where both routes now stand

Each has exactly one piece left, and in both cases it is EFFECTIVITY
rather than truth:

| | truth | effectivity |
|---|---|---|
| Route A (LJF◯ exhaustion) | `bridge_iff` ✓, `search_complete` ✓ | a feasible depth bound ✗ |
| Route B (forward construction) | `not_laxND_iff_built` ✓ (unconditional) | choice-free, computable extraction ✗ |

Neither is now blocked on a missing theorem about the logic.

*(2026-08-15: both routes are now IMPLEMENTED and linked —
`lean_exe twosided`, certified layer `wip/ljfo_link.lean`. On this
file's own 462-cell corpus the linked engine reproduces the entire
settled matrix — 158/158 proofs by LJF◯ at fuel ≤ 44 in ~0 ms,
302/302 refutations by Built-tree certificates — with zero conflicts;
the two flags resist both sides. `docs/two-sided-engine.md`.)*

### A caveat on one downstream claim

`docs/ljfo-fidelity.md` §5 now reads "uniform interpolation for PLL —
OPEN (needs `CimpAnt` only; focalization for PLL is now PROVED)".
Focalization being proved is correct and checked. "`CimpAnt` only"
understates by one MECHANISATION step, which this repo's own
discipline should not let pass silently: stating UI for PLL in
`Deriv`/`LaxND` terms needs the read-back family that
`LJFComplete.lean` supplies for IPC —

    exI, allI, exI_pfree, allI_pfree, exI_sound, exI_min,
    allI_sound, allI_min, pfree_unPos/unNeg/trans/negOf, pfreeCtx

(`LJFComplete.lean:462–575`). A branch-wide grep finds those names in
`LJFComplete.lean` and nowhere else, so no PLL analogue exists yet.
For IPC it was about a hundred routine lines, and it is expected to be
routine again — but `◯` is exactly where routine has stopped being
routine before in this development, since `PFree` must now traverse
`circ` under `negOfO`. The accurate ledger entry is "needs `CimpAnt`,
plus the interpolant read-back through `negOfO`".

### The 48 unreached cells

The 48 cells LJF◯ does not reach at depth 32 are concentrated where
the hypothesis is a disjunction of modal formulas (ρ5, ρ6, ρ9 as
antecedents) — the case where inversion generates the most phases
before a focus can commit. That is a fuel-ladder observation, not a
completeness claim: LJF◯ completeness at sufficient fuel is the
pigeonhole layer of `LJFOSearch`, and nothing here bears on it.

## Replay

    lake build rhoorder rhoengines
    .lake/build/bin/rhoorder norm      # the pipeline on the sweep's cells
    .lake/build/bin/rhoorder sweep     # the full sweep, simpset in place of nfc
    .lake/build/bin/rhoorder matrix    # the 22 × 22 order  (~14 s)
    .lake/build/bin/rhoorder pin       # matrix + kernel pin lines
    .lake/build/bin/rhoorder flags     # the two flags at raised budget
    .lake/build/bin/rhoengines pol     # polarisation round trip
    .lake/build/bin/rhoengines cross   # both engines

Streams: `wip/rho_order_out.txt`, `wip/rho_engines_out.txt`,
`wip/rho_sweep_out.txt`.
