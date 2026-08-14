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
