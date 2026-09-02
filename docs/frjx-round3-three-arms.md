# FRJX round 3 — three arms, identical sources, differing only in what they may consult

1 September 2026, branch `FRJX`.  Model: Opus 5 for all three arms.

Three sibling directories `wipa/`, `wipb/`, `wipc/`, verified byte-identical
modulo the import prefix, each starting at 8 open ports and 15 open plan
lemmas.  All three excluded from the corpus.  Same brief verbatim apart from
the access clause; same verifier (`lake env lean` + `#print axioms`).

| arm | may consult |
|---|---|
| **A** | its own three files only |
| **B** | its own files + the retrieval harness (13 433 signatures, no bodies) |
| **C** | its own files + the whole repository, no harness |

## Result

| | A — nothing | B — harness | C — sources |
|---|---|---|---|
| closed, sorry-free | **2 of 9** | **4 of 9** | **4 of 9** |
| worst pin | `[propext, Classical.choice, Quot.sound]` | `[propext, Quot.sound]` | `[propext, Quot.sound]` |
| tokens | 186k | 187k | **135k** |
| tool calls | 24 | 32 | **26** |
| wall-clock | 1 245 s | 1 045 s | **503 s** |
| repo consulted | none | 12 search calls | 3 625 lines (**1.45 %** of 249 503) |

All figures re-verified independently of the arms' own reports.

**B and C closed the IDENTICAL set** — `evalI_of_evalR` (X6), `gbuInv8'`,
`gbuInv14'`, `unrefutedBelow_step'` — left the identical five open, reached
the same structural diagnosis independently, made the same recommendation,
and even made the same incidental decision to move `unrefutedBelow_step'`
below `gbuInv14'`.

A closed X6 and `gbuInv8'` only, and its `gbuInv8'` carries
`Classical.choice` (entering through `List.filter` decidability, not through
the mathematics).  Its `gbuSuccCirc'` and `unrefutedBelow_step'` compile but
depend on `sorryAx`, so they are NOT closed; the arm said so itself.

## What it means

**The harness recovers the whole gap between "nothing" and "full sources".**
A < B = C.  That is the case for it: on a corpus too large to read, B's
access buys C's outcome.  At THIS scale it does not pay — C was cheaper by
39 % in tokens and 2× in wall-clock, because grep over structured Lean names
is already a precise retriever and C only ever pulled 1.45 % of the corpus.

**Where retrieval was load-bearing, it was constructor signatures.**  Arm B's
own accounting: decisive for `gbuInv8'` (`FRJVi.impInI`, "unguessable") and
`gbuInv14'` (`FRJVi.circNotIn`, `FRJVi.axIC`); contributed nothing to X6.
Its summary — the index is strong on inductive constructor signatures and
weak on `def`s whose content is the body (`EvalR`, `EvalI`,
`UnrefutedBelow`, `RefutedCleanly`, `vacZoneA`), which had to be
reverse-engineered from destructuring patterns.

**Arm A's block table is the sharpest evidence for a types+constructors
index.**  Seven distinct blocks; three broken by guessing names at the
elaborator, four not broken at all — and all four were "which rules exist?":
a regular `◯` rule with an irregular premise; the `himp`-join building `Γ`
for `RefutedCleanly`; zone-change for `◯` goals; a regular `∨` rule over a
common context.  Retrieval cannot return an ABSENCE, and an absence is
exactly what settled the campaign's main finding.

Arm A's own integrity note, worth keeping: it used `apply`/`exact` with
guessed constructor names and read the goal states, and observes that if
that counts as retrieval its honest total is **1 of 9**.

## The campaign finding, which outweighs the experiment

Plan §2's claim "one lemma, fifteen ports" is FALSE, and both B and C found
why independently:

> `(Lift)` adds ROWS TO THE DATABASE, not DERIVATIONS TO `FRJVi`.  Every port
> whose original feeds an `FRJVi` derivation into `orI` or a `⋈` join
> (`prem : ∀ j, FRJVi G (stab j) (th j) (rhs j)`) is blocked in the lifted
> branch, where only `∃ t, Nonempty (FRJVr G t Γ C)` is available.

The four that closed are exactly those whose irregular rule has a regular
counterpart — `andI1/2 ↔ andR1/2`, `impInI ↔ impIn`, `circNotIn/axIC ↔ id`.
The five that did not are exactly those that do not.  `FRJVr` has no `orR`
constructor at all, deliberately: refuting one disjunct does not refute the
disjunction.

So the re-scope is: **`(Lift)` must extend `FRJVi`, or the joins must admit
regular premises.**  Both are calculus changes — the thing `SaturatedOver`
was designed to avoid.  Decision for Matthew.

`gbuInv10'` has a candidate refutation at `C₁ = C₂ = ◯(◯p ⊃ p)` (arm B),
NOT certified: settling it needs `joinOr`'s `RefAt` obligation decided.
Recorded OPEN, not REFUTED.
