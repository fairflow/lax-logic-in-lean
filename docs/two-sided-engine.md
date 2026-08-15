# The two-sided engine — LJF◯ proves, Reject refutes

*2026-08-14/15 night. Files: `wip/ljfo_link.lean` (the certified
layer), `wip/two_sided.lean` + `wip/two_sided_run.lean`
(`lean_exe twosided`), `wip/two_sided_pins.lean` (kernel exemplars).
Streams: `wip/two_sided_{corpus,close,flags6,flags7}_out.txt`.
Everything sits on the merge of `claude/t1-lax-logic-refutation-37c0bf`
into `ljf-pll` (merge `8a2d1a8`); nothing under `LaxLogic/` or
`Reject/` is edited.*

## What it is

Matthew's directive: the LJF◯ machinery was lying unused — link it to
`Reject/` and make the pair effective. The link is two Bools, one per
side of a sequent question `[φ] ⊢? ψ`, each with a kernel-checked
soundness theorem:

| side | Bool | certificate theorem | pin |
|---|---|---|---|
| proof | `TwoSidedLink.searchProves f Γ φ` — LJF◯ backward search on the bridge's ◯-preserving polarisation | `laxND_of_searchProves : … = true → Nonempty (LaxND Γ φ)` | `[propext, Quot.sound]` |
| refutation | `Reject.certifies M w Γ φ` — a Built-class tree countermodel | `not_laxND_of_certifies : … = true → ¬ Nonempty (LaxND Γ φ)` | `[propext, Quot.sound]` |

with, on the proof side, **completeness**:

    searchProves_complete : Nonempty (LaxND Γ φ) → ∃ f, searchProves f Γ φ = true

(`FocalizationPLL` + `search_complete`, the `Nonempty` eliminated into
a propositional goal, so **no choice is used**), and, joining them,

    two_sided_disjoint : searchProves f Γ φ = true →
                         Reject.certifies M w Γ φ = true → False

so the engine cannot contradict itself as a matter of kernel-checked
mathematics, not merely of testing. `deriv_iff_simplify` is the
normalise-before-search adapter (search the `simplifyWith`-reduced
sequent, report the verdict for the original).

The refutation side is complete in principle too —
`not_laxND_iff_built` (T2 + (R)) — but not yet effectively: that
theorem is an existence statement pinning `Classical.choice`. The
engine therefore *searches* the Built class (battery filter at ≤5
worlds, streamed tree generation at 6–7) rather than *computing* the
certificate from a derivation.

## Acceptance: the 462 ρ-order cells as PLL questions

Ground truth recomputed the OLD way in the same binary (full
10,534-frame battery + the G4c oracle at budgets 20k/100k), then the
engine, then a closing pass that spends more budget on exactly the
engine's flag cells.

| | old machinery | engine, first pass | engine, after the closing pass |
|---|---|---|---|
| ⊢ | 158 (9.8 s) | 127 at fuel ≤ 32, ~0 ms | **158/158** at fuel ≤ 44, ~0 ms |
| ⊬ | 302 (same battery) | 248 from the Built subbattery (570 frames), 32 s | **302/302** (+ 6-world streamed trees) |
| flag | 2 | 87 | **2** — exactly the ground truth's own |
| conflicts | — | 0 | **0** |

**The engine reproduces the entire settled matrix.** Every one of the
158 derivable cells is an LJF◯ certificate; every one of the 302
refutable cells is a `certifies` certificate; the two cells the old
machinery could not settle are precisely the two the engine cannot
either.

Points of substance:

* **The proof side is free at the fuels this corpus needs.** All 158
  derivable cells land by fuel 44, each below timer resolution, versus
  9.8 s for the G4c oracle. Minimum-fuel histogram: 46 at ≤8, 10 at
  ≤12, 4 at ≤16, 10 at ≤20, 24 at ≤24, 19 at ≤28, 14 at ≤32, 31 at
  36–44. **But a fast `false` is NOT exhaustion**: on the two flag
  cells the search answers `false` in ~0 ms at every fuel to 52 and
  then runs into minutes at 64 — the space grows explosively with
  depth, so a bounded `false` reveals nothing about underivability.
  Only the pigeonhole bound (open) can turn search failure into a
  certificate.
* **570 of 10,534 battery frames are Built** (5.4%), and that 5.4%
  already retains 248 of 302 refutations. The missing 54 are exactly
  the cells whose bisimilar tree needs more than 5 worlds — T2's
  duplication made concrete and countable. The closing pass recovers
  **54 of 54** with 6-world trees.
* **One tree does most of the closing work.** The 6-world tree
  `ri = [(0,1),(0,2),(0,3),(0,4),(0,5),(1,5)]`,
  `rm = [(0,1),(0,5),(1,5)]`, `fall = [5]` — a root with five
  children, one of which has a fallible leaf above it — refutes
  DOZENS of the 54 cells at its root alone. That is
  `not_laxND_of_check_any`'s mining asymmetry in action: one canonical
  countermodel settles many sequents, which no derivation can do.
* The PLL and DerivU verdicts coincide on all 460 settled cells —
  none of the 158 derivabilities needs distribution, consistent with
  the catalogue's finding that distribution's visible effect lives
  inside classes, not between representatives.

## Kernel exemplars (`wip/two_sided_pins.lean`)

Both certificate formats are `decide`-checked end to end — the kernel
literally re-runs the focused search:

    theorem edge_rho3_rho4 : Nonempty (LaxND [¬◯⊥] (¬◯⊥ ∨ ◯⊥)) :=
      laxND_of_searchProves (f := 16) (by decide)
    theorem obot_not_bot : ¬ Nonempty (LaxND [◯⊥] ⊥) :=
      Reject.not_laxND_of_certifies
        (M := ⟨2, [(0,1)], [(0,1)], [1], []⟩) (w := 0) (by decide)

both `[propext, Quot.sound]`, the file checks in ~1 s, **no
`native_decide`**. Discovery is untrusted; the check is the kernel.
This is discover-then-pin with the discovery step now a calculus
search instead of a battery scan.

## What replaces what

The old refutation method: generate ALL well-formed frames of a fixed
size, test every cell against all of them. The engine replaces both
halves on PLL sequent questions:

* proofs — G4c oracle at 5-digit node budgets → focused search at
  2-digit depth, ~10³× cheaper on this corpus, certificates
  kernel-replayable;
* refutations — 10,534 blind frames → 570 canonical trees plus
  DIRECTED streaming generation of larger trees only where a cell
  demands it. The class is `BuiltB`-decidable, so the generator
  enumerates countermodel candidates and nothing else.

What is NOT yet replaced: the two effectivity theorems.

* Proof side: completeness without a feasible BOUND. A `false` at any
  fuel certifies nothing, and the flag cells show the wall: ~0 ms
  through fuel 52, minutes at 64. The pigeonhole layer over the
  finite subformula universe is the missing theorem.
* Refutation side: `not_laxND_iff_built` with `Classical.choice`.
  Constructivising it (the plan specced with the T1 session) would
  turn "a certificate exists" into "here it is", computed from any
  finite countermodel.

Those two are the whole distance between "engine" and "decision
procedure".

## The two genuine flags

`ρ12 ⊢? ρ15` and `ρ20 ⊢? ρ10`, unsettled by: the G4c oracle at budget
10⁶, the whole ≤5-world confluent battery, LJF◯ to fuel 52 (fast) and
64 (minutes, still running at write-up), Built trees on 6 worlds
(34,624 frames, edge-generated `Rm` family), with the 7-world streamed
hunt running at write-up. Every negative is bounded and labelled;
nothing is dropped.

## Standing caveats

* The tree generator covers the CLOSED corpus (`val = []`); cells with
  atoms need valuation choices added.
* The generator's `Rm` is edge-generated (reflexive-transitive closure
  of a chosen edge subset). A miss rules out only that family at that
  size, not the whole Built class.
* The engine decides `LaxND`. For `DerivU` the refutation side
  transfers only when the found tree is mutually confluent (each hit
  is labelled), and the proof side would need distribution-instance
  premise loading — not built.
* `certifies` re-runs `wellB` per call — essentially the engine's
  entire measured cost. Cache well-formedness per frame to remove it;
  not done, recorded.
* First cut of the generator materialised the whole frame list; at 7
  worlds that is millions of `FinCM`s and it destabilised a concurrent
  run through memory pressure. Now STREAMED; keep it that way.
