# Certified computation in lax-logic-in-lean: what the record shows

2026-10-09, LaxLogic manager session, for Matthew and the locus overseer.
Inputs: the repository at `main` = 9783484, a read-only survey of the
record, and a reply from the *Lean prover-toolkit conservativity proof*
session (the only LaxLogic session running today). Every citation below
was taken from the tree; the two central ones (`Demos.lean`,
`FRJO/Core.lean`) were re-read for this note.

Purpose: input to a generic harness for certified computation, in which
the theory says what must be computed, an efficient implementation
faithful to the theory computes it, and a checker proved sound verifies
the products in the kernel, with termination arguments kept in the
theory and never recomputed at run time.

## 1. The pattern already exists here

The repository already runs this pattern under the name "the repo's
oracle pattern" (`FRJO/Core.lean:49`):

    derivation ──extract──▶ FinCM ──FinCM.checkB──▶ not_provable_of_check

The searcher is untrusted; soundness of each concrete result comes from
extraction plus a verified checker. The generic tool is therefore a
generalisation of working instances, not a new design.

The key design decision, found in every successful instance, is that
**the checker is sound at every fuel, and fuel enters only the
completeness statement**. For LJF◯ (`LJF/OSearch.lean:384, 527`):

    search_sound      : ∀ n s, search n s = true → s.holds
    search_complete_h : s.holds → search (height of a derivation) s = true

A hit is a certificate whatever the bound, so the bound never enters the
trusted path; a miss at fuel n means only "no derivation of height ≤ n".

## 2. Where certificates and reflection are used, and how it went

| mechanism | files | certifies | soundness theorem | axioms | outcome |
|---|---|---|---|---|---|
| G4c search, fuelled | `LaxLogic/PLL/G4/G4Dec.lean` | provability | `search_sound` (l.171, 278), `G4c_iff_search` (l.634) | propext, Quot.sound | sound; packaged decider capped at weight ≈ 4–5 (§3) |
| G4c proof terms, fuel-free searcher | `LaxLogic/PLL/G4/G4Term.lean`, tactic `pll_g4c` in `LaxLogic/PLL/Search/Run.lean` | provability, by a proof term the kernel type-checks | `G4cTm.toG4c` / `sound'` | propext, Quot.sound | the gap sequent went from >6.5 min to milliseconds (acc0a2a) |
| Finite countermodels | `LaxLogic/PLL/Semantics/CountermodelEmit.lean:239, 261`; `Search.lean:689-700` | non-provability | `not_provable_of_check` via `FinCM.checkB` | propext, Quot.sound; explicitly no `Lean.ofReduceBool` | emitter, battery and minimiser are untrusted `partial def`s; every hit passes `checkB` |
| FRJ countermodel tables | `FRJ/Bridge.lean:136, 141`; `FRJ/Search/Pin.lean`; `tools/Cert.lean` | non-derivability | `not_derivable_of_countermodel` | propext, Quot.sound | 740 generated `by decide` refutations in `Certified/RhoRefutations.lean`; minimisation is "what makes the final `by decide` affordable" |
| Refutation side of the two-sided engine | `Reject/Cert.lean:87, 93` | LaxND non-derivability | `not_laxND_of_certifies` | propext, Quot.sound | needs no fuel |
| Proof side of the two-sided engine | `wip/ljfo_link.lean:58, 67` | LaxND derivability | `laxND_of_searchProves` | propext, Quot.sound | the kernel *re-runs the search* under fuel (`docs/two-sided-engine.md`); see §3 |
| Closed FRJW store | `wip/check_closed.lean:54, 121` | proof or disproof of a sequent | `checkClosed_sound`, `decideGbuW_of_check` | propext, Quot.sound | gate 20/20 pass; check < 1 ms on stores ≤ 49 rows (`docs/checkclosed-checks.md` §8); still in `wip/` |
| CLP / QLL | `LaxLogic/QLL/CLPCore.lean:153`, `LinQ.lean:207, 453, 465`, `CLPWolfram.lean` | SLD proof trees; ℚ witnesses and Farkas refutations | `checkC_sound`, `certifyVerdict_sat/unsat` | (per file pins) | Wolfram used as an untrusted solver; the checker carries the proof |
| BiLax | `BiLax/Pipeline.lean` | non-derivability | saturation certificate `by decide` | propext, Quot.sound | |
| Databases built from certified cells | `Certified/Register.lean`, `RNDB/DB.lean`, `RNDB/Types.lean`, `Rewrite/Core.lean:66` | 1,776 kernel-checked facts as one object; 679 rewrite rules | `Entry.ok` is a proof field; no rule enters a simpset unless its cell is proved | each cited theorem re-pinned under `#guard_msgs` | the best worked example of "products verified by a sound checker" |

**`native_decide` is the counter-example.** Exactly two declarations use
it (`LaxLogic/Belief/Examples.lean:44, 52`, cardinality claims, held out
by name in `Audit/Production.lean`). Under Lean 4.31 it no longer cites
`Lean.ofReduceBool` but mints its own `…_native.native_decide.ax_1_1`
axiom, so `scripts/ledger.lean:28-37` checks both spellings. The kernel
never sees the computation, so it is out of scope for a kernel-checked
harness.

**Well-founded recursion does not reduce in the kernel.** The Iemhoff G4
decider (`docs/g4ill-gap-review.md:55`) is defined by `WellFounded.fix`,
so `by decide` is unavailable and it is trusted only through compiled
`#eval`. A kernel-checkable checker must be structurally recursive.

## 3. The termination-bounds example

This is the example Matthew cites. `decide (G4c Γ C)` routes through
`decideFuel` (`G4Dec.lean:629`), whose fuel is

    2 ^ |enum| · |enum| + 1,   enum = the weight-bounded formula space.

Measured on `⊢ ◯p → ◯p` (`docs/demos.md` §3; summary in
`LaxLogic/PLL/Search/Demos.lean:29-43`):

| what | time |
|---|---|
| `(enum {p} 5).card` alone | 6.06 s |
| `decideFuel` | 5.83 s |
| full `search … decideFuel` | 5.86 s |
| `find` with a hand-supplied fuel of 10 000 | 34–72 ms |

The cost is not the bound arithmetic (the 54-digit number is free). It
is **constructing the object the bound is a function of**: `.card`
builds `enum` level by level, with `|enum|²` products and quadratic
`Finset` deduplication per level. On this provable sequent the search
itself adds nothing measurable; that is not true in general. The early
fuelled search was itself very inefficient on refutable goals:
`PROGRESS.md` §10 (2026-07-19, "fuel demoted") records that it "ground
for minutes" where the fuel-free `G4cTm.find` took 0 ms, because a
failing branch is explored to the full fuel depth. So the record shows
two costs of fuel: building the bound's domain, and searching failing
branches to the bound. `docs/demos.md` states that this construction "exists only
to certify completeness", and `docs/calculus-formalisation-method.md`
§4 puts the general point as: the fuel in a decidability theorem is there
to satisfy the kernel, not the CPU.

Consequences already in force:

- `TOOLS.md:34` and `CLAUDE.md` rule 4: never drive discovery through
  `decideFuel`.
- Fixes, in order: 16dc68a filtered `enum` (doubly- to singly-exponential
  fuel, construction cost unchanged); acc0a2a added the fuel-free,
  untrusted `G4cTm.find` whose output the kernel checks.
- `FRJO/Core.lean:40-47` replaces bound arithmetic with a feasible
  termination argument (contexts grow monotonically inside the finite
  subformula universe; a history `H` blocks revisits). Its soundness and
  completeness are stated as named propositions and carried OPEN
  (`SoundnessFRJO`, `CompletenessFRJO`).
- **Unbuilt and queued (Matthew, 2026-08-26, `docs/next-session.md:427-447`):**
  certificate passing for the LJF◯ proof side. An untrusted compiled
  `emitTree`, a structural fuel-free `checkDeriv : Tree → LSeq → Bool`,
  and one theorem `provable_of_checkDeriv`. Campaign theorems would then
  be `laxND_of_checkDeriv (by decide)` on a tree literal, with `decide`
  cost linear in tree size. No `checkDeriv` exists in the tree today.
  This is the closest existing specification of the harness Matthew
  wants, for one calculus.

### Other cases of the same shape

- **Deep fuel in the kernel.** Compiled `searchProves` at fuel 64 on
  ρ12 ⊢ ρ15 was killed after about 24 h (`docs/disproof-handoff.md:1373`).
- **Freshness chosen for the proof, paid for at run time.**
  `LaxLogic/QLL/Kit.lean:25-32` makes `freshFor` concatenate every name
  in scope, "crude on purpose", because freshness is wanted as a theorem.
  `certify` adds each fresh name to the context, so name length doubles
  per binder: 38 GB at binder depth 25 (25c3abb). The fix, 0333c19
  (names one byte longer than the longest in scope; 2–85 ms), is on
  `claude/practical-euclid-a10fc3` only and **not on main**.
- **Interpolants.** In `LaxLogic/PLL/UI/G4UITrunc.lean` fuel is "a shadow
  parameter", irrelevant above a measure μ by an indifference lemma. That
  is the right placement: the fuel is in the statement, and a lemma says
  the run does not depend on it.

## 4. What was slow, and why

Four separate causes; a harness must treat them separately.

1. **Constructing the measure's domain** (`decideFuel`, §3). Dominant
   cost at run time.
2. **Elaborating well-founded mutual recursion.** `LJF/OFuelPFam.lean`
   (17 mutual definitions, founded on μ = (height, weight, sizeOf)): 25–28
   min to build, 17.8 GB peak RSS, 237 MB olean. Measured in
   `docs/ui-ljfo-clause-table.md` §4.20: as `unsafe def` 3.0 s; with
   `skipKernelTC` 510 s; committed 1463 s. So about 507 s is the
   `WellFounded.fix` translation and about 950 s the kernel; the 176
   `decreasing_by` proofs are a minor part. A structural (`Nat.rec`)
   design is recorded, not built.
3. **Untrusted engine cost.** FRJW (`docs/engine-profile.md`): 94 % in
   the promise-join cross product; semi-naive evaluation (5387505, off
   by default) gives 2.6× on the engine but 1.04× over the 129-cell
   batch, because the output layer (minimisation, SVG, the two-pass kernel
   certificate, about 34 s on one cell) dominates. The `--check` file
   check costs 10.85 s per pass, 8.2 s of it Lake overhead.
4. **Classical taint (a correctness cost, not a speed one).** Mathlib's
   `Fin` and `Finset` instances bring in `Classical.choice`, which blocks
   `decide` and breaks the axiom pins; finite models are hand-built on a
   bare inductive with a `Nat` index, and `FRJ/Basic` moved to Batteries
   (e89f003). A `Decidable` hypothesis must come from completeness plus
   the finite model property, never from choice.

## 5. What a generic harness would need to cover for this repository

**Four producers, with four certificate shapes:**

| producer | certificate | checker | status here |
|---|---|---|---|
| proof search | derivation tree or proof term | structural re-walk (`search_sound`), or kernel type-checking of a term (`G4cTm`) | built for G4c; queued for LJF◯ (`checkDeriv`) |
| countermodel construction | finite Kripke model | forcing evaluation (`FinCM.checkB`, `Tab.okB`, `checkClosed`) | built, several calculi |
| decision procedure | a `Decidable` instance whose soundness is a theorem (`decidePLL`, `FRJ/Gbu/W/Saturate.lean:2333`) | none at run time: a proof object, "not a practical algorithm" (`docs/calculus-map.md`) | built; practical use goes through the two producers above |
| interpolant | a formula plus two derivations, with a variable-freeness side condition | two derivation checks plus a syntactic check | fuel-founded; the hardest to package; do last |

**Parameters a generic harness should expose:**

1. *Measure placement.* The theory may mention a measure; the run never
   materialises it. Soundness holds at every fuel; fuel appears only in
   completeness.
2. *Verdict.* Three-valued, pass / fail / flag. `fail` only on a
   certificate; a `flag` is re-run at a raised budget, never dropped.
3. *Axiom allowance per producer,* checked with `collectAxioms` only
   (`#axioms_within`, `docs/pins.md`). Default `[propext, Quot.sound]`;
   `native_decide` excluded.
4. *Checker recursion.* Structural, so `decide` reduces in the kernel;
   no `WellFounded.fix` in a checker.
5. *Bounded execution.* Run the compiled binary under a deadline, never
   `lake exe`; report every skip and cap.
6. *Certificate minimisation* before the kernel check, since kernel
   `decide` cost grows with certificate size (the FRJ tables).
7. *Splice point.* Result consumed as a term in a proof (tactic splicing,
   `pll_g4c`) or as a generated file of facts (`RhoRefutations`, RNDB).
8. *Completeness as an obligation.* Completeness is usually the OPEN half
   and is passed as a typed hypothesis, never assumed; the harness must
   work with soundness alone.

**Differences from locus (state-space exploration, bisimulation
certificates):**

- Our certificates are syntax trees or small finite models whose checker
  is structural recursion; their size is bounded by the derivation or the
  model, not by a reachable state space.
- Failure is asymmetric: a refutation is a positive object (a model, or
  a disproof in FRJ/FRJV), checked by a different checker from proofs.
  `Reject/Bisim.lean` and `Reject/Complete.lean` do use bisimulation, so
  that part may share a checker with locus.
- Completeness is usually OPEN, carried as a named proposition
  (`FRJO/Core.lean:58-64`). A harness that requires completeness will not
  fit here.
- Proof terms can be checked by the kernel directly (`G4cTm`), which has
  no analogue for a bisimulation relation; there the relation must be
  checked by a decision procedure over a finite carrier.

## 6. Open items surfaced by this survey

- 0333c19 (`freshFor` fix) is not on main.
- `checkDeriv` for LJF◯ (queued 2026-08-26) is unbuilt.
- `wip/check_closed.lean` (`checkClosed`) is not promoted out of `wip/`.
- The structural redesign of `LJF/OFuelPFam.lean` is recorded, not built.
- The record has no measured cost of kernel `decide` over the whole of
  `Certified/RhoRefutations.lean`, and no use of `implemented_by` or
  `@[csimp]` to connect a fast implementation to a specification.
