# Review of the LJF◯ marathon (2026-08-10 10:00 → 2026-08-11 04:20)

*Commissioned by Matthew 2026-08-11, before any further building: the
marathon did not reach unconditional E2/A2, so step back and review.
Items: (0) what changed in the calculus vs the interpolants; (1) did the
efficiency proposals work; (2) what mathematics of general use was
produced; (3) how much can proofs be condensed without definition
changes; (4) up to three simplification rounds; (5) the blocked-result
pattern: `cascade_boxgoal_pos` vs the semantic blocker vs `CimpAnt`,
including a fresh refutation attack on `CimpAnt`; (6) handover refresh.*

---

## 0. What was changed, and what layer 4 would change (the confirmation)

Matthew's reading is correct, with one refinement.

**The calculus was changed once, early, and is frozen.** The inference
rules of LJF◯ are exactly those in `LJFOCore.lean`: the four flagged
judgments, `circL` lax-only, `circR` setting its premise lax,
`impR`/`andR` tru-only, persistent contexts, plus the coercion

    laxOf : Stab Γ tru P → Stab Γ lax P

which was added on 2026-08-09 when the ported `PLLFocused` design was
found incomplete (it missed `◯φ` for provable implicational `φ`). Since
`laxOf` landed, no rule has changed. The height-indexed judgments of
`LJFOHeight.lean` are a re-presentation, PROVED equivalent
(`toH`/`ofH`), not a change.

**The interpolant definition `interp` was revised three times, each
time because the previous A-side was provably incorrect, and E1/A1 were
re-proved after each revision.** Precisely:

* forced change #1 (paper stage): the A-side box-opening row must be
  E-guarded, `↓E(↑R :: rest) ⊃ A(↑R :: rest ⇒ ◯Q)`, because
  `E(done) ⊢tru E(↑R :: rest)` is false;
* forced change #2 (caught by the machine): the ◯-goal direct row must
  be the lax goal-inversion row FAMILY, because `◯` does not distribute
  over `∨`;
* forced change #3 (caught by a 2-line countermodel): the ◯-goal
  aggregate must be box-wrapped,
  `interp p [] done (some (.circ P)) = ◯(↓ nOrAll rows)`, because with
  the bare disjunction `SatA2` is FALSE at `done = []`, `Δ = [◯q]`;
* route (3) part 1 additionally uniformised the modal antecedent to
  `A(rest ⇒ ↑↓◯Q′)`.

In each case the previously proved E1/A1 (`eSound`/`aSound`) were
reproved against the new definition; they are currently proved outright
and pinned. So: heroic preservation of the RULES, yes; the original
A-interpolant was sound (A1 held) but provably NOT minimal (A2
refutable), and minimality is what forced the redefinitions.

**Layer 4 changes the interpolant only, not the calculus.**
`LJFOFuel.lean`'s `interpF` is a SECOND interpolant definition:
`interp` mirrored clause for clause, founded on fuel instead of the
weight measure, with the retention guard `A(done ⇒ ↑↓◯Q′)` at the full
station in all 12 modal-row sites. All four UI statements would be
proved afresh for `interpF` (as `eSoundF`(/`aSoundF`/`satE2F`/`satA2F`);
the existing `interp` results stand unchanged beside it. The theorem
"LJF◯ has uniform interpolation" is an existence statement, so swapping
the witness definition is legitimate strategy; changing the CALCULUS
would change the theorem, and that is not proposed. One consequence to
state plainly: if layer 4 succeeds, the E1/A1 already proved for
`interp` do not transfer; the four statements are re-established for
`interpF`, and `interp`'s development becomes the comparison object.

---

## 1. The efficiency proposals: adopted or not, and how they performed

The reviewer note (`ljfo-cost-review.md`, second agent, 2026-08-10)
made seven recommendations. Scorecard:

| § | proposal | adopted? | outcome |
|---|---|---|---|
| 1 | single-build tee loop | YES, same day | worked exactly as claimed: halved every iteration mechanically (the old loop ran two full builds; failed builds are never cached) |
| 2 | split at the Part 4/5 boundary | YES (`b96d1bb`) | the biggest single win: iterations stopped paying for the frozen 12M-heartbeat core; one cross-module repair (`interpA_atom_eq`'s closing `simp`) was the only friction |
| 3 | develop the hard member outside the mutual (`wip/ljfo_dev.lean`) | in a STRONGER form | instead of a scratch file, the mutual was parameterised by `cAnt : CimpAnt p` (DykAnt-style) inside the theory file, which isolated the hard member AND made E2/A2 landable conditionally; the literal scratch file was never created because every subsequent discharge design died at the termination analysis, before there was code to compile |
| 4 | the executable oracle over the in-repo decider/countermodel stack | YES (`wip/ljfo_eval.lean`), one deviation | engines are `PLLND.Search.prove?Bounded`/`refute?` (the certificate pair), not `checkB`/`decide` directly: the standing repo rule forbids driving discovery through the decidability theorem, and the first `decideFuel` attempt did hang. Calibrated live-fire on forced change #3 as the note prescribed |
| 5 | name the ◯-goal row family (`laxRows`) before writing the U-family | NO | the note's "strictly cheaper now" premise had lapsed by reading time (the U-family was already written against the seven inlined shapes); deferred then, now the centrepiece of proposed round 2 |
| 6 | profile instead of raising heartbeat ceilings | NO | ceilings stand (8M in the tail); scheduled for proposed round 3 |
| 7 | land E2 fully before A2 | NOT AVAILABLE as stated | E2/A2 are genuinely mutual through the T/U families; the intent (a legible checkpoint) was met by the conditional pins commit instead |

**Did they speed development significantly? Yes, measurably.** Before
adoption (10:00–22:55): four commits, the E2/A2 port at 15–30 minutes
per iteration. After (22:55–04:20): twenty-four commits, among them the
route-(3) row surgery, 12 `interp` sites plus soundness plus the whole
tail plus pins, propagated green in ONE pass (the `cAnt`
parameterisation absorbed the change), and zero statement bugs reached
the elaborator after the evaluator was calibrated. Two qualifications:
part of the post-adoption pace is that the route-(B) layers are new
small modules, fast to compile regardless; and no process change
touched the actual wall. The tools made reaching the terminus cheap;
they could not make it avoidable. The note's own §4 claim ("the only
proposal that changes the rate, not the cost") was borne out.

**On Matthew's specific question about instrumenting the theory files
with the in-repo decidability/countermodel machinery:** implemented as
the note designed it, one file OUTWARD from the theory: harness files
(`wip/ljfo_eval.lean`, now `wip/ljfo_attack.lean`) import
`LJFOCore` + `PLLG4Dec` + `PLLSearch`, so the dependency points inward
and the theory files keep the zero-import auditability property and
untainted pins. The theory files themselves are deliberately not
instrumented. What was NOT done during the marathon, and is this
review's correction, is coverage: the bank stopped at the degenerate
ends the note listed and never replayed the repo's hard corpus or
extended the frontier; §5c below is the repair, and the doctrine is now
in `CLAUDE.md`.

---

## 2. Mathematics of general use produced since 10:00 on 2026-08-10

Beyond campaign bookkeeping, seven items with life outside this branch:

1. **E1/A1 for a focused lax calculus, machine-checked** (`eSound`/
   `aSound` over LJF◯): soundness of both Pitts quantifiers for a
   focused calculus with a lax modality. As far as the in-repo survey
   knows, no mechanised analogue exists elsewhere.
2. **The box-wrapping law** (forced change #3): the ∀p aggregate at a
   ◯-goal must itself be ◯-wrapped; refutable in two lines if omitted.
   A small, citable fact about lax uniform interpolation.
3. **The row-family law** (forced change #2): because `◯` does not
   distribute over `∨`, the ◯-goal ∀p needs the goal-inversion FAMILY,
   not a single direct row. Same character as (2).
4. **The duplication terminus, stated sharply**: every
   consumed-implication architecture for the modal antecedent fails at
   χ-uses inside crossed-station material, the same ①/② configuration
   as Howe's duplication and the machine-checked G4iLL incompleteness.
   This is the sharpest available statement of WHY contraction-free lax
   calculi resist uniform interpolation, and it connects three
   previously separate observations.
5. **The decider round-trip for LJF◯** (`LJFOSearch.lean`): derivable ⟺
   searchable at existential fuel, with `search_sound` rebuilding
   kernel derivations. A reusable proof-search kit for the calculus
   (relevant to the decidability thread and to any future automation);
   its completeness proof caught two real defects in the height layer
   (leaves must consume fuel).
6. **The height/universe kit** (`LJFOHeight.lean`, `LJFOUniverse.lean`):
   height-indexed equivalence and the subformula-closure invariant.
   Standard machinery, but built once and reusable.
7. **The negative catalogue**: ten discharge architectures for the
   modal antecedent, each pinned with its exact failure point
   (`docs/ljfo-plan.md`). Negative results, but they are what prevents
   any future session from spending a week rediscovering them.

---

## 3. Condensation without definition changes (the survey)

Measured duplication in the current files (statements untouched
throughout; everything below is proof/organisation only):

* the seven-shape ◯-goal family: ~40 `interpA_circ*` equation-lemma
  occurrences in `LJFO.lean`, each shape carrying an equation, an
  `interp_pfree` block, an `aSound` clause and a U-arm;
* 28 `dec_*` termination lemmas + 18 `decreasing_by` farms in the core;
  the simp-round-1 analysis estimated only ~10 farm entries actually
  fire;
* 21 membership-resolution chains (`resolve_left`/`mem_singleton`
  ladders) across `LJFO.lean` and `LJFOSearch.lean`, all the same
  three-step shape;
* the T/U families' lax arms share a `circR`/`lfoc`/`circL`/`downL`
  prefix that is spelled out per arm (11 `laxOf` sites);
* `LJFOUniverse.lean`'s transitivity is an eightfold mutual whose
  halves are polarity-dual;
* `LJFOSearch.lean`'s five named instance families each carry a
  hand-rolled soundness case of identical shape.

The precedent for yield is simp round 1 on `LJF.lean`: −33% lines,
−13% compile, zero statement changes. The tail here was written faster
and under more pressure than `LJF.lean` was, so the duplication density
is higher; a similar or better ratio is realistic.

## 4. The three proposed rounds

Discipline for every round, inherited from `docs/ljf-simp-round1.md`:
zero statement changes, all pins re-run after every batch, superseded
proofs moved to `Archive/` with a header note (never deleted), metrics
(lines, wall-clock) logged per round.

**Round 1 — mechanical dedup, tail only.** The membership-resolution
tactical; the shared lax-prefix combinators (extending `circROf`/
`upSelf`); the generic instance-family soundness scheme in the search
module; halving the universe transitivity mutual by polarity duality.
No `LJFOCore.lean` edits at all. Estimate: −20–25% of the ~3,900
non-core lines. Lowest risk, immediate legibility gain.

**Round 2 — name the ◯-goal row family** (the deferred reviewer §5,
now the centrepiece). Define `laxRows p done Q : List Neg` once,
top-level; collapse the seven parallel shape clauses in each of the
four layers to ONE clause about `laxRows`, discharged by `cases Q`
inside a single lemma per layer. `interp`'s VALUES are unchanged, so
this is still statement-preserving; the core is edited but only
re-organised. Estimate: −600–900 lines across both files. This is the
round that makes the development followable by a human reader, which is
the concern Matthew raised; it is also the precondition for any paper
version of the proof.

**Round 3 — compile-time and fidelity.** Trim the farms to firing
entries; `count_heartbeats`/profiler on the 8M block and retire the
raised ceilings (reviewer §6); produce the calculus-fidelity table (per
clause: does the induction step run on raw rules or on toolkit lemmas,
and do Pitts/Dyckhoff make the corresponding move on paper), which
doubles as the paper-exposition skeleton; archive dead toolkit detours
it exposes. Target: tail build at half its current wall-clock, and the
fidelity table as a standalone document.

Sizing note: my refactor estimates in this repo have run about 4×
pessimistic (recorded 2026-08-05), so these are afternoons, not days.

**Round 1 executed (2026-08-11 morning, Matthew's go).** Support
modules only, after the survey found that every LJFO.lean round-1
candidate sits inside the seven-shape regions round 2 rewrites
wholesale (doing them twice would be waste — they merge into round 2):

* `LJFOSearch.lean`: `memSingle` replacing 14 singleton-membership
  chains; `premsH0/H1/H2` replacing 19 premise lambdas. Compiles
  green; statements untouched.
* `LJFOUniverse.lean`: the eightfold mutual assessed and deliberately
  left — the imp constructor's Pos/Neg asymmetry blocks the duality
  collapse; recorded so no later round re-derives this.
* Metrics baseline banked for rounds 2–3: the `LJFO.lean` tail alone
  re-elaborates in **1773 s (≈29.6 min)** (measured under the attack
  runs' load — the realistic working condition); the pins passed in
  that same build.

---

## 5. The blocked-result pattern

### 5a. The three blockers, side by side

* **`cascade_boxgoal_pos`** (`wip/absorb_base.lean:2281`, the G4c
  tower kernel): the A-side budget descent AT A ◯-GOAL: from
  `itpA p S fs (b+1) Γ ◯D` (and ambient `itpE` at `b+1`) derive
  `itpA p S ft b Γ ◯D`, under the room
  `defect S Γ · (|jumpGoals S| + 2) ≤ b`. The unresolved case is the
  jump clause, whose target-side disjunct sits one budget unit below
  the source. The room hypothesis is what excludes every known
  countermodel, three times over.
* **The semantic blocker** (`PLLSemUIChar.lean:322,327` and its
  descendants in `PLLSemUILayered`/`PLLSemUIHenkin`): the `mforth`/
  `mback` clauses, the MODAL forth/back conditions of the layered
  bisimulation: matching an R-crossing while preserving agreement at
  the decremented depth, the "need 2d, have 2d−1" promise-financing
  wall.
* **`CimpAnt`** (`LJFO.lean:1342`): mining `A(rest ⇒ ↑↓◯Q′)` from a
  derivation of the modal implication's antecedent whose χ-uses recur
  inside crossed-station material; every structural or measure-based
  finance pays for one crossing, and the second use (the ①/②
  configuration) is unfinanced.

### 5b. Same problem?

Yes. All three are instances of one configuration: **the ∀p side must
traverse a ◯-crossing once more than its finance (budget, bisimulation
depth, termination measure) pays for.** Three independent formal
settings, a budget recursion over G4c, a layered bisimulation over
Kripke models, a structural recursion over a focused calculus, and in
each the identical configuration is the LAST remaining obligation while
everything else is machine-checked. That is strong evidence this is one
problem, not three.

On hard-versus-untrue: the duplication is financed inside derivations
by contraction-free reuse of persistent modal implications, and on the
algebra side it leans on the monad multiplication `◯◯A → ◯A`, the
transitivity-like law. Transitivity is precisely what kills uniform
interpolation for K4 and S4 (Ghilardi–Zawadowski; Bílková), and the
semantic route's escalation ladder (`p∨¬p → φ★ → φ♦`) was already
suspected in-session as a potential Ghilardi–Zawadowski family. PLL is
not S4 and the literature genuinely leaves PLL open, but with the same
wall standing in three routes, UNTRUE has to be treated as live, and
the cheap spend is refutation, not construction. Hence 5c. Two
additional data points cut the other way and should be recorded: the
fuel/pigeonhole finance is NOT structural (it bounds crossings globally
over the finite subformula space), which is exactly how the G4c decider
escaped the same arithmetic; and every extensional test of the UI
statements to date has passed. So the evidence is mixed, and the
discriminator is exactly a wider countermodel search.

There is also a process observation Matthew's framing implies, worth
adopting as a rule: **three campaigns each ended parked on a single
unprovable lemma, and in each case the statement-level attack on that
lemma was run late or narrowly.** The rule now in `CLAUDE.md`: when one
obligation blocks a route, attack the obligation's STATEMENT with the
full testing discipline before any further proof architecture is built,
and when the same obstruction shows up in a second route, treat
refutation as the default next spend.

### 5c. The fresh attack on `CimpAnt`

Review of the marathon's refutation attempts confirms Matthew's
suspicion: the bank's `CimpAnt` cells drew from four shapes per axis,
station size ≤ 2, a single modal implication per station, χ only at the
head position, no corpus seeds, `Q′` at modal depth ≤ 1. Thorough at
the degenerate ends, no frontier extension.

The new attack (`wip/ljfo_attack.lean`) tests the full statement (χ at
every split of every station, side conditions enforced so a certified
fail is a genuine counterexample) in four directions: corpus replay
(the blocker station `[◯p→r, ◯((◯p→r)→◯p)]` itself, with the
p-CARRYING modal implication; the join shape `↓◯p ⊃ ◯p`; the unboxed
blocker), frontier extension (two modal implications crossed, station
size 3, `Q′` at modal depth 2–3, p-placement variations), boundary and
branch coverage (`Q′ = ⊥`, or-shaped `Q′`, the no-row corner
`Q′ = ↓(implication)`, kept boxes with implication content), plus E2/A2
minimality sweeps over the same extended stations (the frontier may
force change #4 in the aggregates rather than in the antecedent
obligation).

Two structural findings arrived before any verdict did:

* **The screening horizon is real here too.** The first (ungated) run
  hung on the blocker station: `sum3 [◯p→r, ◯((◯p→r)→◯p)] = 177,390`
  and the engine cost blows up with it, while the small stations the
  marathon bank used sit at `sum3` 243–729 with interpolant values of
  35–170 nodes. This is quantitatively the G4c room finding again (the
  γ-clause regime needed 10⁵–10⁶-node tables, past `checkB`): in both
  routes the DISCRIMINATING regime of the blocked lemma begins near the
  edge of what the screens can decide. The corrected attack gates cells
  by constructed value size and REPORTS what it skips (no silent caps);
  the interpreter `#eval` bank was also replaced by a compiled driver
  (`lake build attackrun`, the repo's native-oracle pattern), which is
  the right standing form for all future banks. Note `sum3` alone
  over-predicts: the φ★ station has `sum3` ≈ 1.6M yet its E-value is
  only 569 nodes, so the gate belongs on constructed size.
* **A cross-route validation cell now exists** (`wip/ljfo_crosscheck.lean`):
  the semantic campaign PROVED `∃p.φ★ = ¬¬◯⊥` for
  `φ★ = ((◯⊥ ⊃ p) ⊃ (◯⊥ ∧ p)) ∧ ¬¬p`, and φ★ polarises into a legal
  parked station, so `interp`'s E-value has a machine-known correct
  answer to be tested against — the first direct bridge between the
  semantic route's results and the focused calculus's interpolant.
  First verdicts: `¬¬◯⊥ ⊢ E` CERTIFIED YES (the soundness direction
  agrees with the proved strongest value); `E ⊢ ¬¬◯⊥` unknown at the
  40k budget (a flag, escalated at 400k in the native run).

**Results (compiled sweeps + two escalation tiers, 2026-08-11 morning):**

* **Zero certified failures of `CimpAnt`**, across corpus replay,
  crossed-χ, size-3, GZ-nesting, p-placement, boundary and no-row-corner
  strata, with χ at every split position and the statement's own side
  conditions enforced per cell.
* The sweep's flags concentrated on ONE family: p-carrying modal
  implication beside a p-carrying box (`[◯p→r, ◯p]`,
  `[◯p→r, ◯(↓◯p)]`) — exactly the stratum the marathon bank never
  mixed. Escalation at 400k nodes resolved `[◯p→r, ◯p]` (both kept
  variants) and the GZ depth-2 cell to certified YES; two survivors
  remained unknown at 400k: the `[◯p→r, ◯(↓◯p)]` conclusion and the
  φ★ minimality direction `E ⊢ ¬¬◯⊥`.
* **Kernel escalation settled both survivors TRUE** (Matthew's
  direction): `LJFOSearch.search` found derivations at fuel 32
  (`E(φ★) ⊢ ¬¬◯⊥`) and fuel 48 (`E ⊢ A` on the `◯(↓◯p)` cell, and
  `⊢ A` outright over the empty context), each a kernel derivation via
  `search_sound`. Every escalated flag has resolved YES; the earlier
  unknowns were engine reach, not falsity.
* Method finding with standing value: **the focused kernel search
  out-screens the G4c certificate prover on interpolant values by
  orders of magnitude** (seconds at fuel 32–48 versus unknown at 400k
  nodes) — focusing prunes the space the unfocused prover drowns in.
  It is now the escalation engine of record (CLAUDE.md), and it is the
  instrument that can plausibly push INTO the `bchi` screening horizon
  next (the one regime still unscreened; `refute?`'s complete emit
  stage is capped at closure ≤ 12, so "no countermodel" is weak
  evidence exactly there).
* Net position for §5b: the attack found no evidence against
  `CimpAnt` anywhere it could decide, including the corpus seeds
  carrying the known duplication content. The evidence now tilts
  toward TRUE-but-hard, with the fuel/retention route (B) being
  precisely the non-structural finance the three-blocker analysis
  says is needed. The GZ-style risk stays live only past the
  screening horizon, with the kernel-search screen as the named next
  stratum.
* (The E2/A2 minimality sweeps over the extended stations were
  TERMINATED after 8.8 CPU-hours inside their chunks, with zero fail
  or flag records emitted after the horizon report — the unfocused
  prover cannot practically decide the box-wrapped aggregates at
  p-carrying stations, the same reach limit as above. Minimality
  screening at that scale belongs to the kernel-search engine; noted
  as a layer-4 instrumentation item.)

### 5d. Testing doctrine

No repo `CLAUDE.md` existed (the instruction surface was HANDOFF.md,
the old next-session note, and memory, which is why instructions kept
being re-derived). One now does, kept short, with a
"Testing for counterexamples" section carrying the four-direction
discipline above, the three-valued certificate-only verdict rule, the
flag-escalation rule, and the residue-defines-the-next-stratum rule.
Validated in the writing by being applied to `CimpAnt` (the attack file
is the § worked example).

---

## 6. Handover actions taken in this round

* `docs/next-session.md` trimmed to the operational constraints + the
  live thread + the layer-4 brief (now marked PAUSED pending this
  review); the 2026-08-07 full note archived verbatim at
  `docs/archive/next-session-2026-08-07-full.md`.
* `CLAUDE.md` created (above).
* `HANDOFF.md` §11 appended pointing here.
* Layer 4 remains paused; nothing in this round changed a definition or
  a proof. The decision stack for Matthew, in order: (i) whether the
  attack's outcome changes the layer-4 plan; (ii) whether to run
  simplification rounds 1–3 (and how many) BEFORE layer 4; (iii) the
  standing (A′)/(B)/(C) choice, currently (B).
