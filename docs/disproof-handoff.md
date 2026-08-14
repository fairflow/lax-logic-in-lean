# The DISPROOF investigation — dedicated handover

*Created 2026-08-13.  This file is the standing handover for ONE
thread: building a calculus in which non-provability is established by
a POSITIVE derivation.  It is deliberately separate from `HANDOFF.md`
(repo-wide), `docs/next-session.md` (whatever is live), and the UI
handovers.  Append dated sections; do not rewrite.*

**Scope rule.** If a question is about uniform interpolation, it does
not belong here.  The UI campaign is PARKED by Matthew's decision
(2026-08-13): no UI work until the disproof side has more machinery
and results.

---

## 1. The goal, stated so it can fail

A refutation should be a **finite syntactic object, built forwards by
rules, checkable by a decidable rule-application predicate** — not a
countermodel found by search and not a failed proof search re-read.
Then "REFUTED" is as cheap as "PROVED" under the machine-checked
mandate, and the 109 open flags of the closed-fragment catalogue
become attackable.

Success criterion, concrete: **derive a sample of the catalogue's 57
pinned crank-7 separations as `Reject` derivations** (calibration),
then settle flags the battery could not (discovery).

## 2. Where the thread stands (2026-08-13)

### Live: `Reject/` — the forward, model-generating calculus

Template: Fiorentini–Ferrari, FRJ(G) (TABLEAUX 2017 appendix read at
source; TOCL 2020) and their JLC 31(3) 2021 S4 model-generation
calculus (**paywalled — abstract only; obtaining it is a task**).  The
principle: *rules ARE model constructors; each rule's soundness is a
forcing lemma about the construction*.

PROVED, and **all four core lemmas are AXIOM-FREE**:

| name | role |
|---|---|
| `addRoot` | the constructor: a new root BELOW a model |
| `addRoot_force_some` | forcing unchanged above the new root — why this is the safe direction |
| `boxRefuteHere` (◯∈) | refute `◯A` at the root: root and its `Rm`-cone refute `A` |
| `boxRefuteAbove` (◯∉) | refute `◯A` via a world above with no `Rm`-successor forcing `A` |
| `boxHolds` | the ◯-POSITIVE rule (carry `◯A` in the root's context) |
| `solo`, `solo_force_somehow` | base case; `◯` is the identity at a single world |
| `not_laxND_of_root` | read the conclusion off the root → certified PLL underivability |

`Reject/Demo.lean`: `⊬ ¬◯⊥` and `⊬ ◯p` as CONSTRUCTION TERMS.

### The two screens that licensed this (both green, both re-runnable)

* **arity** (`lean_exe frjprobe`): the ◯-rule's arity = number of
  `Rm`-MAXIMAL successors.  **reduced + confluent ⟹ 100% unary**
  (52,800 worlds at n=3).  Reducedness is the load-bearing condition;
  confluence alone does nothing.  Full PLL's arity grows with frame
  size (Goranko's `Alt_n`), so **PCLL is the easier target** — a
  genuine inversion.
* **`Cl` transfer** (`lean_exe clscreen`): FRJ absorbs left rules into
  a closure `Cl`, valid because a world is `Cl` of its determining
  part.  The literal IPC choice (atoms + implications) **FAILS for
  PLL**, 32 certificates, witness `◯(p ∧ ◯q)` at `deep5` w=2,3.
  Adding ◯-formulas closes it: **0 failures in 156 cells**.  So the
  modal zone in the sequent is FORCED, not a design flourish.

### Retained but NOT active: `BiLax/`

* `not_laxND_iff_coimp_sat` — **`φ ⊬ ψ ⟺ (emb φ ⤙ emb ψ) satisfiable`**,
  machine-checked both directions.  Its role: the SPECIFICATION a
  `Reject` derivation meets (the model a derivation builds witnesses
  exactly that ∃, by reflexivity of `Ri`).  Nothing in the FRJ route
  consumes it.
* `⤙` needs NO new frame conditions (persistence uses only
  `Ri`-transitivity).  All of `Rc`/`square_c`/`counit_c`/`serial_c`
  exists for `◯∃` alone.
* **`◯∃` is currently UNUSED machinery.**  It collapses to the
  identity over the natural class (`colax_collapse_of_rm`, proved),
  needed a whole extra relation to be non-trivial, and appears in
  neither certified refutation.  Not refuted as a concept; not needed
  for disproof.
* Rounds 1–2's Hintikka/checker machinery is a COUNTERMODEL
  CONSTRUCTOR.  Both round reports carry corrections saying so.

### Killed, with certificates

* Skura-style rejection systems: **wrong template** (non-analytic;
  `r_mp` hides an IPC proof and `r_sb` a substitution guess — model
  search inside a side condition).
* Candidate ◯-rejection rules R3 (`⊣φ / ⊣(◯φ⊃φ)`) and R4
  (`⊣φ / ⊣¬¬◯φ`): certified Ł-soundness violations (`lean_exe
  rejscreen`).  R1, R2, R5 survive but show no PCLL-discrimination
  witness — the Kreisel–Putnam danger sign, still open.
* `addTop` (adjoining a fallible top to satisfy `serial_c`):
  **UNSOUND** — makes `◯φ` true everywhere.  Corpse kept in
  `BiLax/Internal.lean`.

## 2b. The adversarial pass — DONE (2026-08-13), and it changed T1

`Reject/Audit.lean`, all pinned, three of five answers good and two
that constrain the join rule.

| question | verdict |
|---|---|
| Are `boxRefuteHere`'s premises vacuous or over-strong? | **Neither** — `boxRefuteHere_exact` proves they are EXACTLY "no `Rm`-successor of the root forces `A`" |
| Is `S = ∅` legal, and does it break anything? | Legal (`emptyS`); the rule stays sound, as an instance of the above.  Documented, not a defect |
| Does `addRoot` preserve REDUCEDNESS? | **YES** (`addRoot_reduced`) |
| Does `addRoot` preserve CONFLUENCE? | **NO** — `addRoot_not_confluent`, machine-checked counterexample |
| Do the rules COMPOSE to a real result? | **YES** — `boxp_not_p`: the repo landmark `◯p ⊬ p` by construction |

**The finding that constrains T1.**  The counterexample is two
incomparable worlds with identity relations (confluent and reduced);
adding a root whose modal cone is one of them destroys confluence —
`Rm root (some true)` and `Ri root (some false)` have no common
completion.  This matters because the **unary-arity licence for the
◯-rule holds on reduced AND confluent frames** (docs/frj-lifting.md
§3).  A calculus whose constructor leaves the confluent class loses
that licence.  So T1 must choose, EXPLICITLY:

* **(a)** carry a confluence side condition on the join (stay in the
  class where the ◯-rule is unary — the PCLL-first route); or
* **(b)** accept non-confluent constructions and give the ◯-rule its
  general list-of-premises form (Goranko's `Alt_n` shape, heavier to
  mechanise).

Recommendation: **(a)**, consistent with "PCLL is the easier target".
Either way the choice must be made and recorded, not drifted into.

**Also fixed**: `boxHolds` was INCOMPLETE — it could witness `◯A` at
the root only through a PROPER `Rm`-successor, missing the reflexive
case where the root itself forces `A`.  `boxHoldsRoot` supplies it.
Lesson for T1: check the reflexive/degenerate case of every new rule.

## 3. The task queue, in Matthew's agreed order

### T1 — the JOIN rule  ⟵ START HERE
Generalise `addRoot` to several premise models: disjoint union + fresh
root, with the join declaring which components are `Rm`-successors
(subject to `Rm ⊆ Ri`, reflexivity, transitivity, and the
◯-positive obligation as a side condition).  Without it the calculus
builds only linear models, which is why the demos are the corpus's two
smallest facts.  **Model: Opus 5. Effort: high.**  Reason: design plus
fiddly dependent-type plumbing (a `Sigma`/sum world type), and the
soundness lemmas must be got right first time or the whole tower
leans.

### T2 — COMPLETENESS
The FRJ Lemma 4 analogue: from any countermodel, extract a derivation,
by induction on world HEIGHT (then sequent type, then `|C|`).  Needs
reducedness for the measure to decrease — the second place
reducedness is load-bearing.  **Model: Opus 5. Effort: max.**  Reason:
this is the hardest mathematics in the thread and the point where it
either becomes a calculus or stays a certificate format.  Do not
delegate; do not interleave.

### T3 — the SEARCHER
Forward saturation over the finite sequent set (goal-parametrised, so
termination is structural — this is exactly what the labelled route
lacked).  Compiled `lean_exe`, streaming one line per cell, per repo
doctrine.  **Model: Sonnet 5 for the engine after Opus 5 fixes the
saturation strategy. Effort: medium–high.**  Reason: once the rules
are frozen this is engineering, and Sonnet is the better
cost/throughput point for grind.

### T4 — the 109 FLAGS
Calibrate on the 57 pinned separations, then attack the flags.
**Model: Sonnet 5 (runs, triage), Opus 5 for interpreting residue.
Effort: medium.**  Mechanical once T3 lands.

### T0 (parallel, cheap, do anytime)
Obtain the JLC 2021 S4 paper — institutional access, interlibrary, or
email the authors.  It will very likely have solved T1's side
conditions and T2's induction for `□`.  **Model: Haiku 4.5 or a
research subagent. Effort: low.**

### Standing before every proof is scoped
Adversarial pass on `Reject`'s current rules — in particular whether
`boxRefuteHere`'s side condition is doing real work or is vacuously
satisfiable on the constructions we can build.  **Model: Opus 5.
Effort: high.**  Four hours old, no adversarial pass yet.

## 4. The systematic method Matthew asked for

Not ad-hoc screens per question, but a standing pipeline.  Four
stages, each with the repo's existing tooling named:

1. **CANDIDATE GENERATION — `tools/FrontierSampler`.**  Stop
   hand-picking rule shapes and corpus cells.  Generate candidates
   stratified by the residue shape of the previous round (repo
   CLAUDE.md's standing rule).  Applies to: candidate ◯-rules, join
   side conditions, and the formulas a searcher is calibrated on.
   The `rejscreen` corpus was hand-built and was UNDER-POWERED because
   of it (the instantiation defect, §"corrections" below) — exactly
   what the sampler exists to prevent.
2. **EXTENSIONAL ATTACK — the four directions of repo CLAUDE.md.**
   Corpus replay first (the G4iLL blocker, the catalogue's merge
   sites, the φ★/φ♦ ladder), then boundary cells, then frontier
   extension, then branch coverage.  Three-valued verdicts; `fail`
   only on a certificate; `flag` never dropped.
3. **EFFICIENT COMPUTATION — compiled harnesses, never `#eval`.**
   `lean_exe`, one appended line per cell, gated by CONSTRUCTED value
   size, every skip reported.  The four harnesses this thread already
   has (`frjprobe`, `clscreen`, `rejscreen`, `s0screens`) are the
   pattern; a fifth for join side conditions is T1's companion.
4. **VERIFICATION — discover-then-pin.**  Search untrusted, certify by
   kernel.  `BiLax/Check.lean`'s `FinBranch → by decide → Hintikka`
   is the worked example; `Reject` needs its analogue so searcher
   output becomes a construction term automatically.

**The route from proof theory to computation and back**, stated as the
standing shape: a rule is DESIGNED from the semantics (a forcing
lemma), SCREENED by a compiled harness before any proof is scoped,
IMPLEMENTED with its soundness lemma, and CONSUMED by a searcher whose
output is re-certified by the kernel.  Every arrow in that cycle
exists in the tree already; T1–T4 walk it once more.

## 5. Corrections made in this investigation (keep, do not repeat)

* Rounds 1–2 were presented as a disproof engine; they are a
  countermodel constructor.  Corrected at the head of both reports.
* "The ∀∃ clause forces a hybrid deduction–refutation rule" — TRUE for
  a backward calculus, FALSE for a forward one.  The model is the
  derivation's own product, so "all `Rm`-successors" is a
  construction-time side condition.
* "On the closed fragment PCLL ≈ PLL" — FALSE; this repo's own
  kernel-pinned merges witness `PLL ⊊ PCLL` there.  The merges are
  SPARSE (4 of 680 cells).  The screen's empty discrimination column
  was an INSTANTIATION defect.
* The Brunner–Carnielli reference is REAL (*J. Applied Logic* 3
  (2005) 161–184) but the duality is **provability ⟷ refutability**,
  so non-provability stays existential on both sides — the wrong
  category by Matthew's own ∀∃/∃∀ criterion.

## 6. Replay

    lake build Reject          # the calculus + demos
    lake build BiLax           # internalisation, retained machinery
    lake exe frjprobe          # ◯-rule arity by frame class
    lake exe clscreen          # the Cl transfer screen
    lake exe rejscreen         # Kreisel-Putnam screen for ◯-rules

Docs: `docs/frj-lifting.md` (the design + both screens),
`docs/bilax-b-report.md` (literature + corrections),
`docs/bilax-plan.md`, `docs/bilax-round{1,2}-report.md` (corrected),
`docs/pcll-closed-fragment-catalogue.md` (the acceptance corpus).

---

## 2026-08-14 (late) — the normalisation pipeline repaired; the RN dictionary's true status

Standing item adopted at Matthew's direction: **whenever equations are
banked, re-run the loop** (`rwscreen`, then `rnextend`, then promote
anything that closes, then re-pin the axioms). Full record:
`docs/rn-dictionary-status.md`. Summary for whoever takes T1:

**Two defects found and fixed.**

1. `Rewrite/Catalogue.lean` had harvested all 323 cell theorems of
   `wip/rnDict.lean` by name, but that file proves only 236 — 87 are
   `sorry`, and **four are REFUTED** (`cAnd_8_10`, `cImp_9_4`,
   `cImp_12_4`, `cImp_14_4`: the stated collapse to `q0` is FALSE).
   So `rndSet` and `fullSet` carried `sorryAx`, and four rules
   rewrote a formula to one *not* interderivable with it. `RwRule.ok`
   is exactly what makes `norm_interd` unconditional, so a `sorry`ed
   `ok` voids that guarantee silently. Fixed: 236 proved cells only,
   with `#print axioms rndSet`/`fullSet` now `#guard_msgs`-pinned as a
   standing guard against a repeat.
2. The canonicaliser was fighting its own rules: `canon` sorts ∧/∨
   arguments, the harvested rules were stated in the dictionary's
   argument order, so canonicalising a goal moved it out of reach.
   A control against the cells the table *provably* closes read
   **47/237**. Fixed with `canonRule`/`canonSet` (rules through the
   same canonicaliser — sound for free) and `simpIter` (alternate
   `norm` and `canon` to a fixpoint). Control now **237/237**.

**Use `Rewrite.simplifyWith Rewrite.fullSetC fuel φ`** — not
`simplify`, not `fullSet`, not `norm`. Measured gain over the previous
figures: flat cells rewritten 68% → **89%**, crank cut 21% → **34%**,
distinct forms 96 → **28**; nested corpus 167 → **25** distinct forms
(floor 15) with crank down 40%.

**Can the method extend the RN(◯,{}) analysis? No, and the negative is
informative.** `lean_exe rnextend` tests whether the simpset closes any
of the 87 unproved dictionary cells — a syntactic match of normal
forms would be a certificate, needing no search. **0 of 87**, with the
control at 237/237 in the same run, the fifteen representatives still
pairwise distinct (15/15), and the four refuted cells correctly *not*
matched. Rewriting is congruence closure over banked equations, and
the open cells are by construction outside it: recombination cannot
settle them. Only a new proof search or a ≥5-world confluent
countermodel can.

**What this hands T1.** The 83 open cells are a concrete target list
(⊃ 43, ∨ 28, ∧ 14, ◯ 2 — the implication table is where the dictionary
is weakest, which is exactly where a refutation calculus should bite),
machine-readable as `RnExtend.openCells` in `wip/rn_extend.lean`. If
the join rule makes branching countermodels constructible, these are
the first cells to aim it at. Also inherited: the *pattern* for a
trustworthy null result — control plus adversarial check in the same
run — which T1's screens should follow.

---

## 2026-08-14 — T1 DONE: the JOIN rule, and the confluence decision

`Reject/Join.lean` (build: `lake build Reject`; screen: `lake exe
joinscreen`, source `wip/join_screen.lean`, output
`wip/join_screen_out.txt`).  The calculus is no longer restricted to
chains.

### The construction, and why it factors

    join Mods D  =  addRoot (union Mods) D

`union` (the disjoint union of the premise models, world type
`Σ i, (Mods i).W`) is the only new constructor; the fresh root is the
existing `addRoot`.  That factorisation is the design decision that
made T1 cheap: every lemma of `Reject/Build.lean` —
`addRoot_force_some`, both ◯-refutation rules, `boxHolds`/
`boxHoldsRoot`, `addRoot_reduced`, `not_laxND_of_root` — applies to a
join unchanged, and the dependent-type plumbing is confined to one
inductive family (`Lift`) whose single constructor says the union
relates only worlds of the same component.  `rcases` on it recovers
the component with no transport, which is why every core lemma below
is axiom-free.

### PROVED, with pins (all transcribed verbatim, `#guard_msgs`-pinned in the file)

| result | statement | pin |
|---|---|---|
| `union_force` | forcing inside a component is unchanged by the other components | *no axioms* |
| `join_force_comp` | the preservation lemma for the join (the analogue of `addRoot_force_some`) | *no axioms* |
| `join_force_box_iff` | **the ◯ rule at a join, exactly**: root ⊩ ◯A ⟺ (root ⊩ A ∨ some cone world forces A) ∧ every component world has an `Rm`-successor forcing A | *no axioms* |
| `joinBoxRefuteHere` / `joinBoxRefuteAbove` / `joinBoxHolds` | ◯∈, ◯∉, ◯-positive, componentwise | *no axioms* |
| `join_refute_box_iff` | **the two refutation rules are jointly EXACT** — the root refutes ◯A iff ◯∈'s premises hold or ◯∉'s do | `[propext, Classical.choice, Quot.sound]` |
| `addRoot_confluent_iff` | confluence of `addRoot`, exactly: `MutuallyConfluent M ∧ ∀ s t, S s → ∃u. s Rᵢ u ∧ t Rₘ u` | *no axioms* |
| `union_confluent_iff` | the union is confluent iff every premise is | *no axioms* |
| `join_confluent_iff` | the side condition, exactly | `[propext]` |
| `join_confluent_of_cone_empty` | confluent premises + empty cone ⟹ confluent join | `[propext]` |
| `join_cone_empty_of_confluent_branching` | a confluent BRANCHING join has an empty modal cone | `[propext]` |
| `join_empty_box_iff` | 0 premises: `◯` is the identity at the root | `[propext]` |
| `join_unit_box_iff` | 1 premise: the modal rule degenerates to `addRoot`'s | `[propext]` |
| `Iso.force` | **forcing transfer**: isomorphic constraint models force the same formulas at corresponding worlds | *no axioms* |
| `join_unit_force` | 1 premise: the join agrees with `addRoot` **POINTWISE** — every world, every formula | *no axioms* |
| `not_derivU_of_root` | a confluent root certifies **PCLL** underivability | `[propext]` |
| `rho6_needs_branching` | every world refuting `¬¬◯⊥ ∨ ¬◯⊥` has two `Ri`-INCOMPARABLE successors | `[propext, Classical.choice, Quot.sound]` |
| `not_derivable_rho6` | **`⊬ ¬¬◯⊥ ∨ ¬◯⊥`** (catalogue class ρ6 = t 5 = q7, crank 4) | `[propext, Quot.sound]` |
| `not_derivU_rho6` | **`⊬_PCLL ¬¬◯⊥ ∨ ¬◯⊥`** — same derivation, read in PCLL | `[propext, Quot.sound]` |

`MJ_confluent` `[propext]` and `MJ_root_branches`
`[propext, Classical.choice, Quot.sound]` are pinned too.  22 pins in
all; the build fails if any drifts.

### THE CONFLUENCE DECISION: **(a)**, and why

**Taken: (a) — the join carries a confluence side condition.**  Not
drifted into; the alternative was screened and priced.

The condition is exact, not a sufficient guess:

    MutuallyConfluent (join Mods D)
      ⟺ (∀ i, MutuallyConfluent (Mods i)) ∧ ConeDominates Mods D

where `ConeDominates` is `∀ s t, D.S s → ∃u. s Rᵢ u ∧ t Rₘ u`.  The
audit's `addRoot_not_confluent` is exactly the instance where the
second conjunct fails, so the counterexample is now explained rather
than merely recorded.

**What it costs, stated as a theorem, not a hope.**
`join_cone_empty_of_confluent_branching`: when the join genuinely
branches — two distinct components, one carrying a cone world, the
other inhabited — confluence forces the root's modal cone to be
EMPTY.  In the union, `s Rᵢ u` keeps `u` in `s`'s component and
`t Rₘ u` keeps it in `t`'s, so no common completion exists across
components.

**Why that is a design and not a restriction.**  On a confluent frame
`w ⊩ ◯A ⟺ ∃u. w Rₘ u ∧ u ⊩ A` (`force_somehow_iff_of_confluent`,
already in the tree).  A branching root's only `Rm`-successor is
itself, so it witnesses `◯A` through itself: **the ◯-rule at a
branching root is unary, with the root as its own witness** — which is
precisely the arity licence docs/frj-lifting.md §3 measured (reduced +
confluent ⟹ 100% unary, 52,800 worlds at n=3) and which option (b)
would have thrown away.

**And it pays.**  Because the constructions stay confluent, a
refutation certifies underivability in **PCLL** as well as PLL
(`not_derivU_of_root`, on the tree's `ConfluentU.derivU_sound`).  PCLL
is the logic the acceptance corpus is stated in
(docs/pcll-closed-fragment-catalogue.md), so option (a) makes the
calculus speak the corpus's own language.  Option (b) would have
bought unrestricted cones at the price of a list-arity ◯-rule
(Goranko's `Alt_n` shape) and PLL-only conclusions.  The general rules
are nonetheless proved here unconditionally — `join_force_box_iff` and
the three rules carry no confluence hypothesis — so (b) remains
available without redoing any of this work; only the side condition
would be dropped.

### What the screens found

`lean_exe joinscreen`: 16 cells × 24 formulas, seven sections, each
with a control that must fail in the same run.  **All seven green**
(`VERDICT A=true B=true C=true D=true E=true F=true G=true`).

* **A** constructor laws: 16/16 well-formed.  Control A′: an
  `Rm`-cone that is not `Rm`-upward closed, and a root atom absent
  from a component, are both REJECTED — the two `RootData` laws do
  real work.
* **B** preservation: 984 (component-world × formula) cells, 0
  mismatches.  Control B′: of 2 well-formed cross-linked joins (an
  `Ri` link between two components) 1 BREAKS preservation, certificate
  `comp 0 world 0 formula ¬◯⊥` — the check has teeth.
* **C** the exact ◯ rule: 360 cells, 0 mismatches.  Control C′: the
  INCOMPLETE rule (the `boxHolds` defect the audit found — no
  reflexive disjunct) is exposed on 8/15 cells, witness `◯⊤`.  The
  degenerate case is therefore covered by test as well as by proof.
* **D** confluence: the characterisation agrees with `confl` on 16/16
  cells; the branching corollary holds on 4/4 branching cells with a
  non-empty cone.  Both are now theorems.
* **E** degeneracy: 5/5 single-component cells agree POINTWISE with an
  independently-written `addRoot`.  Now also PROVED — see the
  addendum below.
* **F** soundness, adversarially: 7 sequents certified derivable by
  the searcher IN THE SAME RUN — including the G4iLL blocker
  `◯((◯p⊃r)⊃◯p), ◯p⊃r ⇒ r` — and no cell's root witnesses any of them
  as refuted.  Control F′: 7/16 cells refute `¬◯⊥∨◯⊥`, 3/16 refute
  `(p⊃q)∨(q⊃p)`, so the pipeline fires.
* **G** which targets NEED branching (added after the screen corrected
  the first choice of target — see below).  Exhaustive chain battery:
  2,378 closed chains ≤ 5 worlds, 5,510 p,q-chains ≤ 4 worlds.
  Needs-branching in the corpus: `¬¬◯⊥∨¬◯⊥` (ρ6), `¬¬◯⊥∨◯¬◯⊥` (ρ9),
  `g1` (ρ11), `r1` (ρ12), and the control `(p⊃q)∨(q⊃p)`.  Positive
  control (Gödel–Dummett must need branching) and negative control
  (`◯p`, `¬◯⊥∨◯⊥` must be chain-refutable) both pass.

**A correction the screen forced.**  The first choice of worked
target, `¬◯⊥ ∨ ◯⊥` (ρ4), does NOT need branching: a single
`addRoot` over the two-world chain refutes it at the root (the root
refutes `◯⊥` through its own trivial modal cone, while a world above
forces it — heredity runs upward only).  Section G was written to
choose the target on evidence instead, and `rho6_needs_branching` then
upgrades that evidence to a theorem: any world refuting ρ6, in any
constraint model, has two `Ri`-incomparable successors.  So the worked
composition provably cannot be built by `addRoot` alone.

### Normalisation (§H), reported as measured

On this corpus the certified pipeline
`Rewrite.simplifyWith Rewrite.fullSetC 12` rewrites **1/24 cells (4%)**,
24 → 23 distinct forms, crank 72 → 70 (**2%**) — far below the 89% /
34% of `rwscreen`'s flat corpus.  The reason is the corpus, not the
normaliser: these are the catalogue's own canonical representatives,
which are already in normal form.  The CONTROL in the same run
confirms it — on a scrambled corpus (`⊤∧(φ∨φ)`, `◯◯φ`) the pipeline
rewrites **48/48 (100%)**, 48 → 32 distinct forms, crank 243 → 169
(**30%**).  Per `docs/rn-dictionary-status.md`, a low rate reported
without that control would not have been trustworthy.

### The banking loop

**No new certified `Interd` was established by T1** — the results are
forcing lemmas and underivabilities, not interderivabilities — so
there is nothing to bank and `rwscreen`/`rnextend` were not re-run.
Recording the negative explicitly so the standing item is not silently
skipped.

### What T2 (completeness) inherits

* The constructor is now **complete for branching**: any finite family
  of premise models can be joined, and `join_force_comp` says the
  premise refutations survive the join verbatim.  The Lemma 4 analogue
  can therefore decompose a countermodel into components without
  re-proving anything about forcing.
* **The rules are EXACT, not merely sound.**  `join_force_box_iff` and
  `join_refute_box_iff` are iffs, so the completeness direction does
  not need new modal lemmas — it needs only to produce the premises,
  which are stated entirely inside the components.
* **The class is fixed**: reduced (`addRoot_reduced`) and, under the
  side condition, confluent (`join_confluent_iff`).  Both of the
  places docs/frj-lifting.md §5 says reducedness is load-bearing — the
  unary arity and the height induction — are therefore available.
* **The height measure is safe under the join**: the root is strictly
  below every component world and components are mutually
  `Ri`-incomparable (`Lift.fst_eq`), so `h(root) = 1 + max h(premise)`.
  This is the measure T2's induction needs; it has not been mechanised
  yet and is the first thing T2 should write.
* **A calibration target exists**: `not_derivU_rho6` is the first
  catalogue class settled by construction rather than by search.  The
  57 pinned crank-7 separations are the rest of the calibration set,
  and §G's list (ρ6, ρ9, ρ11, ρ12) says which of them need the join.
* **A forcing-transfer lemma is available** (`Iso.force`, added the
  same day — see the addendum): isomorphic constraint models force the
  same formulas at corresponding worlds, axiom-free and stated with an
  explicit two-sided inverse, so nothing classical enters.  T2 will
  want it as soon as it renames or quotients models.

### Addendum (same day) — the unary degeneracy is PROVED, not screened

The one item left open above is closed.  Three new results, all
`#guard_msgs`-pinned and all **axiom-free**:

* **`Iso.force`** — the general forcing-transfer lemma.  `Iso C D` is a
  bijection of worlds that reflects and preserves both relations,
  fallibility and the valuation; stated with an explicit two-sided
  inverse rather than a surjectivity hypothesis, so no choice is
  needed.  The two quantifier clauses (`⊃`, `◯`) are where the
  inverse does the work: a successor on the target side is pulled back
  before the induction hypothesis applies.
* **`unitIso`** — a unary join IS an `addRoot`, via the map that
  forgets the (unique) component index (`Option.map Sigma.snd`).  Every
  field is `Iff.rfl` except the two relation clauses, where `Lift`'s
  single constructor is introduced and eliminated.
* **`join_unit_force`** — `(join (fun _ : Unit => M) D).force x φ ↔
  (addRoot M (unitRootData D)).force (x.map Sigma.snd) φ`, for EVERY
  world and EVERY formula, with `join_unit_root_force` the root
  instance a derivation reads.

So `joinscreen` §E's 5/5 pointwise agreement is now a theorem, and the
boundary cell the doctrine demands of a generalisation — the new
constructor must reduce to the old one when its extra freedom is
unused — is discharged by proof.  25 pins in the file.

**T2 is unblocked**: nothing in the join is now screened-only.
