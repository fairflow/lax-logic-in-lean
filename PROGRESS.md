# PROGRESS — uniform interpolation for PLL, the one-variable programme

2026-07-15 · live session log (Fable 5) · updated in place while work continues.
Read top-down: §1 is the mathematics, §2–4 the tooling questions you asked,
§5 the manual-oracle recipe, §6 the running status line.

---

## 1. Where the mathematics stands

### 1.1 The target

The whole uniform-interpolation development has ONE open `sorry`:
`cascade_low_pos_box` (`wip/absorb_base.lean`), already reduced in
`wip/onevar.lean` (sorry-free reduction) to the semantic residual

> **descent_forcing.**  In every constraint model M, at every world w,
> for one-variable S, Γ, g (all atoms ⊆ {p}), past the threshold
> defect(S,Γ) · (J+2) ≤ c :
>
>   force w (itpA p S fuel (c+1) Γ g)  →  force w (itpA p S fuel c Γ g)

Equivalently (by the mechanised completeness): the derivability
`itpA (c+1) ⊢ itpA c` — the **budget descent**. The ascent
`itpA c ⊢ itpA (c+1)` is already a library theorem (`itp_budget_mono`),
so the descent says: *the ascending budget sequence has stabilised by the
threshold*.

### 1.2 Evidence (oracle-sound, i.e. every `true` is a genuine derivation)

* 24 configurations (natural, rich, adversarial): descent TRUE at every
  b ≥ 1. No counterexample.
* **3-chain confinement REFUTED**: with ⊥ ∈ S (natural — any negation puts
  ⊥ in the subformula space) the interpolants ESCAPE {⊥, ◯⊥, ⊤}: configs
  reaching ¬◯⊥ (stable), and one — **X9** — that CLIMBS:
  S = {⊥, ◯⊥, ¬◯⊥, p, ◯p}, Γ = [¬◯⊥], g = ◯p gives normal-form weights
  1, 2, 39, 143, 566 at b = 0..4, still growing.
* **X9 VERDICT (deep run, oracle-sound): the counterexample candidate is
  DEAD.** With the truncation absorption (§1.3½) + canonicalisation, the
  X9 interpolant classes are

  | b | 0 | 1 | 2 | 3 … 9 (checked) |
  |---|---|---|---|---|
  | ∀-interpolant | ⊥ | ◯⊥ | ◯(¬◯⊥ ⊃ ◯¬¬◯⊥) | **same class** |
  | ∃-interpolant | ⊤ | ¬◯⊥ | same | **same class** |

  Stabilisation at **b = 2**, versus threshold **16** — fourteen levels of
  slack. The earlier "climb" (nf weights 39, 143, 566, …) was pure
  syntactic bloat of one constant equivalence class. Strongest datum: the
  canonical dictionary stays at **5 classes** ({⊥, ⊤, ◯⊥, ¬◯⊥,
  ◯(¬◯⊥ ⊃ ◯¬¬◯⊥)}) across ALL budgets and ALL sub-contexts of the
  recursion — the entire X9 recursion lives in a 5-element state space.
  Total oracle work: 23 identification calls (the memo did the rest).
  En route the oracle certified the RN(◯,{}) collapse
  ¬◯¬¬◯⊥ ≡ ¬◯⊥ (and (¬a ⊃ a) ≡ ¬¬a does the rest by hand).
  H2 (∃-side stabilisation) is empirically TRUE for X9 from b = 1.

### 1.3 The Lean proof development (`wip/onevar_descent_dev.lean`)

Statement under attack (syntactic form; `descent_forcing` follows by
soundness):

> **itpA_descent.**  For all fuel, b, Γ, C, past threshold, one variable:
> G4c [itpA p S fuel (b+1) Γ C] (itpA p S fuel b Γ C)

Proved / reduced so far (file compiles, `sorry`-count = 1 → being split):

1. **∃-side descent is FREE.** `[itpE (b+1)] ⊢ itpE b` is exactly
   `itp_budget_mono.1` — no threshold, no one-variable hypothesis needed.
2. **Base case done** (`itpA 0 = ⊥`).
3. **Successor case reduced** (via `itpA_succ` + `orAll_elim`) to the
   per-disjunct obligation: each disjunct of the (b+1)-table entails the
   b-table.
4. **Key structural discovery** (from reading the ascent's combinator
   `itpAfull_map`): the ◯-goal *truncation disjunct* transfers if and only
   if we can supply
   > **itpE stabilisation (the distilled core).**  Past threshold:
   > G4c [itpE p S fuel b Γ] (itpE p S fuel (b+1) Γ)
   — the ∃-ascent, i.e. the ∃-side has ALSO stabilised. (The free
   direction is the reverse.) With that lemma, the library combinator
   `itpAfull_map` closes the ◯-goal case including all its edge cases.

So the open mathematics compresses to **two pieces**:
   (a) *mechanical bulk*: the per-disjunct map for the non-truncation
       clauses — a ~500-line mirror of `itp_budget_mono`'s clause walk,
       with threshold bookkeeping at the jump clauses;
   (b) *itpE stabilisation at threshold* — the distilled semantic core.

**Honest flag on (a):** jump clauses that do NOT grow Γ (the budget-gated
clauses at the same context) drop the budget without dropping the defect,
so the plain threshold `defect·(J+2) ≤ b` does not rethread through the
induction there. The full cascade in `wip/absorb_base.lean` handles exactly
this with a *seen-set* refinement ((jumpGoals S \ seen).card bookkeeping).
The one-variable statement will need the same refinement — OR this is
precisely where a counterexample would live if the bookkeeping cannot
close. This is the current front line of both the proof AND the refutation
search, and the deep-X9 probe (§3) tests piece (b) directly.

### 1.3½ DISCOVERY (from the shape diagnosis): the X9 recursion + the absorption law

Printing the pure-nf interpolant values (no oracle) exposed a clean
recursion.  Writing g := ◯⊥, n := ¬◯⊥, the X9 interpolants satisfy

    A₁ = g,   E₁ = n,
    E_{b+1} = ¬◯(E_b ⊃ A_b),
    A_{b+1} = P_b ∨ ◯(E_b ⊃ P_b)     where  P_b = ◯¬E_b ∨ ◯(E_b ⊃ A_b).

And the growth-killer, provable in two lines from the ◯-unit:

> **Truncation absorption.**  For every o ∈ others:
> o ⊢ orAll others ⊢ (E ⊃ orAll others) ⊢ ◯(E ⊃ orAll others), hence
>     orAll (others ++ [◯(E ⊃ orAll others)]) ≡ ◯(E ⊃ orAll others).
> The ◯-goal truncation disjunct absorbs its whole disjunct table.

Consequences:
* applied at the assembly site, it kills the ~7×/step raw growth
  (X9 b=2: weight 39 → 22, oracle-confirmed still ≡ the library value);
* it collapses A_{b+1} ≡ ◯(E_b ⊃ P_b) — with the further hand-collapse
  (¬a ⊃ a) ≡ ¬¬a giving P₁ ≡ ◯¬¬◯⊥: these values live in small RN(◯,{})
  territory after all;
* proof-relevant: for ◯-goals the whole `itpAfull` table is ≡ its
  truncation disjunct alone — a derived lemma that could reroute the H1
  clause walk for ◯-goals entirely through the (now H2-fed) guard.

### 1.4 Session steps (brief, chronological)

1. Redirect accepted: back to UI-for-PLL, prove-or-refute at one variable.
2. Probe harness built (`wip/onevar_probe.lean`): efficient oracle + sound
   syntactic simplifier `nf` (raw interpolants blow up ~8×/budget step; nf
   collapses e.g. weight 9,128,167 → 2).
3. 24-config sweep: descent true everywhere at b ≥ 1; interpolants seemed
   confined to {⊥, ◯⊥, ⊤} — then the ⊥∈S configs refuted that confinement
   and produced the X9 climb (sub-threshold, see §1.2).
4. Actual Lean development started (`wip/onevar_descent_dev.lean`), state
   as in §1.3: base + ∃-half closed, successor reduced per-disjunct,
   truncation disjunct isolated, itpE-stabilisation identified as the core.
5. NOW: (i) canonicalising simplifier-as-you-go (§3) to probe X9 past its
   threshold 16 — direct test of the distilled core; (ii) dev file being
   restructured around `itpAfull_map` + the two named holes.

---

## 2. Oracle — state and inefficiencies

**What it is.** `PLLND.search W as fuel V Γ C : Bool`
(`LaxLogic/PLLG4Dec.lean:63`) — backward proof search for the complete
calculus G4c, loop-checked by a visited set V.
* `search … = true` ⇒ genuine derivation, at ANY fuel (`search_sound`).
  Kernel-grade yes.
* `search … = false` ⇒ "not found within fuel" — NOT a certified no.
  (Certified no needs the exponential `decide (G4c …)` or a countermodel.)
* Efficient use = hand fuel: `PLLND.find Γ C` (fuel 10 000,
  `PLLDemos.lean:103`) — the exponential cost of `decide` lives ONLY in
  the `decideFuel` completeness packaging, never in the search itself.
  Measured: weight-6 goal 39 ms via `find` vs >90 s aborted via `decide`.

**Inefficiencies (confirmed this session).**
1. **No cross-call caching.** Every `entails` call recomputes from
   scratch; dedup loops are O(n²)·oracle. Fix: a result cache keyed on
   (Γ, C) at the probe layer — cheap, planned.
2. **Visited set is a `Finset (Finset PLLFormula × PLLFormula)`** —
   set-of-sets comparisons on big formulas; no hashing. Costs dominate
   precisely on the bloated interpolants. Mitigation: simplify BEFORE
   searching (nf/canon), keeping the space tiny.
3. **The space cap W = input weight**: search space scales with formula
   bloat — same mitigation.
4. **The fast memoised searcher (`g4B`/`g4bud`, `wip/g4ill_probe.lean`)
   decides the WRONG calculus** (Iemhoff's G4iLL, which is incomplete for
   PLL — machine-checked gap). Porting its HashMap memoisation to G4c is
   the right medium-term investment (relates to pending task #16).
5. **Raw interpolant construction explodes** (~7×/budget step) — at X9,
   b ≥ 6 is unbuildable even before any oracle call. Hence §3.

---

## 3. Simplification as you go (being built now: `wip/slick_probe.lean`)

**Why it is sound.** The `itpE`/`itpA` clause guards test membership of
*context* formulas (A ∈ Γ, A ∈ S) only — they never inspect interpolant
values. Interpolants are only *assembled* by ∧, ∨, ⊃, ◯. Since PLL-
equivalence is a congruence for these connectives, replacing every
recursive interpolant return by ANY equivalent formula yields an
end-result equivalent to the library's. So a simplifier applied at each
clause return preserves the interpolant's equivalence class — exactly the
object `descent_forcing` speaks about. (Cross-checked against the library
`itpA` by oracle at small budgets.)

**Design.** Two layers:
* `nf` — the syntactic rewriter already in use (Heyting ⊥/⊤ laws, ◯⊤ = ⊤,
  ◯◯ = ◯; each rewrite an equivalence).
* `canon` — oracle-backed canonicalisation: keep a growing dictionary of
  representatives; each new value is nf-ed then identified (entails both
  ways) with an existing representative or added. A syntactic memo avoids
  repeated oracle calls.

**Payoff.**
* *Refutation search:* interpolants stay dictionary-small at EVERY budget,
  so X9 can be probed to b = 18 > threshold 16 — the direct test of the
  distilled core (§1.3(b)). A new dictionary entry appearing past
  threshold = counterexample alarm; freezing = strong support.
* *Proof:* the dictionary that canon builds is a candidate for the finite
  invariant the induction needs (the sublattice the one-variable
  interpolants actually inhabit). If the reachable classes are finite and
  computable, the stabilisation argument has a concrete carrier.

---

## 4. Driving the oracle manually (recipe)

Scratch-file route (recommended). Create e.g. `wip/scratch.lean`:

```lean
import LaxLogic.PLLG4Dec
import LaxLogic.PLLDemos
open PLLFormula PLLND

-- formulas: prop "p", falsePLL, .and, .or, .ifThen, .somehow
def X : PLLFormula := (prop "p").somehow.ifThen (prop "p")   -- ◯p ⊃ p

#eval find [] X                     -- ⊢ X ?         (fuel 10000)
#eval find [X] (prop "p")           -- X ⊢ p ?
#eval search (listWeight [X]) (listAtoms [X]) 3000 ∅ [] X   -- explicit fuel
```

Run with:  `lake env lean wip/scratch.lean`

**Long-running probes — streaming gotcha.** `#eval someIOAction` buffers ALL
its output until the action completes (it goes through Lean's message
stream), so a hung probe looks totally silent. For anything long, define
`def main : IO Unit := …` at top level and run
`lake env lean --run wip/<file>.lean` — that streams to real stdout as it
goes. (This explained every "silent hang" in this session; compile time of
even the big probe file is only ~5 s.)

Reading the answers:
* `true`  — PROVED: a genuine G4c/PLL derivation exists (`search_sound`;
  no fuel caveat on the yes side).
* `false` — not found within the fuel; raise the fuel to gain confidence;
  a *certified* no needs `#eval decide (G4c Γ C)` (exponential — only for
  small weights) or a countermodel.

CLI route: `scripts/laxrun.sh help` (compiled `lake exe laxrun`; drivers
`runSearch`/`runQuant`/`runZoo` in `LaxLogic/PLLExec.lean`) — good for the
packaged demos; the scratch file is more flexible for ad-hoc sequents.

---

## 5. Files

| File | Role |
|---|---|
| `wip/onevar.lean` | sorry-free reduction of the open lemma to `descent_forcing` (1 sorry = the target) |
| `wip/onevar_descent_dev.lean` | the live proof development (§1.3) |
| `wip/onevar_probe.lean` | probe harness: nf simplifier + oracle sweeps (24 configs, X-configs, X9) |
| `wip/slick_probe.lean` | (being written) canon-as-you-go interpolants + deep X9 |
| `wip/lattice_cmp.lean` | RN(◯,{}) toolkit: `entails`/`equiv`/dedup/enumeration |
| `LaxLogic/PLLG4Dec.lean` | the oracle (`search`, soundness/completeness, `decide`) |
| `LaxLogic/PLLG4UITrunc.lean` | interpolants `itpE`/`itpA`, ascent `itp_budget_mono`, combinator `itpAfull_map` |

## 6. Status line (updated as work proceeds)

* [x] PROGRESS.md written
* [x] dev file restructured: compiles with EXACTLY TWO sorries —
      `itpE_stab` (H2, the distilled core) and the `hoth` clause walk (H1).
      The ◯-goal truncation case is CLOSED modulo H2 via `itpAfull_map`
      (guard arithmetic discharged; a `subst`-eliminates-the-wrong-variable
      trap cost three compile cycles, fixed with `rw`).
* [x] canon-as-you-go probe built + cross-checked vs library (all six
      cross-checks TRUE, including the weight-39 X9 value)
* [x] **deep X9 verdict: stabilises at b = 2 ≪ threshold 16; dictionary
      frozen at 5 classes through b = 9; counterexample candidate DEAD;
      H2 empirically true from b = 1** (see §1.2)
* [x] memory + this file updated with the outcome

**Where this leaves the mathematics.**  No counterexample survives at one
variable: every configuration probed (24 broad + X-escapes + X9 deep)
stabilises well below its threshold. The proof of the one-variable descent
is reduced to (H1) the mechanical clause walk and (H2) `itpE_stab`, with
two brand-new handles: the *truncation absorption law* (mechanisable in a
few lines; it collapses the ◯-goal table to its guard disjunct, the very
disjunct H2 feeds) and the *finite-class invariant* the canonical
dictionary exhibits (the induction's candidate carrier). Next session:
mechanise the absorption law, then attack H2 with the seen-set threshold,
then the H1 walk; independently, the 2-variable probe (each quantifier one
free variable) is ready to run on this harness.

---

## 7. 2026-07-18 addendum (from the belief-paper session)

The instruments changed while this file slept; the mathematics above is
untouched. In one line each — details and file pointers in
`docs/ui-notes-belief-session.md`:

* the oracle is **two-sided** now: `G4cTm.find` (fuel-free, returns
  kernel-checkable proof terms) on the yes-side, and
  `CounterEmit.emit` → verified `checkB` → `not_provable_of_check`
  giving *certified* underivability on the no-side — a refuted H1/H2
  instance can be cashed as a machine-checked countermodel, not a fuel
  timeout;
* `emitMin`/`emitMinClean` shrink countermodels (20 → 3 recovers F&M
  Fig. 3, pinned) and `PLLDiagram.lean` draws them (TikZ/SVG);
* the finitised canonical model + truth lemma + enumeration landed
  constructively (`PLLFinComp.lean`, `[propext, Quot.sound]`) — a
  Ghilardi-style semantic route to UI is now attemptable, and
  refutation search over a closure is complete, not merely sound;
* toolchain `v4.31.0` on `main`: native ≈22× the old interpreter.

---

## 8. 2026-07-19 addendum (semantic-route session, worktree branch)

The semantic route (task #33) moved past its universal-property layer;
the mathematics of §1–6 (syntactic route) is untouched. Full statements
and file anchors in `docs/semantic-ui-route.md` §0; everything below is
machine-checked in `LaxLogic/PLLSemUI.lean` (the file's only sorries
remain the two definability targets).

* **The essential-fibre conjecture is PROVED, as an iff.** For p-free ξ:
  ξ is the ∀p-value of some formula in which p is essential iff ⊬ ξ
  (witness `ξ ∨ p`); dually for ∃p iff ξ ⊬ ⊥ (witness `ξ ∧ p`). On the
  closed fragment: essential ∀p-image = RN(◯,{}) ∖ {⊤}, essential
  ∃p-image = RN(◯,{}) ∖ {⊥}. The two exercise lemmas
  (`IsSemAll p M ⊤ → ⊢ M`, `IsSemEx p M ⊥ → M ⊢ ⊥`) are the ⊤/⊥
  exclusions.
* **Certificate method for definability**: substitution instances
  (via truth-set redecorations) and the lower transform of the DOUBLED
  model (two copies stacked on the 2-chain) turn oracle-checkable
  derivability facts into `IsSemAll`/`IsSemEx` proofs. First values
  beyond substitution: ∀p.(p∨¬p) = ∀p.(◯p⊃p) = ∀p.(¬¬p⊃p) = ⊥ —
  with a machine-checked proof that substitution certificates alone
  cannot reach the first.
* **Value-table probe COMPLETE** (`wip/semui_probe.lean`, table +
  analysis in `docs/semantic-ui-1pv-table.md`): ALL 25 one-variable
  classes (weight ≤ 5 + extras) certified on BOTH sides by the
  three-generator basis; every candidate a unique max/min over the
  7-class ladder; values attained {⊥, ◯⊥, ⊤, ¬◯⊥, ◯¬◯⊥}; a fourth
  generator (sideways/Löb) needed exactly at the ◯-guarded classical
  schemata; first ∃-side beyond-substitution value ∃p.(¬◯p ∨ ◯p) = ⊤
  (proved: `semEx_wem_box`). Definability at 1 pv = empirically
  complete conjecture with a uniform syntactic proof target (see the
  table doc). Oracle warning: failing `search` cost is UNPREDICTABLE in
  fuel (non-monotone); cap weights and order cheap attempts first.

### §8 continued — overnight 2026-07-19 (same branch)

* **The reconstruction reduction (PROVED)**: definability follows if
  the generator conjunction (∀-side) / disjunction (∃-side)
  reconstructs M — `isSemAll/isSemEx_of_reconstruction`,
  `semAll/semEx_definable_of_reconstruction`.
* **Fixed bases REFUTED, machine-checked, both sides**: ∀-side at the
  Peirce family — the exhaustive weight-≤7 sweep (2758 formulas) has
  exactly 8 failures, all `(X⊃p)⊃Y` with X ∈ {◯⊥,◯p,◯◯⊥,◯◯p}; Lean
  witness `∀p.((◯⊥⊃p)⊃p) = ◯⊥` (`semAll_peirce`, `allRec_fails`).
  ∃-side at the biconditional `(¬◯⊥⊃p)∧(p⊃¬◯⊥)` (weight 14):
  `∃p = ⊤` (`semEx_bicond_top`, `exRec_fails`); oracle finds the next
  escape at the ◯¬◯⊥-biconditional (weight 16).
* **Repairs oracle-verified everywhere**: ladder-rung substitutions
  (◯⊥ for ∀; ¬◯⊥/◯¬◯⊥ for ∃) fix every found failure; iterated Löb
  to depth 4 reconstructs without new frame constructions.
* **The per-instance support law**: generator pool = substitutions
  over the closed-fragment rungs occurring in M + lowT + sideT.
  Converges with the corrected-Cor-10 constraint-transfer analysis:
  the canonical descriptions must record exactly the ladder rungs of
  cl(M) — the promise/Θ data.

## 9. 2026-07-19 (day session): graduation, the sandwich, the two-sided oracle

* **Graduation**: the theory file is now `LaxLogic/PLLSemUI.lean`
  (root-registered, sorry-free; definability = `Prop`-level conjectures
  `SemExDefinable`/`SemAllDefinable`; 27 flagship audits clean).
* **The constraint–ladder comparison (Matthew's equivalence question),
  PROVED as the sandwich** (`LaxLogic/PLLSemUICtx.lean`, instantiated
  with the packaged tower quantifiers in `wip/semui_ctx_equiv.lean`,
  no sorryAx):

      ξ^C ⊢ᴵᴾᶜ ∀ᴵᴾᶜp.(M^C) ⊢ᴵᴾᶜ (M[p:=χ])^C   (all χ; dually for ∃)

  Bridge lemma `subC_substP`: `(M[p:=χ])^C = (M^C)[p:=χ^C]` for
  p-free C.  So the constraint route = the substitution fragment of
  the ladder route, exactly; the frozen-C failure (§0(j) oracle
  witness ◯p⊃p) is the lowT/sideT gap, now provably so.  A constraint
  -models theorem = closing that gap with per-M constraint families
  (OPEN; fallibility prediction is the first test).
* **The two-sided oracle packaged** (`wip/oracle2.lean`): staged
  decide2 = cheap search → verified battery sweep (FinCM.checkB) →
  deep search → gated emit → UNKNOWN.  Benchmarks below.
* **oracle2 benchmarks** (10 cases: 5 provable incl. weight-34
  reconstruction rows, 5 refutable incl. the weight-40 Peirce
  reconstruction failure): 10/10 correct verdicts, EVERY case 0 ms
  (interpreted); compiled suite 0.02 s CPU total.  Contrast: plain
  one-sided `search` on `allCand(peirce) ⊢ peirce` @fuel 400 grinds
  >100 s interpreted AND >120 s native (both killed) — the
  countermodel stage, not compilation, is what beats the unpredictable
  failing-search cost.  Countermodels arrive minimal (1–3 worlds,
  verified by `FinCM.checkB`).  Correction to the recorded pathology:
  bare `¬¬◯⊥ ⊢ ◯⊥` @500 is 0 ms — the recorded minutes-case had a
  larger antecedent; non-monotonicity itself stands as documented.
* **Toolchain**: this branch is on v4.31.0 — `lean_exe` builds run
  fine (~10 s incremental; stale lakefile segfault comment fixed);
  `lake exe oracle2` is a compiled decision tool.

## 10. 2026-07-19 (afternoon, Matthew's follow-ups): fuel demoted, compiled probes, the prediction lands

* **"Are you using the most efficient versions?" — no, and now yes.**
  The fuel-free `G4cTm.find` (built 2026-07-18, left on the shelf)
  decides the ENTIRE oracle2 benchmark at 0 ms in find-only mode —
  including failing fast on the refutables where fueled `search`
  ground for minutes.  The unpredictable failing cost was an artifact of the
  fueled engine, not the problem.  oracle2 v3: nf preprocessing (the
  built simplifier), battery first, find as the positive engine; fuel
  appears nowhere in the decision path.
* **Compiled probes** (`lake exe ctxprobe/ctxrel/ctxcert`): the
  stalled §0(j) rows ran.  Full chain2 table (9/9) + chain3 (8/9):
  every substitution row commutes, the failures are exactly the
  frame-changing rows (`◯p⊃p` LOW, `◯(◯p⊃p)` SIDE — the latter a NEW
  frozen-C failure), as the sandwich mandates.
* **The fallibility prediction (was OPEN)**: chain2 rel-comm HOLDS
  (all rows, find-term grade); chain3 rel-comm FAILS at both ◯-rows,
  **certified by checkB-verified ONE-WORLD countermodels** — the
  single non-fallible world with only `a0` true, i.e. the α-top
  residue world of the §0(j) analysis, now machine-checked.  Frame
  theories over the same names provably cannot close the lowT/sideT
  gap; the constraint pool itself must grow.  Fork: BOTH ◯-rows certified-refuted by the same one-world model (§0(m)); prediction confirmed on all three test models.

## 11. 2026-07-19 (evening, Matthew's instruction): the general fails-half PROVED

`LaxLogic/PLLSemUIRes.lean` (library, audited; the collapse lemma at
[propext] alone): residue model + ResiduePair (the Lemma-7 shape at a
non-fallible Rₘ-stable world) + the collapse `residue_applyC` (C[x] ↔ x
at the residue point) + diagram derivations `diag_row1/row2` (via
completeness) + engine `residue_obstruction` + headlines
`fails_half_boxp_imp_p` / `fails_half_box_lob`: for EVERY such
constraint, EVERY IsIPCAll-value of the two frame-changing rows, and
EVERY n₀-avoiding frame theory of negated atoms, A :: Θ cannot derive
the translated PLL value.  chain3's §0(m) certificate re-derived as
corollary `chain3_fails_half`.  The fails-half of the fallibility
prediction is now a general THEOREM; the holds-half (chain2 direction)
remains OPEN as a general law.

## 12. 2026-07-19 (late): the holds-half PROVED — the dichotomy closes

Same file (PLLSemUIRes.lean).  ThetaNamed (all pair-names Θ-negated =
all stable worlds fallible) → theta_applyC ([propext]): Θ derives
every C[x] → holds_half_boxp_imp_p (choice-free): every IsIPCAll-value
A of (◯p⊃p)^C is Θ-equivalent to ⊥ (A,Θ ⊢ p by lower+theta_applyC,
then substND p:=⊥); holds_half_box_lob: A ≡_Θ (◯⊥)^C (Θ derives the
value outright and A via greatest at ⋀Θ).  chain2 verdict = corollary
chain2_holds_half.  With §11's fails-half the Lemma-7 dichotomy is a
pair of theorems: commutes iff no Θ-avoiding pair-name — the
fallibility prediction PROVED both ways at the constraint level.

## 13. 2026-07-19: the dichotomy lifted to models — c0Of in the library

FinModel tables + c0Of (Lemma-7 recipe, naming parametric) + falAxioms;
shape lifts c0Of_thetaNamed / c0Of_residuePair (only Rᵢ-reflexivity
needed); model_dichotomy_boxp_imp_p / model_dichotomy_box_lob: for any
finite model, injective p-avoiding naming, any IsIPCAll-value A of the
translated frame-changing row: A ⊢_Θ value ⟺ all Rₘ-stable worlds
fallible.  decide-pins: c0Of reproduces the probes' chain2C/chain3C.
The fallibility prediction is a machine-checked iff at model level.

## 14. 2026-07-19: the pool experiment — disjoint-alphabet saturations REFUTED (certified)

Pools {c0Of m, c0Of double(m), c0Of lob3(m)} on alphabets a/b/c, value
= meet of relative tower ∀-values, target = translated PLL value under
the joint fallibility theory.  chain3, BOTH frame-changing rows: every
sub-pool REFUTED by a one-world checkB-verified countermodel forcing
ALL residue names at once (a0, b3, c0).  Mechanism: interpolants are
alphabet-local, so the joint residue defeats each conjunct
independently; Cmeet-concatenation already dead by the proved
fails-half (combined constraint keeps a residue pair).  Consequence:
frame-changing content is unreachable from the constraint side —
the routes factor (constraints = substitution fragment, exactly;
transforms lowT/sideT = frame content, irreplaceably).  Capstone
target: set-valued residue ⟹ general disjoint-pool obstruction.
Harness note: certified verdicts at sequent weight ~10⁶ in ms.

## 15. 2026-07-19 midnight: frontier row settled — ∀-law REFUTED in Lean

((p⊃◯⊥)⊃p)⊃p: instances all ⊤; lowT ≡ sideT ≡ ¬¬◯⊥; value = ◯⊥;
certified 4-chain countermodel (Rₘ = id ∪ {2→3}, top fallible,
p at {1,2,3}) — pool forced at root, row refuted.  Kernel-decide pins
in PLLSemUILaw: poolAll_insufficient_frontier + reconLawAll_refuted
(¬ ReconLawAll).  ∃-law untouched.  Third generator (depth-3 levelled
construction descending to ◯⊥) is now the named mainline target;
chain4 frame added to Search.defaultFrames + probe battery.  Also:
PLLSearchEx (Hilbert axioms via PLLSearch, answers→decisions, both
#guard-verified; WF-recursion kernel-reduction limitation documented).

## 16. 2026-07-20 overnight: split variant MECHANISED — frontier value PROVED

LaxLogic/PLLSemUISplit.lean (sorry-free, audits pinned at
[propext, Classical.choice, Quot.sound]).  t₃ = the split: duplicate
the Rᵢ-cluster of z isomorphically strictly above itself (whole
cluster, not one point — the pointwise m-zigzag forces this in
non-antisymmetric preorders; on posets = the one-point §0(u) form),
copies carry internal Rₘ and escape only to strict Rₘ-successors, p
on copies ∪ strict cone ∪ F.  Projection = total PBisim.  Payoffs:
semAll_frontier `∀p.(((p⊃◯⊥)⊃p)⊃p) = ◯⊥` (upper half: no ◯⊥ ⇒ some
future has fallibility-free Rₘ-row ⇒ split there refutes the row);
boxBot_derives_frontier; poolAll_not_derives_value (pool provably
below the value it cannot reach); semAll_em_p_via_split (split
subsumes the doubling on ∀p.(p∨¬p) = ⊥).  Fourth machine-checked
modal quantifier value; first beyond the whole transform pool.
OPEN: iterated splits vs the levelled row ◯(◯p⊃p); syntactic splT
(cluster-anchored ⊃-clauses obstruct a naive formula transform;
canonical model is a poset — trivial-cluster form may suffice);
graded law.

## 17. 2026-07-20 overnight: ◯-free fragment AGREES with IPC; split tower ≠ levelled

(1) Matthew's fragment test: PLLSemUIOFree.lean — fallible-top graft
topExt (◯-free forcing unchanged, ◯⊥ global) + flat models (¬◯⊥
global) ⇒ BOTH cone exclusions PROVED: underivable ◯-free M has no
lower bound in cone(◯⊥) ∪ cone(¬◯⊥); ⊤-half + conditional collapse
semAll_value_bot_of_cones (+ ∃-side duals).  Sweep (ofreesweep,
w ≤ 8, 1,758 rows): 0 escapes, 0 unknowns — allCandP ⊢ ⊥ on every
underivable row, exCandP derivable on every consistent row, 7/7 rungs
two-cone covered.  RN({p}) values stay {⊥,⊤} = Pitts.  FV-climb not
blocked at the base; next rung: one ◯, two variables.  OPEN: two-cone
coverage of RN(◯,{})∖{⊥} for the unconditional collapse.
(2) Iterated splits do NOT reach ◯(◯p⊃p): RmClusterInternal invariant
(split + redecorate preserve; forces ◯A⊃A globally) ⇒
splitTower_oneW_forces_lob (AXIOM-FREE) — no split-tower variant of
oneW refutes the Löb row, sideways Rₘ-creation is essential; basis
needs both surgeries.

## 18. 2026-07-20: sufficiency PROVED — RN({p}) definable, Pitts values

ofree_semAll_definable / ofree_semEx_definable (PLLSemUIOFree.lean):
every ◯-free 1-var M has definable semantic quantifiers with values
in {⊤,⊥} — unconditional (classical em on derivability only).
Engine: flatten (non-fallible part; ◯-free forcing preserved at
non-fallible worlds; output flat) + ofreeGraft (fibre flat
countermodel over arbitrary C; projection = total PBisim; fibre
forcing = K-forcing at non-fallible fibres).  Both = semantic
conservativity (Matthew's q_M-atomisation, model-side).  One uniform
construction covers the whole fragment: surgery proliferation is a
◯-depth phenomenon.  ⊤/⊥ halves (derivable/inconsistent) hold for
arbitrary M.

## 19. 2026-07-20 afternoon: parametric point-adjunction — surgeries unified

PLLSemUIAdjoin.lean: adjoin N n₀ U R (anchored point; U = cone, R =
constraint escapes) + ABisim.comp + adjoin_pbisim (AXIOM-FREE): any
PBisim extends along an anchored pair given five cover conditions; Z
accumulates so adjunctions iterate; mback_cover = the promise
mechanism (⋆ may reach any world Z-equivalent to an anchor-successor).
Cores re-derived: adjoinAtP_not_em (doubling), adjoinAtP_not_frontier
(split), lobTower_not_lob (levelled, two-storey tower, sideways
R = {⋆₁}); adjoin_reaches_lob at oneW = exact contrast with
splitTower_oneW_forces_lob.  Global surgeries = uniformizations over
cluster/level multiplicities; one construction, changing parameters.
Merged Matthew's parallel BLL branch (nucleus join + belief paper).

## 20. 2026-07-20: amalgamation reduction — the variable-induction skeleton

PLLSemUIAmalg.lean: relGraft (graft ALONG a bisimulation: fibres =
B₀-related pairs over flatten C; p from K, other atoms pointwise,
agreement by B₀.atoms; fallible-base re-entries only) + pbisim +
force_iff (◯-free, ANY atoms).  Reduction theorems
isSemAll_of_flatAmalg / isSemEx_of_flatAmalgEx: for ◯-free M in any
variables, the PLL semantic spec = two derivability facts + a purely
IPC-side flat amalgamation property (FlatAmalgAll/Ex).  Fallibility +
◯ discharged once; the variable induction lives inside IPC.
flatAmalgAll_bot + semAll_ofree_bot': the 1-var case re-derived as an
instance — "both steps collapse to one".  OPEN: FlatAmalgAll for
Pitts interpolants at ≥2 variables (Ghilardi descriptions / finite
canonical model).

## 21. 2026-07-20: box-commutation law + one-◯ two-variable sweep clean

PLLSemUIBox.lean: semAll_box / semEx_box — IsSem{All,Ex} p φ ψ +
BoxRowAmalg{All,Ex} ⇒ IsSem{All,Ex} p ◯φ ◯ψ; free halves
unconditional (semEx_box choice-free); residues = pure ∀∃-amalgamation
statements (quantifier machinery discharged).  ◯-clause of the
definability induction reduced to residues; ⊃/∨ remain the hard
connectives (as in IPC).  Sweep (oneboxsweep, w ≤ 5, 214 p-rows,
24-slice): 0 anomalies of any kind — fragment preserved, values
compositional (box-commutation on ◯-heads + pointwise laws:
∀p.(◯p∨q)=◯⊥∨q, ∀p.(q⊃◯p)=q⊃◯⊥, ∀p.(◯q⊃p)=¬◯q), current transform
stock covers everything at this weight.  Harness: refute?-first +
23-frame battery + gated decide2 + monotone pruning (matrix 16.8s →
143ms); repeated find-grind lesson → node-budget chip spawned.

## 22. 2026-07-20: residues attacked — promise class discharged, law generates values

PLLSemUIBox extended: Lob0Refutes (level-0/"all promises withheld"
refutation class) + boxRowAmalgAll_lob0 (∀-residue discharged there,
value ⊥) + instances (p, p∨¬p, ¬¬p⊃p) ⇒ FIRST LAW-GENERATED VALUES:
∀p.◯(p∨¬p) = ◯⊥, ∀p.◯(¬¬p⊃p) = ◯⊥ (new), ∀p.◯p = ◯⊥ (re-derived,
consistency).  ∃-side: boxRowAmalgEx_prop ⇒ ∃p.◯p = ◯⊤.  Honest
gap: ◯p⊃p not Lob0 (vacuous at promise-free rows) — general residues
need the canonical-cone graft (second wave).

## 23. 2026-07-20: second wave landed — the description graft complete

PLLSemUIDesc.lean: DescPack (realisation relation; atoms only on
tracked alphabet — filtration problem dissolved by reading protected
atoms from the base) + descGraft (paired fibres; relaxed Rᵢ into
fallible K-worlds, strictly paired Rₘ) + descGraft_pbisim +
descGraft_force_iff (◯ INCLUDED; two fallibility absorptions) +
boxRowAmalg{All,Ex}_of_desc.  The ◯-step of the definability
induction now = finite combinatorics: closure triple with ◯φ ∈
fal/val realised over x by a pack into canonFin cl (truth lemma
bridges membership to forcing).  Open centre: the descriptions
functor and its m-clauses — decidable per closure, oracle-probeable.
Merged: node-budgeted search (chip; find is partial-with-visited-set,
not WF — PLLSearchEx note carries stale attribution, flagged).

## 24. 2026-07-20 pm: descriptions functor built and measured — route corrected, gap row probe-discharged

trace C cl c mechanised (PLLSemUITrace.lean, sorry-free): consistency
by soundness-at-c; clauses atoms/fall/iforth/mforth PROVED (mforth =
the mfal design validation), kback/mback REFUTED machine-checked.
Pack clauses positive in R ⇒ largest pack Realises (axiom-free
union lemma); residue discharges reduce to per-(C,x) triple
realisation.  Pre-triple sandwich PROVED: residue ⟹
Cons⟨pfval(x), {◯φ}∪pffal(x), pfmfal(x)⟩ ⟹ canonical candidate
exists; realised candidate ⟹ residue.  PROBES (desc_probe,
resid_probe, both compiled): full-canonFin target DEAD (gfp empty on
all ∀-instances; kill-chain = promise-forgetting extensions + T⊥ on
F-free rows; rank-stratified dies by round 3, formula-independently)
— but the residues themselves are TRUE on the whole battery by SMALL
GADGETS: proved rows at k ≤ 1, and the GAP ROW ∀p.◯(◯p⊃p) at
k ≤ 2 (47/47: 9 redecorate, 18 one-point, 20 two-point tail with
in-chain Rm and sideways m-exit — lobTowerBase shape).  Corrected
ledger: canonical triples CLASSIFY (consistency crux necessary,
proved), adjunction tails KILL.  Next: mechanise the gap row's
3-case discharge as a Lob0-style class lemma ⇒ ∀p.◯(◯p⊃p) = ◯⊥.
Frame hygiene: onebox fork frames not transitively closed as listed;
probes close on intake (sweeps unaffected — unclosed members cannot
certify).

## 25. 2026-07-20 eve: literature sweep + the Litak–Visser skeleton

Three-agent sweep (standard vocabulary): Visser 1996 = our
construction with the right budget bookkeeping (witnessing triples,
Henkin-depth-financed layered bisimulation — explains the dead
canonical-target gfp exactly); Litak–Visser 2404.11969 = semantic UI
for iSL (coreflection like PLL) — the closest template, §5.1 read in
full; Iemhoff's published UIP claim = the G4iLL paper whose
completeness we machine-refuted; algebra side (amalgamation, model
completion for nuclear Heyting algebras) OPEN in print — our result
would settle it.  Papers in papers/ (untracked).  NEW FILE
PLLSemUILayered.lean: crank (◯ costs 2 under the ∀∃-clause),
LayeredBisim, rank-preservation PROVED (+ consistency corollary
recovering unbounded invariance), sorried pillars: frag_reps_exist,
layered_of_frag_agree (characters), amalgamation (Lemma 5.4 PLL-form
with their proof shape + PLL additions documented).  The official
interpolant construction reinstated: ∀p.M = join of rank-bounded
p-free derivers.  Oracle test (wip/rank_join.lean): the join for
◯(◯p⊃p) certified = ◯⊥, zero unknowns after adding the F-free
3-chain with rigid bottom row (battery gap — the residue probe's own
gadget was the missing countermodel frame).

## 26. 2026-07-20 night: pillar attack begun — Henkin amalgam scaffold

Pillar 1 (frag_reps_exist) delegated to a worktree agent with the
full DNF-over-components blueprint (comps recursion, nonempty
conjunct-lists since truePLL = ⊥→⊥ has crank 1, canonicalisation via
filter-sublists).  Pillar 3 scaffold LANDED (PLLSemUIHenkin.lean):
canonDepth := cl.card − val.card with strict drop PROVED; WitTriple
(Litak–Visser Lemma 5.4 triples, budget 2·depth+1); witAmalgam
(componentwise relations — canonical side carries promise-aware Rₘ —
fallibility from the theory coordinate, atoms from the union) with
ALL frame legality proved; amalgamation_assembled PROVED modulo the
two claims wit_pbisim (projection is the p-variant bisimulation; the
two-case budget argument, Henkin-side moves = trace_iforth /
trace_mforth) and wit_force (pair forces φ ∈ cl iff φ ∈ Δ.val;
◯-case = i-zigzag + m-zigzag + fallible absorption).  When the claims
land, the Layered interface `amalgamation` retires in favour of the
assembled card-budget form.  Pillar 2 (characters, Thm 4.7) queued
behind the agent's bigAnd/bigOr calculus.

## 27. 2026-07-20 late: pillar 2 obstruction MACHINE-CHECKED

layered_of_frag_agree_refuted PROVED (pins standard three): the
Litak–Visser Thm 4.7 form is FALSE over constraint models — chainF
(two-point chain, fallible top, trivial rows) agrees with oneW on
every variable-free formula of complexity ≤ 1 (chainF_oneW_agree,
conservativity: the fallible top forces everything so never blocks an
implication; ◯ needs complexity 2), yet iforth at the fallible top
demands a fallible partner that oneW lacks.  Redesign boundary fixed
in the file: escape-iforth (partner OR fallible successor, DescPack
style) survives the character argument — non-fallible successors
refute their θ⁻ — so pillar 2's open content is exactly the
m-clauses: which row-zigzag weakening is agreement-derivable AND
strong enough for wit_pbisim's budget argument.

## 28. 2026-07-20 night II: forth-m probe clean + the repaired layered form PROVED

wip/mforth_probe.lean: 24 closed frames, 90 systematically generated
variable-free formulas, 2324 agreeing pointed pairs — forth-m
candidates = 0 (a violation would have been an a-fortiori
counterexample to the repaired pillar 2; clean pass = supporting
evidence).  LayeredBisimE mechanised (PLLSemUILayered §3′): the
DescPack clause shape — i-zigzags escape at fallible targets,
m-zigzags may pair fallible witnesses; LayeredBisim.toE embedding;
**force_iff_of_layeredE PROVED first-try** (every escape absorbs by
force_of_fallible, mirroring descGraft_force_iff).  PLLSemUIHenkin
switched to consume LayeredBisimE throughout (WitTriple, witAmalgam,
claims, assembly) — full library green.  Remaining pillar-2 content:
characters for the E-form (agreement ⇒ LayeredBisimE, probe-backed);
then wit_pbisim/wit_force.

## 29. 2026-07-20 night III: character LEGO proved

PLLSemUIChar.lean (sorry-free, pins standard three): force_bigAnd_iff
/ force_bigOr_of_mem (semantic forcing of the finite connectives);
charPos/charNeg (θ± as classical filters over a representative list);
force_charPos; not_force_charNeg (non-fallible worlds refute their
negative character — the fallibility hypothesis is exactly where the
machine-checked obstruction lives); agree_of_char (character
transfer: forcing θ⁺ and refuting θ⁻ yields full list agreement).
Remaining pillar-2 content is now ONE induction: Z α := rank-α
agreement satisfies the LayeredBisimE clauses (escape-iforth via
not_force_charNeg at non-fallible targets; forth-m probe-backed),
with slack bookkeeping for the crank-1 ⊤.

## 30. 2026-07-20 night IV: the m-escape geography MACHINE-CHECKED, axiom-free

Probe extension: fallible-PAIR escape fails on 82 of 2324 agreeing
pairs (non-fallible clause still 0).  Both boundaries now theorems,
ALL AXIOM-FREE: weak_escape_breaks_force_iff (weak m-escape kills
rank preservation — chainFM bottom forces ◯⊥ through its fallible
row-member, oneW cannot); forkF_agree (the fork's bottom agrees with
the lone point on EVERY formula — unconditional, all atoms) +
pair_escape_not_from_agreement (yet no pair-escape layered
bisimulation links them) — incidentally separating logical
indistinguishability from escape-bisimilarity in PLL outright.
SETTLED DESIGN: two relations — LayeredBisimE (pair escape, 4.6-valid,
the OUTPUT format) and NEW LayeredBisimW (weak escape, the INPUT
format agreement can deliver; force_iff provably fails for it);
repaired pillar 2 stated as layered_of_frag_agree_W (sorried,
probe-backed); the amalgamation must bridge E/W inside the amalgam by
routing its ◯-case through the canonical promise components (mfal) —
the structural reason F&M theories carry promises.

## 31. 2026-07-20 night V: the i-clauses of the repaired pillar 2 PROVED

agree_iforth / agree_iback PROVED sorry-free (pins standard three):
the character argument lands for PLL — for a NON-fallible successor
v, the implication charPos(v) ⊃ charNeg(v) fails at the base world (v
witnesses it, via sub_mi for the m-case's future use), its complexity
fits the budget 2α+2 (crank_charPos_le r+1 absorbing the crank-1 ⊤,
crank_charNeg_le r), agreement transfers the failure across, and the
failing instance is the partner — full rank-2α agreement through
frag_reps_exist' + soundness-at-a-point (force_of_deriv).
layered_of_frag_agree_W ASSEMBLED in PLLSemUIChar: Z α := agreement
at rank 2α; mono/atoms/fall/iforth/iback/root all proved;
sorry-footprint EXACTLY the two weak m-clauses (probe: 2324/0).
Pillar 2 is now: two m-clause character derivations away.

## 32. 2026-07-20 close: the m-clause hunt at scale

mforth_probe extended with 240 pseudorandom frames (4–6 worlds,
closed random relations, up-closed fallible sets; fingerprints
precomputed): 746,108 agreeing pairs — NON-fallible forth-m
violations: 0 (the W-form m-clause is now backed at scale; the pure
statement of resolution (a) very plausibly TRUE, proof still open);
fallible-PAIR failures: 22,506 (the machine-checked boundary of
§30 confirmed en masse).  Ledger at close: pillar 1 PROVED; pillar 2
= i-clauses PROVED + two probe-backed m-sorries with the ∀∃ analysis
recorded (§0(gg)); pillar 3 scaffolded to wit_pbisim/wit_force with
the promise-routed ◯-case as the designed bridge.  Next session:
wit_force's ◯-case via canonical promises (trace_mforth prototype),
then wit_pbisim's two-case budget argument, then Thm 5.1 assembly ⇒
∀p.◯(◯p⊃p) = ◯⊥.
