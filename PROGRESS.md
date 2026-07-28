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

## 33. 2026-07-20 late: Lemma 5.4 mechanics extracted; canonical LEGO PROVED; same-trace no-descent REFUTED

Re-read Litak–Visser pp. 21–23 line by line.  Their proof balances on
(1) strict theory growth for every K-side-first truth-lemma move (the
⊃ ψ-trick, which ports; the Lewis-arrow <-maximality trick, which
needs Löb well-foundedness and does NOT port — PLL's reflexive Rᵢ
means a ◯χ-refuter can never force ◯χ), and (2) the primed pair as a
reusable reservoir financing same-theory moves whose M-side is given
(links are propositions, not resources).  The one combination their
bookkeeping cannot finance is same-theory + K-side-first — exactly
PLL's ◯-case.

Canonical LEGO PROVED and pinned in PLLSemUIHenkin.lean (8 lemmas):
canon_box_dichotomy (validated ◯χ: the world is its own row-witness
by reflexivity of Rₘ, or the witness strictly grows the theory —
[propext, Quot.sound]); trace_box_refuter + promise_blocks_row (a
◯χ-refuting world has a successor promising χ, and promises are
validated by NO canonical Rₘ-successor — the amalgam refutes ◯χ with
no Rₘ-move in M; choice-free); imp_unval_cases + traceT_val_ssubset
(the ⊃-split with guaranteed strictness); traceT_mfal_empty_of_fallible
+ canonTop + rm_canonTop_iff (fallible row-members erase promises;
escapes land on the canonical top).  Library green, 3001 jobs; only
wit_pbisim/wit_force remain sorried.

THE WALL, isolated: the forward ◯-case at a same-val-trace successor
needs an unprimed link at 2d; every spend yields 2d−1.  Candidate
repair (same-trace no-descent: closure-trace-equal i-moves keep the
rank) probed in wip/samval_probe.lean, two passes.  Variable-free:
CLEAN (0 failures; needed cases vanish as the closure grows: 109/5/0).
One-atom (650 hereditarily-decorated models, 2,377,307 agreeing
pairs): REFUTED — 499/44/12 failures over [⊥,q] / [⊥,q,◯q] /
Sub(◯q⊃q)∪{⊥}.  Decoded by hand: the moved world is a rigid dead-end
(q ∧ ¬◯⊥, crank 3); the partner model lacks dead-ends above w′; the
roots agree low because dead-end-absence registers only at ¬¬◯⊥
(crank 4).  The one-level descent of agree_iforth is SHARP under
closure-trace-equality; every decoded failure involves a dead-end
successor (the rigid postponement points of §0(ee)).  Open design
question for next session: the promise-pair invariant with a degraded
link, or a dedicated dead-end clause.  Route doc §0(hh).

## 34. 2026-07-25: the confluent amalgamation CLOSED modulo ONE Prop — the same-theory wall dissolves

`wip/witTripleC.lean` (ui-confluence, b10d274+) is sorry-free with
`#guard_msgs`-pinned audits: `witTriple_iforth`, `witTriple_mforth`,
`wit_pbisimC` (Claim 1), `wit_forceC` (Claim 2 — the full truth
lemma), `amalgamation_assembledC` — all conditional on the single
displayed Prop `MforthResidue`.  The two bare sorries that were "the
open mathematics" of Lemma 5.4 are gone as separate problems.

The two mechanisms: (1) same-trace ◯-moves are matched REFLEXIVELY
(`RmC_refl`) with the base regenerated from the reservoir by
`B.iback` along `Rₘ ⊆ Rᵢ` — §33's wall assumed the ◯-move must be
consumed by `mback`, and it need not be; K-side same-theory ◯-moves
never arise (the witness's trace strictly grows or the world is its
own row-witness).  (2) The truth lemma's ◯-forward direction is
DEFINITIONAL through `RmC`'s anticipation clause (`χ ∈ val Δ₂ →
boxOf χ ∈ val Δ`); ◯-backward is bare possibility in K + `B.mforth`,
strictly financed; ⊃-backward is the K-refuter + `B.iforth`.  No
transfer, no promise component: `mfal` is dead weight in the
confluent route.

Definitions: budgets restored to (2d, 2d+1) — the (d, d+1) `crankC`
recalibration was a MISCALIBRATION (slope 2 refinances two links per
one-level spend; forced, not chosen); `hik` dropped (consumed by
nothing); confluence of M dropped (only K need be confluent); triples
now an inductive with a `top` constructor absorbing every fallible
escape.  Consumption inventory exact: all four E-clauses + atoms +
fall + mono — so pillar 2 still owes the E-form m-clauses.

The residue: an M-side ◯-move at an infallible target where the
reservoir's iback-partner grows the trace (right level 2d, wrong
trace) while the base's mback-partner keeps it (right trace, level
2d−1, one short).  `mforthResidue_of_sameTraceBase` (PROVED) reduces
it to same-trace-partner existence; a structural probe of the exact
configuration is in flight (bii_probe worktree agent), old
samval-failures as negative control.  Route doc §0(ii).  Semantic UI
for PCLL now rests on exactly TWO open obligations, both
m-clause-shaped: pillar 2's agreement-side m-clauses and this
residue.  Cross-route: v2quant re-running with the §33 battery/budget
fixes (second worktree agent); X9 match test pending.

## 35. 2026-07-25 later: probe verdicts land — the residue never arises on the battery; THE X9 CROSS-ROUTE MATCH IS CERTIFIED

**b.ii probe** (wip/bii_probe.lean, exe biiprobe; battery 825 one-atom
models, 531 confluent as K, 438,075 confluent pairs, six ◯-adequate
closures; negative control PASSED — the §33 refuted clause fails ~50k
times per closure in the same approximants): **0 residue
configurations**.  Funnel: 13,204 candidates reach a grown
iback-partner; at every one the mback-partner set is nonempty and
consists ENTIRELY of grown-trace worlds — growth propagates, b.i
always applies.  Counterfactual rescues: R1 (same-trace) 0/13,204, R2
(grown, RmC-financed) 13,204/13,204 — the load-bearing repair is
growth-shaped.  Low-depth impossibility decoded paper-level (d ≤ 2
shut; open region d ≥ 3 with a crank-2d distinguisher, beyond the
battery's stabilisation depth).  Lean: mforthResidue_of_config_absurd
pins the vacuity route; MforthResidue weakened to carry SubClosed cl
(verifier finding).

**v2quant completion** (wip/v2quant_probe.lean + out3; 24-frame sweep
battery incl. the F-free 3-chain + resid-probe gadgets, scan at
findBudget 2000 with skip-counting, match tests at 40000): every
pending row stabilises at r ≤ 4 against budgets 5–11.  **THE X9 MATCH
TEST PASSES, proof-certified in BOTH directions**:
∀p(¬◯⊥⊃◯p) ≡ ◯(¬◯⊥⊃◯¬¬◯⊥) ≡ ¬◯⊥⊃◯⊥ (one RN(◯,{}) class, ¬¬◯⊥) —
the syntactic H2 stabilisation and the semantic rank-descent compute
the same object; per the §33 ledger, one proof now pays three debts.
Also certified: ∀p(gap row) ≡ ◯⊥, ∀p(◯p) ≡ ◯⊥.  ONE undecided cell in
the whole experiment: D₆ = ◯¬◯⊥⊃(◯⊥∨¬◯⊥) vs ◯(◯p⊃p) (the recorded
staller; killed at 2000 and 40000 nodes) — if D₆ ⊢ ◯(◯p⊃p) the
gap-row join would climb at r=6.

**Verification fan-out** (4 adversarial agents): could not refute the
closure claim.  Quote discipline: "the amalgamation THEOREMS are
sorry-free and axiom-clean" (the import chain retains the sorried
general wit_pbisim/wit_force, provably not depended on).  Recorded
gaps: entry budget 2·cl.card+1 coarser than 2·nu+1 (interpolant rank
recalibrates); E-form input not agreement-derivable in general — BUT
the no-go counterexample (forkF) is NOT mutually confluent, so over
confluent models E-form delivery is OPEN, a new pillar-2 opening.

## 36. 2026-07-25 afternoon: growth propagation SPLIT — boundary theorem proved; the configuration is satisfiable (vacuity route dead)

wip/residueGrowth.lean (913b4d3), three theorems, #guard_msgs-pinned
[propext, Classical.choice, Quot.sound]:

* `residue_growth_boundary` PROVED: over a `Ranked` link (level-n
  links transfer p-free formulas of crankC ≤ n — definitional for
  agreement-built links), every p-FREE formula in a residue
  configuration's growth tr(kv)∖val Δ has crankC ≥ 2d.  Sub-boundary
  protected growth crosses to u (level 2d) and back to κ (level
  2d−1), contradicting tr(κ) = val Δ.  So the residue's
  distinguishing formulas are p-laden or boundary-crank — the
  machine-checked location of the S4/K4-style failure mechanism
  (bisimulation rank outrunning interpolant rank), and of the samval
  sharpness decode.

* `residue_config_satisfiable` PROVED: the b.ii configuration IS
  satisfiable — chainP (2-point confluent chain, p at top, no
  fallibles, Rm = Ri) with the FULL link family (a lawful
  LayeredBisimE off p: atoms clause only sees protected atoms) and
  the ◯-adequate closure {⊥,p,◯⊥,◯p}; growth {p,◯p} is PURE-p,
  invisible to the atoms clause.  CORRECTION of §35: the first
  probe's "0 configurations" was an artifact — its closures contained
  no p.  The vacuity route (mforthResidue_of_config_absurd) is dead
  as a general strategy.

* `residue_config_example_resolves` PROVED: in that instance the
  conclusion holds — the growth is ◯-ANTICIPATED (◯p ∈ val Δ), so
  the grown answer works with (kv,u) as its own base and reservoir.
  MforthResidue is therefore CONTENTFUL and OPEN exactly at: growth
  whose ◯-anticipation fails.

Corrected probe IN FLIGHT (bii_p_probe worktree agent): p-containing
closures, p UNPROTECTED in the approximants, two-atom decorations,
full conclusion search at every configuration; failures would be
counterexamples to MforthResidue forcing a triple redesign.  Also
explored and recorded here: the degraded-triple calculus (base 2d−1
after a mismatch) closes the first mismatch but regresses at
b.ii-from-degraded — degradation alone cannot serve the unbounded
bisimulation game; it becomes viable only combined with growth
propagation or an anticipation lemma.

## 37. 2026-07-25 latest: the last v2quant cell decided — D₆ ⊬ ◯(◯q⊃q); the gap row is fully certified at ◯⊥

The §35 undecided cell is REFUTED: `◯¬◯⊥ ⊃ (◯⊥ ∨ ¬◯⊥) ⊢ ◯(◯q⊃q)` is
underivable in plain LaxND, countermodel-certified in the kernel
(wip/d6_gap_cell.lean; all pinned theorems axiom-clean, `[propext,
Quot.sound]`).  The countermodel is `defaultFrames` item 6 decorated
p@{2} — the 3-chain with rigid first Rₘ-step and fallible top — and a
fallible-free twin (chain3F, p@{2}) certifies too, since every
fallible-free model forces D₆ everywhere.  Consequence: the gap-row
∀-join does NOT climb at r=6; all 15 dictionary classes are
certificate-decided on that row's ∀-side, so the rank-bounded
`∀p.◯(◯p⊃p)` = ◯⊥ from r=2 through r=9, matching the §35 match test
(≡ ◯⊥ proved both ways).  No anomaly against the rank-2 stabilisation
pattern remains anywhere in the experiment's ∀-tables.

Post-mortem: the recorded 6-hour/10-minute grinds were the ∃-side call
`◯(◯p⊃p) ⊢ D₆` (no battery frame refutes it), misattributed to the
∀-side, which the battery had refuted all along; the forced skip then
swallowed both sides.  Correction noted at `skipCells` in
wip/v2quant_probe.lean.  Bonus: the gap row's crank≤5 ∃-side skip
`◯(◯p⊃p) ⊢ (◯¬◯⊥) ∨ ¬¬◯⊥` is also REFUTED (4-fork frame, pinned in
the same file); the two D₆-family ∃-cells remain OPEN and touch only
the ∃-meet, whose value ⊤ is unchanged.

## 38. 2026-07-26 night: corrected probe verdict — 0/36.6M failures; the open zone is exactly the strictly-descending regime

Corrected b.ii probe (wip/bii_p_probe.lean, p-containing closures, p
UNPROTECTED, exhaustive conclusion search; 1603 models, 1,739,255
pairs, 56 s): control PASSES (finds the chainP instance; note the
growth there is {p}, not {p,◯p} — ◯p ∈ val Δ already, by pointwise
χ⊃◯χ, which is precisely the anticipation the resolution uses).
**36,588,835 configurations, 0 failures.**  Growth composition: 100%
pure-p-laden, 0 protected members at ANY crank (the boundary theorem
is empirically loose: protected growth never occurs at all in the
fixpoint regime, since a fixpoint E-link over both-confluent models
transfers every protected formula).  Resolution: EVERY config
resolves by a SAME-TRACE answer — the battery's Z-hierarchies
stabilise by level 3, so the level-(2d−1) link at κ already holds at
2d (fixpoint collapse) and κ is its own rescue; grown answers exist
at exactly the ~4% whose growth is ◯-anticipated; grown-ONLY 0.
Also: empirical crankC-rankedness clean on confluent×confluent pairs
only (33k–72k violations with M non-confluent — crankC transfer
needs both models confluent, as force_iff_of_layeredC says).

Lean: `mforthResidue_of_stabilised` PROVED (+audit) — pointwise
level-collapse at the mback-partner's link discharges the residue;
the machine-checked name of the fixpoint-regime rescue.  MforthResidue
remains OPEN, unrefuted, with the danger zone now pinned exactly:
links strictly below the Z-stabilisation level at small canonical
depth = long strictly-descending bisimulation hierarchies = the
◯⊃-alternation towers of the cross-route experiment (X9/D₆
territory).  Small batteries cannot reach it (Z stabilises too fast);
the syntactic route reaches it as the D₆ cell.

## 39. 2026-07-26: THE STABILISATION LEMMA mechanised — the residue is PAID in the one-variable setting

wip/stabilise.lean (68996ab), sorry-free, #guard_msgs-pinned, every
theorem conditional only on `D : RNDict` (the certified variable-free
dictionary interface; instantiation from the v2quant closure tables in
flight as wip/rnDict.lean).  The cross-route plan as a theorem chain:

* `RNDict`: finitely many variable-free reps + crank bound + certified
  connective-closure tables up to `Interd` (PLLSemUIFrag's calculus).
* `dict_collapse` PROVED: structural induction with the Interd
  congruences — EVERY variable-free formula is interderivable with a
  rep.  The finite closure certificate decides the WHOLE fragment;
  this resolves the 2026-07-13 objection ("finitely many probes cannot
  settle the fragment's infinitude"): closure under the generating
  connectives can, and the probe's round-6 fixpoint was exactly that.
* `dict_agree_stab` PROVED — THE STABILISATION LEMMA: variable-free
  agreement at rank crankBound is agreement at every rank.
* `vfB` PROVED (m-clauses as hypotheses VfMforth/VfMback): the
  CONSTANT family Z n := vfAgree is a lawful LayeredBisimE between
  p-pure models; i-clauses = agree_iforth/agree_iback at alphabet ∅,
  the 2α+2 character budget ABSORBED by stabilisation; atoms by
  p-purity; fall at rank 0.
* `vfB_mforthResidue` PROVED: constant family ⇒ level-collapse
  hypothesis is `id` ⇒ MforthResidue holds.  THE RESIDUE IS PAID.
* `restricted_amalgamation_oneVar` PROVED: for p-pure confluent K and
  p-pure M, root agreement at rank crankBound (fixed, closure-
  independent!) yields the full p-variant conclusion — no residue
  hypothesis, entry budget crankBound instead of 2·cl.card+1.

Status of one-variable PCLL semantic UI after this: pillar 3 fully
paid; the ONLY remaining obligation is VfMforth/VfMback — the two
m-clauses of pillar 2 for the constant variable-free-agreement link —
plus the Thm 5.1 wrapper.  Note the contrast with IPC: the one-variable
p-free fragment there is the (infinite) Rieger–Nishimura lattice, so
no constant-link shortcut exists; PLL's variable-free fragment is
FINITE (the ◯⊥-ladder stabilises) — the modality is what makes the
restricted case easier, not harder.

## 40. 2026-07-26: the 15-class closure is REFUTED — the dictionary premise falls, the stabilisation chain stands

The rnDict instantiation agent's verdict, consolidated (d37f9c0):
**the RN(◯,{}) dictionary is NOT connective-closed at 15 classes.**
wip/rnDictRefute.lean proves, axiom-clean [propext, Quot.sound] and
#guard_msgs-pinned:

  refute_cAnd_8_10  : ∀ k : Fin 15, ¬ Interd (q8.and q10)     (rep15 k)
  refute_cImp_9_4   : ∀ k : Fin 15, ¬ Interd (q9.ifThen q4)   (rep15 k)
  refute_cImp_12_4  : ∀ k : Fin 15, ¬ Interd (q12.ifThen q4)  (rep15 k)
  refute_cImp_14_4  : ∀ k : Fin 15, ¬ Interd (q14.ifThen q4)  (rep15 k)

each candidate eliminated by a checkB-certified countermodel (the
refuting battery COMPLETE for variable-free refutation at ≤ 4 worlds).
All four witnesses are X9-tower combinations of size 20–23 — beyond
v2quant's SZMAX = 16 candidate cap.  "Closure at round 6" was closure
of the size-≤16 QUOTIENT.  Kernel-checked consequence: RN(◯,{}) has
**≥ 16 classes** (≥ 19 if the four witnesses are pairwise distinct —
not yet pinned).  rnDict15 is UNCOMPLETABLE as an instantiation; its
603/690 certified cells (236 emitted G4cTm terms via rnDictGen, 367
generic Interd laws, rnDictBase) are kept as raw material for the
enlarged dictionary.  83 further cells OPEN (unprovable by both
searchers, unrefuted at ≤ 4 worlds; per-cell candidate shortlists
recorded — ⊤-vs-tower ambiguities needing ≥ 5-world countermodels or
deeper proofs).

CONSEQUENCES.  (1) The variable-free fragment-finiteness question is
REOPENED, now leaning infinite (the tower splits past every cap so
far) — supporting the Curry-problem thread's RN(◯,{})-infinite
direction, and giving the nucleus/assembly thread its first
kernel-checked lower bound on the RN(◯,{}) size.  (2) The
stabilisation chain (wip/stabilise.lean) is UNTOUCHED and now carries
the question precisely: by dict_collapse, an RNDict exists iff the
fragment is finite; restricted_amalgamation_oneVar is blocked pending
that.  (3) The v2quant r-tables were computed over the truncated
quotient: every certified derivability (incl. the X9 match and
D₆ ⊬ gap row) STANDS, but the "join" columns are joins over the
15-class scan — computed join ⊢ true join; per-row values could rise
if a new class derives a row.  Re-audit needed over the enlarged
dictionary.  (4) The correct fallback for one-variable UI is the
rank-relative form (per-rank finiteness = frag_reps_exist', PROVED):
IPC's precedent says UI can hold over an infinite one-variable
fragment (Pitts over the Rieger–Nishimura lattice) — global collapse
was a shortcut, not a necessity.

## 41. 2026-07-26: the RANK-RELATIVE stabilisation lemma — band collapse; the open core is a plateau

wip/bandStabilise.lean (9dcda2c), sorry-free, pinned.  The finite
dictionary was certification apparatus only; the chain needs one Prop:
`BandCollapse R E` (every variable-free formula of crank ≤ E
interderivable with one of crank ≤ R), with E = 2R+2 dictated by the
character budget.  PROVED: band_agree_stab (CHOICE-FREE
[propext, Quot.sound]); bandB (constant family Z n := bandAgree R, a
lawful LayeredBisimE between p-pure models — i-clauses upgrade across
the band then spend agree_iforth/iback); bandB_mforthResidue (residue
paid); restricted_amalgamation_oneVar_band (one-variable amalgamation
at entry rank R from BandCollapse R (2R+2) + BandMforth/BandMback);
bandCollapse_of_dict (the global constant-link theorem is the E-free
special case — "reinstated-if-closed" made precise).  OPEN CORE now:
exhibit ONE R with BandCollapse R (2R+2) — a PLATEAU of the
variable-free class-count function n(r) on [R, 2R+2].  Strictly weaker
than fragment finiteness: n may resume growing above the band; failure
for ALL R requires new classes at doubling density FOREVER (every
window [R, 2R+2] hits a new class) — the S4 signature.  Observed so
far: new classes at essentially every crank ≤ 7-8 (incl. the §40
witnesses at 6-7); the dictionary-mapping session's class-count curve
is exactly the data that locates or excludes a plateau.  Terminology
correction for §40's prose: the lattice whose size the literature
leaves open is RN(◯,{}) (variable-free PLL; ◯⊥ is not a free
generator); RN({p}) — Rieger–Nishimura proper — is classically
infinite (Rieger 1949, Nishimura 1960), and with ◯-free conservativity
the one-VARIABLE PLL fragment is infinite too; neither settles
RN(◯,{}).  Note the compatibility: the Curry-problem thread wants
RN(◯,{}) infinite, UI wants a plateau — both can hold.

## 42. 2026-07-26: the infallible collapse formalised; the m-clause positive half proved

wip/bandM.lean (sorry-free, pinned).  Matthew's observation — PLL+¬◯⊥
is complete for infallible constraint models, where ◯⊥ ≡ ⊥ and
RN(◯,{}) collapses to {⊥,⊤} — is now a theorem pair:
`infallible_amalgamation` (between p-pure INFALLIBLE models, K
confluent, the total link is a lawful LayeredBisimE — all eight
clauses trivial, m-clauses included — and the one-variable
amalgamation holds with NO agreement hypothesis; the first
UNCONDITIONAL instance of the whole amalgamation tower and a
constructive non-vacuity certificate), and `band_mforth_positive`
(general fallible case: the POSITIVE half of the banded m-forth
clause via charPos + bare possibility on both sides + band transfer
at α+3 ≤ R; the NEGATIVE half — no overshoot — is the isolated
remainder).  Reading: the m-clause difficulty, like the tower itself,
is EXACTLY fallibility-grading; over ¬◯⊥ everything trivialises, so
any PLL-UI proof factors its hard content through the fallibility
dimension.  PRECISION note on §40: "≥ 16 classes kernel-checked"
overstated — the four ∀k-refutations are fully pinned, but pairwise
distinctness of the 15 representatives (and of the 4 witnesses) is
probe-certified only, not yet Lean-pinned; the mapping session should
pin the separations.

## 43. 2026-07-26 evening: the two quotients computed — RN ≥ 16 PINNED, RNC first map; no plateau in sight; the gap row survives everything

Two independent certification streams landed and consolidate here.

**PLL (the dictionary-mapping session; wip/rnDict2Report.md, artifacts
rnSep/rnSepColl/rnDict2Hand/rnDict2/rnDictRefute2):** the four §40
witnesses are ONE class, q15 := q9⊃q4, kernel-pinned (two of the three
fusions AXIOM-FREE; the searcher could not find them — hand Deriv
terms; gap patterns catalogued).  The 15 base classes are NOW pairwise
distinct CERTIFIED (165 pinned countermodels; {q1,q11,q13} and
{q9,q12,q14} need 5 worlds — the ≤4-world battery cannot see them;
exhaustive ROOTED 5-world completeness by generated-submodel
reduction).  Aggregate `rep16_pairwise_distinct` [propext, Quot.sound]:
**RN(◯,{}) ≥ 16, fully pinned** (the §42 precision debt is paid).
The 16-class closure round FAILS massively: ~40 cells match no class
(⊃-block dominates; three pinned 6-WORLD models were needed — some
refutations invisible at ≤5 worlds); ∧-family spawns all-distinct.
Class count rises through every observed crank window: **no plateau
visible; BandCollapse unsupported below crank ~8.**
**THE GAP ROW SURVIVES THE FULL ENLARGEMENT**: among all 16 reps and
all 41 spawned-class witnesses, only ⊥ and ◯⊥ derive ◯(◯p⊃p) (pinned
countermodels for every other candidate) ⇒ ∀p.◯(◯p⊃p) = ◯⊥ stands
over everything now known.

**PCLL (the RNC probe, §consolidated 4f0cb6d):** distribution merges
q9 ≡ q12 and fuses the witness class (distF q3 q6 exactly), 19 → 15;
new reusable certificate theorem not_derivU_of_checkConf (confluent
countermodel ⇒ PCLL-underivability); but the RNC closure sweep spawns
26 new-class cells — **the tower continues past distribution**.  Sole
open matrix cell [q14] ⊢ q13 in both logics.

**Synthesis:** fragment-infinitude now the working picture for BOTH
quotients; the plateau (constant/band link) route is empirically dead
at accessible ranks; the PER-INSTANCE route is simultaneously
STRENGTHENED (the gap-row value certified against the entire
enlargement — B1 + per-instance-B2 evidence at its strongest).  Route
forward: the mforth choice-freedom refactor + the per-instance residue
treatment, over whichever of PLL/PCLL the Thm 5.1 assembly targets.

## 44. 2026-07-26 night: the 16-round is FULLY DECIDED — 58 spawned witnesses, exact families, RN(◯,{}) ≥ 25

Completion of the dictionary-mapping session (§43 reported it in
flight).  Every one of the 140 searched cells of the 16-class closure
round is now DECIDED — zero open cells:

  82 LANDED (19 searcher + 63 hand certificates — wip/rnDict2Hand.lean,
     the searcher-gap catalogue: ofImpTop order facts, ex falso inside
     ◯, ◯-intro under orElim, collapse-lemma cuts);
  58 NEW-CLASS witnesses (6 ∧, 15 ∨, 35 ⊃, 2 ◯), each with every
     candidate countermodel-eliminated; witness theorems over Fin 16
     in wip/rnDictRefute2.lean; wip/rnDict2.lean emits the partial
     rnDict16 : RNDict with exactly these 58 sorried cells.

FIVE pinned 6-world countermodels (extraCMs) decide candidates
invisible at ≤5 worlds — among them [q14] ⊬ q13 (§43's "sole open
matrix cell", now closed), ⊬ q8∨q10, [q13] ⊬ q5∨q8, [q13] ⊬ q8∨q12.

The spawned classes classify EXACTLY within the scanned families
(wip/xsep_*.txt + the 8 hand collapse certificates of
wip/rnSpawnColl.lean — ALL eight previously-open spawned pairs are
COLLAPSES, e.g. q8∨q10 ≡ q8∨q11 and the cross-shape q10⊃q4 ≡ q11⊃q7,
two pinned AXIOM-FREE):

  ∧-family: exactly 6 classes;  ∨-family: exactly 9;
  ⊃-family (scanned subset of 12): exactly 8;  ◯-column: 2;
  25 further ⊃-witnesses and all cross-family pairs unscanned.

CLASS-COUNT: rep16_pairwise_distinct pins ≥ 16 in the kernel; the
∨-family clique (9 spawned classes pairwise distinct and distinct
from all 16) lifts the certified count to **RN(◯,{}) ≥ 25**
(checkB-gated run-log countermodels, kernel-pinnable on demand); with
58 witnesses outstanding the true count is plausibly 40+.  The
class-count curve rises through every crank window observed (spawned
reps at crank 6–9) — the §41 plateau remains without support, and the
Curry-problem thread's RN(◯,{})-infinite direction strengthens again.

The gap-row audit of §43 stands unchanged over the completed round:
only ⊥ and ◯⊥ derive ◯(◯p⊃p); ∀p.◯(◯p⊃p) = ◯⊥.

Deliverables: wip/rnSep.lean (165 sep certificates), wip/rnSepColl.lean
(witness collapse + rep16 aggregate), wip/rnDict2Hand.lean (63 hand
cells), wip/rnDict2.lean (726/784 cells certified), 
wip/rnDictRefute2.lean (58 witness theorems), wip/rnSpawnColl.lean
(8 spawned collapses), wip/rnDict2Report.md (the class map), run
outputs wip/gen2logs/ + wip/xsep_*.txt + wip/gaprow_*.txt.

## 44. 2026-07-26 night: the mforth choice-freedom refactor — the input link is LayeredBisimWit

fc9ab18, whole chain green, audits unchanged.  The consumption audit
(§34's inventory) showed the E-form's mforth spent at ONE site — the
truth lemma's ◯-backward — where the K-side witness is chosen, not
given.  The input format is now `LayeredBisimWit`: mforth replaced by
the witness clause

  mwit : Z (n+1) k m → (∃ κ, Rm k κ ∧ force κ ψ) →
    ∃ κ u', Rm k κ ∧ force κ ψ ∧ Rm m u' ∧ (Z n κ u' ∨ pair-fallible)

(the ◯-obligation for SOME row-witness of the formula in play; the
prover picks).  `LayeredBisimE.toWit` embeds the old format — strictly
one-way, so pillar 2's debt is strictly weakened; the weakened Props
are `VfMwit`/`BandMwit` with `…_of_…forth` bridges.  Adversarial
clauses (iback, mback) unchanged; wit_pbisimC's OUTPUT is still a full
unbounded PBisim.  What this buys the negative half: the maximal-type
ascent arguments now have their proper home (the samval-decoded
unmatchable row-members — the dead-end partners no formula can force a
match for — no longer refute the obligation, since the prover may
choose a matchable witness).  What it does not buy: the crank
treadmill (matching at rank R needs characters boxed at R+3) stands;
the remaining depth is per-instance stabilisation, as §43 concluded.
Concurrent: the mapping session continues landing separation-scan
artifacts on this branch (be0ca34).

## 45. 2026-07-27: THE MAXIMAL-TYPE ASCENT — the witness-form m-clause PROVED under the band

wip/bandM.lean (d164be5), sorry-free, pinned:

  bandMwit_of_collapse : 1 ≤ R → BandCollapse R (2R+2) →
    MutuallyConfluent K → MutuallyConfluent M → BandMwit R K M

No fallible escape is consumed.  Engine (the ascent): a ψ-witness κ in
k's row boxes its rank-R positive character across the link — the band
collapse pulls ◯charPos (crank R+3) back under rank R, defeating the
crank treadmill — and bare possibility in M realises it at u′.  Exact
type match ⇒ rank-R agreement, done.  Overshoot at a representative D₀
⇒ the backward transfer returns κ′ ∈ row(k) covering u′'s type, and
the confluence square over (Rₘ k κ, Rᵢ k κ′) yields y ∈ row(k) that
keeps ψ (persistence along Rᵢ κ y) and swallows κ′'s type (persistence
along Rₘ κ′ y) — a ψ-witness with strictly larger type.  Finitely many
representatives ⇒ termination.  Supporting lemmas:
band_row_char_partner/_rev, private countP arithmetic.

New capstone `restricted_amalgamation_oneVar_band'`: the banded
one-variable amalgamation from BandCollapse R (2R+2) + BandMback ONLY.
LEDGER after tonight: the forth-side m-obligation is PAID (under the
band); remaining = the plateau itself (empirically unsupported at
accessible ranks, §43) and BandMback (adversarial; dead-end gap).
Matthew's observation recorded: mwit + ascent is a reducibility-
candidates-style move (System F SN) — quantify over observations
rather than raw moves, then saturate witnesses; kinship with the
repo's own ⊤⊤-lifting SN proof (biorthogonal closure) noted in the
session log.

## 46. 2026-07-27: Matthew's BandCollapse objection — correction of record; RN(PCLL,◯,{}) presented

**The correction.**  Matthew challenged `BandCollapse R (2R+2)`
("iterate it and everything collapses to crank 0 — absurd").  The
specific reductio fails — the band is anchored at R and gives no
descent below R — but the substance of the objection is RIGHT and the
§41/§45 record was WRONG on the key point: one band bootstraps
UPWARD.  By exactly the dict_collapse rebuild induction (collapse the
subformulas to rank ≤ R, reassemble with one connective: crank ≤ R+2
≤ 2R+2, collapse again), `BandCollapse R (2R+2)` implies collapse of
the WHOLE variable-free fragment to rank ≤ R.  So the band hypothesis
is EQUIVALENT to fragment finiteness (with a rank-R representative
bound) — NOT "strictly weaker: growth may resume above the band", and
the "failure needs doubling-density growth forever" characterisation
is retracted.  Consequences: (a) the ascent theorem
bandMwit_of_collapse and the banded amalgamation are conditional on
fragment finiteness, no less; (b) the plateau question and the
fragment-finiteness question are ONE question; (c) the injectivity
delegation (agent in flight: h : RN({p}) → RN(L,◯,{}) under p ↦ ◯⊥,
faithfulness for L ∈ {PLL, PCLL} via the fallible-top U-transfer
construction) would settle it NEGATIVELY for both logics, killing the
band route and crowning the per-instance ascent (the ascent proof
only uses finiteness + transferability of the TEST LIST, so it
relativises to finite test sets — the per-instance form is the
surviving shape).

**Class-count confirmations** (Matthew's notation RN(L,◯,{}) with the
logic as argument, ADOPTED): RN(PLL,◯,{}) ≥ 16, fully kernel-pinned
(rep16_pairwise_distinct).  RN(PCLL,◯,{}): the 19 candidates fall
into 15 classes — the 15 PLL base reps collapse to 14 (sole merge
q9 ≡ q12, via the single instance distF q3 q6), plus the fused
witness class w = q8∧q10 ≡ q9⊃q4 ≡ q12⊃q4 ≡ q14⊃q4 distinct from all
14.  Certification status: all separations pinned per-pair
(wip/rncCert.lean, confluent countermodels, [propext, Quot.sound]);
merges pinned (rncCertPos/rnSepColl — the witness fusions are
PLL-level, two of three axiom-free, hence PCLL); an AGGREGATE
pairwise-distinctness theorem for the 15 (analogue of
rep16_pairwise_distinct) is one decide-glue file away and not yet
written.  The raw probe matrix's "18 classes" line predates the
hand-certificate fusion layer.  Sole unknown cell of the 15×15
PCLL matrix: q14 ⊢ q13.  Hasse structure extracted and drawn
(session diagram): heights 0..6, q9* the only distribution-merge,
w incomparable to ◯¬◯⊥, covers as certified.

## §47 (2026-07-27) — The witness-form OUTPUT: force_iff_of_witOut, the re-typed projection, BandMback leaves the ledger

The candidates-lens conclusion of §46's session made Lean.  The
specification consumes exactly one property of the output p-variant
link — preservation of p-free formulas — and that property survives
weakening BOTH ◯-directions of the output to witness form, over a
confluent base.

**New structures** (wip/witTripleC.lean refactor + wip/witOut.lean,
all sorry-free, [propext, Classical.choice, Quot.sound] throughout):

* The input `LayeredBisimWit` loses its adversarial `mback` FIELD —
  demoted to the optional side condition `MBack`, consumed at exactly
  one site (`witTriple_mforth`); the refactor compiling IS the
  consumption audit.  New M-side WITNESS clause `MWitM` (the adversary
  picks the formula, not the world), strictly weaker (`mwitM_of_mback`).
* `ABisimWit`/`PBisimWit`: the unbounded witness-form output link.
  `force_iff_of_witOut` — THE LINCHPIN: a witness-form link between a
  MUTUALLY CONFLUENT base and an ARBITRARY variant transfers every
  protected formula at every rank.  ◯-forward extracts the base-row
  witness from the ∀∃ clause directly and pushes it through `mwit`;
  ◯-backward pulls the reflexive-successor witness through `mback` and
  rebuilds ∀∃ by bare possibility — the single use of confluence.
* `MwitResidue`: the witness-form residue, strictly weaker than
  `MforthResidue` on both sides (extra hypotheses: the partners come
  from the witness clause with a forcing fact riding along; weaker
  conclusion: ANY row-witness may answer).  Bridges:
  `mwitResidue_of_mforthResidue`, `mwitResidue_of_stabilised`.
* `witTriple_mwit` / `wit_pbisimW` / `amalgamation_assembledW`: the
  ◯-maintenance, projection, and assembly in witness form — no
  adversarial clause consumed anywhere; the assembly delivers closure
  agreement AND (over a confluent base) full p-free transfer at the
  root.

**The banded cascade** (wip/bandW.lean): `BandMwitM` discharged by the
MIRRORED maximal-type ascent (bandAgree is symmetric), so
`restricted_amalgamation_oneVar_wit` needs the band collapse and
NOTHING else — `BandMback`, the last unproved m-obligation of the §45
route, left the ledger.

## §48 (2026-07-27) — THE RANKED ASCENT: pillar 2 closes with no band and no finiteness

The decisive observation, minutes after §47: the ascent's finiteness
input is `frag_reps_exist'` — PER-RANK finiteness (pillar 1) — not
fragment finiteness.  The band entered §45's proof at exactly one
point: lifting link agreement to the boxed-character rank.  Supplying
that rank directly (wip/rankedM.lean, all sorry-free):

* `rankedMwit`: over mutually confluent models, variable-free
  agreement at rank α+3 answers every K-row ψ-witness by one whose
  M-partner agrees at rank α — NO escape, rank spend +3 (cheaper than
  the i-clauses' 2α+2 halving).  `rankedMwitM` by symmetry;
  `bandMwit_of_collapse'` refactors §45's ascent as stabilisation
  feeding the ranked clause.
* `rankedB`: Z n := agreement at rank `rslope n`
  (rslope(n+1) = 2·rslope n + 3) is a lawful `LayeredBisimWit` off p
  between one-variable mutually confluent models, plus `MWitM` —
  EVERY input clause of the witness pipeline from pure rank-bounded
  agreement.  **PILLAR 2 IS CLOSED in the ranked setting.**
* `restricted_amalgamation_oneVar_ranked`: the one-variable
  amalgamation from root agreement at the FIXED rank
  rslope(2·|cl|+1) (tower-exponential in the closure, but determined
  by it), modulo the ONE open Prop `MwitResidue` of the ranked link.
  The residue — whose geography §§40-42 already mapped
  (`residue_growth_boundary`: genuine configurations are p-laden or
  boundary-crank; the S4/K4 UI-killer mechanism) — is now the ENTIRE
  unproved content of the route.

## §49 (2026-07-27) — Fragment infinitude LANDS: the band is REFUTED, the dictionary impossible, the purity corrected

The injectivity delegation returned stronger than commissioned
(wip/rnEmbed.lean, cherry-picked; 1069 lines, 15 pinned audits): the
full Rieger–Nishimura ladder embeds under p ↦ ◯⊥ into BOTH quotients,
pairwise distinct at EVERY index — over the single infinite RN frame
on ℕ with closed-form rung truth sets, no decide budget.  Kernel-checked:
`varfree_no_finite_cover_pll/_pcll` (**both variable-free fragments
are INFINITE** — §46's "likely" upgraded to theorem, Nishimura not
consumed), `rank_escape_pll/_pcll` (every rank is escaped),
`rnSub_derivU_iff_deriv` (PCLL conservative over PLL on the embedded
ladder; image order = truth-set containment in both logics),
`crank_rnP_emb` (two fresh rungs per crank forever).

Consequences, mechanised the same night (wip/bandRefute.lean):

* `global_collapse_of_band` — §46's rebuild induction in Lean: one
  band `BandCollapse R E`, `E ≥ R+2`, bootstraps to global collapse
  at rank R.
* `bandCollapse_refuted` — **BandCollapse R E is FALSE for every R
  and every E ≥ R+2** (in particular the character width 2R+2).  The
  band route of §§43-45 and §47 is closed NEGATIVELY: those theorems
  keep their (true) conditional content with antecedents now known
  unsatisfiable.  The ranked route (§48), which never used the band,
  is the survivor — built hours before its rival died.
* `rnDict_false` — the `RNDict` interface is UNINSTANTIABLE; the
  dictionary-closure certification program (603/690 cells) cannot
  complete.  No further effort there.
* `ppure_ffree` (axiom-free) + `ppure_oneVar_trivial` — formulation
  audit: `full_F` forces `PPure` models infallible, so the p-pure
  one-variable amalgamation was UNCONDITIONALLY true
  (`infallible_amalgamation`), i.e. the p-pure hypotheses trivialised
  those statements.  Corrected purity `POnly` (V a ⊆ F off p) adopted
  by the ranked chain — fallible one-variable models genuinely in
  scope.

**The route, after tonight**: everything unconditional except ONE
displayed Prop — `MwitResidue` for the ranked link at slope
2s+3 — consumed at one site, bridged from stabilisation and from the
old residue, boundary-mapped, probe-populated.  Next: (i) decide
MwitResidue for ranked links (the boundary theorem constrains genuine
configurations to p-laden/boundary-crank growth whose ◯-anticipation
fails; the §42 probe battery re-aimed at the witness form); (ii) the
spec layer over PBisimWit (IsSemExW) and the PCLL UI statement it
feeds.

## §50 (2026-07-27) — The residue probe re-aimed at MwitResidue: clean at ~330M instances, and the open zone pinned to large models

wip/mwit_probe.lean (exe mwitprobe; output wip/mwit_out.txt; control =
the hand instance of residue_config_satisfiable, PASS).  The certified
b.ii funnel enriched by a ψ-loop and the witness-freedom verdict
(GIVEN / OTHER / FAIL per (configuration, ψ)), answer search extended
by the canonical-top answer, run over TWO link families:

* **mode R** — the RANKED family Z n := variable-free agreement at
  rank rslope n over a ◯⊥-alternation pool, POnly-corrected
  decorations, both models confluent — the exact link of the open
  Prop MwitResidue cl (rankedB …): 131,044 pairs, 4,314,267
  configurations per closure, 30–39M instances per closure —
  **GIVEN = 100%, OTHER = 0, FAIL = 0**; every pair's chain stabilises
  by level 2, live window EMPTY.
* **mode G** — the largest lawful layered family (hard mode,
  p unprotected), reproducing the §38 scan scale: 1,739,255 pairs,
  ~12.2M configurations per closure (×3 ≈ the old 36.5M), 85–109M
  instances per closure — **GIVEN = 100%, OTHER = 0, FAIL = 0**;
  stabilisation by level ≤ 3, live window EMPTY, 0 monotonicity
  violations.

READING (three facts, kept distinct): (1) MwitResidue is UNREFUTED at
~330M instances across both families — no counterexample candidate
exists at ≤7 worlds.  (2) The witness freedom was NEVER exercised
(OTHER = 0): at battery scale every configuration already resolves at
the given witness, so the probe shows the re-typing SAFE but not yet
NECESSARY — its value remains the strictly weaker Prop and the
BandMback elimination, plus whatever the large-model regime holds.
(3) The live window is empty in both modes: every reachable
configuration sits at stabilised link levels, where
mwitResidue_of_stabilised is a THEOREM — so the entire open content
of MwitResidue is confined to the strictly-descending regime, which
(by the ladder-needs-depth fact of wip/rnEmbed.lean: rung k needs
~k/2 worlds) requires models beyond any small battery.  The open Prop
stays OPEN with its geography sharpened: genuinely dangerous
configurations need LARGE confluent models whose variable-free
agreement chain still descends at the financed levels — the infinite
alternation-tower territory, exactly where a UI counterexample would
have to live.

Also this session: the parallel track's searcher optimisations merged
(cherry-picks 294251b/5413696 = order-canonical ckey + global failure
memo for the plain searcher, authorship preserved) and COMPOSED into
the bounded searcher (budget × memo × key; failures cached only with
budget remaining — sound because exhaustion is sticky); findBounded's
public signature unchanged; verified by the in-tree #guard gates plus
a 1100-sequent cross-check (0 mismatches).  Merge guidance recorded:
belief branch → main first, then ui-confluence, resolving
PLLG4Term.lean to the combined version; never rebase ui-confluence.

## §51 (2026-07-27) — The deep probe REACHES the descending regime: RankGap verified at 1.17M live instances

wip/mwit_deep.lean (exe mwitdeep; output wip/mwit_deep_out.txt).  On
the lifted ladder truncations (8/10/12 base worlds + fallible top) the
ranked chain is STILL DESCENDING at level 5 on every one of 17,424
confluent pairs (stab histogram: 5×17,424 — the rung-pool ceiling,
genuine descent through rslope 4 = 45).  For the first time the LIVE
window is occupied: 140,616 configurations with 2d−1 < stab (cl1;
first dump: d=2, stab=5 on the 8-world lifted ladder), carrying
1,174,068 (config,ψ) instances — GIVEN = 100%, OTHER = 0, FAIL = 0.
Total across modes: ~51M further instances, all clean.  (Gdeep: gfp
chains now stabilise as late as level 11 on the deep frames; its
configurations still all sit at stabilised levels.)

READING: RankGap now has direct evidence INSIDE the descending regime
— the previously untouched zone.  The live configurations resolve at
the given witness, meaning full-rank same-trace partners exist
pointwise even while the global agreement chain descends.  Open
remainder, sharpened once more: deeper d (live configs so far have
d=2), heterogeneous pairs, and the true infinite-model limit.  The
balance of evidence has shifted from "confined to stabilisation" to
"RankGap plausibly TRUE in general" — the proof attempt should target
a pointwise full-rank partner construction at residue configurations
(the ladder models suggest the same-trace κ-partner itself carries
full-rank agreement there), with the §50 boundary machinery
(pOnly_V_eq_F + residue_growth_boundary) as the tool.

## §52 (2026-07-27) — The pointwise attack: the ∀∃-descent, the row-rigid theorem, and the open Prop shrinks to RankGapGrow

wip/rankGapPoint.lean, all sorry-free, guards pinned:

* **The ∀∃-descent** (reservoir_row_cover / _witness) — a genuinely
  new transfer move: a positive character boxed at the reservoir's
  K-side world (bare possibility, K confluent) crosses the reservoir
  at its FULL rank rslope(2d+1) = 2·rslope(2d)+3, and the ∀∃ clause
  of ◯ at m' EVALUATES DOWNWARD at the i-successor m — realising
  every row(k')-type inside row(m), at ranks far ABOVE the missing
  window; the confluence square in M merges the cover with the
  ψ-witness.  First transfer in the whole development that lands
  inside m's row.
* **rankGap_of_rowRigid + mwitResidue_ranked_of_rowRigid**: over
  row-rigid bases (every infallible ◯-move reflexive — all lifted
  ladders of §51's battery), RankGap and hence the ranked MwitResidue
  are PROVED outright (the witness is m itself; kb := k closes by the
  base link).  The entire §51 live-window evidence class is now
  theorem.
* **rankGap_of_grow**: the case split — if SOME ψ-witness adds
  nothing to m's vf-theory at rank rslope(2d), kb := k closes by
  transitivity (bandAgree_trans_mid).  THE OPEN PROP SHRINKS TO
  RankGapGrow: configurations where EVERY ψ-witness strictly grows
  m's rank-rslope(2d) vf-theory.  Its geography: each witness's
  growth rep D₀ gives m ⊨ ◯D₀ at crank ≤ rslope(2d)+2 — one to two
  connectives above the base link, ranked-invisible (the M-row mirror
  of residue_growth_boundary).
* Designed next step recorded: reinstate the dropped K-side edge
  k' Rᵢ k in WitTripleC (maintainable through every constructor in
  use) — then boxes at k' also evaluate downward into row(k), giving
  the two-sided saturation the maximal-type ascent needs to terminate
  at an exact match in the grow case.

## §53 (2026-07-27) — hik REINSTATED; the square descent made confluence-native; the two-sided saturation packaged

Register point first (Matthew's design constraint): the §52 "∀∃-descent"
as first proved consumed the raw ∀-half of ◯'s ∀∃ clause — the exact
adversarial quantifier the PCLL/confluent programme exists to avoid
(the S4/iK4 UI-killing mechanism), and a proof consuming it
irreducibly would hold over the WRONG model class.  Matthew right in
principle; the move itself innocent: over the confluent class the same
conclusion follows from bare possibility + one confluence square +
persistence.  reservoir_row_cover REPROVED in that register (hM added;
register note in the docstring); "descent" now means precisely:
push-down of a row-witness along Rᵢ through a confluence square.

The classical K-side edge hik : k' Rᵢ k is REINSTATED in WitTripleC —
threaded through the constructor, every construction site
(witTriple_iforth/mforth/mwit, wit_forceC, both assemblies), both
residue Props (MforthResidue, MwitResidue), all bridges
(sameTraceBase's sufficient condition now supplies K.Ri k' kb;
stabilised bridges derive the edge by trans_i hik ∘ sub_mi), the
config-satisfiability witness, RankGap/RankGapGrow (hypothesis + the
K.Ri k' kb conjunct in the conclusion) and their proofs.  Whole tree
green, every #guard_msgs audit passing.  Probe note: the §50/§51
funnels do not test k' Rᵢ k, so their clean verdicts cover a SUPERSET
of the reinstated configurations a fortiori.

NEW: row_push_down (K-side square: row(k') pushes into row(k), no
link crossing, all ranks) and config_two_sided_saturation — in a
residue configuration, every world of row(k') is simultaneously
pushed into row(k) AND covered inside row(m) by a ψ-carrying witness,
at every rank α ≤ rslope(2d+1) − 3.  Both rows saturate over
row(k')'s types.  The single missing ingredient for an exact-type
match — now the entire distance between RankGapGrow and closure — is
the BACKWARD leg: reflecting row(m)-types into row(k').

## §54 (2026-07-27) — The backward leg: all routes converge on ONE window; residue_window PROVED; the grow case exposed as empirically untested

The backward-leg attempt (reflect row(m)-types into row(k')) reduces,
on every route tried, to the SAME obstruction — the rank window
(rslope(2d−1), rslope(2d)]:

* the (k,m)-link reflection is capped at rslope(2d)−3 (◯ξ costs +3);
* the reservoir reflection needs a box at m', i.e. a row(m')-witness
  the configuration lacks (and k' ⊨ ◯ξ ⟺ m' ⊨ ◯ξ across the link, so
  producing one is circular);
* CLOSURE ENLARGEMENT (add low-rank vf representatives to cl so that
  vf-growth becomes trace-visible and the grown case fires) fails
  twice: the bootstrap diverges (the needed rank rslope(2·|cl|) grows
  faster in |cl| than any finite representative stock, fragment
  infinite), AND residue_window (NEW, PROVED, wip/rankGapPoint.lean)
  shows the witness's cl-visible vf-growth at window-floor rank is
  EMPTY in every residue configuration — the κ-partner forces it and
  its trace keeps Δ;
* re-sloping the triple cannot help: any base-spend answer needs
  b − 1 ≥ b.

So RankGapGrow either has a countermodel or needs machinery not in
the toolbox; scale-invariance of the window across all routes is
itself evidence the question is sharp.  A countermodel must have
NON-ROW-RIGID M-rows (else rankGap_of_rowRigid applies) — and the §51
deep battery was entirely row-rigid, so THE GROW CASE HAS NEVER BEEN
EXERCISED empirically.  wip/mwit_deep.lean extended: non-row-rigid
lifted ladders (dense base Rₘ-chains), dense random frames, and a
u' ≠ m split in every verdict column — the first probe aimed at
RankGapGrow itself.

## §55 (2026-07-27) — The grow-case hunt: 4.2M non-rigid configurations, 1.8M in the descending window — all clean

wip/mwit_grow_out.txt (the §54-extended battery: 294 models, 174
confluent; non-row-rigid lifted ladders with dense base Rₘ-chains +
dense random frames).  Mode Rdeep (the exact ranked link): 6.9M/7.2M
configurations per closure with the LIVE window now MASSIVELY
occupied (5.33M live configs, cl1); the NON-RIGID class (u' ≠ m — the
only class where a RankGapGrow countermodel can live) holds 1,961,316
configurations per closure, 1,833,552 of them LIVE (cl1), carrying
16.0M/18.6M instances — GIVEN = 100%, OTHER = 0, FAIL = 0.  Gdeep
adds 2.24M non-rigid configurations per closure, likewise clean.
Every pair's ranked chain still descending at level 5 (pool ceiling).

READING: the first probe evidence in RankGapGrow's own territory —
non-reflexive witnesses, genuinely descending chains — and pointwise
promotion KEEPS HOLDING there (every given witness had a same-trace
full-rank partner).  Caveat kept distinct: u' ≠ m does not yet verify
RankGapGrow's FULL hypothesis (that every ψ-witness vf-grows m's
rank-rslope(2d) theory); a refinement flagging exactly the all-grow
configurations (computable against the rung pool) is the designed
next probe.  Balance of evidence: RankGap plausibly true outright;
the window (§54) remains the sole theoretical obstruction, now with
~230M clean instances around it.

## §56 (2026-07-27 night) — The all-grow flag NEVER FIRES: RankGapGrow's hypothesis empirically unsatisfiable; the open Prop becomes StableWitness

wip/mwit_ag_out.txt: across 31M configurations / 258M (config,ψ)
instances (both modes, both closures, including 4.2M non-rigid
configurations and 5.3M live ones), the ALL-GROW flag fired ZERO
times — every residue configuration contained a pool-stable ψ-witness
(one adding nothing to m's variable-free theory at rank rslope(2d)).
The winning-answer classification never ran for lack of subjects.

The promotion theorem, adjudicated: promotion_iff_internal (PROVED,
[propext, Quot.sound]) shows that with the kv-partner at full rank,
window promotion of ANY K-world's link is a K-INTERNAL question —
full-rank agreement with the grown kv — so "pointwise promotion at κ"
is refutable in isolation (ladder worlds agree to rslope(2d−1) but
not rslope(2d) at every depth) and is DEAD as a theorem target.  The
data instead singles out:

  StableWitness (NEW, the open Prop's working form): in every residue
  configuration, SOME ψ-witness in m's row adds nothing to m's
  variable-free theory at rank rslope(2d).  M-INTERNAL — no K-side
  vocabulary in the conclusion.  rankGap_of_stableWitness (PROVED):
  StableWitness ⟹ RankGap (kb := k through the base link).

Ledger after tonight: MwitResidue(ranked) ⟸ RankGap ⟸ StableWitness,
all bridges PROVED; StableWitness OPEN, supported at 258M/258M
instances, confined by residue_window to failures whose witness
growth lives strictly inside the rank window; RowRigid bases PROVED
outright.  Next: either prove StableWitness (an M-internal minimal-
witness construction — e.g. a ≤-minimal-type ψ-witness in the finite
row, needing that minimal witnesses add nothing at rank rslope(2d),
which residue_window supports for the cl-visible part), or hunt its
countermodel with a battery whose M-rows force GENUINE vf growth on
every witness (rows into strictly-higher ladder rungs — the current
batteries' rows aim at the fallible top or descend).

## §57 (2026-07-27 night) — The minimal-type construction collapses to ONE K-internal inclusion: the grown partner's vf-invisibility

The construction went further than a minimality argument.  The given
witness u' always satisfies type u' ⊇ type m (Rₘ ⊆ Rᵢ persistence),
so a MINIMAL witness adds nothing iff u'-style witnesses reach type m
— and for u' itself the question is settled by the links:

* internal_inclusion (PROVED): type_{r₂}(k) ⊆ type_{r₂}(kv) in every
  configuration — half of stability is free.
* stable_given_iff_internal (PROVED, [propext, Quot.sound]): the
  given witness is stable at rank r ⟺ kv vf-agrees with k at rank r.
  THE M SIDE DROPS OUT of StableWitness-via-u'.
* stableWitness_of_kvInvisible (PROVED): if in every configuration
  the grown iback-partner's variable-free theory at rank rslope(2d)
  equals the base's — its cl-trace growth being vf-INVISIBLE
  (p-laden) — then StableWitness holds and the entire chain
  MwitResidue(ranked) ⟸ RankGap ⟸ StableWitness closes.

THE OPEN KERNEL, in its sharpest form yet: kv's growth over k is
vf-invisible at rank rslope(2d).  Kernel-checked support: the
all-grow flag's 0/258M (which, unpacked, says exactly that u' never
pool-grew m — equivalently kv never pool-grew k); residue_window
covers the cl-visible part at rank ≤ rslope(2d−1).  Falsifier design
(next): the CONFIG-COMPLETION probe — enumerate same-cl-trace,
vf-differing K-pairs (they exist on p-decorated ladders: cl-trace
bands are height-intervals, rungs refine them) and test whether ANY
completes to a full configuration; whichever hypothesis blocks
completion is the proof's missing ingredient.

## §58 (2026-07-27 night) — Config-completion verdict: 0/7,362 complete; the WITNESS LINK does the protecting

wip/mwit_complete_out.txt (264 models, 162 confluent, 81 s):

  cl1: pairs 4,043; vf-VISIBLE 3,621 (kv-adds 3,564, kv-drops 0,
       mixed 57); blocking S0=190 S1=0 S2=0 S3=3,431 S4=0; COMPLETED 0.
  cl3: pairs 4,202; vf-VISIBLE 3,741 (3,705/0/36);
       blocking S0=184 S1=0 S2=0 S3=3,557 S4=0; COMPLETED 0.

Three readings.  (1) kvInvisible survives its direct assault: not one
visible pair completes to a configuration.  (2) internal_inclusion's
prediction confirmed exactly: kv-drops pairs are ABSENT even as
candidates (0/7,362 — persistence up Rᵢ from the common k' forbids
dropping).  (3) The protection is concentrated in ONE hypothesis: S3
— the witness link.  For 95% of visible pairs, k' exists, the
reservoir partner m' exists, the base partner m exists — and then NO
infallible u' in m's row realises kv's grown vf-type at rank
rslope(2d).  The reservoir and base stages never block (S1 = S2 = 0).

THE MECHANISM, named: witness-realisability.  A completing u' must
realise kv's exact pool-type inside the ◯-row of a base-type
realiser; on the batteries, grown types live at fixed ladder heights,
rows step by fixed strides, and the band/stride/type alignment never
occurs.  The two decisive next moves, in priority order:
(i) the HAND-ALIGNED countermodel attempt — engineer U, the
p-decoration and the Rₘ-stride so band boundary, vf-difference and
row-step coincide (if it completes, kvInvisible is dead and the
StableWitness/RankGap conclusions get their first genuine test);
(ii) the witness-realisability lemma — prove abstractly that an
infallible row-witness over a rank-rslope(2d)-agreeing base cannot
realise a vf-visibly grown type (this would close kvInvisible, hence
StableWitness, hence RankGap, hence the ranked MwitResidue — the
entire route).  The wall, if it is one, now has exactly one brick.

## §59 (2026-07-27 late) — Witness-realisability FALSE as a row-fact; the ranked route retired; the synthesis

The §58(ii) abstract lemma is dead before being stated: the canonical
model canonU itself contains infallible vf-VISIBLE row-risers.  Take a
prime theory T of the q5-class (◯¬◯⊥ ∈ T, ¬◯⊥ ∉ T, proper): obInv T
is a proper theory containing ¬◯⊥ — an infallible row-successor whose
variable-free type strictly grows, exactly what witness-realisability
must forbid.  The probes never saw it because (hand-check,
scratchpad/handcheck.lean) the aligned battery frames were silently
NON-CONFLUENT — the stride/parity split breaks the squares, and
mutConf filtered the whole class out.  Verdict on the §58 fork: the
hand-aligned countermodel is the LIVE branch (q5→q3 riser, D = ¬◯⊥,
crank 3, d = 2, links r₁ = 21 / r₂ = 45), and the lemma branch is
CLOSED.

Stepping back (the wood): every uniformly-quantified clause this route
posed was refuted by the ◯⊥-ladder — bandCollapse (E ≥ R+2),
rnDict_false, and now the residue's realisability core; every
formula-local, per-instance statement was PROVED or held at 100% over
~330M instances.  Fragment infinitude (rnEmbed, kernel-checked) is not
a nuisance in the bookkeeping, it IS the obstruction: no rank bound
uniform in the closure can survive, so the residue must be quantified
per interpolation instance (rank a function of φ), or the target logic
must lose the ladder.  Both moves now proceed in parallel; the second
is §60.

## §60 (2026-07-27 late) — PCLL+¬◯⊥ (the infallible system): variable-free collapse, 1-variable UI, sound+complete semantics, search commands — ALL PROVED

New library modules LaxLogic/PLLNoFall.lean, PLLSearchNoFall.lean
(imported from LaxLogic.lean; manual §6; demo §6 pinned).  The system:
DerivUNoFall Γ φ := DerivU (¬◯⊥ :: Γ) φ — axiom = persistent
hypothesis, legitimate because every rule carries its context and the
deduction theorem holds.  Results, all sorry-free and guard-pinned
clean-classical:

  varfree_dichotomy   every variable-free A: ⊢ A or A ⊢ ⊥.  The
                      ◯⊥-ladder collapses to {⊥,⊤}; the axiom is used
                      ONCE (◯-case: ◯A ⊢ ◯⊥ ⊢ ⊥); distribution is
                      never used, so PLL+¬◯⊥ inherits the proof.
  exUI / allUI        strongest variable-free consequence and weakest
                      variable-free antecedent exist for EVERY φ
                      (⊤/⊥ by consistency resp. derivability) — for
                      1-variable φ these are ∃p.φ / ∀p.φ of the
                      1-variable language.  UI(1pv) for PCLL+¬◯⊥ is
                      SETTLED (positively, and trivially — the right
                      kind of trivial: the ladder was the problem).
  consistent          [propext] only, one-world infallible model.
  derivUNoFall_iff_infallible_valid
                      sound and COMPLETE for mutually confluent
                      infallible models — canonU relativised to the
                      proper primes containing ¬◯⊥ (obInv preserves
                      both properties: unit gives ◯¬◯⊥, and ◯⊥ + ¬◯⊥
                      is inconsistent; prime_extension re-used as-is,
                      properness free from avoiding a formula).  The
                      "take as read" model theory is now a theorem.
  pcll_not_nobot      the extension is proper (0 ⊳ fallible 1, pinned
                      by decide).

Search: infB (no fallible worlds) joins confB as the battery filter;
#searchNF / #refuteNF mirror #search / #refuteConf; certificate
theorems not_derivUNoFall_of_check ([propext, Quot.sound], checked
context is Γ alone — infallible models force the axiom) and
derivUNoFall_of_nd ([propext]).  Showcase guard: ◯⊥ ⊢ ⊥ is
PLL-REFUTED and NF-PROVED.

Scope kept precise: exUI/allUI interpolate against VARIABLE-FREE ψ
(the 1-variable language's p-free formulas).  Against p-free ψ over
additional variables the property is not asserted — that is the
≥2-variable theatre, where the 1-variable fragment (still infinite:
the Rieger–Nishimura lattice survives ¬◯⊥) becomes the target.

## §61 (2026-07-28) — UI for PCLL+¬◯⊥, stage 1: the ◯-normalisation engine, the IPC calibration, and the divergence separator

Matthew's directive: prove UI completely for PCLL+¬◯⊥, then adapt to
PLL+¬◯⊥; probe only when stuck.  Route chosen: SYNTACTIC (Pitts-style
computation over a terminating calculus).  The semantic
bisimulation-quantifier route would re-meet the fragment-infinitude
wall one variable up (the 1-variable target fragment of the ≥2-variable
problem is Rieger–Nishimura-infinite even under ¬◯⊥); the syntactic
technology is exactly what handles infinite target fragments (IPC).

Landed tonight (LaxLogic/PLLNoFallNF.lean, PLLNoFallSep.lean; all
guard-pinned, [propext, Quot.sound] or clean-classical):

  * EquivNF congruence kit; the lattice-homomorphism laws: ◯ commutes
    with ∧ (strong monad), ∨ (distribution — its single use), ⊥ (the
    axiom), and is idempotent.
  * nf : every formula is interderivable (nf_equiv) with a ◯-NORMAL
    form — ◯ only on atoms and implications (nf_normal); derivability
    invariant under normalisation (nf_iff).  The calculus and the
    interpolant computation need only speak normal forms; the ◯∨/◯⊥
    cases are compiled away.
  * derivUNoFall_iff_IPLND: the ◯-free fragment of PCLL+¬◯⊥ is EXACTLY
    IPC (erasure kills the axiom and the distribution instances;
    IPLND embeds back).  Calibration: full UI here CONTAINS Pitts'
    theorem for IPC; nothing cheaper closes it.
  * THE SEPARATOR (sep_derivable / sep_not_pll_nofall, both by decide):
    ◯(a⊃(b∨c)), ◯a ⊢ ◯b∨◯c is ◯-normal, PCLL+¬◯⊥-derivable, and NOT
    PLL+¬◯⊥-derivable (five-world infallible ∀∃-countermodel,
    necessarily non-confluent).  So distribution is NOT admissible
    from ¬◯⊥ even on normal forms: the PCLL+¬◯⊥ calculus needs a
    distribution-aware ◯-rule (laxL with conclusions in the
    ∨-closure of ◯-formulas and ⊥ — sound by confluence + Rm ⊆ Ri,
    derives distribution, and its ⊥-case carries the density power),
    while PLL+¬◯⊥ keeps G4iLL″'s laxL.  The two Pitts computations
    will differ exactly there.

LITERATURE (checked tonight): Iemhoff, Proof Theory for Lax Logic
(arXiv:2209.08976) claims UI for PLL via G4iLL; its completeness
(Corollary 1, via Thm 1 of arXiv:2011.11847) is REFUTED
machine-checked in this repo (PLLG4Gap.lean: ◯G', F' ⇒ r with
F' = ◯p⊃r, G' = F'⊃◯p — Howe duplication straddling the box-opening).
So the published UI-for-PLL proof has a gap at its completeness step,
and this programme would repair a published result, not merely fill a
silence.

NEXT (stage 2): the calculus.  For PCLL+¬◯⊥: G4iLL″ with the widened
laxL/impLLaxLax conclusions (◯-disjunctive targets incl. ⊥), stated on
◯-normal sequents; prove sound for DerivUNoFall and complete (target:
via the canonN semantics or by adapting the G4c equiv_nd chain);
establish the termination order.  For PLL+¬◯⊥: G4iLL″ + nobot as
persistent hypothesis (complete by equiv_nd already — only the
◯⊥-absurdity needs building in or keeping as the hypothesis).  Then
stage 3: the Pitts computation by induction on the termination order,
following the mechanised-UI blueprint (Férée–van der Giessen–van
Gool–Shillito's Coq development for IPC/K/GL).

## §62 (2026-07-28) — Stage 2 design fork resolved: the PICLL calculus must be multi-succedent; PILL needs no new calculus

Working the cut cases of the planned single-succedent calculus (G4iLL″
with laxL conclusions widened to disjunctions of ◯-formulas and ⊥) BEFORE
building it exposed a genuine incompleteness: cut on a laxL-produced
disjunction cannot be pushed below the widened rule (its goal restriction
blocks the left commutation), and the obstruction is realised by a
concrete sequent, now PINNED (PLLNoFallSep.lean):

  ◯(a⊃(b∨c)), ◯a, ◯b⊃p, ◯c⊃p ⊢ p
    PICLL-derivable (cutNeed_derivable — through ◯b∨◯c, i.e. a cut)
    PILL-underivable (cutNeed_not_pll — p-decorated five-world model).

In any cut-free single-succedent derivation the goal must commit to ◯b
or ◯c before the box opens, and the b∨c case split happens inside the
box: the other branch strands.  Conclusion: the PICLL calculus carries a
MULTI-SUCCEDENT ◯-rule — from Γ, X ⊢ ◯B₁,…,◯Bₖ infer
Γ, ◯X ⊢ ◯B₁,…,◯Bₖ, Δ (k = 0 gives the density power; the ◯-succedent
travels through implication eliminations together) — over an m-G4ip
core (invertible ∨R with both disjuncts in the succedent; ⊃R and the
implication-proving premises single-succedent).  Open design points,
deliberately not baked in tonight: whether the LaxLax repair (Howe
duplication) is still required in m-form, and the exact premise shapes
of the ⊃◯-left rules; both need the g4p-ladder analysis re-run against
the m-format.

PILL, by contrast, needs NO new calculus: no distribution, so G4iLL″ +
¬◯⊥ as permanently inhabited context is complete (equiv_nd), has
admissible cut (SelfAbsorb chain), and a terminating decider (G4sh.dec)
— and nobot is variable-free, so the inhabited context never interferes
with p-freeness in an interpolant computation.

SEQUENCING RECOMMENDATION (within Matthew's "up to you" licence on the
calculus handling): run the Pitts computation FIRST for PILL on the
existing complete machinery — every interpolant clause is a template
for the PICLL version — THEN build the m-chain (def/perm/weaken/inv/
ctr/cut/comp, patterned on PLLG4H*) and port the computation.  The
PICLL-first order at the calculus stage would mean building the ~2.5k
line m-chain before any UI content exists to test it against.

## §63 (2026-07-28) — Iemhoff's interpolant assignment transcribed; the adaptation obstacle identified: G4iLL″ is not ≪-reductive, so the recursion must run on the cumulative-set formulation

Fetched and read Iemhoff, Proof Theory for Lax Logic (arXiv:2209.08976;
PDF in the session scratchpad).  Her G4iLL (Fig. 2.3) = G4ip + R◯, L◯,
R◯→, L◯→ — all four in CONSUMING form (L◯: Γ,ψ ⇒ ◯φ / Γ,◯ψ ⇒ ◯φ
replaces the box by its opening; L◯→ premise 1 = Γ,◯χ ⇒ ◯φ drops both
ψ and the implication).  The repo's repair keeps the box (membership)
and keeps the implication in premise 1 — the gap sequent showed the
consuming forms incomplete.

Her UI method (§§6.3–6.7), the shape to adapt:
  * interpolant assignment ι: to each rule instance R with conclusion S,
    p-free-of-lower-rank formulas ι∃ᵖRS, ι∀ᵖRS; to non-principal
    occurrences ι∃ᵖR̄S, ι∀ᵖR̄S; ∀pS ↦ ∀⁺ ∨ ∀⁻ ∨ ∀ᵃᵗ, ∃pS ↦ ∃⁺ ∧ ∃⁻ ∧ ∃ᵃᵗ
    (∀ᵃᵗ/∃ᵃᵗ the atom clauses); rewrite relation ⟶ confluent + SN by
    reductivity (her Lemma 2 ← Iemhoff 2019b Lemma 3).
  * three interpolant properties (∀l), (∃r), (∀∃) over p-partitions
    (Sʳ, Sⁱ); six inductive properties per rule (IPP/IPN × ∀/∃, DPP,
    DPN) with the induction along ≺; Theorem 5: balanced calculus +
    sound assignment ⟹ UI.
  * the standard assignment for the ◯-rules (her §6.6):
      R◯, L◯:  ι∃ = ◯∃pS₁, ι∀ = ◯∀pS₁; non-principal ⊤/⊥.
      R◯→:     ι∃ = ∃pS₁ ∧ (∀pS₁ → ∃pS₂); ι∀ = ∀pS₁ ∧ ∀pS₂;
               non-principal ∃ = ⊤ or ∃p(Sᵃ ⇒); ∀ = ⊥.
      L◯→:     ι∃ = ◯∃pS₁ ∧ (◯∀pS₁ → ∃pS₂); ι∀ = ◯∀pS₁ ∧ ∀pS₂;
               non-principal via Sᵞ: for γ = ◯α→β ∈ Sᵃ,
               Sᵞ⁰ = (Sᵃ\{γ} ⇒ ◯α), Sᵞ¹ = (Sᵃ\{γ}, β ⇒ Sˢ);
               ∃-side ⋀ over boxed members and such γ; ∀-side
               ⋁ ◯∀pSᵞ⁰ ∧ ∀pSᵞ¹.
    Soundness = her Lemmas 3–6 (templates for ours).

THE OBSTACLE (found by checking her side conditions against G4iLL″):
her whole recursion lives on the reductive order ≺ built from the
Dershowitz–Manna weight order ≪, and rule premises must be ≪-BELOW
their conclusions.  The repo's REPAIRED rules are not: laxL and L◯→″
keep their principals (membership) and add the opening, so the premise
multiset properly grows — G4iLL″ terminates by the finite-space
loop-check (G4s, the cumulative set calculus of PLLG4Set/PLLG4Dec),
not by ≪-descent.  Consequently the interpolant recursion for PILL
must run on the CUMULATIVE-SET formulation: sequents = (set context,
goal) inside the finite closure space; the measure = the decider's own
(remaining-space, …) order; the lower-rank side conditions of the
assignment become later-in-that-well-order conditions.  This is the
principled divergence from Iemhoff — the same spot as the
completeness repair, as expected.

NEXT (stage 3 concrete): (1) recon PLLG4Set's G4s rules + the exact
decreasing measure of G4sh.dec; (2) define the interpolant pair over
G4s-space by well-founded recursion on that measure, clauses = her
table with the keeping-form adjustments (premise-1 of L◯→″ keeps the
implication: its ι-clauses take S₁ = (X :: Γ ⇒ ◯A) with the
implication still inside — check rank/space side conditions); (3) the
six properties per rule, her Lemmas 3–6 adapted; (4) assemble
UI(PILL); then the m-chain for PICLL.

## §64 (2026-07-28) — The interpolant recursion design for G4iLL″: fuel-indexed over the finite sequent space

G4s recon (PLLG4Set): fully cumulative Finset contexts, every rule
inserts-and-keeps, G4c.iff_setFin, decider G4sh.dec structural on
height.  Working Iemhoff's assignment against it:

THE PRECISE BREAKAGE of her static order: within a FIXED context the
backward rule graph of the keeping-form calculus can revisit sequents
(a laxL whose opening is already present is a literal self-loop;
impLImp/impLLaxLax instances whose insertions are present jump the
goal to an antecedent of a context member, and goal chains can cycle).
So no static rank ≺ exists with all premises below their conclusions,
and her rewrite ⟶ would diverge.  What remains true: G4sh premises
sit at strictly smaller HEIGHT, and a minimal-height derivation never
repeats a sequent along a branch (a repeat is a removable detour), so
every minimal derivation has branch length ≤ |seqEnumF|.

THE DESIGN, replacing the static rank: FUEL-INDEXED interpolants

  I∀, I∃ : Nat → Seq → Formula
  I(0, S)     := neutral (⊥ for the ∀-disjunction, ⊤ for ∃)
  I(n+1, S)   := Iemhoff's per-rule combination (her §6.6 table with
                 the keeping-form premise shapes) applied to
                 I(n, premise)s, over all rule instances with
                 conclusion S, plus the atom clauses

with ∀pS := I∀(N, S), ∃pS := I∃(N, S) at N := |seqEnumF| + 1.  The
big disjunctions/conjunctions are finite because instances-with-
conclusion-S range over the finite context and subformula data ✓.
The three interpolant properties are then proved by induction on
minimal derivation height, which is ≤ N along every branch, matching
the fuel: her six per-rule inductive properties (Lemmas 3–6) become
lemmas about I(n+1, S) vs I(n, ·) with the derivability hypotheses at
minimal height.  The self-loop/cycle instances contribute neutral
elements at fuel 0 and are harmless precisely because minimal
derivations never use them (the detour-removal lemma is the new
plumbing obligation, alongside fuel-monotonicity of the properties —
NOT of the formulas: no I(n) ≡ I(n+1) stability needed if the
properties are proved directly at fuel N).

Candidate simplification to examine first: can laxL consume its box
(≪-style) with only impLLaxLax in keeping form, preserving
completeness?  The gap analysis blamed only L◯→'s consumed
implication; if consuming-laxL + repaired-L◯→ is still complete, the
cycle sources shrink (though impLLaxLax premise-1 goal-jump remains,
so the fuel design is needed regardless).

NEXT SESSION (stage 3 build order): (1) Seq/space plumbing: reuse
seqEnumF; instance enumeration per conclusion; (2) I∀/I∃ by fuel
recursion (computable, so the searcher can TEST the interpolant
properties on concrete sequents before any proof — cheap sanity per
Matthew's probe discipline, since a failed property here would be a
counterexample, not a probe); (3) detour-removal + minimal-height
lemmas; (4) the six properties per rule (12 core rules from her G3ip
lemmas + 4 lax rules from Lemmas 3–6, keeping-form-adjusted); (5)
assemble (∀l), (∃r), (∀∃) and UI for PLL — with UI for PILL as the
nobot-context instance (nobot variable-free: p-freeness untouched).

## §65 (2026-07-28) — THE RECORD CORRECTED: the syntactic tower already exists (July 8–11), assembled to the crown with ONE open kernel; §64's "fresh design" re-derived its architecture

Matthew: "the syntactic route was tried in a different session, which
ended a week ago."  Confirmed, and the trace IS in the repo — in wip/,
outside the lakefile globs and outside PROGRESS.md (which postdates
it), which is how the §61–64 survey missed it.  My memory thread
recorded only its endpoint ("UI proof effort STOPPED 2026-07-12,
budget stop" and the descent-probe redirect) without the tower itself
— a memory failure, now fixed.

The tower (commits ≤ b32ee91, 2026-07-11, all ancestors of HEAD):

  LaxLogic/PLLG4UITrunc.lean  base: weight/atoms, G4c/G4s/G4sh + cut,
                              defect/mu measures, the TRUNCATED
                              QUANTIFIER TABLES itpE/itpA (fuel- and
                              budget-indexed), itp_pfree, itp_sound.
                              Axiom-clean.
  wip/absorb_base.lean        kcap budget + absorption/stabilisation
                              ladder (itp_stab_le); THE open kernel
                              cascade_low_pos (sorry) — the only
                              sorryAx entry.
  wip/adequacy.lean           PieceClosed spaces; Pitts (iv)
                              itp_adequate (sorry-free in itself).
  wip/indiff.lean             FUEL INDIFFERENCE proved: above mu the
                              quantifiers are syntactically equal
                              across fuels.  (The §64 worry about
                              cross-fuel mismatch was solved here.)
  wip/spaceindiff.lean        space indifference proved.
  wip/packaging.lean          existsP/forallP; Pitts (i)–(iii)
                              outright; (iv)+factorisation modulo
                              hFI/hSI.
  wip/final.lean              discharges hFI/hSI; the crown
                              uniform_interpolation_PLL, pinned:
                              [propext, sorryAx, Classical.choice,
                              Quot.sound], sorryAx via exactly
                              cascade_low_pos.

  95480dc: the box-free instance cascade_low_pos_boxfree PROVED ⟹
  **uniform interpolation for IPC, sorry-free**, inside this repo.

THE OPEN KERNEL, precisely (absorb_base.lean:2259,
cascade_low_pos_box): a low-BUDGET descent for the ◯-involving case —
from G4c Δ (itpE p S fuel (c+1) Γ) and G4c Δ (itpA p S fh (c+1) Γ g)
(fh ≤ fuel, 1 ≤ defect S Γ, defect·(|jumpGoals|+2) ≤ c) conclude
G4c Δ (itpA p S fuel c Γ g).  Its docstring records: zoo-tested TRUE
at every probed instance; the known decompositions all fail (chains
hit the (◯-goal, 0) false point; the E-mate fails at 1; continuations
cannot cross seals); the semantics' mechanism at c = 1 is syntactic
starvation (b-gated tables at saturated contexts collapse to ⊥); the
proposed proof plan = starvation-collapse lemmas + a (defect, budget)-
lex landing map meeting the pigeonhole band from below —
"cascade_main-scale work, not attempted".

THE UNIFIED HISTORY, now visible: the tower stalled on
cascade_low_pos (budget stop 2026-07-12) → its 1-variable case was
proved TRUE (3322f22) and "reduced to a single semantic-stabilisation
descent" → that descent became the SEMANTIC campaign (semui files,
layered/ranked pipeline) → which died at witness-realisability
(§59).  One wall, two clothings: the ◯-case descent.  Matthew's
skepticism was exactly right in shape; what he remembered as "the
syntactic route led nowhere" is more precisely "the syntactic route
reached ONE lemma, whose semantic reformulation then also stalled".

REVISED PLAN (supersedes §64's from-scratch build): resurrect the
tower (verify it compiles on v4.31; wire the build), then attack
cascade_low_pos_box ON it, in order:
  (1) the docstring's own plan (starvation-collapse + (defect,budget)-
      lex landing map) — the prior session's named next step, never
      attempted;
  (2) the post-July-12 assets against it: the ◯-normalisation engine
      (obAnd/obOb + PLL-valid laws thin the ◯-case combinatorics),
      canonN-style completeness thinking, and the PILL reading (nobot
      in Γ: does infallibility shrink the starvation analysis? —
      Matthew's original hope, now with a precise target);
  (3) only if (1)+(2) fail: the consuming-laxL redesign / Iemhoff-
      faithful sequent order, checking completeness of consuming-laxL
      + repaired-L◯→ first.
The probe discipline: cascade_low_pos_box is zoo-TRUE, so this is
proof work, not probing; probes only if a sub-lemma of (1) looks
unsatisfiable.

## §66 (2026-07-28) — The kernel campaign opens: floor starvation pinned as theorems (wip/starve.lean)

Translating the tower's vocabulary to standard language as mandated:
the "zoo" = the exhaustive finite nucleus-model battery
(wip/refute4.lean, 34 pairs); a "seal" = one of the four branch shapes
whose box/⊃-introduction blocks the descent's continuations;
"starvation" = a quantifier table's clause list becoming empty, so the
table is literally ⊥ (orAll [] = ⊥).

First bricks PROVED ([propext, Quot.sound], first-compile): at budget
0 a ◯-shaped goal's table loses its goal clause and truncation
disjunct (itpAgoal_obGoal_floor, itpAfull_obGoal_floor), so it
normalises to its environment clauses alone (itpA_obGoal_floor), and
an empty environment table collapses it to ⊥ literally
(itpA_starve_floor) — the battery's unique false point of the bare
low-band descent, now a theorem boundary.

Campaign continuation (the kernel's own unattempted plan, now with
its base): (1) classify starved states ABOVE the floor — which
(Γ, goal, b) have empty tables at b ≥ 1 (the b-gated families vanish;
environment guards are decidable memberships); (2) the
(defect, budget)-lexicographic landing map for the c = 1 base meeting
the pigeonhole band from below; (3) lift the battery's proved-free
laws: the fresh-antecedent equality E@(c+1)(Γ) ⊓ E@c(C₁::Γ) =
E@(c+1)(C₁::Γ) (exact on every battery instance) and the
piece-closed-S goal-membership invariant (kills the fresh-antecedent
seal for the adequacy consumer's closed spaces — recorded by the
prior session as usable for the CONSUMER'S instance even though the
∀S interface keeps the seal).  The mutual-pair scheme stays dead
below budget 2 (the existential ascent E@c ⊢ E@(c+1) is
countermodel-refuted at c = 1), so the landing map must be
single-sided — that is the mathematical heart of what remains.

## §67 (2026-07-28) — Matthew's check executed: wip/G4conf.lean's assumed metatheory REFUTED kernel-checked; the inconsistency unwound

The rule added to G4c for confluence exists: wip/G4conf.lean (branch
ui-confluence, design docs/confluent-ui-plan.md) defines G4cf = the 17
G4iLL″ rules + distL (analytic left rule: from ◯(A∨B) ∈ Γ branch to
◯A resp. ◯B), with soundness PROVED and — under stated licence — four
sorried claims: G4c ⊆ G4cf (true, routine), distF derivable (true,
routine), completeness for confluent validity, and cut admissibility.

VERDICT of the check (wip/g4confGap.lean, all [propext, Quot.sound],
first-compile): **completeness-without-cut is FALSE and hence cut is
NOT admissible** (granted the two routine lemmas).  Witness = the §62
cut-necessity sequent ◯(a⊃(b∨c)), ◯a, ◯b⊃p, ◯c⊃p ⊢ p:
  * derivU_gapSeq — PCLL derives it (pinned searcher term through the
    cut formula ◯b∨◯c); confluent-valid by derivU_sound;
  * g4hf_to_g4h — on sequents with no subformula of shape ◯(A∨B)
    (invariant NoObOr, preserved by all 18 rules; distL can never
    fire), G4cf collapses to G4c;
  * pll_not_gapSeq — PLL refutes the sequent (five-world ∀∃
    countermodel, decide);
  * g4cf_not_gapSeq, g4cf_complete_refuted — the conclusions.
G4conf.lean's two false statements are REMOVED and replaced by an
adjudication block; the two true sorried lemmas remain, annotated.
No Lean file imported the false claims (blast radius: two docs).

THE UNWOUND ACCOUNT (correcting §§62–65's narrative and yesterday's
"nothing exists for PCLL"): a single-succedent confluence-extended
calculus DID exist in the repo, with its completeness and cut assumed.
The §62 stranding analysis, found independently this session, is
precisely the refuter of those assumptions — the two threads now agree,
adjudicated by the kernel: for the distributing systems (PCLL, PICLL),
an analytic hypothesis-keyed distribution rule cannot give a cut-free
complete single-succedent calculus; the repair must carry ◯-disjunctions
across implication eliminations (multi-succedent ◯-rule, or an
elimination rule internalising the case split).  The PLL tower (§65) is
untouched: it never used distL, and PLL never derives such sequents.

## §68 (2026-07-28) — Seal analysis with fresh eyes: the E-ascent is avoidable at seals; box_absurd (the starved-seal engine) PROVED; the candidate landing measure

Reading the four seal call sites (absorb_base 2605/2634/3142/3361)
and the guarded/consumed campaign record produced three observations,
the first two banked as theorems, the third as the design to build:

1. **The E-ascent is NOT needed inside a seal.**  The recorded failure
   ("the E-mate genuinely fails low", zoo-refuted at c = 1) closes off
   the mutual-pair scheme — but inside a seal the entire outer context
   crosses the box (laxL retains contexts), so the outer ambient
   E@(c+1) is available INSIDE, and firing the opened source guard
   needs only the DOWNWARD E@(c+1) ⊢ E@c (budget monotonicity), never
   the ascent.  The seal's residual obligation is then the pair
   descent one budget down at the same Γ — the same statement with
   c − 1 — plus room bookkeeping.  So the low-band knot is purely the
   TERMINATION of same-Γ seal chains, not the E-mate.

2. **Starved seals close** (wip/starve.lean, PROVED, first-compile):
   box_absurd — a boxed guarded implication whose value slot is ⊥,
   with a derivable guard, yields ANY ◯-conclusion (open, fire,
   explode).  Plus itpA_starve_elimAtom: the eliminated atom's goal
   clause is empty at EVERY budget, so its table collapses to literal
   ⊥ whenever the environment table is empty — starvation is not only
   a floor phenomenon.  Together: any seal whose inner partner
   starves is dispatched outright.

3. **The candidate landing measure** (to formalise next): strengthen
   the descent statement so seals recurse into IT rather than around
   it, with the lexicographic measure
       (defect S Γ, budget, unvisited jump goals, goal weight):
   growth moves drop defect (defect_lt_of_mem) and reset everything;
   seal moves drop budget at fixed defect (same Γ) and reset the rest;
   fresh jump moves drop the unvisited count; repeat jumps must close
   by splice from the in-context recorded value (the one step whose
   DIRECTION must be checked against cascade_main's actual splice —
   itp_budget_mono_le's orientation decides whether the splice works
   below the pigeonhole band or needs the starvation classification to
   discharge the low-budget repeats); decomposition drops weight.
   The room hypothesis defect·(J+2) ≤ c funds exactly J+2 seal-burns
   per defect level, which the measure consumes as budget-drops at
   fixed defect — the arithmetic to verify is that goal repeats within
   a fixed (defect, Γ) band arrive within J+2 burns (the pigeonhole
   the prior session ran OUTSIDE seals, now run inside the recursion).

NEXT ACTIONS: read cascade_main's splice case (the exact direction of
itp_budget_mono_le at repeats) and the four call sites' room
arithmetic; then draft the strengthened statement and run its measure
against each of the 10 move classes on paper before any Lean.

## §69 (2026-07-28) — The kernel's state graph mapped; the two reduction targets T1/T2

Monotonicity directions CONFIRMED in the tower: itp_budget_mono_le is
the free pair (E downward: [E@b] ⊢ E@b' for b' ≤ b; A upward:
[A@b'] ⊢ A@b), proved outright; itp_stab_le is the hard pair (E-ascent
+ A-descent), proved only above kcap via the cascade.  cascade_main's
continuations take g'-values at the entry budget and any superset
context; its E-half carries room J+3+defect·(J+2) ≤ c — consistent
with the zoo's bare-ascent refutation at c = 1.

THE SEAL STATE GRAPH (same Γ, kernel(c) := [E@(c+1), A@(c+1)(Γ,g)] ⊢
A@c(Γ,g), all moves verified against the clause tables):
  * goal-γ seal (g = ◯D): commit target ◯(E@(c-1) ⇢ A@(c-1)(Γ,D));
    inside: fire the source guard with E@c from the ambient by
    DOWNWARD mono (no ascent!), then kernel(c-1) at goal D — the
    goal UNBOXES: weight strictly drops.
  * clause-γ seal (env ◯⊃-family member ◯A₁⊃B): inner goal ◯A₁ —
    weight resets, but heads range over the FIXED finite γ-head set;
    cycles possible (the zoo's chained-d2 IS the 2-cycle
    ◯p ⇄ ◯r via ◯p⊃r, ◯r⊃s) — budget burns along the cycle.
  * truncation seal: same state, budget ↓.
  * fresh-antecedent seal: outside-S piece; dead for piece-closed S
    (the consumer's case).
  * non-seal moves: growth (defect ↓, room replenishes by J+2),
    decomposition (weight ↓), jump family (cascade_main's own
    pigeonhole, unsealed).
Termination resources: unboxing (weight), defect drops, SOURCE-side
starvation (box_absurd dispatches any branch whose source inner value
is ⊥ — with the guard from ambient downward mono), and the open
residue: non-starving γ-head cycles above the floor, where repeats
yield nothing (values lift UP, obligations point DOWN) — the
one-step budget stabilisation at low budget, once more.

REDUCTION TARGETS (bounded, plausibly provable now):
  T1 (seal one-step reduction): IF kernel(c−1) holds for all goals at
     this Γ THEN the four sealed branches of kernel(c) close — the
     plumbing is: orAll-intro the corresponding target disjunct, laxR
     wait laxL-commit on the source box, fire the guard by ambient
     downward mono (itp_budget_mono_le.1), impR, invoke kernel(c−1).
     Lands kernel = downward induction on c with a single base at the
     band floor, replacing "all c in the band" by "the floor c₀".
  T2 (starvation dispatch): integrate box_absurd + the starve
     classification: every sealed branch whose source inner table is
     empty closes outright; with itpA_starve_floor / _elimAtom this
     kills the x = 0-adjacent layer and every saturated-state branch.
After T1+T2 the open content is exactly: the floor instance of the
descent at non-starving cycling states — a finitely-generated family
per (S, Γ) — to be attacked by per-shape stabilisation (the state
graph at fixed Γ is finite; the conjecture is that within one full
γ-head cycle every branch either starves, unboxes, or grows).
