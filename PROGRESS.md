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
machine-checked in `wip/semantic_ui.lean` (the file's only sorries
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
  table doc). Oracle warning: failing `search` cost is CHAOTIC in
  fuel (non-monotone); cap weights and order cheap attempts first.
