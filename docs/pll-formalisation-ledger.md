# The PLL formalisation in Lean: statement-level ledger

*Generated 2026-07-16, branch `claude/belief-lax-logic-handover-f331bf`,
toolchain Lean v4.31.0 + Mathlib v4.31.0.*

**Paths.** All file references are repository-root-relative (from this `docs/`
directory, prepend `../`). *Promotion note (2026-07-16): under the policy that
nothing in `wip/` is ever claimed as formally proved, the Curry-paper files and
the finished belief modules were moved into the `LaxLogic/` library —
`wip/context_completeness.lean` → [`LaxLogic/PLLCtxCompleteness.lean`](../LaxLogic/PLLCtxCompleteness.lean),
`wip/lax_infinite.lean` → [`LaxLogic/PLLLaxInfinite.lean`](../LaxLogic/PLLLaxInfinite.lean), and the seven
`wip/belief_*.lean` files → `LaxLogic/Belief*.lean` (see
[belief-mechanisation-index.md](belief-mechanisation-index.md)) — all imported
by the library root, so `lake build` checks them. Only the in-development
[`wip/belief_realisability.lean`](../wip/belief_realisability.lean) and the separate UI-probe files remain in
`wip/`.*

**Purpose.** Lean's kernel checks the *proofs*; what remains for a human is to
check that the *statements* — the definitions and the displayed theorems — say
what they are claimed to say. This ledger is that checklist: each row names a
result, its Lean identifier and location, and its axiom audit, so the human
task reduces to reading the statement at the cited location and agreeing it
formalises the intended claim. Every audit below was **re-run on 2026-07-16**
(not copied from earlier notes); to re-verify any row, run
`lake env lean <file>` for a file containing `#print axioms <name>`.

**Axiom key.**
- **none** — fully constructive: no axioms at all.
- **[p]** = `[propext]`; **[p,Q]** = `[propext, Quot.sound]` — no choice.
- **clean** = `[propext, Classical.choice, Quot.sound]` — the ordinary axioms
  of classical Lean.
- No entry uses `sorryAx` (no `sorry` anywhere in `LaxLogic/`) and none uses
  `ofReduceBool`/`native_decide` except where explicitly flagged.

---

## 1. The systems and their equivalence (F&M I&C 1997, §2)

| result | Lean name | location | axioms |
|---|---|---|---|
| Natural deduction for PLL (membership-based contexts; weakening/exchange/contraction admissible, cast-free) | `LaxND` (+ `LaxND.rename`) | [`PLLNDCore.lean:72`](../LaxLogic/PLLNDCore.lean) | (def) |
| Cut-free G3-style sequent calculus, height-indexed | `SCh` / `SC` | [`PLLSequent.lean:31,58`](../LaxLogic/PLLSequent.lean) | (def) |
| **Cut admissibility** (lexicographic induction; F&M Thm 2.6 engine) | `SC.cut` | [`PLLSequent.lean:524`](../LaxLogic/PLLSequent.lean) | clean |
| **Cut elimination** | `cutElimination` | [`PLLSequent.lean:615`](../LaxLogic/PLLSequent.lean) | clean |
| Sequent ⟶ natural deduction | `SC_to_ND` | [`PLLSequent.lean:546`](../LaxLogic/PLLSequent.lean) | clean |
| Natural deduction ⟶ sequent | `ND_to_SC` | [`PLLSequent.lean:578`](../LaxLogic/PLLSequent.lean) | clean |
| **Disjunction property** (F&M Lemma 2.7) | `disjunction_property` | [`PLLSequent.lean:623`](../LaxLogic/PLLSequent.lean) | clean |
| **`◯`-reflection**: `⊢ ◯M ⟹ ⊢ M` (F&M Lemma 2.7) | `somehow_reflection` | [`PLLSequent.lean:637`](../LaxLogic/PLLSequent.lean) | clean |
| **Hilbert ⟷ natural deduction** | `hd_iff_ND` | [`PLLHilbert.lean:194`](../LaxLogic/PLLHilbert.lean) | **[p]** |
| **Conservativity over IPL** (erasure form) | `conservativity_prop` | [`PLLNDCore.lean:193`](../LaxLogic/PLLNDCore.lean) | [p,Q] |
| **Conservativity over IPL** (classic form: IPL sequents) | `conservativity_IPL` | [`PLLNDCore.lean:211`](../LaxLogic/PLLNDCore.lean) | **[p,Q]** — no choice |
| Strong extensionality (F&M Thm 2.5) | `strong_extensionality` | [`PLLTheorems.lean:178`](../LaxLogic/PLLTheorems.lean) | clean |

## 2. Kripke constraint semantics (F&M §3–4)

| result | Lean name | location | axioms |
|---|---|---|---|
| Constraint models (F&M Def 3.1) + forcing (Def 3.2) | `ConstraintModel`, `force` | [`PLLKripke.lean:28,52`](../LaxLogic/PLLKripke.lean) | (def) |
| **Soundness** (F&M Thm 3.3, sequent form) | `soundness` | [`PLLKripke.lean:97`](../LaxLogic/PLLKripke.lean) | **[p]** |
| **Completeness** (F&M Thm 4.4, strengthened to sequents) | `completeness` | [`PLLCompleteness.lean:614`](../LaxLogic/PLLCompleteness.lean) | clean |

## 3. Countermodels — known non-theorems, formally refuted (F&M Fig. 3)

| non-theorem | Lean name | location | axioms |
|---|---|---|---|
| `⊬ ¬◯⊥` (no doxastic `D`) | `not_provable_not_somehow_false` | [`PLLFrames.lean:88`](../LaxLogic/PLLFrames.lean) | [p,Q] |
| `⊬ ◯(A∨B) ⊃ (◯A ∨ ◯B)` | `not_provable_somehow_or_dist` | [`PLLFrames.lean:142`](../LaxLogic/PLLFrames.lean) | clean |
| `⊬ (◯A ⊃ ◯B) ⊃ ◯(A ⊃ B)` | `not_provable_imp_somehow_dist` | [`PLLFrames.lean:205`](../LaxLogic/PLLFrames.lean) | clean |

## 4. Proof-term calculus: strong normalisation

| result | Lean name | location | axioms |
|---|---|---|---|
| **Strong normalisation of the full reduction** (β + `let`-assoc interleaved; Lindley–Stark ⊤⊤-lifting) | `strong_normalisation` | [`PLLTopTop.lean:1266`](../LaxLogic/PLLTopTop.lean) | clean |
| Certified normaliser (normal form reached) | `Tm.normalize_spec` | [`PLLTopTop.lean:1296`](../LaxLogic/PLLTopTop.lean) | clean |

*(Component results — `assoc_sn`, the certified one-step reducer `Tm.step?`, and
the machine-checked failure of quasi-commutation forcing the semantic method —
live in [`PLLStrongNorm.lean`](../LaxLogic/PLLStrongNorm.lean) / [`PLLReducibility.lean`](../LaxLogic/PLLReducibility.lean); not separately audited
here, subsumed by the above.)*

## 5. Beyond the I&C paper

| result | Lean name | location | axioms |
|---|---|---|---|
| **Craig interpolation for PLL** (Maehara over the cut-free calculus) | `craig_interpolation` | [`PLLCraig.lean:401`](../LaxLogic/PLLCraig.lean) | clean |
| Interpolation for implications | `craig_implication` | [`PLLCraig.lean:411`](../LaxLogic/PLLCraig.lean) | clean |
| **Kleene–Brouwer order on an inductively well-founded tree over a well-founded alphabet is well-founded** | `wellFounded_kb`, `wellFounded_kb'` | [`KleeneBrouwer.lean:164,180`](../LaxLogic/KleeneBrouwer.lean) | **none — fully constructive** (in-file guard asserts it) |

*(Naming: the file and the literature say Kleene–Brouwer, also Lusin–Sierpiński;
"Kolmogorov" could not be verified as part of the standard name.)*

## 6. The Curry-paper results (F&M TYPES 2000, LNCS 2277) — [`LaxLogic/PLLCtxCompleteness.lean`](../LaxLogic/PLLCtxCompleteness.lean), [`LaxLogic/PLLLaxInfinite.lean`](../LaxLogic/PLLLaxInfinite.lean)

| result | Lean name | location | axioms |
|---|---|---|---|
| Constraint-context soundness (Thm 6, ⟸ direction engine) | `Ctx.thm6_soundness` | [`PLLCtxCompleteness.lean:173`](../LaxLogic/PLLCtxCompleteness.lean) | [p,Q] |
| **Context completeness** (Thm 6): `PLL ⊢ φ ⟺ ∀ standard C, IPL ⊢ φ^C` | `Ctx.thm6` | [`PLLCtxCompleteness.lean:651`](../LaxLogic/PLLCtxCompleteness.lean) | clean |
| Lemmas 8, 9 (escape family) | `Ctx.lemma8`, `Ctx.lemma9` | `:973,:864` | clean |
| **No finite constraint set suffices** (Cor 10) | `Ctx.corollary10` | [`PLLCtxCompleteness.lean:981`](../LaxLogic/PLLCtxCompleteness.lean) | clean |
| **The constraint algebra `𝕊` is a Boolean algebra** (Thm 2, bundled Mathlib instance) | `Ctx.thm2_boolean_algebra`, `Ctx.CQuot.instBooleanAlgebra` | `:1588,:1667` | **[p,Q]** |
| **The closed lax fragment `RN(◯,{})` is infinite** | `LaxInfinite.closed_lax_infinite` | [`PLLLaxInfinite.lean:616`](../LaxLogic/PLLLaxInfinite.lean) | clean |

## 7. Decidability of PLL — F&M Theorem 2.8, MECHANISED

*Ledger correction (2026-07-17): an earlier version of §7/§8 wrongly recorded
decidability as "not mechanised". It **is** mechanised — as a full, terminating,
kernel-honest decision procedure — via the **repaired** calculus `G4iLL″`
(`G4h`/`G4c`), not the naive Iemhoff `G4iLL` (`G4`). The naive calculus is
incomplete for PLL (§7.2 below); that incompleteness is exactly what *motivated*
the repair, and the repair carries the decidability.*

### 7.1 The decision procedure (via `G4iLL″` = `G4c`)

| result | Lean name | location | axioms |
|---|---|---|---|
| Repaired calculus proves exactly PLL (proof-theoretic half of Thm 2.8): `G4c Γ φ ↔ Nonempty (Tm Γ φ)` | `G4c.equiv_tm` | [`PLLG4HComp.lean:115`](../LaxLogic/PLLG4HComp.lean) | clean |
| …and `↔ Nonempty (LaxND Γ C)` | `G4c.g4c_iff_nd` (via `equiv_nd`) | [`PLLG4HComp.lean`](../LaxLogic/PLLG4HComp.lean) | clean |
| Cut admissible / completeness of `G4c` | `G4c.cut`, `G4c.completeness` | [`PLLG4HComp.lean`](../LaxLogic/PLLG4HComp.lean) | clean |
| Loop-checked, fuel-bounded backward search decides `G4c` | `G4c_iff_search` | [`PLLG4Dec.lean:556`](../LaxLogic/PLLG4Dec.lean) | clean |
| search success ⟹ derivation | `search_sound` | [`PLLG4Dec.lean:121`](../LaxLogic/PLLG4Dec.lean) | clean |
| minimal-height derivation ⟹ search success | `search_complete` | [`PLLG4Dec.lean:228`](../LaxLogic/PLLG4Dec.lean) | clean |
| **`G4c` is decidable** | `decidableG4c` (`Decidable (G4c Γ C)`) | [`PLLG4Dec.lean:589`](../LaxLogic/PLLG4Dec.lean) | clean |
| **PLL provability is decidable** (F&M Thm 2.8): `Decidable (Nonempty (Tm Γ φ))` | `decidablePLL` | [`PLLG4Dec.lean:596`](../LaxLogic/PLLG4Dec.lean) | clean |
| Pigeonhole height bound (bonus): derivable ⟹ height ≤ `decideFuel` | `height_bound` | [`PLLG4Dec.lean`](../LaxLogic/PLLG4Dec.lean) | clean |

It is a **full** decision procedure (total `Decidable`, terminates on every
input by the fuel bound + finite gated space + visited-set loop-check), and it is
**kernel-honest**: `#eval decide (Nonempty (Tm [p] p.somehow))` and
`#eval decide (G4c …)` run in `PLLDemos.lean` under `#guard_msgs`, **no
`native_decide`**. `decide`/`#eval` on `decidablePLL` reduce, through
`equiv_tm` and `G4c_iff_search`, to the executable `search`; the loop-check
(visited sequents keyed by `toFinset`) is the efficiency device (no re-search),
and `decideFuel` is computed arithmetically (the powerset is never built).

### 7.1a Proof-term emission — fuel-free search (added 2026-07-17)

The verified decider above is a *theorem*, not a practical tool: `decideFuel`
is exponential (it exists only to make the completeness induction go through),
and running `search` to it times out even on the gap sequent.  The practical
searcher lives in [`PLLG4Term.lean`](../LaxLogic/PLLG4Term.lean) and returns
the **derivation itself**:

| result | Lean name | location | axioms |
|---|---|---|---|
| `Type`-valued proof terms for `G4iLL″` (list contexts, membership `Prop`s, `Tm`-style) | `G4cTm` | [`PLLG4Term.lean`](../LaxLogic/PLLG4Term.lean) | — (a datatype) |
| Fuel-free backward searcher emitting terms (untrusted `partial`; loop-checked by canonical list keys — no `decideFuel`, no `enum`) | `prove` / `G4cTm.find` | [`PLLG4Term.lean`](../LaxLogic/PLLG4Term.lean) | — (a program) |
| Every term projects to a `G4s` derivation | `G4cTm.sound` | [`PLLG4Term.lean`](../LaxLogic/PLLG4Term.lean) | clean-classical |
| A term certifies `G4c`, hence PLL, provability | `G4cTm.toG4c`, `G4cTm.toTm` | [`PLLG4Term.lean`](../LaxLogic/PLLG4Term.lean) | clean-classical |
| Every `G4c`-derivable sequent has a term | `G4cTm.ofG4c` | [`PLLG4Term.lean`](../LaxLogic/PLLG4Term.lean) | clean-classical |
| `Nonempty (G4cTm Γ C) ↔ Nonempty (Tm Γ C)` | `G4cTm.equiv_tm` | [`PLLG4Term.lean`](../LaxLogic/PLLG4Term.lean) | clean-classical |

Trust is factored by the type discipline: the searcher is untrusted code, but
anything it emits inhabits `G4cTm Γ C`, which the kernel checks — *if we can
build a term, Lean can check it*.  The gap sequent
`◯((◯p → r) → ◯p), ◯p → r ⊢ r`, on which running the verified decider timed
out beyond 6.5 minutes, is solved in milliseconds with its derivation tree
emitted (`#eval` smoke tests in the file).

### 7.1b The derivability tactic `pll_g4c` — certificate splicing (added 2026-07-17)

[`PLLRun.lean`](../LaxLogic/PLLRun.lean) packages the searcher as a tactic.
`pll_g4c` runs `G4cTm.find` at *elaboration time* as untrusted code, quotes the
found derivation back into surface syntax (membership side conditions as
explicit `List.Mem` constructor chains — no decision procedure, no axioms), and
the kernel checks the spliced `G4cTm` certificate, transported to the goal by
the §7.1/§7.1a equivalences.  It closes `Nonempty (Tm Γ C)`,
`Nonempty (LaxND Γ C)`, `SC Γ C`, `G4c Γ C`, `G4cTm Γ C` and
`Nonempty (G4cTm Γ C)` for concrete sequents.

- **Complete** (`G4c.equiv_tm`): a search failure *refutes* derivability — an
  underivable specimen (`◯p ⊢ p`) is pinned as an expected error under
  `#guard_msgs`.
- **No `native_decide`**: the trust base of a `pll_g4c` proof is exactly that
  of the transport lemmas — clean-classical for `Tm`/`LaxND`/`SC`/`G4c` goals
  (pinned: `PLLND.unit_nd`), and **no axioms at all** for a bare `G4cTm`
  certificate (pinned: `PLLND.gap_certificate`, the gap-sequent derivation).

This **retires `pll_g4`** (same file, removed 2026-07-17), which ran the
*naive* `G4iLL` (§7.2 — incomplete, so its failures proved nothing) under
`native_decide` (so its successes carried a per-use compiled-evaluator axiom).

### 7.2 The naive Iemhoff `G4iLL` is incomplete (why the repair was needed)

| result | Lean name | location | axioms |
|---|---|---|---|
| The separating sequent is PLL-derivable | `PLLG4Gap.sep_SC` | [`PLLG4Gap.lean:58`](../LaxLogic/PLLG4Gap.lean) | clean |
| …but not naive-`G4iLL`-derivable | `PLLG4Gap.sep_not_G4` | [`PLLG4Gap.lean:340`](../LaxLogic/PLLG4Gap.lean) | **[p]** |
| Contraction not admissible in naive `G4iLL` | `PLLG4Gap.contraction_not_admissible` | [`PLLG4Gap.lean:378`](../LaxLogic/PLLG4Gap.lean) | **[p]** |
| Cut not admissible in naive `G4iLL` | `PLLG4Gap.cut_not_admissible` | [`PLLG4Gap.lean:396`](../LaxLogic/PLLG4Gap.lean) | **[p]** |

(`G4` = naive Iemhoff `G4iLL`, `PLLG4.lean`; `G4h`/`G4c` = repaired `G4iLL″`,
`PLLG4H.lean`. The gap results refute *only* the naive calculus.)

## 8. Open items (stated honestly)

- **Decidability (F&M Thm 2.8): DONE** (§7.1) — this line previously mis-stated it
  as open; corrected 2026-07-17. F&M's own route was via the finite model
  property; the mechanised route is the repaired terminating calculus `G4iLL″`.
  A countermodel **specification** is now proved:
  `not_provable_iff_exists_finite_countermodel` ([`PLLCountermodel.lean`](../LaxLogic/PLLCountermodel.lean),
  clean) — `⊬φ ⟺ ∃ finite constraint model refuting φ` (contrapositive of the
  finite model property). This is the guarantee any extractor must meet and the
  seed for Route B realisability completeness (`route-b-model.md` §6).
  **A computable emitter with a verified checker now exists** (added
  2026-07-17, [`PLLCountermodelEmit.lean`](../LaxLogic/PLLCountermodelEmit.lean)):
  `FinCM` (finite models as data), `forceB` (computable forcing), the
  reflection lemma `force_iff`, and the certificate theorem
  `not_provable_of_check` — **choice-free** `[propext, Quot.sound]`: any
  finite model passing the executable check refutes derivability, by
  soundness.  The emitter `CounterEmit.emit` (untrusted, checker-gated)
  builds worlds as pairs (prime `G4c`-closed theory, coherent refutation
  promises — the syntactic mirror of the filtration's `Fmset`) and emits
  guarded countermodels for `⊬ p`, `◯p ⊬ p`, `⊬ ¬◯⊥` and the
  ∨-distribution `◯(p∨q) ⊬ ◯p∨◯q` (mechanically rediscovering the split
  model), with a pinned kernel-`decide` certificate `somehow_p_not_p` (no
  `native_decide`).  Still open: *completeness of the emitter* (a proof
  that it succeeds on every underivable sequent — the constructive
  upgrade of the Zorn existence inside `completeness`), and the Route B
  step of decorating emitted worlds with evidence (§6 of
  `route-b-model.md`).
- **The uniform-interpolation probe** (`wip/onevar.lean`, `wip/absorb_base.lean`,
  `wip/g4ill_ui.lean`) is a separate research thread and carries the repo's only
  open `sorry`s (5, all listed in those files' headers). No result above depends
  on them. (`height_bound` of §7.1 is the pigeonhole ingredient that route needs.)

## 9. The belief-paper layer (2026-07-14…16)

Statement-level index for the *Belief in Lax Logic* results (Boolean collapse,
`N(B) ≃o B`, normality, introspection/omniscience, open vs closed nuclei, `◯⊥`
facts, small-algebra enumerations): [`belief-mechanisation-index.md`](belief-mechanisation-index.md).
Route B realisability results (the two evidence clauses, heredity, the local
nucleus laws, the separation triptych, the double-negation believer, and
combinatory completeness `Poly.abs_spec` **[p,Q]**):
[`wip/belief_realisability.lean`](../wip/belief_realisability.lean), statuses in [`route-b-model.md`](route-b-model.md) §8.

---
---

# Part II — the formal definitions and theorem statements

*What follows is the trusted content, verbatim from the sources (proof bodies
stripped): the definitions a reader must accept as formalising the intended
notions, interleaved with the exact statements of the audited theorems. Large
auxiliary machinery (the proof-term calculus, the G4 calculus, the constraint
lattice operations) is pointed to rather than reproduced, and said so. Read
this Part against Part I's audit column.*

## II.1 The language

```lean
inductive PLLFormula where
  | prop (constantName : String)
  | falsePLL
  | and (a b : PLLFormula)
  | or (a b : PLLFormula)
  | ifThen (antecedant consequent : PLLFormula)
  | somehow (a : PLLFormula)          -- the lax modality ◯

abbrev notPLL (F : PLLFormula) : PLLFormula := ifThen F falsePLL
abbrev truePLL := ifThen falsePLL falsePLL
```

`somehow` is `◯`; `notPLL`/`truePLL` are the defined `¬`/`⊤`.

## II.2 Natural deduction ([`PLLNDCore.lean`](../LaxLogic/PLLNDCore.lean))

Contexts are lists; the identity rule is membership-based, so weakening,
exchange and contraction are admissible (`LaxND.rename`), not structural:

```lean
inductive LaxND : List PLLFormula → PLLFormula → Type
  | iden      {Γ φ}   (h : φ ∈ Γ) : LaxND Γ φ
  | falsoElim {Γ} (φ) (p : LaxND Γ .falsePLL) : LaxND Γ φ
  | impIntro  {Γ φ ψ} (p : LaxND (φ :: Γ) ψ) : LaxND Γ (.ifThen φ ψ)
  | impElim   {Γ φ ψ} (p₁ : LaxND Γ (.ifThen φ ψ)) (p₂ : LaxND Γ φ) : LaxND Γ ψ
  | andIntro  {Γ φ ψ} (p₁ : LaxND Γ φ) (p₂ : LaxND Γ ψ) : LaxND Γ (.and φ ψ)
  | andElim1  {Γ φ ψ} (p : LaxND Γ (.and φ ψ)) : LaxND Γ φ
  | andElim2  {Γ φ ψ} (p : LaxND Γ (.and φ ψ)) : LaxND Γ ψ
  | orIntro1  {Γ φ ψ} (p : LaxND Γ φ) : LaxND Γ (.or φ ψ)
  | orIntro2  {Γ φ ψ} (p : LaxND Γ ψ) : LaxND Γ (.or φ ψ)
  | orElim    {Γ φ ψ χ} (p₀ : LaxND Γ (.or φ ψ))
      (p₁ : LaxND (φ :: Γ) χ) (p₂ : LaxND (ψ :: Γ) χ) : LaxND Γ χ
  | laxIntro  {Γ φ}   (p : LaxND Γ φ) : LaxND Γ (.somehow φ)
  | laxElim   {Γ φ ψ} (p₁ : LaxND Γ (.somehow φ))
      (p₂ : LaxND (φ :: Γ) (.somehow ψ)) : LaxND Γ (.somehow ψ)
```

The two lax rules are F&M's `◯I`/`◯E`. Provability of `φ` is
`Nonempty (LaxND [] φ)`.

For conservativity, the IPL fragment is its own judgment (same rules minus the
two lax ones — `IPLND`, [`PLLNDCore.lean:167`](../LaxLogic/PLLNDCore.lean)), and erasure removes `◯`:

```lean
def erase : PLLFormula → PLLFormula     -- ◯φ ↦ erase φ, else homomorphic
def isIPL : PLLFormula → Prop            -- no ◯ anywhere

theorem conservativity_prop {Γ φ} (p : LaxND Γ φ) :
    IPLND (Γ.map erase) (erase φ)

theorem conservativity_IPL {Γ φ} (hφ : isIPL φ) (hΓ : ∀ ψ ∈ Γ, isIPL ψ)
    (p : LaxND Γ φ) : IPLND Γ φ
```

## II.3 Sequent calculus and cut elimination ([`PLLSequent.lean`](../LaxLogic/PLLSequent.lean))

```lean
inductive SCh : Nat → List PLLFormula → PLLFormula → Prop
  | init  {n Γ a}     (h : PLLFormula.prop a ∈ Γ) : SCh n Γ (.prop a)
  | botL  {n Γ C}     (h : PLLFormula.falsePLL ∈ Γ) : SCh n Γ C
  | andR  {n Γ A B}   : SCh n Γ A → SCh n Γ B → SCh (n+1) Γ (A.and B)
  | andL  {n Γ A B C} (h : A.and B ∈ Γ) : SCh n (A :: B :: Γ) C → SCh (n+1) Γ C
  | orR1  {n Γ A B}   : SCh n Γ A → SCh (n+1) Γ (A.or B)
  | orR2  {n Γ A B}   : SCh n Γ B → SCh (n+1) Γ (A.or B)
  | orL   {n Γ A B C} (h : A.or B ∈ Γ) :
      SCh n (A :: Γ) C → SCh n (B :: Γ) C → SCh (n+1) Γ C
  | impR  {n Γ A B}   : SCh n (A :: Γ) B → SCh (n+1) Γ (A.ifThen B)
  | impL  {n Γ A B C} (h : A.ifThen B ∈ Γ) :
      SCh n Γ A → SCh n (B :: Γ) C → SCh (n+1) Γ C
  | laxR  {n Γ A}     : SCh n Γ A → SCh (n+1) Γ (A.somehow)
  | laxL  {n Γ A B}   (h : A.somehow ∈ Γ) :
      SCh n (A :: Γ) (B.somehow) → SCh (n+1) Γ (B.somehow)

def SC (Γ : List PLLFormula) (C : PLLFormula) : Prop := ∃ n, SCh n Γ C
```

Height-indexed, G3-style (principal formulas kept in the context); **no cut
rule**. The audited theorems:

```lean
theorem SC.cut {Γ A C} (h₁ : SC Γ A) (h₂ : SC (A :: Γ) C) : SC Γ C

theorem SC_to_ND : ∀ {n Γ C}, SCh n Γ C → Nonempty (LaxND Γ C)
theorem ND_to_SC : ∀ {Γ C}, LaxND Γ C → SC Γ C

/-- Cut elimination, headline form (F&M Theorem 2.6). -/
theorem cutElimination {Γ C} : Nonempty (LaxND Γ C) ↔ SC Γ C

/-- Disjunction property (F&M Lemma 2.7(i)). -/
theorem disjunction_property {A B}
    (h : Nonempty (LaxND [] (A.or B))) :
    Nonempty (LaxND [] A) ∨ Nonempty (LaxND [] B)

/-- ◯-reflection (F&M Lemma 2.7(ii)): ⊢ ◯M implies ⊢ M. -/
theorem somehow_reflection {A}
    (h : Nonempty (LaxND [] (A.somehow))) : Nonempty (LaxND [] A)
```

## II.4 Hilbert system ([`PLLAxiom.lean`](../LaxLogic/PLLAxiom.lean), [`PLLHilbert.lean`](../LaxLogic/PLLHilbert.lean))

The axiom schemes (the three `◯`-schemes displayed; the remainder are the
standard IPC schemes `K`, `S`, the `∧`/`∨` rules and ex falso —
[`PLLAxiom.lean:36–60`](../LaxLogic/PLLAxiom.lean)):

```lean
inductive PLLAxiom where
  | somehowR (M) | somehowM (M) | somehowS (M N) | somehowBind (M N)
  | impK (A B) | impS (A B C)
  | andElim1 (A B) | andElim2 (A B) | andIntro (A B)
  | orIntro1 (A B) | orIntro2 (A B) | orElim (A B C)
  | explosion (A)

def PLLAxiom.get : PLLAxiom → PLLFormula
  | somehowR M    => M ⊃ ◯M                    -- ifThen M (somehow M)
  | somehowM M    => ◯◯M ⊃ ◯M
  | somehowS M N  => (◯M ∧ ◯N) ⊃ ◯(M ∧ N)
  | ...                                        -- standard IPC schemes

inductive HdOn (Ax : PLLFormula → Prop) (Γ : List PLLFormula) : PLLFormula → Prop
  | ax  {φ} (h : Ax φ)  : HdOn Ax Γ φ
  | hyp {φ} (h : φ ∈ Γ) : HdOn Ax Γ φ
  | mp  {φ ψ} : HdOn Ax Γ (φ.ifThen ψ) → HdOn Ax Γ φ → HdOn Ax Γ ψ

def PLLAx (φ : PLLFormula) : Prop := ∃ a : PLLAxiom, φ = a.get
abbrev Hd (Γ : List PLLFormula) (φ : PLLFormula) : Prop := HdOn PLLAx Γ φ

/-- F&M Theorem 2.3: Hilbert and natural-deduction consequence coincide. -/
theorem hd_iff_ND {Γ φ} : Hd Γ φ ↔ Nonempty (LaxND Γ φ)
```

Strong extensionality (F&M Theorem 2.5; `iffPLL M N` is `(M⊃N) ∧ (N⊃M)`,
`substProp a M C` is `C[M/a]`):

```lean
theorem strong_extensionality (a : String) (M N C : PLLFormula) :
    Nonempty (LaxND [] ((iffPLL M N).ifThen
      (iffPLL (substProp a M C) (substProp a N C))))
```

## II.5 Kripke constraint semantics ([`PLLKripke.lean`](../LaxLogic/PLLKripke.lean))

```lean
structure ConstraintModel where
  W : Type
  Ri : W → W → Prop        -- intuitionistic accessibility
  Rm : W → W → Prop        -- modal (constraint) accessibility
  F : Set W                -- fallible worlds
  V : String → Set W
  refl_i : ∀ w, Ri w w
  trans_i : ∀ {w v u}, Ri w v → Ri v u → Ri w u
  refl_m : ∀ w, Rm w w
  trans_m : ∀ {w v u}, Rm w v → Rm v u → Rm w u
  sub_mi : ∀ {w v}, Rm w v → Ri w v
  hered_F : ∀ {w v}, Ri w v → w ∈ F → v ∈ F
  hered_V : ∀ {a w v}, Ri w v → w ∈ V a → v ∈ V a
  full_F : ∀ {a w}, w ∈ F → w ∈ V a

def force (C : ConstraintModel) : C.W → PLLFormula → Prop
  | w, .prop a     => w ∈ C.V a
  | w, .falsePLL   => w ∈ C.F
  | w, .and φ ψ    => C.force w φ ∧ C.force w ψ
  | w, .or φ ψ     => C.force w φ ∨ C.force w ψ
  | w, .ifThen φ ψ => ∀ v, C.Ri w v → C.force v φ → C.force v ψ
  | w, .somehow φ  => ∀ v, C.Ri w v → ∃ u, C.Rm v u ∧ C.force u φ

def Consequence (Γ : List PLLFormula) (φ : PLLFormula) : Prop :=
  ∀ (C : ConstraintModel) (w : C.W), (∀ ψ ∈ Γ, C.force w ψ) → C.force w φ

theorem soundness    {Γ φ} (p : LaxND Γ φ) : Γ ⊨- φ            -- F&M Thm 3.3
theorem completeness {Γ φ} (h : Γ ⊨- φ) : Nonempty (LaxND Γ φ)  -- F&M Thm 4.4
```

## II.6 Countermodels (F&M Fig. 3; [`PLLFrames.lean`](../LaxLogic/PLLFrames.lean))

Each is soundness against a small explicit `ConstraintModel` (the models
`modelFallible`, `modelOrSplit`, `modelNoImpDist` are defined at
[`PLLFrames.lean:60–201`](../LaxLogic/PLLFrames.lean) and are `decide`-checkable):

```lean
theorem not_provable_not_somehow_false :
    ¬ Nonempty (LaxND [] (notPLL (somehow falsePLL)))

theorem not_provable_somehow_or_dist :
    ¬ Nonempty (LaxND [] ((somehow ((prop "A").or (prop "B"))).ifThen
        ((somehow (prop "A")).or (somehow (prop "B")))))

theorem not_provable_imp_somehow_dist :
    ¬ Nonempty (LaxND [] (((somehow (prop "A")).ifThen (somehow (prop "B"))).ifThen
        (somehow ((prop "A").ifThen (prop "B")))))
```

## II.7 Strong normalisation ([`PLLTopTop.lean`](../LaxLogic/PLLTopTop.lean))

The proof-term calculus `Tm`, the full one-step reduction `Step` (β for every
connective + `let`-assoc), strong normalisation `SNt`, and normal forms `Nf`
are defined in [`PLLTerms.lean`](../LaxLogic/PLLTerms.lean) / [`PLLProof.lean`](../LaxLogic/PLLProof.lean) / [`PLLNormal.lean`](../LaxLogic/PLLNormal.lean) (not
reproduced — a full calculus). The audited statements:

```lean
theorem strong_normalisation {Γ φ} (t : Tm Γ φ) : SNt t

def Tm.normalize {Γ φ} (t : Tm Γ φ) : Tm Γ φ          -- total normaliser
theorem Tm.normalize_spec {Γ φ} (t : Tm Γ φ) :
    Steps t t.normalize ∧ Nf t.normalize
```

## II.8 Craig interpolation ([`PLLCraig.lean`](../LaxLogic/PLLCraig.lean))

```lean
theorem craig_interpolation {Γ₁ Γ₂ C} (h : SC (Γ₁ ++ Γ₂) C) :
    ∃ I : PLLFormula,
      SC Γ₁ I ∧ SC (I :: Γ₂) C ∧
      I.atoms ⊆ atomsList Γ₁ ∩ (atomsList Γ₂ ∪ C.atoms)

theorem craig_implication {A B} (h : SC [] (A.ifThen B)) :
    ∃ I : PLLFormula,
      SC [] (A.ifThen I) ∧ SC [] (I.ifThen B) ∧ I.atoms ⊆ A.atoms ∩ B.atoms
```

## II.9 Kleene–Brouwer well-foundedness ([`KleeneBrouwer.lean`](../LaxLogic/KleeneBrouwer.lean))

```lean
def DevLeft (v u : List α) : Prop :=      -- v branches lt-left of u
  ∃ (w : List α) (a b : α) (v' u' : List α),
    v = w ++ a :: v' ∧ u = w ++ b :: u' ∧ lt a b

def KB (s t : List α) : Prop :=           -- Kleene–Brouwer relation on T
  T s ∧ T t ∧ ((t <+: s ∧ s ≠ t) ∨ DevLeft lt s t)

def Child (s t : List α) : Prop := T s ∧ ∃ a, s = t ++ [a]

theorem wellFounded_kb
    (hlt : WellFounded lt)
    (hpc : ∀ ⦃s t⦄, T s → t <+: s → T t)          -- T prefix-closed
    (hacc : ∀ l, T l → Acc (Child T) l) :          -- tree inductively WF
    WellFounded (KB lt T)

theorem wellFounded_kb'
    (hlt : WellFounded lt) (hpc : …) (hacc : WellFounded (Child T)) :
    WellFounded (KB lt T)
```

Audit: **no axioms at all** (in-file guard).

## II.10 The Curry-paper results ([`LaxLogic/PLLCtxCompleteness.lean`](../LaxLogic/PLLCtxCompleteness.lean), [`LaxLogic/PLLLaxInfinite.lean`](../LaxLogic/PLLLaxInfinite.lean))

Standard constraints and the expansion `φ^C`:

```lean
def basic (K L x : PLLFormula) : PLLFormula := K.ifThen (x.or L)  -- [K,L]x = K ⊃ (x ∨ L)

abbrev StdCtx := List (PLLFormula × PLLFormula)   -- acts as ⋀ᵢ (Kᵢ ⊃ (x ∨ Lᵢ))
def applyC : StdCtx → PLLFormula → PLLFormula      -- C[x], truePLL for []

def subC (C : StdCtx) : PLLFormula → PLLFormula    -- φ^C: homomorphic, and
  | .somehow φ => applyC C (subC C φ)              --   (◯φ)^C = C[φ^C]
```

```lean
/-- Theorem 6 (context completeness): PLL ⊢ φ  iff  IPL ⊢ φ^C for every C. -/
theorem thm6 {φ} :
    Nonempty (LaxND [] φ) ↔ ∀ C : StdCtx, Nonempty (LaxND [] (subC C φ))

/-- Corollary 10: no finite set of standard constraints is complete. -/
theorem corollary10 (𝔻 : Finset StdCtx) :
    ∃ φ, (∀ C ∈ 𝔻, Nonempty (LaxND [] (subC C φ))) ∧ ¬ Nonempty (LaxND [] φ)

/-- Theorem 2: the constraint algebra is Boolean (all sixteen laws, over the
equivalence `Cequiv`; `Cmeet/Cjoin/Cbar/Ctop/Cbot` defined at :1016–1474). -/
theorem thm2_boolean_algebra :
    (∀ C D, Cequiv (Cmeet C D) (Cmeet D C)) ∧ … ∧
    (∀ C, Cequiv (Cmeet C (Cbar C)) Cbot) ∧
    (∀ C, Cequiv (Cjoin C (Cbar C)) Ctop)
-- bundled as a Mathlib instance:  BooleanAlgebra CQuot   (CQuot = StdCtx/≈)
```

The infinite closed fragment:

```lean
def Le (a b : PLLFormula) : Prop :=       -- Lindenbaum preorder, semantically
  ∀ (M : ConstraintModel) (w : M.W), M.force w a → M.force w b
  -- (coincides with derivability: le_iff_nonempty)

def LaxEquiv (a b : PLLFormula) : Prop := Le a b ∧ Le b a
def Closed := {φ : PLLFormula // atomFree φ = true}
instance closedSetoid : Setoid Closed where r x y := LaxEquiv x.1 y.1 …

/-- The closed lax fragment RN(◯,{}) is infinite. -/
theorem closed_lax_infinite : Infinite (Quotient closedSetoid)
```

## II.11 Decidability — F&M Theorem 2.8 ([`PLLG4H.lean`](../LaxLogic/PLLG4H.lean), [`PLLG4Dec.lean`](../LaxLogic/PLLG4Dec.lean))

The repaired calculus `G4iLL″` is `G4h` (height-indexed) / `G4c`; the decider is
the loop-checked backward `search` over the set calculus (both large, not
reproduced — see `PLLG4H.lean`, `PLLG4Dec.lean`). The bridge and the two
`Decidable` instances:

```lean
def G4c (Γ : List PLLFormula) (C : PLLFormula) : Prop := ∃ n, G4h n Γ C

/-- G4iLL″ proves exactly the PLL sequents (proof-theoretic half of Thm 2.8). -/
theorem G4c.equiv_tm {Γ φ} : G4c Γ φ ↔ Nonempty (Tm Γ φ)

/-- The loop-checked, fuel-bounded search decides G4c. -/
theorem G4c_iff_search {Γ C} :
    G4c Γ C ↔
    search (listWeight (C :: Γ)) (listAtoms (C :: Γ)) (decideFuel Γ C) ∅ Γ C = true

instance decidableG4c (Γ C) : Decidable (G4c Γ C) :=
  decidable_of_iff _ G4c_iff_search.symm

/-- F&M Theorem 2.8: PLL provability (term-calculus inhabitation) is decidable. -/
instance decidablePLL (Γ φ) : Decidable (Nonempty (Tm Γ φ)) :=
  decidable_of_iff _ G4c.equiv_tm
```

A full, terminating, kernel-honest decider (`#eval decide (Nonempty (Tm [p] p.somehow))`
runs under `#guard_msgs` in `PLLDemos.lean`; no `native_decide`).

## II.12 The naive-G4iLL incompleteness gap ([`PLLG4Gap.lean`](../LaxLogic/PLLG4Gap.lean))

The *naive* Iemhoff calculus (`G4`, contraction-free) is defined in
[`PLLG4.lean`](../LaxLogic/PLLG4.lean) (not reproduced); these results show it is
incomplete for PLL — the motivation for the `G4iLL″` repair above:

```lean
def Fa : PLLFormula := ((prop "p").somehow).ifThen (prop "r")   -- F' = ◯p ⊃ r
def Ga : PLLFormula := Fa.ifThen (prop "p").somehow             -- G' = F' ⊃ ◯p

theorem sep_SC     : SC [Ga.somehow, Fa] (prop "r")             -- PLL derives it
theorem sep_not_G4 : ¬ G4 [Ga.somehow, Fa] (prop "r")           -- G4iLL cannot

theorem contraction_not_admissible :
    G4 [Ga.somehow, Fa, Fa] (prop "r") ∧ ¬ G4 [Ga.somehow, Fa] (prop "r")

theorem cut_not_admissible :
    G4 [Ga.somehow, Fa] ((prop "p").somehow) ∧
    G4 [(prop "p").somehow, Ga.somehow, Fa] (prop "r") ∧
    ¬ G4 [Ga.somehow, Fa] (prop "r")
```

*(End of Part II. The belief-paper layer's statements are indexed separately in
[`belief-mechanisation-index.md`](belief-mechanisation-index.md) and [`wip/belief_realisability.lean`](../wip/belief_realisability.lean).)*
