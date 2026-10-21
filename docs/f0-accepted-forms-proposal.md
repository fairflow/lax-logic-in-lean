# F0 accepted forms and keys: a proposal (spike S2, 2026-10-21)

**Status: OPEN.**  This is a statements document for gate G3 of
`METHOD-F0.md` ("accepted forms and keys": decided by Matthew before any
tool that maps formulas to classes).  It proposes; it binds nothing until
Matthew approves, amends or strikes each part.  Every Lean item below is a
statement, not a proof: those marked *obligation* are for gate G2.

Context: `docs/f0-reimplementation-plan.md` (branch `method-f0`), principles
P1, P3, P7 and P9, and the S1 audit `docs/rndb-audit-2026-10-21.md`.
Branch `f0-forms-s2`, from `origin/main` at `1e1abe6` plus the S1
exporter commit.  Nothing under `RNDB/` changes.  The measurements in §6 are on the OLD data, through a new
read-only program, `tools/F0S2Measure.lean` (`lake build f0s2`).

**Notation.**  Library notation: `↠` for implication, `¬A` for `A ↠ ⊥`,
`⊤` for `⊥ ↠ ⊥`.  `∧` binds tighter than `∨`, and `∨` tighter than `↠`.
`[φ] ⊢ ψ` is `Deriv [φ] ψ`; `[φ] ⊬ ψ` is its negation.  ρ-names are those
of `LaxLogic/RN/Rho.lean`.

**Decided only by the public tools.**  The deciders used are the G4c engine
and the FinCM battery and emitter of `LaxLogic/PLL/Search/Search.lean`.
Nothing private is used or referred to.

## 1 · Fragment first: the ◯-free closed fragment (smoke test)

The ◯-free variable-free formulas are built from `⊥` with `∧`, `∨`, `↠`.
Each is interderivable with `⊥` or with `⊤`, according to its value in
the two-element Boolean algebra.  This is the end-to-end smoke test for
every layer below (plan, P9).

**Statement (obligation, G2).**  Let `⟦φ⟧ ∈ {0, 1}` be the Boolean value.
For every `φ` with `atomFree φ = true` and `isIPL φ` (no `◯`):

    canonFix φ = ⊥   if ⟦φ⟧ = 0,          canonFix φ = ⊤   if ⟦φ⟧ = 1,

and hence, for two such formulas,

    [φ] ⊢ ψ   ⟺   ⟦φ⟧ ≤ ⟦ψ⟧.

`canon`'s constant folding (`mkAnd`, `mkOr`, `mkImp`, `consAnd`, `consOr`)
covers every case by induction on `φ`.  So on this fragment the identity
key of §3 *is* the class key, and `ask` never returns `unknown`:

* `[φ] ⊢ ψ` follows from equal keys, or from `⊥` least and `⊤` greatest;
* `[φ] ⊬ ψ` holds exactly when `⟦φ⟧ = 1` and `⟦ψ⟧ = 0`, and follows from
  the one stored row `[⊤] ⊬ ⊥` by the propagation rule of §4.

Any `unknown` on this fragment is a defect.

**Accepted forms of the fragment:** `ρ0 = ⊥` and `ρ1 = ⊤`.

## 2 · Accepted forms (part a)

### 2.1 Names

    namespace F0

    /-- The name of an accepted form.  Issued once; never reused; never
        re-pointed to a different formula. -/
    inductive FormName where
      | rho  (i : Nat)   -- the finite named list, by issue number
      | rung (k : Nat)   -- the closed Rieger–Nishimura ladder, by rung
      deriving DecidableEq, Repr

    /-- The finite list, BY VALUE: a frozen literal, append-only.  Version 1
        is the 22 formulas of `LaxLogic/RN/Rho.lean`, under their indices. -/
    def rhoList : List PLLFormula := [ρ0, ρ1, …, ρ21]

    /-- The family.  `sLad` is the one-variable Rieger–Nishimura ladder
          s₀ = p,   s₁ = p ∨ ¬p,   sₖ₊₂ = sₖ₊₁ ∨ (sₖ₊₁ ↠ sₖ)
        (`LaxLogic/PLL/Semantics/LaxInfinite.lean`), and `subOb` substitutes
        `◯⊥` for every atom. -/
    def rung (k : Nat) : PLLFormula := LaxInfinite.subOb (LaxInfinite.sLad k)

    def FormName.formula : FormName → Option PLLFormula
      | .rho i  => rhoList[i]?
      | .rung k => some (rung k)

The first rungs, displayed:

    rung 0 = ◯⊥                                  (= ρ2, syntactically)
    rung 1 = ◯⊥ ∨ ¬◯⊥                            (= ρ4, syntactically)
    rung 2 = (◯⊥ ∨ ¬◯⊥) ∨ ((◯⊥ ∨ ¬◯⊥) ↠ ◯⊥)
    rung 3 = rung 2 ∨ (rung 2 ↠ rung 1)

### 2.2 Invariants

**(A1) Closed.**  Every accepted form `φ` satisfies
`LaxInfinite.atomFree φ = true`; for the family this is
`subOb_atomFree`.

**(A2) Stable.**  `FormName.formula n` never changes once it is defined.
`rhoList` grows only by appending, and CI compares it with the previous
version.  The ρ- and q-numberings become alias tables into `FormName`;
they are not names in their own right:

* ρi ↦ `.rho i`;
* the 14 q-representatives with a ρ twin ↦ that twin
  (q5 ↦ ρ7, q6 ↦ ρ5, q7 ↦ ρ6, q8 ↦ ρ11, q10 ↦ ρ8, q11 ↦ ρ10, q14 ↦ ρ12,
  q15 ↦ ρ14, and qk ↦ ρk for k ≤ 4 and k = 9);
* q12 and q13 have no ρ twin.  §6.4 places q13 outside R (computed)
  and reduces q12 to one cell.  Whether either becomes an accepted form
  is Q1, under A5.

**(A3) Distinct, with certificates.**  Two names that are not declared
aliases denote different classes.  For each such pair the store holds a
certified `⊬` in at least one direction.  A new name is accepted only
together with its separation from every earlier name.  For the family,
the statement is

    ∀ k,   [rung k] ⊢ rung (k+1)   and   [rung (k+1)] ⊬ rung k.

`LaxInfinite.lean` proves this for its own ladder:

* `disjLadder_fwd` gives the forward entailments;
* `exists_escaping_rungs` (with `rhoLad`, `rn_disj_eq` and
  `subOb_disjLadder`) gives the strictness.

Restating it for `rung` is an obligation (G2).  It makes the rungs
pairwise distinct classes, and it is what proves F0 infinite
(`closed_lax_infinite`).

**(A4) Aliases.**  When two names denote one class, an alias row records
`(n, m, certificate of ⊣⊢)`, and the earlier-issued name is the primary
one.  Known now:

* rung 0 = ρ2 and rung 1 = ρ4 (syntactic);
* rung 2 ⊣⊢ ρ6 and rung 3 ⊣⊢ ρ10 (computed in §6.4, with the IPC
  reasons; obligations for G2).

**(A5) Who adds a name.**  Only Matthew, at G3.  A tool may propose a
candidate class with its separations; it may not name one.

## 3 · Keys (part b)

### 3.1 The identity key

    /-- `canon` iterated to a fixpoint, with fuel. -/
    def canonIter : Nat → PLLFormula → PLLFormula
      | 0,     φ => φ
      | n + 1, φ => if Rewrite.canon φ = φ then φ else canonIter n (Rewrite.canon φ)

    def canonFix (φ : PLLFormula) : PLLFormula := canonIter (fuelFor φ) φ

    def key (φ : PLLFormula) : String := Rewrite.keyF (canonFix φ)

Statements:

    canonFix_interd :  ∀ φ,  Interd φ (canonFix φ)
        -- every fuel; from Rewrite.canon_interd by induction on the fuel

    canonFix_fixed :   ∀ φ,  Rewrite.canon (canonFix φ) = canonFix φ
        -- obligation: needs a fuel bound `fuelFor`

    keyF_injective :   ∀ φ ψ,  Rewrite.keyF φ = Rewrite.keyF ψ → φ = ψ
        -- obligation: keyF is a prefix code, so this should be routine

    key_sound :        ∀ φ ψ,  key φ = key ψ → Interd φ ψ
        -- from the three above

**Invariants.**

* **(K1) Soundness:** `key_sound`.
* **(K2) Idempotence:** `key (canonFix φ) = key φ`.  One pass of `canon`
  is not enough (S1, finding 10):

      ◯(◯⊥ ∨ ¬◯⊥)  ↦canon  ◯(¬◯⊥ ∨ ⊥)  ↦canon  ◯¬◯⊥

* **(K3) Versioned:** a change to `canon` changes keys.  So `canon`
  carries a version, every stored key records the version that made it,
  and a change of version is a migration with a parity report, never a
  silent rebuild.
* **(K4) Display is not identity:** humans read `pp`; machines compare
  `key`.

**Choice.**  `Rewrite.canon_interd` currently depends on
`Classical.choice` (pinned in `Rewrite/Canon.lean`).  Computing the key
does not use it.  Using `canonFix_interd` as a certificate does, until a
choice-free proof replaces it.  The plan (P6) wants a choice-free
library, so this needs a decision (§7, Q4).

### 3.2 The class key

    /-- The class of φ, with a certificate, or unknown.  Computed; never
        stored as an authority. -/
    def cls (φ : PLLFormula) : Option (FormName × InterdCert φ)

It is computed by the strategies of plan P8, in this order:

1. **key:** `key φ` equals the key of an accepted form or of an alias row;
2. **union-find:** union-find over stored `⊢`-both-ways pairs reaches a
   form;
3. **order:** order facts place `φ` between two classes that coincide;
4. **decider:** bounded search on `[φ] ⊢? form` and `[form] ⊢? φ`.

**Invariants.**

* **(C1)** `cls φ = some (n, c)` only with a certificate `c` for
  `φ ⊣⊢ form n`.
* **(C2)** `none` is never read as "a new class".  "φ lies in no class of
  version v" is an aggregate claim (§5), and it needs a certified
  separation from every form of v.
* **(C3)** `cls` is not stored.  A membership found by the decider is
  stored as its two base `⊢` facts (§4), and `cls` recomputes from them.

## 4 · Storing the order (part c)

    inductive Fact where
      | le  (φ ψ : PLLFormula)    -- [φ] ⊢ ψ
      | nle (φ ψ : PLLFormula)    -- [φ] ⊬ ψ

    def Fact.Holds : Fact → Prop
      | .le φ ψ  => Deriv [φ] ψ
      | .nle φ ψ => ¬ Deriv [φ] ψ

A row is `(Fact, certificate)`.  It is indexed by `(key φ, key ψ)` and
carries no scope (§5).  The certificate formats are the plan's decision
D3, not part of G3.

**Derived, never stored:**

* `Interd φ ψ := le φ ψ ∧ le ψ φ`;
* transitive consequences;
* classes;
* covers and the Hasse diagram;
* propagated non-entailments;
* aggregate claims.

The old `symm`/`trans` entries become queries.  The rules a query may
use, each sound and each turning certificates into a certificate:

       [φ] ⊢ ψ     [ψ] ⊢ χ                key φ = key ψ
      ─────────────────────── cut        ─────────────── key
             [φ] ⊢ χ                        [φ] ⊢ ψ

      ─────────── ⊥            ─────────── ⊤
        [⊥] ⊢ φ                  [φ] ⊢ ⊤

       [φ'] ⊬ ψ'     [φ'] ⊢ φ     [ψ] ⊢ ψ'
      ───────────────────────────────────── propagation
                   [φ] ⊬ ψ

In propagation, the countermodel of the first premise is the
countermodel of the conclusion, re-checked by `FinCM.checkB` against
`(φ, ψ)`.

**Invariants.**

* **(O1) Consistent:** no pair has both a derivable `⊢` and a derivable
  `⊬`.  CI checks this with the S1 contradiction test, over the closure
  under the rules above, not only over the rows.
* **(O2) No derived row:** a row the rules already derive from other
  rows is reported as redundant (a view), not deleted.  Redundancy is
  allowed but counted.
* **(O3) Every row checked:** every row's certificate is re-checked in
  CI.

## 5 · Scope (part d)

A base fact `[φ] ⊬ ψ` is true or false whatever the representative list
is, so **base facts carry no scope** (plan P7, decision D4).  Scope
belongs only to aggregate claims, and it is given by value:

    /-- A frozen version of the accepted forms, by value. -/
    structure FormsVersion where
      version : Nat                          -- strictly increasing
      forms   : List (FormName × PLLFormula) -- the forms at that version
      digest  : String                       -- hash of the printed keys, for citation

    /-- The one kind of statement that needs a scope. -/
    def OutsideAll (v : FormsVersion) (φ : PLLFormula) : Prop :=
      ∀ p ∈ v.forms, ¬ Interd φ p.2

**Invariants.**

* **(S1)** An aggregate claim names a `FormsVersion` value, or its
  digest, never a definition that grows (today's `rhoScope` and
  `RNReps.reps`).
* **(S2)** Versions only grow.  `OutsideAll v φ` stays true for `v`; for
  `v + 1` it is a new question, asked and not rewritten.
* **(S3)** A table entry `∉R` means `OutsideAll v_R φ`, with `v_R`
  stated.

The old escape decomposition becomes 16 base `⊬` facts per compound plus
one aggregate `OutsideAll v_q φ`, where `v_q` is the frozen q-list.

## 6 · Measurements on the old data

The question: on the existing facts, how much does each layer of the
proposal settle by itself?  The program is `tools/F0S2Measure.lean`
(`lake build f0s2`, then the binary under `gtimeout`).  It reads
`RNDB.allEntries` (read-only) into an in-memory store keyed by the
identity key of §3.1, and asks each cell `[φ] ⊢? ψ` of a designed test set
in the order of plan P8.  The tier that settles a cell is the first that
answers:

* **K, key lookup:** `key φ = key ψ`, or a stored fact on the key pair;
* **U, lookup plus union-find over `interd`:** the two keys have one
  union-find root, or a stored `⊬` joins their two classes;
* **O, order facts:** the rules of §4 over the stored facts (cut along
  `≤`, `⊥` least, `⊤` greatest, and propagation of `⊬`);
* **D, the public decider:** `PLLND.Search.verdictWhy`, the G4c engine
  with the FinCM battery and emitter, at node budget 200,000 and emit cap
  12 (limit 30 s).  On a node-budget cutoff it is asked again at
  2,000,000 nodes (**D2**, limit 120 s); when only the emit cap stopped it,
  at emit cap 16 (**D3**, limit 120 s).

A `⊢` from the decider carries a G4c proof term and a `⊬` a FinCM model
accepted by `FinCM.checkB`.  Neither is re-checked by the kernel in this
spike, so every verdict below that comes from tier D is a *computed*
verdict, not a PROVED one.  Tiers K and U read kernel-checked RNDB
entries; tier O composes them by the rules of §4.  The tier counts are
cumulative in the order K, U, O, D.

### 6.1 The test set (designed; no sweeps)

* **T0, the fragment-first smoke test** (24 cells).  Six closed ◯-free
  formulas, each asked against `⊥` and `⊤` in both directions:

      ⊥,   ⊤,   ¬⊤,   ¬¬⊤,   (⊥ ∨ ⊤) ∧ (⊤ ↠ ⊤),   (⊤ ∧ ⊥) ∨ (¬⊤ ∧ ⊤)

* **T1, the ρ-matrix** (462 cells): `[ρi] ⊢? ρj` for all `i ≠ j`.
* **T2, formulas outside the catalogue or in it by accident** (440
  cells): ten formulas, each against all 22 ρ in both directions.

  | label | formula | why it is in the set |
  |---|---|---|
  | q12 | `◯(¬◯⊥ ∨ ¬¬◯⊥)` | a q-representative with no ρ twin |
  | q13 | `◯(◯¬◯⊥ ↠ ◯⊥ ∨ ¬◯⊥)` | the other one |
  | q5 ∨ q8 | `◯¬◯⊥ ∨ (◯¬◯⊥ ↠ ◯⊥ ∨ ¬◯⊥)` | escape compound; `canonFix` gives the key of ρ15 (control) |
  | q10 ↠ q4 | `(¬¬◯⊥ ↠ ◯⊥) ↠ ◯⊥ ∨ ¬◯⊥` | escape compound; it *is* ρ13 (control) |
  | q10 ∧ q13 | `(¬¬◯⊥ ↠ ◯⊥) ∧ ◯(◯¬◯⊥ ↠ ◯⊥ ∨ ¬◯⊥)` | escape compound |
  | ◯q11 | `◯(¬¬◯⊥ ∨ (¬¬◯⊥ ↠ ◯⊥))` | escape compound |
  | q10 ↠ q7 | `(¬¬◯⊥ ↠ ◯⊥) ↠ ¬◯⊥ ∨ ¬¬◯⊥` | escape compound |
  | q8 ↠ q4 | `(◯¬◯⊥ ↠ ◯⊥ ∨ ¬◯⊥) ↠ ◯⊥ ∨ ¬◯⊥` | escape compound |
  | rung 2 | `(◯⊥ ∨ ¬◯⊥) ∨ (◯⊥ ∨ ¬◯⊥ ↠ ◯⊥)` | the family of §2 |
  | rung 3 | `rung 2 ∨ (rung 2 ↠ ◯⊥ ∨ ¬◯⊥)` | the family of §2 |

  Each escape compound has 16 `esc` entries in RNDB (one `⊬` per
  q-representative), checked against the export.

Three stores are used:

* **old:** the 1,874 RNDB entries as they are: 345 distinct keys, 1,120
  class-level `⊬` facts, no `le` facts (an `interd` entry counts as `≤`
  both ways).  `canonFix` needs at most 2 changing rounds on any RNDB
  formula.
* **banked:** the old store plus the decider's T1 verdicts stored as base
  facts, which is the "store the order" design of §4.
* **closure:** every verdict of the run (T1 and T2) taken as a base fact
  and closed under the rules of §4.  This is the design in which every
  decider answer is banked as it arrives.  It is computed by
  `scripts/f0_s2_summary.py` from the measured verdicts, not by the Lean
  store.

### 6.2 What settles a cell

Cumulative cells settled, tier by tier (run of 2026-10-21, 16:34 to
17:05 BST, about 30 minutes, almost all of it in the decider).

| set | store | K | K+U | K+U+O | + decider | unknown | store tiers, median per cell |
|---|---|---|---|---|---|---|---|
| T0 (24) | old | 18 (75.0%) | 18 (75.0%) | **24 (100%)** | not called | 0 | 0.2 µs |
| T1 (462) | old | 304 (65.8%) | 304 (65.8%) | 345 (74.7%) | **462 (100%)** | 0 | 3.0 µs |
| T2 (440) | old | 134 (30.5%) | 134 (30.5%) | 158 (35.9%) | 380 (86.4%) | 60 | 17.5 µs |
| T2 (440) | banked | 156 (35.5%) | 156 (35.5%) | 210 (47.7%) | not called | 230 | 4.8 µs |
| T2 (440) | banked + D | 156 (35.5%) | 156 (35.5%) | 210 (47.7%) | 392 (89.1%) | 48 | 5.8 µs |
| T2 (440) | closure | | | | 424 (96.4%) | 16 | (Python) |

The decider, in detail:

* **T1:** 117 calls, every one a `⊢` answered by a G4c proof term;
  1.85 s in all, median 14 ms, maximum 200 ms.  All 304 `⊬` cells of the
  ρ-matrix were found by key lookup (RNDB banks them), and 41 `⊢` cells
  by `⊥` least and `⊤` greatest.  RNDB banks no `⊢` cell, so the other
  117 needed the decider.
* **T2, old store:** 260 fresh calls (22 more cells reused a memoised
  answer for the same key pair), 1,773 s in all:

  | outcome | cells | time |
  |---|---|---|
  | settled (97 `⊢`, 103 `⊬`) | 200 | 3.3 s (median 14 ms, 90th percentile 15 ms, max 241 ms) |
  | all stages ran and missed (no proof, no countermodel within the frames) | 28 | 177 s (median 1.8 s, max 27.6 s) |
  | stopped by a time limit (25 at the 30 s first stage, 7 at the 120 s D3 stage) | 32 | 1,593 s |

  The raised budgets D2 and D3 settled no cell.
* **banked + decider:** the decider answers are the memoised ones of the
  old run; banking the T1 order settles 12 of the old run's 60 unknown
  cells by propagation, without the decider.
* **Verdict clashes:** none between the runs, and none in the closure
  (invariant O1 holds on the measured verdicts).

The smoke test passes: every T0 cell settles without the decider, and
`canonFix` sends each of the six formulas to `⊥` or `⊤` according to its
Boolean value.

### 6.3 The ρ-order as base facts

The decided ρ-matrix has 158 `⊢` and 304 `⊬` cells.  It is a partial
order on the 22 classes (no two ρ interderivable, `⊢` transitive), and it
is generated by **37 covers and 11 `⊬` facts**: the reflexive-transitive
closure of the covers gives all 158 `⊢` cells, and the propagation rule of
§4 applied to the 11 facts gives all 304 `⊬` cells.

The covers (`ρi < ρj`: `[ρi] ⊢ ρj`, and nothing strictly between):

    ρ0 < ρ2, ρ3        ρ2 < ρ4, ρ5        ρ3 < ρ4
    ρ4 < ρ6, ρ7, ρ14   ρ5 < ρ6            ρ6 < ρ9, ρ13, ρ17
    ρ7 < ρ9, ρ16, ρ19  ρ8 < ρ10           ρ9 < ρ12, ρ18, ρ20
    ρ11 < ρ15          ρ12 < ρ21          ρ13 < ρ11, ρ12
    ρ14 < ρ16, ρ17     ρ16 < ρ8, ρ18      ρ17 < ρ11, ρ18
    ρ18 < ρ10, ρ15     ρ19 < ρ8, ρ20      ρ20 < ρ21
    ρ10, ρ15, ρ21 < ρ1

The `⊬` basis:

    [ρ2] ⊬ ρ3     [ρ3] ⊬ ρ5     [ρ5] ⊬ ρ8     [ρ7] ⊬ ρ11
    [ρ12] ⊬ ρ15   [ρ13] ⊬ ρ10   [ρ13] ⊬ ρ20   [ρ14] ⊬ ρ21
    [ρ19] ⊬ ρ12   [ρ19] ⊬ ρ15   [ρ20] ⊬ ρ10

The coatoms are ρ10, ρ15 and ρ21.  RNDB states this order through a
banked row for each of the 304 `⊬` cells, and none for a `⊢` cell.

One limitation, found while watching the summary's gates fail: turning a
*cover* into a `⊬` gives another consistent partial order, so no check on
the matrix alone can see that fault.  Only re-checking each row's
certificate (invariant O3) catches it.

### 6.4 Placements of the designed formulas

After the closure.  Each verdict rests on G4c proof terms and FinCM
models computed in this spike, not re-checked by the kernel, together
with kernel-checked RNDB rows; as Lean statements they are OPEN.

| formula | place | how |
|---|---|---|
| q5 ∨ q8 | ≡ ρ15 | equal keys (`canonFix`) |
| q10 ↠ q4 | ≡ ρ13 | it is ρ13 as written |
| q10 ↠ q7 | ≡ ρ13 | decider |
| q8 ↠ q4 | ≡ ρ19 | decider |
| rung 2 | ≡ ρ6 | decider |
| rung 3 | ≡ ρ10 | decider |
| q13 | **∉R** | strictly between the coatom ρ15 and ⊤ |
| ◯q11 | **∉R** | strictly between the coatom ρ10 and ⊤ |
| q12 | open: ≡ ρ9, or ∉R | `[ρ9] ⊢ q12`, `[q12] ⊢ ρ12`, ρ9 < ρ12 a cover |
| q10 ∧ q13 | open: ≡ ρ16, or ∉R | `[ρ16] ⊢ q10 ∧ q13`, `[q10 ∧ q13] ⊢ ρ8`, ρ16 < ρ8 a cover |

The four aliases have short reasons in IPC with `a := ◯⊥`, which is what
makes them obligations rather than discoveries:

    rung 2 = (a ∨ ¬a) ∨ ((a ∨ ¬a) ↠ a)   and   (a ∨ ¬a) ↠ a  ⊣⊢  ¬¬a,
        so rung 2 ⊣⊢ ¬a ∨ ¬¬a = ρ6;
    rung 3 = rung 2 ∨ (rung 2 ↠ rung 1)   and   ρ6 ↠ ρ4  ⊣⊢  ¬¬a ↠ a = ρ8,
        so rung 3 ⊣⊢ ρ6 ∨ ρ8 ⊣⊢ ¬¬a ∨ (¬¬a ↠ a) = ρ10;
    q10 ↠ q7 = ρ8 ↠ ρ6   and   ρ8, ρ6 ⊢ ρ4,   so  ρ8 ↠ ρ6 ⊣⊢ ρ8 ↠ ρ4 = ρ13;
    q8 ↠ q4 = ρ11 ↠ ρ4,  ρ19 = ρ11 ↠ ρ7,  ρ11 = ρ7 ↠ ρ4,  and  ρ4 ⊢ ρ7,
        so the two are interderivable.

So the first four rungs are ρ2, ρ4, ρ6 and ρ10, and the first rung that
can leave R is rung 4 (not measured).

`docs/rho-structure.md` places q12 = ◯ρ6 and q13 = ◯ρ11 outside the
catalogue (R4): the q13 placement agrees, and q12 is left open here.  The
same note lists ◯ρ10 among the predicted new generators (C1), each of
which "either lands on a known class or is a new join-irreducible";
◯q11 is ◯ρ10, and here it lands on no class of R.  Each open placement is
one designed cell, because the formula sits between the two ends of a
cover of R:

    [q12] ⊢? ρ9             ⊢ means q12 ≡ ρ9;   ⊬ means q12 ∉R;
    [q10 ∧ q13] ⊢? ρ16      ⊢ means ≡ ρ16;      ⊬ means ∉R.

Four of the six escape compounds lie in R (ρ13 twice, ρ15, ρ19).  That is
not a contradiction: each was recorded as escaping the 16 q-representatives,
and these are classes of R that have no q twin.  It is the reason for S3
in §5: "escapes" is a claim about a version of the forms, and it must
name that version.

### 6.5 Findings for G3

1. **Key lookup does most of the work on stored material:** 65.8% of
   the ρ-matrix, 75% of the smoke test, in microseconds.  On new formulas
   it does much less (30.5% of T2), as it should.
2. **Union-find added nothing (U = 0) on every set.**  The reason is in
   the old data: its 321 `derived` rows already store the transitive
   consequences of `interd`.  The proposed store keeps no derived rows
   (§4), so this work moves to the `cut` rule.  A separate union-find
   tier is not needed (Q6).
3. **Storing the order pays.**  Banking the 117 decider answers on T1
   raises the store-only rate on T2 from 35.9% to 47.7%, and settles 12
   cells that the decider could not.  Closing *all* answers under the §4
   rules settles 32 of the remaining 48, leaving 16 (96.4% settled).
4. **The whole ρ-order is 48 facts** (37 covers, 11 `⊬`), against 462
   cells, of which RNDB banks the 304 `⊬` cells row by row (Q5).
5. **The decider's cost is all in what it cannot settle.**  A settled
   cell costs about 14 ms.  The 60 unsettled cells of T2 cost 1,770 s,
   and the raised budgets settled none of them.  A refuter with a
   different method (FRJW `checkClosed`) is the next step for these, not
   a larger budget (Q7).
6. **Not run:** FRJW `checkClosed` (`lake exe pll`).  In this worktree's
   build its dependencies are out of date (`lake build --no-build pll` lists
   `FRJ.CalculusW`, `FRJ.Gbu.Base`, `tools.Svg`, `wip.rcells` and others),
   and a rebuild of that size was outside the spike.  Nothing private was
   used or consulted.

### 6.6 Reproduce

    lake build f0s2
    gtimeout 3000 .lake/build/bin/f0s2 _out/f0s2-cells.jsonl
    python3 -I scripts/f0_s2_summary.py _out/f0s2-cells.jsonl --json _out/f0s2-summary.json
    python3 -I scripts/f0_s2_summary.py _out/f0s2-cells.jsonl --selftest

The per-cell file (`_out/`, about 0.7 MB) is not committed.  The
self-test plants three faults in the measured verdicts (a `⊬` cell of
the ρ-matrix turned into `⊢`, a transitive `⊢` cell turned into `⊬`, a
decided T2 `⊬` turned into `⊢`) and requires the summary to catch each:
3/3 caught.

## 7 · Decisions for G3

Each item is a question for Matthew with the proposal's default.  Nothing
here is decided until he says so.

**Q1 · The accepted forms, version 1.**  Default: the 22 ρ of
`LaxLogic/RN/Rho.lean`, frozen by value as `rhoList`, plus the family
`rung k`.  The 16 q-representatives become an alias table (§2.2, A2), and
the q-list survives only as the frozen version `v_q` that the old escape
facts were stated against (§5).  Alternatives: (a) admit no family now
and add `rung` at a later version; (b) take as the family the whole
one-variable Rieger–Nishimura lattice at `p := ◯⊥` (the "left rail" of
`docs/rho-structure.md`, R5), of which `rung` is one chain.  `rung` is
proposed because its strictness is already proved (`LaxInfinite.lean`)
and because its first four members are aliases (§6.4), so it starts as
a check on the catalogue rather than a source of new names.

**Q2 · Names.**  Default: `FormName.rho i | FormName.rung k`, issued once,
never reused, never re-pointed; the earlier-issued name is primary in an
alias row (A4).  Open sub-question: whether a placement found by the
decider (§6.4) may be recorded as an alias row by a tool, or only after
review (A5 says only the naming is reserved to Matthew).

**Q3 · Identity key.**  Default: `key φ = Rewrite.keyF (canonFix φ)`, with
`canon` carrying a version (K3).  Alternative: fix `canon` so that one pass
is idempotent, and keep a single pass.  The default needs no change to
`Rewrite/`; the alternative is cleaner but touches the certified
normaliser.

**Q4 · Choice in the key certificate.**  `Rewrite.canon_interd` depends on
`Classical.choice`.  Options: (a) accept it for the key's certificate only,
as a recorded exception; (b) require a choice-free `canon_interd` before
any tool relies on `key_sound` (plan P6).  Default: (b), with (a) as the
interim state, labelled as such in the pins.

**Q5 · How much of the order to store.**  §6.3 shows that the 462
ρ-cells follow from 37 covers and 11 ⊬ facts by the rules of §4.
Options: (a) store every decided cell as a row, and count the redundant
ones (O2); (b) store only a basis, and let queries derive the rest.
Default: (a).  A row costs one certificate, and the basis depends on the
current set of forms, so it is a view, not an identity.

**Q6 · Union-find.**  Over these test sets union-find over `interd` added
nothing to key lookup (§6.5, item 2), because the old data stores the
transitive consequences as rows.  Default: no union-find tier in `ask`;
the `cut` rule of §4 does that work over base facts, and a union-find
structure is at most an index behind it.

**Q7 · Unknown cells.**  Of the 60 cells the public decider left open on
T2, 28 ended with "all stages ran and missed" (no proof, no countermodel
within the configured frames) and 32 at a time limit; the closure then
settles 32 of the 48 left after banking, so 16 remain (§6.2, §6.4).  By
the discipline these are `flag`, not `fail`: each is re-run at a raised
budget, never dropped.  The raised budgets of this spike (D2, D3) settled
none, so the options are a different method rather than more of the same:
(a) widen `Config.frames` / `comboCap` of the FinCM battery; (b) FRJW
`checkClosed`, which is public but whose executable (`pll`) needs a
rebuild of `FRJ.CalculusW`, `FRJ.Gbu.Base` and others.  Default: (b), as
a separate bounded run after Matthew's word on the rebuild, starting with
the two one-cell questions of §6.4.

**Q8 · Scope of `∉R`.**  Default: every `∉R` cell in a table means
`OutsideAll v_R φ` with `v_R` the frozen 22-form version (S3), and the old
escape facts are restated against `v_q`.  The measurement shows why this
matters: some compounds recorded as escaping the q-list lie in ρ-classes
(§6.4).

**Q9 · The next designed cells.**  If Matthew wants the open placements
closed before G3, two cells do it, and a third question extends the
family check; each is for a public refuter:

    [q12] ⊢? ρ9               (q12 ≡ ρ9, or q12 ∉R)
    [q10 ∧ q13] ⊢? ρ16        (≡ ρ16, or ∉R)
    rung 4 against the 22 ρ   (44 cells; the first rung that can leave R)

The first two are single cells because the formula lies between the two
ends of a cover of R (§6.4).
