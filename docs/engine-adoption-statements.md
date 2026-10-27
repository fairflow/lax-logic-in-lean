# Engine adoption: statements for gate G2

**Status: OPEN, for gate G2** (`METHOD-F0.md` §3; lean-certify R10).
2026-10-22, branch `engine-adoption` from `origin/main` 0005006.  Nothing
here is built and no Lean file was changed.  Every statement marked NEW is
a proposal until Matthew approves it or supplies an alternative; every
statement marked PROVED names an existing declaration, its file and its
axioms (from the file's own pin or from `docs/status-ledger.jsonl`).

**Refreshed 2026-10-27 (F0 plan step 4): see §9** for what steps 1–3 of
the plan and Matthew's gate decisions have settled, and for the status of
M1–M10.  Above §9, only the locations of the subframe tableau's files
were brought up to date (public since #74); the rest of the text is
unchanged.

The rule this document applies is the draft `METHOD-F0.md` §6 (branch
`method-f0`, 998510b): *every tool is adopted as a lean-certify `Engine`;
tools are invoked only through the decider settings; a pre-registered
comparison (G4) sets the order of the pairs, and its result is recorded in
the table of tools* (§1 B), so that no tool is chosen at random (§1 D).
The decider interface is lean-certify v0.3.0 (35ebd72):
`Certify.Prover`, `Certify.Disprover`, `Certify.Decider`,
`Harness.Registry`, `Harness.DeciderConfig` (`LeanCertify/Decider.lean`),
with `Certify.Certifier` and `Certify.Engine` (`LeanCertify/Certifier.lean`).

Contents: §0 summary; §1 the common specification; §2 the contestants;
§3 the settings file; §4 what depends on the FRJ library; §5 the slot for
the F0 database engine; §6 order of work; §7 decisions for Matthew;
§8 sources.

## 0 · Summary

| tool | settings name | sides | ⊢ certificate | ⊬ certificate | soundness | producer | to do | effort |
|---|---|---|---|---|---|---|---|---|
| subframe tableau | `subtab` | pair | `TCert` | `SubCM` | PROVED (`LaxLogic/PLL/SubTab/`) | `SubTab.solve`, no budget | one `Holds`; a budget (M6) | none here |
| finite countermodels | `fincm` | disprover | | `FinCM × Nat` | PROVED | `CounterEmit.emit` | formula-level certifier (one line); producer wrapper | 1 h |
| G4c | `g4c` | prover | `Σ ψ, G4cTm [] ψ` | | PROVED | `G4cTm.findBounded` | certifier (one line); Boolean checker only if M2 asks | 1 h (Boolean: 3 to 5 h) |
| LJF◯ | `ljfo` | prover | `DerivTree` | | PROVED | `emitTree` | formula-level certifier (one line); producer into a library module | 1 h |
| Built-class trees | `reject` | disprover | | `FinCM × Nat` | PROVED | T3 forward searcher (`wip/`) | promote; producer wrapper; M3 | 2 to 3 h |
| FRJW + `checkClosed` | `frjw` | pair | `Σ ψ, Tm [] ψ` (B) or the store (A) | `FinCM × Nat` (B) or a root row (A) | parts PROVED, split lemmas NEW | `decideDataByEngine` | promote 7 `wip/` modules; 2 or 3 NEW lemmas; `Tab.toFinCM`; gates | about 1 day |
| FRJV | none | excluded (§2.6) | | | | | | |
| F0 database | `f0db` | pair, slot | a chain of `DerivTree`s | a stored `FinCM` | chain certifier NEW | lookup and order reasoning | step 6 | not estimated |

Estimates are agent time, excluding builds.  On the record, estimates of
this kind have run about four times too high, so read them as upper
bounds.

## 1 · The common specification

All tools in one decider share one specification type and one `Holds`
(`Harness.Registry Spec Holds` is a list of `Prover Spec Holds` and
`Disprover Spec Holds`).  The proposal:

```lean
Spec     := PLLFormula
Holds φ  := Nonempty ([] ⊢ φ)          -- inside PLLND, `[] ⊢ φ` is the type `LaxND [] φ`
Holds φ → False   is   [] ⊬ φ          -- by unfolding: `⊬` on a type of derivations is `¬ Nonempty`
```

This is exactly the `Holds` of the subframe tableau (`PLLND.SubTab.Holds`,
`LaxLogic/PLL/SubTab/Sound.lean`, approved under R10 on 2026-10-15), and it is
definitionally `PLLND.SemUI.Deriv [] φ` (`LaxLogic/Deriv.lean`).  It is a
proposition, as `Certify.Decider` requires (`Holds : Spec → Prop`).

### 1.1 A formula, not a sequent

1. Two of the engines decide formulas only.  The subframe tableau checks
   `check ⟨false, [], [φ]⟩ c`; the FRJW decision chain takes a goal
   `G : Form` in the empty context (`decideGbuW`, `ofPLL`, `toPLL`).
2. The other three certify sequents and take the empty context unchanged:
   `FinCM.checkB M w [] φ`, `checkDeriv (decideSeq [] φ) t`, `G4cTm [] φ`.
3. The F0 store's base facts have one hypothesis (`[φ] ⊢ ψ`, `[φ] ⊬ ψ`,
   `docs/f0-reimplementation-plan.md` P1), and the deduction theorem
   carries it across both ways:

       PLLND.deduction_iff :
           Nonempty (φ :: Γ ⊢ ψ)  ↔  Nonempty (Γ ⊢ φ ↠ ψ)
                               PROVED, LaxLogic/PLL/ND/Theorems.lean, [propext]

   so that, at `Γ = []`,

       Nonempty ([φ] ⊢ ψ)  ↔  Holds (φ ↠ ψ).

   A countermodel of `[φ] ⊢ ψ` at a world `x` is a countermodel of
   `⊢ φ ↠ ψ` at the same `x` (`x` forces `φ` and not `ψ`, and the order is
   reflexive), so a producer may search either form; the certifier always
   re-checks the formula.
4. The price for the sequent engines is one invertible right-implication
   step, which is negligible.  A sequent specification would instead put a
   curried conversion inside the subframe tableau's certifiers (already
   adopted at the formula) and inside FRJW's.

Questions with several hypotheses are asked through the curried formula:

```lean
curry Γ ψ := Γ.foldl (fun acc γ => γ ↠ acc) ψ

curry_iff :  Nonempty (Γ ⊢ ψ)  ↔  Holds (curry Γ ψ)          -- NEW, by induction on Γ with deduction_iff
```

PCLL (`DerivU`) questions are outside this `Holds`; they stay with
`PLLND.Search` and `Config.accept := RNC.confB`, and no decider tool is
proposed for them.

### 1.2 Where `Holds` lives

One declaration, in a module importing only `LaxLogic.PLL.ND.NDCore`
(proposed: `Harness/Spec.lean`, namespace `PLLDecider`).  The subframe
tableau, once moved, should take `PLLND.SubTab.Holds` to be that constant
(an `abbrev`).  Otherwise the registry relies on definitional unfolding to
identify two constants of the same value (decision M9; to be agreed with
the agent doing the move).

### 1.3 What each existing certifier needs to meet `Holds`

| tool | existing soundness (PROVED) | at the common specification |
|---|---|---|
| `fincm` | `FinCM.not_provable_of_check : FinCM.checkB M w Γ C = true → Γ ⊬ C` (`LaxLogic/PLL/Semantics/CountermodelEmit.lean`, `[propext, Quot.sound]`) | instance `Γ := []`, `C := φ`; the conclusion `[] ⊬ φ` is `Holds φ → False`.  No new lemma. |
| `ljfo` | `LJFO.laxND_of_checkDeriv : checkDeriv (decideSeq Γ φ) t = true → Nonempty (Γ ⊢ φ)` (`LJF/OCheckDeriv.lean`, `[propext, Quot.sound]`) | instance `Γ := []`; the conclusion is `Holds φ`.  No new lemma. |
| `g4c` | `PLLND.Search.proved_sound : G4cTm Γ C → Nonempty (Γ ⊢ C)` (`LaxLogic/PLL/Search/Search.lean`, `[propext, Quot.sound]`) | instance `Γ := []`.  No new lemma. |
| `reject` | `Reject.not_laxND_of_certifies : Reject.certifies M w Γ C = true → Γ ⊬ C` (`Reject/Cert.lean`, `[propext, Quot.sound]`) | instance `Γ := []`.  No new lemma. |
| `subtab` | `PLLND.SubTab.holds_of_check`, `PLLND.SubTab.SubCM.refutes_sound` (`LaxLogic/PLL/SubTab/Sound.lean`, `[propext, Quot.sound]`) | already at `Holds`. |
| `frjw` | `FRJ.Gbu.laxND_of_provableGbuC : ProvableGbuC G → Nonempty ([] ⊢ toPLL G)` (`FRJ/Gbu/LaxND.lean`, `[propext, Quot.sound]`); `FRJ.soundnessW : DisprovableW G → ¬ PLL G` (`FRJ/SoundW.lean`, `[propext, Quot.sound]`); `FRJ.valid_of_derivable : ([] ⊢ φ) → ∀ K, K.valid (ofPLL φ)` (`FRJ/Bridge.lean`, `[propext, Quot.sound]`); `FRJ.toPLL_ofPLL : toPLL (ofPLL φ) = φ` (`FRJ/Bridge.lean`, `[propext]`) | two NEW one-line bridges, below. |
| Tm terms (FRJW option B) | `PLLND.Tm.toND : Tm Γ φ → (Γ ⊢ φ)` (`LaxLogic/PLL/ND/Terms.lean`, no axioms) | instance `Γ := []`.  No new lemma. |

The two FRJW bridges (NEW):

```lean
holds_of_provableGbuC     :  ProvableGbuC (ofPLL φ)  →  Holds φ
    -- toPLL_ofPLL φ ▸ laxND_of_provableGbuC h   (as in FRJ.Gbu.W.laxND_of_PLL)
not_holds_of_disprovableW :  DisprovableW (ofPLL φ)  →  [] ⊬ φ
    -- fun ⟨p⟩ => soundnessW h (fun K => valid_of_derivable p K)
```

Optional (NEW), only to make the producers' sequent-to-formula step
auditable; the certifier re-checks either way:

```lean
FinCM.checkB M w [φ] ψ = true  →  FinCM.checkB M w [] (φ ↠ ψ) = true
```

## 2 · The contestants

Notation for budgets: `b` is the `budget` the decider hands to `produce`
(default 1000, multiplied by `budgetFactor` = 4 on each of `flagReruns` = 2
raises).  Every budget mapping below is PROVISIONAL: G4 fixes it together
with the order.

The bodies of `sound` and `produce` below are sketches, not checked code.

Two kinds of certificate occur.  A *Boolean-checked* certificate is
literal data judged by a structurally recursive `check` (`DerivTree`,
`FinCM`, `TCert`, `SubCM`).  A *type-checked* certificate is a term of an
indexed family (`G4cTm [] ψ`, `Tm [] ψ`, an FRJW row); its correctness is
established by the kernel's type checker when the term is elaborated, and
`check` only compares its index with the specification.  lean-certify's
step 2 asks for literal data; whether type-checked certificates are
admitted is decision M2.

### 2.1 `subtab`: the subframe tableau (the model)

**Exists** (public since #74): `PLLND.SubTab.engine : Certify.Engine
PLLFormula TCert SubCM Holds` (`LaxLogic/PLL/SubTab/Engine.lean`), with

```lean
yes.check φ c := check ⟨false, [], [φ]⟩ c
holds_of_check :  check ⟨false, [], [φ]⟩ c = true  →  Holds φ          -- PROVED, Sound.lean, [propext, Quot.sound]
no.check φ m := m.refutes φ
SubCM.refutes_sound :  m.refutes φ = true  →  Holds φ → False          -- PROVED, Sound.lean, [propext, Quot.sound]
complete :  (∃ c, yes.check φ c = true) ∨ (∃ m, no.check φ m = true)   -- PROVED, Complete.lean, [propext, Quot.sound]
```

`#certify_structural` and `#certify_statement` pass on `yes`, `no` and
`engine`.  `tools/SubTab/Settings.lean` registers it (`"subtab"`, a pair)
with the `"enum"` disprover (`PllFast.firstHitCap`,
`LaxLogic/PLL/SubTab/ModelEnum.lean`).

**Producer and budget.**  `SubTab.solve` (`LaxLogic/PLL/SubTab/Tableau.lean`, `partial`):
a closed tableau or an open branch read off as `SubCM`.  The budget is
ignored and the producer never returns `flag`; only the decider's deadline
bounds it.

**Missing.**  Nothing for adoption beyond the move.  Three consequences
for the rest of this document: one `Holds` (§1.2, M9); a budget, since a
first pair that never flags makes the fallback pairs unreachable (§3, M6);
for banking into the F0 store, `SubCM` and `TCert` are not the store's
formats (M5).

### 2.2 `fincm`: finite constraint countermodels (disprover)

**Exists.**  The checker and its soundness (above);
`CertifyAdoption.countermodel : Certifier (List PLLFormula × PLLFormula)
(FinCM × Nat) (fun s => s.1 ⊬ s.2)` at the sequent specification, with the
gate watched rejecting corrupted models (`CertifyAdoption.lean`).  Two
producers: the closure emitter `CounterEmit.emit` (worlds are pairs of a
prime `G4c`-closed theory and a promise set over the subformula closure;
complete over the closure in intent, unproved, exponential in the closure)
and the frame battery `Search.sweepCert` (decorations of the fixed frames
`defaultFrames`, that is, enumeration).  The minimiser
`CounterEmit.simplify` is checker-gated (R6).

**Certificate.**  `FinCM × Nat`, a model and a world.

**Certifier** (NEW, one line, the formula-level instance):

```lean
def fincmNo : Certifier PLLFormula (FinCM × Nat) (fun φ => Holds φ → False) where
  check φ c := FinCM.checkB c.1 c.2 [] φ
  sound _ _ h := FinCM.not_provable_of_check h
```

**Producer and budget.**  `CounterEmit.emit [] (Search.nf φ) (budget :=
some (200 * b))`, skipped when the closure exceeds
`Search.Config.emitClosureCap` (12), then `CounterEmit.simplify`; the
certifier re-checks on `φ` itself, as `Search.settleWhy` does.  The budget
is the node budget of `emit`'s G4c pre-check: 200 000 nodes at `b = 1000`,
which is `Search.defaultFindBudget`.  The closure cap is fixed; a formula
above it gets no certificate.  The battery stays out of the producer unless
Matthew rules otherwise (M3).  `Rewrite` is not used for normalisation: its
closure contains the sorried `SemUILayered`.

**Missing.**  The certifier and the producer wrapper.  1 h.

### 2.3 `g4c`: proof terms of G4iLL″ (prover)

**Exists.**  `G4cTm Γ C` (type-valued proof terms of the repaired calculus,
`LaxLogic/PLL/G4/G4Term.lean`), the fuel-free searcher `G4cTm.find` and the
node-budgeted `G4cTm.findBounded` (memo repaired 2026-10-19, #70),
`Search.proved_sound` (above), the tactic `pll_g4c` that splices a found
term for the kernel (`LaxLogic/PLL/Search/Run.lean`), and the printer
`G4cTm.src` (`Search.lean` §11).  G4c has no disprover of its own: the
refutation stages of `Search.settle` are `fincm`'s producers.

**Is there a Boolean checker for G4c derivations?**  None exists in this
repository.  The only Boolean G4c procedure is the fuelled `search` of
`LaxLogic/PLL/G4/G4Dec.lean` (`search_sound`, fuel `decideFuel`), which is
the route CLAUDE.md rule 4 forbids and lean-certify R1/R2 reject.

**Certificate.**  Type-checked route (recommended, no new proof):
`Σ ψ : PLLFormula, G4cTm [] ψ`.  Boolean route (only under M2): a NEW
untyped tree with one constructor per rule of `G4cTm`, principal formulas
named by value, as `SubTab.TCert` does.

**Certifier.**

```lean
-- type-checked route (NEW, one line)
def g4cYes : Certifier PLLFormula (Σ ψ : PLLFormula, G4cTm [] ψ) Holds where
  check φ c := decide (c.1 = φ)
  sound φ c h := (of_decide_eq_true h) ▸ Search.proved_sound c.2

-- Boolean route (NEW, only under M2)
checkG4c   :  List PLLFormula → PLLFormula → G4cTree → Bool        -- structural in the tree
g4c_of_check :  checkG4c Γ C t = true  →  Nonempty (G4cTm Γ C)
```

**Producer and budget.**  `(G4cTm.findBounded (200 * b) [] φ).1`, packed
with its index.  The budget is the node budget over the whole search tree:
200 000 nodes at `b = 1000`.  Exhaustion with budget left is `none`, never
a refutation (TOOLS.md §8).

**Missing.**  The certifier and producer wrapper, 1 h.  The Boolean
route, 3 to 5 h.  A splice printer exists (`G4cTm.src`).

### 2.4 `ljfo` and `reject`: the two-sided engine

**Exists, proof side.**  `checkDeriv : LSeq → DerivTree → Bool`
(structural, fuel-free) and `laxND_of_checkDeriv` (above), in the library
module `LJF/OCheckDeriv.lean`; the certifiers `laxNDCertifier` (sequent
specification) and `derivEngine : Engine LSeq DerivTree Empty LSeq.holds`
(no refutation side), the untrusted producer `emitTree` (iterative
deepening over `LSeq.succs`, `partial`), exemplars and negative tests, all
in `CertifyAdoption/CheckDeriv.lean`.  The fuelled `searchProves` of
`wip/ljfo_link.lean` is superseded for certification by `checkDeriv`
(TOOLS.md §8) and is not used here.

**Exists, refutation side.**  `Reject.certifies M w Γ C := BuiltB M &&
checkB M w Γ C` with `Reject.not_laxND_of_certifies` (above).  Its
soundness is `FinCM.not_provable_of_check` on the second conjunct;
`BuiltB` (rooted `Rᵢ`-tree, fallible worlds only at leaves) is a canonical
form, not a soundness condition (`Reject/Cert.lean` §1).  Three producers,
all in `wip/`: the battery filtered by `BuiltB` and the streamed generator
of Built trees (`wip/two_sided.lean`; closed formulas only, `val := []`),
both enumerations; and the T3 forward searcher (`wip/t3_search.lean`,
`T3Search.saturate` and `refutesAt`): saturation over `solo`/`join`
constructions with sharing, atoms supported, sound, not known complete.
`lake exe twosided` is a corpus runner over the 462 ρ-cells, not a
decider for one question.

**Certificates.**  `DerivTree` for `ljfo`; `FinCM × Nat` for `reject`.

**Certifiers** (NEW, one line each):

```lean
def ljfoYes : Certifier PLLFormula DerivTree Holds where
  check φ t := checkDeriv (decideSeq [] φ) t
  sound _ _ h := laxND_of_checkDeriv h

-- `reject` uses `fincmNo` (§2.2).  If Matthew wants the canonical form enforced
-- in the certificate itself:
def rejectNo : Certifier PLLFormula (FinCM × Nat) (fun φ => Holds φ → False) where
  check φ c := Reject.certifies c.1 c.2 [] φ
  sound _ _ h := Reject.not_laxND_of_certifies h
```

**Producers and budgets.**  `ljfo`: `emitTree (b / 25) (decideSeq [] φ)`,
a depth bound of 40 at `b = 1000` (the depth the exemplars were emitted
at).  The cost is exponential in the depth on failing branches, and on the
larger goals of `lake exe frjhard` LJF◯ was two to three orders of
magnitude slower than G4c (`tools/Engines.lean`, `ljfoProve`, 2026-08-22),
so the mapping is a G4 question.  `reject`: the T3 searcher with arity,
rounds and store cap derived from `b`, fixed at G4.

**Missing.**  The two certifiers (minutes).  `emitTree` should move from
`CertifyAdoption/CheckDeriv.lean` into a library module the settings can
import without the exemplars.  For `reject`: promote `wip/t3_search.lean` (content into a library
module, `main` into a thin entry point) and wrap it as `PLLFormula → Nat →
Option (FinCM × Nat)`, 2 to 3 h, after decision M3.  No minimiser exists
for `DerivTree` (R6); the exemplars were small enough without one.

### 2.5 `frjw`: the FRJW engine with `checkClosed`

**Exists.**  The untrusted W-engine (`FRJ.Search.W.wOps`,
`FRJ/Search/OpsW.lean`) and, in `wip/check_closed.lean`:

```lean
checkClosed G db := decide ((db.map (·.s)).Nodup) && chkScan G db && chkJoins G db
checkClosed_sound   :  checkClosed G db = true → DBClosedDG G db         -- PROVED, [propext, Quot.sound]
dbClosed_of_check   :  checkClosed G db = true → DBClosed G db           -- PROVED, [propext, Quot.sound]
decideGbuW_of_check :  (db : List (WRow G)) → checkClosed G db = true
                         → ProvableGbuC G ⊕' DisprovableW G              -- PROVED, [propext, Quot.sound]
decideByEngine G cfg     : Option (ProvableGbuC G ⊕' DisprovableW G)
decideDataByEngine G cfg : Option (GbuRC G [] G ⊕ (Σ' t Γ, FRJWr G t Γ G))
```

with, in the library, `decideOfStore` (`FRJ/Gbu/W/Saturate.lean`,
`[propext, Quot.sound]`): on a closed store, `some` root row gives the
disproof, and `none` gives a `Gbu◯` derivation by `searchW`.  The gate was
watched failing in compiled form (`lake exe checkprobe`: join rows deleted,
`false` 14/14; first row deleted, `false` 20/20).  `lake exe pll` runs
engine, `checkClosed` and `decideOfStore`, then turns a proof into a
`PLLND.Tm [] φ` (`laxOfR`, `ndToTm`) and a disproof into a minimised
`FRJ.Search.Tab` countermodel (`modR`, `tabOf`, `Tab.minimise`), with
printers for both (`tools/Decide.lean`, `answerOf`, `tmSnippet`,
`cmFile`).

**The split.**  The store certifies a dichotomy, `ProvableGbuC G ⊕'
DisprovableW G`.  It splits along `rootDisproof?`, and the two sides are
not symmetric:

* the **no** side needs no closure check at all: one stored root row is a
  disproof by itself, because its derivation is a term of `FRJWr`;
* the **yes** side needs the closure check: `checkClosed` is what licenses
  the step from "no root row" to provability.

Two ways to package it.

*Option A, the store as certificate* (Boolean closure check as the gate):

```lean
structure WStore where          -- certificate types independent of the specification
  G  : Form
  db : List (WRow G)
structure WRoot where
  G : Form
  r : WRS G

def frjwYesA : Certifier PLLFormula WStore Holds where
  check φ c := decide (c.G = ofPLL φ) && checkClosed c.G c.db && (rootDisproof? c.db).isNone
  sound := …     -- provableGbuC_of_check, then holds_of_provableGbuC

def frjwNoA : Certifier PLLFormula WRoot (fun φ => Holds φ → False) where
  check φ c := decide (c.G = ofPLL φ) && decide (c.r.rhs = c.G)
  sound := …     -- disprovableW_of_hit, then not_holds_of_disprovableW
```

```lean
provableGbuC_of_check :                                                -- NEW
    checkClosed G db = true  →  rootDisproof? db = none  →  ProvableGbuC G
    -- the `none` branch of `decideOfStore`:
    -- ⟨searchW (wsat_of_closed db (tC_of_closed (dbClosed_of_check h))) … (rootDisproof?_none hr)⟩
FRJ.Search.W.disprovableW_of_hit :  r.rhs = G  →  DisprovableW G        -- PROVED, FRJ/Search/OpsW.lean, [propext]
```

*Option B, the certificates the engine already prints* (recommended):

```lean
def tmYes : Certifier PLLFormula (Σ ψ : PLLFormula, Tm [] ψ) Holds where     -- NEW, one line
  check φ c := decide (c.1 = φ)
  sound φ c h := (of_decide_eq_true h) ▸ ⟨c.2.toND⟩

def frjwEngine : Engine PLLFormula (Σ ψ, Tm [] ψ) (FinCM × Nat) Holds where
  yes := tmYes
  no  := fincmNo
  produce φ b := match decideDataByEngine (ofPLL φ) (cfgOf b) with
    | some (.inl d)         => .pass ⟨φ, toPLL_ofPLL φ ▸ ndToTm (laxOfR d)⟩   -- as `answerOf`
    | some (.inr ⟨_, _, d⟩) => .fail (Tab.toFinCM ((tabOf (W.modR d) (atoms φ)).minimise (ofPLL φ)))
    | none                  => .flag                                         -- store not closed within bound
```

with `Tab.toFinCM` NEW and untrusted (worlds `0 … n-1`; `ri`, `rm` the
strict pairs of `leT`, `rmT`; `fall` from `falT`; `val` from `atomsT`; the
world is `root`).  The translation is faithful in principle
(`FRJ.Bridge.force_toConstraint`: forcing in an FRJ model agrees with
forcing in its constraint model, and a `Tab`'s valuation, like a `FinCM`'s,
makes fallible worlds force every atom), and `fincmNo` re-checks every
instance, so a wrong translation is REJECTED as a tool defect and never
gives a wrong verdict.  The F0 plan
needs the same translation for its import of the ρ `Tab` models (§5.1
there).

Why B: both certificates can be spliced as kernel facts today (`tmSnippet`,
and a `FinCM` checked by `decide`), whereas no printer exists for `WRow`
derivations, so an option-A fact file cannot be written; B shares its
certifiers with `fincm` and with any producer of `Tm` terms, so its only
new soundness obligation is the one-line `tmYes`; and B keeps `checkClosed`
inside the producer, which is where `docs/f0-reimplementation-plan.md` §4
places it.  A is the choice if Matthew wants the closure check itself to be
the gate (M4).  Under A, `#certify_structural` has never been run on
`checkClosed`, and its kernel cost on a printed store is unmeasured.

**Producer and budget.**  `cfgOf b` sets the W-engine's `Config` (default
`rounds 10, jmax 3, pmax 2, lamCap 10, maxRS 800, maxIS 800`):

```lean
cfgOf b := { rounds := b / 100, maxRS := 4 * b / 5, maxIS := 4 * b / 5,
             jmax := 3 + k, pmax := 2 + k, lamCap := 10 }   -- k = number of factor-4 raises above 1000
```

which is the default `Config` at `b = 1000`.  The join arities drive a cost
exponential in `G` (TOOLS.md §3, `impInI` 2^|Θ|, `axIC` 2^|gAt|), so this
mapping is a G4 question.  `none` from `decideDataByEngine` is
`not-closed-within-bound`, mapped to `flag`, never to a verdict.

**What must be promoted out of `wip/`.**  The closure of
`wip.check_closed` reaches seven `wip/` modules: `check_closed`,
`check_scan`, `check_join`, `dbclosed_dg`, `b1b2_lemmas`, `b1b2_relaxed`,
`b1b2_hitting`.  The ledger records 246 declarations in them, none sorried,
every one within `[propext, Quot.sound]`.  Promotion is a move (new module
names, with forwarding stubs left in `wip/` if wanted), the lakefile, and
the importers `tools/Decide.lean`, `tools/CheckProbe.lean`,
`tools/Bench.lean`, `Audit/Experimental.lean` and six `_probe/` files.
With it go the gates the promoted certifier must carry: R3 and R2 lints,
the axiom pins (present), and an R9 negative test pinned with
`#guard_msgs` (a deleted join row; for option B, a translated model with a
fallible flag removed).

**Missing.**  Promotion, 2 to 4 h plus a build of the chain.  NEW lemmas:
`holds_of_provableGbuC` and `not_holds_of_disprovableW` (both options),
`provableGbuC_of_check` (option A), 1 to 2 h.  `tmYes` and `Tab.toFinCM`
with a test, 1 to 2 h.  The gates, 1 to 2 h.  About one day in all.

### 2.6 FRJV: excluded

FRJV is excluded: in Matthew's words an old incomplete attempt, its
completeness never established and abandoned for FRJW, whose calculus is
complete (`decidePLL`); it is not an open problem of the project.
(Separately, completeness of the paper calculus FRJ◯ is REFUTED, by the
kernel-checked witnesses #80 and #81.)

## 3 · The settings file `Harness/Settings.lean`

One public settings file, in the form of lean-certify `docs/deciders.md`.
The registry names every adopted tool once; the decider names tools from
it.  **The order of the pairs is provisional until the G4 comparison**,
and the result of that comparison is recorded in TOOLS.md (§1 B), never
edited here by hand.

```lean
import Harness.Tools        -- the adapters of §2 (NEW)

/-! # Lean certify settings for lax-logic-in-lean

DRAFT (G2).  Edit only the lines marked EDIT.  A tool is named by a string
from `Harness.tools`; a misspelt name is an error when this file is
compiled (`#certify_decider`).  THE ORDER OF THE PAIRS IS PROVISIONAL: it
is set by the pre-registered comparison (gate G4) and recorded in TOOLS.md.
For readers who do not know Lean: `docs/deciders.md` in lean-certify. -/

open Certify PLLDecider

/-- The tools this project offers, by name. -/
def Harness.tools : Harness.Registry PLLFormula Holds :=
  [ .pair      "subtab" (Prover.ofEngine PLLND.SubTab.engine "subtab")
                        (Disprover.ofEngine PLLND.SubTab.engine "subtab"),
    .pair      "frjw"   (Prover.ofEngine frjwEngine "frjw")
                        (Disprover.ofEngine frjwEngine "frjw"),
    .prover    "ljfo"   ljfoProver,
    .prover    "g4c"    g4cProver,
    .disprover "fincm"  fincmDisprover ]
  -- "reject": registered after decision M3 (§2.4)
  -- "f0db":   the F0 database engine, step 6 (§5)

/-- The decider.  PROVISIONAL ORDER (G4). -/
def Harness.decider : Harness.DeciderConfig where
  prover    := "subtab"                                                   -- EDIT
  disprover := "subtab"                                                   -- EDIT
  fallback  := [("frjw", "frjw"), ("ljfo", "fincm"), ("g4c", "fincm")]   -- EDIT: pairs, tried in order
  run       := { mode := .race,                                           -- EDIT: .race | .sequential
                 budget := 1000, flagReruns := 2, budgetFactor := 4,
                 deadlineSec := 120 }

#certify_decider Harness.decider           -- checks every name against Harness.tools
```

The rest of the layout (NEW): `Harness/Config.lean` holds the project's
one `Harness.config`, moved from `CertifyAdoption.lean` (which then
imports it), because two declarations of `Harness.config` cannot share an
environment; `Harness/Spec.lean` holds `Holds`, `curry`, `curry_iff` and
the formula parser `parse : String → Except String PLLFormula`, moved
(not copied) from `tools/Decide.lean`, whose closure reaches the sorried
`SemUILayered` through `Rewrite`; `Harness/Tools.lean` holds the adapters
of §2; `Harness/Main.lean` is the thin entry point `def main :=
Certify.Cli.main Harness.tools PLLDecider.parse Harness.decider`.  A new
`lean_lib Harness` (explicit globs) and a `lean_exe` (proposed name
`plldecide`), outside `defaultTargets`.  The exit codes are lean-certify's
(0 yes, 1 no, 2 parse error, 3 flag), which differ from `lake exe pll`'s;
TOOLS.md must say so.  `CertifyAdoption/Regression.lean` gains a pin for
every new certifier.

Three facts about this provisional order, for G4:

1. **The first pair never flags.**  `subtab`'s producer ignores the budget
   and always returns `pass` or `fail`, and `deadlineSec` bounds the whole
   run, so the fallback pairs are reached only after a REJECTED
   certificate, never on a hard formula.  G4 should decide between giving
   the tableau a node budget and placing it last (M6).
2. **An engine pair runs its producer twice.**  `Prover.ofEngine` and
   `Disprover.ofEngine` each call `E.produce`: in race mode both threads
   run the same engine, and in sequential mode a refutable formula runs it
   twice in series.  For `subtab` this is cheap; for `frjw` it doubles the
   cost.  A fix belongs in lean-certify (one producer run feeding both
   sides of a pair), which is Matthew's library (M7).
3. **`PLLND.Search.settle` is not registered.**  Its stages are `fincm`'s
   producers and `g4c` in a fixed order; registering it would fix an order
   outside the settings, against §1 D.

## 4 · What depends on the FRJ library, and what does not

I found no document that defines "the FRJ rebuild"; this section reads it
as "work that edits, or forces a rebuild of, modules of the FRJ library".
Please correct the reading if a specific campaign is meant.

**Needs FRJ.**  Only `frjw`.  Its closure is `FRJ.CalculusW`,
`FRJ.StepW`, `FRJ.ExtractW`, `FRJ.SoundW`, `FRJ.Bridge`,
`FRJ.Search.{Core, Engine, OpsW, Pin}`, the `FRJGbu` library
(`FRJ.Gbu.Base` … `FRJ.Gbu.W.Saturate`, `FRJ.Gbu.LaxND`,
`FRJ.Gbu.W.LaxND`), and, through `wip/b1b2_lemmas.lean`, `FRJ.CalculusV`
and `FRJ.RefAt` (definitions shared with FRJV; FRJV's soundness and
completeness are not used).  The `Tab.toFinCM` translation imports
`FRJ.Search.Pin`.  **No existing FRJ module is edited by this proposal**:
the NEW lemmas and adapters go in new modules downstream of
`FRJ.Gbu.W.Saturate`, `FRJ.Gbu.LaxND` and `FRJ.Search.OpsW`.  What is
rebuilt is the seven promoted modules (new names) and their importers.

**Does not need FRJ.**  `subtab` (its own semantics module, moved with
it), `fincm` (`LaxLogic.PLL.Semantics.CountermodelEmit`,
`LaxLogic.PLL.Search.Search`), `g4c` (`LaxLogic.PLL.G4.G4Term`), `ljfo`
(`LJF.OCheckDeriv`; `lake build LJF.OCheckDeriv` about 8 s, 3.2 GB),
`reject` (`Reject.Cert`, whose closure reaches the semantic-UI module
`LaxLogic.PLL.SemUI.SemUI`, sorry-free), `Harness/Spec.lean` and
`Harness/Settings.lean` apart from the `frjw` line, and the chain
certifier of §5.

So the decider can be built and used without FRJ by leaving out the
`frjw` line, and `frjw` can be added after the promotion without touching
any other tool.

## 5 · Slot: the F0 database engine (step 6, not specified here)

Settings name `f0db`, a pair, specified with the store (plan phases D to
G).  Its prover answers `Holds (φ ↠ ψ)` from stored `⊢` rows, by lookup or
by a chain; its disprover answers from a stored `⊬` row by the order
reasoning of the F0 plan §4 (the stored model refutes the derived pair at
the same world, and `fincmNo` re-checks it), so the disprover needs no new
certifier.  The **one new certifier** is the chain, for Matthew's tactic of
§1 A:

```lean
-- NEW (OPEN), step 6
chainCheck : PLLFormula → List (PLLFormula × DerivTree) → Bool
--  chainCheck (φ ↠ ψ) [(χ₁, t₁), …, (χₖ, tₖ)] = true  exactly when  χₖ = ψ  and,
--  with χ₀ := φ,  checkDeriv (decideSeq [χᵢ₋₁] χᵢ) tᵢ = true  for 1 ≤ i ≤ k

chain_sound :  chainCheck (φ ↠ ψ) c = true  →  Holds (φ ↠ ψ)
```

sound by transitivity: `laxND_of_checkDeriv` at each step,
`PLLND.SemUI.Deriv.cutHead` (PROVED, `LaxLogic/Deriv.lean`, `[propext]`)
`k − 1` times, then `deduction_iff`.

For the strict order of §1 A, write `u < w` for `Nonempty ([u] ⊢ w) ∧
[w] ⊬ u`.  The tactic transports a stored cover `u ⋖ v` to `u < v`
(dropping the minimality clause, which is relative to the database) and
composes.  The strict part needs nothing beyond `fincmNo`, because

```lean
Nonempty ([u] ⊢ v)  →  [w] ⊬ v  →  [w] ⊬ u
```

(if `[w] ⊢ u` then `[w] ⊢ v` by cut), and the stored model of `[w] ⊬ v`
refutes `[w] ⊢ u` at the same world.  So `u ⋖ v ⋖ w` in the database gives
the kernel-checked fact `u < w` from one chain certificate and one
re-checked model.  The tactic itself, and how it reads the store, are
step 6.

## 6 · Order of work, once approved

1. `Harness/Config.lean`, `Harness/Spec.lean` (`Holds`, `curry_iff`, the
   parser moved), and the `fincm`, `ljfo` and `g4c` adapters.  **◯-free
   first** (CLAUDE.md rule 8): each adapter is run end to end on two or
   three designed ◯-free cells, for instance `⊢ p ↠ p` (yes) and
   `⊢ ((p ↠ q) ↠ p) ↠ p` (no), then on PLL cells, for instance
   `⊢ p ↠ ◯p` (yes), `⊢ ◯p ↠ p` (no), and the G4iLL gap
   `⊢ ◯((◯p ↠ r) ↠ ◯p) ↠ (◯p ↠ r) ↠ r` (yes).  These are smoke cells
   (rule 9), not the G4 comparison set.
2. Each new certifier gets `#certify_structural`, `#certify_statement`,
   its axiom pin, and a negative test watched failing (R9), pinned in
   `CertifyAdoption/Regression.lean`.
3. `Harness/Settings.lean` and the entry point, with `subtab` once the
   move has landed.
4. `frjw`: promotion of the seven modules, the NEW lemmas, `Tab.toFinCM`,
   the gates.
5. `reject`, if decision M3 admits it.
6. G4: the designed cells, budgets and measures fixed in advance; the
   result recorded in TOOLS.md, one row per settings name (verdict
   agreement, time, certificate size, kernel time, METHOD-F0 §5).  Only
   then is the order of §3 set.

## 7 · Decisions for Matthew

- **M1. The common specification.**  `Spec := PLLFormula`,
  `Holds φ := Nonempty ([] ⊢ φ)`, sequents asked through `deduction_iff`
  (§1).  The alternative is a sequent specification, which moves the
  conversion into the subframe tableau and FRJW.
- **M2. Type-checked certificates.**  Admit terms of indexed families
  (`G4cTm [] ψ`, `Tm [] ψ`, FRJW rows) as certificates whose `check`
  compares the index, or require every certificate to be Boolean-checked
  literal data.  The second needs a NEW `checkG4c` (§2.3), and for FRJW's
  yes side either option A or a NEW Boolean type checker for
  natural-deduction terms, which is the "LaxND terms" alternative of the
  plan's D3.
  Recommendation: admit them.  The Boolean route is further proof effort
  for a small gain (uniform lint coverage), which §1 D argues against.
- **M3. Enumeration as a producer.**  `tools/Engines.lean` registers
  `Reject.certifies` with `mayDiscover := false` ("no discovery by battery
  enumeration"), and TOOLS.md §3 says the same of the confluent battery.
  Does the rule bind decider disprovers?  If it does: `fincm` produces
  from `CounterEmit.emit` only, `reject` from the T3 searcher only, and
  the enumeration `"enum"` is not registered as a decider disprover.  A
  small NEW check could tie each
  name in `Harness.tools` to an `Engines.registered` record with
  `mayDiscover := true`.
- **M4. The FRJW split.**  Option B (`Tm` and `FinCM` certificates,
  `checkClosed` inside the producer) or option A (the store as
  certificate, the closure check as the gate).  Recommendation: B.
- **M5. Decider certificates against store formats.**  The decider takes
  each tool's own certificate; the F0 store wants one format per relation
  (plan P2, D3: `DerivTree` for `⊢`, `FinCM` for `⊬`).  Before banking,
  `SubCM` needs a NEW untrusted translation to `FinCM` (re-checked), and a
  `⊢` answer from `subtab`, `g4c` or `frjw` must be re-proved by `ljfo`
  (no translation into `DerivTree` exists), or the store admits more than
  one format per relation.
- **M6. A budget for the subframe tableau, or last place** (§3, fact 1).
- **M7. lean-certify: one producer run per engine pair** (§3, fact 2).
  A v0.4 statement, if wanted.
- **M8. Promotion.**  The seven `wip/` modules of the `checkClosed` chain
  (into `FRJGbu`, or a new library), and `wip/t3_search.lean`.
- **M9. One `Holds`.**  To be agreed with the agent moving the subframe
  tableau (§1.2).
- **M10. Stale records in `tools/Engines.lean`** (found while reading, not
  changed): `ljfoProve` cites the fuelled `searchProves`, superseded by
  `checkDeriv`; `frjwRefute` gives completeness as OPEN, but
  `decideGbuW`, `frjw_complete` and `gbuw_complete` are PROVED; `frjRefute`
  (paper FRJ◯) gives completeness as OPEN, but it is REFUTED (#80, #81).
  The engine register is what RNDB cites, so it should be corrected
  before the comparison is recorded.

## 8 · Sources

Read for this document, all read-only:

- `origin/main` 0005006: `CertifyAdoption.lean`, `CertifyAdoption/*.lean`,
  `LaxLogic/PLL/Semantics/CountermodelEmit.lean`,
  `LaxLogic/PLL/Search/{Search, Run}.lean`, `LaxLogic/PLL/G4/{G4Term,
  G4Dec}.lean`, `LaxLogic/PLL/ND/{NDCore, Theorems, Terms}.lean`,
  `LaxLogic/Deriv.lean`, `LaxLogic/Util/Turnstile.lean`, `LJF/OCheckDeriv.lean`,
  `Reject/Cert.lean`, `wip/{ljfo_link, two_sided, t3_search, check_closed}.lean`
  and the imports of the `checkClosed` chain, `FRJ/CalculusW.lean`,
  `FRJ/Bridge.lean`, `FRJ/Search/{OpsW, Pin, Engine}.lean`,
  `FRJ/Gbu/{LaxND, W/LaxND, W/Closure, W/Saturate}.lean`, `tools/Decide.lean`,
  `tools/Engines.lean`, `lakefile.toml`, `TOOLS.md`, `docs/calculus-map.md`,
  `docs/certified-computation-findings-2026-10-09.md`,
  `docs/status-ledger.jsonl`, `Audit/Production.lean`.
- `origin/method-f0` 998510b: `METHOD-F0.md`,
  `docs/f0-reimplementation-plan.md`.
- lean-certify v0.3.0 (35ebd72): `LeanCertify/{Certifier, Decider, Config,
  Chunk}.lean`, `docs/deciders.md`, `docs/v0.3-statements.md`, `SKILL.md`.
- The subframe tableau (public since #74):
  `LaxLogic/PLL/SubTab/{Engine, Sound, Complete}.lean` and
  `tools/SubTab/Settings.lean`.

Import closures were computed by reading `import` lines (no build), and
axiom sets were taken from in-file pins or from `docs/status-ledger.jsonl`.

## 9 · Refresh of 2026-10-27 (F0 plan step 4)

What steps 1–3 of `docs/f0-reimplementation-plan.md` §6 and Matthew's gate
decisions of 2026-10-27 (`METHOD-F0.md` §3) have settled since §0–§8 were
written (2026-10-22, from `origin/main` 0005006).  Above this section only
the locations of the subframe tableau's files were brought up to date;
where the rest differs from this section, this section wins.  The record of step 4 itself is `docs/f0-step4-STATUS.md`.

### 9.1 What changed

* **The subframe tableau is public** (step 1, 2026-10-22).
  `PLLND.SubTab.engine`, its certifiers `yes` and `no`, the producer
  `SubTab.solve` and the finite-model enumeration are in the library
  `SubTab` (`LaxLogic/PLL/SubTab/`), a default target, whose import closure
  holds no `tools/` or `wip/` module (re-checked by step 3).  §2.1's
  statements are unchanged, and their pins are in
  `LaxLogic/PLL/SubTab/Sound.lean`.
* **One `Holds`** (§1.2; M1, M9).  The public tableau's

      PLLND.SubTab.Holds φ := Nonempty ([] ⊢ φ)        LaxLogic/PLL/SubTab/Sound.lean

  is the common specification.  No second `Holds` is defined: new
  certifiers are stated against this constant, so the registry needs no
  definitional identification of two constants.  It is a `def`, not an
  `abbrev`; proofs unfold it.  `Harness/Spec.lean` is not needed for it.
* **The parser** (§3) is `PLLTools.parseFormula : String → Except String
  PLLFormula` in `LaxLogic/PLL/Syntax/Parse.lean`, moved (not copied) from
  `tools/Decide.lean` by step 3 (#96), so its closure no longer reaches
  `Rewrite` or `wip/`.  It reaches `Classical.choice` through Lean core's
  `String.toList`, and its pin says so:

      #axioms_within parseFormula [propext, Classical.choice, Quot.sound]

  The parser is untrusted input handling, not a certifier: every
  certificate is checked against the formula the parser returned, so no
  answer's soundness depends on it.
* **D6** (step 3): the sorried `SemUI.amalgamation` moved out of
  `SemUILayered` to `wip/semUILayeredAmalgamation.lean`, and
  `collectAxioms` finds no `sorryAx` in the tableau's closure.  The reason
  §2.2 gave for not normalising with `Rewrite` (the sorried `SemUILayered`
  in its closure) no longer holds for that module.  `fincm` still does not
  use `Rewrite` (`Search.nf` suffices); the rest of `Rewrite`'s closure was
  not re-checked here.
* **M5 is settled** by plan D3 and Matthew's amendment of P2 (2026-10-27):
  during the comparison each engine uses its own certificate; after it,
  one format per relation is fixed, and not revisited until the system is
  reviewed or replaced.
* **G2** is approved subject to the choice of engines; statements that
  depend on an engine wait for G4.  The two certificates of step 4,
  `DerivTree` (`ljfo`) and `FinCM × Nat` (`fincm`), are Boolean-checked
  data, so no open decision affects them.

### 9.2 The decisions M1–M10

| | decision | status, 2026-10-27 |
|---|---|---|
| M1 | the common specification | **settled** in practice: `Spec := PLLFormula`, `Holds := PLLND.SubTab.Holds`; sequents through `deduction_iff` |
| M2 | type-checked certificates | **live**; it affects `g4c` and `frjw` only, which wait for Matthew |
| M3 | enumeration as a producer | **live**.  The new settings register `enum` exactly as `tools/SubTab/Settings.lean` already does; `fincm`'s producer uses the closure emitter only, not the frame battery; `reject` waits |
| M4 | the FRJW split | **live**; `frjw` waits |
| M5 | decider certificates against store formats | **settled** (above) |
| M6 | a budget for the tableau, or last place | **live**.  The provisional order keeps `subtab` first, as the existing settings do, so a pair after it is reached only after a REJECTED certificate (§3, fact 1) |
| M7 | lean-certify: one producer run per engine pair | **live**; lean-certify is still v0.3.0 |
| M8 | promotion of the `checkClosed` chain and of `t3_search` | **live**; waits with `frjw` and `reject` |
| M9 | one `Holds` | **settled**, with M1 |
| M10 | stale records in `tools/Engines.lean` | **partly settled**: `frjwRefute` and `frjRefute` were corrected by `aff2b9e` (status sweep, 2026-10-22); `ljfoProve` still cites the fuelled `searchProves`.  Not changed by step 4 |

### 9.3 The layout of §3: done, step 4, waiting

| part of §3 | status |
|---|---|
| `Holds` in `Harness/Spec.lean` | not needed (M9) |
| the parser moved out of `tools/Decide.lean` | **done** by step 3: `LaxLogic/PLL/Syntax/Parse.lean` |
| `subtab` registered "once the move has landed" | **done**: public since step 1, registered with `enum` by `tools/SubTab/Settings.lean` |
| `curry`, `curry_iff` | not built; the one-hypothesis case is `deduction_iff` at `Γ = []` |
| `Harness/Config.lean`, holding the moved `Harness.config` | step 4 decides: it is needed only if two `Harness.config` would share an environment |
| `Harness/Tools.lean`, `Harness/Settings.lean`, `Harness/Main.lean`, `lean_lib Harness`, `lean_exe plldecide` | step 4, with `fincm` and `ljfo` added to `subtab` and `enum` |
| pins in `CertifyAdoption/Regression.lean` for every new certifier | step 4 |
| `frjw`, `g4c`, `reject` | waiting (M2, M3, M4, M8) |

### 9.4 Step 4, as built (2026-10-27)

Recorded in full in `docs/f0-step4-STATUS.md`; in short:

* **Layout.**  `Harness/Statements.lean` (the statements, as `Prop`s,
  committed before the proofs), `Harness/Tools.lean` (the proofs, the
  certifiers `fincmNo` and `ljfoYes`, the disprover `fincm`, the prover
  `ljfo`, and a verbatim copy of `enum`), `Harness/Gates.lean` (exemplars
  and negative tests), `Harness/Settings.lean` (the one project-wide
  settings file), `Harness/Main.lean` (the entry point of `plldecide`);
  `lean_lib Harness` with explicit globs and `lean_exe plldecide`, both
  outside `defaultTargets`.  Namespace `PLLDecider`.
* **No new lemma.**  The statements of §2.2 and §2.4 are one-line instances
  of `FinCM.not_provable_of_check` and `LJFO.laxND_of_checkDeriv` at
  `Holds := PLLND.SubTab.Holds`, within `[propext, Quot.sound]`;
  `Nonempty ([φ] ⊢ ψ) ↔ Holds (φ ↠ ψ)` is `deduction_iff`, within
  `[propext]`.
* **`Harness/Config.lean` was not needed.**  `Harness.config` stays in
  `CertifyAdoption.lean`, reached through `CertifyAdoption.CheckDeriv`
  (where `emitTree` still lives); no environment holds two.  `Harness.tools`
  and `Harness.decider` are declared by both settings files, which therefore
  never share an environment; the old one is unchanged (G5).
* **The provisional order** keeps `subtabdecide`'s two pairs and appends
  (`ljfo`, `fincm`); the new pair is reached only after a REJECTED
  certificate (M6).
* **A finding for §3.**  In race mode lean-certify v0.3 returns at the
  deadline, but the other producer's thread runs on and the Lean runtime
  waits for it, so `deadlineSec` did not bound the process.  `plldecide`
  now exits as soon as it has printed its answer; a fix inside lean-certify
  is a question for Matthew beside M7.
