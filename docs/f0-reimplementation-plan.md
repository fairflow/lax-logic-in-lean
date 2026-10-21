# Re-implementing the F0 database: a plan

**A note to us both (Matthew and Claude), 2026-10-21.  DRAFT, binding
nothing until Matthew has approved §3 and the decisions in §8.**
Companion to `METHOD-F0.md`, which sets the method this plan follows.
The evidence is the S1 audit, `docs/rndb-audit-2026-10-21.md`
(branch `rndb-audit`, 32c33eb).

Matthew's verdict: what is currently built for F0 is a mess and basically
unworkable.  The audit agrees, and §1 says why in terms of causes rather
than symptoms.  The plan is to build a new library beside the old one, on
the principles of §3.  It is to be fed from the existing producers, and it
replaces the old one only when it answers every question the old one
answers (gate G5).  **Nothing existing is removed or rewritten** by this
plan, apart from the documentation fixes in the tidy-up PR.

## 1 · Why the current build is unworkable

What is right and should be kept: entries carry proofs (`Entry.ok`), so
an unproved entry cannot be written; and open questions are data
(`Frontier`), never sorried theorems.  The problems are in everything
around that.

1. **Truth is spread over at least four places that do not know about
   each other.**
   * RNDB: 1874 entries.
   * The ground rewrite set `Rewrite.fullSetC`: 681 rules, each an
     `Interd` proof between two closed formulas.  It is a second table of
     facts, maintained separately and not derived from RNDB.
   * The 158 `⊢` cells of the ρ-order: recomputed by `rhocover` at run
     time and stored nowhere.
   * The frontier lists, which are all stale.
2. **The order is not stored, and derived facts are.**  There are 0 `le`
   entries, so the order, the covers and the Hasse diagram cannot be
   computed from the database.  Meanwhile 321 entries are `symm`/`trans`
   consequences of other entries, linked to their parents by string ids
   that only an external script checks.
3. **No identity.**  Formulas are stored raw, under two numberings (ρ and
   q) that agree only on 0–4 and 9.  Tools that look up by index miss
   facts: `frjv-sweep-check.py` misses 24 of the 304 banked `⊬` cells.
   `canon` is not idempotent.  It is sound as a key for removing
   duplicates, but it is not a class key: 581 of the 639 `interd` entries
   relate different canonical forms.
4. **Every source proves its entries its own way**, so every source drags
   in its own dependencies.  There are three countermodel formats alone:
   * esc entries carry an inline `FinCM` model;
   * rho entries cite `FRJ.Search.Tab` models in
     `Certified/RhoRefutations.lean`;
   * sep entries cite the confluent-battery models of
     `Certified/RhoSeparations.lean`.

   The interderivabilities cite theorems in `wip/`.  The closure of
   `RNDB.DB` reaches 15 `wip/` modules and 4 sorried declarations.  One
   of them is the library theorem `SemUILayered.amalgamation`, which is
   also imported by `Rewrite/Core.lean`.
5. **Scope by reference.**  A negative entry's scope is the term
   `rhoScope` or `RNReps.reps`, whose value grows whenever R grows.  So
   the recorded scope of an old verdict silently changes on the next
   build.
6. **Data with no generator.**  Seven of the eight GENERATED entry files
   have no generator in the repository, so they cannot be regenerated,
   checked against a regeneration, or extended consistently.  Ids are
   generation-order serials, so a regeneration in another order would
   renumber the entries and orphan the parent references.
7. **Tool sprawl.**  Twelve executables on main read or write F0 data:
   * `rhocover`, `rcellsgen`, `rnpin`, `frjcert` and `frjvrun`;
   * `wscreen`, `checkprobe`, `pll` and `twosided`;
   * `rwscreen`, `rnDictGen` and `rnextend`.

   Each has its own view of what is known.  There is no single question
   "what do we know about φ and ψ, and how?" with a single answer.

## 2 · What the new library is for

Pending §1 of `METHOD-F0.md` (Matthew's vision), the working assumption is
one service.  For closed formulas φ, ψ:

    ask φ ψ  ∈  { [φ] ⊢ ψ with a certificate,  [φ] ⊬ ψ with a certificate,  unknown }

It must be answered from what is known where possible, and by a bounded
certified search otherwise.  The answer is added to what is known.  The
order, the covers, the class of a formula, the ground rewrite table and
the catalogue page are all computed from the stored facts and are never
stored as authorities.  The users are proofs in Lean (a certificate
becomes a term), agents (a fast query), and Matthew (the catalogue,
generated).

## 3 · Principles

Each principle answers one or more causes in §1.  They specialise
METHOD-F0.md §2 and CLAUDE.md rules 1, 3, 4 and 9.

**P1. One store of base facts; everything else computed.**  There are two
kinds of base fact:

    [φ] ⊢ ψ        [φ] ⊬ ψ

Interderivability is `⊢` both ways.  The order, covers, classes,
transitive consequences and the ground rewrite table are queries over the
store, never rows.  (Answers §1.1, §1.2.)

**P2. One certificate format per relation, one verified checker.**  Both
checkers exist on main, in library modules, choice-free:

    LJFO.laxND_of_checkDeriv :
        checkDeriv (decideSeq Γ φ) t = true  →  Nonempty (LaxND Γ φ)
                                        (LJF/OCheckDeriv.lean, [propext, Quot.sound])

    FinCM.not_provable_of_check :
        FinCM.checkB M w Γ C = true  →  Γ ⊬ C
                                        (LaxLogic/PLL/Semantics/CountermodelEmit.lean,
                                         within [propext, Quot.sound]: the esc entries
                                         use it, and RNDB.allEntries is pinned there)

A row is `(fact, certificate)`, with the certificate an LJF◯ derivation
tree for `⊢` and a finite constraint model with a world for `⊬`.  One
function

    check : Fact → Cert → Bool

with one theorem

    check_sound :  check f c = true  →  f.Holds

certifies every row.  A file of rows is certified by one kernel
evaluation of `rows.all (fun r => check r.fact r.cert) = true`.  No row
cites a theorem from elsewhere, so the store's import closure is the two
checkers and nothing else.  This is the pattern `lean-certify` packages
(untrusted producer, verified checker), and the repo has already adopted
it.  (Answers §1.4.)

**P3. Identity by content; one list of accepted forms.**  A formula's
identity key is its printed canonical form, computed by `canon` iterated
to a fixpoint.  **The key is an index, not evidence**: equal keys locate
rows, and they certify nothing.  There are two reasons, both found by S2:
* `Rewrite.canon_interd` depends on `Classical.choice`;
* `Rewrite/` imports the sorried `SemUILayered`.

So `canon` enters the new library only as a computation, moved out of
`Rewrite/`.  Where a stored formula needs `φ ⊣⊢ canonFix φ`, that is two
certified `⊢` rows like any others.  The class representatives are one list with stable names that are never
reused, decided by Matthew at gate G3.  The ρ- and q-numberings become
alias tables into that list.  Infinite families (the Rieger–Nishimura
ladder rungs) are named by a parameter, not by an index into a growing
list.  (Answers §1.3.  Spike S2 is the proposal.)

**P4. Append-only identities.**  A row's id is a function of its fact,
not of the order of generation.  A manifest of issued ids only ever
grows, and CI checks that the new manifest extends the old one.  A row
that is wrong or superseded is marked retired, with a reason; it is
never deleted.  (Answers §1.6.)

**P5. Every data file is generated and regenerable.**  Rows live in
generated Lean files, sorted by id, written by one committed generator.
CI regenerates and diffs.  JSONL and SQLite exports for agents and pages
are derived from the rows and are never the authority.  (Answers §1.6.)

**P6. A clean closure, gated.**  The new library imports library modules
only: no `wip/`, and no sorried declaration anywhere in its closure.  An
`#axiom_sweep` over its modules, allowing `[propext, Quot.sound]`, is
checked in CI.  If the congruence lemmas for `Interd` are needed, they
are hoisted into `LaxLogic/Interd.lean`, as `Deriv`/`Interd` were on
2026-08-24, rather than imported from the semantic-UI chain.
(Answers §1.4.)

**P7. Base facts are absolute; scope belongs to aggregate claims.**
`[φ] ⊬ ψ` is true or false whatever the representative list is, so a
base fact carries no scope.  A statement that is relative to a list,
such as "φ is interderivable with none of the representatives", names a
frozen version of that list by value, never a definition that grows.
This reverses a deliberate choice of `RNDB/Types.lean`, so it needs
Matthew's word (§8, D4).  (Answers §1.5.)

**P8. Every answer certified or unknown.**  `ask` tries strategies in a
fixed order and returns the first certified answer:

1. lookup by identity key;
2. order reasoning over stored facts;
3. normalisation to representatives;
4. bounded search by the existing producers, with the result checked and
   then banked as a new row.

A search that finds nothing returns `unknown`, never `⊬` (the lesson of
the G4c failure memo, #70).

**P9. Fragment first** (CLAUDE.md rule 8).  The ◯-free part of F0 is the
two-element algebra: every closed IPC formula is interderivable with `⊥`
or with `⊤`.  Every layer is built and run end to end there first, and on
that fragment `ask` must never return `unknown`.  Any `unknown` there is
a defect, which makes it a sharp smoke test.

**P10. One front end, measured.**  One executable, `f0`, with
subcommands (`ask`, `bank`, `regen`, `export`, `measure`), registered in
TOOLS.md.  Coverage is measured on designed test sets (rule 9) and
reported per METHOD-F0.md §5.

## 4 · Architecture

Four layers.  Each depends only on the layers before it.

| layer | contents | depends on |
|---|---|---|
| L0 identity | closed formulas; `canonFix`; the printed key, an index only; the list of accepted forms and its alias tables | `LaxLogic/Interd.lean`; `canon` as a computation, moved out of `Rewrite/` (P3, P6) |
| L1 certificates | `Fact`, `Cert`, `check`, `check_sound` | L0, `LJF/OCheckDeriv.lean`, `CountermodelEmit.lean` |
| L2 store | generated row files, each with its one kernel evaluation; the id manifest; retirements; exports | L1 |
| L3 query | `ask`, with the four strategies of P8; class of a formula; order, covers and Hasse diagram as computed views; generation of the ground rewrite table | L2, and the producers, which are untrusted |
| L4 products | the catalogue page and explorer, generated from exports; the harness search index (spike S3) | L3 |

**Order reasoning without new lemmas.**  From stored facts

    [φ'] ⊬ ψ',   [φ'] ⊢ φ,   [ψ] ⊢ ψ'

it follows that `[φ] ⊬ ψ`.  The countermodel of the first fact refutes
the new pair too, so the derived answer carries the same model, which
`check` re-checks against `(φ, ψ)`.  `⊢` chains compose by cut into a
`LaxND` term.  Nothing derived is stored.

**Producers.**  These are the existing engines, used through the
lean-certify v0.3 decider settings, which name a prover, a disprover and
fallback pairs:
* the LJF◯ tree emitter;
* the FinCM emitter;
* the FRJW engine with `checkClosed`.

No new engine is built under this plan.  `checkClosed` lives in `wip/`.
It is a producer here, not part of the checked base, so the store does
not import it.

## 5 · Migration: import, then compare, then decide

The old RNDB, `Rewrite/`, the frontier files and the twelve executables
stay as they are and keep building.

1. **Import.**  A one-off importer reads the RNDB export (the S1
   exporter) and, for each entry:
   * an `nle` entry becomes a `⊬` row with a `FinCM` model.  The esc
     models are taken as they are.  The rho (`Tab`) and sep (battery)
     models are converted by an untrusted translation, and the result is
     re-checked by `FinCM.checkB`.  If a conversion fails, the FinCM
     emitter is run on the pair instead, and the case is reported;
   * an `interd` entry becomes two `⊢` rows, each certificate produced by
     the LJF◯ tree emitter;
   * a `symm`/`trans` entry becomes nothing: it is a query.

   The same is done for the 681 rules of `fullSetC` and for the 158 `⊢`
   ρ-cells.
2. **Parity report.**  For every old entry, rewrite rule and ρ-cell, the
   report gives the new `ask` answer and its time.  Anything not answered
   is listed by name.
3. **Gate G5.**  With the parity report in hand, Matthew decides item by
   item what is marked superseded in TOOLS.md.  Superseded means a
   pointer, not a deletion.  Until then the old `fullSetC` stays the
   normaliser of record for the probes and the proving harness.

## 6 · Phases

Each phase names its gate and its deliverable.  Spikes are at most half a
day and end in a written result.

| phase | work | gate | deliverable |
|---|---|---|---|
| A (S2 done; awaiting G3) | S2: accepted forms and keys, measured on the old data | G3 | `docs/f0-accepted-forms-proposal.md` |
| A | Matthew: METHOD-F0 §1 and §8; the decisions of §8 below | G1 | edits to METHOD-F0.md |
| B | S4: certificate cost.  On designed rows, measure kernel time for one `rows.all check` evaluation against per-row theorems, LJF◯ tree sizes on the hardest ⊢ cells (the `f := 44` cell ρ11 ∨ ρ18 ≡ ρ15), and FinCM model sizes.  Pin the transitive closure and axioms of both checkers | — | spike report |
| C | Statements of L0–L1: `Fact`, `Cert`, `check`, `check_sound`, `canonFix` with its theorem, the key's injectivity, the form of `ask`'s answer | G2 | statements document, displayed formulas, `sorry`-free stubs only as typed parameters |
| D | L0–L2 on the ◯-free fragment, end to end, with CI gates watched failing; then F0 | — | PR: new library, generator, manifest, gates |
| E | S5: import dry run of §5.1 on a designed sample, before the full import | — | spike report |
| F | Full import and the parity report | — | PR, report |
| G | L3 `ask`; coverage on a designed test set fixed in advance | G4 | PR, coverage report |
| H | L4: generated catalogue; ground rewrite table generated from rows, screened by `rwscreen` against `fullSetC`; S3 harness index | G6 for any Pages run | PRs |
| I | Supersession decisions | G5 | TOOLS.md pointers |
| later | F1, the one-variable fragment | G1 | — |

Phases B and C do not wait for G3: base facts relate formulas, not
classes, so L1 and L2 are independent of the choice of representatives.
Only L3's class key needs G3.

## 7 · Risks, and how each is checked

* **Kernel cost of checking thousands of rows.**  Measured in S4 before
  any design depends on it.  The fallbacks are chunked files, each with
  its own evaluation, or a theorem per row.
* **Proof certificates may be large for the hardest cells.**  Measured in
  S4.  `checkDeriv` was under 40 ms per direction on the `f := 44` cell
  (TOOLS.md §8), which is encouraging but is one cell.
* **The LJF◯ emitter may fail on some imported interderivabilities**
  within budget.  Such a cell is listed in the parity report as
  `unknown`, never dropped.  The old proof stays in RNDB until G5.
* **`canon` is not idempotent** (S1, finding 10).  The plan uses
  `canonFix`; whether to repair `canon` itself is a separate small PR.
* **`canon`'s soundness uses choice** (S2, §3.1).  `canon_interd` is
  pinned at `[propext, Classical.choice, Quot.sound]`.  The first draft
  of this plan used it as L0's certificate.  It has been corrected to
  use the key as an index only (P3).  A choice-free `canon_interd` would
  restore equal keys as evidence; that is S2's Q4.
* **Drift.**  Each phase's report sets its work against §2 and METHOD-F0
  §1 (METHOD-F0.md §5, drift), and anything mapping to no goal is flagged.

## 8 · Decisions needed from Matthew

* **D1.**  The principles of §3: approve, amend or strike.
* **D2.**  The name and place of the new library.  The proposal is a
  top-level `F0/` with namespace `F0`, a new `lean_lib`, outside
  `defaultTargets` until G5.
* **D3.**  The certificate formats.  The recommendation is LJF◯ trees for
  `⊢` (fuel-free, checker on main, carried to `LaxND` by `bridge_iff`)
  and FinCM models for `⊬`.  The alternative is `LaxND` terms for `⊢`,
  which uses the reference calculus directly but has no Boolean checker
  today.
* **D4.**  P7: base facts without scope, with scope kept only on
  aggregate claims and by value.
* **D5.**  The accepted forms and keys, at G3.  S2's proposal is
  `docs/f0-accepted-forms-proposal.md` (branch `f0-forms-s2`, 6ff5f88).
  Its questions Q1–Q9, each with a default, are the G3 decisions.
* **D6.**  The sorried library theorem `SemUILayered.amalgamation`.  The
  new library does not need it (P6), but `Rewrite/Core.lean` imports its
  module, so the old normaliser's closure keeps it until you decide.
