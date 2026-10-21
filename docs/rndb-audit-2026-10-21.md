# RNDB audit, 2026-10-21 (spike S1)

A read-only measurement of RNDB, the database of F0 = RN(◯,∅), the
variable-free fragment of PLL.  Nothing under `RNDB/`, `Rewrite/`, `wip/`
or `LaxLogic/` was changed.  Branch `rndb-audit`, cut from `origin/main`
at `1e1abe6`.

**How the numbers were produced.**  `tools/RNDBExport.lean` (new, built as
`lake build rndbexport`) walks `RNDB.allEntries` source list by source
list and checks that the walk is `allEntries` itself (same 1874 ids, same
order).  It writes one JSON row per entry, per frontier claim and per
representative to a JSON Lines file (not committed; see Reproduce), printing every
formula twice: raw, and through `Rewrite.canon`.  `scripts/rndb_audit.py`
reads that file plus the repository sources and computes everything
below.  Both gates were watched failing: `rndbexport --gate-watch` (a
printer without parentheses gives 388 collisions over 7496 printed
formulas; `pp` gives 0) and `rndb_audit.py --selftest` (10 planted faults,
10 detected).

**Keys.**  RAW is the printed syntax tree.  The printer is injective,
checked on all 696 distinct printed formulas against `Rewrite.keyF`.
CANON is `Rewrite.canon φ`, printed.  CANONFIX is CANON iterated to a
fixpoint (see finding 10).  Equal CANON keys imply interderivability,
because `Rewrite.canon_interd : Interd φ (canon φ)` is a theorem.  The
converse does not hold.

**Notation.**  Library notation: `↠` for implication, `¬A` for `A ↠ ⊥`,
`⊤` for `⊥ ↠ ⊥`.  `∧` binds tighter than `∨`, `∨` tighter than `↠`, and
`↠` associates to the right.  Displayed examples add parentheses where
they help.  `[φ] ⊬ ψ` is the claim `¬ Deriv [φ] ψ`, and ρ-names refer to
`LaxLogic/RN/Rho.lean`.

**Build note.**  The `.lake` seed predated the 2026-10-12 notation sweep of
`LaxLogic/Interd.lean` and `Deriv.lean`, so lake rebuilt 43 modules: the
RNDB, Certified and Rewrite modules, the dictionary `wip/` modules and
some `LaxLogic/` modules.  Every `#guard_msgs` pin in the twelve RNDB
modules the exporter imports (all of `RNDB/` except `Diamond.lean`, which
was not built) passed on current `main`.  That includes `RNDB.allEntries`
and `RNDB.allEntries_hold` at `[propext, Quot.sound]`.

## Headline numbers

| quantity | value |
|---|---|
| entries in `allEntries` | 1874 (`allEntries_length`, kernel-checked) |
| by relation | 1235 `nle`, 639 `interd`, **0 `le`** |
| by source | rho 185, dict R1 236, dict R2 82, frjCert 24, derived 321 (318 symm + 3 trans), esc 928, order 3, sep 95 |
| distinct claims (RAW key) | 1801; 72 clusters hold 73 surplus entries, all cross-source |
| distinct claims (CANON key) | 1680; 149 clusters hold 194 surplus entries, 21 of them within one source |
| distinct formulas in entries | 395 raw, 345 canonical (CANONFIX) |
| contradictions | **none** (see below) |
| duplicate ids | 0 |
| derived entries with a referential fault | 0 of 321 |
| `nle` entries without a scope | 0 |
| ρ-matrix cells banked | 304 of 462, all `⊬`; 0 of the 158 `⊢` cells |
| `frontier79` members already banked | **79 of 79** |
| `exampleFrontier` members already settled | 2 of 2 (1 as claimed, 1 against) |
| `frontierOrder` | empty |
| `canon` closes a dictionary cell on its own | 29 of 318 (9.1%) |

## Contradictions: none

No ALARM.  Under each of the three keys:

* no ordered pair carries both a positive entry and an `nle` entry, with
  `interd` counted in both directions;
* no `nle` entry relates two formulas with the same canonical form, starts
  at a formula whose canonical form is `⊥`, or ends at one whose canonical
  form is `⊤`;
* no `nle` entry has both sides in one interderivability class, where the
  classes are the union-find closure of all 639 `interd` entries.

There are no `le` entries, so a chain test through `⊢` had nothing to
check.  The selftest plants an `nle` against an `interd` pair, and an
`nle` across a two-step `interd` chain; both raise the alarm.

## Findings, ranked by severity

### High

**1. The `⊢` half of the order is not in the database.**  RNDB holds no
`Rel.le` entries at all; the only `le` value anywhere is the worked
example `rndb-0001` in `RNDB/Examples.lean`, which is not in
`allEntries`.  Of the 462 directed ρ-cells, 304 have an `nle` entry; the
158 `⊢` cells are "engine-certified" (`RNDB/Order.lean:226`).  They are
recomputed by `lake exe rhocover` at run time and are entries nowhere.
`RNDB/Order.lean` proves four of them as theorems, not entries:
`rho6_lt_rho12`, `rho6_lt_rho9`, `rho9_le_rho12` and `rho6_lt_rho13`.
Consequences:

* `Lt`, `CoversIn` and the Hasse diagram cannot be computed from the
  database.  The blueprint (`LaxBlueprint/Chapters/RN.lean`, definition
  `rn_order_def`) says of `CoversIn` that "the database can decide [it]
  from its own entries".  With the present data it cannot.
* The 639 positive entries are all `interd`, and none relates two
  distinct ρ representatives.

**2. `RNDB/Frontier79.lean` is entirely stale, and 11 of its members were
already banked when it was generated.**  All 79 claims
`⟨ρi, ρj, nle, rhoScope⟩` are backed by an entry with the same raw
`(lhs, rhs, nle)`: 68 by `sep-*` entries (added 2026-08-25) and 11 by
`esc-*` entries.  The esc wave was committed before the frontier
(`072ee1a`, then `738cf92`), so those 11 were never unsettled relative to
the database.  The generator checked freshness against the 185 `rho-*`
entries by ρ-index pairs, and the esc entries are keyed by q-formulas.
The 11 are frontier indices 5, 12, 21, 31–34, 60–62 and 76.  Example
(member #31, banked as `esc-0500`):

    [ρ13] ⊬ ρ4,   i.e.   [(¬¬◯⊥ ↠ ◯⊥) ↠ (◯⊥ ∨ ¬◯⊥)] ⊬ ◯⊥ ∨ ¬◯⊥

The file still says each member is "UNSETTLED RELATIVE TO THIS DATABASE:
no entry in `allEntries` backs it".  TOOLS.md §4 calls the frontier lists
"the record of what is unsettled".  `frontier79` is imported by nothing
except the new exporter.  The 79 claims are separately described as
FRJ(◯) incompleteness candidates; this audit does not assess that role,
only their status as open questions.

The worked `exampleFrontier` (`RNDB/Examples.lean`) is also settled.
Its first claim

    (◯⊥ ∨ ¬◯⊥) ∧ ((¬¬◯⊥ ↠ ◯⊥) ↠ ◯¬◯⊥)  ⊣⊢  ◯⊥ ∨ ¬◯⊥

is banked as `d2-0011` (with `ds-0247`).  Its second claim

    (◯¬◯⊥ ↠ (◯⊥ ∨ ¬◯⊥)) ∧ (¬¬◯⊥ ∨ (¬¬◯⊥ ↠ ◯⊥))  ⊣⊢  ◯¬◯⊥ ↠ (◯⊥ ∨ ¬◯⊥)

is REFUTED by `esc-0008`, which states

    [◯¬◯⊥ ↠ (◯⊥ ∨ ¬◯⊥)] ⊬ (◯¬◯⊥ ↠ (◯⊥ ∨ ¬◯⊥)) ∧ (¬¬◯⊥ ∨ (¬¬◯⊥ ↠ ◯⊥)).

**3. No content key, and two numberings of one formula set; lookups by
ρ-index miss banked cells.**  An entry carries its two formulas raw.  They
are written either through `RhoOrder.rhoF i` (rho, sep, order) or through
the q-representatives `RNReps.qk` (dict, esc, frjCert).  The two families
share 14 formulas under different indices, e.g. ρ5 = q6 = `¬¬◯⊥`,
ρ7 = q5 = `◯¬◯⊥`, ρ12 = q14, ρ14 = q15 (full map below).  Some escape
compounds ARE ρ-formulas: ρ13, ρ17, ρ19, ρ20 and ρ21 syntactically, and
ρ15, ρ16 and ρ18 after `canon`, which sorts the disjuncts.  Hence:

* 21 ρ-cells are banked ONLY by esc entries scoped to `RNReps.reps`.
  They are ρ1⊬ρ19, ρ1⊬ρ20, ρ1⊬ρ21, ρ8⊬ρ19, ρ10⊬ρ19, ρ11⊬ρ13, ρ11⊬ρ17,
  ρ13⊬ρ4, ρ13⊬ρ7, ρ13⊬ρ8, ρ13⊬ρ9, ρ13⊬ρ10, ρ13⊬ρ14, ρ17⊬ρ6, ρ17⊬ρ9,
  ρ17⊬ρ12, ρ19⊬ρ9, ρ20⊬ρ9, ρ21⊬ρ8, ρ21⊬ρ9 and ρ21⊬ρ10.
* `tools/frjv-sweep-check.py` builds its "banked ⊬" set with a regex for
  `(sepEntry|nleEntry|frjCertEntry|escEntry) "id" i j`.  That shape occurs
  only for `sepEntry` and `nleEntry`; `frjCertEntry` and `escEntry` take
  formulas, and the three `ord-*` entries are structures.  It therefore
  sees 280 of the 304 banked cells.  It misses those 21 plus ρ12⊬ρ9,
  ρ12⊬ρ15 and ρ13⊬ρ6.  A FRJV MISS on one of these 24 is reported as
  "unbanked" rather than as an incompleteness candidate.
* `tools/Cover.lean` (`rhocover`) matches the DB by syntactic equality
  with `rhoF i`.  That happens to cover all 304 today, because no cell is
  reachable only through `canon`.  It is correct by coincidence of
  syntax, not by construction.

### Medium

**4. The scope is stored by reference to lists that grow, and it means
different things in different sources.**

* `rhoScope := (List.range RhoOrder.n).map RhoOrder.rhoF`
  (`RNDB/RhoEntries.lean`) and `RNReps.reps` (append-only) are
  definitions, and every claim's `scope` is the term `some rhoScope` or
  `some RNReps.reps`.  When R gains a class ρ22, every existing ρ-entry's
  recorded scope becomes the 23-list on the next build.  The same happens
  to the q-entries when `reps` is appended.  This is the provenance the
  schema's `scope` field exists to keep (`RNDB/Types.lean`, the
  `q0…q14` / `q0…q15` example).  The exporter therefore records the
  length (22 and 16 today) next to the name.
* For the 283 ρ-scoped `nle` entries, both sides are members of the
  scope.  For the 952 entries scoped to `RNReps.reps` (esc 928, frjCert
  24), exactly one side is: a representative against a compound.  The
  field records "asked against" in two senses.
* `Claim.Holds` for `nle` is `¬ Deriv [lhs] rhs`, which does not mention
  the scope.  The scope matters only to aggregate statements such as "the
  compound escapes all 16", which no single entry states.  The esc
  decomposition is complete for that purpose: each of the 58 compounds
  has exactly one row per q-representative.
* 952 of the 1235 `nle` entries name the 16-representative list.  R is
  the reference set (CLAUDE.md rule 3), and that list is internal
  plumbing.

**5. Seven of the eight generated data files have no generator in the
repository.**  Eight RNDB data files say "GENERATED" in their header;
three of them (Rho, Dict, Dict2) also say "regenerate rather than
hand-edit".  Only `RNDB/SepEntries.lean` has an emitter in the tree:
`lake exe rhocover emit`, which prints `ENT|` lines (`tools/Cover.lean:118`).
`tools/BankRho.lean` generates the certificates in
`Certified/RhoRefutations.lean`, but not the `RNDB/RhoEntries.lean`
wrapper.  There is nothing to regenerate Dict, Dict2, FRJCert, Derived,
Esc or Frontier79 with.  `RNDB/Order.lean` is hand-written and says so.

**6. The import closure of `RNDB.DB` reaches 15 `wip/` modules and four
sorried declarations; no entry is tainted.**  By static import analysis,
`RNDB.DB` has 101 in-repo modules in its closure, 15 of them in `wip/`:
`canonFinC`, `crankC`, `residueGrowth`, `rnDict`, `rnDict2`,
`rnDict2Hand`, `rnDictBase`, `rnDictRefute`, `rnFRJCerts`, `rnSep`,
`rnSepColl`, `semui_char`, `semui_henkin`, `stabilise` and `witTripleC`.

* They enter through `DictEntries` → `wip.rnDict` → `wip.stabilise` →
  {`wip.witTripleC` → `wip.semui_henkin`, `wip.semui_char`}, through
  `Dict2Entries` → `wip.rnDict2`, and through `FRJCertEntries` →
  `wip.rnFRJCerts`.
* Sorried declarations in the closure, from the build's own warnings:
  `wip/semui_henkin.lean:338` and `:349`, `wip/semui_char.lean:285`, and
  `LaxLogic/PLL/SemUI/SemUILayered.lean:821` (`amalgamation`).  The last
  is a library module, against CLAUDE.md rule 1, and it is also in the
  closure of `Rewrite.Canon`.
* Taint: none.  The pins on `allEntries` (`[propext, Quot.sound]`) passed
  in this build.
* 663 entries (dict 318, frjCert 24, derived 321) cite certificates that
  live in `wip/`.  The other 1211 (rho, sep, order, esc) close
  `wip`-free.
* All 24 frjCert entries duplicate an esc entry exactly (finding 9).  So
  `FRJCertEntries`, which pulls `wip.rnFRJCerts`, `tools.Bank` and
  `FRJ.Bridge` into the closure, contributes corroboration and no new
  claim.

**7. Referential integrity is enforced by no one but an external check;
ids are positional.**  `Evidence.derived` names its parents as strings,
and the kernel checks only `ps.length = rule.arity`.  The `ok` proof is
built from the dictionary theorem directly, so a wrong parent id
mislabels provenance silently.  Today all 321 derived entries are sound:

* every parent exists and precedes its child;
* every parent is `interd`, and every arity is right;
* every `symm` child is its parent reversed, and every `trans` child
  chains its two parents;
* each of the 318 dictionary entries has exactly one `symm` child.

The ids are generation-order serials (`rho-0000`…, `sep-1`…,
`d1-0000`…), not functions of the claim.  Regenerating a file in a
different order would renumber it and orphan the parent references.

### Low

**8. Documentation drift.**

* `RNDB/DB.lean:6` says "1,776 kernel-checked dictionary facts", and its
  table omits `orderEntries` (3) and `sepEntries` (95).  The kernel-checked
  `allEntries_length` in the same file says 1874.
* `README.md:192` and `docs/certified-computation-findings-2026-10-09.md:50`
  repeat 1,776.
* `RNDB/Types.lean` (header) says `wip/rnDict.lean` "states 323 cell
  theorems of which 87 are … `sorry`".  That file now has 0 `sorry`
  tokens in code; its closure layer was deleted on 2026-08-25.
* `RNDB/Examples.lean` still calls `wip/rnDict.lean` "sorried".
* The `frontier79` header: see finding 2.

`TOOLS.md` ("1874") and `docs/rn-catalogue.html` ("1874"; "304 ⊬") agree
with the data.

**9. Duplicates (deliberate, quantified).**  `RNDB/DB.lean` permits
cross-source duplicates as corroboration.

* Under RAW keys there are 72 clusters, all cross-source:
  * esc+rho: 47;
  * esc+frjCert: 23;
  * esc+frjCert+rho: 1;
  * esc+order: 1.

  Every frjCert entry and 48 rho entries are restated by esc.  Example:
  `rho-0011` and `esc-0497` both state

      [⊤] ⊬ (¬¬◯⊥ ↠ ◯⊥) ↠ (◯⊥ ∨ ¬◯⊥).

* Under CANON keys there are 149 clusters.  21 of them lie within a
  single source; these are dictionary cells that differ only by
  associativity or commutativity of `∨`.  Example: `d1-0197`, `d1-0213`
  and `d1-0214` state respectively

      ◯⊥ ∨ (¬◯⊥ ∨ ¬¬◯⊥)  ⊣⊢  ¬◯⊥ ∨ ¬¬◯⊥
      (◯⊥ ∨ ¬◯⊥) ∨ ¬¬◯⊥  ⊣⊢  ¬◯⊥ ∨ ¬¬◯⊥
      (◯⊥ ∨ ¬◯⊥) ∨ (¬◯⊥ ∨ ¬¬◯⊥)  ⊣⊢  ¬◯⊥ ∨ ¬¬◯⊥

* 49 ρ-cells are banked more than once.  The recorded `worlds` agrees
  with the inline model's size on all 928 esc entries.

**10. `canon` is not idempotent on one formula.**

    ◯(◯⊥ ∨ ¬◯⊥)  ↦canon  ◯(¬◯⊥ ∨ ⊥)  ↦canon  ◯¬◯⊥

`stripBox` turns the inner `◯⊥` into `⊥` inside a disjunction that has
already been built, so `⊥ ∨ ψ = ψ` is not applied in the same pass.  This
is the case the `Rewrite.canon` docstring describes ("`simpIter`
re-canonicalises").  It affects 2 entries (`d1-0066`, `ds-0066`): under
CANONFIX their cell `◯(◯⊥ ∨ ¬◯⊥) ⊣⊢ ◯¬◯⊥` closes, and under CANON it does
not.

**11. Id formats are inconsistent.**  `rho-NNNN` and `esc-NNNN` are
zero-padded; `sep-N` is not; `ord-000N` is padded; the trans entries are
`dt-t_w1_w3` and so on, which embed names; the examples use `rndb-000N`.
All 1874 ids are distinct.  The ids are deliberately NOT renamed.  An id,
once issued, is a stable identity: `Evidence.derived` cites ids as
parents, and the append-only rule forbids reusing or changing one.  The
inconsistency is recorded here instead of repaired.

## Is `canon` a usable key?

* **As a sound deduplication key: yes, after iterating to a fixpoint.**
  It never puts two relations on one ordered pair: 0 pairs under CANON or
  CANONFIX.  Every merge it makes is an interderivability, since
  `canon_interd` is a theorem.  It maps 77 distinct raw formulas onto 27
  values.  Of its 149 duplicate clusters, 77 group claims whose raw syntax
  differs, which the RAW key cannot see.  Example:
  ρ15 = `(◯¬◯⊥ ↠ (◯⊥ ∨ ¬◯⊥)) ∨ ◯¬◯⊥` and the escape compound
  `◯¬◯⊥ ∨ (◯¬◯⊥ ↠ (◯⊥ ∨ ¬◯⊥))` get one key.  Use CANONFIX, not one pass:
  finding 10.
* **As a key for interderivability classes: no.**  Of the 639 `interd`
  entries, 581 (90.9%) relate formulas with different CANON keys (579
  under CANONFIX).  Of the 318 dictionary cells, `canon` closes 29 on its
  own (30 under CANONFIX).  Over the union-find classes of the `interd`
  entries there are 74 classes:
  * 58 hold a single canonical form;
  * the other 16 are exactly the 16 q-classes, and they split into
    between 4 and 65 canonical forms each;
  * the largest is the class of `⊤`, with 65 forms.

  Typical misses are laws outside `canon`'s list:
  * absorption: `d1-0000`,
    `(¬¬◯⊥ ↠ ◯⊥) ∧ (¬¬◯⊥ ∨ (¬¬◯⊥ ↠ ◯⊥)) ⊣⊢ ¬¬◯⊥ ↠ ◯⊥`;
  * contradiction: `d1-0008`, `◯⊥ ∧ ¬◯⊥ ⊣⊢ ⊥`;
  * every collapse that needs PLL reasoning rather than lattice
    normalisation.

  Where it succeeds, it is mostly through the `◯⊥` absorber.  Example:
  `d1-0003`, `◯⊥ ∧ (¬¬◯⊥ ↠ ◯⊥) ⊣⊢ ◯⊥`.
* **Representatives under canon.**  The 22 ρ have 22 distinct canonical
  forms, and the 16 q have 16.  The 14 shared formulas coincide, as they
  must.

Every dictionary cell has a representative as its right-hand side
(318/318).  The class key that exists in the data is therefore "the
representative a dictionary cell names", obtained by union-find over
`interd` entries.  It is not anything `canon` computes.

## Formulas that are not representatives

395 distinct raw formulas occur in entries.

* **24** are representatives: 22 ρ and 16 q, 14 of them shared.
* **301** are linked to a ρ-class, through equal CANONFIX keys or
  `interd` entries.
* **20** are linked only to q12 = `◯(¬◯⊥ ∨ ¬¬◯⊥)` or
  q13 = `◯(◯¬◯⊥ ↠ (◯⊥ ∨ ¬◯⊥))`.  These are the two q-representatives
  without a ρ twin, and no entry in the database relates either of them
  to any ρ.
* **50** are linked to no representative.  All 50 are escape compounds:
  35 occur in esc only, and 15 in esc and frjCert.  Example:
  `(¬¬◯⊥ ↠ ◯⊥) ∧ ◯(◯¬◯⊥ ↠ (◯⊥ ∨ ¬◯⊥))`.  The database records that each
  lies in none of the 16 q-classes.  It does not record whether any lies
  in R.

  Of the 58 escape compounds, 8 are ρ-formulas:
  * syntactically: ρ13, ρ17, ρ19, ρ20 and ρ21;
  * after `canon`: ρ15, ρ16 and ρ18.

## The ρ ↔ q cross-map (syntactic identity)

| ρ | formula | q |
|---|---|---|
| ρ0 | `⊥` | q0 |
| ρ1 | `⊤` | q1 |
| ρ2 | `◯⊥` | q2 |
| ρ3 | `¬◯⊥` | q3 |
| ρ4 | `◯⊥ ∨ ¬◯⊥` | q4 |
| ρ5 | `¬¬◯⊥` | q6 |
| ρ6 | `¬◯⊥ ∨ ¬¬◯⊥` | q7 |
| ρ7 | `◯¬◯⊥` | q5 |
| ρ8 | `¬¬◯⊥ ↠ ◯⊥` | q10 |
| ρ9 | `◯¬◯⊥ ∨ ¬¬◯⊥` | q9 |
| ρ10 | `¬¬◯⊥ ∨ (¬¬◯⊥ ↠ ◯⊥)` | q11 |
| ρ11 | `◯¬◯⊥ ↠ (◯⊥ ∨ ¬◯⊥)` | q8 |
| ρ12 | `(¬¬◯⊥ ↠ ◯⊥) ↠ ◯¬◯⊥` | q14 |
| ρ13 | `(¬¬◯⊥ ↠ ◯⊥) ↠ (◯⊥ ∨ ¬◯⊥)` | — |
| ρ14 | `(◯¬◯⊥ ∨ ¬¬◯⊥) ↠ (◯⊥ ∨ ¬◯⊥)` | q15 |
| ρ15 | `(◯¬◯⊥ ↠ (◯⊥ ∨ ¬◯⊥)) ∨ ◯¬◯⊥` | — |
| ρ16 | `((◯¬◯⊥ ∨ ¬¬◯⊥) ↠ (◯⊥ ∨ ¬◯⊥)) ∨ ◯¬◯⊥` | — |
| ρ17 | `¬¬◯⊥ ∨ ((◯¬◯⊥ ∨ ¬¬◯⊥) ↠ (◯⊥ ∨ ¬◯⊥))` | — |
| ρ18 | `((◯¬◯⊥ ∨ ¬¬◯⊥) ↠ (◯⊥ ∨ ¬◯⊥)) ∨ (◯¬◯⊥ ∨ ¬¬◯⊥)` | — |
| ρ19 | `(◯¬◯⊥ ↠ (◯⊥ ∨ ¬◯⊥)) ↠ ◯¬◯⊥` | — |
| ρ20 | `(◯¬◯⊥ ↠ (◯⊥ ∨ ¬◯⊥)) ↠ (¬◯⊥ ∨ ¬¬◯⊥)` | — |
| ρ21 | `((◯¬◯⊥ ∨ ¬¬◯⊥) ↠ (◯⊥ ∨ ¬◯⊥)) ↠ ◯¬◯⊥` | — |
| — | `◯(¬◯⊥ ∨ ¬¬◯⊥)` | q12 |
| — | `◯(◯¬◯⊥ ↠ (◯⊥ ∨ ¬◯⊥))` | q13 |

Indices agree only for 0–4 and 9.

## ρ-matrix coverage

The 304 `⊬` cells are covered as follows:

| covered by | cells |
|---|---|
| rho only | 137 |
| sep only | 95 |
| esc and rho | 47 |
| esc only | 21 |
| order only | 2 |
| esc, frjCert and rho | 1 |
| esc and order | 1 |

By recorded scope:

* entries scoped to `rhoScope` only: 234 cells;
* both scopes: 49;
* `RNReps.reps` only: 21.

No cell is reached only through `canon`.  The 158 `⊢` cells have no
entries (finding 1).

## Reproduce

    lake build rndbexport
    gtimeout 300 .lake/build/bin/rndbexport _out/rndb-export.jsonl
    gtimeout 300 .lake/build/bin/rndbexport --gate-watch
    python3 -I scripts/rndb_audit.py --export _out/rndb-export.jsonl --repo . \
        --summary _out/rndb-audit-summary.json
    python3 -I scripts/rndb_audit.py --export _out/rndb-export.jsonl --repo . --selftest

The export itself is not committed: it is about 0.9 MB and is derived
data.  Regenerate it with the first two commands.  The output is
deterministic (two runs were byte-identical).  At `1e1abe6` it has 1998
rows:

* 1874 `entry` rows;
* 4 `example_entry` rows;
* 81 `frontier` rows;
* 38 `rep` rows;
* 1 `meta` row.

## Corrections made with this audit (branch `rndb-tidy`, 2026-10-21)

The statements of current state that the findings showed to be stale
were corrected:

* `RNDB/DB.lean` header: 1,874, with the order and sep rows in the table.
* `README.md`: the RNDB sentence.
* `RNDB/Types.lean` header: the `wip/rnDict.lean` sorry count is now 0.
* `TOOLS.md` §4: the description of the frontier lists, and a row registering the audit tools (also added to `tools/tools-register.sh`).
* `RNDB/Frontier79.lean` header: all 79 members are banked; the comment
  table maps each member to its banking entry.  The list itself is kept
  unchanged.

Dated records, such as `docs/certified-computation-findings-2026-10-09.md`,
are not rewritten; that one gets a one-line dated note at its end.

Not changed here: `RNDB/Examples.lean`.  Its header still calls `wip/rnDict.lean` sorried, and the `exampleFrontier` docstring still presents its two claims as open; findings 2 and 8 record both.
