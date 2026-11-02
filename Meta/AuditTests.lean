/-
Regression tests for the dependence queries of `Meta/Audit.lean`, 2026-11-02.

Until 2026-11-02 `dependsOn c n` was `c ∈ collectAxioms n`, which is right
only when `c` is an axiom: `collectAxioms` follows every path but reports
only the axioms at its ends.  Asked about a theorem, `#axiom_path` said
"does not depend" whatever the facts.  The S1 realizers study (PR #118)
met it on `baseCriterion` → `ts_realizes` (`wip/f0Endpoints.lean`).

The cells below are designed, one per way the query can go wrong:

| query                       | the facts                                   | expected |
|-----------------------------|---------------------------------------------|----------|
| `#uses base realizes`       | the proof of `base` cites `realizes`; no axiom anywhere (the false negative) | true  |
| `#uses t2 d0`               | `t2`'s type names `d2`, `d2 := d1 + 1`, `d1 := d0 + 1`: three steps, through a type | true  |
| `#uses shareA shareB`       | both use `propext`, neither cites the other  | false |
| `#uses realizes base`       | the converse of the first row                | false |

With `#uses` running on the old `dependsOn` the two `true` rows printed
`false` (watched, 2026-11-02).  The two `false` rows were watched failing
under two mutants of the fix: answering by shared axioms (`shareA`/`shareB`
printed `true`) and with the arguments swapped (`realizes`/`base` printed
`true`).
-/
import Meta.Audit

namespace Audit.AuditTests

def d0 : Nat := 0
def d1 : Nat := d0 + 1
def d2 : Nat := d1 + 1

theorem t2 : d2 = 2 := rfl

theorem realizes : d1 = 1 := rfl
theorem base : d1 = 1 ∧ True := ⟨realizes, trivial⟩

theorem shareA (p : Prop) (h : p) : p = True :=
  propext ⟨fun _ => trivial, fun _ => h⟩
theorem shareB (p : Prop) (h : ¬p) : p = False :=
  propext ⟨fun hp => h hp, fun f => f.elim⟩

/-! ## The reproduction: `#axiom_path` with a theorem as its target -/

/--
info: 'Audit.AuditTests.base' reaches 'Audit.AuditTests.realizes' by:
  0. base    [«this file»]
  1. realizes    [«this file»]
-/
#guard_msgs in
#axiom_path realizes base

/-! ## Controls: two dependences, two non-dependences -/

/--
info: 'Audit.AuditTests.base' uses 'Audit.AuditTests.realizes': true, by
  0. base    [«this file»]
  1. realizes    [«this file»]
-/
#guard_msgs in
#uses base realizes

/--
info: 'Audit.AuditTests.t2' uses 'Audit.AuditTests.d0': true, by
  0. t2    [«this file»]
  1. d2    [«this file»]
  2. d1    [«this file»]
  3. d0    [«this file»]
-/
#guard_msgs in
#uses t2 d0

/-- info: 'Audit.AuditTests.shareA' uses 'Audit.AuditTests.shareB': false -/
#guard_msgs in
#uses shareA shareB

/-- info: 'Audit.AuditTests.realizes' uses 'Audit.AuditTests.base': false -/
#guard_msgs in
#uses realizes base

/-! ## `dependsOn` itself, for callers outside the commands -/

open Lean Elab Command in
/-- info: [true, false] -/
#guard_msgs in
#eval show CommandElabM Unit from do
  logInfo s!"{[← dependsOn ``realizes ``base, ← dependsOn ``base ``realizes]}"

/-! ## Unchanged: an axiom as the target -/

/--
info: 'Audit.AuditTests.shareA' reaches 'propext' by:
  0. shareA    [«this file»]
  1. propext    [Init.Core]

Read the modules: where they stop being yours is where the axiom enters from the library.
-/
#guard_msgs in
#axiom_path propext shareA

/-- info: 'Audit.AuditTests.shareA' uses 'propext': true, by
  0. shareA    [«this file»]
  1. propext    [Init.Core]
-/
#guard_msgs in
#uses shareA propext

/-! ## Pins

The reproduction cell carries no axiom at all, so `collectAxioms` has
nothing to say about it.  The tooling carries `Classical.choice`, as every
declaration of `Meta/Audit.lean` did before this change: it enters through
the type `Lean.Environment` itself (its `NameMap`, at a balancing proof of
`Std.DTreeMap`; `#choice_path Audit.isAxiom`), so no code that reads the
environment can avoid it. -/

#axioms_within realizes []
#axioms_within base []
#axioms_within Audit.isAxiom [propext, Classical.choice, Quot.sound]
#axioms_within Audit.usesPath [propext, Classical.choice, Quot.sound]
#axioms_within Audit.dependsOn [propext, Classical.choice, Quot.sound]
#axioms_within Audit.elabUses [propext, Classical.choice, Quot.sound]

end Audit.AuditTests
