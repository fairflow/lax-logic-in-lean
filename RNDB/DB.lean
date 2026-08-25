/-
# The database, as one object

The union of every migrated entry list.  `Entry.holds` makes each claim a
theorem; `entries_hold` (RNDB/Types.lean) lifts that to any list; so this
single definition is 1,776 kernel-checked dictionary facts with their
provenance, and the pin at the foot is the standing guard: if any entry
anywhere acquires `sorryAx`, the build fails HERE.

| source | entries | relation |
|---|---|---|
| `RhoEntries`      |  185 | `nle`, ρ-scope |
| `DictEntries`     |  236 | `interd` (round 1, the `rndSet` harvest) |
| `Dict2Entries`    |   82 | `interd` (round 2, sorry-free subset) |
| `FRJCertEntries`  |   24 | `nle` (rnFRJCerts countermodels) |
| `DerivedEntries`  |  321 | `interd` (318 symm + 3 trans, evidence DAG) |
| `EscEntries`      |  928 | `nle` (the 58 universal escapes, decomposed) |

Duplicates ACROSS sources are permitted and deliberate: an entry records
one piece of evidence, and the same claim backed twice (say, an FRJ(◯)
construction and a battery FinCM) is corroboration, not redundancy.
Dedup is a VIEW concern, downstream.
-/
import RNDB.RhoEntries
import RNDB.DictEntries
import RNDB.Dict2Entries
import RNDB.FRJCertEntries
import RNDB.DerivedEntries
import RNDB.EscEntries
import RNDB.Order
import RNDB.SepEntries

namespace RNDB

def allEntries : List Entry :=
  rhoEntries ++ dictEntriesR1 ++ dictEntriesR2 ++ frjCertEntries
    ++ derivedEntries ++ escEntries ++ orderEntries ++ sepEntries

set_option maxRecDepth 65536 in
theorem allEntries_length : allEntries.length = 1873 := by
  simp [allEntries, rhoEntries_length, dictEntriesR1_length,
    dictEntriesR2_length, frjCertEntries_length, derivedEntries_length,
    escEntries_length, orderEntries_length, sepEntries_length]

/-- Every claim in the database is true — instantiating the type-level
fact at the concrete list. -/
theorem allEntries_hold : ∀ e ∈ allEntries, e.claim.Holds :=
  fun e _ => e.holds

/-! ## Pins — UNGUARDED as emitted; guard via tools/pin-backfill.py -/

/-- info: 'RNDB.allEntries' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms allEntries

/-- info: 'RNDB.allEntries_hold' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms allEntries_hold

/-- info: 'RNDB.allEntries_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms allEntries_length

end RNDB
