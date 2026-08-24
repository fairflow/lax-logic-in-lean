/-
# Layer 2 — the ENGINE REGISTER

"Part of this problem is that old tools get used for new results when
they should not be."  This file is the fix, and the fix is to make
version and role **typed fields** rather than conventions.

An engine may only be cited by the database through a record in this
file, and the record carries:

* a `version`, bumped on any behavioural change, so a result records
  which engine produced it and a stale engine cannot silently produce a
  new one;
* a `role` — `proves`, `refutes`, or `checks` — and a `mayDiscover`
  flag.  This is where the standing process rule lives: **no discovery
  by battery enumeration.**  An enumerating engine is registered with
  `mayDiscover := false`, so "a countermodel found by generate-and-test"
  becomes unwritable rather than merely discouraged;
* the soundness statement AS A `Prop`, together with a proof of it.  A
  `String` naming a theorem can go stale silently; a `Prop` field cannot
  — if the cited theorem changes statement or disappears, this file
  fails to compile.  This is `RwRule.ok` applied to engines.

The axiom pin at the foot is the standing guard: if any registered
engine's soundness ever acquires `sorryAx`, the build fails HERE rather
than in the results.
-/
import Certified.Register
import LaxLogic.PLLSearch

open PLLND

namespace Engines

/-- What an engine is entitled to conclude. -/
inductive Role where
  /-- Answers `Γ ⊢ φ` affirmatively. -/
  | proves
  /-- Answers `Γ ⊬ φ` affirmatively, by CONSTRUCTING a countermodel. -/
  | refutes
  /-- Re-checks a certificate someone else produced.  Never a finder. -/
  | checks
  deriving DecidableEq, Repr

structure Engine where
  name : String
  /-- Bumped on ANY behavioural change.  A result records the version it
  was produced by. -/
  version : Nat
  role : Role
  /-- May this engine be cited as the ORIGIN of a result, as opposed to a
  confirmation of one?  `false` for anything that works by filtering a
  battery of generated models: enumeration is structurally incapable of
  beating a constructive engine and is essentially incomplete, so it is
  banned as a discovery method and survives only as a check. -/
  mayDiscover : Bool
  /-- The soundness statement itself, not its name. -/
  soundStmt : Prop
  /-- ...and its proof.  Cannot be `sorry`ed without the pin below
  turning red. -/
  sound : soundStmt
  /-- Transcribed from the `#guard_msgs`-checked pin in
  `Certified/Register.lean`.  The register is what checks it; this is a
  copy for reading. -/
  pin : String
  /-- Is completeness PROVED, or OPEN? -/
  completeness : String
  /-- What it was last measured on, and when.  Folklore decays; a dated
  corpus does not. -/
  corpus : String
  measured : String

/-! ## The registered engines -/

/-- **A proof engine, and NOT the fastest one on larger input.**  LJF◯
focused search, sound AND complete for PLL, choice-free.

Permanent caveat: a `false` certifies NOTHING at any fuel, so on
unprovable input it must walk the whole ladder.  Use FRJ(◯) or G4c for
the negative side.

**RE-MEASURED 2026-08-22, and the standing claim does not scale.**
`CLAUDE.md` records "~10³× cheaper than the G4c oracle", measured on the
462 ρ-order cells.  On the larger goals of `lake exe frjhard` the ordering
REVERSES by two to three orders of magnitude:

| goal (provable) | G4c | LJF◯ |
|---|---|---|
| H1inv, \|G\|=51 | 25 ms | 7499 ms (fuel 40) |
| H2inv, \|G\|=66 | 15 ms | 4460 ms (fuel 40) |
| H5inv, \|G\|=83 | 144 ms | 100830 ms (fuel 44) |

and on the three unprovable converses G4c refuted in 2–25 ms where LJF◯
timed out at 150 s.  So the ρ-cell result is a fact about SMALL closed
sequents, not a general ranking.  Pick LJF◯ for the ρ-cell regime and G4c
above it, until `enginecmp` measures the crossover. -/
def ljfoProve : Engine where
  name := "LJF◯ focused search (TwoSidedLink.searchProves)"
  version := 2
  role := .proves
  mayDiscover := true
  soundStmt := ∀ (f : Nat) (Γ : List PLLFormula) (φ : PLLFormula),
    TwoSidedLink.searchProves f Γ φ = true → Nonempty (LaxND Γ φ)
  sound := fun _ _ _ h => TwoSidedLink.laxND_of_searchProves h
  pin := "[propext, Quot.sound]"
  completeness := "PROVED: TwoSidedLink.searchProves_complete, choice-free"
  corpus := "the 462 ρ-order cells: 158/158 at fuel ≤ 44.  BUT SEE BELOW"
  measured := "2026-08-15 (docs/two-sided-engine.md); RE-MEASURED 2026-08-22"

/-- **The refutation engine.**  FRJ(◯) CONSTRUCTS its countermodel out of
the refutation derivation (`FRJ.modR`); it never enumerates.  That is why
it is the canonical finder despite completeness being open: against a
workload of many sequents, a fast sound engine with an open completeness
question beats a slow one with a closed one, and each failure it reports
is itself a candidate incompleteness witness. -/
def frjRefute : Engine where
  name := "FRJ(◯) forward refutation search (FRJ/)"
  version := 2
  role := .refutes
  mayDiscover := true
  soundStmt := ∀ G : FRJ.Form, FRJ.Provable G → ¬ FRJ.PLL G
  sound := fun _ h => FRJ.soundness h
  pin := "[propext, Quot.sound]"
  completeness := "OPEN — docs/frj-w4.md §9; see Certified.CompletenessFRJ"
  corpus := "the RN(◯,{}) bank (tools/Bank.lean), whose status tags are WITHDRAWN"
  measured := "2026-08-21"

/-- **The independent second checker.**  `Reject.certifies` re-derives a
refutation through different code from FRJ(◯)'s, so it is a genuine
cross-check on a model FRJ(◯) built.

`mayDiscover := false` is the load-bearing field.  Driving this as a
search means filtering a battery of generated models — generate-and-test
with a smaller battery, not a different method.  Registered as a checker,
it can confirm a countermodel and can never be the reason one is
believed. -/
def rejectCheck : Engine where
  name := "Reject.certifies (Reject/Cert.lean)"
  version := 1
  role := .checks
  mayDiscover := false
  soundStmt := ∀ (M : FinCM) (w : Nat) (Γ : List PLLFormula) (C : PLLFormula),
    Reject.certifies M w Γ C = true → Γ ⊬ C
  sound := fun _ _ _ _ h => Reject.not_laxND_of_certifies h
  pin := "[propext, Quot.sound]"
  completeness := "not_laxND_iff_built, but with Classical.choice: EXISTENCE, not construction"
  corpus := "the 462 ρ-order cells: 54 refutations recovered by 6-world trees"
  measured := "2026-08-15 (wip/two_sided_close_out.txt)"

/-- **The G4c certificate engine.**  Two-sided and the historic oracle:
`.proved` carries a `G4cTm` proof term, `.refuted` a checked `FinCM`.

Registered as `proves` because its refutation side is a battery-checked
`FinCM`, which is a CHECK on a model rather than a construction of one.
NOT superseded.  On the 462-cell corpus `ljfoProve` wins (158/158 at fuel
≤ 44 against 9.8 s), but on the larger `frjhard` ladder this engine wins
by 300-700x on provable goals AND settles the unprovable ones LJF◯ cannot
touch.  It also remains the only tool for premise-loaded (PCLL /
`DerivU`) work.  Two regimes, two engines; the crossover is unmeasured
and that is what `enginecmp` is for. -/
def g4cSearch : Engine where
  name := "G4c certificate search (PLLND.Search.decide)"
  version := 3
  role := .proves
  mayDiscover := true
  soundStmt := ∀ (Γ : List PLLFormula) (C : PLLFormula), PLLND.G4cTm Γ C →
    Nonempty (LaxND Γ C)
  sound := fun _ _ t => PLLND.Search.proved_sound t
  pin := "see LaxLogic/PLLSearch.lean; G4c.equiv_nd is the PLL bridge"
  completeness := "PROVED for the calculus; the SEARCH is fuel-bounded"
  corpus := "462 ρ-cells in 10629 ms; AND the frjhard ladder, where it beats LJF◯ 300-700x"
  measured := "2026-08-15 (wip/two_sided_corpus_out.txt); ladder 2026-08-22"

/-- Every engine the database may cite.  Anything absent from this list
is not citable, whatever it can do. -/
def registered : List Engine :=
  [ljfoProve, frjRefute, rejectCheck, g4cSearch]

/-- The engines that may ORIGINATE a result.  `Evidence` in the database
must draw from this list, which is how the battery-enumeration ban is
enforced structurally rather than by review. -/
def finders : List Engine := registered.filter (·.mayDiscover)

/-! ## The standing guard

If any registered engine's soundness proof ever acquires `sorryAx`, this
pin turns red and the build fails here — before any result produced by
that engine can be written into the database.  Keep it pinned. -/

/-- info: 'Engines.registered' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms registered

end Engines
