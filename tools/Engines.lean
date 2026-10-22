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
import LaxLogic.PLL.Search.Search
import FRJ.SoundW
import LaxLogic.PLL.SubTab.Engine
import LaxLogic.PLL.SubTab.Translate
import wip.check_closed

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
`TOOLS.md` §2 records "~10³× cheaper than the G4c oracle", measured on the
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

/-- **The refutation engine of the paper calculus.**  FRJ(◯) CONSTRUCTS
its countermodel out of the refutation derivation (`FRJ.modR`); it never
enumerates.  A hit is a countermodel by `FRJ.soundness`.  The calculus is
incomplete: `Certified.CompletenessFRJ` is REFUTED by
`FRJ80.not_CompletenessFRJ` (`wip/frj80_noprov.lean`, witness #80), so a
miss is never a verdict, at any bound.  The calculus whose completeness
is PROVED is FRJW (`frjwRefute` below). -/
def frjRefute : Engine where
  name := "FRJ(◯) forward refutation search (FRJ/)"
  version := 2
  role := .refutes
  mayDiscover := true
  soundStmt := ∀ G : FRJ.Form, FRJ.Provable G → ¬ FRJ.PLL G
  sound := fun _ h => FRJ.soundness h
  pin := "[propext, Quot.sound]"
  completeness := "REFUTED: FRJ80.not_CompletenessFRJ : ¬ Certified.CompletenessFRJ (wip/frj80_noprov.lean, witness #80)"
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
  -- 4 (2026-10-19, #70): `find` memoises a failure with the ancestor keys its loop-check cuts met.
  version := 4
  role := .proves
  mayDiscover := true
  soundStmt := ∀ (Γ : List PLLFormula) (C : PLLFormula), PLLND.G4cTm Γ C →
    Nonempty (LaxND Γ C)
  sound := fun _ _ t => PLLND.Search.proved_sound t
  pin := "see LaxLogic/PLL/Search/Search.lean; G4c.equiv_nd is the PLL bridge"
  completeness := "PROVED for the calculus; the SEARCH is fuel-bounded"
  corpus := "462 ρ-cells in 10629 ms; AND the frjhard ladder, where it beats LJF◯ 300-700x"
  measured := "2026-08-15 (wip/two_sided_corpus_out.txt); ladder 2026-08-22"

/-- **The FRJW refutation engine** — the W-family instance `wOps` of the
modular saturation core (`FRJ/Search/OpsW.lean`): FRJV's rule set with
`⊃∉` deleted and `Lift` added (maximal retained zone, riding in the
`stepNotIn` slot, so the shared loop is untouched).  Rows carry their
`FRJWr`/`FRJWi` derivations, so a hit IS a `DisprovableW` witness
(`disprovableW_of_hit`).  Smoke-validated 2026-08-31 on the duality-gap
cell: on `◯(◯p ⊃ p)` the V-engine has no irregular row (matching the
kernel-checked `not_evalI_Gcc`) and this engine produces one via
`Lift`, matching W4's hand witness.

Completeness of the CALCULUS is PROVED (`FRJ.Gbu.W.frjw_complete`,
`FRJ.Gbu.W.decideGbuW`, `FRJ/Gbu/W/Saturate.lean`).  The ENGINE is
bounded (join arities `jmax`/`pmax`, rounds), so a miss is
`not-found-within-bound`, never a verdict; `checkClosedCheck` below
certifies its store. -/
def frjwRefute : Engine where
  name := "FRJW forward refutation search (FRJ/Search/OpsW.lean, wOps)"
  -- 2 (2026-09-02/03): the A3 repair (relaxed ⋈^◯) and the semi-naive round (`Config.semiNaive`, default off).
  version := 2
  role := .refutes
  mayDiscover := true
  soundStmt := ∀ G : FRJ.Form, FRJ.DisprovableW G → ¬ FRJ.PLL G
  sound := fun _ h => FRJ.soundnessW h
  pin := "[propext, Quot.sound]"
  completeness := "calculus PROVED: FRJ.Gbu.W.frjw_complete, FRJ.Gbu.W.decideGbuW (FRJ/Gbu/W/Saturate.lean), [propext, Quot.sound]; the exclusion half is FRJ/Gbu/W/Exclusion.lean.  The engine is bounded: a miss is not-found-within-bound, never a verdict"
  corpus := "smoke 2026-08-31: Gcc gap cell (irregular row via Lift where V has none); ◯-free agreement with vOps on Peirce; no false hits on p ⊃ p or ◯(p ⊃ ◯p)"
  measured := "2026-08-31"

/-- **The subframe tableau, proof side** (`PLLND.SubTab.engine`, library
`SubTab`, `LaxLogic/PLL/SubTab/`).  The producer `SubTab.solve`
(`Tableau.lean`) is `partial` and UNTRUSTED: it returns a closed tableau
`TCert` or a finite subframe countermodel `SubCM`, and the certifiers
judge.  This record is the proof side, for `Holds φ := Nonempty ([] ⊢ φ)`.
Two certifiers check the same `TCert`, both PROVED
`[propext, Quot.sound]`: `yes` (the engine's, sound through
`SubframeModel.CF.completeness`, which reaches FRJW) and `yes'`
(`Translate.lean`, sound by the tableau's own rules through `termOf`).
`complete` (`Complete.lean`) proves that every formula has a closed
tableau or a finite subframe countermodel; it is a theorem about the
proof's dichotomy, and that the compiled `solve` terminates is a paper
argument, so completeness of the producer (`Certify.Engine.Complete`)
is not claimed. -/
def subTabProve : Engine where
  name := "subframe tableau, proof side (PLLND.SubTab.engine; certifiers yes, yes')"
  version := 1
  role := .proves
  mayDiscover := true
  soundStmt := ∀ (φ : PLLFormula) (c : PLLND.SubTab.TCert),
    PLLND.SubTab.yes.check φ c = true → PLLND.SubTab.Holds φ
  sound := PLLND.SubTab.yes.sound
  pin := "[propext, Quot.sound]"
  completeness := "PROVED for the tableau: PLLND.SubTab.complete, [propext, Quot.sound]; the producer SubTab.solve is partial, its termination a paper argument"
  corpus := "the 26 benchmark cells and the 7 refbench cells: the same 33 verdicts as the earlier benchmark record"
  measured := "2026-10-15; port checks 2026-10-22 (TOOLS.md §3)"

/-- **The subframe tableau, refutation side** (`PLLND.SubTab.engine`).  An
open tableau becomes a finite subframe countermodel (`toSubCM`), so the
countermodel is CONSTRUCTED from the search, not drawn from a battery;
`no` checks it, PROVED `[propext, Quot.sound]` (`SubCM.refutes_sound`).
The finite-model enumeration of `ModelEnum.lean` (the `enum` disprover
of `subtabdecide`, and the minimiser of `pllfast`) is enumeration, and
is not registered here. -/
def subTabRefute : Engine where
  name := "subframe tableau, refutation side (PLLND.SubTab.engine; certifier no)"
  version := 1
  role := .refutes
  mayDiscover := true
  soundStmt := ∀ (φ : PLLFormula) (m : PLLND.SubTab.SubCM),
    PLLND.SubTab.no.check φ m = true → ¬ PLLND.SubTab.Holds φ
  sound := PLLND.SubTab.no.sound
  pin := "[propext, Quot.sound]"
  completeness := "PROVED for the tableau: PLLND.SubTab.complete, [propext, Quot.sound]; the producer SubTab.solve is partial, its termination a paper argument"
  corpus := "the 26 benchmark cells and the 7 refbench cells: the same 33 verdicts as the earlier benchmark record"
  measured := "2026-10-15; port checks 2026-10-22 (TOOLS.md §3)"

/-- **The verified store certificate behind `pll`** (`wip/check_closed.lean`).
The untrusted W-engine (`frjwRefute`) proposes a store of FRJW
disproofs; `FRJ.Arity.checkClosed` certifies that the store is closed
under the 21 clauses, whence `DBClosed G db` (`dbClosed_of_check`) and
the decision `ProvableGbuC G ⊕' DisprovableW G` (`decideGbuW_of_check`).
A checker, not a finder: the store comes from the engine, and
`decideByEngine` returning `none` is `not-closed-within-bound`, never a
verdict. -/
def checkClosedCheck : Engine where
  name := "checkClosed, the store certificate (FRJ.Arity.checkClosed, wip/check_closed.lean)"
  version := 1
  role := .checks
  mayDiscover := false
  soundStmt := ∀ (G : FRJ.Form) (db : List (FRJ.Gbu.W.WRow G)),
    FRJ.Arity.checkClosed G db = true → FRJ.Gbu.W.DBClosed G db
  sound := fun _ _ h => FRJ.Arity.dbClosed_of_check h
  pin := "[propext, Quot.sound]"
  completeness := "none claimed for the check: a store failing it is not-closed-within-bound; the closure theorem decideGbuW_of_dbClosed turns a passing store into the decision"
  corpus := "the 20 probe stores of checkprobe, sub-millisecond; gate watched failing 2026-09-02 (join rows deleted: false 14/14; first row deleted: false 20/20)"
  measured := "2026-09-02 (wip/checkprobe_out.txt)"

/-- Every engine the database may cite.  Anything absent from this list
is not citable, whatever it can do. -/
def registered : List Engine :=
  [ljfoProve, frjRefute, frjwRefute, rejectCheck, g4cSearch,
   subTabProve, subTabRefute, checkClosedCheck]

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
