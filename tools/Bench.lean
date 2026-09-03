/-
# `lake exe pllbench` — like-for-like comparison of PLL decision procedures

Matthew, 2026-09-03: "if the presentation engine we are building here is
modular, you can plug in G4c or FRJ/GBUW or another DP and compare
exactly like for like and tabulate the efficiency gains.  For instance,
there MIGHT be formulae that are decided faster by FRJ/GBU than by
G4c."

That last is a hypothesis to TEST, not to assume.  The engine profile
(`docs/engine-profile.md`) measured FRJW at 174 s against the G4c
oracle's 7 ms on one cell, which invites the conclusion that FRJW is
uniformly slower; a per-cell tabulation is what settles it, and a single
cell where FRJW wins would be a real finding about where each calculus
bites.

**The engines are not the same kind of object, and the table says so.**

| engine | what it is | can it say "don't know"? |
|---|---|---|
| `frjw` | `FRJ.Arity.decideDataByEngine` — untrusted W-engine, VERIFIED `checkClosed` certificate, then `decideOfStore`.  Total as a theorem (`decidePLL`), both witnesses built from the derivation. | only as `not-closed-within-bound`, a budget marker |
| `g4c` | `PLLND.Search.settle` — budgeted proof search with a countermodel battery. | YES: `.unknown`, and a failure certifies nothing at any fuel |

So a `g4c` win on time is not a win on the same task: `frjw` is
producing a certificate a total decision procedure can stand behind.
The table reports both, and flags DISAGREEMENTS, which would be a
soundness alarm in one of the two and must be escalated, never averaged
away.

    lake exe pllbench [--cells=FILE] [--limit=N] [--engines=frjw,g4c]
                      [--rounds=N] [--jmax=N] [--pmax=N] [--lamCap=N]

`--cells` is a TSV as produced for `batch/formulas.txt`
(`id <TAB> class <TAB> formula`); default `batch/formulas.txt`.
Output is TSV on stdout: one row per cell per engine, plus a summary.
-/
import wip.check_closed
import tools.Decide
import LaxLogic.PLLSearch
-- Explicit since 2026-09-03: the foundation modules no longer
-- re-export Mathlib.  OUTSIDE the runtime closure of `lake exe pll`.

open FRJ FRJ.Search FRJ.Gbu.W PLLTools

namespace PLLBench

/-- What an engine returned, normalised so two engines can be compared. -/
inductive Res where
  | valid | invalid | dontKnow
  deriving BEq, Repr

def Res.str : Res → String
  | .valid => "valid" | .invalid => "invalid" | .dontKnow => "don't-know"

/-- **The FRJW route**: untrusted engine, verified certificate, decision.
`none` from `decideDataByEngine` is `not-closed-within-bound`. -/
def runFrjw (cfg : Config) (φ : PLLFormula) : Res :=
  match FRJ.Arity.decideDataByEngine (ofPLL φ) cfg with
  | none => .dontKnow
  | some (.inl _) => .valid
  | some (.inr _) => .invalid

/-- **The G4c oracle**: budgeted search, may answer `.unknown`. -/
def runG4c (φ : PLLFormula) : Res :=
  match PLLND.Search.settle {} [] φ with
  | .proved _ => .valid
  | .refuted _ _ _ => .invalid
  | .unknown => .dontKnow

def timed (f : Unit → Res) : IO (Res × Nat) := do
  let t0 ← IO.monoMsNow
  let r := f ()
  -- force the result before stopping the clock
  let s := r.str
  let t1 ← IO.monoMsNow
  pure (if s.isEmpty then r else r, t1 - t0)

structure Row where
  id : String
  cls : String
  formula : String
  frjw : Res
  frjwMs : Nat
  g4c : Res
  g4cMs : Nat

def parseLine (l : String) : Option (String × String × String) :=
  match l.splitOn "\t" with
  | [a, b, c] => some (a, b, c.trim)
  | _ => none

structure Args where
  cells : String := "batch/formulas.txt"
  limit : Nat := 0
  cfg : Config :=
    { rounds := 16, jmax := 3, pmax := 2, lamCap := 24, maxRS := 3000, maxIS := 3000 }

def parseArgs (l : List String) : Args := Id.run do
  let mut a : Args := {}
  for s in l do
    if s.startsWith "--cells=" then a := { a with cells := (s.drop 8).toString }
    else if s.startsWith "--limit=" then a := { a with limit := (s.drop 8).toString.toNat! }
    else if s.startsWith "--rounds=" then
      a := { a with cfg := { a.cfg with rounds := (s.drop 9).toString.toNat! } }
    else if s.startsWith "--jmax=" then
      a := { a with cfg := { a.cfg with jmax := (s.drop 7).toString.toNat! } }
    else if s.startsWith "--pmax=" then
      a := { a with cfg := { a.cfg with pmax := (s.drop 7).toString.toNat! } }
    else if s.startsWith "--lamCap=" then
      a := { a with cfg := { a.cfg with lamCap := (s.drop 9).toString.toNat! } }
  return a

def main (argv : List String) : IO UInt32 := do
  let a := parseArgs argv
  let txt ← IO.FS.readFile a.cells
  let mut cells := (txt.splitOn "\n").filterMap parseLine
  if a.limit > 0 then cells := cells.take a.limit
  IO.println s!"# pllbench: {cells.length} cells; frjw cfg rounds={a.cfg.rounds} \
jmax={a.cfg.jmax} pmax={a.cfg.pmax} lamCap={a.cfg.lamCap}"
  IO.println "id\tclass\tformula\tfrjw\tfrjw_ms\tg4c\tg4c_ms\tnote"
  let mut rows : List Row := []
  for (id, cls, f) in cells do
    match parseFormula f with
    | .error _ =>
      IO.println s!"{id}\t{cls}\t{f}\tPARSE-ERROR\t0\t-\t0\tskipped"
      (← IO.getStdout).flush
    | .ok φ =>
      let (rf, tf) ← timed (fun _ => runFrjw a.cfg φ)
      let (rg, tg) ← timed (fun _ => runG4c φ)
      let note :=
        if rf != .dontKnow && rg != .dontKnow && rf != rg then "*** DISAGREEMENT ***"
        else if rf != .dontKnow && rg == .dontKnow then "frjw decided, g4c did not"
        else if rf == .dontKnow && rg != .dontKnow then "g4c decided, frjw did not"
        else if rf != .dontKnow && tf < tg then "FRJW FASTER"
        else ""
      IO.println s!"{id}\t{cls}\t{f}\t{rf.str}\t{tf}\t{rg.str}\t{tg}\t{note}"
      -- flush per row: without this a redirected run looks HUNG for
      -- minutes while stdout sits in the buffer (misdiagnosed as a hang
      -- on cell 079, 2026-09-03 — both engines decide it in ms).
      (← IO.getStdout).flush
      rows := rows ++ [⟨id, cls, f, rf, tf, rg, tg⟩]
  -- summary
  let dis := rows.filter (fun r => r.frjw != .dontKnow && r.g4c != .dontKnow && r.frjw != r.g4c)
  let both := rows.filter (fun r => r.frjw != .dontKnow && r.g4c != .dontKnow)
  let frjwWins := both.filter (fun r => r.frjwMs < r.g4cMs)
  let onlyFrjw := rows.filter (fun r => r.frjw != .dontKnow && r.g4c == .dontKnow)
  let onlyG4c := rows.filter (fun r => r.frjw == .dontKnow && r.g4c != .dontKnow)
  let sum := fun (l : List Nat) => l.foldl (· + ·) 0
  IO.println ""
  IO.println s!"# cells                : {rows.length}"
  IO.println s!"# both decided         : {both.length}"
  IO.println s!"# frjw only            : {onlyFrjw.length}"
  IO.println s!"# g4c only             : {onlyG4c.length}"
  IO.println s!"# FRJW FASTER          : {frjwWins.length}"
  IO.println s!"# total ms frjw / g4c  : {sum (both.map (·.frjwMs))} / {sum (both.map (·.g4cMs))}"
  IO.println s!"# DISAGREEMENTS        : {dis.length}"
  for r in dis do
    IO.println s!"#   {r.id} {r.formula}: frjw={r.frjw.str} g4c={r.g4c.str}"
  for r in frjwWins do
    IO.println s!"#   faster: {r.id} {r.formula}  frjw={r.frjwMs}ms g4c={r.g4cMs}ms"
  pure (if dis.isEmpty then 0 else 1)

end PLLBench

def main (argv : List String) : IO UInt32 := PLLBench.main argv
