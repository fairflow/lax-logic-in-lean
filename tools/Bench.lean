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
import Rewrite
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


def parseLine (l : String) : Option (String × String × String) :=
  match l.splitOn "\t" with
  | [a, b, c] => some (a, b, c.trimAscii.toString)
  | _ => none

structure BArgs where
  cells : String := "batch/formulas.txt"
  limit : Nat := 0
  /-- Normalise with the certified simpset before deciding (default ON).
  BOTH engines get the same normalised formula, so the comparison stays
  like-for-like; `--raw` decides the formula as written. -/
  normalise : Bool := true
  /-- Which engine to run: `frjw` (default) or `g4c`.  ONE engine per
  process, so the shell can time it. -/
  engine : String := ""
  /-- Run only the cell with this id.  A pure Lean computation cannot be
  interrupted from inside, so a per-cell WALL bound has to come from
  outside: `batch/bench-run.sh` drives one cell per process under
  `perl -e 'alarm N'`, the same discipline `batch/run.sh` uses.  Without
  it one level-3 cell can hold the whole table for minutes. -/
  only : String := ""
  cfg : Config :=
    { rounds := 16, jmax := 3, pmax := 2, lamCap := 24, maxRS := 3000, maxIS := 3000 }

def parseArgs (l : List String) : BArgs := Id.run do
  let mut a : BArgs := {}
  for s in l do
    if s.startsWith "--cells=" then a := { a with cells := (s.drop 8).toString }
    else if s.startsWith "--only=" then a := { a with only := (s.drop 7).toString }
    else if s.startsWith "--engine=" then a := { a with engine := (s.drop 9).toString }
    else if s == "--raw" then a := { a with normalise := false }
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

/-- **Do not time in-process.**  The first version of this file did

    let r := f (); let s := r.str; pure (if s.isEmpty then r else r, t1 - t0)

intending `r.str` to force the computation inside the window.  Both
branches of the `if` are `r`, so the compiler dropped `s` as dead code,
never forced `f ()`, and every cell reported 0 ms — the table measured
nothing (2026-09-03).  Forcing a pure value inside an `IO` window is
fragile in general: anything the optimiser can prove unused, it may
drop.

So the WALL clock is taken from OUTSIDE, by `batch/bench-run.sh`, which
runs one engine on one cell per process.  Both engines pay the same
process startup, so the comparison stays like-for-like; the runner
reports that constant separately rather than pretending it away. -/
def runOne (a : BArgs) (eng : String) (φ : PLLFormula) : Res :=
  if eng == "g4c" then runG4c φ else runFrjw a.cfg φ

def main (argv : List String) : IO UInt32 := do
  let a := parseArgs argv
  let txt ← IO.FS.readFile a.cells
  let mut cells := (txt.splitOn "\n").filterMap parseLine
  if a.only != "" then cells := cells.filter (fun c => c.1 == a.only)
  if a.limit > 0 then cells := cells.take a.limit
  let eng := if a.engine == "" then "frjw" else a.engine
  for (id, _, f) in cells do
    match parseFormula f with
    | .error e => IO.println s!"{id}\tparse-error\t{e}"
    | .ok φ0 =>
      let φ := if a.normalise then Rewrite.simplifyWith Rewrite.fullSetC 40 φ0 else φ0
      -- The result is PRINTED, so the computation cannot be optimised
      -- away; the wall clock is the shell's, around this whole process.
      IO.println s!"{id}\t{eng}\t{(runOne a eng φ).str}"
      (← IO.getStdout).flush
  pure 0

end PLLBench

def main (argv : List String) : IO UInt32 := PLLBench.main argv
