/-
# Construction vs construction: FRJ(◯) `modR` against G4c stage 3

Matthew's correction, 2026-08-22/23: the earlier `frjdiff --rho` run set
`emitClosureCap := 0`, which DISABLES G4c's only constructive stage.
Every refutation it reported came from `sweepCert` — a look-up against
`LaxLogic.PLLSearch.defaultFrames`, eleven hand-curated frames of ≤ 4
worlds (pre-existing code, `LaxLogic/PLLSearch.lean:272`, none of it
written this session).  That is a battery match, not a construction, and
comparing it to FRJ(◯) was comparing the wrong things.

This is the fair test: FRJ(◯)'s `modR` — a one-pass STRUCTURAL FOLD over
the refutation derivation (`FRJ/Extract.lean:509`, `preR`, one recursive
call per rule instance, no search) — against G4c's `CounterEmit.emit`,
the "complete over the closure but exponential" constructive stage,
isolated by setting `frames := []` so the cheap battery cannot answer
first.

Corpus: 27 known-refutable ρ-order cells (from the 2026-08-22 two-sided
ground truth), filtered to exclude the degenerate antecedents `ρ0` (⊥)
and `ρ1` (⊤) on EITHER side — every goal here is a real two-sided
sequent between two non-trivial representatives, both indices ≤ 12.

    lake exe frjconstruct [--emitcap=N] [--budget=N] [--lamcap=N]
-/
import FRJ.Search.Profile
import FRJ.Search.Pin
import FRJ.Bridge
import LaxLogic.PLLSearch
import LaxLogic.RN.Rho
import wip.ljfo_link

open FRJ

namespace FrjConstruct

/-- 27 cells, both indices ≤ 12, neither side ρ0/ρ1 — picked evenly across
the antecedent range from the full 462-cell ground-truth run so as not to
repeat the ρ1-biased sample that misled the first comparison. -/
def corpus : List (Nat × Nat) :=
  [(2,3), (3,5), (4,3), (5,2), (5,4), (5,8), (6,3), (6,5), (6,8), (7,3),
   (8,2), (8,4), (8,6), (8,9), (9,2), (9,4), (9,7), (10,2), (10,4), (10,6),
   (10,8), (10,12), (11,3), (11,5), (11,7), (11,9), (12,2)]

/-- FRJ(◯), Profile engine, cap-free on both arities (Lemma 1 + 2).  On a
hit, extract the derivation and run it through `modR` — the same one-pass
fold that produces every certificate in `wip/rnFRJCerts.lean` — then
`Search.tabOf` for a world count, exactly as `Tools/Cert.lean` does. -/
def frjBuild (G : Form) (cfg : Search.Config) : IO (Option Nat × Nat) := do
  let t0 ← IO.monoMsNow
  let (db, _) := Search.saturateProf G cfg
  let hit := (db.rs.find? (fun x => decide (x.rhs = G))).map
    (fun r => (Search.tabOf (modR r.der) (Search.atomsOf G)).n)
  let t1 ← IO.monoMsNow
  return (hit, t1 - t0)

/-- G4c, STAGE 3 ONLY: `frames := []` removes the battery, so `.refuted`
can only come from `CounterEmit.emit`.  `findBudget` insures stage 2
(proof search) cannot run away on a mis-classified goal.

Uses `settleWhy`, NOT `settle`: a `none` from `settle` conflates "the
emitter ran and found nothing" with "the emitter never ran because the
closure exceeded `emitClosureCap`" (`Reason.closureTooBig`) — exactly the
kind of report that must not be made without the distinction, per this
session's own standing rule. -/
def g4cStage3 (φ : PLLFormula) (emitCap budget : Nat) : IO (Option Nat × Nat × String) := do
  let t0 ← IO.monoMsNow
  let v := PLLND.Search.settleWhy
    { frames := [], emitClosureCap := emitCap, findBudget := some budget } [] φ
  let t1 ← IO.monoMsNow
  match v with
  | .refuted M _ _ => return (some M.n, t1 - t0, "ran")
  | .proved _ => return (none, t1 - t0, "PROVED?!")
  | .unknown (.closureTooBig sz cap) =>
      return (none, t1 - t0, s!"SKIPPED — closure {sz} > cap {cap}")
  | .unknown (.budgetExhausted b) => return (none, t1 - t0, s!"budget {b} exhausted")
  | .unknown .allStagesMissed => return (none, t1 - t0, "ran, found nothing")

def getNat (args : List String) (k : String) (d : Nat) : Nat :=
  match args.find? (fun a => a.startsWith ("--" ++ k ++ "=")) with
  | some a => ((a.drop (k.length + 3)).toString.toNat?).getD d
  | none => d

/-- Single-cell FRJ(◯)-only mode, for a driver that imposes a
process-level time cap per search: one cell per invocation, one
tab-separated line per result.  Misses are classified — a cap-free
closure is printed as such, never as a mere not-found. -/
def frjOne (i j : Nat) (cfg : Search.Config) : IO Unit := do
  let φ := PLLFormula.ifThen (RhoOrder.rhoF i) (RhoOrder.rhoF j)
  let G := ofPLL φ
  let t0 ← IO.monoMsNow
  let (db, st) := Search.saturateProf G cfg
  let t1 ← IO.monoMsNow
  let s := st.toStats
  let capFree := !s.lamCapped && !s.dbCapped && s.roundsUsed < cfg.rounds
  let cl := (if s.lamCapped then ["lamCap"] else [])
         ++ (if s.dbCapped then ["maxRS/maxIS"] else [])
         ++ (if s.roundsUsed ≥ cfg.rounds then ["rounds"] else [])
  let caps := if cl.isEmpty then "NONE" else String.intercalate "+" cl
  let stats := s!"r={s.roundsUsed} RS={s.rsSize} IS={s.isSize} fams={st.fams} caps={caps}"
  match db.rs.find? (fun x => decide (x.rhs = G)) with
  | some r =>
      let n := (Search.tabOf (modR r.der) (Search.atomsOf G)).n
      IO.println s!"ρ{i}⊃ρ{j}	REFUTED {n}w	{t1 - t0}ms	{stats}"
  | none =>
      let v := if capFree then "CLOSED-CAP-FREE" else "not-found-within-bound"
      IO.println s!"ρ{i}⊃ρ{j}	{v}	{t1 - t0}ms	{stats}"

def main (args : List String) : IO Unit := do
  let emitCap := getNat args "emitcap" 40
  let budget := getNat args "budget" 50000
  let lc0 := getNat args "lamcap" 0
  let lamCap := if lc0 == 0 then 1000000 else lc0   -- 0 = uncapped (see README)
  let cfg : Search.Config := { rounds := getNat args "rounds" 12, lamCap := lamCap,
                               maxRS := getNat args "maxrs" 800, maxIS := getNat args "maxis" 800 }
  if (args.find? (fun a => a == "--ljf")).isSome then
    -- Single-cell PROOF side: `TwoSidedLink.searchProves` on ρi ⊃ ρj at a
    -- deep fuel ladder (an LJF◯ `false` certifies nothing at any fuel).
    let i := getNat args "i" 0
    let j := getNat args "j" 0
    let φ := PLLFormula.ifThen (RhoOrder.rhoF i) (RhoOrder.rhoF j)
    let fuels := (List.range (getNat args "maxfuel" 64 / 4 + 1)).map (· * 4) |>.filter (· ≥ 8)
    let t0 ← IO.monoMsNow
    match fuels.find? (fun f => TwoSidedLink.searchProves f [] φ) with
    | some f =>
        let t1 ← IO.monoMsNow
        return (← IO.println s!"ρ{i}⊃ρ{j}	LJF◯-PROVED fuel={f}	{t1 - t0}ms")
    | none =>
        let t1 ← IO.monoMsNow
        return (← IO.println s!"ρ{i}⊃ρ{j}	ljf-not-found-≤fuel-{fuels.getLast?.getD 0} (certifies nothing)	{t1 - t0}ms")
  if (args.find? (fun a => a.startsWith "--i=")).isSome then
    return (← frjOne (getNat args "i" 0) (getNat args "j" 0) cfg)
  IO.println s!"FRJ(◯) Profile: rounds={cfg.rounds} lamCap={lamCap} (cap-free arity)"
  IO.println s!"G4c stage 3 only: frames=[] emitClosureCap={emitCap} findBudget={budget}"
  IO.println ""
  let mut jagged := 0
  let mut both := 0
  let mut frjOnly := 0
  let mut g4cOnly := 0
  let mut neither := 0
  for (i, j) in corpus do
    let φ := PLLFormula.ifThen (RhoOrder.rhoF i) (RhoOrder.rhoF j)
    let G := ofPLL φ
    let (fw, fms) ← frjBuild G cfg
    let (gw, gms, gwhy) ← g4cStage3 φ emitCap budget
    let tag := match fw, gw with
      | some _, some _ => "both"
      | some _, none   => "FRJ-only"
      | none,   some _ => "G4c-only"
      | none,   none   => "NEITHER"
    match fw, gw with
    | some _, some _ => both := both + 1
    | some _, none => frjOnly := frjOnly + 1
    | none, some _ => g4cOnly := g4cOnly + 1
    | none, none => neither := neither + 1
    let ratio : Float :=
      if fms == 0 || gms == 0 then 0.0 else
      if fms ≥ gms then (Float.ofNat fms) / (Float.ofNat gms)
      else (Float.ofNat gms) / (Float.ofNat fms)
    let isJagged := ratio ≥ 3.0 || tag == "FRJ-only" || tag == "G4c-only"
    if isJagged then jagged := jagged + 1
    let fwStr := match fw with | some n => s!"{n} worlds" | none => "NO MODEL"
    let gwStr := match gw with | some n => s!"{n} worlds" | none => "NO MODEL"
    let verdict := if isJagged then "JAGGED" else "comparable"
    IO.println s!"ρ{i}⊃ρ{j}   [{tag}]"
    IO.println s!"    FRJ(◯) modR:      {fwStr}  [{fms} ms]"
    IO.println s!"    G4c CounterEmit:  {gwStr}  [{gms} ms]  ({gwhy})"
    IO.println s!"    ⇒ {verdict}"
    (← IO.getStdout).flush
  IO.println ""
  IO.println s!"-- {corpus.length} goals: both={both} FRJ-only={frjOnly} G4c-only={g4cOnly} neither={neither}"
  IO.println s!"-- JAGGED (≥3x time difference, or one side found nothing): {jagged} / {corpus.length}"

end FrjConstruct

def main (args : List String) : IO Unit := FrjConstruct.main args
