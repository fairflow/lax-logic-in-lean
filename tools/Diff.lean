/-
# The differential test: `Fast` vs `Profile`, and the cost

`FRJ/Search/Profile.lean` replaces clique enumeration with a profile-indexed
fixpoint, licensed by `FRJ/Profile.lean`.  The lemma licenses the METHOD.
This checks the IMPLEMENTATION, and it checks it two ways, because the two
questions are different:

* **MATCHED arity** (`saturateProfMatched`, layers = `jmax - 1`): the two
  engines explore the same families, so the verdicts must be IDENTICAL.
  Any difference isolates a defect in the merging.
* **UNBOUNDED arity** (`saturateProf`): the profile engine explores every
  arity, so it may find MORE.  `Fast` hit / `Prof` miss is a DEFECT;
  `Prof` hit / `Fast` miss is the point of the exercise.

`lake exe frjdiff [--rounds=N] [--jmax=N] [--pmax=N] [--limit=N] [--bank]`
-/
import FRJ.Search.Profile
import FRJ.Bridge
import Tools.Bank
import LaxLogic.RN.Reps
import LaxLogic.PLLSearch
import wip.rho_order

open FRJ

namespace FrjDiff

def p : Form := .atom "p"
def q : Form := .atom "q"

/-- Small ◯-goals, as in `frjterm`: six PLL theorems and two non-theorems. -/
def smallCells : List (String × Form) :=
  [ ("unit      p ⊃ ◯p",              .imp p (.circ p))
  , ("mult      ◯◯p ⊃ ◯p",            .imp (.circ (.circ p)) (.circ p))
  , ("mono      ◯(p ∧ q) ⊃ ◯p",       .imp (.circ (.and p q)) (.circ p))
  , ("strength  ◯p ∧ ◯q ⊃ ◯(p ∧ q)",  .imp (.and (.circ p) (.circ q)) (.circ (.and p q)))
  , ("K         ◯(p⊃q) ⊃ (◯p⊃◯q)",    .imp (.circ (.imp p q)) (.imp (.circ p) (.circ q)))
  , ("triv      ◯⊥ ⊃ ◯⊥",             .imp (.circ .bot) (.circ .bot))
  , ("NOT-thm   ◯p ⊃ p",              .imp (.circ p) p)
  , ("NOT-thm   ¬◯⊥",                 .imp (.circ .bot) .bot) ]

structure Row where
  name : String
  /-- GROUND TRUTH from G4c, which is two-sided and certificate-carrying:
  `.proved` is a `G4cTm`, `.refuted` a `FinCM` the verified checker
  accepts.  Without this column a differential test between two FRJ(◯)
  engines only shows they AGREE — it cannot show whether they are
  agreeing on the right answer. -/
  truth : String
  truthMs : Nat
  fastHit : Bool
  fastMs : Nat
  fastFams : Nat
  matchHit : Bool
  matchMs : Nat
  matchFams : Nat
  profHit : Bool
  profMs : Nat
  profFams : Nat
  /-- Every cap, so "cap-free closure" is OBSERVED and not inferred.  A
  miss with a cap binding is a frontier marker; a miss with NO cap
  binding, against a G4c-certified countermodel, is an incompleteness
  candidate for FRJ(◯). -/
  profCapFree : Bool
  profCaps : String

def runOne (cfg : Search.Config) (nm : String) (G : Form) : IO Row := do
  let tg0 ← IO.monoMsNow
  let truth := match PLLND.Search.decide { findBudget := some 200000, emitClosureCap := 0 }
                      [] (toPLL G) with
    | .proved _ => "PROVABLE"
    | .refuted _ _ _ => "REFUTABLE"
    | .unknown => "unknown"
  let tg1 ← IO.monoMsNow
  let t0 ← IO.monoMsNow
  let (dbF, stF) := Search.saturateFast G cfg
  let hF := Search.derivable G dbF
  let t1 ← IO.monoMsNow
  let (dbM, stM) := Search.saturateProfMatched G cfg
  let hM := Search.derivable G dbM
  let t2 ← IO.monoMsNow
  let (dbP, stP) := Search.saturateProf G cfg
  let hP := Search.derivable G dbP
  let t3 ← IO.monoMsNow
  let sp := stP.toStats
  let capFree := !sp.lamCapped && !sp.dbCapped && sp.roundsUsed < cfg.rounds
  let cl := (if sp.lamCapped then ["lamCap"] else [])
         ++ (if sp.dbCapped then ["maxRS/maxIS"] else [])
         ++ (if sp.roundsUsed ≥ cfg.rounds then ["rounds"] else [])
  return ⟨nm, truth, tg1 - tg0, hF, t1 - t0, stF.fams, hM, t2 - t1, stM.fams,
          hP, t3 - t2, stP.fams, capFree,
          if cl.isEmpty then "NONE" else String.intercalate "+" cl⟩

def report (r : Row) : String :=
  let v (b : Bool) := if b then "REFUTED" else "none"
  let verdict :=
    if r.fastHit != r.matchHit then
      "!! DEFECT — matched arity, verdicts differ"
    else if r.fastHit && !r.profHit then
      "!! DEFECT — Fast refuted, unbounded Profile did not"
    else if r.profHit && !r.fastHit then
      "** PROFILE FINDS MORE (the point)"
    else if r.truth == "REFUTABLE" && !r.profHit && r.profCapFree then
      "!!! INCOMPLETENESS CANDIDATE — saturation CLOSED with NO cap bound, yet G4c certifies a countermodel"
    else if r.truth == "REFUTABLE" && !r.profHit then
      "!! missed at this bound (a cap bound the run — re-run raised)"
    else "agree"
  String.intercalate "\n"
    [ s!"{r.name}   [G4c: {r.truth} {r.truthMs}ms]",
      s!"    fast    {v r.fastHit}  fams={r.fastFams}  {r.fastMs}ms",
      s!"    matched {v r.matchHit}  fams={r.matchFams}  {r.matchMs}ms",
      s!"    profile {v r.profHit}  fams={r.profFams}  caps={r.profCaps}  {r.profMs}ms",
      s!"    ⇒ {verdict}" ]

def getNat (args : List String) (k : String) (d : Nat) : Nat :=
  match args.find? (fun a => a.startsWith ("--" ++ k ++ "=")) with
  | some a => ((a.drop (k.length + 3)).toString.toNat?).getD d
  | none => d

def main (args : List String) : IO Unit := do
  let cfg : Search.Config := {
    rounds := getNat args "rounds" 10, jmax := getNat args "jmax" 3,
    pmax := getNat args "pmax" 2, lamCap := (fun n => if n == 0 then 1000000 else n) (getNat args "lamcap" 10),
    maxRS := getNat args "maxrs" 800, maxIS := getNat args "maxis" 800 }
  let limit := getNat args "limit" 0
  -- `--cand=K` retargets every cell at representative `qK` instead of the
  -- one the table assigns.  At K=0 (⊥) most cells become REFUTABLE, which
  -- is the corpus this comparison actually needs: measured 2026-08-22,
  -- the untargeted bank yielded only ONE refutation in 120 goals, so the
  -- differential test was thinly exercised on the case that matters —
  -- constructing a countermodel, rather than failing to.
  let cand := (args.find? (fun a => a.startsWith "--cand=")).bind
    (fun a => (a.drop 7).toString.toNat?)
  let cells : List (String × Form) :=
    if args.contains "--bank" then
      let bs := match cand with
        | none => RNBank.cells.flatMap (fun c => c.forms)
        | some k => match RNBank.reps[k]? with
          | none => []
          | some r => RNBank.cells.flatMap (fun c =>
              [(s!"{c.name}→q{k}", Form.imp (ofPLL c.lhs) (ofPLL r)),
               (s!"{c.name}←q{k}", Form.imp (ofPLL r) (ofPLL c.lhs))])
      if limit == 0 then bs else bs.take limit
    else if args.contains "--rho" then
      -- THE REFUTATION BENCHMARK.  The 462 ordered ρ-order cells.
      --
      -- Why this corpus and not the bank: measured 2026-08-22, 118 of 120
      -- bank goals are PROVABLE, so they have no countermodel to find and
      -- `fun _ => none` scores 118/120 on them.  A refutation engine
      -- cannot be evaluated on inputs with no refutation.
      --
      -- The ρ-cells are the opposite: the two-sided run settled them as
      -- 158 ⊢ / 302 ⊬, so 302 of the 462 have a countermodel KNOWN to
      -- exist, each with a recorded witness in
      -- `wip/two_sided_close_out.txt`.  Every strict `A < B` also yields
      -- a refutable converse `B ⊃ A`, since the 22 classes are pairwise
      -- distinct.
      let ps := (List.range RhoOrder.n).flatMap (fun i =>
        (List.range RhoOrder.n).filterMap (fun j =>
          if i == j then none
          else some (s!"ρ{i}⊃ρ{j}",
            Form.imp (ofPLL (RhoOrder.rhoF i))
                     (ofPLL (RhoOrder.rhoF j)))))
      let ps := match (args.find? (fun a => a.startsWith "--only=")) with
        | none => ps
        | some a =>
            let want := ((a.drop 7).toString.splitOn ",")
            ps.filter (fun c => want.contains c.1)
      if limit == 0 then ps else ps.take limit
    else smallCells
  IO.println s!"rounds={cfg.rounds} jmax={cfg.jmax} pmax={cfg.pmax} \
lamCap={cfg.lamCap} maxRS={cfg.maxRS} maxIS={cfg.maxIS}; {cells.length} goals"
  IO.println ""
  let mut defects := 0
  let mut more := 0
  let mut missed := 0
  let mut refutable := 0
  let mut tF := 0; let mut tM := 0; let mut tP := 0
  let mut fF := 0; let mut fM := 0; let mut fP := 0
  for (nm, G) in cells do
    let r ← runOne cfg nm G
    IO.println (report r)
    (← IO.getStdout).flush
    if r.fastHit != r.matchHit || (r.fastHit && !r.profHit) then defects := defects + 1
    if r.profHit && !r.fastHit then more := more + 1
    if r.truth == "REFUTABLE" then
      refutable := refutable + 1
      if !r.profHit then missed := missed + 1
    tF := tF + r.fastMs; tM := tM + r.matchMs; tP := tP + r.profMs
    fF := fF + r.fastFams; fM := fM + r.matchFams; fP := fP + r.profFams
  IO.println ""
  IO.println s!"-- DEFECTS={defects}  profile-finds-more={more}"
  IO.println s!"-- GROUND TRUTH (G4c): {refutable} goals are REFUTABLE; FRJ(◯) MISSED {missed} of them"
  IO.println s!"-- time   fast={tF}ms  matched={tM}ms  profile={tP}ms"
  IO.println s!"-- fams   fast={fF}    matched={fM}    profile={fP}"

end FrjDiff

def main (args : List String) : IO Unit := FrjDiff.main args
