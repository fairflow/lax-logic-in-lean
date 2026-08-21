/-
COPY, not a move.  The `wip/` original is left in place unchanged so that
other branches still compile; this file is the maintained version.  Do not
edit the `wip/` twin — it is stale by construction (2026-08-21).
-/
/-
# The RN(◯,{}) harness: FRJ(◯) countermodel search against the oracle bank

Runs a countermodel search over every cell of the certified RN(◯,{})
dictionary (`wip/rnBank.lean`, generated from `wip/rnDict.lean`) and grades
each result against what the repository already knows.

Why this bank.  On an infallible model with `Rm = ≤` the lax modality IS
the double negation (`FRJ.circ_iff_nn`), and every variable-free IPC
formula is decided, so the whole fragment would collapse to two classes.
RN(◯,{}) has at least sixteen.  Every RN separation therefore needs a
model with `Rm ⊊ ≤`: the bank lives entirely outside the two rows of the
completeness map that are settled, in the region where FRJ(◯) is not a
notational variant of FRJ.

Grading, per cell (both directions of the stated interderivability are
searched; refuting either refutes the cell):

* `proved`  — kernel-checked in `rnDict`.  A hit contradicts a theorem, so
  it is reported as **ENGINE-BUG**, never as a result.
* `refuted` — known FALSE with a certified ≤4-world countermodel.  A hit is
  `pass`; a miss is an incompleteness datum, not a verdict about the cell.
* `open`    — neither proved nor refuted at ≤4 worlds.  A hit is a **NEW
  REFUTATION**: the dictionary entry is false and the ladder gains a class.

Verdict vocabulary (repo standard; there is no CERTAIN category).  A
search that stops without a derivation reports either
`no-derivation-at-fixpoint` (the rule set produced nothing new, relative to
the engine's own caps) or `no-derivation-at-budget` (a cap or the round
limit was hit — a frontier marker to re-run raised, never dropped).

Usage:  `lake exe rnfrj [--rounds=N] [--jmax=N] [--pmax=N] [--lamcap=N]
                        [--status=proved|refuted|open|all] [--limit=N]
                        [--only=NAME[,NAME...]] [--cand=K]`
-/
import Tools.Bank
import FRJ.Search.Engine
import FRJ.Search.Fast

open FRJ

namespace RNFRJ

/-! ## Per-goal search -/

inductive Outcome where
  | hit
  | fixpoint
  | budget
  deriving DecidableEq

def Outcome.toString : Outcome → String
  | .hit      => "refuted"
  | .fixpoint => "no-derivation-at-fixpoint"
  | .budget   => "no-derivation-at-budget"

structure GoalResult where
  name : String
  out  : Outcome
  rounds : Nat
  rs : Nat
  is : Nat
  ms : Nat
  fams : Nat
  pfams : Nat

def runGoal (fast : Bool) (cfg : Search.Config) (nm : String) (G : Form) :
    IO GoalResult := do
  let t0 ← IO.monoMsNow
  let (hit, st, nf, np) :=
    if fast then
      let (db, st) := Search.saturateFast G cfg
      (Search.derivable G db, st.toStats, st.fams, st.pfams)
    else
      let (db, st) := Search.saturate G cfg
      (Search.derivable G db, st, 0, 0)
  let t1 ← IO.monoMsNow
  let atFixpoint := !st.lamCapped && !st.dbCapped && st.roundsUsed < cfg.rounds
  let out := if hit then Outcome.hit else if atFixpoint then .fixpoint else .budget
  return ⟨nm, out, st.roundsUsed, st.rsSize, st.isSize, t1 - t0, nf, np⟩

/-! ## Per-cell grading -/

def grade (s : RNBank.Status) (anyHit : Bool) (anyBudget : Bool) : String :=
  match s, anyHit with
  | .proved,  true  => "ENGINE-BUG (typed derivation against a kernel-checked Interd)"
  | .proved,  false => "control-ok"
  | .refuted, true  => "pass"
  | .refuted, false => if anyBudget then "miss-at-budget" else "miss-at-fixpoint"
  | .«open»,  true  => "NEW-REFUTATION (dictionary cell is FALSE)"
  | .«open»,  false => if anyBudget then "open-at-budget" else "open-at-fixpoint"

structure Tally where
  bug : Nat := 0
  ctrl : Nat := 0
  pass : Nat := 0
  miss : Nat := 0
  newRef : Nat := 0
  openStill : Nat := 0
  ms : Nat := 0

def Tally.bump (t : Tally) (s : RNBank.Status) (anyHit : Bool) (ms : Nat) : Tally :=
  let t := { t with ms := t.ms + ms }
  match s, anyHit with
  | .proved,  true  => { t with bug := t.bug + 1 }
  | .proved,  false => { t with ctrl := t.ctrl + 1 }
  | .refuted, true  => { t with pass := t.pass + 1 }
  | .refuted, false => { t with miss := t.miss + 1 }
  | .«open»,  true  => { t with newRef := t.newRef + 1 }
  | .«open»,  false => { t with openStill := t.openStill + 1 }

def runCell (fast : Bool) (cfg : Search.Config) (c : RNBank.Cell) (t : Tally) : IO Tally := do
  let mut res : List GoalResult := []
  for (nm, G) in c.forms do
    res := res ++ [← runGoal fast cfg nm G]
  let anyHit := res.any (fun r => r.out == .hit)
  let anyBudget := res.any (fun r => r.out == .budget)
  let ms := res.foldl (fun a r => a + r.ms) 0
  let detail := String.intercalate " " (res.map (fun r =>
    s!"{r.name}={r.out.toString}(r={r.rounds},RS={r.rs},IS={r.is},fam={r.fams},pfam={r.pfams},{r.ms}ms)"))
  IO.println s!"{c.name} [{c.status.toString}]: {grade c.status anyHit anyBudget} | {detail}"
  (← IO.getStdout).flush
  return t.bump c.status anyHit ms

/-! ## Driver -/

def getArg (args : List String) (key : String) : Option String :=
  (args.find? (fun a => a.startsWith ("--" ++ key ++ "="))).map
    (fun a => (a.drop (key.length + 3)).toString)

def getNat (args : List String) (key : String) (dflt : Nat) : Nat :=
  match getArg args key with
  | some s => s.toNat?.getD dflt
  | none   => dflt

def main (args : List String) : IO Unit := do
  let cfg : Search.Config := {
    rounds := getNat args "rounds" 10,
    jmax   := getNat args "jmax" 3,
    pmax   := getNat args "pmax" 2,
    lamCap := getNat args "lamcap" 10,
    maxRS  := getNat args "maxrs" 800,
    maxIS  := getNat args "maxis" 800 }
  let fast := (getArg args "engine").getD "fast" == "fast"
  let engineName := if fast then "fast" else "ref(frozen)"
  let statusSel := (getArg args "status").getD "all"
  let limit := getNat args "limit" 0
  let only := getArg args "only"
  -- `--cand=k` retargets each selected cell at representative `qk` instead
  -- of the one the table assigns.  An open cell carries a CANDIDATE LIST
  -- and is sorried at the first open candidate, so refuting the stated
  -- collapse only eliminates that candidate; this is how the survivors are
  -- attacked.  The status tag then no longer grades the goal, so cells run
  -- under `--cand` are reported but not tallied against the oracles.
  let cand := getArg args "cand"
  let sel := RNBank.cells.filter (fun c =>
    (statusSel == "all" || c.status.toString == statusSel) &&
    (match only with | some n => (n.splitOn ",").contains c.name | none => true))
  let sel := match cand with
    | none => sel
    | some k => match RNBank.reps[k.toNat?.getD 99]? with
      | some r => sel.map (fun (c : RNBank.Cell) => ⟨c.name, c.lhs, r, c.status⟩)
      | none   => sel
  let sel := if limit == 0 then sel else sel.take limit
  let banner := "RN(◯,{}) bank"
  IO.println s!"{banner}: {RNBank.cells.length} cells (proved {RNBank.count .proved}, refuted {RNBank.count .refuted}, open {RNBank.count .«open»}); running {sel.length}"
  IO.println s!"engine={engineName} rounds={cfg.rounds} jmax={cfg.jmax} pmax={cfg.pmax} lamCap={cfg.lamCap} maxRS={cfg.maxRS} maxIS={cfg.maxIS}"
  -- No silent caps: `seedsIC` enumerates the full valuation lattice only
  -- while |Ĝ_at| ≤ 4, and above that tries three valuations.  Report the
  -- worst |Ĝ_at| over the selected goals so a capped run is never read as
  -- an exhaustive one.  (RN(◯,{}) is variable-free, so this is 0 there.)
  let maxAt : Nat := sel.foldl (fun (m : Nat) (c : RNBank.Cell) =>
    c.forms.foldl (fun (m : Nat) (p : String × Form) =>
      max m (FRJ.gAt p.2).length) m) 0
  IO.println (if maxAt ≤ 4 then
      s!"seedsIC valuation lattice: FULL on every goal (max |Ĝ_at| = {maxAt} ≤ 4)"
    else
      s!"seedsIC valuation lattice: CAPPED — max |Ĝ_at| = {maxAt} > 4, so goals above the cap try 3 valuations, not 2^|Ĝ_at|")
  let mut t : Tally := ({} : Tally)
  for c in sel do
    t ← runCell fast cfg c t
  IO.println s!"-- summary: ENGINE-BUG={t.bug} control-ok={t.ctrl} pass={t.pass} miss={t.miss} NEW-REFUTATION={t.newRef} open-still={t.openStill} | {t.ms}ms"

end RNFRJ

def main (args : List String) : IO Unit := RNFRJ.main args
