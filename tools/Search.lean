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

Verdict vocabulary (repo standard; there is no CERTAIN category).  Two
negative outcomes, and they are genuinely different:

* `not-found-within-bound` — the search stopped with at least one cap
  binding.  A limitation of the run, never a statement about the
  sequent; the whole `Config` is printed so a re-run knows every
  dimension it can raise.
* `closed-no-cap-bound` — saturation reached `fresh == 0` with NO
  recorded cap binding.  Still not "no countermodel exists", but a much
  stronger situation, and the one worth escalating: if FRJ(◯) is
  complete it means the goal is PROVABLE, so the move is to run the
  proof engine.  See `lake exe frjterm`.

WITHDRAWN 2026-08-21: `no-derivation-at-fixpoint`.  This tool used to
split the negative case, reporting a "fixpoint" when
`!lamCapped && !dbCapped && roundsUsed < rounds`.  That reads THREE of the
five things that can truncate a round: `Config` also carries `jmax` and
`pmax`, and `roundStep` forms premise families only up to those arities,
which `Stats` did not record at all (it does now — `jmaxBinding` /
`pmaxBinding`, added the same day).  So the flag was blind to exactly the
two caps most likely to bind, and there is precedent for it firing falsely
— `FRJ/Search/Engine.lean` records that on 2026-08-17 a gap in the zone
enumeration made the engine "report a rule-closure fixpoint without the
goal".  Repaired for that cause; the arity cause was never closed.

The label is DELETED rather than repaired, because "fixpoint" will be read
as exhaustion whatever the docstring says, and three legitimate fixpoint
notions sit next to it in this codebase (`FRJ/Saturate.lean`'s `AllMet`
demand-closure, and `FRJ/Search/Fast.lean`'s Fast-vs-Engine agreement) to
lend it credibility it never had.  What WOULD justify a genuine "no
derivation exists" verdict is a bound on FRJ(◯)'s join arity in terms of
the goal's finite subformula universe, making the arity truncation
provably non-binding.  There is no such theorem, so there is no such
outcome.

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

/-- Three outcomes.  Neither negative one says "no countermodel exists". -/
inductive Outcome where
  | hit
  /-- Saturation reached `fresh == 0` with NO recorded cap binding: the
  rule set, run to its own closure, produced nothing new.

  This is NOT the deleted `fixpoint` flag returning.  That one was
  computed from three of the five things that can truncate a round and
  fired on runs where both arity caps were cutting the enumeration.  This
  one reads all five, which only became possible when `jmaxBinding` /
  `pmaxBinding` were added to `FRJ.Search.Stats` on 2026-08-21.

  What it does NOT license: "there is no countermodel".  `fresh == 0`
  still depends on the subsumption in `insertAllR`/`insertAllI` not
  over-subsuming, which is unproved, and on `Certified.SearchComplete`,
  which is OPEN.

  What it IS good for: **if FRJ(◯) is complete, a cap-free closure with
  no refutation means the goal is PROVABLE** — so the next move is to run
  the proof engine, which is sound AND complete
  (`TwoSidedLink.searchProves_complete`).  Agreement confirms the
  closure; a proof engine that also finds nothing, at fuel high enough to
  matter, is a candidate incompleteness witness for FRJ(◯).  `lake exe
  frjterm` does exactly this pairing, and demonstrates the outcome is not
  vacuous: `p ⊃ ◯p` closes cap-free in two rounds and the prover proves
  it at fuel 8. -/
  | closed
  /-- Stopped with at least one cap binding.  NOT FOUND within the
  `Config` given; never "does not exist". -/
  | noneAt
  deriving DecidableEq

def Outcome.toString : Outcome → String
  | .hit    => "refuted"
  | .closed => "closed-no-cap-bound"
  | .noneAt => "not-found-within-bound"

structure GoalResult where
  name : String
  out  : Outcome
  rounds : Nat
  rs : Nat
  is : Nat
  ms : Nat
  fams : Nat
  pfams : Nat
  /-- Every cap the run could have hit, so a `noneAt` is re-runnable
  without re-deriving why it stopped. -/
  lamCapped : Bool
  dbCapped : Bool
  jmaxBinding : Bool
  pmaxBinding : Bool

/-- The caps that actually bound this run, as a printable list.  Empty
means no recorded cap truncated anything — which is NOT a fixpoint claim:
`fresh == 0` also depends on the subsumption in `insertAllR`/`insertAllI`
not over-subsuming, and that is unproved. -/
def GoalResult.bindingCaps (r : GoalResult) : String :=
  let l := (if r.lamCapped then ["lamCap"] else [])
        ++ (if r.dbCapped then ["maxRS/maxIS"] else [])
        ++ (if r.jmaxBinding then ["jmax"] else [])
        ++ (if r.pmaxBinding then ["pmax"] else [])
        ++ (if r.rounds > 0 then [] else [])
  if l.isEmpty then "none-recorded" else String.intercalate "+" l

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
  let capFree := !st.lamCapped && !st.dbCapped && !st.jmaxBinding
                 && !st.pmaxBinding && st.roundsUsed < cfg.rounds
  let out := if hit then Outcome.hit else if capFree then .closed else .noneAt
  return ⟨nm, out, st.roundsUsed, st.rsSize, st.isSize, t1 - t0, nf, np,
          st.lamCapped, st.dbCapped, st.jmaxBinding, st.pmaxBinding⟩

/-! ## Per-cell grading -/

/-- **The status tags this grades against are WITHDRAWN** (see
`Tools/Bank.lean`), so `ENGINE-BUG` and `NEW-REFUTATION` are currently
claims about an unsound oracle, not about the engine or the cell.  The
strings are kept so a regenerated bank makes the harness live again; until
then read only the per-goal outcomes.  Rebuilding the oracle is Phase 3 of
the layer plan. -/
def grade (s : RNBank.Status) (anyHit : Bool) : String :=
  match s, anyHit with
  | .proved,  true  => "ENGINE-BUG? (typed derivation against a cell tagged proved)"
  | .proved,  false => "control-ok"
  | .refuted, true  => "pass"
  | .refuted, false => "miss"
  | .«open»,  true  => "NEW-REFUTATION? (cell tagged open, engine refutes)"
  | .«open»,  false => "open-still"

/-- Cells whose search CLOSED cap-free are the ones to hand to the proof
engine: on those, and only those, a completeness assumption would turn
"no refutation" into "provable". -/
def escalate (res : List GoalResult) : Bool := res.any (fun r => r.out == .closed)

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
  let ms := res.foldl (fun a r => a + r.ms) 0
  let detail := String.intercalate " " (res.map (fun r =>
    s!"{r.name}={r.out.toString}(r={r.rounds},RS={r.rs},IS={r.is},fam={r.fams},pfam={r.pfams},caps={r.bindingCaps},{r.ms}ms)"))
  IO.println s!"{c.name} [{c.status.toString}]: {grade c.status anyHit} | {detail}"
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
    lamCap := (fun n => if n == 0 then 1000000 else n) (getNat args "lamcap" 10),
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
