/-
# Is the THIRD outcome reachable?

`tools/Search.lean` reports two outcomes, `hit` and `not-found-within-bound`,
after the old `no-derivation-at-fixpoint` was deleted on 2026-08-21 for
reading only three of the five things that can truncate a round.

But there IS a third, genuinely different situation, and it only became
CHECKABLE on the same day, when `jmaxBinding` / `pmaxBinding` were added
to `FRJ.Search.Stats`:

    the saturation reached `fresh == 0` with NO recorded cap binding.

That is not "ran out of budget".  It is "the rule set, run to its own
closure, produced nothing new".  And it matters because of what it would
mean: **if FRJ(◯) is complete, a clean closure with no countermodel says
the goal is PROVABLE.**  The follow-up is then to run the proof engine,
which IS proved sound and complete — `TwoSidedLink.searchProves`.  If
that finds a proof, the two agree.  If it does not, one of them is
incomplete, and since `searchProves_complete` is proved, the finger
points at FRJ(◯).  That is the incompleteness miner in its smallest form.

This probe answers only the prior question: **is the outcome reachable at
all**, or is it vacuous?  If no run can ever close without a cap binding,
the third outcome should not exist.

Every goal below is a PLL THEOREM containing ◯, except the two controls.
By `FRJ.soundness` a refutation of a theorem is impossible, so the only
outcomes available on them are `closed` and `not-found-within-bound` —
which is what makes them the right test cells.

    lake exe frjterm [--rounds=N] [--jmax=N] [--pmax=N] [--lamcap=N]
-/
import FRJ.Search.Fast
import FRJ.Bridge
import Tools.Engines

open FRJ

namespace FrjTerminate

def p : Form := .atom "p"
def q : Form := .atom "q"

/-- Goal formulas.  `provable = true` means PLL ⊢ this, so FRJ(◯) MUST
NOT find a refutation; `false` means it should. -/
structure Cell where
  name : String
  provable : Bool
  form : Form

def cells : List Cell :=
  [ ⟨"unit          p ⊃ ◯p",              true,  .imp p (.circ p)⟩
  , ⟨"mult          ◯◯p ⊃ ◯p",            true,  .imp (.circ (.circ p)) (.circ p)⟩
  , ⟨"mono          ◯(p ∧ q) ⊃ ◯p",       true,  .imp (.circ (.and p q)) (.circ p)⟩
  , ⟨"strength      ◯p ∧ ◯q ⊃ ◯(p ∧ q)",  true,  .imp (.and (.circ p) (.circ q)) (.circ (.and p q))⟩
  , ⟨"K             ◯(p ⊃ q) ⊃ (◯p ⊃ ◯q)", true, .imp (.circ (.imp p q)) (.imp (.circ p) (.circ q))⟩
  , ⟨"triv          ◯⊥ ⊃ ◯⊥",             true,  .imp (.circ .bot) (.circ .bot)⟩
  , ⟨"CONTROL       ◯p ⊃ p   (NOT a theorem)", false, .imp (.circ p) p⟩
  , ⟨"CONTROL       ¬◯⊥      (NOT a theorem)", false, .imp (.circ .bot) .bot⟩ ]

/-- The three-way classification.  `closed` is stated in the weakest form
that is defensible: no RECORDED cap bound this run.  It is not a claim
that no countermodel exists — `fresh == 0` still depends on the
subsumption layer in `insertAllR`/`insertAllI` not over-subsuming, which
is unproved.  What would license the strong reading is
`Certified.SearchComplete`, which is OPEN. -/
inductive Outcome3 where | hit | closed | noneAt
  deriving DecidableEq

def classify (hit : Bool) (st : Search.Stats) (cfg : Search.Config) : Outcome3 :=
  if hit then .hit
  else if !st.lamCapped && !st.dbCapped && !st.jmaxBinding && !st.pmaxBinding
          && st.roundsUsed < cfg.rounds then .closed
  else .noneAt

def caps (st : Search.Stats) : String :=
  let l := (if st.lamCapped then ["lamCap"] else [])
        ++ (if st.dbCapped then ["maxRS/maxIS"] else [])
        ++ (if st.jmaxBinding then ["jmax"] else [])
        ++ (if st.pmaxBinding then ["pmax"] else [])
  if l.isEmpty then "NONE" else String.intercalate "+" l

def getNat (args : List String) (k : String) (d : Nat) : Nat :=
  match args.find? (fun a => a.startsWith ("--" ++ k ++ "=")) with
  | some a => ((a.drop (k.length + 3)).toString.toNat?).getD d
  | none => d

/-- The fuel ladder from `docs/two-sided-engine.md`: every one of the 462
ρ-order cells that is derivable was found at fuel ≤ 44. -/
def fuels : List Nat := [8, 12, 16, 20, 24, 28, 32, 40, 44]

/-- Run the PROOF engine on the same cell.  `searchProves` is sound AND
complete (`TwoSidedLink.searchProves_complete`), but the completeness is
"at SOME fuel": a `false` at any particular fuel certifies nothing.  So
`none` here means NOT FOUND up to fuel 44, never "unprovable". -/
def proveAt (φ : PLLFormula) : Option Nat :=
  fuels.find? (fun f => TwoSidedLink.searchProves f [] φ)

def run (cfg : Search.Config) : IO Unit := do
  IO.println s!"rounds={cfg.rounds} jmax={cfg.jmax} pmax={cfg.pmax} \
lamCap={cfg.lamCap} maxRS={cfg.maxRS} maxIS={cfg.maxIS}"
  IO.println ""
  let mut nClosed := 0
  let mut nNone := 0
  let mut nHit := 0
  let mut wrong : List String := []
  for c in cells do
    let t0 ← IO.monoMsNow
    let (db, st) := Search.saturateFast c.form cfg
    let hit := Search.derivable c.form db
    let t1 ← IO.monoMsNow
    let s := st.toStats
    let o := classify hit s cfg
    let tag := match o with
      | .hit => "REFUTED"
      | .closed => "CLOSED  (no cap bound)"
      | .noneAt => "not-found-within-bound"
    match o with
    | .hit => nHit := nHit + 1
    | .closed => nClosed := nClosed + 1
    | .noneAt => nNone := nNone + 1
    -- soundness cross-check: a refutation of a THEOREM would contradict
    -- FRJ.soundness, so it is an engine defect, not a result.
    if hit && c.provable then
      wrong := wrong ++ [s!"{c.name}: refuted a PLL THEOREM — contradicts FRJ.soundness"]
    IO.println s!"{c.name}"
    IO.println s!"    FRJ(◯):  {tag}  [r={s.roundsUsed}/{cfg.rounds} RS={s.rsSize} \
IS={s.isSize} caps={caps s} {t1 - t0}ms]"
    -- the PROOF engine on the same cell, through FRJ.toPLL
    let t2 ← IO.monoMsNow
    let pf := proveAt (toPLL c.form)
    let t3 ← IO.monoMsNow
    let pstr := match pf with
      | some f => s!"PROVED at fuel {f}"
      | none   => s!"not found up to fuel 44 (certifies NOTHING)"
    IO.println s!"    LJF◯:    {pstr}  [{t3 - t2}ms]"
    -- the joint reading: this is the incompleteness miner in miniature
    let joint := match o, pf with
      | .closed, some _ =>
          "AGREE — FRJ(◯) closed cap-free and the complete prover found a proof"
      | .closed, none =>
          "!! CANDIDATE INCOMPLETENESS WITNESS for FRJ(◯): closed cap-free, \
yet no proof at fuel 44.  Raise the fuel before believing it."
      | .hit, some _ =>
          "!! ENGINE DEFECT — refuted AND proved; two_sided_disjoint forbids this"
      | .hit, none => "AGREE — refuted, and no proof found"
      | .noneAt, some f => s!"consistent — FRJ(◯) hit a cap; the prover settled it at fuel {f}"
      | .noneAt, none => "both stopped short; nothing concluded"
    IO.println s!"    ⇒ {joint}"
    (← IO.getStdout).flush
  IO.println ""
  IO.println s!"-- REFUTED={nHit}  CLOSED={nClosed}  not-found={nNone}"
  IO.println (if nClosed > 0 then
      "-- The third outcome IS reachable: a run closed with no cap binding."
    else
      "-- No run closed cap-free at this Config; the third outcome was not \
observed here.")
  for w in wrong do IO.println s!"!! ENGINE DEFECT: {w}"

end FrjTerminate

def main (args : List String) : IO Unit :=
  FrjTerminate.run
    { rounds := FrjTerminate.getNat args "rounds" 10,
      jmax   := FrjTerminate.getNat args "jmax" 3,
      pmax   := FrjTerminate.getNat args "pmax" 2,
      lamCap := (fun n => if n == 0 then 1000000 else n) (FrjTerminate.getNat args "lamcap" 10),
      maxRS  := FrjTerminate.getNat args "maxrs" 800,
      maxIS  := FrjTerminate.getNat args "maxis" 800 }
