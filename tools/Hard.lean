/-
# The escalation ladder: goals past what the old tools reach

`frjdiff` compares engines on the RN(◯,{}) bank, whose hardest cell
(`cAnd_8_11`) `Fast` settles in 133 s.  This runs a ladder of goals built
to be LARGER than that, and runs ONE engine per invocation so the caller
can impose a real timeout — Lean cannot interrupt a pure computation, so
a per-engine budget has to be a process budget.

    lake exe frjhard --goal=N --engine=prof|fast|ljf [--fuel=N] [--rounds=N]

`--engine=prof` is the profile-indexed FRJ(◯) (both Profile Lemmas, no
arity cap anywhere); `fast` is the clique engine with `jmax`/`pmax`;
`ljf` is `TwoSidedLink.searchProves`, the proof engine, which answers a
DIFFERENT question and is here for contrast, not as a competitor.
-/
import FRJ.Search.Profile
import FRJ.Bridge
import LaxLogic.RN.Reps
import wip.ljfo_link
import LaxLogic.PLLSearch

open FRJ

namespace FrjHard

/-- Subformula count, so "larger" is a number rather than an impression. -/
def size : Form → Nat
  | .atom _ => 1
  | .bot => 1
  | .and a b => 1 + size a + size b
  | .or a b => 1 + size a + size b
  | .imp a b => 1 + size a + size b
  | .circ a => 1 + size a

open RNReps in
/-- The ladder, in PLL syntax, translated by `FRJ.ofPLL`.  Each rung adds
one more representative to the antecedent or one more layer of nesting,
so the derived database grows. -/
def ladder : List (String × PLLFormula) :=
  [ ("H1  (q8 ∧ q11) ⊃ q15",                    .ifThen (.and q8 q11) q15)
  , ("H2  (q8 ∧ q11 ∧ q13) ⊃ q15",              .ifThen (.and q8 (.and q11 q13)) q15)
  , ("H3  (q8 ∧ q11 ∧ q13 ∧ q14) ⊃ q15",        .ifThen (.and q8 (.and q11 (.and q13 q14))) q15)
  , ("H4  ((q8 ∧ q11) ⊃ (q13 ∧ q14)) ⊃ q15",    .ifThen (.ifThen (.and q8 q11) (.and q13 q14)) q15)
  , ("H5  ◯((q8 ∧ q11) ⊃ q13) ⊃ (q14 ∨ q15)",   .ifThen (.somehow (.ifThen (.and q8 q11) q13)) (.or q14 q15))
  , ("H6  (q8 ∧ q11 ∧ q13 ∧ q14 ∧ q15) ⊃ q10",  .ifThen (.and q8 (.and q11 (.and q13 (.and q14 q15)))) q10) ]

/-- The converse of a top-level implication.  `H1 … H6` are all `A ⊃ B`,
so this is `B ⊃ A` — the other half of the interderivability question. -/
def converse : PLLFormula → PLLFormula
  | .ifThen a b => .ifThen b a
  | φ => φ

def getNat (args : List String) (k : String) (d : Nat) : Nat :=
  match args.find? (fun a => a.startsWith ("--" ++ k ++ "=")) with
  | some a => ((a.drop (k.length + 3)).toString.toNat?).getD d
  | none => d

def getStr (args : List String) (k : String) (d : String) : String :=
  match args.find? (fun a => a.startsWith ("--" ++ k ++ "=")) with
  | some a => (a.drop (k.length + 3)).toString
  | none => d

def main (args : List String) : IO Unit := do
  let n := getNat args "goal" 1
  let eng := getStr args "engine" "prof"
  let cfg : Search.Config := {
    rounds := getNat args "rounds" 10, jmax := getNat args "jmax" 3,
    pmax := getNat args "pmax" 2, lamCap := (fun n => if n == 0 then 1000000 else n) (getNat args "lamcap" 10),
    maxRS := getNat args "maxrs" 800, maxIS := getNat args "maxis" 800 }
  let conv := args.contains "--converse"
  match ladder[n - 1]? with
  | none => IO.println s!"no such goal: {n} (ladder has {ladder.length})"
  | some (nm0, φ0) =>
      let φ := if conv then converse φ0 else φ0
      let nm := if conv then s!"CONVERSE of {nm0}" else nm0
      let G := ofPLL φ
      IO.println s!"goal {n}: {nm}   |G| = {size G}   engine = {eng}"
      (← IO.getStdout).flush
      let t0 ← IO.monoMsNow
      match eng with
      | "ljf" =>
          let fuels := [8, 12, 16, 20, 24, 28, 32, 40, 44, 52]
          match fuels.find? (fun f => TwoSidedLink.searchProves f [] φ) with
          | some f =>
              let t1 ← IO.monoMsNow
              IO.println s!"  LJF◯: PROVED at fuel {f}  [{t1 - t0} ms]"
          | none =>
              let t1 ← IO.monoMsNow
              IO.println s!"  LJF◯: not found up to fuel 52 — CERTIFIES NOTHING  [{t1 - t0} ms]"
      | "g4c" =>
          -- The G4c certificate engine is TWO-SIDED: `.proved` carries a
          -- `G4cTm` proof term, `.refuted` a `FinCM` the checker accepts.
          -- So it is an independent check on FRJ(◯)'s negative answers.
          let b := getNat args "budget" 20000
          match PLLND.Search.decide { findBudget := some b, emitClosureCap := 0 } [] φ with
          | .proved _ =>
              let t1 ← IO.monoMsNow
              IO.println s!"  G4c: PROVED (G4cTm certificate)  [budget {b}, {t1 - t0} ms]"
          | .refuted M w _ =>
              let t1 ← IO.monoMsNow
              IO.println s!"  G4c: REFUTED (checked FinCM, {M.n} worlds, root {w})  [budget {b}, {t1 - t0} ms]"
          | .unknown =>
              let t1 ← IO.monoMsNow
              IO.println s!"  G4c: unknown at budget {b} — CERTIFIES NOTHING  [{t1 - t0} ms]"
      | "fast" =>
          let (db, st) := Search.saturateFast G cfg
          let hit := Search.derivable G db
          let t1 ← IO.monoMsNow
          let v := if hit then "REFUTED (countermodel built)" else "NO REFUTATION FOUND"
          IO.println s!"  FRJ(◯) Fast: {v}  [r={st.roundsUsed}/{cfg.rounds} RS={st.rsSize} IS={st.isSize} fams={st.fams} pfams={st.pfams} jmaxBound={st.jmaxBinding} pmaxBound={st.pmaxBinding} {t1 - t0} ms]"
      | _ =>
          let (db, st) := Search.saturateProf G cfg
          let hit := Search.derivable G db
          let t1 ← IO.monoMsNow
          let v := if hit then "REFUTED (countermodel built)" else "NO REFUTATION FOUND"
          -- every cap, so a cap-free closure is visible rather than inferred
          let capFree := !st.lamCapped && !st.dbCapped
                         && st.roundsUsed < cfg.rounds
          let caps := (if st.lamCapped then ["lamCap"] else [])
                   ++ (if st.dbCapped then ["maxRS/maxIS"] else [])
                   ++ (if st.roundsUsed ≥ cfg.rounds then ["rounds"] else [])
          let capStr := if caps.isEmpty then "NONE" else String.intercalate "+" caps
          let outcome := if hit then "a countermodel was constructed"
                         else if capFree then "CLOSED (no cap bound, no arity cap)"
                         else "not-found-within-bound"
          IO.println s!"  FRJ(◯) Profile: {v} — {outcome}  [r={st.roundsUsed}/{cfg.rounds} RS={st.rsSize} IS={st.isSize} fams={st.fams} pfams={st.pfams} caps={capStr} {t1 - t0} ms]"
      (← IO.getStdout).flush

end FrjHard

def main (args : List String) : IO Unit := FrjHard.main args
