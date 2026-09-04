/-
# `checkprobe` — the untrusted engine + verified `checkClosed`, with its gate watch

Per cell: run the W-engine (`FRJ.Search.W.wOps`, `saturateO`), carry its
store into contract rows (`rowsOfDBO`), certify with `checkClosed`
(wip/check_closed.lean), decide through `decideGbuW_of_check`, and set
the verdict beside the G4c certificate oracle (`PLLND.Search.settle`).

  * `PASS`   — the store is certified and the decision agrees with the
               oracle (or the oracle is unknown and the store certified).
  * `ALARM`  — the store is certified and the decision DISAGREES with the
               oracle: a soundness alarm in one of the two — escalate.
  * `FLAG`   — the engine's store is NOT certified at this budget
               (`not-closed-within-bound`, never a verdict): raise
               `jmax`/`pmax`/rounds, never drop.

The gate watch (CLAUDE.md: never ship a gate you have not watched fail),
on every certified store:

  * `gate-join` — delete every join-built row (the rows whose derivation
    is one of the eight `join*` constructors) and require `checkClosed`
    to go `false`; `n/a` where the store has no join rows.
  * `gate-drop` — delete the FIRST row and require `false`.

Exit code 1 on any ALARM or any gate that did not fail.
-/
import wip.check_closed
import FRJ.Bridge
import LaxLogic.PLLSearch
import wip.ljfo_link

open FRJ FRJ.Search FRJ.Gbu.W FRJ.Arity Form

namespace CheckProbe

abbrev P := PLLFormula

def p : P := .prop "p"
def q : P := .prop "q"
def r : P := .prop "r"
def z : P := .prop "z"

/-- `(⋀_{j=1..n} (pⱼ ⊃ q)) ⊃ q`: the A2 witness, needs an `n`-ary `⋈At`. -/
def witnessA2 (n : Nat) : P :=
  let imps := (List.range n).map (fun j => PLLFormula.ifThen (.prop s!"p{j + 1}") q)
  let conj := match imps with
    | [] => q
    | a :: rest => rest.foldl (fun acc x => PLLFormula.and acc x) a
  .ifThen conj q

def cells : List (String × P) := [
  ("p ⊃ p            [valid]", .ifThen p p),
  ("⊥ ⊃ ⊥            [valid]", .ifThen .falsePLL .falsePLL),
  ("p ⊃ ◯p           [valid]", .ifThen p (.somehow p)),
  ("◯◯p ⊃ ◯p         [valid]", .ifThen (.somehow (.somehow p)) (.somehow p)),
  ("◯p ⊃ ◯◯p         [valid]", .ifThen (.somehow p) (.somehow (.somehow p))),
  ("(◯p∧◯q) ⊃ ◯(p∧q) [valid]", .ifThen ((PLLFormula.somehow p).and (.somehow q))
      (.somehow (p.and q))),
  ("licence cell w    [valid]", .ifThen (.somehow ((PLLFormula.ifThen (.somehow p) r).and
      (.somehow p))) ((PLLFormula.somehow r).or z)),
  ("G2 = A2 witness   [inv]", witnessA2 2),
  ("G3 = A2 witness   [inv]", witnessA2 3),
  ("p                 [inv]", p),
  ("⊥                 [inv]", .falsePLL),
  ("◯⊥                [inv]", .somehow .falsePLL),
  ("¬◯⊥               [inv]", .ifThen (.somehow .falsePLL) .falsePLL),
  ("◯p ⊃ p   (Gcr)    [inv]", .ifThen (.somehow p) p),
  ("◯(◯p ⊃ p) (Gcc)   [inv]", .somehow (.ifThen (.somehow p) p)),
  ("◯(p∨q) ⊃ ◯p∨◯q    [inv]", .ifThen (.somehow (p.or q))
      ((PLLFormula.somehow p).or (.somehow q))),
  ("big-ante variant  [inv]", .ifThen (.somehow ((PLLFormula.ifThen (.somehow p) q).and
      (.somehow p))) (.somehow r)),
  ("p ∨ ¬p            [inv]", p.or (.ifThen p .falsePLL)),
  ("Peirce            [inv]", .ifThen (.ifThen (.ifThen p q) p) p),
  ("◯p ∨ ¬◯p          [inv]", (PLLFormula.somehow p).or (.ifThen (.somehow p) .falsePLL))
]

def engineCfg : Config := { rounds := 16, jmax := 3, pmax := 2, lamCap := 24, maxRS := 3000, maxIS := 3000 }

def oracle (φ : P) : String :=
  match PLLND.Search.settle {} [] φ with
  | .proved _ => "valid"
  | .refuted _ _ _ => "invalid"
  | .unknown => "unknown"

def flags (st : Stats) : String :=
  let l := [(st.lamCapped, "lamCap"), (st.dbCapped, "dbCap"),
            (st.jmaxBinding, "jmax"), (st.pmaxBinding, "pmax")]
  match (l.filter (·.1)).map (·.2) with
  | [] => "-"
  | fs => String.intercalate "," fs

/-- Is a regular derivation join-built? -/
def isJoinR {G : Form} {t : Tag} {Γ : List Form} {C : Form} : FRJWr G t Γ C → Bool
  | .joinAt .. => true
  | .joinAtP .. => true
  | .joinAtF .. => true
  | .joinOr .. => true
  | .joinOrP .. => true
  | .joinOrF .. => true
  | .joinCirc .. => true
  | .joinCircP .. => true
  | _ => false

def isJoinRow {G : Form} : WRow G → Bool
  | ⟨.reg _ _ _, d⟩ => isJoinR d
  | ⟨.irr _ _ _, _⟩ => false

/-- The decision, as a string, from a certified store. -/
def decisionOf (G : Form) (rows : List (WRow G)) : String :=
  if h : checkClosed G rows = true then
    match decideGbuW_of_check rows h with
    | .inl _ => "PROVABLE"
    | .inr _ => "DISPROVABLE"
  else "NOT-CLOSED"

/-- Returns (alarm?, gate-failed?). -/
def runCell (cfg : Config) (nm : String) (φ : P) : IO (Bool × Bool) := do
  let G := ofPLL φ
  let t0 ← IO.monoMsNow
  let (db, st) := saturateO (W.wOps G) cfg
  let rows := rowsOfDBO G db
  let t1 ← IO.monoMsNow
  let chk := checkClosed G rows
  let t2 ← IO.monoMsNow
  let dec := if chk then decisionOf G rows else "NOT-CLOSED"
  let ov := oracle φ
  let verdict :=
    match ov, dec with
    | "valid", "PROVABLE" => "PASS"
    | "invalid", "DISPROVABLE" => "PASS"
    | "unknown", "NOT-CLOSED" => "FLAG"
    | _, "NOT-CLOSED" => "FLAG"
    | "unknown", _ => "PASS(oracle unknown)"
    | _, _ => "ALARM"
  let joinRows := rows.filter isJoinRow
  let mut gateFail := false
  let mut gateJoin := "n/a"
  let mut gateDrop := "n/a"
  if chk then
    if joinRows.length > 0 then
      let rows' := rows.filter (fun x => !isJoinRow x)
      let c' := checkClosed G rows'
      gateJoin := if c' then "FAIL(still true)" else "ok(false)"
      if c' then gateFail := true
    let rows'' := rows.drop 1
    let c'' := checkClosed G rows''
    gateDrop := if c'' then "FAIL(still true)" else "ok(false)"
    if c'' then gateFail := true
  IO.println s!"{verdict}  {nm}  oracle={ov}  decision={dec}  rows={rows.length} (reg {db.rs.length}, irr {db.is.length}, join-built {joinRows.length})  engine={t1 - t0}ms check={t2 - t1}ms rounds={st.roundsUsed} caps={flags st}  gate-join={gateJoin} gate-drop={gateDrop}"
  pure (verdict == "ALARM", gateFail)

/-- `--semi-naive` runs the engine's differential round
(`Config.semiNaive`, `FRJ/Search/Core.lean`); DEFAULT OFF, as the field
itself is.  The certificate does not depend on it — `checkClosed`
verifies whatever store the engine produced — so the flag can only
change the ENGINE column and, if the delta logic were incomplete, turn a
`PASS` into a `FLAG` (`NOT-CLOSED`).  It can never turn one into an
`ALARM` without `checkClosed` being wrong too. -/
def main (argv : List String) : IO UInt32 := do
  let cfg := if argv.contains "--semi-naive" then { engineCfg with semiNaive := true }
             else engineCfg
  IO.println s!"checkprobe: {cells.length} cells, engine cfg rounds={cfg.rounds} jmax={cfg.jmax} pmax={cfg.pmax} lamCap={cfg.lamCap} semiNaive={cfg.semiNaive}"
  let mut alarms := 0
  let mut gateFails := 0
  for (nm, φ) in cells do
    let (a, g) ← runCell cfg nm φ
    if a then alarms := alarms + 1
    if g then gateFails := gateFails + 1
  IO.println s!"checkprobe: alarms={alarms} gate-failures={gateFails}"
  pure (if alarms == 0 && gateFails == 0 then 0 else 1)

end CheckProbe

def main (argv : List String) : IO UInt32 := CheckProbe.main argv
