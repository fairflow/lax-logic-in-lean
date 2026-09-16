/-
# `LaxLogic.QLL.CLPWolfram` — Wolfram as an untrusted constraint solver, through the bridge

Run with `scripts/clp-wolfram.sh`.  Local only: the Lean–Wolfram bridge is the
sibling repository `mathematica-in-lean` (same toolchain, same mathlib commit),
put on `LEAN_PATH` by the script rather than made a Lake dependency; nothing
imports this file.

Wolfram finds, Lean checks.  Through the bridge's persistent kernel, Wolfram is
asked for a satisfying instance (`FindInstance`), for Farkas multipliers refuting
an infeasible system (`FindInstance` on the dual system), and for the least
value of a variable (`Minimize`), whose lower bound is then refuted below by
Farkas multipliers.  Every answer goes through `certifyVerdict` or
`lowerBoundCert`, the same proved-sound checkers as the in-Lean Fourier–Motzkin
solver, so Wolfram is outside the trusted base: a wrong answer comes back as
"unknown", never as a wrong verdict.
-/
import Mathematica
import LaxLogic.QLL.CLPExamples

namespace LaxLogic.QLL.CLPWolfram

open LaxLogic.QLL LaxLogic.QLL.Engine LaxLogic.QLL.LinQ LaxLogic.QLL.CLPExamples

/-- The payload of a wire-form string `T["…"]`. -/
def unwire (s : String) : String :=
  String.ofList (((s.toList.dropWhile (· != '"')).drop 1).takeWhile (· != '"'))

/-- The variables of a system, each once. -/
def varsOf (cs : List LinCon) : List String :=
  (cs.flatMap fun c => c.e.terms.map (·.1)).eraseDups

/-- The Wolfram symbol for a variable. -/
def sym (vs : List String) (x : String) : String := s!"v{vs.idxOf x}"

/-- A Wolfram list. -/
def wlList (xs : List String) : String := "{" ++ ", ".intercalate xs ++ "}"

/-- A linear expression in Wolfram syntax. -/
def wlLin (vs : List String) (e : Lin) : String :=
  "(" ++ " + ".intercalate ((e.terms.map fun p => s!"({p.2})*{sym vs p.1}") ++ [s!"({e.const})"]) ++ ")"

/-- A constraint in Wolfram syntax. -/
def wlCon (vs : List String) (c : LinCon) : String :=
  wlLin vs c.e ++ (match c.k with | .le => " <= 0" | .lt => " < 0" | .eq => " == 0")

/-- Values of `vars` in the first instance of `cons`, comma-separated, or `none`. -/
def findCmd (cons vars : List String) : String :=
  s!"Module[\{r = FindInstance[{wlList cons}, {wlList vars}, Reals]}, If[r === \{}, \"none\", StringRiffle[ToString[#, InputForm] & /@ ({wlList vars} /. First[r]), \",\"]]]"

/-- Rationals from Wolfram's comma-separated reply. -/
def parseVals (s : String) : Option (List ℚ) :=
  if s.isEmpty then some [] else (s.splitOn ",").mapM parseRat?

/-- Send a command through the bridge and unwrap the string reply. -/
def ask (t : Mathematica.Transport) (cmd : String) : IO String :=
  return unwire (← Mathematica.executeRaw t cmd)

/-- A satisfying assignment found by Wolfram (not yet checked). -/
def wolframSat (t : Mathematica.Transport) (cs : List LinCon) : IO (Option (List (String × ℚ))) := do
  let vs := varsOf cs
  let r ← ask t (findCmd (cs.map (wlCon vs)) ((List.range vs.length).map fun i => s!"v{i}"))
  if r == "none" then return none
  return (parseVals r).map (vs.zip ·)

/-- Farkas multipliers found by Wolfram (not yet checked): `λᵢ ≥ 0` off the
equations, `Σ λᵢ aᵢ = 0` for every variable, and a positive constant, or a
non-negative one with some strict constraint used. -/
def wolframFarkas (t : Mathematica.Transport) (cs : List LinCon) : IO (Option (List ℚ)) := do
  let vs := varsOf cs
  let ci := cs.zipIdx
  let ls := (List.range cs.length).map fun i => s!"l{i}"
  let nonneg := (ci.filter (·.1.k != .eq)).map fun p => s!"l{p.2} >= 0"
  let coeff (x : String) : String :=
    let ts := (ci.filter fun p => zc x p.1.e.terms != 0).map fun p => s!"({zc x p.1.e.terms})*l{p.2}"
    if ts.isEmpty then "0" else " + ".intercalate ts
  let zeros := vs.map fun x => coeff x ++ " == 0"
  let cterms := (ci.filter (·.1.e.const != 0)).map fun p => s!"({p.1.e.const})*l{p.2}"
  let csum := if cterms.isEmpty then "0" else " + ".intercalate cterms
  let strict := (ci.filter (·.1.k == .lt)).map fun p => s!"l{p.2}"
  let ssum := if strict.isEmpty then "0" else " + ".intercalate strict
  let cond := s!"(({csum}) >= 1) || ((({csum}) >= 0) && (({ssum}) >= 1))"
  let r ← ask t (findCmd (nonneg ++ zeros ++ [cond]) ls)
  if r == "none" then return none
  return parseVals r

/-- Wolfram's verdict, checked by `certifyVerdict`. -/
def wolframSolve (t : Mathematica.Transport) (cs : List LinCon) : IO Verdict := do
  match ← wolframSat t cs with
  | some w => return certifyVerdict cs (.sat w)
  | none => match ← wolframFarkas t cs with
    | some m => return certifyVerdict cs (.unsat m)
    | none => return .unknown

/-- The least value of `z`, from Wolfram, with a witness attaining it and
multipliers refuting anything smaller; both checked in Lean. -/
def wolframMin (t : Mathematica.Transport) (cs : List LinCon) (z : String) :
    IO (Option (ℚ × Bool × Bool)) := do
  let vs := varsOf cs
  let syms := (List.range vs.length).map fun i => s!"v{i}"
  let cmd := s!"Module[\{r = Minimize[\{{sym vs z}, And @@ {wlList (cs.map (wlCon vs))}}, {wlList syms}]}, If[Head[r] =!= List || !NumericQ[r[[1]]], \"none\", StringRiffle[ToString[#, InputForm] & /@ Prepend[{wlList syms} /. r[[2]], r[[1]]], \",\"]]]"
  let r ← ask t cmd
  match parseVals r with
  | some (zstar :: vals) =>
      let w := vs.zip vals
      let wok := checkWitness cs (asg w) && decide (asg w z = zstar)
      match ← wolframFarkas t (cs ++ [(⟨⟨[(z, 1)], -zstar⟩, .lt⟩ : LinCon)]) with
      | some m =>
          let μ := m.getLastD 0
          let ms := (m.dropLast).map (· / μ)
          return some (zstar, wok, μ != 0 && lowerBoundCert cs z zstar ms && ms.length == cs.length)
      | none => return some (zstar, wok, false)
  | _ => return none

/-- Print a verdict. -/
def showV : Verdict → String
  | .sat _ => "sat (witness checked)"
  | .unsat _ => "unsat (Farkas certificate checked)"
  | .unknown => "unknown"

/-- Run an action and measure it. -/
def timed {α : Type} (act : IO α) : IO (α × Nat) := do
  let t0 ← IO.monoMsNow
  let a ← act
  let t1 ← IO.monoMsNow
  return (a, t1 - t0)

/-- Both solvers on one system; the in-Lean one is forced before its clock stops. -/
def compare (t : Mathematica.Transport) (name : String) (cs : List LinCon) (fmToo : Bool := true) :
    IO Unit := do
  let (vw, tw) ← timed (wolframSolve t cs)
  let fmPart ← if fmToo then do
      let (vf, tf) ← timed (do let v := solve cs; IO.println s!"  [{showV v}]"; pure v)
      pure s!"; Fourier–Motzkin: {showV vf}, {tf} ms"
    else pure ""
  IO.println s!"{name}: {cs.length} constraints, {(varsOf cs).length} variables; Wolfram: {showV vw}, {tw} ms{fmPart}"

/-- Report Wolfram's certified minimum. -/
def minimise (t : Mathematica.Transport) (name : String) (cs : List LinCon) (z : String)
    (expected : ℚ) : IO Unit := do
  let (r, tw) ← timed (wolframMin t cs z)
  match r with
  | some (zstar, wok, lok) =>
      IO.println s!"{name}: least {z} = {zstar} (expected {expected}); witness checked {wok}, lower bound checked {lok}; {tw} ms"
  | none => IO.println s!"{name}: Wolfram gave no minimum"

/-- The answer constraint of the engine's first proof, as linear constraints. -/
def consOfProof (Θ : Program) (G : Form) (eager : Bool) (fuel : Nat) : List LinCon :=
  match run Θ isLinC eager fuel G with
  | some (p, _) => (consOf p.total).getD []
  | none => []

/-- A system on which elimination blows up: every `±xᵢ ± xⱼ ≤ 1`, `i < j < n`
(satisfiable, at `x = 0`); with `Σ xᵢ ≥ n` added it is infeasible, since the
pairwise bounds force `Σ xᵢ ≤ n/2`. -/
def crossSystem (n : Nat) (infeasible : Bool) : List LinCon :=
  let x (i : Nat) := s!"x{i}"
  let pairs := (List.range n).flatMap fun i => ((List.range n).filter (i < ·)).map (i, ·)
  let signs : List (ℚ × ℚ) := [(1, 1), (1, -1), (-1, 1), (-1, -1)]
  let base := pairs.flatMap fun (i, j) => signs.map fun (a, b) =>
    (⟨⟨[(x i, a), (x j, b)], -1⟩, .le⟩ : LinCon)
  if infeasible then
    base ++ [⟨⟨(List.range n).map (fun i => (x i, (-1 : ℚ))), (n : ℚ)⟩, .le⟩]
  else base

/-- The comparison runs. -/
def main : IO Unit := do
  let t ← Mathematica.defaultTransport
  -- a designed cell where Fourier–Motzkin's elimination blows up
  compare t "±xᵢ ± xⱼ ≤ 1, n = 5" (crossSystem 5 false)
  compare t "±xᵢ ± xⱼ ≤ 1 and Σ xᵢ ≥ 5, n = 5" (crossSystem 5 true)
  -- Example 6.1
  compare t "Example 6.1" cs61
  minimise t "Example 6.1" cs61 "z" 44
  -- the mortgage program, query 1
  let cm := consOfProof mortgage
    (query (at_ "mortgage" [v "P", num "120", num "1/100", num "172165/100", num "0"])) true 2000
  compare t "mortgage, query 1" cm
  -- scheduling: the deadline-12 answer with the deadline lowered to 10 is infeasible
  let cs12 := consOfProof CLPExamples.sched (query (conj [at_ "schedule" [v "Sa", v "Sb", v "Sc", v "Sd", v "E"],
    leq (v "E") (num "12")])) true 100
  compare t "schedule (c before b) with E ≤ 10" (cs12 ++ [⟨⟨[("E", 1)], -10⟩, .le⟩])
  -- adders: one output, then every output
  for n in [8, 16, 32] do
    let cs := consOfProof (adder n) (query (at_ s!"c{n}" [v "z"])) false (20 * n + 20)
    compare t s!"adder n={n}, carry-out" cs
    minimise t s!"adder n={n}, carry-out" cs "z" (4 * n + 3)
  for n in [4, 8] do
    let outs := (List.range n).map (fun i => (s!"s{i}", s!"zs{i}")) ++ [(s!"c{n}", "zc")]
    let cs := consOfProof (adder n) (query (conj (outs.map fun o => at_ o.1 [v o.2]))) false (40 * n + 40)
    compare t s!"adder n={n}, all outputs" cs (fmToo := false)
    minimise t s!"adder n={n}, all outputs" cs "zc" (4 * n + 3)

#eval main

end LaxLogic.QLL.CLPWolfram
