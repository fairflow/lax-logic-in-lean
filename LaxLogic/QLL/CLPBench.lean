/-
# `LaxLogic.QLL.CLPBench` — the engine on programs of realistic size

Not part of the library build (nothing imports it).  Run with

    lake env lean LaxLogic/QLL/CLPBench.lean

Every run prints what was checked.  "checked" is `checkC` (sound by
`checkC_sound`), so `Θ ⊢ total(p) ⊃ G` holds for the tree `p` returned
(`mkAnswer_sound`); the timing figures are certified from both sides by a
witness (`checkWitness_sound`) and a Farkas refutation of anything smaller
(`lowerBoundCert_sound`); mortgage values by `entailsEq_sound`.  These checks
run as compiled or interpreted Booleans, so the trust base includes the Lean
compiler and interpreter; `CLPExamples.lean` has the kernel-checked cases.
-/
import LaxLogic.QLL.CLPExamples

open LaxLogic.QLL LaxLogic.QLL.Engine LaxLogic.QLL.LinQ LaxLogic.QLL.CLPExamples

/-- `q` to `k` decimal places (truncated). -/
def dec (q : ℚ) (k : Nat) : String :=
  let m : Int := (q * ((10 : ℚ) ^ k)).floor
  let s := (toString m.natAbs).toList
  let s := List.replicate (k + 1 - s.length) '0' ++ s
  (if m < 0 then "-" else "") ++ String.ofList (s.take (s.length - k)) ++ "." ++
    String.ofList (s.drop (s.length - k))

def benchAdder (n : Nat) : IO Unit := do
  let Θ := adder n
  let G := query (at_ s!"c{n}" [v "z"])
  let t0 ← IO.monoMsNow
  let some (p, _) := run Θ isLinC false (20 * n + 20) G
    | IO.println s!"adder n={n}: no answer"
  let ok := checkC isLinC Θ G p
  let t1 ← IO.monoMsNow
  let cs := (consOf p.total).getD []
  let st := settle cs "z"
  let up := upClosed cs "z"
  let t2 ← IO.monoMsNow
  IO.println s!"adder n={n}: {Θ.length} clauses; proof tree {psize p} nodes, {cs.length} constraints; checked {ok}; c{n} settles at {st.zstar} (4n+3 = {4*n+3}); witness {st.witnessOK}, lower bound {st.lowerOK}, upward closed {up}; search+check {t1-t0} ms, settle+certify {t2-t1} ms"

/-- All outputs at once: `s₀(z₀) ∧ … ∧ s_{n-1}(z_{n-1}) ∧ cₙ(zₙ)`. -/
def benchAdderAll (n : Nat) : IO Unit := do
  let Θ := adder n
  let outs := (List.range n).map (fun i => (s!"s{i}", s!"zs{i}")) ++ [(s!"c{n}", "zc")]
  let G := query (conj (outs.map fun o => at_ o.1 [v o.2]))
  let t0 ← IO.monoMsNow
  let some (p, _) := run Θ isLinC false (40 * n + 40) G
    | IO.println s!"adder-all n={n}: no answer"
  let ok := checkC isLinC Θ G p
  let t1 ← IO.monoMsNow
  let cs := (consOf p.total).getD []
  let sts := outs.map fun o => (o.1, settle cs o.2)
  let allOK := sts.all fun s => s.2.witnessOK && s.2.lowerOK
  let worst := sts.foldl (fun m s => max m s.2.zstar) 0
  let t2 ← IO.monoMsNow
  IO.println s!"adder-all n={n}: proof tree {psize p} nodes, {cs.length} constraints; checked {ok}; {outs.length} outputs settled, all certified {allOK}; latest output {worst}; search+check {t1-t0} ms, settle+certify {t2-t1} ms"

def benchMortgage : IO Unit := do
  let G1 := query (at_ "mortgage" [v "P", num "120", num "1/100", num "172165/100", num "0"])
  let t0 ← IO.monoMsNow
  match answer mortgage isLinC true 2000 G1 with
  | none => IO.println "mortgage query 1: no answer"
  | some a =>
    let cs := (consOf a.constraint).getD []
    match a.verdict with
    | .sat w =>
      let pv := asg w "P"
      let det := entailsEq cs ⟨[("P", 1)], -pv⟩
      let t1 ← IO.monoMsNow
      IO.println s!"mortgage query 1 (D = 120, I = 1/100, MP = 1721.65, B = 0): checked {a.typed}; {cs.length} constraints; P = {dec pv 6}, determined (certified) {det}; {t1-t0} ms"
    | _ => IO.println "mortgage query 1: no certified verdict"
  for (i, name) in [((1 : ℚ) / 100, "1/100"), ((1 : ℚ) / 10, "1/10")] do
    let G := query (at_ "mortgage" [v "P", num "5", num name, v "MP", num "0"])
    match answer mortgage isLinC true 200 G with
    | none => IO.println s!"mortgage query 2 (I = {name}): no answer"
    | some a =>
      let cs := (consOf a.constraint).getD []
      let r := 1 + i
      let k := r ^ 5 / ((List.range 5).map (fun j => r ^ j)).sum
      let det := entailsEq cs ⟨[("MP", 1), ("P", -k)], 0⟩
      IO.println s!"mortgage query 2 (D = 5, I = {name}, B = 0): checked {a.typed}; MP = {k} · P = {dec k 9}… · P, certified {det}"

/-- Precedence scheduling with one shared machine (a disjunctive constraint). -/
def sched : Program :=
  [ cl "schedule" ["Sa", "Sb", "Sc", "Sd", "E"] (conj [
      geq (v "Sa") (num "0"),
      geq (v "Sb") (plus (v "Sa") (num "3")),
      geq (v "Sc") (plus (v "Sa") (num "3")),
      geq (v "Sc") (num "4"),
      geq (v "Sd") (plus (v "Sb") (num "2")),
      geq (v "Sd") (plus (v "Sc") (num "4")),
      geq (v "E") (plus (v "Sd") (num "2")),
      at_ "disjoint" [v "Sc", num "4", v "Sb", num "2"]]),
    cl "disjoint" ["X", "DX", "Y", "DY"] (geq (v "Y") (plus (v "X") (v "DX"))),
    cl "disjoint" ["X", "DX", "Y", "DY"] (geq (v "X") (plus (v "Y") (v "DY"))) ]

def benchSched : IO Unit := do
  for d in [12, 11, 10] do
    let G := query (conj [at_ "schedule" [v "Sa", v "Sb", v "Sc", v "Sd", v "E"],
      leq (v "E") (num (toString d))])
    match answer sched isLinC true 100 G with
    | none => IO.println s!"schedule, deadline {d}: no answer (every branch refuted by the solver)"
    | some a =>
      let cs := (consOf a.constraint).getD []
      let st := settle cs "E"
      let branch := match a.proof with
        | .andI (.clause _ _ p) _ => match p with
          | .andI _ (.andI _ (.andI _ (.andI _ (.andI _ (.andI _ (.andI _ (.clause w _ _))))))) =>
              if w == 1 then "c before b" else "b before c"
          | _ => "?"
        | _ => "?"
      IO.println s!"schedule, deadline {d}: checked {a.typed}; order {branch}; earliest end {st.zstar}, certified {st.witnessOK && st.lowerOK}"

#eval benchSched
#eval benchMortgage
#eval benchAdder 8
#eval benchAdder 16
#eval benchAdder 32
#eval benchAdder 64
#eval benchAdderAll 8
#eval benchAdderAll 16
#eval benchAdderAll 32
