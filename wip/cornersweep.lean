/- The V-free corner sweep: hunt cells satisfying the chase-revisit
residual's hypotheses (critical, heZ, hne, ¬EvalRP, no classical cm,
every antecedent refuted-or-(modal∧big), some unrefuted).  Each hit is
classified: RefAt-keepability of the stuck antecedents (with ups = Z ::
refuted antecedents, at ctx [] and ctx Ψ), and oracle-derivability of
the stuck antecedent at Ψ (chase-resolvable vs REAL alarm). -/
import FRJ.Search.OpsW
import FRJ.Bridge
import FRJ.Minimal
import wip.gbu_circ
import LaxLogic.PLLSearch
open FRJ FRJ.Search Form

def pa : Form := .atom "p"
def qa : Form := .atom "q"
def ra : Form := .atom "r"
def ba : Form := .atom "b"
def ca : Form := .atom "c"
def xa : Form := .atom "x"
def ya : Form := .atom "y"
def za : Form := .atom "z"

def nF (A : Form) : Form := .imp A .bot

def corpus : List (String × Form) := [
  ("Gx", .imp (.and (.imp (.circ ra) ba) (nF (nF ra))) (.circ ra)),
  ("Glic", .imp (.and (.imp (.circ pa) ra) pa) (.circ ra)),
  ("Gba", .imp (.circ (.and (.imp (.circ pa) qa) (.circ pa))) (.circ ra)),
  ("Glw", .imp (.circ (.and (.imp (.circ pa) ra) (.circ pa))) (.or (.circ ra) za)),
  ("Gdp", .imp (.circ (.or pa qa)) (.or (.circ pa) (.circ qa))),
  ("Gcc", .circ (.imp (.circ pa) pa)),
  ("Gcr", .imp (.circ pa) pa),
  ("Gn1", .imp (.imp (.circ (.and xa (.circ ya))) ba) (.circ ya)),
  ("Gn2", .imp (.imp (.circ (.or xa (.circ ya))) ba) (.circ ya)),
  ("Gn4", .imp (.and (.imp (.circ za) ba) (.imp (.circ (nF za)) ca)) (.circ za)),
  ("Gt1", .imp (.imp (.circ (.circ pa)) (.circ pa)) (.circ pa)),
  ("Gm", .or (.circ pa) (nF (.circ pa))),
  ("Gp1", .imp (.imp (.imp (.circ pa) qa) (.circ pa)) (.circ pa)),
  ("Gp2", .circ (.imp (.imp (.circ pa) ra) (.circ pa))),
  ("Gn5", .imp (.and (.imp (.circ (.or pa qa)) ba) (nF pa)) (.circ qa))
]

def cfg : Config := { rounds := 16, lamCap := 24, maxRS := 3000, maxIS := 3000 }

def ppF : Form → String
  | .atom a => a
  | .bot => "F"
  | .and a b => s!"({ppF a}&{ppF b})"
  | .or a b => s!"({ppF a}|{ppF b})"
  | .imp a b => s!"({ppF a}>{ppF b})"
  | .circ a => s!"O{ppF a}"

def evalIb {G : Form} (db : DBO (W.wOps G)) (om : List Form) (C : Form) : Bool :=
  db.is.any (fun (i : W.WIS G) =>
    decide (i.rhs = C) && decide (i.stab ⊆ om) && decide (om ⊆ i.stab ++ i.th))

def pledgedB {G : Form} (r : W.WRS G) (C : Form) : Bool :=
  match r.t with
  | .barren => true
  | .chain W => coversB r.ctx W C
  | .blocked => false

def evalRPb {G : Form} (db : DBO (W.wOps G)) (om : List Form) (C : Form) : Bool :=
  db.rs.any (fun (r : W.WRS G) =>
    decide (r.rhs = C) && pledgedB r C && om.all (fun X => cloB r.ctx X))

def hasCM (G : Form) (om : List Form) (Z : Form) : Bool :=
  (gAt G).sublists.any (fun ats =>
    (!classForce ats Z) && om.all (fun X => classForce ats X))

def oracleD (om : List Form) (A : Form) : String :=
  match PLLND.Search.settle {} (om.map toPLL) (toPLL A) with
  | .proved _ => "derivable"
  | .refuted _ _ _ => "underivable"
  | .unknown => "unknown"

def sweep (G : Form) : List String := Id.run do
  let (db, st) := saturateO (W.wOps G) cfg
  let hat := gAt G ++ gImp G
  let bodies := (sfR G).filterMap (fun C => match C with
    | .circ Z => some Z
    | _ => none)
  let mut out : List String := []
  if st.lamCapped || st.dbCapped then
    out := out ++ [s!"  CAPPED: lam={st.lamCapped} db={st.dbCapped}"]
  if hat.length > 10 then
    out := out ++ [s!"  SKIPPED: |hat|={hat.length} > 10"]
    return out
  for om in hat.sublists do
    for Z in bodies do
      if evalIb db om Z && !(evalIb db om (.circ Z)) then
        if !(evalRPb db om Z) && !(hasCM G om Z) then
          let antes := (impPart om).map ante
          let refuted := antes.filter (fun A => evalIb db om A)
          let unref := antes.filter (fun A => !(evalIb db om A))
          let stuckOK := unref.all (fun A =>
            A.hasCirc && !(decide (A.size < (Form.circ Z).size)))
          if stuckOK && !unref.isEmpty then
            -- the corner's decidable closures (2026-09-01, afternoon):
            -- (ii) RefAt over Ψ ITSELF with R₀ = ALL refuted Sf^R-forms
            let r0 := (sfR G).filter (fun A => evalIb db om A)
            let ups := Z :: r0
            let keptClosed := (impPart om).all (fun Y =>
              decide (ante Y ∈ r0) || refAtB true ups om (ante Y))
            -- prime-Z axI-family cover through the engine's keptOf
            let th0 : Fin 1 → List Form :=
              fun _ => rm (gAt G) Z ++ gImp G ++ gCirc G
            let base0 := joinCtxOrVBase (fun _ : Fin 1 => []) th0
            let ctx0 := base0 ++
              keptOf (upsilon (fun _ : Fin 1 => Z)) base0 (thPool th0)
            let axiCov := Z.isPrime && !(decide (Z ∈ om)) &&
              om.all (fun X => cloB ctx0 X)
            let diag := unref.map (fun A =>
              s!"{ppF A}[keepPsi={refAtB true ups om A},{oracleD om A}]")
            let verdict :=
              if keptClosed then "CLOSED(kept-chain)"
              else if axiCov then "CLOSED(axI-keptOf)"
              else "RESIDUAL"
            out := out ++
              [s!"  CORNER Ψ={om.map ppF} goal=O{ppF Z} {verdict} stuck={diag}"]
  return out

def main : IO Unit := do
  for (nm, G) in corpus do
    IO.println s!"== {nm} : {ppF G}"
    for l in sweep G do IO.println l
    (← IO.getStdout).flush
  IO.println "sweep done"

#eval main
