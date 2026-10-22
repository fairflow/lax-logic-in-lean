import tools.SubTab.Tableau
import LaxLogic.PLL.SubTab.Translate
import LaxLogic.RN.Rho
import F0.Weight
import RNDB.DB
import RNDB.Frontier79
import RNDB.Examples
import Rewrite.Canon
import Lean.Data.Json

/-!
# `explorergen`: the facts and the data of the RN(◯,∅) explorer

2026-10-22.  UNTRUSTED generator.  For the 22 ρ-classes (`RhoOrder.rhoF`,
historical labels in order of discovery) it decides, with the subframe
tableau (`SubTab.solve`), every cell the explorer shows, and writes

* Lean source, one theorem per fact, under `F0/` (`F0/Order/PartK.lean`,
  `F0/Ops/PartK.lean`, `F0/Members/PartK.lean` and the three umbrella
  modules), each fact `PLLND.SubTab.yes'.verdict` (a closed tableau,
  translated into a derivation; `LaxLogic/PLL/SubTab/Translate.lean`) or
  `PLLND.SubTab.no.verdict` (a finite subframe countermodel), checked by
  the kernel (`decide +kernel`) and pinned at `[propext, Quot.sound]`;
* the explorer data, `docs/explorer/f0-explorer-data.json`.

The facts the kernel checks are the only evidence: a cell is written to
the JSON as `"status": "proved"` only for a part named in `--checked`
(the parts whose modules the build accepted); otherwise `"pending"`.

Every certificate is also run through the kernel's own Boolean checker
(`PLLND.SubTab.check`, `SubCM.refutes`) before it is written; a rejection
is a tool defect and stops the run.

Weights (`depth`, `size`, `scope`) and the minimal member come from
`F0/Weight.lean` (`F0.boxDepth`, `F0.size`, `F0.boxScope`, `F0.pickRep`).

Known members of a class: every closed formula of the RNDB record (both
sides of every entry and frontier claim, raw and through
`Rewrite.canon`), placed in its class by the tableau and CERTIFIED by two
facts of `F0/Members` (`⊢ X ↠ ρk`, `⊢ ρk ↠ X`).  The RNDB evidence and
`Rewrite.canon` only propose candidates.

Usage (run the built binary under a deadline):

    explorergen lean <repo-root>
    explorergen json <repo-root> <date> <commit> <checked: order,ops,members>
-/

open Lean (Json toJson)

namespace ExplorerGen

abbrev F := PLLFormula
abbrev TCert := PLLND.SubTab.TCert
abbrev SubCM := PLLND.SubTab.SubCM

/-! ## Printing in the library notation (as `tools/RNDBExport.lean`) -/

def prec : F → Nat
  | .ifThen .falsePLL .falsePLL => 3
  | .ifThen _ .falsePLL => 3
  | .ifThen _ _ => 0
  | .or _ _ => 1
  | .and _ _ => 2
  | _ => 3

def par (b : Bool) (s : String) : String := if b then "(" ++ s ++ ")" else s

def pp : F → String
  | .prop s => s
  | .falsePLL => "⊥"
  | .ifThen .falsePLL .falsePLL => "⊤"
  | .ifThen a .falsePLL => "¬" ++ par (prec a < 3) (pp a)
  | .ifThen a b => par (prec a == 0) (pp a) ++ " ↠ " ++ pp b
  | .or a b => par (prec a ≤ 1) (pp a) ++ " ∨ " ++ par (prec b ≤ 1) (pp b)
  | .and a b => par (prec a ≤ 2) (pp a) ++ " ∧ " ++ par (prec b ≤ 2) (pp b)
  | .somehow a => "◯" ++ par (prec a < 3) (pp a)

def isClosed : F → Bool
  | .prop _ => false
  | .falsePLL => true
  | .and a b | .or a b | .ifThen a b => isClosed a && isClosed b
  | .somehow a => isClosed a

/-! ## Lean source, with the shared names of `LaxLogic/RN/Reps.lean` -/

def rho (i : Nat) : F := RhoOrder.rhoF i
def nR : Nat := RhoOrder.n
def rhoSrc (i : Nat) : String := s!"(RhoOrder.rhoF {i})"

/-- Named formulas (the generated files `open RNReps`). -/
def named : List (String × F) :=
  [("q0", RNReps.q0), ("q1", RNReps.q1), ("q2", RNReps.q2), ("q3", RNReps.q3),
   ("q4", RNReps.q4), ("q5", RNReps.q5), ("q6", RNReps.q6), ("q7", RNReps.q7),
   ("q8", RNReps.q8), ("q9", RNReps.q9), ("q10", RNReps.q10), ("q11", RNReps.q11),
   ("q12", RNReps.q12), ("q13", RNReps.q13), ("q14", RNReps.q14), ("q15", RNReps.q15)] ++
  ((List.range 22).filterMap fun i =>
    if [RNReps.q0, RNReps.q1, RNReps.q2, RNReps.q3, RNReps.q4, RNReps.q5, RNReps.q6, RNReps.q7,
        RNReps.q8, RNReps.q9, RNReps.q10, RNReps.q11, RNReps.q12, RNReps.q13, RNReps.q14,
        RNReps.q15].contains (rho i) then none
    else some (rhoSrc i, rho i))

def src (φ : F) : String :=
  match named.find? (·.2 == φ) with
  | some (n, _) => n
  | none =>
    match φ with
    | .prop a => s!"(PLLFormula.prop \"{a}\")"
    | .falsePLL => "PLLFormula.falsePLL"
    | .and A B => s!"(PLLFormula.and {src A} {src B})"
    | .or A B => s!"(PLLFormula.or {src A} {src B})"
    | .ifThen A B => s!"(PLLFormula.ifThen {src A} {src B})"
    | .somehow A => s!"(PLLFormula.somehow {src A})"

def tcertSrc : TCert → String
  | .bot => ".bot"
  | .ax A => s!"(.ax {src A})"
  | .andL A B c => s!"(.andL {src A} {src B} {tcertSrc c})"
  | .orL A B c₁ c₂ => s!"(.orL {src A} {src B} {tcertSrc c₁} {tcertSrc c₂})"
  | .impL A B c₁ c₂ => s!"(.impL {src A} {src B} {tcertSrc c₁} {tcertSrc c₂})"
  | .boxL A c => s!"(.boxL {src A} {tcertSrc c})"
  | .andR A B c₁ c₂ => s!"(.andR {src A} {src B} {tcertSrc c₁} {tcertSrc c₂})"
  | .orR A B c => s!"(.orR {src A} {src B} {tcertSrc c})"
  | .impLoc A B c => s!"(.impLoc {src A} {src B} {tcertSrc c})"
  | .boxLoc A c => s!"(.boxLoc {src A} {tcertSrc c})"
  | .impR A B c => s!"(.impR {src A} {src B} {tcertSrc c})"
  | .boxR A c => s!"(.boxR {src A} {tcertSrc c})"

def subcmSrc (m : SubCM) : String :=
  s!"\{ n := {m.n}, root := {m.root}, le := {m.le}, S := {m.S}, val := {repr m.val} }"

/-- The number of rule applications in a closed tableau. -/
def tsize : TCert → Nat
  | .bot | .ax _ => 1
  | .andL _ _ c | .boxL _ c | .orR _ _ c | .impLoc _ _ c | .boxLoc _ c | .impR _ _ c
  | .boxR _ c => tsize c + 1
  | .orL _ _ c₁ c₂ | .impL _ _ c₁ c₂ | .andR _ _ c₁ c₂ => tsize c₁ + tsize c₂ + 1

/-! ## Deciding a cell -/

inductive Cell where
  | le (c : TCert)
  | nle (m : SubCM)

/-- Cheap: is `⊢ φ` provable (the search's verdict only). -/
def provable (φ : F) : Bool :=
  match _root_.SubTab.solve φ with
  | .ok _ => true
  | .error _ => false

/-- The verdict on `⊢ φ` with its certificate: a closed tableau, or a
countermodel minimised (greedy deletion, then the smallest-first
enumeration below that size, up to 6 worlds).  Both are run through the
kernel's Boolean checkers here. -/
def decideF (φ : F) : Except String Cell :=
  match _root_.SubTab.solve φ with
  | .ok c =>
    if PLLND.SubTab.check ⟨false, [], [φ]⟩ c then .ok (.le c)
    else .error s!"tool defect: tableau rejected for {pp φ}"
  | .error m =>
    let m1 := if m.n ≤ 64 then _root_.SubTab.minimiseCM m φ else m
    let m2 :=
      if m1.n ≤ 1 then m1
      else match PllFast.firstHit φ (min 6 (m1.n - 1)) with
        | some (_, bm) =>
          let e := PllFast.bmToSubCM bm (PllFast.atomsL φ).eraseDups
          if e.refutes φ then e else m1
        | none => m1
    if m2.refutes φ then .ok (.nle m2)
    else .error s!"tool defect: countermodel rejected for {pp φ}"

def Cell.isLe : Cell → Bool
  | .le _ => true
  | .nle _ => false

def certJson : Cell → Json
  | .le c => Json.mkObj [("kind", Json.str "tableau"), ("nodes", toJson (tsize c))]
  | .nle m => Json.mkObj [("kind", Json.str "countermodel"), ("n", toJson m.n),
      ("root", toJson m.root), ("le", toJson m.le), ("S", toJson m.S), ("val", toJson m.val)]

/-- One theorem: `name` (unqualified), its docstring, the spec as source. -/
def thmSrc (name doc specS : String) : Cell → String
  | .le c =>
    s!"/-- {doc} -/\ntheorem {name} : PLLND.SubTab.Holds {specS} :=\n  PLLND.SubTab.yes'.verdict {specS}\n    {tcertSrc c}\n"
  | .nle m =>
    s!"/-- {doc} (countermodel, {m.n} worlds) -/\ntheorem {name} : PLLND.SubTab.Holds {specS} → False :=\n  PLLND.SubTab.no.verdict {specS}\n    {subcmSrc m}\n"

/-! ## The facts -/

/-- A fact: its theorem name (qualified), docstring, spec source and cell. -/
structure Fact where
  name : String
  doc : String
  spec : String
  cell : Cell

def nm (i : Nat) : String := s!"ρ{i}"

/-! ### The order -/

structure OrderCell where
  i : Nat
  j : Nat
  fact : Fact

def orderCells : Except String (List OrderCell) :=
  ((List.range nR).flatMap fun i => (List.range nR).filterMap fun j =>
      if i == j then none else some (i, j)).mapM fun (i, j) => do
    let c ← decideF ((rho i).ifThen (rho j))
    let rel := match c with | .le _ => "⊢" | .nle _ => "⊬"
    pure ⟨i, j, ⟨s!"F0.Order.c_{i}_{j}", s!"{nm i} {rel} {nm j}",
      s!"({rhoSrc i}.ifThen {rhoSrc j})", c⟩⟩

/-! ### The operation tables -/

inductive Op where
  | and | or | imp | box
  deriving BEq

def Op.name : Op → String
  | .and => "and" | .or => "or" | .imp => "imp" | .box => "box"

def Op.sym : Op → String
  | .and => "∧" | .or => "∨" | .imp => "↠" | .box => "◯"

def Op.apply : Op → Nat → Nat → F
  | .and, i, j => (rho i).and (rho j)
  | .or, i, j => (rho i).or (rho j)
  | .imp, i, j => (rho i).ifThen (rho j)
  | .box, i, _ => (rho i).somehow

def Op.srcOf : Op → Nat → Nat → String
  | .and, i, j => s!"({rhoSrc i}.and {rhoSrc j})"
  | .or, i, j => s!"({rhoSrc i}.or {rhoSrc j})"
  | .imp, i, j => s!"({rhoSrc i}.ifThen {rhoSrc j})"
  | .box, i, _ => s!"({rhoSrc i}.somehow)"

def Op.docOf : Op → Nat → Nat → String
  | .box, i, _ => s!"◯{nm i}"
  | o, i, j => s!"{nm i} {o.sym} {nm j}"

def Op.tag : Op → Nat → Nat → String
  | .box, i, _ => s!"box_{i}"
  | o, i, j => s!"{o.name}_{i}_{j}"

inductive OpResult where
  | hit (k : Nat) (fwd bwd : Fact)
  | notR (seps : List (Nat × String × Fact))   -- k, direction, the refutation

structure OpCell where
  op : Op
  i : Nat
  j : Option Nat
  res : OpResult

/-- The search order for the class of `op(ρi, ρj)`: the answer the order
predicts first, then the rest by label. -/
def candidates (le : Nat → Nat → Bool) : Op → Nat → Nat → List Nat
  | .and, i, j => let g := if le i j then [i] else if le j i then [j] else []
                  g ++ (List.range nR).filter (!g.contains ·)
  | .or, i, j => let g := if le i j then [j] else if le j i then [i] else []
                 g ++ (List.range nR).filter (!g.contains ·)
  | .imp, i, j => let g := if le i j then [1] else []
                  g ++ (List.range nR).filter (!g.contains ·)
  | .box, i, _ => let g := [i]
                  g ++ (List.range nR).filter (!g.contains ·)

def opCell (le : Nat → Nat → Bool) (o : Op) (i j : Nat) : Except String OpCell := do
  let φ := o.apply i j
  let φs := o.srcOf i j
  let tag := o.tag i j
  let doc := o.docOf i j
  let jo := if o == .box then none else some j
  match (candidates le o i j).find? (fun k => provable (φ.ifThen (rho k)) && provable ((rho k).ifThen φ)) with
  | some k =>
    let cf ← decideF (φ.ifThen (rho k))
    let cb ← decideF ((rho k).ifThen φ)
    pure ⟨o, i, jo, .hit k
      ⟨s!"F0.Ops.{tag}_fwd", s!"{doc} ⊢ {nm k}", s!"({φs}.ifThen {rhoSrc k})", cf⟩
      ⟨s!"F0.Ops.{tag}_bwd", s!"{nm k} ⊢ {doc}", s!"({rhoSrc k}.ifThen {φs})", cb⟩⟩
  | none =>
    let seps ← (List.range nR).mapM fun k => do
      if provable (φ.ifThen (rho k)) then
        let c ← decideF ((rho k).ifThen φ)
        pure (k, "bwd", (⟨s!"F0.Ops.{tag}_sep_{k}", s!"{nm k} ⊬ {doc}",
          s!"({rhoSrc k}.ifThen {φs})", c⟩ : Fact))
      else
        let c ← decideF (φ.ifThen (rho k))
        pure (k, "fwd", (⟨s!"F0.Ops.{tag}_sep_{k}", s!"{doc} ⊬ {nm k}",
          s!"({φs}.ifThen {rhoSrc k})", c⟩ : Fact))
    pure ⟨o, i, jo, .notR seps⟩

def opCells (le : Nat → Nat → Bool) : Except String (List OpCell) := do
  let pairs := (List.range nR).flatMap fun i => (List.range nR).map fun j => (i, j)
  let mut out := #[]
  for o in [Op.and, Op.or, Op.imp] do
    for (i, j) in pairs do
      out := out.push (← opCell le o i j)
  for i in List.range nR do
    out := out.push (← opCell le .box i 0)
  return out.toList

def OpCell.isHit (c : OpCell) : Bool :=
  match c.res with
  | .hit .. => true
  | .notR _ => false

def OpCell.facts (c : OpCell) : List Fact :=
  match c.res with
  | .hit _ f b => [f, b]
  | .notR seps => seps.map (·.2.2)

/-! ### Known members, from the RNDB record -/

def rndbFormulas : List F :=
  let es := RNDB.allEntries ++ RNDB.exampleEntries
  let cs : List RNDB.Claim := es.map (·.claim) ++ (show List RNDB.Claim from RNDB.frontierOrder) ++ (show List RNDB.Claim from RNDB.frontier79) ++ (show List RNDB.Claim from RNDB.exampleFrontier)
  cs.flatMap fun c => [c.lhs, c.rhs, Rewrite.canon c.lhs, Rewrite.canon c.rhs]

/-- The closed RNDB formulas other than the 22 ρ, deduplicated, sorted by
their printed form. -/
def candidatesRNDB : List F :=
  let fs := rndbFormulas.filter fun φ => isClosed φ && !((List.range nR).any fun i => rho i == φ)
  let ss := (fs.map fun φ => (pp φ, φ)).mergeSort (fun a b => decide (a.1 ≤ b.1))
  (ss.foldl (fun (acc : Array (String × F)) p =>
    if acc.size > 0 && acc[acc.size - 1]!.1 == p.1 then acc else acc.push p) #[]).toList.map (·.2)

structure Member where
  k : Nat
  t : Nat            -- index within the class (sorted by printed form)
  φ : F
  fwd : Fact
  bwd : Fact

def members : Except String (List Member × Nat) := do
  let placed := candidatesRNDB.filterMap fun φ =>
    ((List.range nR).find? fun k => provable (φ.ifThen (rho k)) && provable ((rho k).ifThen φ)).map (·, φ)
  let outside := candidatesRNDB.length - placed.length
  let mut out := #[]
  for k in List.range nR do
    let ms := placed.filter (·.1 == k)
    let mut t := 0
    for (_, φ) in ms do
      let cf ← decideF (φ.ifThen (rho k))
      let cb ← decideF ((rho k).ifThen φ)
      out := out.push ⟨k, t, φ,
        ⟨s!"F0.Members.r{k}_m{t}_fwd", s!"{pp φ} ⊢ {nm k}", s!"({src φ}.ifThen {rhoSrc k})", cf⟩,
        ⟨s!"F0.Members.r{k}_m{t}_bwd", s!"{nm k} ⊢ {pp φ}", s!"({rhoSrc k}.ifThen {src φ})", cb⟩⟩
      t := t + 1
  return (out.toList, outside)

/-! ## Writing the Lean files -/

def header (part title : String) : String :=
  s!"import LaxLogic.PLL.SubTab.Translate\nimport LaxLogic.RN.Rho\n\n/-!\n# {title}\n\nGENERATED by `explorergen lean` (tools/F0/ExplorerGen.lean); do not edit.\nOne theorem per fact: `PLLND.SubTab.yes'.verdict` (a closed subframe\ntableau, translated into a derivation) or `PLLND.SubTab.no.verdict` (a\nfinite subframe countermodel), checked by the kernel; each pinned at\n`[propext, Quot.sound]`.  The ρ-indices are historical labels.\n-/\n\nset_option maxRecDepth 100000\n\nopen RNReps\n\nnamespace F0.{part}\n\n"

def short (full : String) : String := (full.splitOn ".").getLast!

def partFile (part title : String) (fs : List Fact) : String :=
  let body := String.intercalate "\n" (fs.map fun f => thmSrc (short f.name) f.doc f.spec f.cell)
  let pins := String.intercalate "\n" (fs.map fun f => s!"#axioms_within {f.name} [propext, Quot.sound]")
  header part title ++ body ++ s!"\nend F0.{part}\n\n" ++ pins ++ "\n"

def chunk {α} (n : Nat) (l : List α) : List (List α) :=
  if n == 0 then [l] else
  (List.range ((l.length + n - 1) / n)).map fun k => (l.drop (n * k)).take n

/-- Write `F0/<part>/PartK.lean` and the umbrella `F0/<part>.lean`;
returns the module names. -/
def writePart (root : System.FilePath) (part title : String) (psize : Nat) (fs : List Fact) :
    IO (List String) := do
  let dir := root / "F0" / part
  IO.FS.createDirAll dir
  let cs := chunk psize fs
  let mut mods := #[]
  let mut k := 0
  for c in cs do
    IO.FS.writeFile (dir / s!"Part{k}.lean")
      (partFile part s!"{title}, part {k} ({c.length} facts)" c)
    mods := mods.push s!"F0.{part}.Part{k}"
    k := k + 1
  let umb := String.intercalate "\n" (mods.toList.map (s!"import {·}")) ++
    s!"\n\n/-! # {title}: {fs.length} facts in {cs.length} parts. GENERATED by `explorergen lean`. -/\n"
  IO.FS.writeFile (root / "F0" / s!"{part}.lean") umb
  return mods.toList

/-! ## JSON -/

def js (s : String) : Json := Json.str s

def lines (xs : List Json) : String :=
  if xs.isEmpty then "[]" else
  "[\n" ++ String.intercalate ",\n" (xs.map fun x => "    " ++ x.compress) ++ "\n  ]"

def weightOf (φ : F) : List (String × Json) :=
  [("depth", toJson (F0.boxDepth φ)), ("size", toJson (F0.size φ)), ("scope", toJson (F0.boxScope φ))]

def run (args : List String) : IO UInt32 := do
  match args with
  | mode :: root :: rest =>
    let root : System.FilePath := root
    let t0 ← IO.monoMsNow
    let oc ← IO.ofExcept orderCells
    let leTab : Array (Array Bool) := (List.range nR).toArray.map fun i =>
      (List.range nR).toArray.map fun j =>
        i == j || oc.any fun c => c.i == i && c.j == j && c.fact.cell.isLe
    let le (i j : Nat) : Bool := (leTab[i]!)[j]!
    let t1 ← IO.monoMsNow
    IO.eprintln s!"order: {oc.length} cells in {t1 - t0} ms"
    let ops ← IO.ofExcept (opCells le)
    let t2 ← IO.monoMsNow
    IO.eprintln s!"ops: {ops.length} cells, {(ops.flatMap OpCell.facts).length} facts in {t2 - t1} ms"
    let (ms, outside) ← IO.ofExcept members
    let t3 ← IO.monoMsNow
    IO.eprintln s!"members: {ms.length} certified members ({outside} RNDB candidates outside R) in {t3 - t2} ms"
    match mode with
    | "lean" =>
      let partSize := ((rest.head?).bind String.toNat?).getD 120
      let m1 ← writePart root "Order" "The order of the 22 ρ-classes" partSize (oc.map (·.fact))
      let m2 ← writePart root "Ops" "The operation tables of the 22 ρ-classes" partSize
        (ops.flatMap OpCell.facts)
      let m3 ← writePart root "Members" "Known members of the 22 ρ-classes" partSize
        (ms.flatMap fun m => [m.fwd, m.bwd])
      IO.println s!"modules: {m1 ++ m2 ++ m3}"
      return 0
    | "json" =>
      match rest with
      | date :: commit :: checked :: _ =>
        let ck := checked.splitOn ","
        let okO := ck.contains "order"
        let okP := ck.contains "ops"
        let okM := ck.contains "members"
        -- classes
        let classes := (List.range nR).map fun k =>
          let mk := ms.filter (·.k == k)
          let mins := mk.map (·.φ)
          let minimal := F0.pickRep (rho k) mins
          let minFacts := (mk.find? (·.φ == minimal)).map (fun m => [m.fwd.name, m.bwd.name])
          let vf := (rho k) :: mins |>.filter F0.orFree
          let vfw := match vf with
            | [] => none
            | v :: vs => some (F0.pickRep v vs)
          let vfFacts := (vfw.bind fun v => mk.find? (·.φ == v)).map (fun m => [m.fwd.name, m.bwd.name])
          Json.mkObj <|
            [("id", js (nm k)), ("index", toJson k), ("number", Json.null),
             ("formula", js (pp (rho k)))] ++ weightOf (rho k) ++
            [("members_status", js (if okM then "proved" else "pending")),
             ("minimal", if okM then js (pp minimal) else js (pp (rho k))),
             ("minimal_weight", toJson (let mw := if okM then minimal else rho k; [F0.boxDepth mw, F0.size mw, F0.boxScope mw])),
             ("minimal_theorems", toJson (if okM then minFacts.getD [] else [])),
             ("members_known", toJson (if okM then mk.length + 1 else 1)),
             ("members", toJson (if okM then (mk.map fun m => pp m.φ) else [])),
             ("vfree_known", toJson (if okM then vfw.isSome else F0.orFree (rho k))),
             ("vfree_witness", (match vfw with
                | some v => if okM || v == rho k then js (pp v) else Json.null
                | none => Json.null)),
             ("vfree_theorems", toJson (if okM then vfFacts.getD [] else []))]
        -- order
        let order := oc.map fun c =>
          let rel := if c.fact.cell.isLe then "le" else "nle"
          let tail : List (String × Json) :=
            if okO then [("status", js "proved"), ("rel", js rel), ("cert", certJson c.fact.cell)]
            else [("status", js "pending"), ("rel", Json.null), ("cert", Json.null)]
          Json.mkObj ([("i", toJson c.i), ("j", toJson c.j), ("theorem", js c.fact.name)] ++ tail)
        -- covers (only from a fully proved order)
        let distinct := (List.range nR).all fun i => (List.range nR).all fun j =>
          i == j || !(le i j && le j i)
        let covers : List Json :=
          if !okO then [] else
          ((List.range nR).flatMap fun i => (List.range nR).filterMap fun j =>
            if i != j && le i j &&
              !((List.range nR).any fun k => k != i && k != j && le i k && le k j)
            then some (toJson [i, j]) else none)
        -- ops
        let opsJ := ops.map fun c =>
          let base : List (String × Json) :=
            [("op", js c.op.name), ("i", toJson c.i),
             ("j", match c.j with | some j => toJson j | none => Json.null),
             ("formula", js (pp (c.op.apply c.i (c.j.getD 0))))]
          let tail : List (String × Json) :=
            if !okP then [("status", js "pending"), ("result", js "unknown"),
              ("theorems", toJson ([] : List String))]
            else match c.res with
              | .hit k f b => [("status", js "proved"), ("result", js (nm k)),
                  ("theorems", toJson [f.name, b.name])]
              | .notR seps => [("status", js "proved"), ("result", js "notR"),
                  ("theorems", toJson (seps.map (·.2.2.name))),
                  ("separations", Json.arr (seps.map fun (k, d, f) =>
                    Json.mkObj [("k", toJson k), ("dir", js d), ("theorem", js f.name),
                      ("worlds", (match f.cell with | .nle m => toJson m.n | .le _ => Json.null))]).toArray)]
          Json.mkObj (base ++ tail)
        let nNotR := if okP then (ops.filter (!·.isHit)).length else 0
        let nUnknown := if okP then 0 else ops.length
        let perOp := [Op.and, Op.or, Op.imp, Op.box].map fun o =>
          let os := ops.filter (·.op == o)
          (o.name, Json.mkObj [("cells", toJson os.length),
            ("inR", toJson (if okP then (os.filter (·.isHit)).length else 0)),
            ("notR", toJson (if okP then (os.filter (!·.isHit)).length else 0)),
            ("unknown", toJson (if okP then 0 else os.length))])
        let boundary := Json.mkObj [("notR", toJson nNotR), ("unknown", toJson nUnknown),
          ("per_op", Json.mkObj perOp),
          ("note", js (if okP then "every op cell decided and kernel-checked; notR = op(ρi,ρj) separated from all 22 ρ-classes"
                       else "op tables not yet kernel-checked"))]
        let metaJ := Json.mkObj [("pins", js "[propext, Quot.sound]"),
          ("yes", js "PLLND.SubTab.yes' (LaxLogic/PLL/SubTab/Translate.lean)"),
          ("no", js "PLLND.SubTab.no (LaxLogic/PLL/SubTab/Sound.lean)"),
          ("checked", toJson ck), ("rho_pairwise_distinct", toJson (okO && distinct)),
          ("rndb_candidates", toJson candidatesRNDB.length),
          ("rndb_candidates_outside_R", toJson outside),
          ("labels", js "ρ0…ρ21 are historical labels in order of discovery; number is reserved for a systematic numbering")]
        let out :=
          "{\n  \"schema\": 1,\n" ++
          s!"  \"generated\": {(js date).compress},\n  \"commit\": {(js commit).compress},\n" ++
          s!"  \"meta\": {metaJ.compress},\n" ++
          s!"  \"classes\": {lines classes},\n" ++
          s!"  \"order\": {lines order},\n" ++
          s!"  \"covers\": {(Json.arr covers.toArray).compress},\n" ++
          s!"  \"ops\": {lines opsJ},\n" ++
          s!"  \"boundary\": {boundary.compress}\n}\n"
        let path := root / "docs" / "explorer" / "f0-explorer-data.json"
        IO.FS.writeFile path out
        IO.println s!"wrote {path}: order {oc.length} ({if okO then "proved" else "pending"}), ops {ops.length} ({if okP then "proved" else "pending"}), members {ms.length} ({if okM then "proved" else "pending"}); distinct = {distinct}; covers {covers.length}"
        return 0
      | _ => IO.eprintln "usage: explorergen json <root> <date> <commit> <checked>"; return 2
    | _ => IO.eprintln "usage: explorergen lean|json <root> ..."; return 2
  | _ => IO.eprintln "usage: explorergen lean|json <root> ..."; return 2

end ExplorerGen

def main (args : List String) : IO UInt32 := ExplorerGen.run args
