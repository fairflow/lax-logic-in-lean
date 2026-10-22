import LaxLogic.PLL.SubTab.Tableau
import LaxLogic.PLL.SubTab.Translate
import LaxLogic.RN.Rho
import F0.Weight
import RNDB.DB
import RNDB.Frontier79
import RNDB.Examples
import Rewrite.Canon
import F0.Names
import Lean.Data.Json

/-!
# `explorergen`: the facts and the data of the RN(◯,∅) explorer

2026-10-22.  UNTRUSTED generator.  For the 22 ρ-classes (`RhoOrder.rhoF`,
historical labels in order of discovery) it decides, with the subframe
tableau (`SubTab.solve`), every cell the explorer shows, and writes

* Lean source, one theorem per fact, under `F0/` (`F0/Order/PartK.lean`,
  `F0/Ops/PartK.lean`, `F0/Members/PartK.lean`, `F0/Families/PartK.lean` and the umbrella
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

    explorergen lean <repo-root> [part-size]
    explorergen json <repo-root> <date> <facts-commit> <generator-commit> <checked>

where `<checked>` lists the parts the kernel accepted, among
`order,tables,members,families,names`.

Names (2026-10-22, METHOD-F0 §1 E): a class is shown under the preferred
certified membership in the families of `F0/Names.lean` (`F0.nameOf`);
`F0/Families` certifies each membership with two facts, and names the op
results outside R that are family members.  The ρ-labels stay as ids
(`id`, `legacy`).
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

/-- The family members of the search domain (`F0/Names.lean`), as names for
the facts of `F0/Families` only (the other parts print as before). -/
def famNamed : List (String × F) :=
  F0.Fam.domain.filterMap fun (f, n) => match f with
    | .bot | .top => none
    | _ => some (s!"(F0.{f.tag} {n})", f.term n)

def srcWith (ns : List (String × F)) (φ : F) : String :=
  match ns.find? (·.2 == φ) with
  | some (n, _) => n
  | none =>
    match φ with
    | .prop a => s!"(PLLFormula.prop \"{a}\")"
    | .falsePLL => "PLLFormula.falsePLL"
    | .and A B => s!"(PLLFormula.and {srcWith ns A} {srcWith ns B})"
    | .or A B => s!"(PLLFormula.or {srcWith ns A} {srcWith ns B})"
    | .ifThen A B => s!"(PLLFormula.ifThen {srcWith ns A} {srcWith ns B})"
    | .somehow A => s!"(PLLFormula.somehow {srcWith ns A})"

def src (φ : F) : String := srcWith named φ

def tcertSrcWith (ns : List (String × F)) : TCert → String
  | .bot => ".bot"
  | .ax A => s!"(.ax {srcWith ns A})"
  | .andL A B c => s!"(.andL {srcWith ns A} {srcWith ns B} {tcertSrcWith ns c})"
  | .orL A B c₁ c₂ => s!"(.orL {srcWith ns A} {srcWith ns B} {tcertSrcWith ns c₁} {tcertSrcWith ns c₂})"
  | .impL A B c₁ c₂ => s!"(.impL {srcWith ns A} {srcWith ns B} {tcertSrcWith ns c₁} {tcertSrcWith ns c₂})"
  | .boxL A c => s!"(.boxL {srcWith ns A} {tcertSrcWith ns c})"
  | .andR A B c₁ c₂ => s!"(.andR {srcWith ns A} {srcWith ns B} {tcertSrcWith ns c₁} {tcertSrcWith ns c₂})"
  | .orR A B c => s!"(.orR {srcWith ns A} {srcWith ns B} {tcertSrcWith ns c})"
  | .impLoc A B c => s!"(.impLoc {srcWith ns A} {srcWith ns B} {tcertSrcWith ns c})"
  | .boxLoc A c => s!"(.boxLoc {srcWith ns A} {tcertSrcWith ns c})"
  | .impR A B c => s!"(.impR {srcWith ns A} {srcWith ns B} {tcertSrcWith ns c})"
  | .boxR A c => s!"(.boxR {srcWith ns A} {tcertSrcWith ns c})"

def tcertSrc (c : TCert) : String := tcertSrcWith named c

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
  /-- `⊢ A ↠ C` from two proved facts `⊢ A ↠ B`, `⊢ B ↠ C` (`F0.holds_trans`). -/
  | comp (a b : String)

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
  | .comp _ _ => true

def Cell.weight : Cell → Nat
  | .le c => tsize c
  | .nle m => m.n
  | .comp _ _ => 0

def certJson : Cell → Json
  | .le c => Json.mkObj [("kind", Json.str "tableau"), ("nodes", toJson (tsize c))]
  | .nle m => Json.mkObj [("kind", Json.str "countermodel"), ("n", toJson m.n),
      ("root", toJson m.root), ("le", toJson m.le), ("S", toJson m.S), ("val", toJson m.val)]
  | .comp a b => Json.mkObj [("kind", Json.str "composed"), ("of", toJson [a, b])]

/-- One theorem: `name` (unqualified), its docstring, the spec as source. -/
def thmSrc (name doc specS : String) (ns : List (String × F)) : Cell → String
  | .le c =>
    s!"/-- {doc} -/\ntheorem {name} : PLLND.SubTab.Holds {specS} :=\n  PLLND.SubTab.yes'.verdict {specS}\n    {tcertSrcWith ns c}\n"
  | .nle m =>
    s!"/-- {doc} (countermodel, {m.n} worlds) -/\ntheorem {name} : PLLND.SubTab.Holds {specS} → False :=\n  PLLND.SubTab.no.verdict {specS}\n    {subcmSrc m}\n"
  | .comp a b =>
    s!"/-- {doc} (composed) -/\ntheorem {name} : PLLND.SubTab.Holds {specS} :=\n  F0.holds_trans {a} {b}\n"

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
    let rel := if c.isLe then "⊢" else "⊬"
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

/-! ### Family memberships (`F0/Names.lean`) -/

def famTag (f : F0.Fam) : String := f.tag

/-- The displayed name: `⊥`, `⊤`, or the family letter and the index
(`F0.Fam.label`). -/
def famLabel (f : F0.Fam) (n : Nat) : String := f.label n

/-- The member as a Lean term (for the JSON `term` field). -/
def famTerm (f : F0.Fam) (n : Nat) : String :=
  match f with
  | .bot => "PLLFormula.falsePLL"
  | .top => "PLLFormula.truePLL"
  | _ => s!"F0.{famTag f} {n}"

/-- The member as Lean source in a fact. -/
def famSrc (f : F0.Fam) (n : Nat) : String := s!"({famTerm f n})"

/-- One (family, index) of the search domain: its class among the 22 with
the two bridge facts, or `none` (outside R). -/
structure FamCell where
  f : F0.Fam
  n : Nat
  φ : F
  res : Option (Nat × Fact × Fact)

def famCells : Except String (List FamCell) :=
  F0.Fam.domain.mapM fun (f, n) => do
    let φ := f.term n
    match (List.range nR).find? (fun k => provable (φ.ifThen (rho k)) && provable ((rho k).ifThen φ)) with
    | some k =>
      let cf ← decideF (φ.ifThen (rho k))
      let cb ← decideF ((rho k).ifThen φ)
      let tag := s!"{famTag f}_{n}"
      pure ⟨f, n, φ, some (k,
        ⟨s!"F0.Families.{tag}_fwd", s!"{famLabel f n} ⊢ {nm k}", s!"({famSrc f n}.ifThen {rhoSrc k})", cf⟩,
        ⟨s!"F0.Families.{tag}_bwd", s!"{nm k} ⊢ {famLabel f n}", s!"({rhoSrc k}.ifThen {famSrc f n})", cb⟩)⟩
    | none => pure ⟨f, n, φ, none⟩

def FamCell.facts (c : FamCell) : List Fact :=
  match c.res with
  | some (_, f, b) => [f, b]
  | none => []

/-- The name of an op result outside R: the preferred family member outside
R interderivable with it (`F0.nameOf` over the run-time memberships), and
the two bridge facts. -/
structure OpName where
  tag : String
  f : F0.Fam
  n : Nat
  fwd : Fact
  bwd : Fact

/-- Names of the op results outside R.  For each family member that names
some of them, ONE op cell (the hub, the one with the smallest bridge
certificates) is bridged to the member directly; every other cell is
bridged to the hub (two small facts, `F0/Families`) and the bridge to the
member is composed (`F0.holds_trans`, `F0/Named`).  Returns the names, the
direct facts and the composed facts. -/
def opNames (fcs : List FamCell) (ops : List OpCell) :
    Except String (List OpName × List Fact × List Fact) := do
  let outside := fcs.filter (·.res.isNone)
  let mut hits : Array (OpCell × F0.Fam × Nat) := #[]
  for c in ops do
    if !c.isHit then
      let φ := c.op.apply c.i (c.j.getD 0)
      let ms := (outside.filter fun x => provable (φ.ifThen x.φ) && provable (x.φ.ifThen φ)).map
        fun x => (x.f, x.n)
      match F0.nameOf ms with
      | some (f, n) => hits := hits.push (c, f, n)
      | none => pure ()
  let targets := hits.foldl (fun (acc : Array (F0.Fam × Nat)) (_, f, n) =>
    if acc.contains (f, n) then acc else acc.push (f, n)) #[]
  let mut names := #[]
  let mut direct := #[]
  let mut composed := #[]
  for (f, n) in targets do
    let X := f.term n
    let xs := famSrc f n
    let xl := famLabel f n
    let xt := s!"{famTag f}_{n}"
    let hs := (hits.filter fun (_, f', n') => f' == f && n' == n).toList.map (·.1)
    -- the hub: the cell whose direct bridge is cheapest (first on ties)
    let mut best : Option (OpCell × Cell × Cell × Nat) := none
    for c in hs do
      let φ := c.op.apply c.i (c.j.getD 0)
      let cf ← decideF (φ.ifThen X)
      let cb ← decideF (X.ifThen φ)
      let w := cf.weight + cb.weight
      match best with
      | some (_, _, _, w') => if w < w' then best := some (c, cf, cb, w)
      | none => best := some (c, cf, cb, w)
    match best with
    | none => pure ()
    | some (hub, hf, hb, _) =>
      let hφ := hub.op.apply hub.i (hub.j.getD 0)
      let hφs := hub.op.srcOf hub.i (hub.j.getD 0)
      let htag := hub.op.tag hub.i (hub.j.getD 0)
      let hdoc := hub.op.docOf hub.i (hub.j.getD 0)
      let hubF : Fact := ⟨s!"F0.Families.{htag}_is_{xt}_fwd", s!"{hdoc} ⊢ {xl}", s!"({hφs}.ifThen {xs})", hf⟩
      let hubB : Fact := ⟨s!"F0.Families.{htag}_is_{xt}_bwd", s!"{xl} ⊢ {hdoc}", s!"({xs}.ifThen {hφs})", hb⟩
      direct := direct.push hubF |>.push hubB
      names := names.push (⟨htag, f, n, hubF, hubB⟩ : OpName)
      for c in hs do
        let tag := c.op.tag c.i (c.j.getD 0)
        if tag != htag then
          let φ := c.op.apply c.i (c.j.getD 0)
          let φs := c.op.srcOf c.i (c.j.getD 0)
          let doc := c.op.docOf c.i (c.j.getD 0)
          let a ← decideF (φ.ifThen hφ)
          let b ← decideF (hφ.ifThen φ)
          let toF : Fact := ⟨s!"F0.Families.{tag}_to_{htag}_fwd", s!"{doc} ⊢ {hdoc}", s!"({φs}.ifThen {hφs})", a⟩
          let toB : Fact := ⟨s!"F0.Families.{tag}_to_{htag}_bwd", s!"{hdoc} ⊢ {doc}", s!"({hφs}.ifThen {φs})", b⟩
          direct := direct.push toF |>.push toB
          let cF : Fact := ⟨s!"F0.Named.{tag}_is_{xt}_fwd", s!"{doc} ⊢ {xl}", s!"({φs}.ifThen {xs})",
            .comp toF.name hubF.name⟩
          let cB : Fact := ⟨s!"F0.Named.{tag}_is_{xt}_bwd", s!"{xl} ⊢ {doc}", s!"({xs}.ifThen {φs})",
            .comp hubB.name toB.name⟩
          composed := composed.push cF |>.push cB
          names := names.push (⟨tag, f, n, cF, cB⟩ : OpName)
  return (names.toList, direct.toList, composed.toList)

/-- The family members outside R, grouped by class (in the order of
preference, so the first member of a group is its name): 22 separations
for the first member, and two bridge facts for each other member. -/
structure OutGroup where
  rep : FamCell
  others : List (FamCell × Fact × Fact)
  seps : List (Nat × String × Fact)

def outGroups (fcs : List FamCell) : Except String (List OutGroup) := do
  let mut gs : Array OutGroup := #[]
  for x in fcs.filter (·.res.isNone) do
    match (gs.toList.zipIdx).find? (fun (g, _) =>
        provable (x.φ.ifThen g.rep.φ) && provable (g.rep.φ.ifThen x.φ)) with
    | some (g, i) =>
      let rt := s!"{famTag g.rep.f}_{g.rep.n}"
      let xt := s!"{famTag x.f}_{x.n}"
      let cf ← decideF (x.φ.ifThen g.rep.φ)
      let cb ← decideF (g.rep.φ.ifThen x.φ)
      gs := gs.set! i { g with others := g.others ++ [(x,
        ⟨s!"F0.Families.{xt}_is_{rt}_fwd", s!"{famLabel x.f x.n} ⊢ {famLabel g.rep.f g.rep.n}",
          s!"({famSrc x.f x.n}.ifThen {famSrc g.rep.f g.rep.n})", cf⟩,
        ⟨s!"F0.Families.{xt}_is_{rt}_bwd", s!"{famLabel g.rep.f g.rep.n} ⊢ {famLabel x.f x.n}",
          s!"({famSrc g.rep.f g.rep.n}.ifThen {famSrc x.f x.n})", cb⟩)] }
    | none =>
      let xt := s!"{famTag x.f}_{x.n}"
      let doc := famLabel x.f x.n
      let φs := famSrc x.f x.n
      let seps ← (List.range nR).mapM fun k => do
        if provable (x.φ.ifThen (rho k)) then
          let c ← decideF ((rho k).ifThen x.φ)
          pure (k, "bwd", (⟨s!"F0.Families.out_{xt}_sep_{k}", s!"{nm k} ⊬ {doc}",
            s!"({rhoSrc k}.ifThen {φs})", c⟩ : Fact))
        else
          let c ← decideF (x.φ.ifThen (rho k))
          pure (k, "fwd", (⟨s!"F0.Families.out_{xt}_sep_{k}", s!"{doc} ⊬ {nm k}",
            s!"({φs}.ifThen {rhoSrc k})", c⟩ : Fact))
      gs := gs.push ⟨x, [], seps⟩
  return gs.toList

def OutGroup.facts (g : OutGroup) : List Fact :=
  g.seps.map (·.2.2) ++ g.others.flatMap fun (_, f, b) => [f, b]

/-! ### Compound names (`F0.compoundOf`), for the classes with no family name -/

/-- The family name of class `k` (`F0.nameOf` over its run-time placed
memberships, each certified in `F0/Families`). -/
def famNameOf (fcs : List FamCell) (k : Nat) : Option (F0.Fam × Nat) :=
  F0.nameOf ((fcs.filter fun c => match c.res with
    | some (k', _, _) => k' == k
    | none => false).map fun c => (c.f, c.n))

def Op.cop : Op → F0.COp
  | .and => .and | .or => .or | .imp => .imp | .box => .box

/-- The compound as Lean source (its `term`, over the family constants). -/
def cmTerm (k : F0.Compound) : String :=
  match k.op with
  | .box => s!"PLLFormula.somehow {famSrc k.x.1 k.x.2}"
  | .and => s!"PLLFormula.and {famSrc k.x.1 k.x.2} {famSrc k.y.1 k.y.2}"
  | .or => s!"PLLFormula.or {famSrc k.x.1 k.x.2} {famSrc k.y.1 k.y.2}"
  | .imp => s!"PLLFormula.ifThen {famSrc k.x.1 k.x.2} {famSrc k.y.1 k.y.2}"

def cmTag (k : F0.Compound) : String :=
  match k.op with
  | .box => s!"box_{famTag k.x.1}_{k.x.2}"
  | o => s!"{o.tag}_{famTag k.x.1}_{k.x.2}_{famTag k.y.1}_{k.y.2}"

structure CompName where
  k : Nat
  cmp : F0.Compound
  fwd : Fact
  bwd : Fact

/-- For each class with no family name: the candidates are the certified
op cells landing in it whose operands have family names; `F0.compoundOf`
picks the preferred (a shaped term first); two tableau facts on the family terms certify it. -/
def compoundNames (fcs : List FamCell) (ops : List OpCell) : Except String (List CompName) := do
  let mut out := #[]
  for k in List.range nR do
    if (famNameOf fcs k).isNone then
      let cands : List F0.Compound := ops.filterMap fun c => match c.res with
        | .notR _ => none
        | .hit k' _ _ =>
          if k' != k then none else
          match famNameOf fcs c.i with
          | none => none
          | some x =>
            if c.op == .box then some ⟨.box, x, (.bot, 0)⟩
            else match c.j.bind (famNameOf fcs) with
              | some y => some ⟨c.op.cop, x, y⟩
              | none => none
      match F0.compoundOf cands with
      | none => pure ()
      | some cm =>
        let cf ← decideF (cm.term.ifThen (rho k))
        let cb ← decideF ((rho k).ifThen cm.term)
        let tag := cmTag cm
        out := out.push ⟨k, cm,
          ⟨s!"F0.Compound.{tag}_fwd", s!"{cm.label} ⊢ {nm k}", s!"(({cmTerm cm}).ifThen {rhoSrc k})", cf⟩,
          ⟨s!"F0.Compound.{tag}_bwd", s!"{nm k} ⊢ {cm.label}", s!"({rhoSrc k}.ifThen ({cmTerm cm}))", cb⟩⟩
  return out.toList

/-- The textbook shape of a name's term (`F0.shapeOf`), with the operands
named by `F0.labelOf?` where they are family members, printed otherwise;
and the nickname it gives (`F0.Shape.nickname`, the only source of
nicknames). -/
def shapeAndNick (φ : F) : Json × Json :=
  match F0.shapeOf φ with
  | none => (Json.null, Json.null)
  | some s =>
    let (x, y) := match s with
      | .exclMid x y => (x, y)
      | .peirceAnt x y => (x, y)
    let lab (ψ : F) : String := match F0.labelOf? ψ with
      | some (f, n) => f.label n
      | none => pp ψ
    (Json.mkObj [("kind", Json.str s.kind), ("x", Json.str (lab x)), ("y", Json.str (lab y))],
     Json.str (s.nickname (lab x) (lab y)))

/-! ## Writing the Lean files -/

def header (part title : String) (extra : String := "") : String :=
  s!"import LaxLogic.PLL.SubTab.Translate\nimport LaxLogic.RN.Rho\n{extra}\n/-!\n# {title}\n\nGENERATED by `explorergen lean` (tools/F0/ExplorerGen.lean); do not edit.\nOne theorem per fact: `PLLND.SubTab.yes'.verdict` (a closed subframe\ntableau, translated into a derivation) or `PLLND.SubTab.no.verdict` (a\nfinite subframe countermodel), checked by the kernel; each pinned at\n`[propext, Quot.sound]`.  The ρ-indices are historical labels.\n-/\n\nset_option maxRecDepth 100000\n\nopen RNReps\n\nnamespace F0.{part}\n\n"

def short (full : String) : String := (full.splitOn ".").getLast!

def partFile (part title : String) (fs : List Fact) (extra : String := "") (ns : List (String × F) := named) : String :=
  let body := String.intercalate "\n" (fs.map fun f => thmSrc (short f.name) f.doc f.spec ns f.cell)
  let pins := String.intercalate "\n" (fs.map fun f => s!"#axioms_within {f.name} [propext, Quot.sound]")
  header part title extra ++ body ++ s!"\nend F0.{part}\n\n" ++ pins ++ "\n"

def chunk {α} (n : Nat) (l : List α) : List (List α) :=
  if n == 0 then [l] else
  (List.range ((l.length + n - 1) / n)).map fun k => (l.drop (n * k)).take n

/-- Write `F0/<part>/PartK.lean` and the umbrella `F0/<part>.lean`;
returns the module names. -/
def writePart (root : System.FilePath) (part title : String) (psize : Nat) (fs : List Fact)
    (extra : String := "") (ns : List (String × F) := named) : IO (List String) := do
  let dir := root / "F0" / part
  IO.FS.createDirAll dir
  let cs := chunk psize fs
  let mut mods := #[]
  let mut k := 0
  for c in cs do
    IO.FS.writeFile (dir / s!"Part{k}.lean")
      (partFile part s!"{title}, part {k} ({c.length} facts)" c extra ns)
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
    let fcs ← IO.ofExcept famCells
    let (onames, oDirect, oComposed) ← IO.ofExcept (opNames fcs ops)
    let ogs ← IO.ofExcept (outGroups fcs)
    let t4 ← IO.monoMsNow
    IO.eprintln s!"families: {fcs.length} members searched, {(fcs.filter (·.res.isSome)).length} in R; {ogs.length} classes outside R; {onames.length} op results outside R named ({oDirect.length} direct facts, {oComposed.length} composed); in {t4 - t3} ms"
    let famFacts := fcs.flatMap FamCell.facts ++ oDirect ++ ogs.flatMap OutGroup.facts
    let cnames ← IO.ofExcept (compoundNames fcs ops)
    IO.eprintln s!"compound names: {cnames.map fun c => (nm c.k, c.cmp.label)}"
    match mode with
    | "lean" =>
      let partSize := ((rest.head?).bind String.toNat?).getD 120
      let m1 ← writePart root "Order" "The order of the 22 ρ-classes" partSize (oc.map (·.fact))
      let m2 ← writePart root "Ops" "The operation tables of the 22 ρ-classes" partSize
        (ops.flatMap OpCell.facts)
      let m3 ← writePart root "Members" "Known members of the 22 ρ-classes" partSize
        (ms.flatMap fun m => [m.fwd, m.bwd])
      let m4 ← writePart root "Families" "Family memberships of the classes (F0/Names.lean)"
        20 famFacts "import F0.Names\n" (named ++ famNamed)
      let m5 ← writePart root "Named" "Op results outside R bridged to their family names (composed)"
        partSize oComposed "import F0.Names\nimport F0.Bridge\nimport F0.Families\n" (named ++ famNamed)
      let m6 ← writePart root "Compound" "Compound names of the classes with no family name"
        partSize (cnames.flatMap fun c => [c.fwd, c.bwd]) "import F0.Names\n" (named ++ famNamed)
      IO.println s!"modules: {m1 ++ m2 ++ m3 ++ m4 ++ m5 ++ m6}"
      return 0
    | "json" =>
      match rest with
      | date :: commit :: genCommit :: checked :: _ =>
        let ck := checked.splitOn ","
        let okO := ck.contains "order"
        let okP := ck.contains "tables"
        let okM := ck.contains "members"
        let okF := ck.contains "families"
        -- family memberships and names (F0.nameOf), only from checked bridges
        let famsIn (k : Nat) : List FamCell := fcs.filter fun c => match c.res with
          | some (k', _, _) => k' == k
          | none => false
        let famJson (c : FamCell) : Json :=
          let br := match c.res with
            | some (_, f, b) => [f.name, b.name]
            | none => []
          Json.mkObj [("family", js (famTag c.f)),
            ("index", match c.f with | .bot | .top => Json.null | _ => toJson c.n),
            ("label", js (famLabel c.f c.n)), ("term", js (famTerm c.f c.n)),
            ("bridge", toJson br)]
        let okN := ck.contains "names"
        let nameFields (k : Nat) : List (String × Json) :=
          let fs := famsIn k
          let nm? := if okF then F0.nameOf (fs.map fun c => (c.f, c.n)) else none
          let cn? := if okF && okN && nm?.isNone then cnames.find? (·.k == k) else none
          -- name, long name, term, kind, bridge, the name's formula (for the shape)
          let (nmJ, longJ, tmJ, kindJ, brJ, φ?) : Json × Json × Json × Json × Json × Option F :=
            match nm?, cn? with
            | some (f, n), _ =>
              let br := (fs.find? fun c => c.f == f && c.n == n).bind fun c =>
                c.res.map fun (_, a, b) => [a.name, b.name]
              (js (famLabel f n), js (f.long n), js (famTerm f n), js "family", toJson (br.getD []),
                some (f.term n))
            | none, some c =>
              (js c.cmp.label, js c.cmp.long, js (cmTerm c.cmp), js "compound",
                toJson [c.fwd.name, c.bwd.name], some c.cmp.term)
            | none, none => (Json.null, Json.null, Json.null, Json.null, toJson ([] : List String), none)
          let (shapeJ, nickJ) := match φ? with
            | some φ => shapeAndNick φ
            | none => (Json.null, Json.null)
          let cmpJ := match cn? with
            | some c => Json.mkObj [("op", js c.cmp.op.tag),
                ("x", js (c.cmp.x.1.label c.cmp.x.2)),
                ("y", if c.cmp.op == .box then Json.null else js (c.cmp.y.1.label c.cmp.y.2))]
            | none => Json.null
          [("name", nmJ), ("long", longJ), ("term", tmJ), ("name_kind", kindJ), ("name_bridge", brJ),
           ("compound", cmpJ), ("shape", shapeJ), ("nickname", nickJ),
           ("families", Json.arr (if okF then (fs.map famJson).toArray else #[])),
           ("legacy", js (nm k)), ("legacy_const", js s!"RhoOrder.rhoF {k}")]
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
             ("formula", js (pp (rho k)))] ++ nameFields k ++ weightOf (rho k) ++
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
              | .notR seps =>
                let tag := c.op.tag c.i (c.j.getD 0)
                let on := if okF then onames.find? (·.tag == tag) else none
                [("status", js "proved"), ("result", js "notR"),
                  ("result_name", (match on with
                    | some o => js (famLabel o.f o.n)
                    | none => Json.null)),
                  ("result_name_bridge", toJson (match on with
                    | some o => [o.fwd.name, o.bwd.name]
                    | none => [])),
                  ("theorems", toJson (seps.map (·.2.2.name))),
                  ("separations", Json.arr (seps.map fun (k, d, f) =>
                    Json.mkObj [("k", toJson k), ("dir", js d), ("theorem", js f.name),
                      ("worlds", (match f.cell with | .nle m => toJson m.n | _ => Json.null))]).toArray)]
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
        let outsideMembers := fcs.filter (·.res.isNone)
        let metaJ := Json.mkObj [("pins", js "[propext, Quot.sound]"),
          ("yes", js "PLLND.SubTab.yes' (LaxLogic/PLL/SubTab/Translate.lean)"),
          ("no", js "PLLND.SubTab.no (LaxLogic/PLL/SubTab/Sound.lean)"),
          ("commit_meaning", js "commit: the commit whose F0/*.lean facts certify every proved entry of this file (each entry names its theorems); generator_commit: the commit of tools/F0/ExplorerGen.lean that wrote this file"),
          ("checked", toJson ck),
          ("checked_meaning", js "the parts whose generated modules the Lean kernel accepted at commit (order = F0/Order, tables = F0/Ops, members = F0/Members, families = F0/Families and F0/Named, names = F0/Compound), each theorem pinned at [propext, Quot.sound]; entries of other parts are pending"),
          ("rho_pairwise_distinct", toJson (okO && distinct)),
          ("rndb_candidates", toJson candidatesRNDB.length),
          ("rndb_candidates_outside_R", toJson outside),
          ("naming", js "name = the preferred certified family membership (F0.nameOf, F0/Names.lean): families ⊥, ⊤, t, c, g, s, r, w in that order, then the smallest index; t n = rn n [p := ◯⊥] for n ≤ 12, c/g/s/r/w at k = 1…4; a class with no family membership takes a compound name (F0.compoundOf: of the certified x ∘ y or ◯x over family-named operands whose table cell lands in the class, the preferred: a term of a textbook shape (F0.shapeOf) first, then operation order ◯, ∧, ∨, ↠, then the operands in name order), certified by two facts on the family terms (name_bridge); null = neither (unnamed). shape: F0.shapeOf on the name's term, two textbook shapes only; nickname: from the shape only (F0.Shape.nickname); long: the name in words (F0.Fam.word: t rung, c lax rung, g gap, s lax join, r lax arrow, w zigzag). id and legacy (ρk) are the historical labels, kept as stable ids only"),
          ("family_members_outside_R", toJson (outsideMembers.map fun c => famLabel c.f c.n))]
        let familyDefs := F0.Fam.all.map fun f =>
          Json.mkObj [("family", js f.tag), ("word", js f.word), ("definition", js f.definition), ("lean", js f.leanName),
            ("indices", toJson f.indices)]
        -- the family members outside R, one entry per class
        let outsideNamed := ogs.map fun g =>
          let rt := famLabel g.rep.f g.rep.n
          let opsHere := onames.filter fun o => o.f == g.rep.f && o.n == g.rep.n
          let opForms : List (F × List String) := opsHere.filterMap fun o =>
            (ops.find? fun c => c.op.tag c.i (c.j.getD 0) == o.tag).map fun c =>
              (c.op.apply c.i (c.j.getD 0), [o.fwd.name, o.bwd.name])
          let cands : List (F × List String) :=
            g.others.map (fun (x, f, b) => (x.φ, [f.name, b.name])) ++ opForms
          let minimal := F0.pickRep g.rep.φ (cands.map (·.1))
          let minThms := if minimal == g.rep.φ then [] else
            ((cands.find? (·.1 == minimal)).map (·.2)).getD []
          Json.mkObj [("name", js rt), ("long", js (g.rep.f.long g.rep.n)), ("term", js (famTerm g.rep.f g.rep.n)), ("shape", (shapeAndNick g.rep.φ).1), ("nickname", (shapeAndNick g.rep.φ).2),
            ("formula", js (pp g.rep.φ)),
            ("families", Json.arr ((Json.mkObj [("family", js (famTag g.rep.f)),
                ("index", toJson g.rep.n), ("label", js rt), ("term", js (famTerm g.rep.f g.rep.n)),
                ("bridge", toJson ([] : List String))]) ::
              g.others.map fun (x, f, b) => Json.mkObj [("family", js (famTag x.f)),
                ("index", toJson x.n), ("label", js (famLabel x.f x.n)),
                ("term", js (famTerm x.f x.n)), ("bridge", toJson [f.name, b.name])]).toArray),
            ("minimal", js (pp minimal)),
            ("minimal_weight", toJson [F0.boxDepth minimal, F0.size minimal, F0.boxScope minimal]),
            ("minimal_theorems", toJson minThms),
            ("op_results", toJson (opsHere.map (·.tag))),
            ("separations", toJson g.seps.length),
            ("theorems", toJson (g.seps.map (·.2.2.name)))]
        let out :=
          "{\n  \"schema\": 1,\n" ++
          s!"  \"generated\": {(js date).compress},\n  \"commit\": {(js commit).compress},\n" ++
          s!"  \"generator_commit\": {(js genCommit).compress},\n" ++
          s!"  \"meta\": {metaJ.compress},\n" ++
          s!"  \"classes\": {lines classes},\n" ++
          s!"  \"order\": {lines order},\n" ++
          s!"  \"covers\": {(Json.arr covers.toArray).compress},\n" ++
          s!"  \"ops\": {lines opsJ},\n" ++
          s!"  \"family_defs\": {lines familyDefs},\n" ++
          s!"  \"outside_named\": {lines (if okF then outsideNamed else [])},\n" ++
          s!"  \"boundary\": {boundary.compress}\n}\n"
        let path := root / "docs" / "explorer" / "f0-explorer-data.json"
        IO.FS.writeFile path out
        IO.println s!"wrote {path}: order {oc.length} ({if okO then "proved" else "pending"}), ops {ops.length} ({if okP then "proved" else "pending"}), members {ms.length} ({if okM then "proved" else "pending"}); distinct = {distinct}; covers {covers.length}"
        return 0
      | _ => IO.eprintln "usage: explorergen json <root> <date> <facts-commit> <generator-commit> <checked: order,tables,members,families,names>"; return 2
    | _ => IO.eprintln "usage: explorergen lean|json <root> ..."; return 2
  | _ => IO.eprintln "usage: explorergen lean|json <root> ..."; return 2

end ExplorerGen

def main (args : List String) : IO UInt32 := ExplorerGen.run args
