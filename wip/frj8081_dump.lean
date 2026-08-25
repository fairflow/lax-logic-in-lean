/-
# FRJ incompleteness #80/#81 — database dump and semantic table

Diagnostic script, run with `lake env lean --run wip/frj8081_dump.lean`.

For each of the two cells (ρ12 ⊢? ρ9), (ρ13 ⊢? ρ6):
  1. the goal G = ofPLL (ρᵢ ⊃ ρⱼ) and its subformula universes;
  2. the forcing table of the kernel countermodel `RNDB.sepM`
     (5 worlds, rm = {(2,3)}, world 3 fallible) over those universes,
     re-evaluated here against FRJ's own forcing clauses;
  3. the FULL saturated database of the Profile engine at the
     frontier2 budget (rounds=40, RS/IS 6000, lamCap off).
-/
import FRJ.Search.Profile
import FRJ.Bridge
import LaxLogic.RN.Rho

open FRJ RhoOrder

namespace Dump

def ppF : Form → String
  | .atom p => p
  | .bot => "⊥"
  | .and a b => s!"({ppF a} ∧ {ppF b})"
  | .or a b => s!"({ppF a} ∨ {ppF b})"
  | .imp a .bot => s!"¬{ppF a}"
  | .imp a b => s!"({ppF a} ⊃ {ppF b})"
  | .circ a => s!"◯{ppF a}"

def ppL (l : List Form) : String :=
  if l.isEmpty then "·" else String.intercalate ", " (l.map ppF)

def ppTag : Tag → String
  | .barren => "barren"
  | .chain D => s!"chain {ppF D}"
  | .blocked => "blocked"

def cfg : Search.Config :=
  { rounds := 40, lamCap := 1000000, maxRS := 6000, maxIS := 6000 }

def goal (i j : Nat) : Form := ofPLL (PLLFormula.ifThen (rhoF i) (rhoF j))

/-! ## The sepM countermodel, evaluated with FRJ's forcing clauses -/

def up : Nat → List Nat
  | 0 => [0,1,2,3,4]
  | 1 => [1,2,3]
  | 2 => [2,3]
  | 3 => [3]
  | 4 => [4]
  | _ => []

def rms : Nat → List Nat
  | 2 => [2,3]
  | b => [b]

partial def fB (w : Nat) : Form → Bool
  | .bot => w == 3
  | .atom _ => false
  | .and A B => fB w A && fB w B
  | .or A B => fB w A || fB w B
  | .imp A B => (up w).all (fun b => !(fB b A) || fB b B)
  | .circ A => (up w).all (fun b => (rms b).any (fun c => fB c A))

def dedup (l : List Form) : List Form :=
  l.foldl (fun acc x => if x ∈ acc then acc else acc ++ [x]) []

def forcedWorlds (A : Form) : List Nat :=
  [0,1,2,3,4].filter (fun w => fB w A)

/-! ## The dump -/

def dumpCell (i j : Nat) : IO Unit := do
  let G := goal i j
  IO.println s!"===================== ρ{i} ⊢? ρ{j} ====================="
  IO.println s!"G = {ppF G}"
  IO.println ""
  IO.println s!"-- Sf^R(G) ({(dedup (sfR G)).length} formulas):"
  for A in dedup (sfR G) do
    IO.println s!"    {ppF A}"
  IO.println s!"-- Ĝ = Ĝ_at ++ Ĝ_imp ++ Ĝ_circ ({(dedup (gHat G)).length}):"
  for A in dedup (gHat G) do
    IO.println s!"    {ppF A}"
  IO.println ""
  IO.println "-- sepM forcing table (worlds forcing each formula; universe = SfR ∪ SfL):"
  for A in dedup (sfR G ++ sfL G) do
    IO.println s!"    {forcedWorlds A}  ⊩  {ppF A}"
  IO.println s!"-- root refutes G: {!(fB 0 G)}"
  IO.println ""
  let (db, st) := Search.saturateProf G cfg
  let s := st.toStats
  IO.println s!"-- saturation: r={s.roundsUsed} RS={s.rsSize} IS={s.isSize} lamCapped={s.lamCapped} dbCapped={s.dbCapped}"
  IO.println ""
  IO.println s!"-- REGULAR rows ({db.rs.length}):"
  for r in db.rs do
    IO.println s!"    [{ppTag r.t}]  {ppL r.ctx}  ⇒  {ppF r.rhs}"
  IO.println ""
  IO.println s!"-- IRREGULAR rows ({db.is.length}):"
  for r in db.is do
    IO.println s!"    {ppL r.stab} ; {ppL r.th}  →  {ppF r.rhs}"
  IO.println ""

def main : IO Unit := do
  dumpCell 12 9
  dumpCell 13 6

end Dump

def main : IO Unit := Dump.main
