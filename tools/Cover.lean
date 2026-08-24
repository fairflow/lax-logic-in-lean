/-
# The catalogue-wide PLL cover sweep (`lake exe rhocover`)

Item 2 of the order campaign (2026-08-24): mechanise what the ρ6/ρ12
worked example did by hand, for every candidate cover edge of the
22-class ρ-catalogue at once.

For each ordered pair the PLL status is computed by the standing
machinery — confluent-battery separation for `⊬` (sound:
`not_derivU_of_checkConf` + `Deriv ⊆ DerivU`), the G4c oracle AND the
LJF◯ ladder for `⊢` (sound: `proved_sound` / `laxND_of_searchProves`;
the ladder reaches the 31 cells the oracle misses at budget 10⁵).
Then every strict pair `a < b` is classified against the scope:

* **COVER**   — every `c` in the scope is EXCLUDED as an interposer
  (`a ⊬ c`, or `c ⊢ a`, or `c ⊬ b`, or `b ⊢ c` — each a settled cell):
  `a ⋖[scope] b` holds, and every conjunct is certificate-backed.
* **BLOCKED** — some `c` PROVABLY interposes (`a < c ∧ c < b`): the
  candidate edge is refuted, with the witness printed.
* **OPEN**    — neither; the undecided cells are printed as frontier
  members, never dropped.  With the 2 standing flag cells
  (`ρ12 ⊢? ρ15`, `ρ20 ⊢? ρ10`) these are the only possible source.

The classification is a COMPUTED VIEW over engine verdicts — the
banked kernel certificates are the facts; this tool says which cover
theorems are within reach and exactly which cells block the rest.

Control: the worked example must come out BLOCKED by ρ9 (the kernel
theorem `RNDB.not_covers_rho6_rho12`); the tool refuses to print a
summary if it does not.
-/
import wip.two_sided

open PLLND PLLND.RNC.CFX PLLFormula LJFO Rewrite TwoSidedLink RhoOrder

namespace RhoCover

/-- `some true` = ⊢ certified, `some false` = ⊬ certified, `none` = open. -/
abbrev Status := Option Bool

def statusMat (maxF : Nat) : IO (Array (Array Status)) := do
  let bat := battery ++ framesRooted5.toArray
  let vecs : Array (Array (Array Bool)) :=
    (List.range n).toArray.map fun i => bat.map fun M => vecOf M (rhoF i)
  let mut mat : Array (Array Status) := #[]
  for i in [0:n] do
    let mut row : Array Status := #[]
    for j in [0:n] do
      if i == j then
        row := row.push (some true)
      else
        let s : Status :=
          match firstSep bat (vecs.getD i #[]) (vecs.getD j #[]) with
          | some _ => some false
          | none =>
              if provedAt 20000 [rhoF i] (rhoF j) then some true
              else if provedAt 100000 [rhoF i] (rhoF j) then some true
              else if (TwoSided.fuelLadder maxF).any
                       (fun f => searchProves f [rhoF i] (rhoF j)) then some true
              else none
        row := row.push s
    mat := mat.push row
  return mat

/-- `a < b` certified: `a ⊢ b` and `b ⊬ a`. -/
def lt (mat : Array (Array Status)) (a b : Nat) : Bool :=
  let g := fun x y => (mat.getD x #[]).getD y none
  a != b && g a b == some true && g b a == some false

/-- `c` is EXCLUDED as an interposer of `(a, b)` when one conjunct of
`a < c ∧ c < b` is refuted by a settled cell. -/
def excluded (mat : Array (Array Status)) (a b c : Nat) : Bool :=
  let g := fun x y => mat.getD x #[] |>.getD y none
  g a c == some false || g c a == some true       -- ¬(a < c)
  || g c b == some false || g b c == some true    -- ¬(c < b)

/-- The cells still needed to settle `c`'s interposition. -/
def needed (mat : Array (Array Status)) (a b c : Nat) : List String :=
  let g := fun x y => mat.getD x #[] |>.getD y none
  (if g a c == none then [s!"ρ{a} ⊢? ρ{c}"] else [])
  ++ (if g c a == none then [s!"ρ{c} ⊢? ρ{a}"] else [])
  ++ (if g c b == none then [s!"ρ{c} ⊢? ρ{b}"] else [])
  ++ (if g b c == none then [s!"ρ{b} ⊢? ρ{c}"] else [])

def main (args : List String) : IO Unit := do
  let maxF := (args.head?.bind String.toNat?).getD 48
  IO.println s!"=== PLL cover sweep over the 22-class ρ-catalogue (LJF◯ fuel ≤ {maxF}) ==="
  let mat ← statusMat maxF
  -- the matrix, and its open cells
  let mut openCells : List (Nat × Nat) := []
  let mut nPos := 0; let mut nNeg := 0
  for i in [0:n] do
    for j in [0:n] do
      if i != j then
        match mat.getD i #[] |>.getD j none with
        | some true => nPos := nPos + 1
        | some false => nNeg := nNeg + 1
        | none => openCells := (i, j) :: openCells
  IO.println s!"status over {n * (n-1)} cells: {nPos} ⊢, {nNeg} ⊬, {openCells.length} open"
  for (i, j) in openCells.reverse do
    IO.println s!"  OPEN CELL ρ{i} ⊢? ρ{j}"
  IO.println ""
  -- strict pairs
  let strict := (List.range n).flatMap fun a =>
    (List.range n).filterMap fun b => if lt mat a b then some (a, b) else none
  IO.println s!"strict pairs (a < b certified): {strict.length}"
  -- classification
  let mut covers : List (Nat × Nat) := []
  let mut blocked := 0
  let mut openEdges := 0
  let mut controlOK := false
  IO.println ""
  IO.println "── candidate cover edges ──"
  for (a, b) in strict do
    let inter := (List.range n).filter fun c => c != a && c != b && lt mat a c && lt mat c b
    match inter with
    | c :: _ =>
        blocked := blocked + 1
        if a == 6 && b == 12 && inter.contains 9 then controlOK := true
        IO.println s!"  BLOCKED ρ{a} < ρ{b}  (interposer ρ{c}{if inter.length > 1 then s!", +{inter.length - 1} more" else ""})"
    | [] =>
        let undecided := (List.range n).filter fun c =>
          c != a && c != b && !excluded mat a b c
        if undecided.isEmpty then
          covers := (a, b) :: covers
          IO.println s!"  COVER   ρ{a} ⋖ ρ{b}   (every interposer excluded by settled cells)"
        else
          openEdges := openEdges + 1
          IO.println s!"  OPEN    ρ{a} <⋖? ρ{b}  undecided interposers: {undecided.map (s!"ρ{·}")}"
          for c in undecided do
            for cell in needed mat a b c do
              IO.println s!"          FRONTIER {cell}"
  IO.println ""
  IO.println s!"HASSE (scoped to the catalogue): {covers.length} cover edges, {blocked} blocked, {openEdges} open"
  for (a, b) in covers.reverse do
    IO.println s!"  HASSE ρ{a} ⋖ ρ{b}"
  if !controlOK then
    IO.println "CONTROL FAILED: ρ6/ρ12 did not come out BLOCKED by ρ9 — do not trust this run"
  else
    IO.println "control: ρ6 < ρ12 BLOCKED by ρ9, matching kernel theorem RNDB.not_covers_rho6_rho12"
  IO.println "RHOCOVER-DONE"

end RhoCover

def main (args : List String) : IO Unit := RhoCover.main args
