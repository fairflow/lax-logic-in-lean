/-
Measure the FLOOR of the nested ∧/∨ corpus of `wip/rw_screen.lean`.

`rwscreen` reports that the 3,996 nested trees collapse to 25 distinct
normal forms.  `docs/rn-dictionary-status.md` calls 15 "the floor (the
dictionary's classes, which the ∧/∨ closure cannot leave)".  This tool
measures instead of asserting:

* 25 is a CERTIFIED UPPER BOUND on the number of ⊣⊢-classes present,
  because `simplifyWith_interd` makes every collapse an interderivability;
* the LOWER bound is computed here by battery separation between the
  residual forms (a mutually confluent ≤5-world countermodel to
  `[X] ⊢ Y`, sound for PLL through `not_derivU_of_checkConf` +
  `Deriv ⊆ DerivU`), so a reported "distinct" pair is certificate-backed.

Prints the partition and both bounds.  Read-only: no existing file edited.
-/
import Rewrite
import wip.rho_order

open PLLND PLLND.SemUI PLLND.RNC.CFX Rewrite

namespace FloorProbe

abbrev F := PLLFormula

/-! The corpus of `wip/rw_screen.lean`, transcribed verbatim. -/

def bot : F := .falsePLL
def top : F := .ifThen bot bot
def oBot : F := .somehow bot
def nOBot : F := .ifThen oBot bot
def q4 : F := .or nOBot oBot
def nnOBot : F := .ifThen nOBot bot
def q5 : F := .somehow nOBot
def q10 : F := .ifThen nnOBot oBot
def q8 : F := .ifThen q5 q4
def q9 : F := .or nnOBot q5

def reps : List F := [bot, top, oBot, nOBot, q4, nnOBot, q5, q10, q8, q9]

def nested : List F :=
  (reps.flatMap fun a => reps.flatMap fun b => reps.flatMap fun c =>
    [ .and (.and a b) c, .and a (.and b c),
      .and (.and c b) a, .and c (.and b a),
      .or (.or a b) c, .or a (.or b c),
      .or (.or c b) a, .or c (.or b a) ]).eraseDups

def run : IO Unit := do
  let out ← IO.getStdout
  let norms := nested.map (fun c => simplifyWith fullSetC 6 c)
  -- dedup by canonical key
  let mut forms : List F := []
  let mut keys : List String := []
  for f in norms do
    let k := Rewrite.keyF f
    if !keys.contains k then
      keys := keys ++ [k]
      forms := forms ++ [f]
  IO.println s!"nested corpus: {nested.length} cells"
  IO.println s!"distinct normal forms (canon+norm): {forms.length}"
  IO.println s!"UPPER BOUND on classes present: {forms.length}  (simplifyWith_interd)"
  out.flush
  let bat := battery ++ framesRooted5.toArray
  let vecs := forms.toArray.map fun f => bat.map fun M => vecOf M f
  -- union-find over pairs that neither battery-separates in either direction
  let m := forms.length
  let mut sep : Array (Array Bool) := #[]
  for i in [0:m] do
    let mut row : Array Bool := #[]
    for j in [0:m] do
      let s := (firstSep bat (vecs.getD i #[]) (vecs.getD j #[])).isSome
      row := row.push s
    sep := sep.push row
  -- i, j are CERTIFIED distinct if separated in either direction
  let mut distinctPairs := 0
  let mut unresolved : List (Nat × Nat) := []
  for i in [0:m] do
    for j in [i+1:m] do
      if (sep.getD i #[]).getD j false || (sep.getD j #[]).getD i false then
        distinctPairs := distinctPairs + 1
      else
        unresolved := unresolved ++ [(i, j)]
  IO.println s!"pairs certified DISTINCT by battery separation: {distinctPairs} of {m * (m-1) / 2}"
  IO.println s!"pairs the battery leaves unresolved: {unresolved.length}"
  for (i, j) in unresolved do
    IO.println s!"  unresolved: form {i}  vs  form {j}"
  -- a clique of pairwise-separated forms is a certified lower bound;
  -- greedy is enough here, and it is reported as a LOWER bound only.
  let mut clique : List Nat := []
  for i in [0:m] do
    if clique.all (fun j => (sep.getD i #[]).getD j false || (sep.getD j #[]).getD i false) then
      clique := clique ++ [i]
  IO.println s!"LOWER BOUND on classes present (greedy pairwise-separated clique): {clique.length}"
  IO.println s!"  clique members (form indices): {clique}"
  IO.println "the forms:"
  for i in [0:m] do
    let k := keys.getD i ""
    IO.println s!"  [{i}] {k}"
  IO.println "FLOOR-PROBE-DONE"

end FloorProbe

def main : IO Unit := FloorProbe.run
