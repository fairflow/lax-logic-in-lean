/- A1 — the chain saboteur (docs/frjw-fixpoint-attack.md).
Target T-A: every `KeptChain` link lands in `keptOf`.  Seeds are
dependency-shaped (linear, diamond, Clo-mediated, ◯-towers, mixed,
duplicated); per seed ALL orderings of ALL sublists of the pool are
enumerated (exhaustive at the boundary), each checked with the
certificate checker `keptChainB'`, and every link of every valid
chain is required to be in `keptOf`.  GATE-WATCH: `keptOfBroken`
(fuel 0) must go red on the same seeds. -/
import FRJ.RefAt
open FRJ Form

def aa : Form := .atom "a"
def bb : Form := .atom "b"
def uu : Form := .atom "u"
def vv : Form := .atom "v"

-- link₁: antecedent bottoms in Υ directly
def l1 : Form := .imp (.imp aa bb) bb
-- link₂: antecedent needs link₁ IN THE CONTEXT (Clo .base through the
-- imp-clause) — the order-sensitive mechanism
def l2 : Form := .imp (.imp l1 uu) bb
-- link₃: needs link₂
def l3 : Form := .imp (.imp l2 uu) bb
-- link₄ (diamond): needs link₂ AND link₃
def l4 : Form := .imp (.imp l2 (.imp l3 uu)) bb
-- link₅: ◯-tower antecedent, order-free
def l5 : Form := .imp (.circ (.circ vv)) bb
-- link₆: never keepable (antecedent bottoms at an atom outside Υ)
def l6 : Form := .imp (.atom "dead") bb

structure Seed where
  name : String
  ups : List Form
  base : List Form
  pool : List Form

def seeds : List Seed := [
  ⟨"linear", [.imp aa bb, uu], [], [l1, l2, l3]⟩,
  ⟨"diamond", [.imp aa bb, uu], [], [l1, l2, l3, l4]⟩,
  ⟨"tower+mix", [.imp aa bb, uu, vv], [], [l1, l2, l5, l6]⟩,
  ⟨"duplicates", [.imp aa bb, uu], [], [l1, l1, l2]⟩,
  ⟨"base-mediated", [uu], [l1], [l2, l3]⟩
]

/-- All orderings of all sublists. -/
def allChains (pool : List Form) : List (List Form) :=
  pool.sublists.flatMap List.permutations

def checkSeed (keptFn : List Form → List Form → List Form → List Form)
    (s : Seed) : String := Id.run do
  let kept := keptFn s.ups s.base s.pool
  let cands := allChains s.pool
  let valid := cands.filter (keptChainB' s.ups s.base s.pool)
  let mut missed : List Form := []
  for ch in valid do
    for y in ch do
      if !(kept.contains y) && !(missed.contains y) then
        missed := missed ++ [y]
  let verdict := if missed.isEmpty then "PASS" else s!"FAIL missed={missed.length}"
  return s!"{s.name}: candidates={cands.length} valid-chains={valid.length} " ++
    s!"keptOf={kept.length} {verdict}"

/-- The deliberately broken kept function for the gate-watch. -/
def keptOfBroken (_ups _base _pool : List Form) : List Form := []

def main : IO Unit := do
  IO.println "== A1 chain saboteur — the real keptOf =="
  for s in seeds do IO.println (checkSeed keptOf s)
  IO.println "== gate-watch: keptOfBroken (must FAIL wherever chains exist) =="
  for s in seeds do IO.println (checkSeed keptOfBroken s)

#eval main
