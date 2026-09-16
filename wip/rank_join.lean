import LaxLogic.PLL.Search.Search

/-!
# Test: the rank-bounded join for ∀p.◯(◯p⊃p)

The Visser-format uniform interpolant is the join of the p-free
rank-bounded derivers of the target.  For M := ◯(◯p⊃p) the p-free
alphabet is empty, so candidates come from the ◯-⊥ fragment.  The
claimed value ◯⊥ equals the join iff (a) ◯⊥ derives M — known — and
(b) EVERY deriver in the fragment derives ◯⊥.  A deriver violating
(b) would refute ∀p.◯(◯p⊃p) = ◯⊥ outright.  Certified two-sided
verdicts; UNKNOWNs reported.

Run: `lake build rankjoin && .lake/build/bin/rankjoin`.
-/

open PLLFormula PLLND PLLND.Search

namespace RankJoin

def pV : PLLFormula := .prop "p"
def nF (A : PLLFormula) : PLLFormula := A.ifThen .falsePLL
def gB : PLLFormula := PLLFormula.falsePLL.somehow
def tT : PLLFormula := truePLL

/-- The target: ◯(◯p⊃p). -/
def target : PLLFormula := (pV.somehow.ifThen pV).somehow

/-- Variable-free candidates through rank ~5 (representatives of the
◯-⊥ fragment: iterated ◯/¬ over ⊥, with joins/meets that are not
obviously equivalent to earlier entries). -/
def cands : List (String × PLLFormula) :=
  [ ("⊥",        .falsePLL)
  , ("⊤",        tT)
  , ("◯⊥",       gB)
  , ("◯◯⊥",      gB.somehow)
  , ("¬◯⊥",      nF gB)
  , ("¬¬◯⊥",     nF (nF gB))
  , ("◯¬◯⊥",     (nF gB).somehow)
  , ("◯¬¬◯⊥",    (nF (nF gB)).somehow)
  , ("¬◯⊥⊃◯⊥",   (nF gB).ifThen gB)
  , ("¬¬◯⊥⊃◯⊥",  (nF (nF gB)).ifThen gB)
  , ("◯⊥∨¬◯⊥",   gB.or (nF gB))
  , ("◯(◯⊥∨¬◯⊥)", (gB.or (nF gB)).somehow) ]

/-- The battery misses the F-FREE 3-chain whose only live m-edge is
the top one — exactly the shape of the two-point-tail variants the
residue probe found (they refute ¬◯⊥ ⊢ ◯(◯p⊃p)). -/
def cfg : Config :=
  { frames := defaultFrames ++
      [⟨3, [(0,1),(1,2),(0,2)], [(1,2)], []⟩,
       ⟨4, [(0,1),(1,2),(2,3),(0,2),(0,3),(1,3)], [(2,3)], []⟩],
    findBudget := some 100000 }

inductive V3 | yes | no | unk

def decPure (Γ : List PLLFormula) (Cc : PLLFormula) : V3 :=
  match decide cfg Γ Cc with
  | .proved _ => .yes
  | .refuted .. => .no
  | .unknown => .unk

def show3 : V3 → String
  | .yes => "YES"
  | .no => "no"
  | .unk => "UNK?!"

def mainLoop : IO Unit := do
  IO.println s!"=== rank-bounded join test: target {target.toString} ==="
  let mut bad := 0
  let mut unk := 0
  for (nm, d) in cands do
    let der := decPure [d] target
    match der with
    | .yes =>
        let below := decPure [d] gB
        match below with
        | .yes => IO.println s!"  {nm}: derives target, ⊢ ◯⊥ ok"
        | .no =>
            bad := bad + 1
            IO.println s!"  !!VALUE REFUTED: {nm} derives target but NOT ◯⊥"
        | .unk =>
            unk := unk + 1
            IO.println s!"  {nm}: derives target, ◯⊥-comparison UNKNOWN"
    | .no => IO.println s!"  {nm}: does not derive target"
    | .unk =>
        unk := unk + 1
        IO.println s!"  {nm}: derivability UNKNOWN"
  IO.println s!"=== bad={bad} unk={unk} (join = ◯⊥ iff bad=0, modulo unk) ==="

end RankJoin

def main : IO Unit := RankJoin.mainLoop
