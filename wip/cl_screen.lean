/-
THE `Cl` SCREEN — the go/no-go for lifting FRJ(G) to ◯
(docs/frj-lifting.md §5, obligation 1).

FRJ absorbs ALL LEFT RULES into a closure operator `Cl`, justified by
its Lemma 5: a world's theory over the goal's subformulas is
`Cl` of its *determining part* `Λ*` (in IPC: the atoms and
implications — the formulas that are not ∧/∨, since ∧/∨ are
recovered compositionally).  If the PLL analogue fails, left-rule
absorption fails and the architecture does not transfer AS IS.

Matthew's note, respected in the design of this screen: **a failure
may be repairable by changing `Cl` or `Λ*`**.  So the screen does not
test one statement, it tests a LATTICE of variants and reports which
combination survives:

  Λ* variants (the determining part)
    D0  atoms + ⊥                       (deliberately too small: control)
    D1  atoms + ⊥ + implications        (the literal IPC choice)
    D2  D1 + ◯-formulas                 (the proposed PLL repair)
  Cl variants (the closure)
    C0  no closure at all               (control)
    C1  PLL-consequence closure, i.e. {C ∈ S : Λ* ⊢_PLL C}

Direction: `Cl(Λ*) ⊆ Λ` always holds by soundness, so only
`Λ ⊆ Cl(Λ*)` can fail — and a failure is a CERTIFICATE (a world, and
a formula forced there but not derivable from the determining part).
One appended line per failure; counts always printed.
-/
import LaxLogic.PLLCountermodelEmit
import LaxLogic.PLLSearchConf

open PLLND PLLND.FinCM

namespace ClScreen

abbrev F := PLLFormula

/-! ## Goals, and their subformula sets -/

def bot : F := .falsePLL
def oBot : F := .somehow bot
def nOBot : F := .ifThen oBot bot
def nnOBot : F := .ifThen nOBot bot
def q5 : F := .somehow nOBot
def q4 : F := .or nOBot oBot
def q8 : F := .ifThen q5 q4
def pv : F := .prop "p"
def qv : F := .prop "q"

def goals : List (String × F) :=
  [("¬◯⊥", nOBot), ("◯¬◯⊥", q5), ("g1", q8),
   ("◯p⊃p", .ifThen (.somehow pv) pv),
   ("◯(p∨q)⊃(◯p∨◯q)",
     .ifThen (.somehow (.or pv qv)) (.or (.somehow pv) (.somehow qv))),
   ("◯(p∧◯q)", .somehow (.and pv (.somehow qv)))]

/-- Subformulas, closed. -/
def subs : F → List F
  | .prop a => [.prop a]
  | .falsePLL => [.falsePLL]
  | .and A B => .and A B :: (subs A ++ subs B)
  | .or A B => .or A B :: (subs A ++ subs B)
  | .ifThen A B => .ifThen A B :: (subs A ++ subs B)
  | .somehow A => .somehow A :: subs A

def sl (G : F) : List F := (bot :: subs G).eraseDups

/-! ## The determining-part variants -/

def isAtomic : F → Bool
  | .prop _ => true
  | .falsePLL => true
  | _ => false

def isImp : F → Bool
  | .ifThen _ _ => true
  | _ => false

def isBox : F → Bool
  | .somehow _ => true
  | _ => false

def det (variant : Nat) (A : F) : Bool :=
  match variant with
  | 0 => isAtomic A
  | 1 => isAtomic A || isImp A
  | _ => isAtomic A || isImp A || isBox A

/-! ## The battery (curated, per doctrine: failures are certificates) -/

def pvS : String := "p"
def qvS : String := "q"

def bank : List (String × FinCM) :=
  [("chain2", ⟨2, [(0,1)], [(0,1)], [], [(1, pvS)]⟩),
   ("chain3F", ⟨3, [(0,1),(1,2),(0,2)], [(1,2)], [2], [(0,pvS),(1,pvS),(2,pvS)]⟩),
   ("gadget3", ⟨3, [(0,1),(1,2),(0,2)], [(1,2)], [], [(2, pvS)]⟩),
   ("gadget4", ⟨4, [(0,1),(1,2),(2,3),(0,2),(0,3),(1,3)], [(2,3)], [],
      [(3, pvS)]⟩),
   ("lobT", ⟨3, [(0,1),(0,2),(2,1)], [(2,1)], [], [(1, pvS)]⟩),
   ("fork", ⟨3, [(0,1),(0,2)], [(0,2)], [2], [(1, pvS)]⟩),
   ("forkPQ", ⟨3, [(0,1),(0,2)], [(0,1),(0,2)], [], [(1, pvS), (2, qvS)]⟩),
   ("deep5", ⟨5, [(0,1),(1,2),(2,3),(3,4),(0,2),(0,3),(0,4),(1,3),(1,4),(2,4)],
      [(1,2),(2,3),(3,4),(1,3),(1,4),(2,4)], [4],
      [(2,pvS),(3,pvS),(4,pvS)]⟩)]

/-! ## The closure -/

def provedFrom (b : Nat) (Γ : List F) (C : F) : Bool :=
  decide (C ∈ Γ) ||
  (match Search.decide { findBudget := some b, emitClosureCap := 0 } Γ C with
   | .proved _ => true
   | _ => false)

/-- `Cl` variant `c` applied to the determining part. -/
def clOf (c : Nat) (b : Nat) (S : List F) (Λstar : List F) : List F :=
  match c with
  | 0 => Λstar
  | _ => S.filter fun C => provedFrom b Λstar C

/-! ## The screen -/

structure Res where
  cells : Nat := 0
  fails : Nat := 0
  certs : List String := []

def screen (dv cv : Nat) (b : Nat) : Res := Id.run do
  let mut r : Res := {}
  for (gn, G) in goals do
    let S := sl G
    for (mn, M) in bank do
      for w in List.range M.n do
        let Λ := S.filter (M.forceB w ·)
        let Λstar := Λ.filter (det dv ·)
        let cl := clOf cv b S Λstar
        r := { r with cells := r.cells + 1 }
        match Λ.find? (fun C => !(decide (C ∈ cl))) with
        | some C =>
            let msg := s!"D{dv}/C{cv} FAIL goal={gn} model={mn} w={w}: {reprStr C} forced, not in Cl(Λ*)"
            r := { r with fails := r.fails + 1, certs := msg :: r.certs }
        | none => pure ()
  return r

def main : IO Unit := do
  IO.println "The Cl screen: is a PLL world's theory Cl of its determining part?"
  IO.println s!"goals={goals.length}  models={bank.length}  (failures are certificates)"
  IO.println ""
  for cv in [0, 1] do
    for dv in [0, 1, 2] do
      let r := screen dv cv 6000
      let dn := match dv with
        | 0 => "atoms+⊥        "
        | 1 => "atoms+⊥+imp    "
        | _ => "atoms+⊥+imp+◯  "
      let cn := if cv == 0 then "NO closure " else "PLL-closure"
      IO.println s!"  Λ*={dn} Cl={cn}: {r.cells} cells, {r.fails} FAIL"
      for c in r.certs.take 2 do IO.println s!"      {c}"
      (← IO.getStdout).flush
  IO.println ""
  IO.println "CL-SCREEN-DONE"

end ClScreen

def main : IO Unit := ClScreen.main
