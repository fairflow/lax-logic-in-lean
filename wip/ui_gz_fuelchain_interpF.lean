import LJF.O
import LJF.OFuel
import LJF.OBridge
import Rewrite
open LJFO
partial def pp : PLLFormula → String
  | .prop a => a | .falsePLL => "⊥"
  | .and a b => "(" ++ pp a ++ " ∧ " ++ pp b ++ ")" | .or a b => "(" ++ pp a ++ " ∨ " ++ pp b ++ ")"
  | .ifThen a b => "(" ++ pp a ++ " ⊃ " ++ pp b ++ ")" | .somehow a => "◯" ++ pp a
partial def size : PLLFormula → Nat
  | .prop _ => 1 | .falsePLL => 1 | .and a b => 1 + size a + size b | .or a b => 1 + size a + size b
  | .ifThen a b => 1 + size a + size b | .somehow a => 1 + size a
-- the GZ-candidate cell of docs/ljfo-plan.md: ({◯p→r, ◯q} ⇒ ◯p), eliminate p
def Hpr : Neg := .imp (.down (.circ (.atom "p"))) (.up (.atom "r"))   -- ◯p ⊃ r
def Cq  : Neg := .circ (.atom "q")                                      -- ◯q
def S   : List Neg := [Hpr, Cq]
def gCirc : Neg := .circ (.atom "p")                                    -- goal ◯p, plain
def gUp   : Neg := .up (.down (.circ (.atom "p")))                      -- goal ↑↓◯p, the antecedent form
def norm (φ : PLLFormula) : PLLFormula := Rewrite.simplifyWith Rewrite.fullSetC 200 φ
def rep (tag : String) (n : Nat) (g : Option Neg) : String :=
  let φ := eraseNeg (interpF "p" n S [] g)
  let m := norm φ
  tag ++ " fuel=" ++ toString n ++ " raw=" ++ toString (size φ) ++ " normal=" ++ toString (size m) ++ "  " ++ pp m
#eval rep "GZ_E"  4 none
#eval rep "GZ_E"  8 none
#eval rep "GZ_E" 12 none
#eval rep "GZ_E" 16 none
#eval rep "GZ_Ac"  4 (some gCirc)
#eval rep "GZ_Ac"  8 (some gCirc)
#eval rep "GZ_Ac" 12 (some gCirc)
#eval rep "GZ_Ac" 16 (some gCirc)
#eval rep "GZ_Au"  4 (some gUp)
#eval rep "GZ_Au"  8 (some gUp)
#eval rep "GZ_Au" 12 (some gUp)
#eval rep "GZ_Au" 16 (some gUp)
#eval rep "GZ_E" 20 none
#eval rep "GZ_Ac" 20 (some gCirc)
#eval rep "GZ_Au" 20 (some gUp)
