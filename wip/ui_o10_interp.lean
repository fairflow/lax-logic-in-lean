import LJF.O
import LJF.OBridge
import Rewrite

open LJFO

partial def pp : PLLFormula → String
  | .prop a => a
  | .falsePLL => "⊥"
  | .and a b => "(" ++ pp a ++ " ∧ " ++ pp b ++ ")"
  | .or a b => "(" ++ pp a ++ " ∨ " ++ pp b ++ ")"
  | .ifThen a b => "(" ++ pp a ++ " ⊃ " ++ pp b ++ ")"
  | .somehow a => "◯" ++ pp a

partial def size : PLLFormula → Nat
  | .prop _ => 1 | .falsePLL => 1
  | .and a b => 1 + size a + size b | .or a b => 1 + size a + size b
  | .ifThen a b => 1 + size a + size b | .somehow a => 1 + size a

def r  : Pos := .atom "r"
def pa : Pos := .atom "p"
def H  : Neg := .imp (.down (.circ pa)) (.up r)
def K  : Neg := .imp (.down H) (.circ pa)
def G₁ : Neg := .circ (.down K)
def K₂ : Neg := .imp (.down H) (.circ (.down K))
def G₂ : Neg := .circ (.down K₂)
def Γ₁ : List Neg := [G₁, H]
def Γ₂ : List Neg := [G₂, H]
def goalR : Neg := .up r

def norm (φ : PLLFormula) : PLLFormula := Rewrite.simplifyWith Rewrite.fullSetC 200 φ

def report (tag : String) (φ : PLLFormula) : String :=
  let n := norm φ
  tag ++ "  raw size=" ++ toString (size φ) ++ "  normal size=" ++ toString (size n) ++ "\n     " ++ pp n

#eval report "E1" (eraseNeg (interp "p" Γ₁ [] none))
#eval report "A1" (eraseNeg (interp "p" Γ₁ [] (some goalR)))
#eval report "E2" (eraseNeg (interp "p" Γ₂ [] none))
#eval report "A2" (eraseNeg (interp "p" Γ₂ [] (some goalR)))
