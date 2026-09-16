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
def r : Pos := .atom "r"
def pa : Pos := .atom "p"
def H : Neg := .imp (.down (.circ pa)) (.up r)
def K : Neg := .imp (.down H) (.circ pa)
def G₁ : Neg := .circ (.down K)
def K₂ : Neg := .imp (.down H) (.circ (.down K))
def G₂ : Neg := .circ (.down K₂)
def Γ₁ : List Neg := [G₁, H]
def Γ₂ : List Neg := [G₂, H]
def goalR : Neg := .up r
def norm (φ : PLLFormula) : PLLFormula := Rewrite.simplifyWith Rewrite.fullSetC 200 φ
def rep (tag : String) (n : Nat) (Γ : List Neg) (g : Option Neg) : String :=
  let φ := eraseNeg (interpF "p" n Γ [] g)
  let m := norm φ
  tag ++ " fuel=" ++ toString n ++ " raw=" ++ toString (size φ) ++ " normal=" ++ toString (size m) ++ "  " ++ pp m
#eval rep "E1F" 4 Γ₁ none
#eval rep "E1F" 8 Γ₁ none
#eval rep "E1F" 16 Γ₁ none
#eval rep "A1F" 4 Γ₁ (some goalR)
#eval rep "A1F" 8 Γ₁ (some goalR)
#eval rep "A1F" 16 Γ₁ (some goalR)
#eval rep "A2F" 8 Γ₂ (some goalR)
#eval rep "A2F" 16 Γ₂ (some goalR)
