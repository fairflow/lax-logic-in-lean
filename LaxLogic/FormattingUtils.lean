universe u

open Std (Format)

-- If a
def stripParens {α : Type u}
    (reprAuxFn : α  → Nat → Format) (parenLeft: Char := '(')  (parenRight: Char := ')') :
    α  → Nat → Format :=
  fun (a:α)(prec: Nat) =>
    let rawFormat : Format := reprAuxFn a prec
    let str  : String := Format.pretty rawFormat
    if str.length ≥ 2 && str.front = parenLeft && str.back = parenRight then
      -- drop the first and last character
      Format.text <| (str.drop 1).dropRight 1
    else
      rawFormat
