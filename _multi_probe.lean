import LaxLogic.PLLFormula

namespace MultiProbe
open PLLFormula

def size : PLLFormula → Nat
  | .prop _ => 1
  | .falsePLL => 1
  | .ifThen a b => size a + size b
  | .and a b => size a + size b
  | .or a b => size a + size b
  | .somehow a => size a + 1

theorem lemA (φ : PLLFormula) : 0 < size φ := by
  sorry

theorem lemB (φ ψ : PLLFormula) : size (.and φ ψ) = size φ + size ψ := by
  rfl

theorem main (φ : PLLFormula) : 0 < size φ + 1 := by
  have h := lemA φ
  omega

end MultiProbe
