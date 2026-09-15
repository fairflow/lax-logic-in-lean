import LaxLogic.PLL.Semantics.Kripke
import LaxLogic.PLL.G4.G4H
import LaxLogic.QLL.Complete
import LaxLogic.QLL.Kripke

/-!
# Pinned behaviour of the tagged turnstiles (`LaxLogic/Util/Turnstile.lean`)

Elaboration and printing, in and out of the developments' scopes.  `G4h` is
registered here only, as an example of a non-default calculus with a tag
argument.
-/

attribute [turnstile] PLLND.G4h

section outside
variable (Γ : List PLLFormula) (A : PLLFormula)

/-- info: Γ ⊢[PLLND.LaxND] A : Type -/
#guard_msgs in #check Γ ⊢[PLLND.LaxND] A

/-- info: Γ ⊬[PLLND.LaxND] A : Prop -/
#guard_msgs in #check ¬ Nonempty (PLLND.LaxND Γ A)

/--
error: no default relation for `⊢` in scope: write `Γ ⊢[R] A`, or open the development that declares one
-/
#guard_msgs in #check Γ ⊢ A
end outside

section pll
open PLLND
variable (Γ : List PLLFormula) (A : PLLFormula) (n : Nat)

/-- info: Γ ⊢ A : Type -/
#guard_msgs in #check Γ ⊢ A

/-- info: Γ ⊬ A : Prop -/
#guard_msgs in #check Γ ⊬ A

/-- info: Γ ⊨ A : Prop -/
#guard_msgs in #check Γ ⊨ A

/-- info: Γ ⊭ A : Prop -/
#guard_msgs in #check Γ ⊭ A

/-- info: A :: Γ ⊢[G4h n] A : Prop -/
#guard_msgs in #check A :: Γ ⊢[G4h n] A

/-- info: Γ ⊬[G4h n] A : Prop -/
#guard_msgs in #check ¬ G4h n Γ A

-- the notation is the relation, definitionally and syntactically
example : (Γ ⊢ A) = LaxND Γ A := rfl
example : (Γ ⊬ A) = ¬ Nonempty (LaxND Γ A) := rfl
example : (Γ ⊭ A) = ¬ Consequence Γ A := rfl
end pll

section qll
open LaxLogic.QLL
variable (Γ : List Form) (S : Set Form) (A : Form)

/-- info: Γ ⊢ A : Prop -/
#guard_msgs in #check Γ ⊢ A

-- a set context selects `SetPrv`
/-- info: S ⊢ A : Prop -/
#guard_msgs in #check S ⊢ A
example : (S ⊢ A) = SetPrv S A := rfl

/-- info: Γ ⊬ A : Prop -/
#guard_msgs in #check Γ ⊬ A
example : (Γ ⊬ A) = ¬ Prv Γ A := rfl

/-- info: Γ ⊨ A : Prop -/
#guard_msgs in #check Γ ⊨ A
end qll

section both
open PLLND LaxLogic.QLL
variable (Γ : List PLLFormula) (A : PLLFormula) (Δ : List Form) (B : Form)

-- two developments open: the context type decides
/-- info: Γ ⊢ A : Type -/
#guard_msgs in #check Γ ⊢ A

/-- info: Δ ⊢ B : Prop -/
#guard_msgs in #check Δ ⊢ B

-- Lean's own `⊢` in tactic locations is unaffected
example (a b : Nat) (h : a + 0 = b) : a = b + 0 := by simp at h ⊢; exact h
end both

-- a theorem generic in the calculus
theorem Turnstile.generic_mono {F : Type} (R : List F → F → Prop) (Γ : List F) (A : F)
    (h : Γ ⊢[R] A) : Γ ⊢[R] A := h
