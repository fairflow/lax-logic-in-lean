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

/-- info: Γ, A ⊢[G4h n] A : Prop -/
#guard_msgs in #check A :: Γ ⊢[G4h n] A

/-- info: Γ ⊬[G4h n] A : Prop -/
#guard_msgs in #check ¬ G4h n Γ A

-- the notation is the relation, definitionally and syntactically
example : (Γ ⊢ A) = LaxND Γ A := rfl
example : (Γ ⊬ A) = ¬ Nonempty (LaxND Γ A) := rfl
example : (Γ ⊭ A) = ¬ Consequence Γ A := rfl
end pll

section pllContexts
open PLLND
variable (Γ : List PLLFormula) (S : Set PLLFormula) (p q r : PLLFormula) (n : Nat)

-- sequent-style contexts: `Γ, A` is `A :: Γ`, both ways
example : (Γ, p, q ⊢ p) = LaxND (q :: p :: Γ) p := rfl
/-- info: Γ, p, q ⊢ p : Type -/
#guard_msgs in #check LaxND (q :: p :: Γ) p
/-- info: Γ, p ⊢[G4h n] q : Prop -/
#guard_msgs in #check Γ, p ⊢[G4h n] q

-- formula notation, the same inside and outside a sequent
example : (Γ, ◯p ↠ q ⊢ r ∨ ⊥) = LaxND (.ifThen (.somehow p) q :: Γ) (.or r .falsePLL) := rfl
/-- info: Γ, ◯p ↠ q ⊢ r ∨ ⊥ : Type -/
#guard_msgs in #check LaxND (.ifThen (.somehow p) q :: Γ) (.or r .falsePLL)
/-- info: ◯(p ∧ q) ↠ ◯p ∧ ◯q : PLLFormula -/
#guard_msgs in #check ◯(p ∧ q) ↠ ◯p ∧ ◯q
/-- info: Γ ⊬ p ↠ q : Prop -/
#guard_msgs in #check Γ ⊬ p ↠ q
/-- info: Γ ⊨ ◯p ↠ ◯q : Prop -/
#guard_msgs in #check Γ ⊨ ◯p ↠ ◯q

-- a set context selects `SetDeriv`, with comma and with `insert`
example : (S, p ⊢ q) = SetDeriv (insert p S) q := rfl
example : (insert p S ⊢ q) = SetDeriv (insert p S) q := rfl
/-- info: S, p ⊢ q : Prop -/
#guard_msgs in #check SetDeriv (insert p S) q

-- no context variable: a list or a set, so a tag or brackets are needed
/--
error: `⊢` is ambiguous here (PLLND.LaxND, PLLND.SetDeriv): write `Γ ⊢[R] A` (a context without a context variable could be a list or a set: write `[A, B]` or `{A, B}`)
-/
#guard_msgs in #check p, q ⊢ r
example : ([p, q] ⊢ r) = LaxND [p, q] r := rfl
example : (p, q ⊢[LaxND] r) = LaxND [p, q] r := rfl
-- the empty context prints as `[]` while a set default could also read `⊢`
/-- info: [] ⊢ p ↠ p : Type -/
#guard_msgs in #check LaxND [] (p ↠ p)

-- implications between sequents; `Prop` connectives around a sequent need parentheses
example : (Γ ⊢ p → Γ, p ⊢ q) = (LaxND Γ p → LaxND (p :: Γ) q) := rfl
example : ((Γ ⊨ p) ∧ (Γ ⊨ q)) = (Consequence Γ p ∧ Consequence Γ q) := rfl
-- the comma of an unbracketed binder belongs to the binder, not to a context
example : (∀ C : PLLFormula, Γ ⊢ C) = ∀ C, LaxND Γ C := rfl
example : (∀ x y : PLLFormula, Γ, x ⊢ y) = ∀ x y, LaxND (x :: Γ) y := rfl
example (Ds : List PLLFormula) : (∀ φ ∈ Ds, Γ, φ ⊢ r) = ∀ φ ∈ Ds, LaxND (φ :: Γ) r := rfl
example (Ds : List PLLFormula) :
    (∀ φ ∈ Ds, insert φ S ⊢ r) = ∀ φ ∈ Ds, SetDeriv (insert φ S) r := rfl
example : (∃ C : PLLFormula, S, C ⊢ C) = ∃ C, SetDeriv (insert C S) C := rfl
example (h : Γ, p ⊢ q) : Γ, p ⊢ q := h
-- `∧` between propositions and between formulas
example (P Q R : Prop) : (P ∧ Q ∨ R) = ((P ∧ Q) ∨ R) := rfl
example : (p ∧ q ∨ r) = .or (.and p q) r := rfl
-- `⊥` is the formula where a formula is meant, Mathlib's `⊥` elsewhere
example : (p = ⊥) = (p = PLLFormula.falsePLL) := rfl
example : ((⊥ : Prop) = False) := rfl
/-- info: p ∧ q : PLLFormula -/
#guard_msgs in #check p ∧ q
-- with the operand types unknown when `∧` is met, it is still `And`
example (s t : List (Finset Nat)) (i : Nat) : Decidable (s[i]!.card ≤ 1 ∧ t[i]!.card ≤ 1) :=
  inferInstance
-- tuples, lists and tactic locations are unaffected
example : (1, 2) = ((1 : Nat), (2 : Nat)) := rfl
example : [p, q].length = 2 := rfl
end pllContexts

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

example (B : Form) : (Γ, A ⊢ B) = Prv (A :: Γ) B := rfl
example (B : Form) : (S, A ⊢ B) = SetPrv (insert A S) B := rfl
/-- info: Γ, A ⊢ A : Prop -/
#guard_msgs in #check Prv (A :: Γ) A
end qll

section qllFormulas
open LaxLogic.QLL
variable (Γ : List Form) (A B : Form) (q : Q)

-- the modalities (`LaxLogic/QLL/Notation.lean`)
example : (◯[∀] A) = Form.circ .all A := rfl
example : (◯[∃] A) = Form.circ .ex A := rfl
example : (◯[q] A) = Form.circ q A := rfl
/-- info: ◯[∀] A ↠ ◯[∃] B : Form -/
#guard_msgs in #check Form.imp (.circ .all A) (.circ .ex B)
/-- info: ◯[q] (A ∧ B) : Form -/
#guard_msgs in #check Form.circ q (.and A B)

-- in sequents, both ways
example : (Γ, ◯[∀] A ⊢ ◯[∃] A ∨ B) = Prv (.circ .all A :: Γ) (.or (.circ .ex A) B) := rfl
/-- info: Γ, ◯[∀] A ⊢ ◯[∃] A ∨ B : Prop -/
#guard_msgs in #check Prv (.circ .all A :: Γ) (.or (.circ .ex A) B)

-- `⊥ ⊤` (`LaxLogic/QLL/NotationOrder.lean`), and Mathlib's elsewhere
example : (Γ ⊢ ⊤ ∧ ⊥) = Prv Γ (.and .top .bot) := rfl
/-- info: Γ ⊢ ⊤ ↠ ⊥ : Prop -/
#guard_msgs in #check Prv Γ (.imp .top .bot)
example : ((⊤ : Prop) = True) := rfl

-- quantifiers over a de Bruijn body
example : (∀' A) = Form.forall_ A := rfl
example : (∃' A) = Form.exists_ A := rfl
/-- info: Γ ⊢ ∀' A → Γ ⊢ ∃' A : Prop -/
#guard_msgs in #check Prv Γ (.forall_ A) → Prv Γ (.exists_ A)

-- named quantifiers: `x : Tm` stands for `.fvar "x"`, closed by the binder
example : (∀ x, Form.pred "P" [x] ↠ Form.pred "P" [x] : Form)
    = .forall_ (.imp (.pred "P" [.bvar 0]) (.pred "P" [.bvar 0])) := rfl
example : (Γ ⊢ ∃ x, Form.pred "P" [x]) = Prv Γ (.exists_ (.pred "P" [.bvar 0])) := rfl
-- a body of constructors prints with names, avoiding the free `x`
/-- info: ∀ x, Form.pred "P" [x] ↠ ◯[∃] (Form.pred "Q" [x]) : Form -/
#guard_msgs in #check Form.forall_ (.imp (.pred "P" [.bvar 0]) (.circ .ex (.pred "Q" [.bvar 0])))
/-- info: ∀ y, ∃ z, Form.pred "R" [y, z, Tm.fvar "x"] : Form -/
#guard_msgs in #check Form.forall_ (.exists_ (.pred "R" [.bvar 1, .bvar 0, .fvar "x"]))

-- Lean's own `∀ ∃ ∧ ∨` in the scope
example : ∀ n, n + 0 = n := fun _ => rfl
example : ∃ n, n = 3 := ⟨3, rfl⟩
example (P Q : Prop) (h : P ∧ Q) : Q ∨ P := .inl h.2
end qllFormulas

section both
open PLLND LaxLogic.QLL
variable (Γ : List PLLFormula) (A : PLLFormula) (Δ : List Form) (B : Form)

-- two developments open: the context type decides
/-- info: Γ ⊢ A : Type -/
#guard_msgs in #check Γ ⊢ A

/-- info: Δ ⊢ B : Prop -/
#guard_msgs in #check Δ ⊢ B

-- formulas of both developments, told apart by type
example (p r : PLLFormula) (C D : Form) :
    (p ↠ r) = PLLFormula.ifThen p r ∧ (C ↠ D) = Form.imp C D := ⟨rfl, rfl⟩
example (C D : Form) : (Δ, C ∧ D ⊢ ◯[∀] B) = Prv (.and C D :: Δ) (.circ .all B) := rfl
/-- info: (A ↠ A, B ↠ B) : PLLFormula × Form -/
#guard_msgs in #check (PLLFormula.ifThen A A, Form.imp B B)

-- Lean's own `⊢` in tactic locations is unaffected
example (a b : Nat) (h : a + 0 = b) : a = b + 0 := by simp at h ⊢; exact h
end both

-- a theorem generic in the calculus
theorem Turnstile.generic_mono {F : Type} (R : List F → F → Prop) (Γ : List F) (A : F)
    (h : Γ ⊢[R] A) : Γ ⊢[R] A := h
