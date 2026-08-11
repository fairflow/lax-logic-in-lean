/-
LJF◯ — the subformula universe (route (B) infrastructure, layer 2a).

The mutual subformula-closure functions over the polarised syntax, their
reflexivity and transitivity, and the closure facts the finite-space
argument needs: every rule of the calculus stays within the universe of
its conclusion.  List-based (no `Finset`), keeping this layer as
audit-clean as the core: zero imports beyond `LJFOCore`.
-/
import LaxLogic.LJFOCore

namespace LJFO

/-! ## Subformula closures

`uPos P` / `uNeg N`: all positive and negative subformulas (both
polarities), self included, as a pair of lists. -/

mutual

def uPosP : Pos → List Pos
  | .atom a => [.atom a]
  | .fls => [.fls]
  | .or P Q => .or P Q :: (uPosP P ++ uPosP Q)
  | .down M => .down M :: uNegP M

def uNegP : Neg → List Pos
  | .up P => uPosP P
  | .imp Q N => uPosP Q ++ uNegP N
  | .and M N => uNegP M ++ uNegP N
  | .circ P => uPosP P

end

mutual

def uPosN : Pos → List Neg
  | .atom _ => []
  | .fls => []
  | .or P Q => uPosN P ++ uPosN Q
  | .down M => uNegN M

def uNegN : Neg → List Neg
  | .up P => .up P :: uPosN P
  | .imp Q N => .imp Q N :: (uPosN Q ++ uNegN N)
  | .and M N => .and M N :: (uNegN M ++ uNegN N)
  | .circ P => .circ P :: uPosN P

end

/-- Positive self-membership. -/
theorem uPosP_self (P : Pos) : P ∈ uPosP P := by
  cases P <;> simp [uPosP]

/-- Negative self-membership. -/
theorem uNegN_self (N : Neg) : N ∈ uNegN N := by
  cases N <;> simp [uNegN]

/-! ## The one-step closure facts used by the rule-stability argument -/

theorem uPos_or_left {P Q : Pos} : ∀ X ∈ uPosP P, X ∈ uPosP (.or P Q) := by
  intro X hX; simp [uPosP]; right; left; exact hX

theorem uPos_or_right {P Q : Pos} : ∀ X ∈ uPosP Q, X ∈ uPosP (.or P Q) := by
  intro X hX; simp [uPosP]; right; right; exact hX

theorem uPos_down {M : Neg} : ∀ X ∈ uNegP M, X ∈ uPosP (.down M) := by
  intro X hX; simp [uPosP]; right; exact hX

theorem uNeg_down {M : Neg} : ∀ X ∈ uNegN M, X ∈ uPosN (.down M) := by
  intro X hX; simpa [uPosN] using hX

theorem uNeg_up {P : Pos} : ∀ X ∈ uPosN P, X ∈ uNegN (.up P) := by
  intro X hX; simp [uNegN]; right; exact hX

theorem uPos_up {P : Pos} : ∀ X ∈ uPosP P, X ∈ uNegP (.up P) := by
  intro X hX; simpa [uNegP] using hX

theorem uNeg_imp_ant {Q : Pos} {N : Neg} : ∀ X ∈ uPosN Q, X ∈ uNegN (.imp Q N) := by
  intro X hX; simp [uNegN]; right; left; exact hX

theorem uNeg_imp_body {Q : Pos} {N : Neg} : ∀ X ∈ uNegN N, X ∈ uNegN (.imp Q N) := by
  intro X hX; simp [uNegN]; right; right; exact hX

theorem uPos_imp_ant {Q : Pos} {N : Neg} : ∀ X ∈ uPosP Q, X ∈ uNegP (.imp Q N) := by
  intro X hX; simp [uNegP]; left; exact hX

theorem uPos_imp_body {Q : Pos} {N : Neg} : ∀ X ∈ uNegP N, X ∈ uNegP (.imp Q N) := by
  intro X hX; simp [uNegP]; right; exact hX

theorem uNeg_and_left {M N : Neg} : ∀ X ∈ uNegN M, X ∈ uNegN (.and M N) := by
  intro X hX; simp [uNegN]; right; left; exact hX

theorem uNeg_and_right {M N : Neg} : ∀ X ∈ uNegN N, X ∈ uNegN (.and M N) := by
  intro X hX; simp [uNegN]; right; right; exact hX

theorem uNeg_circ {P : Pos} : ∀ X ∈ uPosN P, X ∈ uNegN (.circ P) := by
  intro X hX; simp [uNegN]; right; exact hX

theorem uPos_circ {P : Pos} : ∀ X ∈ uPosP P, X ∈ uNegP (.circ P) := by
  intro X hX; simpa [uNegP] using hX

/-! ## Universes of contexts and sequents -/

def uCtxP (Γ : List Neg) : List Pos := Γ.flatMap uNegP
def uCtxN (Γ : List Neg) : List Neg := Γ.flatMap uNegN

theorem uCtxN_mem {Γ : List Neg} {N X : Neg} (hN : N ∈ Γ) (hX : X ∈ uNegN N) :
    X ∈ uCtxN Γ := List.mem_flatMap.mpr ⟨N, hN, hX⟩

theorem uCtxP_mem {Γ : List Neg} {N : Neg} {X : Pos} (hN : N ∈ Γ) (hX : X ∈ uNegP N) :
    X ∈ uCtxP Γ := List.mem_flatMap.mpr ⟨N, hN, hX⟩

theorem uCtxN_self {Γ : List Neg} : ∀ N ∈ Γ, N ∈ uCtxN Γ :=
  fun N hN => uCtxN_mem hN (uNegN_self N)

/-- A universe (a positive and a negative list) closed under the
subformula step: this is the invariant the rule-stability lemmas of
layer 2b establish for the calculus. -/
structure UClosed (UP : List Pos) (UN : List Neg) : Prop where
  posDown : ∀ M, Pos.down M ∈ UP → M ∈ UN
  posOr1  : ∀ P Q, Pos.or P Q ∈ UP → P ∈ UP
  posOr2  : ∀ P Q, Pos.or P Q ∈ UP → Q ∈ UP
  negUp   : ∀ P, Neg.up P ∈ UN → P ∈ UP
  negImp1 : ∀ Q N, Neg.imp Q N ∈ UN → Q ∈ UP
  negImp2 : ∀ Q N, Neg.imp Q N ∈ UN → N ∈ UN
  negAnd1 : ∀ M N, Neg.and M N ∈ UN → M ∈ UN
  negAnd2 : ∀ M N, Neg.and M N ∈ UN → N ∈ UN
  negCirc : ∀ P, Neg.circ P ∈ UN → P ∈ UP

end LJFO
