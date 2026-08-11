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

namespace LJFO

/-! ## Layer 2b: closure transitivity — subformulas of subformulas -/

mutual

theorem uPP : ∀ (P : Pos) {X : Pos}, X ∈ uPosP P → ∀ {Y : Pos}, Y ∈ uPosP X → Y ∈ uPosP P
  | .atom _, _, hX => by simp [uPosP] at hX; subst hX; exact fun hY => hY
  | .fls, _, hX => by simp [uPosP] at hX; subst hX; exact fun hY => hY
  | .or P Q, X, hX => by
      simp only [uPosP, List.mem_cons, List.mem_append] at hX
      rcases hX with rfl | hX | hX
      · exact fun hY => hY
      · exact fun hY => uPos_or_left _ (uPP P hX hY)
      · exact fun hY => uPos_or_right _ (uPP Q hX hY)
  | .down M, X, hX => by
      simp only [uPosP, List.mem_cons] at hX
      rcases hX with rfl | hX
      · exact fun hY => hY
      · exact fun hY => uPos_down _ (uNP M hX hY)

theorem uNP : ∀ (N : Neg) {X : Pos}, X ∈ uNegP N → ∀ {Y : Pos}, Y ∈ uPosP X → Y ∈ uNegP N
  | .up P, X, hX => by
      simp only [uNegP] at hX ⊢; exact fun hY => uPP P hX hY
  | .imp Q N, X, hX => by
      simp only [uNegP, List.mem_append] at hX ⊢
      rcases hX with hX | hX
      · exact fun hY => .inl (uPP Q hX hY)
      · exact fun hY => .inr (uNP N hX hY)
  | .and M N, X, hX => by
      simp only [uNegP, List.mem_append] at hX ⊢
      rcases hX with hX | hX
      · exact fun hY => .inl (uNP M hX hY)
      · exact fun hY => .inr (uNP N hX hY)
  | .circ P, X, hX => by
      simp only [uNegP] at hX ⊢; exact fun hY => uPP P hX hY

theorem uPN : ∀ (P : Pos) {X : Pos}, X ∈ uPosP P → ∀ {Y : Neg}, Y ∈ uPosN X → Y ∈ uPosN P
  | .atom _, _, hX => by simp [uPosP] at hX; subst hX; exact fun hY => hY
  | .fls, _, hX => by simp [uPosP] at hX; subst hX; exact fun hY => hY
  | .or P Q, X, hX => by
      simp only [uPosP, List.mem_cons, List.mem_append] at hX
      rcases hX with rfl | hX | hX
      · exact fun hY => hY
      · exact fun hY => by
          simp only [uPosN, List.mem_append]; exact .inl (uPN P hX hY)
      · exact fun hY => by
          simp only [uPosN, List.mem_append]; exact .inr (uPN Q hX hY)
  | .down M, X, hX => by
      simp only [uPosP, List.mem_cons] at hX
      rcases hX with rfl | hX
      · exact fun hY => hY
      · exact fun hY => uNeg_down _ (uNN M hX hY)

theorem uNN : ∀ (N : Neg) {X : Pos}, X ∈ uNegP N → ∀ {Y : Neg}, Y ∈ uPosN X → Y ∈ uNegN N
  | .up P, X, hX => by
      simp only [uNegP] at hX; exact fun hY => uNeg_up _ (uPN P hX hY)
  | .imp Q N, X, hX => by
      simp only [uNegP, List.mem_append] at hX
      rcases hX with hX | hX
      · exact fun hY => uNeg_imp_ant _ (uPN Q hX hY)
      · exact fun hY => uNeg_imp_body _ (uNN N hX hY)
  | .and M N, X, hX => by
      simp only [uNegP, List.mem_append] at hX
      rcases hX with hX | hX
      · exact fun hY => uNeg_and_left _ (uNN M hX hY)
      · exact fun hY => uNeg_and_right _ (uNN N hX hY)
  | .circ P, X, hX => by
      simp only [uNegP] at hX; exact fun hY => uNeg_circ _ (uPN P hX hY)

theorem uPPn : ∀ (P : Pos) {X : Neg}, X ∈ uPosN P → ∀ {Y : Pos}, Y ∈ uNegP X → Y ∈ uPosP P
  | .atom _, _, hX => by simp [uPosN] at hX
  | .fls, _, hX => by simp [uPosN] at hX
  | .or P Q, X, hX => by
      simp only [uPosN, List.mem_append] at hX
      rcases hX with hX | hX
      · exact fun hY => uPos_or_left _ (uPPn P hX hY)
      · exact fun hY => uPos_or_right _ (uPPn Q hX hY)
  | .down M, X, hX => by
      simp only [uPosN] at hX
      exact fun hY => uPos_down _ (uNPn M hX hY)

theorem uNPn : ∀ (N : Neg) {X : Neg}, X ∈ uNegN N → ∀ {Y : Pos}, Y ∈ uNegP X → Y ∈ uNegP N
  | .up P, X, hX => by
      simp only [uNegN, List.mem_cons] at hX
      rcases hX with rfl | hX
      · exact fun hY => hY
      · exact fun hY => uPos_up _ (uPPn P hX hY)
  | .imp Q N, X, hX => by
      simp only [uNegN, List.mem_cons, List.mem_append] at hX
      rcases hX with rfl | hX | hX
      · exact fun hY => hY
      · exact fun hY => uPos_imp_ant _ (uPPn Q hX hY)
      · exact fun hY => uPos_imp_body _ (uNPn N hX hY)
  | .and M N, X, hX => by
      simp only [uNegN, List.mem_cons, List.mem_append] at hX
      rcases hX with rfl | hX | hX
      · exact fun hY => hY
      · exact fun hY => by
          simp only [uNegP, List.mem_append]; exact .inl (uNPn M hX hY)
      · exact fun hY => by
          simp only [uNegP, List.mem_append]; exact .inr (uNPn N hX hY)
  | .circ P, X, hX => by
      simp only [uNegN, List.mem_cons] at hX
      rcases hX with rfl | hX
      · exact fun hY => hY
      · exact fun hY => uPos_circ _ (uPPn P hX hY)

theorem uPNn : ∀ (P : Pos) {X : Neg}, X ∈ uPosN P → ∀ {Y : Neg}, Y ∈ uNegN X → Y ∈ uPosN P
  | .atom _, _, hX => by simp [uPosN] at hX
  | .fls, _, hX => by simp [uPosN] at hX
  | .or P Q, X, hX => by
      simp only [uPosN, List.mem_append] at hX ⊢
      rcases hX with hX | hX
      · exact fun hY => .inl (uPNn P hX hY)
      · exact fun hY => .inr (uPNn Q hX hY)
  | .down M, X, hX => by
      simp only [uPosN] at hX ⊢
      exact fun hY => uNNn M hX hY

theorem uNNn : ∀ (N : Neg) {X : Neg}, X ∈ uNegN N → ∀ {Y : Neg}, Y ∈ uNegN X → Y ∈ uNegN N
  | .up P, X, hX => by
      simp only [uNegN, List.mem_cons] at hX
      rcases hX with rfl | hX
      · exact fun hY => hY
      · exact fun hY => uNeg_up _ (uPNn P hX hY)
  | .imp Q N, X, hX => by
      simp only [uNegN, List.mem_cons, List.mem_append] at hX
      rcases hX with rfl | hX | hX
      · exact fun hY => hY
      · exact fun hY => uNeg_imp_ant _ (uPNn Q hX hY)
      · exact fun hY => uNeg_imp_body _ (uNNn N hX hY)
  | .and M N, X, hX => by
      simp only [uNegN, List.mem_cons, List.mem_append] at hX
      rcases hX with rfl | hX | hX
      · exact fun hY => hY
      · exact fun hY => uNeg_and_left _ (uNNn M hX hY)
      · exact fun hY => uNeg_and_right _ (uNNn N hX hY)
  | .circ P, X, hX => by
      simp only [uNegN, List.mem_cons] at hX
      rcases hX with rfl | hX
      · exact fun hY => hY
      · exact fun hY => uNeg_circ _ (uPNn P hX hY)

end

/-- The context universe is closed: the invariant the finite-space
argument runs on. -/
theorem uClosed_ctx (Γ : List Neg) : UClosed (uCtxP Γ) (uCtxN Γ) := by
  constructor
  · intro M h
    obtain ⟨N, hN, hX⟩ := List.mem_flatMap.mp h
    exact uCtxN_mem hN (uNN N hX (by simp [uPosN, uNegN_self M]))
  · intro P Q h
    obtain ⟨N, hN, hX⟩ := List.mem_flatMap.mp h
    exact uCtxP_mem hN (uNP N hX (uPos_or_left _ (uPosP_self P)))
  · intro P Q h
    obtain ⟨N, hN, hX⟩ := List.mem_flatMap.mp h
    exact uCtxP_mem hN (uNP N hX (uPos_or_right _ (uPosP_self Q)))
  · intro P h
    obtain ⟨N, hN, hX⟩ := List.mem_flatMap.mp h
    exact uCtxP_mem hN (uNPn N hX (uPos_up _ (uPosP_self P)))
  · intro Q M h
    obtain ⟨N, hN, hX⟩ := List.mem_flatMap.mp h
    exact uCtxP_mem hN (uNPn N hX (uPos_imp_ant _ (uPosP_self Q)))
  · intro Q M h
    obtain ⟨N, hN, hX⟩ := List.mem_flatMap.mp h
    exact uCtxN_mem hN (uNNn N hX (uNeg_imp_body _ (uNegN_self M)))
  · intro M M' h
    obtain ⟨N, hN, hX⟩ := List.mem_flatMap.mp h
    exact uCtxN_mem hN (uNNn N hX (uNeg_and_left _ (uNegN_self M)))
  · intro M M' h
    obtain ⟨N, hN, hX⟩ := List.mem_flatMap.mp h
    exact uCtxN_mem hN (uNNn N hX (uNeg_and_right _ (uNegN_self M')))
  · intro P h
    obtain ⟨N, hN, hX⟩ := List.mem_flatMap.mp h
    exact uCtxP_mem hN (uNPn N hX (uPos_circ _ (uPosP_self P)))

end LJFO
