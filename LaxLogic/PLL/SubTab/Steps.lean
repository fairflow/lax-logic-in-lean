import LaxLogic.PLL.SubTab.Sound

/-!
# The subframe tableau: universe, measure, steps (for completeness)

2026-10-15.  The ingredients of the completeness proof
(`SubTab/Complete.lean`): the subformula universe and its closure, the
measure `meas` that every rule decreases (stated once, here), and the three
step functions of the search with their specifications: closing
(`closeCert`), local rules (`findStep`) and demands (`demands`).
-/

open PLLFormula

namespace PLLND
namespace SubTab

/-! ## The universe -/

/-- The subformulas of a formula, as a list (with repetitions). -/
def subs : PLLFormula → List PLLFormula
  | .prop a => [.prop a]
  | .falsePLL => [.falsePLL]
  | .and A B => .and A B :: (subs A ++ subs B)
  | .or A B => .or A B :: (subs A ++ subs B)
  | .ifThen A B => .ifThen A B :: (subs A ++ subs B)
  | .somehow A => .somehow A :: subs A

theorem self_mem_subs : ∀ φ : PLLFormula, φ ∈ subs φ
  | .prop _ | .falsePLL | .and _ _ | .or _ _ | .ifThen _ _ | .somehow _ => List.mem_cons_self

theorem subs_sub : ∀ {φ X : PLLFormula}, X ∈ subs φ → ∀ Y ∈ subs X, Y ∈ subs φ
  | .prop _, X, hX, Y, hY => by
      simp only [subs, List.mem_singleton] at hX; subst hX; exact hY
  | .falsePLL, X, hX, Y, hY => by
      simp only [subs, List.mem_singleton] at hX; subst hX; exact hY
  | .and A B, X, hX, Y, hY => by
      rcases List.mem_cons.mp hX with e | hX
      · subst e; exact hY
      · rcases List.mem_append.mp hX with h | h
        · exact List.mem_cons_of_mem _ (List.mem_append_left _ (subs_sub h Y hY))
        · exact List.mem_cons_of_mem _ (List.mem_append_right _ (subs_sub h Y hY))
  | .or A B, X, hX, Y, hY => by
      rcases List.mem_cons.mp hX with e | hX
      · subst e; exact hY
      · rcases List.mem_append.mp hX with h | h
        · exact List.mem_cons_of_mem _ (List.mem_append_left _ (subs_sub h Y hY))
        · exact List.mem_cons_of_mem _ (List.mem_append_right _ (subs_sub h Y hY))
  | .ifThen A B, X, hX, Y, hY => by
      rcases List.mem_cons.mp hX with e | hX
      · subst e; exact hY
      · rcases List.mem_append.mp hX with h | h
        · exact List.mem_cons_of_mem _ (List.mem_append_left _ (subs_sub h Y hY))
        · exact List.mem_cons_of_mem _ (List.mem_append_right _ (subs_sub h Y hY))
  | .somehow A, X, hX, Y, hY => by
      rcases List.mem_cons.mp hX with e | hX
      · subst e; exact hY
      · exact List.mem_cons_of_mem _ (subs_sub hX Y hY)

/-- A universe closed under immediate subformulas. -/
structure Closed (U : List PLLFormula) : Prop where
  and : ∀ A B, PLLFormula.and A B ∈ U → A ∈ U ∧ B ∈ U
  or : ∀ A B, PLLFormula.or A B ∈ U → A ∈ U ∧ B ∈ U
  imp : ∀ A B, PLLFormula.ifThen A B ∈ U → A ∈ U ∧ B ∈ U
  box : ∀ A, PLLFormula.somehow A ∈ U → A ∈ U

theorem subs_closed (φ : PLLFormula) : Closed (subs φ) where
  and A B h := ⟨subs_sub h A (List.mem_cons_of_mem _ (List.mem_append_left _ (self_mem_subs A))),
    subs_sub h B (List.mem_cons_of_mem _ (List.mem_append_right _ (self_mem_subs B)))⟩
  or A B h := ⟨subs_sub h A (List.mem_cons_of_mem _ (List.mem_append_left _ (self_mem_subs A))),
    subs_sub h B (List.mem_cons_of_mem _ (List.mem_append_right _ (self_mem_subs B)))⟩
  imp A B h := ⟨subs_sub h A (List.mem_cons_of_mem _ (List.mem_append_left _ (self_mem_subs A))),
    subs_sub h B (List.mem_cons_of_mem _ (List.mem_append_right _ (self_mem_subs B)))⟩
  box A h := subs_sub h A (List.mem_cons_of_mem _ (self_mem_subs A))

/-! ## The measure (stated here and nowhere later) -/

/-- The members of `U` not yet in `Γ`. -/
def cnt (U Γ : List PLLFormula) : Nat := U.countP fun x => !decide (x ∈ Γ)

theorem cnt_le (U Γ : List PLLFormula) : cnt U Γ ≤ U.length := List.countP_le_length

theorem countP_lt {p q : PLLFormula → Bool} :
    ∀ {U : List PLLFormula}, (∀ x ∈ U, p x = true → q x = true) →
      (∃ x ∈ U, q x = true ∧ p x = false) → U.countP p < U.countP q
  | [], _, ⟨_, hx, _⟩ => absurd hx List.not_mem_nil
  | y :: U, hpq, ⟨x, hx, hqx, hpx⟩ => by
      rw [List.countP_cons, List.countP_cons]
      have hU : ∀ z ∈ U, p z = true → q z = true := fun z hz => hpq z (List.mem_cons_of_mem _ hz)
      have hle : U.countP p ≤ U.countP q := List.countP_mono_left hU
      have hy : p y = true → q y = true := hpq y List.mem_cons_self
      rcases List.mem_cons.mp hx with e | hx
      · subst e
        rw [hpx, hqx]
        exact Nat.lt_succ_of_le hle
      · have hlt := countP_lt hU ⟨x, hx, hqx, hpx⟩
        have key : (if p y = true then 1 else 0) ≤ (if q y = true then 1 else 0) := by
          cases hp : p y
          · exact Nat.zero_le _
          · rw [hy hp]
        omega

/-- Adding a member of `U` that is new to `Γ` lowers `cnt`. -/
theorem cnt_lt {U Γ Γ' : List PLLFormula} {A : PLLFormula} (hA : A ∈ U) (hn : A ∉ Γ)
    (hsub : Γ ⊆ Γ') (hA' : A ∈ Γ') : cnt U Γ' < cnt U Γ :=
  countP_lt (fun x _ h => by
      simp only [Bool.not_eq_true', decide_eq_false_iff_not] at h ⊢
      exact fun hx => h (hsub hx))
    ⟨A, hA, by simp [hn], by simp [hA']⟩

theorem cnt_mono {U Γ Γ' : List PLLFormula} (hsub : Γ ⊆ Γ') : cnt U Γ' ≤ cnt U Γ :=
  List.countP_mono_left fun x _ h => by
    simp only [Bool.not_eq_true', decide_eq_false_iff_not] at h ⊢
    exact fun hx => h (hsub hx)

/-- **The measure.**  A world contributes `2·cnt U Γ`, plus one when it is not
an S-point; inside a world the signed formulas still to come count. -/
def meas (U : List PLLFormula) (isS : Bool) (Γ Δ : List PLLFormula) : Nat :=
  (2 * cnt U Γ + (if isS then 0 else 1)) * (2 * U.length + 1) + (cnt U Γ + cnt U Δ)

theorem lex_lt {x x' y y' K : Nat} (hx : x < x') (hy : y < K) : x * K + y < x' * K + y' := by
  have : x * K + y < (x + 1) * K := by rw [Nat.succ_mul]; omega
  have : (x + 1) * K ≤ x' * K := Nat.mul_le_mul_right K hx
  omega

theorem small (U Γ Δ : List PLLFormula) : cnt U Γ + cnt U Δ < 2 * U.length + 1 := by
  have := cnt_le U Γ; have := cnt_le U Δ; omega

/-- A local rule adding a new formula to `Γ` lowers the measure. -/
theorem meas_ant {U Γ Γ' Δ : List PLLFormula} {A : PLLFormula} (b : Bool) (hA : A ∈ U)
    (hn : A ∉ Γ) (hsub : Γ ⊆ Γ') (hA' : A ∈ Γ') : meas U b Γ' Δ < meas U b Γ Δ := by
  have h := cnt_lt hA hn hsub hA'
  unfold meas
  apply lex_lt _ (small U Γ' Δ)
  omega

/-- A local rule adding a new formula to `Δ` lowers the measure. -/
theorem meas_suc {U Γ Δ Δ' : List PLLFormula} {A : PLLFormula} (b : Bool) (hA : A ∈ U)
    (hn : A ∉ Δ) (hsub : Δ ⊆ Δ') (hA' : A ∈ Δ') : meas U b Γ Δ' < meas U b Γ Δ := by
  have h := cnt_lt hA hn hsub hA'
  unfold meas
  omega

/-- A new world for `A ↠ B` (with `A` new) lowers the measure. -/
theorem meas_impR {U Γ Δ Δ' : List PLLFormula} {A : PLLFormula} (b : Bool) (hA : A ∈ U)
    (hn : A ∉ Γ) : meas U false (Γ ++ [A]) Δ' < meas U b Γ Δ := by
  have h := cnt_lt hA hn (List.subset_append_left Γ [A]) (List.mem_append_right Γ List.mem_cons_self)
  unfold meas
  apply lex_lt _ (small U (Γ ++ [A]) Δ')
  show 2 * cnt U (Γ ++ [A]) + 1 < _
  omega

/-- A new S-point below a world outside S lowers the measure. -/
theorem meas_boxR {U Γ Δ Δ' : List PLLFormula} : meas U true Γ Δ' < meas U false Γ Δ := by
  unfold meas
  apply lex_lt _ (small U Γ Δ')
  exact Nat.lt_succ_self _

/-! ## Closing -/

/-- A closing rule, if one applies. -/
def closeCert (Γ Δ : List PLLFormula) : Option TCert :=
  if decide (PLLFormula.falsePLL ∈ Γ) then some .bot
  else (Γ.find? fun A => decide (A ∈ Δ)).map .ax

theorem closeCert_some {b : Bool} {Γ Δ : List PLLFormula} {c : TCert}
    (h : closeCert Γ Δ = some c) : check ⟨b, Γ, Δ⟩ c = true := by
  unfold closeCert at h
  split at h
  · cases h; simp only [check, mem]; exact ‹_›
  · obtain ⟨A, hA, rfl⟩ := Option.map_eq_some_iff.mp h
    have h1 := List.find?_some hA
    have h2 := List.mem_of_find?_eq_some hA
    simp only [check, mem, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨h2, of_decide_eq_true h1⟩

theorem closeCert_none {Γ Δ : List PLLFormula} (h : closeCert Γ Δ = none) :
    PLLFormula.falsePLL ∉ Γ ∧ ∀ A ∈ Γ, A ∉ Δ := by
  unfold closeCert at h
  split at h
  · cases h
  · refine ⟨fun hb => ‹¬ _› (decide_eq_true hb), fun A hA hAD => ?_⟩
    have := List.find?_eq_none.mp (Option.map_eq_none_iff.mp h) A hA
    exact this (decide_eq_true hAD)

/-! ## Local rules -/

inductive Step where
  | andL (A B : PLLFormula) | orL (A B : PLLFormula) | impL (A B : PLLFormula)
  | boxL (A : PLLFormula)
  | andR (A B : PLLFormula) | orR (A B : PLLFormula) | impLoc (A B : PLLFormula)
  | boxLoc (A : PLLFormula)

def stepL (isS : Bool) (Γ Δ : List PLLFormula) : PLLFormula → Option Step
  | .and A B => if decide (A ∈ Γ) && decide (B ∈ Γ) then none else some (.andL A B)
  | .or A B => if decide (A ∈ Γ) || decide (B ∈ Γ) then none else some (.orL A B)
  | .ifThen A B => if decide (A ∈ Δ) || decide (B ∈ Γ) then none else some (.impL A B)
  | .somehow A => if isS && !decide (A ∈ Γ) then some (.boxL A) else none
  | _ => none

def stepR (isS : Bool) (Γ Δ : List PLLFormula) : PLLFormula → Option Step
  | .and A B => if decide (A ∈ Δ) || decide (B ∈ Δ) then none else some (.andR A B)
  | .or A B => if decide (A ∈ Δ) && decide (B ∈ Δ) then none else some (.orR A B)
  | .ifThen A B => if decide (A ∈ Γ) && !decide (B ∈ Δ) then some (.impLoc A B) else none
  | .somehow A => if isS && !decide (A ∈ Δ) then some (.boxLoc A) else none
  | _ => none

/-- The first applicable local rule, if any. -/
def findStep (isS : Bool) (Γ Δ : List PLLFormula) : Option Step :=
  (Γ.findSome? (stepL isS Γ Δ)).orElse fun _ => Δ.findSome? (stepR isS Γ Δ)

/-- What an applicable step guarantees. -/
def Step.pre (isS : Bool) (Γ Δ : List PLLFormula) : Step → Prop
  | .andL A B => PLLFormula.and A B ∈ Γ ∧ ¬ (A ∈ Γ ∧ B ∈ Γ)
  | .orL A B => PLLFormula.or A B ∈ Γ ∧ A ∉ Γ ∧ B ∉ Γ
  | .impL A B => PLLFormula.ifThen A B ∈ Γ ∧ A ∉ Δ ∧ B ∉ Γ
  | .boxL A => isS = true ∧ PLLFormula.somehow A ∈ Γ ∧ A ∉ Γ
  | .andR A B => PLLFormula.and A B ∈ Δ ∧ A ∉ Δ ∧ B ∉ Δ
  | .orR A B => PLLFormula.or A B ∈ Δ ∧ ¬ (A ∈ Δ ∧ B ∈ Δ)
  | .impLoc A B => PLLFormula.ifThen A B ∈ Δ ∧ A ∈ Γ ∧ B ∉ Δ
  | .boxLoc A => isS = true ∧ PLLFormula.somehow A ∈ Δ ∧ A ∉ Δ

theorem stepL_pre {isS : Bool} {Γ Δ : List PLLFormula} {X : PLLFormula} {st : Step}
    (hX : X ∈ Γ) (h : stepL isS Γ Δ X = some st) : st.pre isS Γ Δ := by
  cases X with
  | and A B =>
    simp only [stepL] at h; split at h
    · cases h
    · cases h; refine ⟨hX, fun ⟨a, b⟩ => ‹¬ _› ?_⟩; simp [a, b]
  | or A B =>
    simp only [stepL] at h; split at h
    · cases h
    · cases h; refine ⟨hX, fun a => ‹¬ _› ?_, fun b => ‹¬ _› ?_⟩ <;> simp [*]
  | ifThen A B =>
    simp only [stepL] at h; split at h
    · cases h
    · cases h; refine ⟨hX, fun a => ‹¬ _› ?_, fun b => ‹¬ _› ?_⟩ <;> simp [*]
  | somehow A =>
    simp only [stepL] at h; split at h
    · cases h
      rename_i hc
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hc
      exact ⟨hc.1, hX, hc.2⟩
    · cases h
  | prop _ => simp [stepL] at h
  | falsePLL => simp [stepL] at h

theorem stepR_pre {isS : Bool} {Γ Δ : List PLLFormula} {X : PLLFormula} {st : Step}
    (hX : X ∈ Δ) (h : stepR isS Γ Δ X = some st) : st.pre isS Γ Δ := by
  cases X with
  | and A B =>
    simp only [stepR] at h; split at h
    · cases h
    · cases h; refine ⟨hX, fun a => ‹¬ _› ?_, fun b => ‹¬ _› ?_⟩ <;> simp [*]
  | or A B =>
    simp only [stepR] at h; split at h
    · cases h
    · cases h; refine ⟨hX, fun ⟨a, b⟩ => ‹¬ _› ?_⟩; simp [a, b]
  | ifThen A B =>
    simp only [stepR] at h; split at h
    · cases h
      rename_i hc
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
        decide_eq_false_iff_not] at hc
      exact ⟨hX, hc.1, hc.2⟩
    · cases h
  | somehow A =>
    simp only [stepR] at h; split at h
    · cases h
      rename_i hc
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hc
      exact ⟨hc.1, hX, hc.2⟩
    · cases h
  | prop _ => simp [stepR] at h
  | falsePLL => simp [stepR] at h

theorem findStep_some {isS : Bool} {Γ Δ : List PLLFormula} {st : Step}
    (h : findStep isS Γ Δ = some st) : st.pre isS Γ Δ := by
  unfold findStep at h
  cases hL : Γ.findSome? (stepL isS Γ Δ) with
  | some st' =>
    rw [hL] at h; cases h
    obtain ⟨X, hX, hs⟩ := List.exists_of_findSome?_eq_some hL
    exact stepL_pre hX hs
  | none =>
    rw [hL] at h
    obtain ⟨X, hX, hs⟩ := List.exists_of_findSome?_eq_some h
    exact stepR_pre hX hs

/-- The saturation conditions of a world. -/
structure Saturated (isS : Bool) (Γ Δ : List PLLFormula) : Prop where
  andL : ∀ A B, PLLFormula.and A B ∈ Γ → A ∈ Γ ∧ B ∈ Γ
  orL : ∀ A B, PLLFormula.or A B ∈ Γ → A ∈ Γ ∨ B ∈ Γ
  impL : ∀ A B, PLLFormula.ifThen A B ∈ Γ → A ∈ Δ ∨ B ∈ Γ
  boxL : ∀ A, isS = true → PLLFormula.somehow A ∈ Γ → A ∈ Γ
  andR : ∀ A B, PLLFormula.and A B ∈ Δ → A ∈ Δ ∨ B ∈ Δ
  orR : ∀ A B, PLLFormula.or A B ∈ Δ → A ∈ Δ ∧ B ∈ Δ
  impLoc : ∀ A B, PLLFormula.ifThen A B ∈ Δ → A ∈ Γ → B ∈ Δ
  boxLoc : ∀ A, isS = true → PLLFormula.somehow A ∈ Δ → A ∈ Δ

theorem findStep_none {isS : Bool} {Γ Δ : List PLLFormula} (h : findStep isS Γ Δ = none) :
    Saturated isS Γ Δ := by
  unfold findStep at h
  cases hL : Γ.findSome? (stepL isS Γ Δ) with
  | some _ => rw [hL] at h; cases h
  | none =>
    rw [hL] at h
    have hl := List.findSome?_eq_none_iff.mp hL
    have hr := List.findSome?_eq_none_iff.mp h
    constructor
    · intro A B hm
      have := hl _ hm; simp only [stepL] at this; split at this
      · rename_i hc; simp only [Bool.and_eq_true, decide_eq_true_eq] at hc; exact hc
      · cases this
    · intro A B hm
      have := hl _ hm; simp only [stepL] at this; split at this
      · rename_i hc; simp only [Bool.or_eq_true, decide_eq_true_eq] at hc; exact hc
      · cases this
    · intro A B hm
      have := hl _ hm; simp only [stepL] at this; split at this
      · rename_i hc; simp only [Bool.or_eq_true, decide_eq_true_eq] at hc; exact hc
      · cases this
    · intro A hS hm
      have := hl _ hm; simp only [stepL] at this; split at this
      · cases this
      · rename_i hc
        exact Decidable.byContradiction fun hn => hc (by simp [hS, hn])
    · intro A B hm
      have := hr _ hm; simp only [stepR] at this; split at this
      · rename_i hc; simp only [Bool.or_eq_true, decide_eq_true_eq] at hc; exact hc
      · cases this
    · intro A B hm
      have := hr _ hm; simp only [stepR] at this; split at this
      · rename_i hc; simp only [Bool.and_eq_true, decide_eq_true_eq] at hc; exact hc
      · cases this
    · intro A B hm hA
      have := hr _ hm; simp only [stepR] at this; split at this
      · cases this
      · rename_i hc
        exact Decidable.byContradiction fun hn => hc (by simp [hA, hn])
    · intro A hS hm
      have := hr _ hm; simp only [stepR] at this; split at this
      · cases this
      · rename_i hc
        exact Decidable.byContradiction fun hn => hc (by simp [hS, hn])

/-! ## Demands -/

inductive Dem where
  | imp (A B : PLLFormula) | box (A : PLLFormula)

def demOf (isS : Bool) (Γ : List PLLFormula) : PLLFormula → Option Dem
  | .ifThen A B => if decide (A ∈ Γ) then none else some (.imp A B)
  | .somehow A => if isS then none else some (.box A)
  | _ => none

/-- The demands of a saturated world: one new world each. -/
def demands (isS : Bool) (Γ Δ : List PLLFormula) : List Dem := Δ.filterMap (demOf isS Γ)

/-- The sequent of the world a demand creates. -/
def Dem.child (Γ : List PLLFormula) : Dem → SSeq
  | .imp A B => ⟨false, Γ ++ [A], [B]⟩
  | .box A => ⟨true, Γ, [A]⟩

/-- The rule that closes a world through a closed demand. -/
def Dem.cert : Dem → TCert → TCert
  | .imp A B, c => .impR A B c
  | .box A, c => .boxR A c

theorem mem_demands {isS : Bool} {Γ Δ : List PLLFormula} {d : Dem}
    (h : d ∈ demands isS Γ Δ) :
    match d with
    | .imp A B => PLLFormula.ifThen A B ∈ Δ ∧ A ∉ Γ
    | .box A => isS = false ∧ PLLFormula.somehow A ∈ Δ := by
  obtain ⟨X, hX, hd⟩ := List.mem_filterMap.mp h
  cases X with
  | ifThen A B =>
    simp only [demOf] at hd; split at hd
    · cases hd
    · cases hd; exact ⟨hX, fun hA => ‹¬ _› (decide_eq_true hA)⟩
  | somehow A =>
    simp only [demOf] at hd; split at hd
    · cases hd
    · cases hd; exact ⟨Bool.eq_false_iff.mpr ‹_›, hX⟩
  | prop _ => simp [demOf] at hd
  | falsePLL => simp [demOf] at hd
  | and _ _ => simp [demOf] at hd
  | or _ _ => simp [demOf] at hd

theorem imp_mem_demands {isS : Bool} {Γ Δ : List PLLFormula} {A B : PLLFormula}
    (h : PLLFormula.ifThen A B ∈ Δ) (hA : A ∉ Γ) : Dem.imp A B ∈ demands isS Γ Δ :=
  List.mem_filterMap.mpr ⟨_, h, by simp [demOf, hA]⟩

theorem box_mem_demands {Γ Δ : List PLLFormula} {A : PLLFormula}
    (h : PLLFormula.somehow A ∈ Δ) : Dem.box A ∈ demands false Γ Δ :=
  List.mem_filterMap.mpr ⟨_, h, by simp [demOf]⟩

theorem demand_check {isS : Bool} {Γ Δ : List PLLFormula} {d : Dem} {c : TCert}
    (hd : d ∈ demands isS Γ Δ) (h : check (d.child Γ) c = true) :
    check ⟨isS, Γ, Δ⟩ (d.cert c) = true := by
  have := mem_demands hd
  cases d with
  | imp A B =>
    simp only [Dem.cert, check, mem, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨this.1, h⟩
  | box A =>
    simp only [Dem.cert, check, mem, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨this.2, h⟩

end SubTab
end PLLND

#axioms_within PLLND.SubTab.meas_ant [propext, Quot.sound]
#axioms_within PLLND.SubTab.meas_suc [propext, Quot.sound]
#axioms_within PLLND.SubTab.meas_impR [propext, Quot.sound]
#axioms_within PLLND.SubTab.meas_boxR [propext, Quot.sound]
#axioms_within PLLND.SubTab.closeCert_some [propext, Quot.sound]
#axioms_within PLLND.SubTab.closeCert_none [propext, Quot.sound]
#axioms_within PLLND.SubTab.findStep_some [propext, Quot.sound]
#axioms_within PLLND.SubTab.findStep_none [propext, Quot.sound]
#axioms_within PLLND.SubTab.mem_demands [propext, Quot.sound]
#axioms_within PLLND.SubTab.demand_check [propext, Quot.sound]
#axioms_within PLLND.SubTab.subs_closed [propext, Quot.sound]
