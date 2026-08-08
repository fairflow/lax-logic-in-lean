/-!
# `LJF`: a focused calculus for intuitionistic logic, from the ground up

This file is **self-contained on purpose**.  It imports nothing from the rest
of the development: not `Deriv`, not `G4c`, not the existing interpolation
machinery.  Everything `LJF` needs — weakening, identity expansion, cut — is
built here, for `LJF`, from its own rules.

Matthew's instruction (2026-08-08), and the reason for it:

* the *technique* is what is under test, so borrowing cut-admissibility or
  completeness from another calculus would measure that calculus's metatheory
  rather than this one's;
* a self-contained development reads as a single argument, which a patchwork
  of imports from three calculi does not;
* and reuse is the exact shape of the back-door that nearly imported the
  existing interpolant through `existsP`.

## Naming

`LJF` is Liang–Miller's focused intuitionistic calculus.  What is built here is
the **canonical-polarity instance** of it: every connective sits at its own
polarity (`∨`, `⊥`, atoms positive; `⊃`, `∧` negative) and atoms are *not*
assignable.  Full `LJF` allows the polarity of atoms to be chosen; that freedom
is not needed here and is not implemented, so this is faithful to `LJF` as a
fragment, not as the whole system.  The lax extension in `PLLFocused.lean` is
`LJF◯` — `LJF` plus `◯` and the second judgment.

## The four judgments

    Inv    Γ ; Ω ⇒ N      inversion (asynchronous) phase
    Stab   Γ     ⇒ P      stable sequent: nothing left to invert
    RFocus Γ    ⇒ [P]     right focus on a positive goal
    LFoc   Γ [N] ⇒ P      left focus on a negative hypothesis

`Γ` is the stable context of negatives, `Ω` the queue of positives still to be
inverted.  Focus is entered only at a stable sequent, and left only at a shift.
-/

namespace LJF

/-! ## Polarised syntax -/

mutual
/-- Positive (synchronous) propositions. -/
inductive Pos where
  | atom : String → Pos
  | fls  : Pos
  | or   : Pos → Pos → Pos
  | down : Neg → Pos
  deriving DecidableEq
/-- Negative (asynchronous) propositions. -/
inductive Neg where
  | up   : Pos → Neg
  | imp  : Pos → Neg → Neg
  | and  : Neg → Neg → Neg
  deriving DecidableEq
end

/-! ## The calculus -/

mutual

/-- A **stable sequent**: `Ω` is empty and the goal is positive, so the only
moves left are to focus, on the right or on a hypothesis. -/
inductive Stab : List Neg → Pos → Type
  | rfoc {Γ P} : RFocus Γ P → Stab Γ P
  | lfoc {Γ P N} (h : N ∈ Γ) : LFoc Γ N P → Stab Γ P

/-- **Right focus** on a positive goal. -/
inductive RFocus : List Neg → Pos → Type
  | init {Γ a} (h : Neg.up (Pos.atom a) ∈ Γ) : RFocus Γ (.atom a)
  | or1 {Γ P Q} : RFocus Γ P → RFocus Γ (.or P Q)
  | or2 {Γ P Q} : RFocus Γ Q → RFocus Γ (.or P Q)
  | rel {Γ N} : Inv Γ [] N → RFocus Γ (.down N)

/-- **Left focus** on a negative hypothesis. -/
inductive LFoc : List Neg → Neg → Pos → Type
  | rel {Γ Q P} : Inv Γ [Q] (.up P) → LFoc Γ (.up Q) P
  | impL {Γ Q N P} : Stab Γ Q → LFoc Γ N P → LFoc Γ (.imp Q N) P
  | and1 {Γ M N P} : LFoc Γ M P → LFoc Γ (.and M N) P
  | and2 {Γ M N P} : LFoc Γ N P → LFoc Γ (.and M N) P

/-- **Inversion.**  Right rules act on the goal, left rules on the head of
`Ω`; `stable` is the exit, available only when `Ω` is empty and the goal is a
shift.  `Ω` is a stack: the head-only discipline is canonical because every
inversion rule is invertible, so the processing order is immaterial. -/
inductive Inv : List Neg → List Pos → Neg → Type
  | impR {Γ Ω Q N} : Inv Γ (Q :: Ω) N → Inv Γ Ω (.imp Q N)
  | andR {Γ Ω M N} : Inv Γ Ω M → Inv Γ Ω N → Inv Γ Ω (.and M N)
  | stable {Γ P} : Stab Γ P → Inv Γ [] (.up P)
  | orL {Γ Ω P Q N} : Inv Γ (P :: Ω) N → Inv Γ (Q :: Ω) N →
      Inv Γ (.or P Q :: Ω) N
  | flsL {Γ Ω N} : Inv Γ (.fls :: Ω) N
  | downL {Γ Ω M N} : Inv (M :: Γ) Ω N → Inv Γ (.down M :: Ω) N
  | atomL {Γ Ω a N} : Inv (.up (.atom a) :: Γ) Ω N → Inv Γ (.atom a :: Ω) N

end

/-! ## Contexts: the subset relation

Contraction and exchange are free because the context is used by membership;
only weakening needs an argument, and one traversal gives all three. -/

/-- `Γ'` contains everything in `Γ`. -/
def Sub (Γ Γ' : List Neg) : Prop := ∀ N, N ∈ Γ → N ∈ Γ'

namespace Sub

theorem refl (Γ : List Neg) : Sub Γ Γ := fun _ h => h

theorem trans {Γ Γ' Γ'' : List Neg} (h₁ : Sub Γ Γ') (h₂ : Sub Γ' Γ'') :
    Sub Γ Γ'' := fun N h => h₂ N (h₁ N h)

/-- Extending both sides by the same hypothesis. -/
theorem cons {Γ Γ' : List Neg} (X : Neg) (h : Sub Γ Γ') :
    Sub (X :: Γ) (X :: Γ') := by
  intro N hN
  rcases List.mem_cons.mp hN with rfl | hN
  · exact List.mem_cons_self ..
  · exact List.mem_cons_of_mem _ (h N hN)

/-- Extending the target. -/
theorem grow {Γ : List Neg} (X : Neg) : Sub Γ (X :: Γ) :=
  fun _ h => List.mem_cons_of_mem _ h

end Sub

/-! ## Weakening

One mutual traversal, structural in the derivation. -/

mutual

/-- Weakening of a stable sequent. -/
def Stab.wk : {Γ Γ' : List Neg} → {P : Pos} → Sub Γ Γ' → Stab Γ P → Stab Γ' P
  | _, _, _, H, .rfoc d   => .rfoc (RFocus.wk H d)
  | _, _, _, H, .lfoc h d => .lfoc (H _ h) (LFoc.wk H d)

/-- Weakening under right focus. -/
def RFocus.wk : {Γ Γ' : List Neg} → {P : Pos} → Sub Γ Γ' → RFocus Γ P → RFocus Γ' P
  | _, _, _, H, .init h => .init (H _ h)
  | _, _, _, H, .or1 d  => .or1 (RFocus.wk H d)
  | _, _, _, H, .or2 d  => .or2 (RFocus.wk H d)
  | _, _, _, H, .rel d  => .rel (Inv.wk H d)

/-- Weakening under left focus. -/
def LFoc.wk : {Γ Γ' : List Neg} → {N : Neg} → {P : Pos} →
    Sub Γ Γ' → LFoc Γ N P → LFoc Γ' N P
  | _, _, _, _, H, .rel d    => .rel (Inv.wk H d)
  | _, _, _, _, H, .impL a d => .impL (Stab.wk H a) (LFoc.wk H d)
  | _, _, _, _, H, .and1 d   => .and1 (LFoc.wk H d)
  | _, _, _, _, H, .and2 d   => .and2 (LFoc.wk H d)

/-- Weakening of an inversion sequent. -/
def Inv.wk : {Γ Γ' : List Neg} → {Ω : List Pos} → {N : Neg} →
    Sub Γ Γ' → Inv Γ Ω N → Inv Γ' Ω N
  | _, _, _, _, H, .impR d   => .impR (Inv.wk H d)
  | _, _, _, _, H, .andR d e => .andR (Inv.wk H d) (Inv.wk H e)
  | _, _, _, _, H, .stable d => .stable (Stab.wk H d)
  | _, _, _, _, H, .orL d e  => .orL (Inv.wk H d) (Inv.wk H e)
  | _, _, _, _, _, .flsL     => .flsL
  | _, _, _, _, H, .downL d  => .downL (Inv.wk (Sub.cons _ H) d)
  | _, _, _, _, H, .atomL d  => .atomL (Inv.wk (Sub.cons _ H) d)

end

/-! ## Size

The measure for identity expansion (and, later, for cut on the cut formula).
Shifts cost one, so `sizeNeg M < sizePos (down M)` and `sizePos P <
sizeNeg (up P)`: crossing a shift always makes the formula strictly smaller,
which is what lets the two expansions call each other. -/

mutual
/-- Size of a positive. -/
def sizePos : Pos → Nat
  | .atom _  => 1
  | .fls     => 1
  | .or P Q  => sizePos P + sizePos Q + 1
  | .down N  => sizeNeg N + 1
/-- Size of a negative. -/
def sizeNeg : Neg → Nat
  | .up P    => sizePos P + 1
  | .imp P N => sizePos P + sizeNeg N + 1
  | .and M N => sizeNeg M + sizeNeg N + 1
end

theorem sizePos_pos (P : Pos) : 0 < sizePos P := by
  cases P <;> simp [sizePos] <;> omega

theorem sizeNeg_pos (N : Neg) : 0 < sizeNeg N := by
  cases N <;> simp [sizeNeg] <;> omega

/-! ## Identity expansion

`LJF`'s only axiom is `init`, at atoms.  That every proposition entails itself
is therefore a **theorem**, and it is proved by the two functions below, which
are the two halves of the same induction on the formula.

* `posRestore Q` says: *inverting `Q` on the left gives it back on the right*.
  To prove `Γ; Q,Ω ⇒ N` it suffices to prove `Γ'; Ω ⇒ N` in the extended
  context `Γ'` produced by inverting `Q`, **with a right focus on `Q` in hand**.
  This is the precise sense in which left inversion loses nothing.

* `idNegK N` says: *if `N` is usable, `N` is provable*.  Given a continuation
  that turns any left focus on `N` into a stable sequent, it builds `Γ ⇒ N`.

The continuations are what make the two mutually recursive without any cut:
`posRestore` hands its caller a `RFocus`, and `idNegK` consumes an `LFoc`. -/

mutual

/-- **Left inversion of a positive returns it on the right.** -/
def posRestore (Q : Pos) (Γ : List Neg) (Ω : List Pos) (N : Neg)
    (k : ∀ Γ', Sub Γ Γ' → RFocus Γ' Q → Inv Γ' Ω N) : Inv Γ (Q :: Ω) N :=
  match Q, k with
  | .atom a, k =>
      .atomL (k (.up (.atom a) :: Γ) (Sub.grow _) (.init (List.mem_cons_self ..)))
  | .fls, _ => .flsL
  | .down M, k =>
      .downL (k (M :: Γ) (Sub.grow _)
        (.rel (idNegK M (M :: Γ)
          (fun _ _ hs lf => .lfoc (hs _ (List.mem_cons_self ..)) lf))))
  | .or P₁ P₂, k =>
      .orL (posRestore P₁ Γ Ω N (fun Γ' hs r => k Γ' hs (.or1 r)))
           (posRestore P₂ Γ Ω N (fun Γ' hs r => k Γ' hs (.or2 r)))
termination_by sizePos Q
decreasing_by
  all_goals simp_wf
  all_goals simp only [sizePos]
  all_goals omega

/-- **A usable negative is a provable negative.** -/
def idNegK (N : Neg) (Γ : List Neg)
    (k : ∀ Γ' P, Sub Γ Γ' → LFoc Γ' N P → Stab Γ' P) : Inv Γ [] N :=
  match N, k with
  | .up P, k =>
      .stable (k Γ P (Sub.refl Γ)
        (.rel (posRestore P Γ [] (.up P) (fun _ _ r => .stable (.rfoc r)))))
  | .imp Q M, k =>
      .impR (posRestore Q Γ [] M (fun Γ' hs r =>
        idNegK M Γ' (fun Γ'' P hs' lf =>
          k Γ'' P (Sub.trans hs hs') (.impL (.rfoc (RFocus.wk hs' r)) lf))))
  | .and M₁ M₂, k =>
      .andR (idNegK M₁ Γ (fun Γ' P hs lf => k Γ' P hs (.and1 lf)))
            (idNegK M₂ Γ (fun Γ' P hs lf => k Γ' P hs (.and2 lf)))
termination_by sizeNeg N
decreasing_by
  all_goals simp_wf
  all_goals simp only [sizePos, sizeNeg]
  all_goals omega

end

/-- **Identity, negative form**: every hypothesis proves itself. -/
def idNeg (N : Neg) (Γ : List Neg) (h : N ∈ Γ) : Inv Γ [] N :=
  idNegK N Γ (fun _ _ hs lf => .lfoc (hs _ h) lf)

/-- **Identity, positive form**: `P ⇒ P`, with `P` inverted on the left and
focused on the right. -/
def idPos (P : Pos) (Γ : List Neg) : Inv Γ [P] (.up P) :=
  posRestore P Γ [] (.up P) (fun _ _ r => .stable (.rfoc r))

end LJF

/-! # Part 2: the uniform interpolant, by weighted recursion

## Where the weight enters, and why it is necessary

The interpolant must be **uniform**: one `p`-free formula per antecedent,
serving every goal and every derivation at once.  So it cannot be defined by
recursion on a derivation — it must be defined by recursion on the *sequent*,
following the rules of the calculus applied backwards.

A naive structural measure does not survive that recursion, because the
clauses do not merely decompose — they **transform**:

* currying `(M₁∧M₂ ⊃ N) ↝ (M₁ ⊃ (M₂ ⊃ N))` preserves the naive size;
* splitting `(Q₁∨Q₂ ⊃ N) ↝ (Q₁ ⊃ N), (Q₂ ⊃ N)` *duplicates* `N`;
* inverting a goal `Q ⊃ N` moves `Q` into the context, which *grows*.

The weight repairs all three at once.  Each connective is assigned a cost —
here `atom = ⊥ = 1`, `∨` and `⊃` and `↓` cost `+1`, `∧` costs `+3`, `↑` costs
`0` — and a context is measured by `Σ 3^(weight)`.  The exponential is doing
the work of a multiset order: replacing one hypothesis of weight `w` by at
most two hypotheses of weight `≤ w − 1` drops the sum, because
`2·3^(w−1) < 3^w`.  The costs themselves are **solved for** from the clause
set: each clause contributes an inequality (currying forces `∧ ≥ 3` given the
shift costs; goal-inversion forces `3^{wQ} + 3^{wN} < 3^{wQ+wN+1}`, true since
both weights are positive), and the assignment above is a solution.  Dyckhoff's
weights for `G4ip` are a solution to the same kind of system for a different
rule set; ours differ because the shifts change the clause set.

Why it is necessary and not merely convenient: termination of proof *search*
could be had by loop-checking, but a loop-checker yields no formula.  The
interpolant is *built by* the recursion, so its existence needs structural
well-foundedness — the weight is what turns "the calculus terminates" into
"the interpolant exists".  It is also what buys predicativity: the
interpolation candidate is a least fixed point, and Girard-style candidates
take such fixed points impredicatively; the weight lets this one be reached by
well-founded recursion instead.
-/

namespace LJF

/-! ## The weight -/

mutual
/-- Weight of a positive.  `atom = ⊥ = 1`; `∨` costs `+1`; `↓` costs `+1`. -/
def wPos : Pos → Nat
  | .atom _ => 1
  | .fls    => 1
  | .or P Q => wPos P + wPos Q + 1
  | .down M => wNeg M + 1
/-- Weight of a negative.  `↑` costs `0`; `⊃` costs `+1`; `∧` costs `+3`
(currying `(M₁∧M₂ ⊃ N) ↝ (M₁ ⊃ (M₂ ⊃ N))` forces `∧ > ⊃ + ↓`, given `↓ = 1`). -/
def wNeg : Neg → Nat
  | .up P    => wPos P
  | .imp Q N => wPos Q + wNeg N + 1
  | .and M N => wNeg M + wNeg N + 3
end

theorem wPos_pos (P : Pos) : 0 < wPos P := by
  cases P <;> simp [wPos] <;> omega

theorem wNeg_pos (N : Neg) : 0 < wNeg N := by
  cases N with
  | up P => simpa [wNeg] using wPos_pos P
  | imp Q N => simp only [wNeg]; omega
  | and M N => simp only [wNeg]; omega

/-! ## Powers of three: the little arithmetic kit, from scratch -/

theorem p3_pos (n : Nat) : 0 < 3 ^ n := Nat.pow_pos (by omega)

theorem p3_mono {a b : Nat} (h : a ≤ b) : 3 ^ a ≤ 3 ^ b :=
  Nat.pow_le_pow_right (by omega) h

theorem p3_strict {a b : Nat} (h : a < b) : 3 ^ a < 3 ^ b := by
  calc 3 ^ a < 3 ^ a * 3 := by have := p3_pos a; omega
    _ = 3 ^ (a + 1) := by rw [Nat.pow_succ]
    _ ≤ 3 ^ b := p3_mono (by omega)

/-- Two summands strictly under the bound: `3^a + 3^b < 3^c` when `a,b < c`. -/
theorem p3_add {a b c : Nat} (ha : a < c) (hb : b < c) :
    3 ^ a + 3 ^ b < 3 ^ c := by
  have h1 : 3 ^ a ≤ 3 ^ (c - 1) := p3_mono (by omega)
  have h2 : 3 ^ b ≤ 3 ^ (c - 1) := p3_mono (by omega)
  have h3 : 3 ^ c = 3 ^ (c - 1) * 3 := by
    rw [← Nat.pow_succ]; congr 1; omega
  have := p3_pos (c - 1)
  omega

/-- `2·3^a < 3^c` when `a < c`. -/
theorem p3_2 {a c : Nat} (ha : a + 1 ≤ c) : 2 * 3 ^ a < 3 ^ c := by
  have h1 : 3 ^ a ≤ 3 ^ (c - 1) := p3_mono (by omega)
  have h3 : 3 ^ c = 3 ^ (c - 1) * 3 := by
    rw [← Nat.pow_succ]; congr 1; omega
  have := p3_pos (c - 1)
  omega

/-- `2·3^a + 3^b < 3^c` when `a + 2 ≤ c` and `b + 1 ≤ c`. -/
theorem p3_21 {a b c : Nat} (ha : a + 2 ≤ c) (hb : b + 1 ≤ c) :
    2 * 3 ^ a + 3 ^ b < 3 ^ c := by
  have h1 : 3 ^ a ≤ 3 ^ (c - 2) := p3_mono (by omega)
  have h2 : 3 ^ b ≤ 3 ^ (c - 2) * 3 := by
    have : 3 ^ b ≤ 3 ^ (c - 1) := p3_mono (by omega)
    have e : 3 ^ (c - 1) = 3 ^ (c - 2) * 3 := by
      rw [← Nat.pow_succ]; congr 1; omega
    omega
  have h3 : 3 ^ c = 3 ^ (c - 2) * 3 * 3 := by
    rw [← Nat.pow_succ, ← Nat.pow_succ]; congr 1; omega
  have := p3_pos (c - 2)
  omega

/-! ## Context measure -/

/-- `Σ 3^(weight)` over a context. -/
def sum3 : List Neg → Nat
  | []     => 0
  | N :: Γ => 3 ^ wNeg N + sum3 Γ

theorem sum3_append (Γ Δ : List Neg) :
    sum3 (Γ ++ Δ) = sum3 Γ + sum3 Δ := by
  induction Γ with
  | nil => simp [sum3]
  | cons N Γ ih => simp [sum3, ih]; omega

/-! ## Inversion of a positive, as data

`invertPos Q` is the list of **branches** produced by fully inverting `Q` on
the left; each branch is the list of stable hypotheses it contributes.
`⊥` has no branches; `∨` concatenates; an atom or a shift is one branch with
one hypothesis. -/

def invertPos : Pos → List (List Neg)
  | .atom a  => [[.up (.atom a)]]
  | .fls     => []
  | .or P Q  => invertPos P ++ invertPos Q
  | .down M  => [[M]]

/-- Each branch weighs no more than the positive it came from. -/
theorem invertPos_le : ∀ (P : Pos), ∀ b ∈ invertPos P, sum3 b ≤ 3 ^ wPos P
  | .atom a, b, hb => by
      simp only [invertPos, List.mem_singleton] at hb; subst hb
      simp [sum3, wNeg, wPos]
  | .fls, b, hb => by simp [invertPos] at hb
  | .or P Q, b, hb => by
      simp only [invertPos, List.mem_append] at hb
      rcases hb with hb | hb
      · exact Nat.le_trans (invertPos_le P b hb)
          (p3_mono (by simp only [wPos]; omega))
      · exact Nat.le_trans (invertPos_le Q b hb)
          (p3_mono (by simp only [wPos]; omega))
  | .down M, b, hb => by
      simp only [invertPos, List.mem_singleton] at hb; subst hb
      simp only [sum3, wPos]
      have := p3_strict (a := wNeg M) (b := wNeg M + 1) (by omega)
      omega
termination_by P => sizePos P
decreasing_by all_goals (simp_wf; simp only [sizePos]; omega)

/-- For a non-atomic positive the inequality is strict — this is what makes
moving a hypothesis's branches into the context a descent. -/
theorem invertPos_lt {P : Pos} (h : ∀ a, P ≠ .atom a) :
    ∀ b ∈ invertPos P, sum3 b < 3 ^ wPos P := by
  cases P with
  | atom a => exact absurd rfl (h a)
  | fls => intro b hb; simp [invertPos] at hb
  | or P Q =>
      intro b hb
      simp only [invertPos, List.mem_append] at hb
      rcases hb with hb | hb
      · exact Nat.lt_of_le_of_lt (invertPos_le P b hb)
          (p3_strict (by simp only [wPos]; have := wPos_pos Q; omega))
      · exact Nat.lt_of_le_of_lt (invertPos_le Q b hb)
          (p3_strict (by simp only [wPos]; have := wPos_pos P; omega))
  | down M =>
      intro b hb; simp [invertPos] at hb; subst hb
      simp only [sum3, wPos]
      have := p3_strict (a := wNeg M) (b := wNeg M + 1) (by omega)
      omega

/-! ## Positional splits

`splits Γ` lists each member of `Γ` together with the rest of the context —
the tool by which the saturated clauses consume a hypothesis without needing
decidable equality on formulas. -/

def splits : List Neg → List (Neg × List Neg)
  | []     => []
  | X :: Γ => (X, Γ) :: (splits Γ).map (fun ⟨Y, rest⟩ => (Y, X :: rest))

theorem splits_sum {Γ : List Neg} :
    ∀ {X rest}, (X, rest) ∈ splits Γ → sum3 Γ = 3 ^ wNeg X + sum3 rest := by
  induction Γ with
  | nil => intro X rest h; simp [splits] at h
  | cons Y Γ ih =>
      intro X rest h
      simp only [splits, List.mem_cons, List.mem_map] at h
      rcases h with h | ⟨⟨Z, rest'⟩, hZ, hEq⟩
      · cases h; rfl
      · cases hEq
        simp only [sum3, ih hZ]; omega

theorem splits_mem {Γ : List Neg} :
    ∀ {X rest}, (X, rest) ∈ splits Γ → X ∈ Γ := by
  induction Γ with
  | nil => intro X rest h; simp [splits] at h
  | cons Y Γ ih =>
      intro X rest h
      simp only [splits, List.mem_cons, List.mem_map] at h
      rcases h with h | ⟨⟨Z, rest'⟩, hZ, hEq⟩
      · cases h; exact List.mem_cons_self ..
      · cases hEq; exact List.mem_cons_of_mem _ (ih hZ)

end LJF

namespace LJF

/-! ## Interpolant connectives

The interpolant is a formula of `LJF` itself, carried as a `Neg` (hypotheses
are negative).  Disjunction of negatives goes through the shifts. -/

/-- `⊤` as a negative: `⊥ ⊃ ⊥`. -/
def nTop : Neg := .imp .fls (.up .fls)
/-- `⊥` as a negative. -/
def nBot : Neg := .up .fls
/-- Conjunction of interpolants. -/
def nAnd (M N : Neg) : Neg := .and M N
/-- Disjunction of interpolants: `↑(↓M ∨ ↓N)`. -/
def nOr (M N : Neg) : Neg := .up (.or (.down M) (.down N))
/-- Conjunction of a list, unit `⊤`. -/
def nAndAll : List Neg → Neg := fun l => l.foldr nAnd nTop
/-- Disjunction of a list, unit `⊥`. -/
def nOrAll : List Neg → Neg := fun l => l.foldr nOr nBot

/-- `p`-guard: the unit `C` when the atom is `p`, else `D`.  A named helper
so the aggregate match-arms stay opaque applications, which keeps the
functional-induction cases clean. -/
def pGuard (p a : String) (C D : Neg) : Neg := if a = p then C else D

/-- The head disjunct of an atomic goal: nothing if the atom is `p`. -/
def atomHead (p q : String) : List Neg := if q = p then [] else [.up (.atom q)]

/-- Is the atom `a` a hypothesis (as `↑a`)? -/
def atomMem (a : String) (Γ : List Neg) : Bool :=
  Γ.any (fun | .up (.atom b) => a == b | _ => false)

/-! ## The fire scan

A parked implication `a ⊃ N` fires as soon as its atom is present.  The scan
walks the positional splits and returns the first firable one. -/

def findFire (full : List Neg) : List (Neg × List Neg) → Option (String × Neg × List Neg)
  | [] => none
  | (X, rest) :: more =>
    match X with
    | .imp (.atom a) N =>
        if atomMem a full then some (a, N, rest) else findFire full more
    | _ => findFire full more

theorem findFire_mem {full : List Neg} :
    ∀ {l : List (Neg × List Neg)} {a N rest},
      findFire full l = some (a, N, rest) → (Neg.imp (.atom a) N, rest) ∈ l := by
  intro l
  induction l with
  | nil => intro a N rest h; simp [findFire] at h
  | cons XR more ih =>
      intro a N rest h
      obtain ⟨X, R⟩ := XR
      match X, h with
      | .imp (.atom b) N', h => ?_
      | .up P, h => exact List.mem_cons_of_mem _ (ih h)
      | .imp .fls N', h => exact List.mem_cons_of_mem _ (ih h)
      | .imp (.or Q₁ Q₂) N', h => exact List.mem_cons_of_mem _ (ih h)
      | .imp (.down M) N', h => exact List.mem_cons_of_mem _ (ih h)
      | .and M₁ M₂, h => exact List.mem_cons_of_mem _ (ih h)
      simp only [findFire] at h
      by_cases hM : atomMem b full
      · simp [hM] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact List.mem_cons_self ..
      · simp [hM] at h
        exact List.mem_cons_of_mem _ (ih h)

/-- Goal component of the measure. -/
def goalW : Option Neg → Nat
  | none   => 0
  | some G => 3 ^ wNeg G

/-! ## The descent lemmas

One lemma per clause of the recursion below, each stating its measure descent
in exactly the shape the termination checker asks for.  Together they are the
spent form of the weight inequalities. -/

theorem dec_park {t d e : Nat} : 2 * t + (3 ^ e + d) < 2 * (3 ^ e + t) + d := by
  have := p3_pos e; omega

theorem dec_drop {t e : Nat} : t < 3 ^ e + t := by
  have := p3_pos e; omega

theorem dec_shift1 {m t : Nat} : 3 ^ m + t < 3 ^ (m + 1) + t := by
  have := p3_strict (a := m) (b := m + 1) (by omega); omega

theorem dec_and {m n t : Nat} :
    3 ^ m + (3 ^ n + t) < 3 ^ (m + n + 3) + t := by
  have := p3_add (a := m) (b := n) (c := m + n + 3) (by omega) (by omega)
  omega

theorem dec_impor {a b n t : Nat} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    3 ^ (a + n + 1) + (3 ^ (b + n + 1) + t) < 3 ^ (a + b + 1 + n + 1) + t := by
  have := p3_add (a := a + n + 1) (b := b + n + 1) (c := a + b + 1 + n + 1)
    (by omega) (by omega)
  omega

theorem dec_stripshift {x n t : Nat} :
    3 ^ (x + n + 1) + t < 3 ^ (x + 1 + n + 1) + t := by
  have := p3_strict (a := x + n + 1) (b := x + 1 + n + 1) (by omega); omega

theorem dec_curry {m₁ m₂ n t : Nat} :
    3 ^ (m₁ + 1 + (m₂ + 1 + n + 1) + 1) + t <
      3 ^ (m₁ + m₂ + 3 + 1 + n + 1) + t := by
  have := p3_strict (a := m₁ + 1 + (m₂ + 1 + n + 1) + 1)
    (b := m₁ + m₂ + 3 + 1 + n + 1) (by omega)
  omega

theorem dec_orctx {P Q : Pos} {b : List Neg} {t : Nat}
    (hb : b ∈ invertPos (Pos.or P Q)) :
    sum3 b + t < 3 ^ (wPos P + wPos Q + 1) + t := by
  have h := invertPos_lt (P := Pos.or P Q) (by intro a h; nomatch h) b hb
  simp only [wPos] at h; omega

theorem dec_fire {done rest : List Neg} {a : String} {N : Neg}
    (hf : findFire done (splits done) = some (a, N, rest)) :
    2 * (3 ^ wNeg N + 0) + sum3 rest < 2 * 0 + sum3 done := by
  have hs := splits_sum (findFire_mem hf)
  simp only [wNeg, wPos] at hs
  have := p3_2 (a := wNeg N) (c := 1 + wNeg N + 1) (by omega)
  omega

theorem dec_qimp {done rest : List Neg} {a : String} {N : Neg}
    (h : (Neg.imp (Pos.atom a) N, rest) ∈ splits done) :
    2 * (3 ^ wNeg N + 0) + sum3 rest < 2 * 0 + sum3 done := by
  have hs := splits_sum h
  simp only [wNeg, wPos] at hs
  have := p3_2 (a := wNeg N) (c := 1 + wNeg N + 1) (by omega)
  omega

theorem dec_qimp_g {done rest : List Neg} {a : String} {N : Neg} {g : Nat}
    (h : (Neg.imp (Pos.atom a) N, rest) ∈ splits done) :
    2 * (3 ^ wNeg N + 0) + sum3 rest < 2 * 0 + sum3 done + g :=
  Nat.lt_of_lt_of_le (dec_qimp h) (by omega)

theorem dec_dyk1 {done rest : List Neg} {Q' : Pos} {N' N : Neg}
    (h : (Neg.imp (Pos.down (Neg.imp Q' N')) N, rest) ∈ splits done) :
    2 * (3 ^ (wNeg N' + 1 + wNeg N + 1) + 0) + sum3 rest +
        3 ^ (wPos Q' + wNeg N' + 1) <
      2 * 0 + sum3 done + 0 := by
  have hs := splits_sum h
  simp only [wNeg, wPos] at hs
  have := p3_21 (a := wNeg N' + 1 + wNeg N + 1) (b := wPos Q' + wNeg N' + 1)
    (c := wPos Q' + wNeg N' + 1 + 1 + wNeg N + 1)
    (by have := wPos_pos Q'; omega) (by have := wNeg_pos N; omega)
  omega

theorem dec_dyk1_g {done rest : List Neg} {Q' : Pos} {N' N : Neg} {g : Nat}
    (h : (Neg.imp (Pos.down (Neg.imp Q' N')) N, rest) ∈ splits done) :
    2 * (3 ^ (wNeg N' + 1 + wNeg N + 1) + 0) + sum3 rest +
        3 ^ (wPos Q' + wNeg N' + 1) <
      2 * 0 + sum3 done + g := by
  have := dec_dyk1 h; omega

theorem dec_dyk2 {done rest : List Neg} {Q' : Pos} {N' N : Neg}
    (h : (Neg.imp (Pos.down (Neg.imp Q' N')) N, rest) ∈ splits done) :
    2 * (3 ^ wNeg N + 0) + sum3 rest < 2 * 0 + sum3 done := by
  have hs := splits_sum h
  simp only [wNeg, wPos] at hs
  have := p3_2 (a := wNeg N) (c := wPos Q' + wNeg N' + 1 + 1 + wNeg N + 1)
    (by have := wPos_pos Q'; have := wNeg_pos N'; omega)
  omega

theorem dec_dyk2_g {done rest : List Neg} {Q' : Pos} {N' N : Neg} {g : Nat}
    (h : (Neg.imp (Pos.down (Neg.imp Q' N')) N, rest) ∈ splits done) :
    2 * (3 ^ wNeg N + 0) + sum3 rest < 2 * 0 + sum3 done + g :=
  Nat.lt_of_lt_of_le (dec_dyk2 h) (by omega)

theorem dec_ainv {Q : Pos} {b : List Neg} {N : Neg} {d : Nat}
    (hb : b ∈ invertPos Q) :
    2 * sum3 b + d + 3 ^ wNeg N < 2 * 0 + d + 3 ^ (wPos Q + wNeg N + 1) := by
  have h1 := invertPos_le Q b hb
  have := p3_21 (a := wPos Q) (b := wNeg N) (c := wPos Q + wNeg N + 1)
    (by have := wNeg_pos N; omega) (by have := wPos_pos Q; omega)
  omega

end LJF

namespace LJF

/-! ## The uniform interpolant

One recursion computes both quantifiers.  `interp p todo done goal`:

* `goal = none` — **`∃p` mode**: the strongest `p`-free consequence of the
  context `todo ++ done`;
* `goal = some G` — **`∀p` mode**: the weakest `p`-free hypothesis that,
  beside the context, suffices for `G`.

`todo` is the unprocessed part of the context; `done` holds the parked
members, which come in exactly three shapes — atoms `↑a`, implications
`a ⊃ N` whose atom is not yet available, and the Dyckhoff implications
`↓(Q' ⊃ N') ⊃ N`.

The processing clauses consume the head of `todo` and replace it by strictly
lighter material (the residual): this is where each weight inequality is
spent, and each clause is annotated with its inequality.  The aggregate
clauses (at `todo = []`) first fire any parked implication whose atom has
arrived, then read the interpolant off the saturated context.

The measure is `2·sum3 todo + sum3 done + goalW goal`: parking moves a
hypothesis from the doubled side to the single side, so even the bookkeeping
steps are strict, and no lexicographic order is needed. -/

def interp (p : String) : (todo done : List Neg) → (goal : Option Neg) → Neg
  -- ── processing phase: consume the head of `todo` ──
  -- park an atom
  | .up (.atom a) :: todo, done, g =>
      interp p todo (.up (.atom a) :: done) g
  -- absurd hypothesis: `∨` over no branches is `⊥`, `∧` over none is `⊤`
  | .up .fls :: _, _, none => nBot
  | .up .fls :: _, _, some _ => nTop
  -- context split: `∨` of branch results in `∃p` mode, `∧` in `∀p` mode
  -- [sum3 b < 3^(w P∨Q), both branches]
  | .up (.or P Q) :: todo, done, none =>
      nOrAll ((invertPos (.or P Q)).attach.map
        (fun ⟨b, hb⟩ => interp p (b ++ todo) done none))
  | .up (.or P Q) :: todo, done, some G =>
      nAndAll ((invertPos (.or P Q)).attach.map
        (fun ⟨b, hb⟩ => interp p (b ++ todo) done (some G)))
  -- a shifted negative moves into the context  [w M < w ↑↓M = w M + 1]
  | .up (.down M) :: todo, done, g =>
      interp p (M :: todo) done g
  -- a conjunction splits  [3^wM + 3^wN < 3^(wM+wN+3)]
  | .and M N :: todo, done, g =>
      interp p (M :: N :: todo) done g
  -- `⊥ ⊃ N` is inert: drop it
  | .imp .fls _ :: todo, done, g =>
      interp p todo done g
  -- `a ⊃ N` parks until its atom arrives
  | .imp (.atom a) N :: todo, done, g =>
      interp p todo (.imp (.atom a) N :: done) g
  -- `(Q₁∨Q₂) ⊃ N` splits  [3^(wQ₁+wN+1) + 3^(wQ₂+wN+1) < 3^(wQ₁+wQ₂+1+wN+1)]
  | .imp (.or Q₁ Q₂) N :: todo, done, g =>
      interp p (.imp Q₁ N :: .imp Q₂ N :: todo) done g
  -- `↓↑P' ⊃ N` strips the double shift  [w drops by 1]
  | .imp (.down (.up P')) N :: todo, done, g =>
      interp p (.imp P' N :: todo) done g
  -- currying: `↓(M₁∧M₂) ⊃ N  ↝  ↓M₁ ⊃ (↓M₂ ⊃ N)`  [w: +5 vs +4 — the
  -- inequality that forces `∧` to cost 3]
  | .imp (.down (.and M₁ M₂)) N :: todo, done, g =>
      interp p (.imp (.down M₁) (.imp (.down M₂) N) :: todo) done g
  -- the Dyckhoff implication parks
  | .imp (.down (.imp Q' N')) N :: todo, done, g =>
      interp p todo (.imp (.down (.imp Q' N')) N :: done) g
  -- ── aggregate phase: `todo` exhausted ──
  | [], done, g =>
    match hf : findFire done (splits done) with
    -- a parked `a ⊃ N` whose atom has arrived fires  [3^wN < 3^(wN+2)]
    | some (_, N, rest) => interp p [N] rest g
    | none =>
      match g with
      -- ∃p mode: conjunction over the saturated context
      | none =>
          nAndAll ((splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
            match X with
            -- a surviving atom is its own p-free content
            | .up (.atom a) => pGuard p a nTop (.up (.atom a))
            -- `a ⊃ N`, atom absent: guard the recursion by the atom
            | .imp (.atom a) N =>
                pGuard p a nTop (.imp (.atom a) (interp p [N] rest none))
            -- the Dyckhoff implication: what it yields, guarded by what
            -- the goal interpolant of its antecedent demands
            | .imp (.down (.imp Q' N')) N =>
                .imp (.down (interp p [.imp (.down N') N] rest
                               (some (.imp Q' N'))))
                     (interp p [N] rest none)
            -- unreachable shapes park nothing
            | _ => nTop))
      -- ∀p mode: by the goal
      | some G =>
        match G with
        -- goal inversion  [2·sum3 b + 3^wN < 3^(wQ+wN+1)]
        | .imp Q N =>
            nAndAll ((invertPos Q).attach.map
              (fun ⟨b, hb⟩ => interp p b done (some N)))
        | .and M N =>
            nAnd (interp p [] done (some M)) (interp p [] done (some N))
        -- context attacks: ways the saturated context can advance any goal;
        -- inlined per goal shape so each aggregate case is self-contained
        | .up (.atom q) =>
            if atomMem q done then nTop
            else nOrAll (atomHead p q ++
              (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X with
              | .imp (.atom a) N =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interp p [N] rest (some (.up (Pos.atom q)))))
              | .imp (.down (.imp Q' N')) N =>
                  nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
                       (interp p [N] rest (some (.up (Pos.atom q))))
              | _ => nBot))
        | .up .fls =>
            nOrAll ((splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X with
              | .imp (.atom a) N =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interp p [N] rest (some (.up Pos.fls))))
              | .imp (.down (.imp Q' N')) N =>
                  nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
                       (interp p [N] rest (some (.up Pos.fls)))
              | _ => nBot))
        | .up (.or P₁ P₂) =>
            nOrAll ([interp p [] done (some (.up P₁)),
                     interp p [] done (some (.up P₂))] ++
              (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X with
              | .imp (.atom a) N =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interp p [N] rest (some (.up (Pos.or P₁ P₂)))))
              | .imp (.down (.imp Q' N')) N =>
                  nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
                       (interp p [N] rest (some (.up (Pos.or P₁ P₂))))
              | _ => nBot))
        | .up (.down M) =>
            nOrAll ([interp p [] done (some M)] ++
              (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X with
              | .imp (.atom a) N =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interp p [N] rest (some (.up (Pos.down M)))))
              | .imp (.down (.imp Q' N')) N =>
                  nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
                       (interp p [N] rest (some (.up (Pos.down M))))
              | _ => nBot))
  termination_by todo done goal => 2 * sum3 todo + sum3 done + goalW goal
  decreasing_by
    all_goals simp_wf
    all_goals simp only [sum3, sum3_append, goalW, wNeg, wPos]
    all_goals first
      | exact dec_park
      | exact dec_drop
      | exact dec_shift1
      | exact dec_and
      | exact dec_curry
      | exact dec_stripshift
      | exact p3_strict (by first
          | omega
          | (have := wPos_pos P₁; have := wPos_pos P₂; omega)
          | (have := wNeg_pos M; have := wNeg_pos N; omega))
      | exact dec_impor (wPos_pos _) (wPos_pos _)
      | exact dec_orctx (by assumption)
      | exact dec_fire (by assumption)
      | exact dec_qimp (by assumption)
      | exact dec_qimp_g (by assumption)
      | exact dec_dyk1 (by assumption)
      | exact dec_dyk1_g (by assumption)
      | exact dec_dyk2 (by assumption)
      | exact dec_dyk2_g (by assumption)
      | exact dec_ainv (by assumption)

namespace LJF

/-! ## `p`-freeness -/

mutual
/-- The atom `p` does not occur (positives). -/
def PFreeP (p : String) : Pos → Prop
  | .atom a  => a ≠ p
  | .fls     => True
  | .or P Q  => PFreeP p P ∧ PFreeP p Q
  | .down M  => PFreeN p M
/-- The atom `p` does not occur (negatives). -/
def PFreeN (p : String) : Neg → Prop
  | .up P    => PFreeP p P
  | .imp Q N => PFreeP p Q ∧ PFreeN p N
  | .and M N => PFreeN p M ∧ PFreeN p N
end

theorem pfree_nTop {p : String} : PFreeN p nTop := by
  simp [nTop, PFreeN, PFreeP]

theorem pfree_nBot {p : String} : PFreeN p nBot := by
  simp [nBot, PFreeN, PFreeP]

theorem pfree_nAnd {p : String} {M N : Neg}
    (hM : PFreeN p M) (hN : PFreeN p N) : PFreeN p (nAnd M N) :=
  ⟨hM, hN⟩

theorem pfree_nOr {p : String} {M N : Neg}
    (hM : PFreeN p M) (hN : PFreeN p N) : PFreeN p (nOr M N) :=
  ⟨hM, hN⟩

theorem pfree_nAndAll {p : String} {l : List Neg}
    (h : ∀ x ∈ l, PFreeN p x) : PFreeN p (nAndAll l) := by
  induction l with
  | nil => exact pfree_nTop
  | cons x l ih =>
      exact pfree_nAnd (h x (List.mem_cons_self ..))
        (ih (fun y hy => h y (List.mem_cons_of_mem _ hy)))

theorem pfree_nOrAll {p : String} {l : List Neg}
    (h : ∀ x ∈ l, PFreeN p x) : PFreeN p (nOrAll l) := by
  induction l with
  | nil => exact pfree_nBot
  | cons x l ih =>
      exact pfree_nOr (h x (List.mem_cons_self ..))
        (ih (fun y hy => h y (List.mem_cons_of_mem _ hy)))

theorem pfree_pGuard {p a : String} {C D : Neg}
    (hC : PFreeN p C) (hD : a ≠ p → PFreeN p D) : PFreeN p (pGuard p a C D) := by
  unfold pGuard; split
  · exact hC
  · exact hD (by assumption)

theorem pfree_atomHead {p q : String} : ∀ x ∈ atomHead p q, PFreeN p x := by
  unfold atomHead; split
  · intro x hx; exact absurd hx (List.not_mem_nil)
  · intro x hx
    rcases List.mem_singleton.mp hx with rfl
    rename_i h
    simpa only [PFreeN, PFreeP] using h

/-- **The interpolant never mentions `p`.**  Every clause either keeps `p` out
by construction, or is guarded by the `a == p` test that replaces the would-be
conjunct or disjunct by its unit. -/
theorem interp_pfree (p : String) :
    ∀ (todo done : List Neg) (g : Option Neg), PFreeN p (interp p todo done g) := by
  intro todo done g
  fun_induction interp p todo done g with
  | case1 => assumption
  | case2 => exact pfree_nBot
  | case3 => exact pfree_nTop
  | case4 =>
      rename_i ih
      apply pfree_nOrAll
      intro x hx
      simp only [List.mem_map, List.mem_attach, true_and] at hx
      obtain ⟨⟨b, hb⟩, rfl⟩ := hx
      exact ih b hb
  | case5 =>
      rename_i ih
      apply pfree_nAndAll
      intro x hx
      simp only [List.mem_map, List.mem_attach, true_and] at hx
      obtain ⟨⟨b, hb⟩, rfl⟩ := hx
      exact ih b hb
  | case6 => assumption
  | case7 => assumption
  | case8 => assumption
  | case9 => assumption
  | case10 => assumption
  | case11 => assumption
  | case12 => assumption
  | case13 => assumption
  | case14 => assumption
  | case15 =>
      rename_i ih3 ih2 ih1
      apply pfree_nAndAll
      intro x hx
      simp only [List.mem_map, List.mem_attach, true_and] at hx
      obtain ⟨⟨⟨X, rest⟩, hXr⟩, rfl⟩ := hx
      cases X with
      | up P =>
          cases P with
          | atom a =>
              exact pfree_pGuard pfree_nTop
                (fun h => by simpa only [PFreeN, PFreeP] using h)
          | fls => exact pfree_nTop
          | or _ _ => exact pfree_nTop
          | down _ => exact pfree_nTop
      | imp Q N =>
          cases Q with
          | atom a =>
              exact pfree_pGuard pfree_nTop
                (fun h => ⟨h, ih3 rest a N hXr⟩)
          | fls => exact pfree_nTop
          | or _ _ => exact pfree_nTop
          | down M =>
              cases M with
              | up _ => exact pfree_nTop
              | and _ _ => exact pfree_nTop
              | imp Q' N' =>
                  exact ⟨ih2 rest Q' N' N hXr, ih1 rest Q' N' N hXr⟩
      | and _ _ => exact pfree_nTop
  | case16 =>
      rename_i ih
      apply pfree_nAndAll
      intro x hx
      simp only [List.mem_map, List.mem_attach, true_and] at hx
      obtain ⟨⟨b, hb⟩, rfl⟩ := hx
      exact ih b hb
  | case17 => exact ⟨by assumption, by assumption⟩
  | case18 => exact pfree_nTop
  | case19 =>
      rename_i q hq ih3 ih2 ih1
      apply pfree_nOrAll
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact pfree_atomHead x hx
      · simp only [List.mem_map, List.mem_attach, true_and] at hx
        obtain ⟨⟨⟨X, rest⟩, hXr⟩, rfl⟩ := hx
        cases X with
        | up P => cases P <;> exact pfree_nBot
        | imp Q N =>
            cases Q with
            | atom a =>
                exact pfree_pGuard pfree_nBot
                  (fun h => pfree_nAnd h (ih3 rest a N hXr))
            | fls => exact pfree_nBot
            | or _ _ => exact pfree_nBot
            | down M =>
                cases M with
                | up _ => exact pfree_nBot
                | and _ _ => exact pfree_nBot
                | imp Q' N' =>
                    exact pfree_nAnd (ih2 rest Q' N' N hXr) (ih1 rest Q' N' N hXr)
        | and _ _ => exact pfree_nBot
  | case20 =>
      rename_i ih3 ih2 ih1
      apply pfree_nOrAll
      intro x hx
      simp only [List.mem_map, List.mem_attach, true_and] at hx
      obtain ⟨⟨⟨X, rest⟩, hXr⟩, rfl⟩ := hx
      cases X with
      | up P => cases P <;> exact pfree_nBot
      | imp Q N =>
          cases Q with
          | atom a =>
              exact pfree_pGuard pfree_nBot
                (fun h => pfree_nAnd h (ih3 rest a N hXr))
          | fls => exact pfree_nBot
          | or _ _ => exact pfree_nBot
          | down M =>
              cases M with
              | up _ => exact pfree_nBot
              | and _ _ => exact pfree_nBot
              | imp Q' N' =>
                  exact pfree_nAnd (ih2 rest Q' N' N hXr) (ih1 rest Q' N' N hXr)
      | and _ _ => exact pfree_nBot
  | case21 =>
      rename_i ihP ihQ ih3 ih2 ih1
      apply pfree_nOrAll
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact ihP
        · rcases List.mem_singleton.mp hx with rfl
          exact ihQ
      · simp only [List.mem_map, List.mem_attach, true_and] at hx
        obtain ⟨⟨⟨X, rest⟩, hXr⟩, rfl⟩ := hx
        cases X with
        | up P => cases P <;> exact pfree_nBot
        | imp Q N =>
            cases Q with
            | atom a =>
                exact pfree_pGuard pfree_nBot
                  (fun h => pfree_nAnd h (ih3 rest a N hXr))
            | fls => exact pfree_nBot
            | or _ _ => exact pfree_nBot
            | down M =>
                cases M with
                | up _ => exact pfree_nBot
                | and _ _ => exact pfree_nBot
                | imp Q' N' =>
                    exact pfree_nAnd (ih2 rest Q' N' N hXr) (ih1 rest Q' N' N hXr)
        | and _ _ => exact pfree_nBot
  | case22 =>
      rename_i ihM ih3 ih2 ih1
      apply pfree_nOrAll
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · rcases List.mem_singleton.mp hx with rfl
        exact ihM
      · simp only [List.mem_map, List.mem_attach, true_and] at hx
        obtain ⟨⟨⟨X, rest⟩, hXr⟩, rfl⟩ := hx
        cases X with
        | up P => cases P <;> exact pfree_nBot
        | imp Q N =>
            cases Q with
            | atom a =>
                exact pfree_pGuard pfree_nBot
                  (fun h => pfree_nAnd h (ih3 rest a N hXr))
            | fls => exact pfree_nBot
            | or _ _ => exact pfree_nBot
            | down M =>
                cases M with
                | up _ => exact pfree_nBot
                | and _ _ => exact pfree_nBot
                | imp Q' N' =>
                    exact pfree_nAnd (ih2 rest Q' N' N hXr) (ih1 rest Q' N' N hXr)
        | and _ _ => exact pfree_nBot
end LJF

/-! ## The contract that remains

With `interp` total and `interp_pfree` proved, the components of the Σ-type
are in place: the formula, built by the clauses, and its `p`-freeness.  The
characteristic properties are the remaining obligations, stated as the
contract for the next stretch — all four internal to `LJF`, none touching
another calculus:

* **(E1) soundness of `∃p`**:
  `Inv (todo ++ done) [] (interp p todo done none)`
* **(A1) soundness of `∀p`**:
  `Inv (interp p todo done (some G) :: todo ++ done) [] G`
* **(E2) minimality of `∃p`**: for `p`-free `Δ` and `ψ`,
  `Inv (todo ++ done ++ Δ) [] ψ  →  Inv (interp p todo done none :: Δ) [] ψ`
* **(A2) minimality of `∀p`**: for `p`-free `Δ`,
  `Inv (todo ++ done ++ Δ) [] G  →
     Inv (interp p todo done none :: Δ) [] (interp p todo done (some G))`

The toolkit they need, also internal: a hypothesis-simulation traversal
(replace uses of one hypothesis by a derived simulator — powers E1/A1 and the
easy inversion directions of E2/A2), and branch extraction
(`Inv Δ (P :: Ω) C → ∀ b ∈ invertPos P, Inv (b ++ Δ) Ω C`, from the
determinism of the inversion phase).  The one expected mountain is the
`E2`/`A2` case for the Dyckhoff implication — the focused form of the
`(A⊃B)⊃C` argument; if it resists, it is to be carried as an explicit
hypothesis, never a `sorry`. -/

namespace LJF

/-! # Part 3: the toolkit for the characteristic properties

Six tools, each internal to `LJF`, each structural, none using cut:

* `routeStab` — CPS re-targeting of a stable proof of a positive `P`: every
  right focus on `P` is handed to a continuation, every left-focus chain and
  goal-side inversion is rebuilt with the new target.  Its instances do the
  work classically assigned to cut: shift release, disjunction routing,
  ex falso from a provable `⊥`.
* `invBranches` — realise `invertPos` on the left: branch derivations
  assemble into the inversion of the positive.
* `extract` — the converse, at any position of `Ω`: the inversion phase is
  deterministic, so a pending positive can be replayed along any one branch.
* `stableFire` — fire a shifted hypothesis `↑R` at a stable sequent, given
  stable continuations for every branch of `R`.
* `upMerge` — eliminate a shifted hypothesis into a negative goal, by
  recursion on the goal; the leaf case is `stableFire`.
* `simStab` — hypothesis simulation: replace every use of one hypothesis
  `H` by derivations manufactured on the other side.  The `init` uses of an
  atomic `H` reduce to left-focus uses via `idPos`, so one handler covers
  everything.
-/

/-! ## Routing a positive conclusion -/

mutual

/-- Re-target a stable proof: any right focus on `P` is passed to `k`. -/
def routeStab {Δ₀ : List Neg} {P P₀ : Pos}
    (k : ∀ {Δ' : List Neg}, Sub Δ₀ Δ' → RFocus Δ' P → Stab Δ' P₀) :
    ∀ {Δ : List Neg}, Sub Δ₀ Δ → Stab Δ P → Stab Δ P₀
  | _, hs, .rfoc r => k hs r
  | _, hs, .lfoc h lf => .lfoc h (routeLFoc k hs lf)

/-- Re-target below a left focus. -/
def routeLFoc {Δ₀ : List Neg} {P P₀ : Pos}
    (k : ∀ {Δ' : List Neg}, Sub Δ₀ Δ' → RFocus Δ' P → Stab Δ' P₀) :
    ∀ {Δ : List Neg} {H : Neg}, Sub Δ₀ Δ → LFoc Δ H P → LFoc Δ H P₀
  | _, _, hs, .rel d => .rel (routeInv k hs d)
  | _, _, hs, .impL s lf => .impL s (routeLFoc k hs lf)
  | _, _, hs, .and1 lf => .and1 (routeLFoc k hs lf)
  | _, _, hs, .and2 lf => .and2 (routeLFoc k hs lf)

/-- Re-target through the inversion of a released antecedent.  The goal is a
shift, so `impR`/`andR` cannot occur and the traversal is total. -/
def routeInv {Δ₀ : List Neg} {P P₀ : Pos}
    (k : ∀ {Δ' : List Neg}, Sub Δ₀ Δ' → RFocus Δ' P → Stab Δ' P₀) :
    ∀ {Δ : List Neg} {Ω : List Pos}, Sub Δ₀ Δ →
      Inv Δ Ω (.up P) → Inv Δ Ω (.up P₀)
  | _, _, hs, .stable s => .stable (routeStab k hs s)
  | _, _, hs, .orL d₁ d₂ => .orL (routeInv k hs d₁) (routeInv k hs d₂)
  | _, _, _, .flsL => .flsL
  | _, _, hs, .downL d => .downL (routeInv k (hs.trans (Sub.grow _)) d)
  | _, _, hs, .atomL d => .atomL (routeInv k (hs.trans (Sub.grow _)) d)

end

/-- Disjunction introduction at the stable level, left side. -/
def stabOr1 {Δ : List Neg} {A B : Pos} (s : Stab Δ A) : Stab Δ (.or A B) :=
  routeStab (Δ₀ := Δ) (fun _ r => .rfoc (.or1 r)) (Sub.refl Δ) s

/-- Disjunction introduction at the stable level, right side. -/
def stabOr2 {Δ : List Neg} {A B : Pos} (s : Stab Δ B) : Stab Δ (.or A B) :=
  routeStab (Δ₀ := Δ) (fun _ r => .rfoc (.or2 r)) (Sub.refl Δ) s

/-! ## Forced-shape extractors -/

/-- An inversion with empty `Ω` and shifted goal must be `stable`. -/
def unStable {Δ : List Neg} {P : Pos} : Inv Δ [] (.up P) → Stab Δ P
  | .stable s => s

/-- A right focus on a shift must be `rel`. -/
def relOf {Δ : List Neg} {M : Neg} : RFocus Δ (.down M) → Inv Δ [] M
  | .rel d => d

/-- An inversion with empty `Ω` and implication goal must be `impR`. -/
def impROf {Δ : List Neg} {Q : Pos} {N : Neg} :
    Inv Δ [] (.imp Q N) → Inv Δ [Q] N
  | .impR d => d

/-- An inversion with empty `Ω` and conjunction goal must be `andR`: left. -/
def andROf1 {Δ : List Neg} {M N : Neg} : Inv Δ [] (.and M N) → Inv Δ [] M
  | .andR d _ => d

/-- Right. -/
def andROf2 {Δ : List Neg} {M N : Neg} : Inv Δ [] (.and M N) → Inv Δ [] N
  | .andR _ e => e

/-! ## Realising and replaying the inversion of a positive -/

/-- Branch derivations assemble into the inversion of the positive. -/
def invBranches : ∀ (R : Pos) {Γ : List Neg} {Ω : List Pos} {N : Neg},
    (∀ b ∈ invertPos R, Inv (b ++ Γ) Ω N) → Inv Γ (R :: Ω) N
  | .atom a, _, _, _, h =>
      .atomL (h [.up (.atom a)] (by simp [invertPos]))
  | .fls, _, _, _, _ => .flsL
  | .or P Q, _, _, _, h =>
      .orL (invBranches P (fun b hb =>
              h b (by simp only [invertPos, List.mem_append]; exact .inl hb)))
           (invBranches Q (fun b hb =>
              h b (by simp only [invertPos, List.mem_append]; exact .inr hb)))
  | .down M, _, _, _, h => .downL (h [M] (by simp [invertPos]))
termination_by R => sizePos R
decreasing_by all_goals (simp_wf; simp only [sizePos]; omega)

/-- **Replay along a branch.**  A pending positive anywhere in `Ω` can be
extracted along any one branch of its inversion — the inversion phase is
deterministic, so the derivation already contains that branch. -/
def extract : ∀ {Γ : List Neg} (Ω₁ : List Pos) {R : Pos} {Ω₂ : List Pos}
    {C : Neg}, Inv Γ (Ω₁ ++ R :: Ω₂) C →
    ∀ b ∈ invertPos R, Inv (b ++ Γ) (Ω₁ ++ Ω₂) C
  -- extraction point at the head
  | _, [], .atom a, _, _, .atomL d, b, hb => by
      simp only [invertPos, List.mem_singleton] at hb; subst hb; exact d
  | _, [], .fls, _, _, .flsL, b, hb => by simp [invertPos] at hb
  | _, [], .or P Q, _, _, .orL d₁ d₂, b, hb =>
      if hP : b ∈ invertPos P then extract [] d₁ b hP
      else extract [] d₂ b (by
        simp only [invertPos, List.mem_append] at hb
        exact hb.resolve_left hP)
  | _, [], .down M, _, _, .downL d, b, hb => by
      simp only [invertPos, List.mem_singleton] at hb; subst hb; exact d
  -- goal rules commute past the extraction point
  | _, [], _, _, _, .impR d, b, hb => .impR (extract [_] d b hb)
  | _, [], _, _, _, .andR d e, b, hb => .andR (extract [] d b hb) (extract [] e b hb)
  | _, S :: Ω₁, _, _, _, .impR d, b, hb => .impR (extract (_ :: S :: Ω₁) d b hb)
  | _, S :: Ω₁, _, _, _, .andR d e, b, hb =>
      .andR (extract (S :: Ω₁) d b hb) (extract (S :: Ω₁) e b hb)
  -- left rules on the head of `Ω₁` are rebuilt
  | _, .or _ _ :: Ω₁, _, _, _, .orL d₁ d₂, b, hb =>
      .orL (extract (_ :: Ω₁) d₁ b hb) (extract (_ :: Ω₁) d₂ b hb)
  | _, .fls :: _, _, _, _, .flsL, _, _ => .flsL
  | _, .down M :: Ω₁, _, _, _, .downL d, b, hb =>
      (extract Ω₁ d b hb).wk (fun X hX => by
        rcases List.mem_append.mp hX with hX | hX
        · exact List.mem_cons_of_mem _ (List.mem_append_left _ hX)
        · rcases List.mem_cons.mp hX with rfl | hX
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (List.mem_append_right _ hX))
      |> Inv.downL
  | _, .atom a :: Ω₁, _, _, _, .atomL d, b, hb =>
      (extract Ω₁ d b hb).wk (fun X hX => by
        rcases List.mem_append.mp hX with hX | hX
        · exact List.mem_cons_of_mem _ (List.mem_append_left _ hX)
        · rcases List.mem_cons.mp hX with rfl | hX
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (List.mem_append_right _ hX))
      |> Inv.atomL

end LJF

namespace LJF

/-! ## Firing a shifted hypothesis, and merging its branches -/

/-- Fire `↑R ∈ Δ` at a stable sequent: stable continuations for every branch
of `R` assemble into one stable proof. -/
def stableFire {Δ : List Neg} {R : Pos} {P₀ : Pos} (h : Neg.up R ∈ Δ)
    (s : ∀ b ∈ invertPos R, Stab (b ++ Δ) P₀) : Stab Δ P₀ :=
  .lfoc h (.rel (invBranches R (fun b hb => .stable (s b hb))))

/-- **Eliminate a shifted hypothesis into a negative goal.**  By recursion on
the goal: implications invert their antecedent (`invBranches`) and push the
branch family through (`extract` + reordering), conjunctions project, and at
a shifted goal the hypothesis fires (`stableFire`).  This subsumes ex falso
(`R = ⊥`: the branch family is vacuous), disjunction elimination, and the
inversion of a shifted hypothesis. -/
def upMerge : ∀ (G : Neg) {Γ : List Neg} {R : Pos}, Neg.up R ∈ Γ →
    (∀ b ∈ invertPos R, Inv (b ++ Γ) [] G) → Inv Γ [] G
  | .imp Q N, Γ, R, h, D =>
      .impR (invBranches Q (fun c hc =>
        upMerge N (List.mem_append_right c h) (fun b hb =>
          (extract [] (impROf (D b hb)) c hc).wk (fun X hX => by
            rcases List.mem_append.mp hX with hX | hX
            · exact List.mem_append_right _ (List.mem_append_left _ hX)
            · rcases List.mem_append.mp hX with hX | hX
              · exact List.mem_append_left _ hX
              · exact List.mem_append_right _ (List.mem_append_right _ hX)))))
  | .and M N, _, _, h, D =>
      .andR (upMerge M h (fun b hb => andROf1 (D b hb)))
            (upMerge N h (fun b hb => andROf2 (D b hb)))
  | .up P, _, _, h, D =>
      .stable (stableFire h (fun b hb => unStable (D b hb)))

/-! ## Hypothesis simulation

Replace every use of one hypothesis `H` by material manufactured on the
target side.  A use is either a left focus on `H` — handled by `fl` — or, for
atomic `H`, an `init`; the latter reduces to the former through `idPos`, so
`fl` alone suffices. -/

theorem memBoth {H M : Neg} {Γ Δ : List Neg}
    (hm : ∀ X, X ∈ Γ → X = H ∨ X ∈ Δ) :
    ∀ X, X ∈ M :: Γ → X = H ∨ X ∈ M :: Δ := by
  intro X hX
  rcases List.mem_cons.mp hX with rfl | hX
  · exact .inr (List.mem_cons_self ..)
  · exact (hm X hX).imp id (List.mem_cons_of_mem _)

mutual

/-- Simulation at a stable sequent. -/
def simStab {H : Neg} {Δ₀ : List Neg}
    (fl : ∀ {Δ' : List Neg} {P : Pos}, Sub Δ₀ Δ' → LFoc Δ' H P → Stab Δ' P) :
    ∀ {Γ Δ : List Neg} {P : Pos}, (∀ X, X ∈ Γ → X = H ∨ X ∈ Δ) →
      Sub Δ₀ Δ → Stab Γ P → Stab Δ P
  | _, _, _, hm, hs, .rfoc r => simRFocus fl hm hs r
  | _, _, _, hm, hs, @Stab.lfoc _ _ N h lf =>
      if e : N = H then fl hs (e ▸ simLFoc fl hm hs lf)
      else .lfoc ((hm _ h).resolve_left e) (simLFoc fl hm hs lf)

/-- Simulation under right focus.  Returns a stable proof, because an `init`
use of an atomic `H` must be re-routed through `fl` (via `idPos`), and that
produces a stable proof, not a focus. -/
def simRFocus {H : Neg} {Δ₀ : List Neg}
    (fl : ∀ {Δ' : List Neg} {P : Pos}, Sub Δ₀ Δ' → LFoc Δ' H P → Stab Δ' P) :
    ∀ {Γ Δ : List Neg} {P : Pos}, (∀ X, X ∈ Γ → X = H ∨ X ∈ Δ) →
      Sub Δ₀ Δ → RFocus Γ P → Stab Δ P
  | _, _, _, hm, hs, @RFocus.init _ a h =>
      if e : Neg.up (.atom a) = H then fl hs (e ▸ LFoc.rel (idPos (.atom a) _))
      else .rfoc (.init ((hm _ h).resolve_left e))
  | _, _, _, hm, hs, .or1 r => stabOr1 (simRFocus fl hm hs r)
  | _, _, _, hm, hs, .or2 r => stabOr2 (simRFocus fl hm hs r)
  | _, _, _, hm, hs, .rel d => .rfoc (.rel (simInv fl hm hs d))

/-- Simulation under a left focus on some other hypothesis. -/
def simLFoc {H : Neg} {Δ₀ : List Neg}
    (fl : ∀ {Δ' : List Neg} {P : Pos}, Sub Δ₀ Δ' → LFoc Δ' H P → Stab Δ' P) :
    ∀ {Γ Δ : List Neg} {H' : Neg} {P : Pos}, (∀ X, X ∈ Γ → X = H ∨ X ∈ Δ) →
      Sub Δ₀ Δ → LFoc Γ H' P → LFoc Δ H' P
  | _, _, _, _, hm, hs, .rel d => .rel (simInv fl hm hs d)
  | _, _, _, _, hm, hs, .impL s lf =>
      .impL (simStab fl hm hs s) (simLFoc fl hm hs lf)
  | _, _, _, _, hm, hs, .and1 lf => .and1 (simLFoc fl hm hs lf)
  | _, _, _, _, hm, hs, .and2 lf => .and2 (simLFoc fl hm hs lf)

/-- Simulation through inversion. -/
def simInv {H : Neg} {Δ₀ : List Neg}
    (fl : ∀ {Δ' : List Neg} {P : Pos}, Sub Δ₀ Δ' → LFoc Δ' H P → Stab Δ' P) :
    ∀ {Γ Δ : List Neg} {Ω : List Pos} {C : Neg},
      (∀ X, X ∈ Γ → X = H ∨ X ∈ Δ) → Sub Δ₀ Δ → Inv Γ Ω C → Inv Δ Ω C
  | _, _, _, _, hm, hs, .impR d => .impR (simInv fl hm hs d)
  | _, _, _, _, hm, hs, .andR d e =>
      .andR (simInv fl hm hs d) (simInv fl hm hs e)
  | _, _, _, _, hm, hs, .stable s => .stable (simStab fl hm hs s)
  | _, _, _, _, hm, hs, .orL d₁ d₂ =>
      .orL (simInv fl hm hs d₁) (simInv fl hm hs d₂)
  | _, _, _, _, _, _, .flsL => .flsL
  | _, _, _, _, hm, hs, .downL d =>
      .downL (simInv fl (memBoth hm) (hs.trans (Sub.grow _)) d)
  | _, _, _, _, hm, hs, .atomL d =>
      .atomL (simInv fl (memBoth hm) (hs.trans (Sub.grow _)) d)

end

/-- The common instantiation: strip the head hypothesis, simulating its
uses. -/
def simHyp {H : Neg} {Γ Δ₀ : List Neg} {C : Neg}
    (fl : ∀ {Δ' : List Neg} {P : Pos}, Sub Δ₀ Δ' → LFoc Δ' H P → Stab Δ' P)
    (hΓ : Sub Γ Δ₀) (d : Inv (H :: Γ) [] C) : Inv Δ₀ [] C :=
  simInv fl (fun X hX => (List.mem_cons.mp hX).imp id (hΓ X)) (Sub.refl Δ₀) d

/-! ## Interpolant-connective introductions and eliminations -/

/-- `⊤` needs nothing. -/
def nTopIntro {Γ : List Neg} : Inv Γ [] nTop := .impR .flsL

/-- Conjunction of a list, introduction. -/
def nAndAllIntro : ∀ {l : List Neg} {Γ : List Neg},
    (∀ x ∈ l, Inv Γ [] x) → Inv Γ [] (nAndAll l)
  | [], _, _ => nTopIntro
  | x :: l, _, h =>
      .andR (h x (List.mem_cons_self ..))
        (nAndAllIntro (fun y hy => h y (List.mem_cons_of_mem _ hy)))

/-- Focused projection out of a list conjunction. -/
def lfocAndAll : ∀ {l : List Neg} {x : Neg} {Δ : List Neg} {P : Pos},
    x ∈ l → LFoc Δ x P → LFoc Δ (nAndAll l) P
  | y :: l, x, _, _, hx, lf =>
      if e : x = y then .and1 (e ▸ lf)
      else .and2 (lfocAndAll (by
        rcases List.mem_cons.mp hx with rfl | hx
        · exact absurd rfl e
        · exact hx) lf)

/-- Disjunction of a list, introduction at a member. -/
def nOrAllIntro : ∀ {l : List Neg} {x : Neg} {Γ : List Neg},
    x ∈ l → Inv Γ [] x → Inv Γ [] (nOrAll l)
  | y :: l, x, _, hx, d =>
      if e : x = y then .stable (.rfoc (.or1 (.rel (e ▸ d))))
      else .stable (.rfoc (.or2 (.rel (nOrAllIntro (by
        rcases List.mem_cons.mp hx with rfl | hx
        · exact absurd rfl e
        · exact hx) d))))

/-- Disjunction of a list, elimination: a case per member. -/
def nOrAllElim : ∀ {l : List Neg} {Γ : List Neg} (G : Neg), nOrAll l ∈ Γ →
    (∀ x ∈ l, ∀ {Γ' : List Neg}, Sub Γ Γ' → Inv (x :: Γ') [] G) → Inv Γ [] G
  | [], _, G, h, _ =>
      upMerge G (R := .fls) h (fun b hb => by simp [invertPos] at hb)
  | x :: l, Γ, G, h, D =>
      upMerge G h (fun b hb =>
        if e : b = [x] then
          e ▸ (D x (List.mem_cons_self ..) (Sub.refl _) |>.wk
            (fun Y hY => by
              rcases List.mem_cons.mp hY with rfl | hY
              · exact List.mem_append_left _ (List.mem_cons_self ..)
              · exact List.mem_append_right _ hY))
        else by
          have hb' : b = [nOrAll l] := by
            simp only [invertPos, List.mem_append, List.mem_singleton] at hb
            exact hb.resolve_left e
          subst hb'
          exact nOrAllElim G (List.mem_append_left _ (List.mem_cons_self ..))
            (fun y hy _ hs => D y (List.mem_cons_of_mem _ hy)
              (fun Z hZ => hs Z (List.mem_cons_of_mem _ hZ))))

/-- A `true` `atomMem` is a membership. -/
theorem atomMem_mem {a : String} {Γ : List Neg} (h : atomMem a Γ = true) :
    Neg.up (.atom a) ∈ Γ := by
  simp only [atomMem, List.any_eq_true] at h
  obtain ⟨x, hx, he⟩ := h
  match x, he with
  | .up (.atom b), he =>
      have : a = b := by simpa [BEq.comm] using he
      subst this; exact hx

end LJF
