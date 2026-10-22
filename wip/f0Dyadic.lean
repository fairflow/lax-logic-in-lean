import wip.f0Indep
import Meta.Audit

/-!
# The dyadic rationals embed in F0

**The theorem** (`dyadic_embedding`, `dyadic_vf`).  There is a map `f` from the
dyadic rationals in `[0, 1]` to variable-free PLL formulas with

    d < d'  ⟹  f d ⊢ f d'  and  f d' ⊬ f d,

`f 0 = ⊥` and `f 1 = ⊤` (`formula_zero`, `formula_one`).  So F0 contains a
chain order-isomorphic to the dyadics in `[0, 1]`, hence (`wip/f0Rat.lean`) a
copy of ℚ.  Pins `[propext, Quot.sound]`.

## The construction

Lattice polynomials over ℕ (`LPoly`: variables, `⊥`, `⊤`, `∧`, `∨`), with
variable `n` read as the odd gap `g(2n+1)` (`LPoly.den`).  The dyadic
`m / 2^n` is `F n m`:

    F 0 0 = ⊥,   F 0 1 = ⊤,
    F (n+1) (2k)   = F n k,
    F (n+1) (2k+1) = F n k ∨ (F n (k+1) ∧ x(n+1, 2k+1)),

the variable `x(n, m) = 2^n + m` being used nowhere else (`idx`; injective on
`m < 2^n`, and decoded by `Nat.log2`).  This is `f(d) = f(a) ∨ (f(b) ∧ x_d)`
for `d = (2k+1)/2^(n+1)` between its neighbours `a = k/2^n`, `b = (k+1)/2^n`.

## The two lemmas behind strictness

    p true at the assignment σ, S ⊇ the true variables of p    ⟹  ⋀_{i∈S} g(2i+1) ⊢ ⟦p⟧
    p false at σ, T ⊇ the false variables of p                  ⟹  ⟦p⟧ ⊢ ⋁_{j∈T} g(2j+1)

(`true_entails`, `false_entails`); with `indep` they give `separate`: if `p`
is true and `q` false at some assignment, then `⟦p⟧ ⊬ ⟦q⟧`.

**Monotonicity** (`F_step`, `F_mono`) is lattice reasoning on the recursion.
**Strictness** (`F_sep`) uses the threshold assignment `thr C N`, under which
`x(n, m)` is true iff `m/2^n ≥ C/2^N`; by induction on the level, `F n m` is
then true iff `m/2^n ≥ C/2^N` (`F_eval`), so for `m < m'` the threshold
`m'/2^N` makes `F N m'` true and `F N m` false.
-/

open PLLFormula

namespace PLLND
namespace F0

open SemUI RNEmbed
open PLLND.LaxInfinite (atomFree)

/-! ## Variable-freeness of the gaps

Copies of `rnSub_atomFree`/`gap_atomFree` (`wip/uiObstruct.lean`, which is
not imported here). -/

theorem rnP_vf :
    ∀ k, atomFree (embed (rnP k).1) = true ∧ atomFree (embed (rnP k).2) = true := by
  intro k
  induction k with
  | zero => exact ⟨by decide, by decide⟩
  | succ k ih =>
      obtain ⟨h1, h2⟩ := ih
      constructor
      · show (atomFree (embed (rnP k).1) && atomFree (embed (rnP k).2)) = true
        rw [h1, h2]
        rfl
      · show ((atomFree (embed (rnP k).1) && atomFree (embed (rnP k).2)) &&
            atomFree (embed (rnP k).1)) = true
        rw [h1, h2]
        rfl

theorem rnSub_vf (n : Nat) : atomFree (rnSub n) = true := by
  match n with
  | 0 => rfl
  | m + 1 =>
      show atomFree (embed (if m % 2 = 0 then (rnP (m / 2)).1
        else (rnP (m / 2)).2)) = true
      split
      · exact (rnP_vf _).1
      · exact (rnP_vf _).2

theorem gap_vf (k : Nat) : atomFree (gap k) = true := by
  show (atomFree (chainF k) && atomFree (rnSub (2 * k + 1))) = true
  rw [show atomFree (chainF k) = true from rnSub_vf _, rnSub_vf]
  rfl

/-! ## Lattice polynomials -/

/-- Lattice polynomials over ℕ. -/
inductive LPoly where
  | var (n : Nat)
  | bot
  | top
  | and (p q : LPoly)
  | or (p q : LPoly)

namespace LPoly

/-- Evaluation at a Boolean assignment. -/
def eval (σ : Nat → Bool) : LPoly → Bool
  | var n => σ n
  | bot => false
  | top => true
  | and p q => p.eval σ && q.eval σ
  | or p q => p.eval σ || q.eval σ

/-- The variables. -/
def vars : LPoly → List Nat
  | var n => [n]
  | bot => []
  | top => []
  | and p q => p.vars ++ q.vars
  | or p q => p.vars ++ q.vars

/-- The interpretation in F0: variable `n` is the odd gap `g(2n+1)`. -/
def den : LPoly → PLLFormula
  | var n => gap (2 * n + 1)
  | bot => .falsePLL
  | top => .ifThen .falsePLL .falsePLL
  | and p q => .and p.den q.den
  | or p q => .or p.den q.den

/-- Every interpretation is variable-free. -/
theorem den_vf : ∀ p : LPoly, atomFree p.den = true
  | var n => gap_vf _
  | bot => rfl
  | top => rfl
  | and p q => by
      show (atomFree p.den && atomFree q.den) = true
      rw [den_vf p, den_vf q]
      rfl
  | or p q => by
      show (atomFree p.den && atomFree q.den) = true
      rw [den_vf p, den_vf q]
      rfl

end LPoly

open LPoly

theorem band_true : ∀ {a b : Bool}, (a && b) = true → a = true ∧ b = true
  | true, true, _ => ⟨rfl, rfl⟩
  | false, _, h => nomatch h
  | true, false, h => nomatch h

theorem bor_true : ∀ {a b : Bool}, (a || b) = true → a = true ∨ b = true
  | true, _, _ => Or.inl rfl
  | false, true, _ => Or.inr rfl
  | false, false, h => nomatch h

theorem band_false : ∀ {a b : Bool}, (a && b) = false → a = false ∨ b = false
  | false, _, _ => Or.inl rfl
  | true, false, _ => Or.inr rfl
  | true, true, h => nomatch h

theorem bor_false : ∀ {a b : Bool}, (a || b) = false → a = false ∧ b = false
  | false, false, _ => ⟨rfl, rfl⟩
  | true, _, h => nomatch h
  | false, true, h => nomatch h

/-! ## The two lemmas, and separation -/

/-- **True at σ ⟹ entailed by the true gaps.**  If every variable of `p` that
`σ` makes true lies in `S`, and `p` is true at `σ`, then
`⋀_{i∈S} g(2i+1) ⊢ ⟦p⟧`. -/
theorem true_entails (σ : Nat → Bool) (S : List Nat) :
    ∀ p : LPoly, (∀ n ∈ p.vars, σ n = true → n ∈ S) → p.eval σ = true →
      Deriv [bigAnd (S.map fun i => gap (2 * i + 1))] p.den
  | .var n, hS, hp =>
      Deriv.bigAndElim (List.mem_map.mpr ⟨n, hS n (List.mem_singleton_self n) hp, rfl⟩)
  | .bot, _, hp => nomatch hp
  | .top, _, _ => Deriv.impIntro (Deriv.iden (.head _))
  | .and p q, hS, hpq =>
      Deriv.andIntro
        (true_entails σ S p (fun n hn => hS n (List.mem_append_left _ hn)) (band_true hpq).1)
        (true_entails σ S q (fun n hn => hS n (List.mem_append_right _ hn)) (band_true hpq).2)
  | .or p q, hS, hpq =>
      (bor_true hpq).elim
        (fun h => Deriv.orIntro1
          (true_entails σ S p (fun n hn => hS n (List.mem_append_left _ hn)) h))
        (fun h => Deriv.orIntro2
          (true_entails σ S q (fun n hn => hS n (List.mem_append_right _ hn)) h))

/-- **False at σ ⟹ entails the false gaps.**  If every variable of `p` that
`σ` makes false lies in `T`, and `p` is false at `σ`, then
`⟦p⟧ ⊢ ⋁_{j∈T} g(2j+1)`. -/
theorem false_entails (σ : Nat → Bool) (T : List Nat) :
    ∀ p : LPoly, (∀ n ∈ p.vars, σ n = false → n ∈ T) → p.eval σ = false →
      Deriv [p.den] (PLLND.bigOr (T.map fun j => gap (2 * j + 1)))
  | .var n, hT, hp =>
      Deriv.bigOrIntroT (List.mem_map.mpr ⟨n, hT n (List.mem_singleton_self n) hp, rfl⟩)
  | .bot, _, _ => Deriv.falsoElim _ (Deriv.iden (.head _))
  | .top, _, hp => nomatch hp
  | .and p q, hT, hpq =>
      (band_false hpq).elim
        (fun h => Deriv.cutHead (Deriv.andElim1 (Deriv.iden (.head _)))
          (false_entails σ T p (fun n hn => hT n (List.mem_append_left _ hn)) h))
        (fun h => Deriv.cutHead (Deriv.andElim2 (Deriv.iden (.head _)))
          (false_entails σ T q (fun n hn => hT n (List.mem_append_right _ hn)) h))
  | .or p q, hT, hpq =>
      Deriv.orElim (Deriv.iden (.head _))
        (Deriv.toHead
          (false_entails σ T p (fun n hn => hT n (List.mem_append_left _ hn)) (bor_false hpq).1))
        (Deriv.toHead
          (false_entails σ T q (fun n hn => hT n (List.mem_append_right _ hn)) (bor_false hpq).2))

/-- **Separation.**  If `p` is true and `q` false at some assignment, then
`⟦p⟧ ⊬ ⟦q⟧` (by `indep`, with `S`/`T` the true/false variables of `p`, `q`). -/
theorem separate {p q : LPoly} (σ : Nat → Bool) (hp : p.eval σ = true)
    (hq : q.eval σ = false) : [p.den] ⊬ q.den := fun h =>
  indep ((p.vars ++ q.vars).filter σ) ((p.vars ++ q.vars).filter fun n => !σ n)
    (fun i hi hi' => by
      have h1 := (List.mem_filter.mp hi).2
      have h2 : (!σ i) = true := (List.mem_filter.mp hi').2
      rw [h1] at h2
      exact absurd h2 (by decide))
    (Deriv.cutHead
      (Deriv.cutHead
        (true_entails σ _ p
          (fun _ hn hσ => List.mem_filter.mpr ⟨List.mem_append_left _ hn, hσ⟩) hp)
        h)
      (false_entails σ _ q
        (fun n hn hσ => List.mem_filter.mpr ⟨List.mem_append_right _ hn,
          by show (!σ n) = true; rw [hσ]; rfl⟩) hq))

/-! ## The dyadic construction -/

/-- The fresh variable of the dyadic `m / 2^n` (`n ≥ 1`, `m` odd, `m < 2^n`). -/
def idx (n m : Nat) : Nat := 2 ^ n + m

/-- `F n m` is the polynomial of the dyadic `m / 2^n`. -/
def F : Nat → Nat → LPoly
  | 0, m => if m = 0 then .bot else .top
  | n + 1, m =>
      if m % 2 = 0 then F n (m / 2)
      else (F n (m / 2)).or ((F n (m / 2 + 1)).and (.var (idx (n + 1) m)))

theorem F_even (n k : Nat) : F (n + 1) (2 * k) = F n k := by
  show (if 2 * k % 2 = 0 then F n (2 * k / 2) else _) = F n k
  rw [if_pos (by omega), show 2 * k / 2 = k by omega]

theorem F_odd (n k : Nat) :
    F (n + 1) (2 * k + 1) =
      (F n k).or ((F n (k + 1)).and (.var (idx (n + 1) (2 * k + 1)))) := by
  show (if (2 * k + 1) % 2 = 0 then F n ((2 * k + 1) / 2)
    else (F n ((2 * k + 1) / 2)).or
      ((F n ((2 * k + 1) / 2 + 1)).and (.var (idx (n + 1) (2 * k + 1))))) = _
  rw [if_neg (by omega), show (2 * k + 1) / 2 = k by omega]

/-- A dyadic is the same polynomial at every finer level. -/
theorem F_lift (n m : Nat) : ∀ k, F (n + k) (m * 2 ^ k) = F n m
  | 0 => by rw [Nat.pow_zero, Nat.mul_one]; rfl
  | k + 1 => by
      have e : m * 2 ^ (k + 1) = 2 * (m * 2 ^ k) := by
        rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm (m * 2 ^ k) 2]
      show F (n + k + 1) (m * 2 ^ (k + 1)) = F n m
      rw [e, F_even]
      exact F_lift n m k

theorem two_pow_succ (n : Nat) : 2 ^ (n + 1) = 2 * 2 ^ n := by
  rw [Nat.pow_succ, Nat.mul_comm]

/-! ### Monotonicity -/

/-- One step up a level: `F n m ⊢ F n (m+1)`. -/
theorem F_step : ∀ n m, m < 2 ^ n → Deriv [(F n m).den] (F n (m + 1)).den := by
  intro n
  induction n with
  | zero =>
      intro m hm
      have h1 : (2 : Nat) ^ 0 = 1 := rfl
      have hm0 : m = 0 := by omega
      subst hm0
      exact Deriv.falsoElim _ (Deriv.iden (.head _))
  | succ n ih =>
      intro m hm
      have hpow := two_pow_succ n
      obtain ⟨k, rfl | rfl⟩ : ∃ k, m = 2 * k ∨ m = 2 * k + 1 := ⟨m / 2, by omega⟩
      · rw [F_even, F_odd]
        exact Deriv.orIntro1 (Deriv.iden (.head _))
      · have e : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
        rw [F_odd, e, F_even]
        exact Deriv.orElim (Deriv.iden (.head _))
          (Deriv.toHead (ih k (by omega)))
          (Deriv.toHead (Deriv.andElim1 (Deriv.iden (.head _))))

/-- **Monotonicity**: `F n m ⊢ F n (m + d)` up to `2^n`. -/
theorem F_mono (n m : Nat) : ∀ d, m + d ≤ 2 ^ n → Deriv [(F n m).den] (F n (m + d)).den
  | 0, _ => Deriv.iden (.head _)
  | d + 1, h => Deriv.cutHead (F_mono n m d (by omega)) (F_step n (m + d) (by omega))

/-! ### Strictness: the threshold assignment -/

/-- The threshold assignment for `C / 2^N`: the variable `x(n, m)` is true iff
`m / 2^n ≥ C / 2^N`. -/
def thr (C N : Nat) (i : Nat) : Bool :=
  decide (C * 2 ^ Nat.log2 i ≤ (i - 2 ^ Nat.log2 i) * 2 ^ N)

theorem log2_idx (n m : Nat) (hm : m < 2 ^ n) : Nat.log2 (idx n m) = n := by
  have hpos := Nat.two_pow_pos n
  have hne : idx n m ≠ 0 := by unfold idx; omega
  apply Nat.le_antisymm
  · have h := (Nat.log2_lt hne).mpr
      (show idx n m < 2 ^ (n + 1) by unfold idx; rw [two_pow_succ]; omega)
    omega
  · exact (Nat.le_log2 hne).mpr (by unfold idx; omega)

theorem thr_idx (C N n m : Nat) (hm : m < 2 ^ n) :
    thr C N (idx n m) = decide (C * 2 ^ n ≤ m * 2 ^ N) := by
  unfold thr
  rw [log2_idx n m hm]
  unfold idx
  rw [Nat.add_sub_cancel_left]

/-- The Boolean step of `F_eval`: with `a = k·2^N`, `X = 2^N`, `Y = C·2^n`,
`[a ≥ Y] ∨ ([a+X ≥ Y] ∧ [2a+X ≥ 2Y]) = [2a+X ≥ 2Y]`. -/
theorem thresh_step (a X Y : Nat) :
    (decide (Y ≤ a) || (decide (Y ≤ a + X) && decide (2 * Y ≤ 2 * a + X))) =
      decide (2 * Y ≤ 2 * a + X) := by
  by_cases h1 : Y ≤ a
  · have h3 : 2 * Y ≤ 2 * a + X := by omega
    rw [decide_eq_true h1, decide_eq_true h3]
    rfl
  · by_cases h3 : 2 * Y ≤ 2 * a + X
    · have h2 : Y ≤ a + X := by omega
      rw [decide_eq_false h1, decide_eq_true h2, decide_eq_true h3]
      rfl
    · rw [decide_eq_false h1, decide_eq_false h3, Bool.and_false]
      rfl

/-- **Under the threshold `C / 2^N`, `F n m` is true iff `m/2^n ≥ C/2^N`.** -/
theorem F_eval (C N : Nat) (hC0 : 0 < C) (hCN : C ≤ 2 ^ N) :
    ∀ n m, m ≤ 2 ^ n → (F n m).eval (thr C N) = decide (C * 2 ^ n ≤ m * 2 ^ N) := by
  intro n
  induction n with
  | zero =>
      intro m hm
      have h1 : (2 : Nat) ^ 0 = 1 := rfl
      rcases Nat.lt_or_ge m 1 with h | h
      · have hm0 : m = 0 := by omega
        subst hm0
        show false = decide (C * 2 ^ 0 ≤ 0 * 2 ^ N)
        rw [h1, Nat.mul_one, Nat.zero_mul]
        exact (decide_eq_false (by omega)).symm
      · have hm1 : m = 1 := by omega
        subst hm1
        show true = decide (C * 2 ^ 0 ≤ 1 * 2 ^ N)
        rw [h1, Nat.mul_one, Nat.one_mul]
        exact (decide_eq_true hCN).symm
  | succ n ih =>
      intro m hm
      have hpow := two_pow_succ n
      have e3 : C * 2 ^ (n + 1) = 2 * (C * 2 ^ n) := by
        rw [hpow, ← Nat.mul_assoc, Nat.mul_comm C 2, Nat.mul_assoc]
      obtain ⟨k, rfl | rfl⟩ : ∃ k, m = 2 * k ∨ m = 2 * k + 1 := ⟨m / 2, by omega⟩
      · rw [F_even, ih k (by omega)]
        apply decide_eq_decide.mpr
        rw [e3, show 2 * k * 2 ^ N = 2 * (k * 2 ^ N) from Nat.mul_assoc 2 k _]
        constructor
        · intro h; omega
        · intro h; omega
      · rw [F_odd]
        show ((F n k).eval (thr C N) ||
            ((F n (k + 1)).eval (thr C N) && thr C N (idx (n + 1) (2 * k + 1)))) = _
        rw [ih k (by omega), ih (k + 1) (by omega),
          thr_idx C N (n + 1) (2 * k + 1) (by rw [hpow]; omega)]
        have e1 : (k + 1) * 2 ^ N = k * 2 ^ N + 2 ^ N := Nat.succ_mul k (2 ^ N)
        have e2 : (2 * k + 1) * 2 ^ N = 2 * (k * 2 ^ N) + 2 ^ N := by
          rw [Nat.succ_mul, Nat.mul_assoc]
        rw [e1, e2, e3]
        exact thresh_step _ _ _

/-- **Strictness**: for `m < m' ≤ 2^N`,  `F N m' ⊬ F N m`. -/
theorem F_sep (N m m' : Nat) (h : m < m') (h' : m' ≤ 2 ^ N) :
    [(F N m').den] ⊬ (F N m).den :=
  separate (thr m' N)
    (by
      rw [F_eval m' N (by omega) h' N m' h']
      exact decide_eq_true (Nat.le_refl _))
    (by
      rw [F_eval m' N (by omega) h' N m (by omega)]
      exact decide_eq_false fun hc => Nat.lt_irrefl _
        (Nat.lt_of_le_of_lt hc (Nat.mul_lt_mul_of_pos_right h (Nat.two_pow_pos N))))

/-! ## The dyadics -/

/-- A dyadic rational `num / 2^exp` in `[0, 1]`. -/
structure Dy where
  num : Nat
  exp : Nat
  le : num ≤ 2 ^ exp

namespace Dy

/-- The order of the values: `num/2^exp < num'/2^exp'`. -/
def lt (d d' : Dy) : Prop := d.num * 2 ^ d'.exp < d'.num * 2 ^ d.exp

/-- `f d`, the formula of the dyadic `d`. -/
def formula (d : Dy) : PLLFormula := (F d.exp d.num).den

end Dy

/-- `f 0 = ⊥`. -/
theorem formula_zero : (⟨0, 0, Nat.zero_le _⟩ : Dy).formula = .falsePLL := rfl

/-- `f 1 = ⊤`. -/
theorem formula_one : (⟨1, 0, Nat.le_refl _⟩ : Dy).formula = .ifThen .falsePLL .falsePLL := rfl

/-- **Every `f d` is variable-free.** -/
theorem dyadic_vf (d : Dy) : atomFree d.formula = true := LPoly.den_vf _

/-- **The dyadic rationals in `[0, 1]` embed in F0, strictly**:

    d < d'  ⟹  f d ⊢ f d'  ∧  f d' ⊬ f d. -/
theorem dyadic_embedding (d d' : Dy) (h : d.lt d') :
    Deriv [d.formula] d'.formula ∧ ([d'.formula] ⊬ d.formula) := by
  have e1 : F (d.exp + d'.exp) (d.num * 2 ^ d'.exp) = F d.exp d.num := F_lift _ _ _
  have e2 : F (d.exp + d'.exp) (d'.num * 2 ^ d.exp) = F d'.exp d'.num := by
    rw [Nat.add_comm]
    exact F_lift _ _ _
  have hle : d'.num * 2 ^ d.exp ≤ 2 ^ (d.exp + d'.exp) := by
    rw [Nat.pow_add, Nat.mul_comm (2 ^ d.exp)]
    exact Nat.mul_le_mul_right _ d'.le
  have h' : d.num * 2 ^ d'.exp < d'.num * 2 ^ d.exp := h
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt h')
  unfold Dy.formula
  rw [← e1, ← e2]
  refine ⟨?_, F_sep _ _ _ h' hle⟩
  rw [hr]
  exact F_mono _ _ r (hr ▸ hle)

end F0
end PLLND

#axioms_within PLLND.F0.LPoly.den_vf [propext, Quot.sound]
#axioms_within PLLND.F0.true_entails [propext, Quot.sound]
#axioms_within PLLND.F0.false_entails [propext, Quot.sound]
#axioms_within PLLND.F0.separate [propext, Quot.sound]
#axioms_within PLLND.F0.F_lift [propext, Quot.sound]
#axioms_within PLLND.F0.F_step [propext, Quot.sound]
#axioms_within PLLND.F0.F_mono [propext, Quot.sound]
#axioms_within PLLND.F0.thr_idx [propext, Quot.sound]
#axioms_within PLLND.F0.F_eval [propext, Quot.sound]
#axioms_within PLLND.F0.F_sep [propext, Quot.sound]
#axioms_within PLLND.F0.formula_zero [propext, Quot.sound]
#axioms_within PLLND.F0.formula_one [propext, Quot.sound]
#axioms_within PLLND.F0.dyadic_vf [propext, Quot.sound]
#axioms_within PLLND.F0.dyadic_embedding [propext, Quot.sound]
