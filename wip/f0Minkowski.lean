import wip.f0Dyadic
import Meta.Audit

/-!
# Minkowski's question-mark function: an explicit, choice-free `ℚ ↪ F0`

`wip/f0Rat.lean` embeds ℚ in F0 through Cantor's back-and-forth
(`Order.iso_of_countable_dense`), which carries `Classical.choice`.  This file
replaces it by an explicit map, built from Minkowski's `?`:

    rat_embedding_cf :  q < q'  ⟹  f' q ⊢ f' q'  ∧  f' q' ⊬ f' q,     f' q := (qm q).formula
    rat_vf_cf        :  atomFree (f' q) = true

with every theorem pinned `[propext, Quot.sound]` (one documented exception,
`rq_bridge`, below).  On the way:

    mink_lt    :  0 ≤ q < q' ≤ 1  ⟹  ?(q) < ?(q')
    mink_onto  :  0 < d < 1 dyadic  ⟹  ∃ q, 0 < q < 1 ∧ ?(q) = d
    qm_lt      :  q < q'  ⟹  qm q < qm q'
    qm_onto    :  0 < d < 1 dyadic  ⟹  ∃ q, qm q = d
    qm_inj     :  qm q = qm q'  ⟹  q = q'
    qm_eq_mink :  σ(q) = r  ⟹  qm q = ?(r)

(`=` on dyadics is equality of values, `eqv`), so `qm` is an explicit order
isomorphism from ℚ onto the dyadic rationals in `(0, 1)`.

## The construction

`?` on `(0, 1)` is the map sending the Stern–Brocot tree (mediants) to the
dyadic tree (midpoints), path for path.  On a pair `a / b` with `0 < a < b`
the root test and the two subtree maps give the recursion (`qmF`)

    ?(a/b) = 1/2                    if 2a = b,
    ?(a/b) = ?(a/(b-a)) / 2         if 2a < b    (x ↦ x/(1+x) is the left subtree),
    ?(a/b) = (1 + ?((2a-b)/a)) / 2  if 2a > b    (x ↦ 1/(2-x) is the right subtree).

Each step lowers `b`, so fuel `b` suffices (`qmF_fuel`); the recursion is
invariant under scaling `a/b ↦ ka/kb` (`qmF_scale`), so lowest terms are never
needed.  `mink` is `?` on a rational, constant `0` below `0` and `1` above `1`.
`qm = ? ∘ σ` with the explicit order-isomorphism `σ(x) = (1 + x/(1+|x|))/2`
from ℚ onto `ℚ ∩ (0, 1)`, computed on numerator and denominator (`sq`).

## Where choice was, and how it is avoided

Core's ℚ operations store proofs that use `Classical.propDecidable`:
`Rat.normalize` (behind `mkRat`, `Rat.divInt`, `numDenCasesOn''`) proves its
`reduced` field through `Int.natAbs_ediv`, and `Rat.mul` (behind `/`) proves its
own through `Int.divExact_eq_tdiv → ⋯ → Nat.right_eq_add`.  So core's
`Rat.lt_iff`, and any term `1 / 3 : ℚ`, carry `Classical.choice` (measured with
`#choice_path`).  The order `<` itself (`Rat.blt`) does not.  This file
uses only `num`, `den` and `Rat.blt`: the order is characterised from the
definition (`rat_lt_iff`), and rationals are built as structures (`rq`), never
normalised.  The bridge cell `rq 1 3 = 1 / 3` (§ Bridge) is the only
declaration pinned with choice, and the choice is in the right-hand side.

Two core `Nat` lemmas also carry choice (`Init.Data.Nat.Mod`, through
`Classical.propDecidable`): `Nat.mul_lt_mul_left` and
`Nat.lt_of_mul_lt_mul_left`.  They are replaced by `Nat.mul_le_mul_left`
arguments (`qmF_scale`, `qm_eq_mink`).  Mathlib's `linarith`/`nlinarith` leave
choice in the proof term; `ring` and `omega` do not, and are the only
arithmetic tactics used.
-/

open PLLFormula

namespace PLLND
namespace F0

open SemUI RNEmbed
open PLLND.LaxInfinite (atomFree)

namespace Mink

/-! ## Operations on dyadics -/

/-- `1/2`. -/
def mid : Dy := ⟨1, 1, by decide⟩

/-- `0`. -/
def zero : Dy := ⟨0, 0, by decide⟩

/-- `1`. -/
def one : Dy := ⟨1, 0, by decide⟩

/-- `d ↦ d/2`. -/
def half (d : Dy) : Dy :=
  ⟨d.num, d.exp + 1, by have := d.le; rw [two_pow_succ]; omega⟩

/-- `d ↦ (1 + d)/2`. -/
def halfUp (d : Dy) : Dy :=
  ⟨d.num + 2 ^ d.exp, d.exp + 1, by have := d.le; rw [two_pow_succ]; omega⟩

/-- Equality of values: `num/2^exp = num'/2^exp'`. -/
def eqv (d d' : Dy) : Prop := d.num * 2 ^ d'.exp = d'.num * 2 ^ d.exp

theorem lt_half {x y : Dy} (h : x.lt y) : (half x).lt (half y) := by
  show x.num * 2 ^ (y.exp + 1) < y.num * 2 ^ (x.exp + 1)
  have h' : x.num * 2 ^ y.exp < y.num * 2 ^ x.exp := h
  have e1 : x.num * 2 ^ (y.exp + 1) = 2 * (x.num * 2 ^ y.exp) := by ring
  have e2 : y.num * 2 ^ (x.exp + 1) = 2 * (y.num * 2 ^ x.exp) := by ring
  rw [e1, e2]
  omega

theorem lt_halfUp {x y : Dy} (h : x.lt y) : (halfUp x).lt (halfUp y) := by
  show (x.num + 2 ^ x.exp) * 2 ^ (y.exp + 1) < (y.num + 2 ^ y.exp) * 2 ^ (x.exp + 1)
  have h' : x.num * 2 ^ y.exp < y.num * 2 ^ x.exp := h
  have e1 : (x.num + 2 ^ x.exp) * 2 ^ (y.exp + 1) =
      2 * (x.num * 2 ^ y.exp) + 2 * (2 ^ x.exp * 2 ^ y.exp) := by ring
  have e2 : (y.num + 2 ^ y.exp) * 2 ^ (x.exp + 1) =
      2 * (y.num * 2 ^ x.exp) + 2 * (2 ^ x.exp * 2 ^ y.exp) := by ring
  rw [e1, e2]
  omega

theorem half_lt_mid {x : Dy} (h : x.num < 2 ^ x.exp) : (half x).lt mid := by
  show x.num * 2 ^ 1 < 1 * 2 ^ (x.exp + 1)
  rw [Nat.pow_one, Nat.one_mul, two_pow_succ]
  omega

theorem mid_lt_halfUp {y : Dy} (h : 0 < y.num) : mid.lt (halfUp y) := by
  show 1 * 2 ^ (y.exp + 1) < (y.num + 2 ^ y.exp) * 2 ^ 1
  rw [Nat.pow_one, Nat.one_mul, two_pow_succ]
  omega

theorem half_lt_halfUp {x y : Dy} (hx : x.num < 2 ^ x.exp) : (half x).lt (halfUp y) := by
  show x.num * 2 ^ (y.exp + 1) < (y.num + 2 ^ y.exp) * 2 ^ (x.exp + 1)
  have h1 : x.num * 2 ^ y.exp < 2 ^ x.exp * 2 ^ y.exp :=
    Nat.mul_lt_mul_of_pos_right hx (Nat.two_pow_pos _)
  have e1 : x.num * 2 ^ (y.exp + 1) = 2 * (x.num * 2 ^ y.exp) := by ring
  have e2 : (y.num + 2 ^ y.exp) * 2 ^ (x.exp + 1) =
      2 * (y.num * 2 ^ x.exp) + 2 * (2 ^ x.exp * 2 ^ y.exp) := by ring
  rw [e1, e2]
  omega

theorem zero_lt {y : Dy} (h : 0 < y.num) : zero.lt y := by
  show 0 * 2 ^ y.exp < y.num * 2 ^ 0
  rw [Nat.zero_mul, Nat.pow_zero, Nat.mul_one]
  exact h

theorem lt_one {x : Dy} (h : x.num < 2 ^ x.exp) : x.lt one := by
  show x.num * 2 ^ 0 < 1 * 2 ^ x.exp
  rw [Nat.pow_zero, Nat.mul_one, Nat.one_mul]
  exact h

theorem not_lt_of_eqv {x y : Dy} (h : eqv x y) : ¬ x.lt y := fun h' => by
  have h1 : x.num * 2 ^ y.exp = y.num * 2 ^ x.exp := h
  have h2 : x.num * 2 ^ y.exp < y.num * 2 ^ x.exp := h'
  omega

/-! ## `?` on pairs -/

/-- **Minkowski's `?` on `a / b`, fuelled.**  For `0 < a < b` and fuel at least
`b` (`qmF_fuel`):

    ?(a/b) = 1/2                    if 2a = b,
    ?(a/b) = ?(a/(b-a)) / 2         if 2a < b,
    ?(a/b) = (1 + ?((2a-b)/a)) / 2  if 2a > b. -/
def qmF : Nat → Nat → Nat → Dy
  | 0, _, _ => mid
  | n + 1, a, b =>
      if 2 * a = b then mid
      else if 2 * a < b then half (qmF n a (b - a))
      else halfUp (qmF n (2 * a - b) a)

/-- `?(a/b)`, with fuel `b`. -/
def qmP (a b : Nat) : Dy := qmF b a b

theorem qmF_succ (n a b : Nat) : qmF (n + 1) a b =
    if 2 * a = b then mid
    else if 2 * a < b then half (qmF n a (b - a))
    else halfUp (qmF n (2 * a - b) a) := rfl

/-- `x ∈ (0, 1)`, as a predicate on the representation. -/
def Inside (x : Dy) : Prop := 0 < x.num ∧ x.num < 2 ^ x.exp

theorem mid_inside : Inside mid := ⟨by decide, by decide⟩

theorem half_inside {x : Dy} (h : Inside x) : Inside (half x) := by
  refine ⟨h.1, ?_⟩
  show x.num < 2 ^ (x.exp + 1)
  have := h.2
  rw [two_pow_succ]
  omega

theorem halfUp_inside {x : Dy} (h : Inside x) : Inside (halfUp x) := by
  have := h.2
  refine ⟨by show 0 < x.num + 2 ^ x.exp; omega, ?_⟩
  show x.num + 2 ^ x.exp < 2 ^ (x.exp + 1)
  rw [two_pow_succ]
  omega

/-- Every value lies strictly between `0` and `1`. -/
theorem qmF_bounds : ∀ n a b, Inside (qmF n a b)
  | 0, _, _ => mid_inside
  | n + 1, a, b => by
      rw [qmF_succ]
      split
      · exact mid_inside
      · split
        · exact half_inside (qmF_bounds n a (b - a))
        · exact halfUp_inside (qmF_bounds n (2 * a - b) a)

theorem qmP_bounds (a b : Nat) : Inside (qmP a b) := qmF_bounds _ _ _

/-- **Fuel**: any fuel at least `b` gives the same value. -/
theorem qmF_fuel : ∀ n m a b, 0 < a → a < b → b ≤ n → b ≤ m → qmF n a b = qmF m a b
  | 0, _, _, _, _, hab, hn, _ => absurd hn (by omega)
  | _ + 1, 0, _, _, _, hab, _, hm => absurd hm (by omega)
  | n + 1, m + 1, a, b, ha, hab, hn, hm => by
      rw [qmF_succ, qmF_succ]
      by_cases h1 : 2 * a = b
      · rw [if_pos h1, if_pos h1]
      · rw [if_neg h1, if_neg h1]
        by_cases h2 : 2 * a < b
        · rw [if_pos h2, if_pos h2,
            qmF_fuel n m a (b - a) ha (by omega) (by omega) (by omega)]
        · rw [if_neg h2, if_neg h2,
            qmF_fuel n m (2 * a - b) a (by omega) (by omega) (by omega) (by omega)]

theorem qmF_eq (n a b : Nat) (ha : 0 < a) (hab : a < b) (hn : b ≤ n) :
    qmF n a b = qmP a b :=
  qmF_fuel n b a b ha hab hn (Nat.le_refl b)

/-- The left step: `?(a/(a+b)) = ?(a/b)/2`. -/
theorem qmP_left {a b : Nat} (ha : 0 < a) (hab : a < b) : qmP a (a + b) = half (qmP a b) := by
  obtain ⟨n, hn⟩ : ∃ n, a + b = n + 1 := ⟨a + b - 1, by omega⟩
  have n1 : ¬ 2 * a = n + 1 := by omega
  have n2 : 2 * a < n + 1 := by omega
  show qmF (a + b) a (a + b) = _
  rw [hn, qmF_succ, if_neg n1, if_pos n2, show n + 1 - a = b by omega,
    qmF_eq n a b ha hab (by omega)]

/-- The right step: `?(b/(2b-a)) = (1 + ?(a/b))/2`. -/
theorem qmP_right {a b : Nat} (ha : 0 < a) (hab : a < b) :
    qmP b (2 * b - a) = halfUp (qmP a b) := by
  obtain ⟨n, hn⟩ : ∃ n, 2 * b - a = n + 1 := ⟨2 * b - a - 1, by omega⟩
  have n1 : ¬ 2 * b = n + 1 := by omega
  have n2 : ¬ 2 * b < n + 1 := by omega
  show qmF (2 * b - a) b (2 * b - a) = _
  rw [hn, qmF_succ, if_neg n1, if_neg n2, show 2 * b - (n + 1) = a by omega,
    qmF_eq n a b ha hab (by omega)]

/-- **Scale invariance**: `?(ka/kb) = ?(a/b)`, at every fuel. -/
theorem qmF_scale {k : Nat} (hk : 0 < k) : ∀ n a b, qmF n (k * a) (k * b) = qmF n a b
  | 0, _, _ => rfl
  | n + 1, a, b => by
      rw [qmF_succ, qmF_succ]
      have c1 : (2 * (k * a) = k * b) ↔ (2 * a = b) := by
        rw [Nat.mul_left_comm]
        exact ⟨Nat.eq_of_mul_eq_mul_left hk, fun h => by rw [h]⟩
      -- not `Nat.mul_lt_mul_left`, which carries `Classical.choice`
      have c2 : (2 * (k * a) < k * b) ↔ (2 * a < b) := by
        rw [Nat.mul_left_comm]
        constructor
        · intro h
          rcases Nat.lt_or_ge (2 * a) b with c | c
          · exact c
          · exact absurd h (Nat.not_lt.mpr (Nat.mul_le_mul_left k c))
        · intro h
          exact Nat.mul_lt_mul_of_pos_left h hk
      by_cases h1 : 2 * a = b
      · rw [if_pos (c1.mpr h1), if_pos h1]
      · rw [if_neg (fun h => h1 (c1.mp h)), if_neg h1]
        by_cases h2 : 2 * a < b
        · rw [if_pos (c2.mpr h2), if_pos h2, ← Nat.mul_sub, qmF_scale hk n a (b - a)]
        · rw [if_neg (fun h => h2 (c2.mp h)), if_neg h2,
            show 2 * (k * a) - k * b = k * (2 * a - b) by rw [Nat.mul_sub, Nat.mul_left_comm],
            qmF_scale hk n (2 * a - b) a]

theorem qmP_scale {k a b : Nat} (hk : 0 < k) (ha : 0 < a) (hab : a < b) :
    qmP (k * a) (k * b) = qmP a b := by
  have : b ≤ k * b := Nat.le_mul_of_pos_left b hk
  show qmF (k * b) (k * a) (k * b) = _
  rw [qmF_scale hk, qmF_eq _ a b ha hab this]

/-- **Strict monotonicity on pairs, fuelled.** -/
theorem qmF_lt : ∀ n a b c d, 0 < a → a < b → 0 < c → c < d → b ≤ n → d ≤ n →
    a * d < c * b → (qmF n a b).lt (qmF n c d)
  | 0, _, _, _, _, _, hab, _, _, hb, _, _ => absurd hb (by omega)
  | n + 1, a, b, c, d, ha, hab, hc, hcd, hb, hd, h => by
      rw [qmF_succ, qmF_succ]
      rcases Nat.lt_trichotomy (2 * a) b with h1 | h1 | h1 <;>
        rcases Nat.lt_trichotomy (2 * c) d with h2 | h2 | h2
      · -- both left
        have n1 : ¬ 2 * a = b := by omega
        have n2 : ¬ 2 * c = d := by omega
        rw [if_neg n1, if_pos h1, if_neg n2, if_pos h2]
        apply lt_half
        apply qmF_lt n a (b - a) c (d - c) ha (by omega) hc (by omega) (by omega) (by omega)
        rw [Nat.mul_sub, Nat.mul_sub, Nat.mul_comm c a]
        have : a * c ≤ a * d := Nat.mul_le_mul_left a (Nat.le_of_lt hcd)
        have : a * c ≤ c * b := by
          rw [Nat.mul_comm a c]
          exact Nat.mul_le_mul_left c (Nat.le_of_lt hab)
        omega
      · -- left, root
        have n1 : ¬ 2 * a = b := by omega
        rw [if_neg n1, if_pos h1, if_pos h2]
        exact half_lt_mid (qmF_bounds _ _ _).2
      · -- left, right
        have n1 : ¬ 2 * a = b := by omega
        have n2 : ¬ 2 * c = d := by omega
        have n3 : ¬ 2 * c < d := by omega
        rw [if_neg n1, if_pos h1, if_neg n2, if_neg n3]
        exact half_lt_halfUp (qmF_bounds _ _ _).2
      · -- root, left: impossible
        exfalso
        subst h1
        have : a * (2 * c) < a * d := Nat.mul_lt_mul_of_pos_left h2 ha
        have e1 : a * (2 * c) = 2 * (a * c) := by ring
        have e2 : c * (2 * a) = 2 * (a * c) := by ring
        omega
      · -- root, root: impossible
        exfalso
        subst h1
        subst h2
        have e1 : a * (2 * c) = c * (2 * a) := by ring
        omega
      · -- root, right
        have n2 : ¬ 2 * c = d := by omega
        have n3 : ¬ 2 * c < d := by omega
        rw [if_pos h1, if_neg n2, if_neg n3]
        exact mid_lt_halfUp (qmF_bounds _ _ _).1
      · -- right, left: impossible
        exfalso
        have : a * (2 * c) < a * d := Nat.mul_lt_mul_of_pos_left h2 ha
        have : c * b < c * (2 * a) := Nat.mul_lt_mul_of_pos_left h1 hc
        have e1 : a * (2 * c) = 2 * (a * c) := by ring
        have e2 : c * (2 * a) = 2 * (a * c) := by ring
        omega
      · -- right, root: impossible
        exfalso
        subst h2
        have : c * b < c * (2 * a) := Nat.mul_lt_mul_of_pos_left h1 hc
        have e1 : a * (2 * c) = 2 * (a * c) := by ring
        have e2 : c * (2 * a) = 2 * (a * c) := by ring
        omega
      · -- both right
        have n1 : ¬ 2 * a = b := by omega
        have n2 : ¬ 2 * a < b := by omega
        have n3 : ¬ 2 * c = d := by omega
        have n4 : ¬ 2 * c < d := by omega
        rw [if_neg n1, if_neg n2, if_neg n3, if_neg n4]
        apply lt_halfUp
        apply qmF_lt n (2 * a - b) a (2 * c - d) c (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega)
        rw [Nat.sub_mul, Nat.sub_mul]
        have : b * c ≤ 2 * a * c := Nat.mul_le_mul_right c (Nat.le_of_lt h1)
        have : d * a ≤ 2 * c * a := Nat.mul_le_mul_right a (Nat.le_of_lt h2)
        have e1 : 2 * a * c = 2 * c * a := by ring
        have e2 : b * c = c * b := Nat.mul_comm b c
        have e3 : d * a = a * d := Nat.mul_comm d a
        omega

/-- **Strict monotonicity on pairs**: `a/b < c/d ⟹ ?(a/b) < ?(c/d)`. -/
theorem qmP_lt {a b c d : Nat} (ha : 0 < a) (hab : a < b) (hc : 0 < c) (hcd : c < d)
    (h : a * d < c * b) : (qmP a b).lt (qmP c d) := by
  rw [← qmF_eq (b + d) a b ha hab (by omega), ← qmF_eq (b + d) c d hc hcd (by omega)]
  exact qmF_lt (b + d) a b c d ha hab hc hcd (by omega) (by omega) h

/-! ## The order of ℚ, choice-free -/

/-- `a < b` in cross-multiplied form, from the definition `Rat.blt`.  Core's
`Rat.lt_iff` states the same but carries `Classical.choice`. -/
theorem rat_lt_iff (a b : ℚ) : a < b ↔ a.num * b.den < b.num * a.den := by
  have hx : (0 : Int) < a.den := by have := a.den_pos; omega
  have hy : (0 : Int) < b.den := by have := b.den_pos; omega
  have nonpos : ∀ {m : Int} {x : Int}, m ≤ 0 → 0 < x → m * x ≤ 0 := fun hm hx' => by
    have := Int.mul_le_mul_of_nonneg_right hm (Int.le_of_lt hx')
    rw [Int.zero_mul] at this
    exact this
  show Rat.blt a b = true ↔ _
  unfold Rat.blt
  split
  · rename_i hc
    rw [Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff] at hc
    have : a.num * b.den < 0 := Int.mul_neg_of_neg_of_pos hc.1 hy
    have : 0 ≤ b.num * a.den := Int.mul_nonneg hc.2 (Int.le_of_lt hx)
    exact ⟨fun _ => by omega, fun _ => rfl⟩
  · split
    · rename_i hz
      rw [hz, Int.zero_mul, decide_eq_true_iff]
      constructor
      · intro hb
        exact Int.mul_pos hb hx
      · intro hb
        rcases Int.lt_or_le 0 b.num with c | c
        · exact c
        · have := nonpos c hx
          omega
    · split
      · rename_i hc
        rw [Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff] at hc
        have : 0 < a.num * b.den := Int.mul_pos hc.1 hy
        have := nonpos hc.2 hx
        exact ⟨fun h => absurd h (by decide), fun _ => by omega⟩
      · exact decide_eq_true_iff

/-- `a ≤ b` in cross-multiplied form. -/
theorem rat_le_iff (a b : ℚ) : a ≤ b ↔ a.num * b.den ≤ b.num * a.den := by
  have key := rat_lt_iff b a
  change (Rat.blt b a = true ↔ _) at key
  change Rat.blt b a = false ↔ _
  cases hc : Rat.blt b a
  · rw [hc] at key
    constructor
    · intro _
      exact Int.not_lt.mp (fun h' => absurd (key.mpr h') (by decide))
    · intro _
      rfl
  · rw [hc] at key
    constructor
    · intro h'
      exact absurd h' (by decide)
    · intro h'
      exact absurd (key.mp rfl) (Int.not_lt.mpr h')

/-- Equal cross-products force equal rationals (both are in lowest terms). -/
theorem rat_eq_of_cross {a b : ℚ} (h : a.num * b.den = b.num * a.den) : a = b := by
  have h' : a.num.natAbs * b.den = b.num.natAbs * a.den := by
    have := congrArg Int.natAbs h
    rw [Int.natAbs_mul, Int.natAbs_mul] at this
    exact this
  have d1 : a.den ∣ b.den := by
    have : a.den ∣ a.num.natAbs * b.den := ⟨b.num.natAbs, by rw [h', Nat.mul_comm]⟩
    exact (Nat.Coprime.symm a.reduced).dvd_of_dvd_mul_left this
  have d2 : b.den ∣ a.den := by
    have : b.den ∣ b.num.natAbs * a.den := ⟨a.num.natAbs, by rw [← h', Nat.mul_comm]⟩
    exact (Nat.Coprime.symm b.reduced).dvd_of_dvd_mul_left this
  have hd : a.den = b.den := Nat.dvd_antisymm d1 d2
  have hn : a.num = b.num := by
    rw [hd] at h
    exact Int.eq_of_mul_eq_mul_right (by have := b.den_pos; omega) h
  exact Rat.ext hn hd

theorem rat_trichotomy (a b : ℚ) : a < b ∨ a = b ∨ b < a := by
  rcases Int.lt_trichotomy (a.num * b.den) (b.num * a.den) with h | h | h
  · exact Or.inl ((rat_lt_iff a b).mpr h)
  · exact Or.inr (Or.inl (rat_eq_of_cross h))
  · exact Or.inr (Or.inr ((rat_lt_iff b a).mpr h))

/-- The rational `n / d` given in lowest terms, built as a structure: no
normalisation runs, so no `Classical.choice` enters. -/
def rq (n : Int) (d : Nat) (h : d ≠ 0 := by decide) (r : n.natAbs.Coprime d := by decide) : ℚ :=
  ⟨n, d, h, r⟩

/-! ## Minkowski's `?` on `[0, 1]` -/

/-- **Minkowski's question-mark function** on `[0, 1]`, constant `0` below `0`
and `1` above `1`. -/
def mink (q : ℚ) : Dy :=
  if q.num ≤ 0 then zero
  else if (q.den : Int) ≤ q.num then one
  else qmP q.num.toNat q.den

theorem mink_of_num {q : ℚ} {k : Nat} (hk : q.num = k) :
    mink q = if k = 0 then zero else if q.den ≤ k then one else qmP k q.den := by
  unfold mink
  rw [hk]
  by_cases h0 : k = 0
  · rw [if_pos (by omega : (k : Int) ≤ 0), if_pos h0]
  · rw [if_neg (by omega : ¬ (k : Int) ≤ 0), if_neg h0]
    by_cases h1 : q.den ≤ k
    · rw [if_pos (by omega : (q.den : Int) ≤ k), if_pos h1]
    · rw [if_neg (by omega : ¬ (q.den : Int) ≤ k), if_neg h1]
      rfl

/-! ### Sanity cells (the refutation stage for the definition) -/

theorem cell_zero : mink 0 = zero := rfl
theorem cell_one : mink 1 = one := rfl
theorem cell_half : mink (rq 1 2) = ⟨1, 1, by decide⟩ := rfl
theorem cell_third : mink (rq 1 3) = ⟨1, 2, by decide⟩ := rfl
theorem cell_two_thirds : mink (rq 2 3) = ⟨3, 2, by decide⟩ := rfl
theorem cell_two_fifths : mink (rq 2 5) = ⟨3, 3, by decide⟩ := rfl

/-- Two cross-checks against the continued-fraction formula
`?([0; a₁, a₂, …]) = 2 Σₖ (−1)^(k+1) 2^−(a₁+⋯+aₖ)`, independent of the
recursion: `5/8 = [0; 1, 1, 1, 2]` gives `11/16`, `3/7 = [0; 2, 3]` gives `7/16`. -/
theorem cell_five_eighths : mink (rq 5 8) = ⟨11, 4, by decide⟩ := rfl
theorem cell_three_sevenths : mink (rq 3 7) = ⟨7, 4, by decide⟩ := rfl

/-- **`?` is strictly increasing on `[0, 1]`.** -/
theorem mink_lt {q q' : ℚ} (h0 : 0 ≤ q) (h : q < q') (h1 : q' ≤ 1) :
    (mink q).lt (mink q') := by
  have e0 : (0 : Int) * (q.den : Int) ≤ q.num * ((1 : Nat) : Int) := (rat_le_iff 0 q).mp h0
  have e : q.num * q'.den < q'.num * q.den := (rat_lt_iff q q').mp h
  have e1 : q'.num * ((1 : Nat) : Int) ≤ (1 : Int) * (q'.den : Int) := (rat_le_iff q' 1).mp h1
  have hx := q.den_pos
  have hx' := q'.den_pos
  obtain ⟨k, hk⟩ : ∃ k : Nat, q.num = k := ⟨q.num.toNat, by omega⟩
  rw [hk] at e
  obtain ⟨k', hk'⟩ : ∃ k' : Nat, q'.num = k' := by
    refine ⟨q'.num.toNat, ?_⟩
    rcases Int.lt_or_le q'.num 0 with c | c
    · exfalso
      have : q'.num * (q.den : Int) < 0 := Int.mul_neg_of_neg_of_pos c (by omega)
      have : (0 : Int) ≤ (k : Int) * (q'.den : Int) := Int.mul_nonneg (by omega) (by omega)
      omega
    · omega
  rw [hk'] at e e1
  have he : k * q'.den < k' * q.den := by omega
  have hk'x : k' ≤ q'.den := by omega
  rw [mink_of_num hk, mink_of_num hk']
  have hk'0 : k' ≠ 0 := by
    intro c
    subst c
    omega
  rw [if_neg hk'0]
  by_cases hk0 : k = 0
  · rw [if_pos hk0]
    by_cases c : q'.den ≤ k'
    · rw [if_pos c]
      exact zero_lt (by decide)
    · rw [if_neg c]
      exact zero_lt (qmP_bounds _ _).1
  · rw [if_neg hk0]
    have hkx : ¬ q.den ≤ k := by
      intro c
      have : q.den * q'.den ≤ k * q'.den := Nat.mul_le_mul_right _ c
      have : k' * q.den ≤ q'.den * q.den := Nat.mul_le_mul_right _ hk'x
      have e2 : q.den * q'.den = q'.den * q.den := Nat.mul_comm _ _
      omega
    rw [if_neg hkx]
    by_cases c : q'.den ≤ k'
    · rw [if_pos c]
      exact lt_one (qmP_bounds _ _).2
    · rw [if_neg c]
      exact qmP_lt (by omega) (by omega) (by omega) (by omega) he

/-! ### `?` is onto the dyadics in `(0, 1)` -/

/-- `x` has the value `m / 2^e`. -/
def IsVal (x : Dy) (m e : Nat) : Prop := x.num * 2 ^ e = m * 2 ^ x.exp

/-- **Every dyadic `m / 2^e` in `(0, 1)` is `?(a/b)` for a pair in lowest terms.** -/
theorem sb_exists : ∀ e m, 0 < m → m < 2 ^ e →
    ∃ a b, 0 < a ∧ a < b ∧ Nat.Coprime a b ∧ IsVal (qmP a b) m e
  | 0, m, h0, h1 => absurd h1 (by rw [Nat.pow_zero]; omega)
  | e + 1, m, h0, h1 => by
      have hp := two_pow_succ e
      rcases Nat.lt_trichotomy m (2 ^ e) with h | h | h
      · obtain ⟨a, b, ha, hab, hc, hv⟩ := sb_exists e m h0 h
        refine ⟨a, a + b, ha, by omega, ?_, ?_⟩
        · show Nat.gcd a (a + b) = 1
          rw [Nat.gcd_self_add_right]
          exact hc
        · rw [qmP_left ha hab]
          have hv' : (qmP a b).num * 2 ^ e = m * 2 ^ (qmP a b).exp := hv
          show (qmP a b).num * 2 ^ (e + 1) = m * 2 ^ ((qmP a b).exp + 1)
          have e1 : (qmP a b).num * 2 ^ (e + 1) = 2 * ((qmP a b).num * 2 ^ e) := by ring
          have e2 : m * 2 ^ ((qmP a b).exp + 1) = 2 * (m * 2 ^ (qmP a b).exp) := by ring
          rw [e1, e2, hv']
      · refine ⟨1, 2, by decide, by decide, by decide, ?_⟩
        show 1 * 2 ^ (e + 1) = m * 2 ^ 1
        rw [h, Nat.pow_one, Nat.one_mul, two_pow_succ, Nat.mul_comm]
      · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 ^ e := ⟨m - 2 ^ e, by omega⟩
        obtain ⟨a, b, ha, hab, hc, hv⟩ := sb_exists e m' (by omega) (by omega)
        refine ⟨b, 2 * b - a, by omega, by omega, ?_, ?_⟩
        · show Nat.gcd b (2 * b - a) = 1
          rw [show 2 * b - a = (b - a) + b by omega, Nat.gcd_add_self_right,
            Nat.gcd_self_sub_right (Nat.le_of_lt hab), Nat.gcd_comm]
          exact hc
        · rw [qmP_right ha hab]
          have hv' : (qmP a b).num * 2 ^ e = m' * 2 ^ (qmP a b).exp := hv
          show ((qmP a b).num + 2 ^ (qmP a b).exp) * 2 ^ (e + 1) =
            (m' + 2 ^ e) * 2 ^ ((qmP a b).exp + 1)
          have e1 : ((qmP a b).num + 2 ^ (qmP a b).exp) * 2 ^ (e + 1) =
              2 * ((qmP a b).num * 2 ^ e) + 2 * (2 ^ (qmP a b).exp * 2 ^ e) := by ring
          have e2 : (m' + 2 ^ e) * 2 ^ ((qmP a b).exp + 1) =
              2 * (m' * 2 ^ (qmP a b).exp) + 2 * (2 ^ (qmP a b).exp * 2 ^ e) := by ring
          rw [e1, e2, hv']

/-- **`?` is onto the dyadics in `(0, 1)`**: every `d` with `0 < d < 1` is
`?(q)` for some rational `0 < q < 1`. -/
theorem mink_onto (d : Dy) (h0 : 0 < d.num) (h1 : d.num < 2 ^ d.exp) :
    ∃ q : ℚ, 0 < q ∧ q < 1 ∧ eqv (mink q) d := by
  obtain ⟨a, b, ha, hab, hc, hv⟩ := sb_exists d.exp d.num h0 h1
  refine ⟨⟨a, b, by omega, hc⟩, ?_, ?_, ?_⟩
  · exact (rat_lt_iff _ _).mpr
      (show (0 : Int) * (b : Int) < (a : Int) * ((1 : Nat) : Int) by omega)
  · exact (rat_lt_iff _ _).mpr
      (show (a : Int) * ((1 : Nat) : Int) < (1 : Int) * (b : Int) by omega)
  · have hn0 : a ≠ 0 := by omega
    have hn1 : ¬ b ≤ a := by omega
    rw [mink_of_num (k := a) rfl, if_neg hn0, if_neg hn1]
    exact hv

/-! ## `qm = ? ∘ σ` on all of ℚ -/

/-- `σ(x) = (1 + x/(1+|x|))/2`, the explicit order-isomorphism `ℚ → ℚ ∩ (0, 1)`,
as an unreduced pair: for `x = n/d`,

    σ(x) = (d + 2n) / (2d + 2n)   if n ≥ 0,
    σ(x) = d / (2d + 2|n|)        if n < 0. -/
def sq (q : ℚ) : Nat × Nat :=
  if 0 ≤ q.num then (q.den + 2 * q.num.toNat, 2 * q.den + 2 * q.num.toNat)
  else (q.den, 2 * q.den + 2 * q.num.natAbs)

/-- **`qm = ? ∘ σ`**: an explicit, computable, choice-free map from ℚ to the
dyadics in `(0, 1)`. -/
def qm (q : ℚ) : Dy := qmP (sq q).1 (sq q).2

theorem sq_of_nonneg {q : ℚ} {k : Nat} (hk : q.num = k) :
    sq q = (q.den + 2 * k, 2 * q.den + 2 * k) := by
  unfold sq
  rw [if_pos (by omega), hk]
  rfl

theorem sq_of_neg {q : ℚ} {m : Nat} (hm : q.num = -((m + 1 : Nat) : Int)) :
    sq q = (q.den, 2 * q.den + 2 * (m + 1)) := by
  unfold sq
  rw [if_neg (by omega), hm]
  rfl

/-- Every rational is `k` or `-(m+1)` over its denominator. -/
theorem num_cases (q : ℚ) :
    (∃ k : Nat, q.num = k) ∨ (∃ m : Nat, q.num = -((m + 1 : Nat) : Int)) := by
  rcases Int.lt_or_le q.num 0 with c | c
  · exact Or.inr ⟨q.num.natAbs - 1, by omega⟩
  · exact Or.inl ⟨q.num.toNat, by omega⟩

theorem qm_cells : qm 0 = mid ∧ qm 1 = ⟨7, 3, by decide⟩ ∧ qm (-1) = ⟨1, 3, by decide⟩ :=
  ⟨rfl, rfl, rfl⟩

/-- **`qm` is strictly increasing on ℚ.** -/
theorem qm_lt {q q' : ℚ} (h : q < q') : (qm q).lt (qm q') := by
  have e := (rat_lt_iff q q').mp h
  have hx := q.den_pos
  have hx' := q'.den_pos
  unfold qm
  rcases num_cases q with ⟨k, hk⟩ | ⟨m, hm⟩ <;> rcases num_cases q' with ⟨k', hk'⟩ | ⟨m', hm'⟩
  · rw [sq_of_nonneg hk, sq_of_nonneg hk']
    rw [hk, hk'] at e
    have he : k * q'.den < k' * q.den := by omega
    apply qmP_lt (by omega) (by omega) (by omega) (by omega)
    have e1 : (q.den + 2 * k) * (2 * q'.den + 2 * k') =
        2 * (q.den * q'.den) + 2 * (k' * q.den) + 4 * (k * q'.den) + 4 * (k * k') := by ring
    have e2 : (q'.den + 2 * k') * (2 * q.den + 2 * k) =
        2 * (q.den * q'.den) + 2 * (k * q'.den) + 4 * (k' * q.den) + 4 * (k * k') := by ring
    rw [e1, e2]
    omega
  · exfalso
    rw [hk, hm', Int.neg_mul] at e
    have : (0 : Int) ≤ (k : Int) * (q'.den : Int) := Int.mul_nonneg (by omega) (by omega)
    have : (0 : Int) ≤ ((m' + 1 : Nat) : Int) * (q.den : Int) :=
      Int.mul_nonneg (by omega) (by omega)
    omega
  · rw [sq_of_neg hm, sq_of_nonneg hk']
    apply qmP_lt (by omega) (by omega) (by omega) (by omega)
    have e1 : q.den * (2 * q'.den + 2 * k') = 2 * (q.den * q'.den) + 2 * (k' * q.den) := by ring
    have e2 : (q'.den + 2 * k') * (2 * q.den + 2 * (m + 1)) =
        2 * (q.den * q'.den) + 2 * (q'.den * (m + 1)) + 4 * (k' * q.den) +
          4 * (k' * (m + 1)) := by ring
    rw [e1, e2]
    have : 0 < q'.den * (m + 1) := Nat.mul_pos hx' (by omega)
    omega
  · rw [sq_of_neg hm, sq_of_neg hm']
    rw [hm, hm', Int.neg_mul, Int.neg_mul] at e
    have he : (m' + 1) * q.den < (m + 1) * q'.den := by omega
    apply qmP_lt (by omega) (by omega) (by omega) (by omega)
    have e1 : q.den * (2 * q'.den + 2 * (m' + 1)) =
        2 * (q.den * q'.den) + 2 * ((m' + 1) * q.den) := by ring
    have e2 : q'.den * (2 * q.den + 2 * (m + 1)) =
        2 * (q.den * q'.den) + 2 * ((m + 1) * q'.den) := by ring
    rw [e1, e2]
    omega

/-- **`qm` is injective** (as a map to dyadic values). -/
theorem qm_inj {q q' : ℚ} (h : eqv (qm q) (qm q')) : q = q' := by
  rcases rat_trichotomy q q' with c | c | c
  · exact absurd (qm_lt c) (not_lt_of_eqv h)
  · exact c
  · have h' : eqv (qm q') (qm q) := Eq.symm h
    exact absurd (qm_lt c) (not_lt_of_eqv h')

theorem sq_bounds (q : ℚ) : 0 < (sq q).1 ∧ (sq q).1 < (sq q).2 := by
  have hx := q.den_pos
  rcases num_cases q with ⟨k, hk⟩ | ⟨m, hm⟩
  · rw [sq_of_nonneg hk]
    exact ⟨show 0 < q.den + 2 * k by omega,
      show q.den + 2 * k < 2 * q.den + 2 * k by omega⟩
  · rw [sq_of_neg hm]
    exact ⟨show 0 < q.den by omega, show q.den < 2 * q.den + 2 * (m + 1) by omega⟩

/-- `u / v` in lowest terms: `u = g u'`, `v = g v'` with `u', v'` coprime. -/
theorem reduce (u v : Nat) (hv : 0 < v) :
    ∃ g u' v', 0 < g ∧ 0 < v' ∧ u = g * u' ∧ v = g * v' ∧ Nat.Coprime u' v' := by
  have hg : 0 < Nat.gcd u v := Nat.gcd_pos_of_pos_right u hv
  obtain ⟨u', hu'⟩ := Nat.gcd_dvd_left u v
  obtain ⟨v', hv'⟩ := Nat.gcd_dvd_right u v
  have hc := Nat.coprime_div_gcd_div_gcd hg
  have e1 : u / Nat.gcd u v = u' := Nat.div_eq_of_eq_mul_left hg (hu'.trans (Nat.mul_comm _ _))
  have e2 : v / Nat.gcd u v = v' := Nat.div_eq_of_eq_mul_left hg (hv'.trans (Nat.mul_comm _ _))
  rw [e1, e2] at hc
  refine ⟨Nat.gcd u v, u', v', hg, ?_, hu', hv', hc⟩
  rcases Nat.eq_zero_or_pos v' with h | h
  · rw [h, Nat.mul_zero] at hv'
    omega
  · exact h

/-- **`qm` is onto the dyadics in `(0, 1)`**: with `qm_lt`, `qm` is an
order-isomorphism from ℚ onto them.  The preimage of `?(a/b)` is
`σ⁻¹(a/b)`, which is `(2a-b)/(2(b-a))` or `-(b-2a)/(2a)`, reduced. -/
theorem qm_onto (d : Dy) (h0 : 0 < d.num) (h1 : d.num < 2 ^ d.exp) :
    ∃ q : ℚ, eqv (qm q) d := by
  obtain ⟨a, b, ha, hab, _, hv⟩ := sb_exists d.exp d.num h0 h1
  suffices h : ∃ q : ℚ, qm q = qmP a b by
    obtain ⟨q, hq⟩ := h
    exact ⟨q, by rw [hq]; exact hv⟩
  by_cases hc : b ≤ 2 * a
  · obtain ⟨g, u, v, hg, hv0, hu, hvv, hcop⟩ := reduce (2 * a - b) (2 * (b - a)) (by omega)
    refine ⟨⟨(u : Int), v, by omega, hcop⟩, ?_⟩
    unfold qm
    rw [sq_of_nonneg (k := u) rfl]
    show qmP (v + 2 * u) (2 * v + 2 * u) = qmP a b
    have e1 : g * (v + 2 * u) = 2 * a := by
      have : g * (v + 2 * u) = g * v + 2 * (g * u) := by ring
      omega
    have e2 : g * (2 * v + 2 * u) = 2 * b := by
      have : g * (2 * v + 2 * u) = 2 * (g * v) + 2 * (g * u) := by ring
      omega
    rw [← qmP_scale (k := g) (a := v + 2 * u) (b := 2 * v + 2 * u) hg (by omega) (by omega),
      e1, e2, qmP_scale (k := 2) (by decide) ha hab]
  · obtain ⟨g, u, v, hg, hv0, hu, hvv, hcop⟩ := reduce (b - 2 * a) (2 * a) (by omega)
    have hu0 : 0 < u := by
      rcases Nat.eq_zero_or_pos u with h | h
      · rw [h, Nat.mul_zero] at hu
        omega
      · exact h
    obtain ⟨w, rfl⟩ : ∃ w, u = w + 1 := ⟨u - 1, by omega⟩
    refine ⟨⟨-((w + 1 : Nat) : Int), v, by omega, by rw [Int.natAbs_neg]; exact hcop⟩, ?_⟩
    unfold qm
    rw [sq_of_neg (m := w) rfl]
    show qmP v (2 * v + 2 * (w + 1)) = qmP a b
    have e1 : g * v = 2 * a := by omega
    have e2 : g * (2 * v + 2 * (w + 1)) = 2 * b := by
      have : g * (2 * v + 2 * (w + 1)) = 2 * (g * v) + 2 * (g * (w + 1)) := by ring
      omega
    rw [← qmP_scale (k := g) (a := v) (b := 2 * v + 2 * (w + 1)) hg (by omega) (by omega),
      e1, e2, qmP_scale (k := 2) (by decide) ha hab]

/-- **`qm = ? ∘ σ`**: if `σ(q) = A/B` (the pair `sq q`) and `r = A/B`, then
`qm q = ?(r)`. -/
theorem qm_eq_mink {q r : ℚ} {A B : Nat} (hs : sq q = (A, B)) (hr : r.num * B = A * r.den) :
    qm q = mink r := by
  have hb := sq_bounds q
  rw [hs] at hb
  obtain ⟨hA, hAB⟩ : 0 < A ∧ A < B := hb
  have hd := r.den_pos
  obtain ⟨n, hn⟩ : ∃ n : Nat, r.num = n := by
    refine ⟨r.num.toNat, ?_⟩
    rcases Int.lt_or_le r.num 0 with c | c
    · exfalso
      have : r.num * (B : Int) < 0 := Int.mul_neg_of_neg_of_pos c (by omega)
      have : (0 : Int) ≤ (A : Int) * (r.den : Int) := Int.mul_nonneg (by omega) (by omega)
      omega
    · omega
  rw [hn] at hr
  have hr' : n * B = A * r.den := by omega
  have hcop : Nat.Coprime r.den n := by
    have := r.reduced
    rw [hn] at this
    exact Nat.Coprime.symm this
  obtain ⟨g, hg⟩ : r.den ∣ B := hcop.dvd_of_dvd_mul_left ⟨A, by rw [hr', Nat.mul_comm]⟩
  have hA' : A = g * n := Nat.eq_of_mul_eq_mul_right hd (by rw [← hr', hg]; ring)
  have hg0 : 0 < g := Nat.pos_of_ne_zero fun h => by
    rw [h, Nat.mul_zero] at hg
    omega
  have hn0 : n ≠ 0 := fun h => by
    rw [h, Nat.mul_zero] at hA'
    omega
  have hnd : n < r.den := by
    have : g * n < g * r.den := by
      rw [← hA', Nat.mul_comm g r.den, ← hg]
      exact hAB
    -- not `Nat.lt_of_mul_lt_mul_left`, which carries `Classical.choice`
    rcases Nat.lt_or_ge n r.den with c | c
    · exact c
    · exact absurd this (Nat.not_lt.mpr (Nat.mul_le_mul_left g c))
  unfold qm
  rw [hs, mink_of_num hn, if_neg hn0, if_neg (by omega)]
  show qmP A B = qmP n r.den
  rw [hA', hg, Nat.mul_comm r.den g,
    qmP_scale (k := g) (a := n) (b := r.den) hg0 (by omega) hnd]

/-! ## Bridge to core's `/`

The cells above use `rq n d`, the rational with numerator `n` and denominator
`d`.  These are the rationals `1/2, 1/3, 2/3, 2/5` as core computes them; the
right-hand sides are built by core's `/`, whose `Rat.mul` stores a proof that
carries `Classical.choice`, so this cell (and only this cell) is pinned with it. -/
theorem rq_bridge : rq 1 2 = 1 / 2 ∧ rq 1 3 = 1 / 3 ∧ rq 2 3 = 2 / 3 ∧ rq 2 5 = 2 / 5 := by
  decide +kernel

end Mink

/-! ## The choice-free embedding of ℚ in F0 -/

/-- `f' q`, the formula of the rational `q`: `?(σ(q))` through `f`. -/
def ratFormulaCF (q : ℚ) : PLLFormula := (Mink.qm q).formula

/-- **Every `f' q` is variable-free.** -/
theorem rat_vf_cf (q : ℚ) : atomFree (ratFormulaCF q) = true := dyadic_vf _

/-- **ℚ embeds in F0, explicitly and without choice**:

    q < q'  ⟹  f' q ⊢ f' q'  ∧  f' q' ⊬ f' q. -/
theorem rat_embedding_cf {q q' : ℚ} (h : q < q') :
    Deriv [ratFormulaCF q] (ratFormulaCF q') ∧ ([ratFormulaCF q'] ⊬ ratFormulaCF q) :=
  dyadic_embedding _ _ (Mink.qm_lt h)

end F0
end PLLND

-- Definitions (the map itself is choice-free).
#axioms_within PLLND.F0.Mink.half [propext, Quot.sound]
#axioms_within PLLND.F0.Mink.halfUp [propext, Quot.sound]
#axioms_within PLLND.F0.Mink.qmF [propext, Quot.sound]
#axioms_within PLLND.F0.Mink.qmP [propext, Quot.sound]
#axioms_within PLLND.F0.Mink.rq [propext, Quot.sound]
#axioms_within PLLND.F0.Mink.mink [propext, Quot.sound]
#axioms_within PLLND.F0.Mink.sq [propext, Quot.sound]
#axioms_within PLLND.F0.Mink.qm [propext, Quot.sound]
#axioms_within PLLND.F0.ratFormulaCF [propext, Quot.sound]
-- Dyadic order lemmas.
#axioms_within PLLND.F0.Mink.lt_half [propext, Quot.sound]
#axioms_within PLLND.F0.Mink.lt_halfUp [propext, Quot.sound]
#axioms_within PLLND.F0.Mink.half_lt_mid [propext, Quot.sound]
#axioms_within PLLND.F0.Mink.mid_lt_halfUp [propext, Quot.sound]
#axioms_within PLLND.F0.Mink.half_lt_halfUp [propext, Quot.sound]
#axioms_within PLLND.F0.Mink.zero_lt [propext, Quot.sound]
#axioms_within PLLND.F0.Mink.lt_one [propext, Quot.sound]
#axioms_within PLLND.F0.Mink.not_lt_of_eqv [propext, Quot.sound]
#axioms_within PLLND.F0.Mink.mid_inside [propext, Quot.sound]
#axioms_within PLLND.F0.Mink.half_inside [propext, Quot.sound]
#axioms_within PLLND.F0.Mink.halfUp_inside [propext, Quot.sound]
-- `?` on pairs.
#axioms_within PLLND.F0.Mink.qmF_succ [propext, Quot.sound]
#axioms_within PLLND.F0.Mink.qmF_bounds [propext, Quot.sound]
#axioms_within PLLND.F0.Mink.qmP_bounds [propext, Quot.sound]
#axioms_within PLLND.F0.Mink.qmF_fuel [propext, Quot.sound]
#axioms_within PLLND.F0.Mink.qmF_eq [propext, Quot.sound]
#axioms_within PLLND.F0.Mink.qmP_left [propext, Quot.sound]
#axioms_within PLLND.F0.Mink.qmP_right [propext, Quot.sound]
#axioms_within PLLND.F0.Mink.qmF_scale [propext, Quot.sound]
#axioms_within PLLND.F0.Mink.qmP_scale [propext, Quot.sound]
#axioms_within PLLND.F0.Mink.qmF_lt [propext, Quot.sound]
#axioms_within PLLND.F0.Mink.qmP_lt [propext, Quot.sound]
-- The order of ℚ.
#axioms_within PLLND.F0.Mink.rat_lt_iff [propext, Quot.sound]
#axioms_within PLLND.F0.Mink.rat_le_iff [propext, Quot.sound]
#axioms_within PLLND.F0.Mink.rat_eq_of_cross [propext, Quot.sound]
#axioms_within PLLND.F0.Mink.rat_trichotomy [propext, Quot.sound]
-- `?` on [0, 1]: cells, monotonicity, onto.
#axioms_within PLLND.F0.Mink.mink_of_num [propext, Quot.sound]
#axioms_within PLLND.F0.Mink.cell_zero [propext, Quot.sound]
#axioms_within PLLND.F0.Mink.cell_one [propext, Quot.sound]
#axioms_within PLLND.F0.Mink.cell_half [propext, Quot.sound]
#axioms_within PLLND.F0.Mink.cell_third [propext, Quot.sound]
#axioms_within PLLND.F0.Mink.cell_two_thirds [propext, Quot.sound]
#axioms_within PLLND.F0.Mink.cell_two_fifths [propext, Quot.sound]
#axioms_within PLLND.F0.Mink.cell_five_eighths [propext, Quot.sound]
#axioms_within PLLND.F0.Mink.cell_three_sevenths [propext, Quot.sound]
#axioms_within PLLND.F0.Mink.mink_lt [propext, Quot.sound]
#axioms_within PLLND.F0.Mink.sb_exists [propext, Quot.sound]
#axioms_within PLLND.F0.Mink.mink_onto [propext, Quot.sound]
-- `qm = ? ∘ σ` on ℚ.
#axioms_within PLLND.F0.Mink.sq_of_nonneg [propext, Quot.sound]
#axioms_within PLLND.F0.Mink.sq_of_neg [propext, Quot.sound]
#axioms_within PLLND.F0.Mink.num_cases [propext, Quot.sound]
#axioms_within PLLND.F0.Mink.qm_cells [propext, Quot.sound]
#axioms_within PLLND.F0.Mink.qm_lt [propext, Quot.sound]
#axioms_within PLLND.F0.Mink.qm_inj [propext, Quot.sound]
#axioms_within PLLND.F0.Mink.sq_bounds [propext, Quot.sound]
#axioms_within PLLND.F0.Mink.reduce [propext, Quot.sound]
#axioms_within PLLND.F0.Mink.qm_onto [propext, Quot.sound]
#axioms_within PLLND.F0.Mink.qm_eq_mink [propext, Quot.sound]
-- The embedding.
#axioms_within PLLND.F0.rat_vf_cf [propext, Quot.sound]
#axioms_within PLLND.F0.rat_embedding_cf [propext, Quot.sound]
-- The one choice pin: core's `/` on the right-hand sides (see § Bridge).
#axioms_within PLLND.F0.Mink.rq_bridge [propext, Classical.choice, Quot.sound]
