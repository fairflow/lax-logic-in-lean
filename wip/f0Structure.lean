import wip.f0Dyadic
import wip.f0Covers
import Meta.Audit

/-!
# How the covers and the copies of ℚ fit together in F0

F0 is the Lindenbaum algebra of the variable-free PLL formulas.  Notation:
`t n = rnSub n`, `g k = gap k`, and `f d = Dy.formula d` for the dyadic
construction of `wip/f0Dyadic.lean` (a lattice polynomial in the odd gaps
`g(2i+1)`, variable `i` read as `g(2i+1)`).  All pins `[propext, Quot.sound]`
except the one corollary marked, which uses excluded middle.

## R1. The ladder sits under the whole copy of ℚ (`ladder_le_formula`)

    n ≤ 15,  0 < d   ⟹   t n ⊢ f d

in particular `t4 ⊢ f d` and `t6 ⊢ f d` (`t4_le_formula`, `t6_le_formula`).
The variables of `F n m` are indices `idx (n+1) m = 2^(n+1) + m ≥ 3`, so `f d`
is a polynomial in gaps `g k` with `k ≥ 7` (not `k ≥ 5`).  Subterms `⊥` do
survive syntactically (`F n 0 = ⊥` is a disjunct of `F (n+1) 1`), but they do
no harm: `F n m` is TRUE at the all-true assignment when `m > 0`
(`F_eval_true`), so `true_entails_ctx` applies with the context `t15`, which
entails every `g k`, `k ≥ 7` (`t15 ⊢ t(2k+1) ⊢ g k`).  The rung order is
taken from the substitution instance of the `rnP` chains (`deriv_substP`),
not from `rungD`/`eo_le`, so no choice enters.  With `cover_1_4`
(`t1 ⋖ t4`, `wip/f0Covers.lean`): the copy of ℚ sits above the cover
`t1 ⋖ t4`, and above every rung up to `t15`.

## R2. Countably many mutually incomparable copies in any interval

Derivability between lattice polynomials is decided by their Boolean
semantics (`lpoly_deriv_iff`, through the decidable check `leCheck`: every
monomial of the disjunctive normal form of `q` makes `p` true):

    ⟦q⟧ ⊢ ⟦p⟧   ⟺   ∀ σ, q(σ) → p(σ)   ⟺   leCheck q p = true.

So `⟦q⟧ ⊬ ⟦p⟧` yields an assignment with `q` true and `p` false
(`nderiv_witness`, read off the failing monomial: no search over formulas).
For lattice polynomials `p`, `q` with `⟦p⟧ ⊢ ⟦q⟧` and `⟦q⟧ ⊬ ⟦p⟧`, the copies

    e k d = p ∨ (q ∧ c k d),     c k d = f d with variable v renamed B + 2^k (2v+1)

(`copyP`, `B` above every variable of `p` and `q`, so the variable sets of
`p`, `q` and the copies are pairwise disjoint) satisfy (`incomparable_copies`)

    ⟦p⟧ ⊢ e k d ⊢ ⟦q⟧,
    d < d'  ⟹  e k d ⊢ e k d'  and  e k d' ⊬ e k d,
    k ≠ k', 0 < d, d' < 1  ⟹  e k d ⊬ e k' d',

and `e k 0 ⊣⊢ ⟦p⟧`, `e k 1 ⊣⊢ ⟦q⟧` (`copy_zero`, `copy_one`).  Each `e k` is
an order embedding of the dyadics in `[0, 1]` into `[⟦p⟧, ⟦q⟧]` with the
endpoints fixed, and the images of `(0, 1)` are pairwise incomparable.
Remark (not a theorem): F0 is countable, so ℵ₀ is the largest possible number
of such copies.

## R3. The cover lemma (`cover_above`)

    DownTable c L,  [c] ⊬ a  ⟹  ∃ b,  a ⋖ b  ∧  b ⊢ a ∨ c        (a, c variable-free)

given that derivability between members of `L` is decided
(`hdec : ∀ x ∈ L, ∀ y ∈ L, x ⊢ y ∨ x ⊬ y`).  Distributivity: `y ↦ y ∧ c`
maps `[a, a ∨ c]` into `[a ∧ c, c] ⊆ ↓c`, which the table makes finite; a
minimal member `m` of `L` strictly above `a ∧ c` (found by a pass over `L`,
`exists_minimal`) gives `b = a ∨ m`.  Without `hdec` the same statement
holds with excluded middle (`cover_above_em`, pin with `Classical.choice`).
-/

open PLLFormula

namespace PLLND
namespace F0

open SemUI RNEmbed
open PLLND.LaxInfinite (atomFree)
open LPoly

/-! ## Lattice polynomials: general lemmas -/

/-- `true_entails` with any context formula: if `A` entails the gap of every
variable true at `σ`, then `A` entails every polynomial true at `σ`. -/
theorem true_entails_ctx (σ : Nat → Bool) (A : PLLFormula) :
    ∀ p : LPoly, (∀ n ∈ p.vars, σ n = true → Deriv [A] (gap (2 * n + 1))) →
      p.eval σ = true → Deriv [A] p.den
  | .var n, h, hp => h n (List.mem_singleton_self n) hp
  | .bot, _, hp => nomatch hp
  | .top, _, _ => Deriv.impIntro (Deriv.iden (.head _))
  | .and p q, h, hpq =>
      Deriv.andIntro
        (true_entails_ctx σ A p (fun n hn => h n (List.mem_append_left _ hn)) (band_true hpq).1)
        (true_entails_ctx σ A q (fun n hn => h n (List.mem_append_right _ hn)) (band_true hpq).2)
  | .or p q, h, hpq =>
      (bor_true hpq).elim
        (fun h' => Deriv.orIntro1
          (true_entails_ctx σ A p (fun n hn => h n (List.mem_append_left _ hn)) h'))
        (fun h' => Deriv.orIntro2
          (true_entails_ctx σ A q (fun n hn => h n (List.mem_append_right _ hn)) h'))

/-- `F n 0 = ⊥` at every level. -/
theorem F_zero : ∀ n, F n 0 = .bot
  | 0 => rfl
  | n + 1 => (F_even n 0).trans (F_zero n)

/-- At the all-true assignment `F n m` is true exactly when `m > 0`. -/
theorem F_eval_true : ∀ n m, 0 < m → (F n m).eval (fun _ => true) = true := by
  intro n
  induction n with
  | zero =>
      intro m hm
      show (if m = 0 then LPoly.bot else LPoly.top).eval (fun _ => true) = true
      rw [if_neg (by omega)]
      rfl
  | succ n ih =>
      intro m hm
      obtain ⟨k, rfl | rfl⟩ : ∃ k, m = 2 * k ∨ m = 2 * k + 1 := ⟨m / 2, by omega⟩
      · rw [F_even]
        exact ih k (by omega)
      · rw [F_odd]
        show ((F n k).eval (fun _ => true) ||
          ((F n (k + 1)).eval (fun _ => true) && true)) = true
        rw [ih (k + 1) (Nat.succ_pos k)]
        cases (F n k).eval (fun _ => true) <;> rfl

/-- At the all-false assignment `F n m` is false when `m < 2^n`. -/
theorem F_eval_false : ∀ n m, m < 2 ^ n → (F n m).eval (fun _ => false) = false := by
  intro n
  induction n with
  | zero =>
      intro m hm
      have h1 : (2 : Nat) ^ 0 = 1 := rfl
      have hm0 : m = 0 := by omega
      subst hm0
      rfl
  | succ n ih =>
      intro m hm
      have hpow := two_pow_succ n
      obtain ⟨k, rfl | rfl⟩ : ∃ k, m = 2 * k ∨ m = 2 * k + 1 := ⟨m / 2, by omega⟩
      · rw [F_even]
        exact ih k (by omega)
      · rw [F_odd]
        show ((F n k).eval (fun _ => false) ||
          ((F n (k + 1)).eval (fun _ => false) && false)) = false
        rw [ih k (by omega), Bool.and_false]
        rfl

/-- Every variable of `F n m` is at least `3`. -/
theorem F_vars_ge : ∀ n m, ∀ i ∈ (F n m).vars, 3 ≤ i := by
  intro n
  induction n with
  | zero =>
      intro m i hi
      have e : (F 0 m).vars = [] := by
        show (if m = 0 then LPoly.bot else LPoly.top).vars = []
        split <;> rfl
      rw [e] at hi
      nomatch hi
  | succ n ih =>
      intro m i hi
      obtain ⟨k, rfl | rfl⟩ : ∃ k, m = 2 * k ∨ m = 2 * k + 1 := ⟨m / 2, by omega⟩
      · rw [F_even] at hi
        exact ih k i hi
      · rw [F_odd] at hi
        have hi' : i ∈ (F n k).vars ++
            ((F n (k + 1)).vars ++ [idx (n + 1) (2 * k + 1)]) := hi
        rcases List.mem_append.mp hi' with h | h
        · exact ih k i h
        · rcases List.mem_append.mp h with h | h
          · exact ih (k + 1) i h
          · have e : i = idx (n + 1) (2 * k + 1) := List.mem_singleton.mp h
            subst e
            have hp := Nat.two_pow_pos n
            have hpow := two_pow_succ n
            unfold idx
            omega

/-! ## R1. The ladder up to `t15` lies under every `f d`, `d > 0` -/

theorem rnSub_odd_embed (k : Nat) : rnSub (2 * k + 1) = embed (rnP k).1 := by
  show embed (rn (2 * k + 1)) = _
  rw [rn_odd_eq]

theorem rnSub_even_embed (k : Nat) : rnSub (2 * k + 2) = embed (rnP k).2 := by
  show embed (rn (2 * k + 2)) = _
  rw [rn_even_eq]

/-- `t(2a+1) ⊢ t(2b+1)` for `a ≤ b`, through the substitution (no `rungD`). -/
theorem odd_odd_cf {a b : Nat} (h : a ≤ b) :
    Deriv [rnSub (2 * a + 1)] (rnSub (2 * b + 1)) := by
  rw [rnSub_odd_embed, rnSub_odd_embed]
  exact deriv_substP (deriv_odd_mono h)

/-- `t(2a+2) ⊢ t(2b+1)` for `a < b`, through the substitution. -/
theorem even_odd_cf {a b : Nat} (h : a < b) :
    Deriv [rnSub (2 * a + 2)] (rnSub (2 * b + 1)) := by
  rw [rnSub_even_embed, rnSub_odd_embed]
  exact deriv_substP (deriv_even_to_odd h)

/-- `t(2k+1) ⊢ g k` (weakening; `rung_le_gap` of `wip/connect.lean`). -/
theorem odd_rung_gap (k : Nat) : Deriv [rnSub (2 * k + 1)] (gap k) :=
  Deriv.impIntro (Deriv.iden (.tail _ (.head _)))

/-- `t15 ⊢ f d` for every dyadic `d > 0`. -/
theorem t15_le_formula (d : Dy) (hd : 0 < d.num) : Deriv [rnSub 15] d.formula :=
  true_entails_ctx (fun _ => true) (rnSub 15) (F d.exp d.num)
    (fun i hi _ => by
      have h3 := F_vars_ge d.exp d.num i hi
      exact Deriv.cutHead (odd_odd_cf (a := 7) (b := 2 * i + 1) (by omega))
        (odd_rung_gap (2 * i + 1)))
    (F_eval_true d.exp d.num hd)

/-- **R1.**  Every rung up to `t15` lies under every `f d` with `d > 0`:

    n ≤ 15,  0 < d   ⟹   t n ⊢ f d. -/
theorem ladder_le_formula {n : Nat} (hn : n ≤ 15) (d : Dy) (hd : 0 < d.num) :
    Deriv [rnSub n] d.formula := by
  refine Deriv.cutHead ?_ (t15_le_formula d hd)
  cases n with
  | zero => exact Deriv.falsoElim _ (Deriv.iden (.head _))
  | succ m =>
      obtain ⟨k, rfl | rfl⟩ : ∃ k, m = 2 * k ∨ m = 2 * k + 1 := ⟨m / 2, by omega⟩
      · exact odd_odd_cf (a := k) (b := 7) (by omega)
      · exact even_odd_cf (a := k) (b := 7) (by omega)

/-- `t4 ⊢ f d` for `d > 0` (`t4 = ¬¬◯⊥` up to `⊣⊢`; `t1 ⋖ t4` is `cover_1_4`). -/
theorem t4_le_formula (d : Dy) (hd : 0 < d.num) : Deriv [rnSub 4] d.formula :=
  ladder_le_formula (by decide) d hd

/-- `t6 ⊢ f d` for `d > 0`. -/
theorem t6_le_formula (d : Dy) (hd : 0 < d.num) : Deriv [rnSub 6] d.formula :=
  ladder_le_formula (by decide) d hd

/-! ## R2. Derivability between lattice polynomials is decidable -/

namespace LPoly

/-- Disjunctive normal form: a list of monomials (lists of variables). -/
def dnf : LPoly → List (List Nat)
  | var n => [[n]]
  | bot => []
  | top => [[]]
  | and p q => p.dnf.flatMap fun M => q.dnf.map fun M' => M ++ M'
  | or p q => p.dnf ++ q.dnf

/-- Renaming of variables. -/
def rename (ρ : Nat → Nat) : LPoly → LPoly
  | var n => var (ρ n)
  | bot => bot
  | top => top
  | and p q => and (p.rename ρ) (q.rename ρ)
  | or p q => or (p.rename ρ) (q.rename ρ)

end LPoly

/-- A monomial, read in F0: the conjunction of its gaps. -/
def mono (M : List Nat) : PLLFormula := bigAnd (M.map fun i => gap (2 * i + 1))

/-- The indicator assignment of a monomial. -/
def ind (M : List Nat) (n : Nat) : Bool := decide (n ∈ M)

/-- **The decidable check**: every monomial of `q` makes `p` true. -/
def leCheck (q p : LPoly) : Bool := q.dnf.all fun M => p.eval (ind M)

theorem bigOr_le {χ : PLLFormula} :
    ∀ {Ds : List PLLFormula}, (∀ φ ∈ Ds, Deriv [φ] χ) → Deriv [PLLND.bigOr Ds] χ
  | [], _ => Deriv.falsoElim _ (Deriv.iden (.head _))
  | ψ :: _, h => Deriv.orElim (Deriv.iden (.head _))
      (Deriv.toHead (h ψ (.head _)))
      (Deriv.toHead (bigOr_le fun φ hφ => h φ (.tail _ hφ)))

/-- `∨`-elimination over a finite disjunction, in any context (choice-free;
`Deriv.bigOrElim` goes through `Nonempty.some`). -/
theorem bigOr_elim {χ : PLLFormula} :
    ∀ {Ds Γ : List PLLFormula}, Deriv Γ (PLLND.bigOr Ds) →
      (∀ φ ∈ Ds, Deriv (φ :: Γ) χ) → Deriv Γ χ
  | [], _, p, _ => Deriv.falsoElim _ p
  | ψ :: Ds, Γ, p, br => Deriv.orElim p (br ψ (.head _))
      (bigOr_elim (Ds := Ds) (Γ := PLLND.bigOr Ds :: Γ) (Deriv.iden (.head _))
        fun φ hφ => (br φ (.tail _ hφ)).rename fun x hx => by
          cases hx with
          | head => exact .head _
          | tail _ h => exact .tail _ (.tail _ h))

theorem bigOr_sub {A B : List PLLFormula} (h : ∀ x ∈ A, x ∈ B) :
    Deriv [PLLND.bigOr A] (PLLND.bigOr B) :=
  bigOr_le fun x hx => Deriv.bigOrIntroT (h x hx)

/-- Every polynomial entails its disjunctive normal form. -/
theorem dnf_derive : ∀ p : LPoly, Deriv [p.den] (PLLND.bigOr (p.dnf.map mono))
  | .var _ => Deriv.orIntro1 (Deriv.iden (.head _))
  | .bot => Deriv.iden (.head _)
  | .top => Deriv.orIntro1 (Deriv.impIntro (Deriv.iden (.head _)))
  | .and p q => by
      have hp : Deriv [(LPoly.and p q).den] (PLLND.bigOr (p.dnf.map mono)) :=
        Deriv.cutHead (Deriv.andElim1 (Deriv.iden (.head _))) (dnf_derive p)
      have hq : Deriv [(LPoly.and p q).den] (PLLND.bigOr (q.dnf.map mono)) :=
        Deriv.cutHead (Deriv.andElim2 (Deriv.iden (.head _))) (dnf_derive q)
      refine bigOr_elim hp fun x hx => ?_
      obtain ⟨M, hM, rfl⟩ := List.mem_map.mp hx
      refine bigOr_elim (Deriv.rename (fun y hy => List.Mem.tail _ hy) hq) fun y hy => ?_
      obtain ⟨M', hM', rfl⟩ := List.mem_map.mp hy
      have hmem : mono (M ++ M') ∈
          ((p.dnf.flatMap fun M => q.dnf.map fun M' => M ++ M').map mono) :=
        List.mem_map.mpr ⟨M ++ M',
          List.mem_flatMap.mpr ⟨M, hM, List.mem_map.mpr ⟨M', hM', rfl⟩⟩, rfl⟩
      refine Deriv.cutHead ?_ (Deriv.bigOrIntroT hmem)
      refine Deriv.bigAndIntro fun D hD => ?_
      rw [List.map_append] at hD
      rcases List.mem_append.mp hD with h | h
      · exact Deriv.cutHead (Deriv.iden (.tail _ (.head _))) (Deriv.bigAndElim h)
      · exact Deriv.cutHead (Deriv.iden (.head _)) (Deriv.bigAndElim h)
  | .or p q => by
      refine Deriv.orElim (Deriv.iden (.head _)) ?_ ?_
      · refine Deriv.toHead (Deriv.cutHead (dnf_derive p) (bigOr_sub fun x hx => ?_))
        obtain ⟨M, hM, rfl⟩ := List.mem_map.mp hx
        exact List.mem_map.mpr ⟨M, List.mem_append_left _ hM, rfl⟩
      · refine Deriv.toHead (Deriv.cutHead (dnf_derive q) (bigOr_sub fun x hx => ?_))
        obtain ⟨M, hM, rfl⟩ := List.mem_map.mp hx
        exact List.mem_map.mpr ⟨M, List.mem_append_right _ hM, rfl⟩

/-- A monomial of `p`, true at `σ`, makes `p` true at `σ`. -/
theorem dnf_eval (σ : Nat → Bool) :
    ∀ (p : LPoly) (M : List Nat), M ∈ p.dnf → (∀ n ∈ M, σ n = true) → p.eval σ = true
  | .var n, M, hM, h => by
      have hM' : M ∈ [[n]] := hM
      have e : M = [n] := List.mem_singleton.mp hM'
      subst e
      exact h n (List.mem_singleton_self n)
  | .bot, M, hM, _ => nomatch (hM : M ∈ ([] : List (List Nat)))
  | .top, _, _, _ => rfl
  | .and p q, M, hM, h => by
      obtain ⟨M1, h1, hM'⟩ := List.mem_flatMap.mp hM
      obtain ⟨M2, h2, rfl⟩ := List.mem_map.mp hM'
      show (p.eval σ && q.eval σ) = true
      rw [dnf_eval σ p M1 h1 (fun n hn => h n (List.mem_append_left _ hn)),
        dnf_eval σ q M2 h2 (fun n hn => h n (List.mem_append_right _ hn))]
      rfl
  | .or p q, M, hM, h => by
      show (p.eval σ || q.eval σ) = true
      rcases List.mem_append.mp hM with h1 | h1
      · rw [dnf_eval σ p M h1 h]
        rfl
      · rw [dnf_eval σ q M h1 h]
        cases p.eval σ <;> rfl

theorem all_mem {α : Type} {f : α → Bool} :
    ∀ {l : List α}, l.all f = true → ∀ x ∈ l, f x = true
  | [], _, _, hx => nomatch hx
  | y :: _, h, x, hx => by
      have h' : (f y && _) = true := h
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact (band_true h').1
      · exact all_mem (band_true h').2 x hx'

theorem all_false {α : Type} {f : α → Bool} :
    ∀ {l : List α}, l.all f = false → ∃ x ∈ l, f x = false
  | [], h => nomatch h
  | y :: _, h => by
      have h' : (f y && _) = false := h
      rcases band_false h' with h1 | h1
      · exact ⟨y, .head _, h1⟩
      · obtain ⟨x, hx, hfx⟩ := all_false h1
        exact ⟨x, .tail _ hx, hfx⟩

theorem leCheck_sound {q p : LPoly} (h : leCheck q p = true) : Deriv [q.den] p.den := by
  refine Deriv.cutHead (dnf_derive q) (bigOr_le fun x hx => ?_)
  obtain ⟨M, hM, rfl⟩ := List.mem_map.mp hx
  exact true_entails (ind M) M p (fun _ _ hn => of_decide_eq_true hn) (all_mem h M hM)

theorem leCheck_witness {q p : LPoly} (h : leCheck q p = false) :
    ∃ σ : Nat → Bool, q.eval σ = true ∧ p.eval σ = false := by
  obtain ⟨M, hM, hp⟩ := all_false h
  exact ⟨ind M, dnf_eval (ind M) q M hM (fun _ hn => decide_eq_true hn), hp⟩

/-- **Derivability between lattice polynomials is Boolean entailment**
(F0's odd gaps generate a free distributive lattice). -/
theorem lpoly_deriv_iff (q p : LPoly) :
    Deriv [q.den] p.den ↔ ∀ σ : Nat → Bool, q.eval σ = true → p.eval σ = true := by
  constructor
  · intro h σ hq
    cases hp : p.eval σ with
    | true => rfl
    | false => exact absurd h (separate σ hq hp)
  · intro h
    cases hc : leCheck q p with
    | true => exact leCheck_sound hc
    | false =>
        obtain ⟨σ, hq, hp⟩ := leCheck_witness hc
        have h' := h σ hq
        rw [hp] at h'
        exact nomatch h'

/-- **... and it is decided by `leCheck`.** -/
theorem lpoly_deriv_decide (q p : LPoly) : Deriv [q.den] p.den ↔ leCheck q p = true := by
  constructor
  · intro h
    cases hc : leCheck q p with
    | true => rfl
    | false =>
        obtain ⟨σ, hq, hp⟩ := leCheck_witness hc
        exact absurd h (separate σ hq hp)
  · exact leCheck_sound

/-- From `⟦q⟧ ⊬ ⟦p⟧`, a Boolean witness: `q` true, `p` false. -/
theorem nderiv_witness {q p : LPoly} (h : [q.den] ⊬ p.den) :
    ∃ σ : Nat → Bool, q.eval σ = true ∧ p.eval σ = false := by
  cases hc : leCheck q p with
  | true => exact absurd (leCheck_sound hc) h
  | false => exact leCheck_witness hc

/-! ## R2. Renaming and the disjoint copies -/

theorem eval_rename (ρ : Nat → Nat) (σ τ : Nat → Bool) (h : ∀ v, σ (ρ v) = τ v) :
    ∀ p : LPoly, (p.rename ρ).eval σ = p.eval τ
  | .var n => h n
  | .bot => rfl
  | .top => rfl
  | .and p q => by
      show ((p.rename ρ).eval σ && (q.rename ρ).eval σ) = (p.eval τ && q.eval τ)
      rw [eval_rename ρ σ τ h p, eval_rename ρ σ τ h q]
  | .or p q => by
      show ((p.rename ρ).eval σ || (q.rename ρ).eval σ) = (p.eval τ || q.eval τ)
      rw [eval_rename ρ σ τ h p, eval_rename ρ σ τ h q]

theorem eval_congr (σ τ : Nat → Bool) :
    ∀ p : LPoly, (∀ n ∈ p.vars, σ n = τ n) → p.eval σ = p.eval τ
  | .var n, h => h n (List.mem_singleton_self n)
  | .bot, _ => rfl
  | .top, _ => rfl
  | .and p q, h => by
      show (p.eval σ && q.eval σ) = (p.eval τ && q.eval τ)
      rw [eval_congr σ τ p (fun n hn => h n (List.mem_append_left _ hn)),
        eval_congr σ τ q (fun n hn => h n (List.mem_append_right _ hn))]
  | .or p q, h => by
      show (p.eval σ || q.eval σ) = (p.eval τ || q.eval τ)
      rw [eval_congr σ τ p (fun n hn => h n (List.mem_append_left _ hn)),
        eval_congr σ τ q (fun n hn => h n (List.mem_append_right _ hn))]

/-- The code of variable `v` of copy `k`, above the bound `B`. -/
def code (B k v : Nat) : Nat := B + 2 ^ k * (2 * v + 1)

theorem pow_odd_inj :
    ∀ (k k' v v' : Nat), 2 ^ k * (2 * v + 1) = 2 ^ k' * (2 * v' + 1) → k = k' ∧ v = v'
  | 0, 0, v, v', h => by
      rw [Nat.pow_zero, Nat.one_mul, Nat.one_mul] at h
      exact ⟨rfl, by omega⟩
  | 0, k' + 1, v, v', h => by
      have e : 2 ^ (k' + 1) * (2 * v' + 1) = 2 * (2 ^ k' * (2 * v' + 1)) := by
        rw [two_pow_succ, Nat.mul_assoc]
      rw [e, Nat.pow_zero, Nat.one_mul] at h
      omega
  | k + 1, 0, v, v', h => by
      have e : 2 ^ (k + 1) * (2 * v + 1) = 2 * (2 ^ k * (2 * v + 1)) := by
        rw [two_pow_succ, Nat.mul_assoc]
      rw [e, Nat.pow_zero, Nat.one_mul] at h
      omega
  | k + 1, k' + 1, v, v', h => by
      have e : 2 ^ (k + 1) * (2 * v + 1) = 2 * (2 ^ k * (2 * v + 1)) := by
        rw [two_pow_succ, Nat.mul_assoc]
      have e' : 2 ^ (k' + 1) * (2 * v' + 1) = 2 * (2 ^ k' * (2 * v' + 1)) := by
        rw [two_pow_succ, Nat.mul_assoc]
      rw [e, e'] at h
      have ih := pow_odd_inj k k' v v' (by omega)
      exact ⟨by rw [ih.1], ih.2⟩

theorem code_inj {B k k' v v' : Nat} (h : code B k v = code B k' v') : k = k' ∧ v = v' :=
  pow_odd_inj k k' v v' (Nat.add_left_cancel h)

theorem le_code (B k v : Nat) : v ≤ code B k v := by
  have h := Nat.le_mul_of_pos_left (2 * v + 1) (Nat.two_pow_pos k)
  unfold code
  omega

theorem any_true {α : Type} {f : α → Bool} :
    ∀ {l : List α}, l.any f = true → ∃ x ∈ l, f x = true
  | [], h => nomatch h
  | y :: _, h => by
      have h' : (f y || _) = true := h
      rcases bor_true h' with h1 | h1
      · exact ⟨y, .head _, h1⟩
      · obtain ⟨x, hx, hfx⟩ := any_true h1
        exact ⟨x, .tail _ hx, hfx⟩

theorem any_of_mem {α : Type} {f : α → Bool} :
    ∀ {l : List α} {x : α}, x ∈ l → f x = true → l.any f = true
  | y :: l, x, hx, hf => by
      show (f y || l.any f) = true
      rcases List.mem_cons.mp hx with rfl | hx'
      · rw [hf]
        rfl
      · rw [any_of_mem hx' hf]
        cases f y <;> rfl

/-- Pull an assignment back along an injection, by a bounded search
(no decoding of `ρ`). -/
def pull (ρ : Nat → Nat) (τ : Nat → Bool) (j : Nat) : Bool :=
  (List.range (j + 1)).any fun v => decide (ρ v = j) && τ v

theorem pull_at {ρ : Nat → Nat} (τ : Nat → Bool) (hinj : ∀ v v', ρ v = ρ v' → v = v')
    (hle : ∀ v, v ≤ ρ v) (v : Nat) : pull ρ τ (ρ v) = τ v := by
  cases hτ : τ v with
  | true =>
      refine any_of_mem (List.mem_range.mpr (Nat.lt_succ_of_le (hle v))) ?_
      show (decide (ρ v = ρ v) && τ v) = true
      rw [decide_eq_true (rfl : ρ v = ρ v), hτ]
      rfl
  | false =>
      cases hp : pull ρ τ (ρ v) with
      | false => rfl
      | true =>
          obtain ⟨w, _, hw⟩ := any_true hp
          have h1 := band_true hw
          have hw' : w = v := hinj w v (of_decide_eq_true h1.1)
          subst hw'
          rw [hτ] at h1
          exact nomatch h1.2

theorem pull_off {ρ : Nat → Nat} (τ : Nat → Bool) {j : Nat} (h : ∀ v, ρ v ≠ j) :
    pull ρ τ j = false := by
  cases hp : pull ρ τ j with
  | false => rfl
  | true =>
      obtain ⟨w, _, hw⟩ := any_true hp
      exact absurd (of_decide_eq_true (band_true hw).1) (h w)

/-- The assignment: `σ0` below `B`, `τ` on copy `k`, false elsewhere. -/
def asg (σ0 : Nat → Bool) (B k : Nat) (τ : Nat → Bool) (j : Nat) : Bool :=
  if j < B then σ0 j else pull (code B k) τ j

theorem asg_lo (σ0 : Nat → Bool) (B k : Nat) (τ : Nat → Bool) {j : Nat} (h : j < B) :
    asg σ0 B k τ j = σ0 j := by
  unfold asg
  rw [if_pos h]

theorem asg_code (σ0 : Nat → Bool) (B k : Nat) (τ : Nat → Bool) (v : Nat) :
    asg σ0 B k τ (code B k v) = τ v := by
  unfold asg
  rw [if_neg (show ¬ code B k v < B from Nat.not_lt.mpr (Nat.le_add_right B _))]
  exact pull_at τ (fun _ _ h => (code_inj h).2) (le_code B k) v

theorem asg_other (σ0 : Nat → Bool) (B : Nat) {k k' : Nat} (hk : k ≠ k') (τ : Nat → Bool)
    (v : Nat) : asg σ0 B k τ (code B k' v) = false := by
  unfold asg
  rw [if_neg (show ¬ code B k' v < B from Nat.not_lt.mpr (Nat.le_add_right B _))]
  exact pull_off τ fun u hu => hk (code_inj hu).1

/-- A bound above every variable of `p` and `q`. -/
def bnd (p q : LPoly) : Nat := (p.vars ++ q.vars).foldr max 0 + 1

theorem lt_bnd_l {p q : LPoly} {n : Nat} (h : n ∈ p.vars) : n < bnd p q :=
  Nat.lt_succ_of_le (le_foldr_max (List.mem_append_left _ h))

theorem lt_bnd_r {p q : LPoly} {n : Nat} (h : n ∈ q.vars) : n < bnd p q :=
  Nat.lt_succ_of_le (le_foldr_max (List.mem_append_right _ h))

/-- The copy `k` of the dyadic chain between `p` and `q`:
`e k d = p ∨ (q ∧ c k d)`. -/
def copyP (p q : LPoly) (k : Nat) (d : Dy) : LPoly :=
  p.or (q.and ((F d.exp d.num).rename (code (bnd p q) k)))

/-- `e k d` in F0. -/
def copyF (p q : LPoly) (k : Nat) (d : Dy) : PLLFormula := (copyP p q k d).den

theorem copy_eval (p q : LPoly) (σ0 τ : Nat → Bool) (k : Nat) (d : Dy) :
    (copyP p q k d).eval (asg σ0 (bnd p q) k τ) =
      (p.eval σ0 || (q.eval σ0 && (F d.exp d.num).eval τ)) := by
  show (p.eval (asg σ0 (bnd p q) k τ) || (q.eval (asg σ0 (bnd p q) k τ) &&
    ((F d.exp d.num).rename (code (bnd p q) k)).eval (asg σ0 (bnd p q) k τ))) = _
  rw [eval_congr (asg σ0 (bnd p q) k τ) σ0 p fun n hn => asg_lo σ0 _ k τ (lt_bnd_l hn),
    eval_congr (asg σ0 (bnd p q) k τ) σ0 q fun n hn => asg_lo σ0 _ k τ (lt_bnd_r hn),
    eval_rename (code (bnd p q) k) (asg σ0 (bnd p q) k τ) τ (asg_code σ0 _ k τ)]

theorem copy_eval_other (p q : LPoly) (σ0 τ : Nat → Bool) {k k' : Nat} (hk : k ≠ k')
    (d : Dy) :
    (copyP p q k' d).eval (asg σ0 (bnd p q) k τ) =
      (p.eval σ0 || (q.eval σ0 && (F d.exp d.num).eval (fun _ => false))) := by
  show (p.eval (asg σ0 (bnd p q) k τ) || (q.eval (asg σ0 (bnd p q) k τ) &&
    ((F d.exp d.num).rename (code (bnd p q) k')).eval (asg σ0 (bnd p q) k τ))) = _
  rw [eval_congr (asg σ0 (bnd p q) k τ) σ0 p fun n hn => asg_lo σ0 _ k τ (lt_bnd_l hn),
    eval_congr (asg σ0 (bnd p q) k τ) σ0 q fun n hn => asg_lo σ0 _ k τ (lt_bnd_r hn),
    eval_rename (code (bnd p q) k') (asg σ0 (bnd p q) k τ) (fun _ => false)
      (asg_other σ0 _ hk τ)]

theorem bool_step : ∀ {a b c c' : Bool}, (c = true → c' = true) →
    (a || (b && c)) = true → (a || (b && c')) = true
  | true, _, _, _, _, _ => rfl
  | false, false, _, _, _, h => h
  | false, true, _, _, hc, h => hc h

/-- Every copy is variable-free. -/
theorem copy_vf (p q : LPoly) (k : Nat) (d : Dy) : atomFree (copyF p q k d) = true :=
  LPoly.den_vf _

theorem copy_lower (p q : LPoly) (k : Nat) (d : Dy) : Deriv [p.den] (copyF p q k d) :=
  Deriv.orIntro1 (Deriv.iden (.head _))

theorem copy_upper {p q : LPoly} (hpq : Deriv [p.den] q.den) (k : Nat) (d : Dy) :
    Deriv [copyF p q k d] q.den := by
  show Deriv [p.den.or (q.den.and ((F d.exp d.num).rename (code (bnd p q) k)).den)] q.den
  exact Deriv.orElim (Deriv.iden (.head _)) (Deriv.toHead hpq)
    (Deriv.toHead (Deriv.andElim1 (Deriv.iden (.head _))))

theorem copy_mono (p q : LPoly) (k : Nat) {d d' : Dy} (h : d.lt d') :
    Deriv [copyF p q k d] (copyF p q k d') := by
  refine (lpoly_deriv_iff (copyP p q k d) (copyP p q k d')).mpr fun σ hσ => ?_
  have hc : ∀ τ, (F d.exp d.num).eval τ = true → (F d'.exp d'.num).eval τ = true :=
    fun τ => (lpoly_deriv_iff (F d.exp d.num) (F d'.exp d'.num)).mp
      (dyadic_embedding d d' h).1 τ
  have e : ∀ e : Dy, (copyP p q k e).eval σ =
      (p.eval σ || (q.eval σ && (F e.exp e.num).eval fun v => σ (code (bnd p q) k v))) :=
    fun e => by
      show (p.eval σ || (q.eval σ && ((F e.exp e.num).rename _).eval σ)) = _
      rw [eval_rename _ σ _ (fun _ => rfl)]
  rw [e] at hσ ⊢
  exact bool_step (hc _) hσ

theorem copy_strict {p q : LPoly} (hqp : [q.den] ⊬ p.den) (k : Nat) {d d' : Dy}
    (h : d.lt d') : [copyF p q k d'] ⊬ copyF p q k d := by
  obtain ⟨σ0, hq, hp⟩ := nderiv_witness hqp
  have h' : d.num * 2 ^ d'.exp < d'.num * 2 ^ d.exp := h
  have hC : 0 < d'.num := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, Nat.zero_mul] at h'
    exact Nat.not_lt_zero _ h'
  refine separate (asg σ0 (bnd p q) k (thr d'.num d'.exp)) ?_ ?_
  · rw [copy_eval, hp, hq, F_eval d'.num d'.exp hC d'.le d'.exp d'.num d'.le]
    show decide (d'.num * 2 ^ d'.exp ≤ d'.num * 2 ^ d'.exp) = true
    exact decide_eq_true (Nat.le_refl _)
  · rw [copy_eval, hp, hq, F_eval d'.num d'.exp hC d'.le d.exp d.num d.le]
    show decide (d'.num * 2 ^ d.exp ≤ d.num * 2 ^ d'.exp) = false
    exact decide_eq_false (Nat.not_le.mpr h')

theorem copy_cross {p q : LPoly} (hqp : [q.den] ⊬ p.den) {k k' : Nat} (hk : k ≠ k')
    {d d' : Dy} (hd : 0 < d.num) (hd' : d'.num < 2 ^ d'.exp) :
    [copyF p q k d] ⊬ copyF p q k' d' := by
  obtain ⟨σ0, hq, hp⟩ := nderiv_witness hqp
  refine separate (asg σ0 (bnd p q) k (fun _ => true)) ?_ ?_
  · rw [copy_eval, hp, hq, F_eval_true _ _ hd]
    rfl
  · rw [copy_eval_other p q σ0 _ hk, hp, hq, F_eval_false _ _ hd']
    rfl

/-- `e k 0 ⊣⊢ ⟦p⟧`. -/
theorem copy_zero (p q : LPoly) (k : Nat) :
    Interd (copyF p q k ⟨0, 0, Nat.zero_le _⟩) p.den := by
  refine ⟨?_, copy_lower p q k _⟩
  refine (lpoly_deriv_iff (copyP p q k ⟨0, 0, Nat.zero_le _⟩) p).mpr fun σ hσ => ?_
  have hσ' : (p.eval σ || (q.eval σ && false)) = true := hσ
  rw [Bool.and_false, Bool.or_false] at hσ'
  exact hσ'

/-- `e k 1 ⊣⊢ ⟦q⟧`. -/
theorem copy_one {p q : LPoly} (hpq : Deriv [p.den] q.den) (k : Nat) :
    Interd (copyF p q k ⟨1, 0, Nat.le_refl _⟩) q.den := by
  refine ⟨copy_upper hpq k _, ?_⟩
  show Deriv [q.den] (p.den.or (q.den.and (LPoly.top.rename _).den))
  exact Deriv.orIntro2 (Deriv.andIntro (Deriv.iden (.head _))
    (Deriv.impIntro (Deriv.iden (.head _))))

/-- **R2.**  Between lattice polynomials `p < q` in F0 hang countably many
pairwise incomparable copies of the dyadics, each an order embedding of the
dyadics in `[0, 1]` into `[⟦p⟧, ⟦q⟧]`:

    ⟦p⟧ ⊢ e k d ⊢ ⟦q⟧,
    d < d'  ⟹  e k d ⊢ e k d'  ∧  e k d' ⊬ e k d,
    k ≠ k', 0 < d, d' < 1  ⟹  e k d ⊬ e k' d'. -/
theorem incomparable_copies (p q : LPoly) (hpq : Deriv [p.den] q.den)
    (hqp : [q.den] ⊬ p.den) :
    ∃ e : Nat → Dy → PLLFormula,
      (∀ (k : Nat) (d : Dy), atomFree (e k d) = true) ∧
      (∀ (k : Nat) (d : Dy), Deriv [p.den] (e k d) ∧ Deriv [e k d] q.den) ∧
      (∀ (k : Nat) (d d' : Dy), d.lt d' → Deriv [e k d] (e k d') ∧ ([e k d'] ⊬ e k d)) ∧
      (∀ (k k' : Nat) (d d' : Dy), k ≠ k' → 0 < d.num → d'.num < 2 ^ d'.exp →
        [e k d] ⊬ e k' d') :=
  ⟨copyF p q, copy_vf p q, fun k d => ⟨copy_lower p q k d, copy_upper hpq k d⟩,
    fun k _ _ h => ⟨copy_mono p q k h, copy_strict hqp k h⟩,
    fun _ _ _ _ hk hd hd' => copy_cross hqp hk hd hd'⟩

/-! ## R3. The cover lemma -/

/-- Strict order. -/
def SLt (x y : PLLFormula) : Prop := Deriv [x] y ∧ ([y] ⊬ x)

theorem SLt.irrefl (x : PLLFormula) : ¬ SLt x x := fun h => h.2 (Deriv.iden (.head _))

theorem SLt.trans {x y z : PLLFormula} (h1 : SLt x y) (h2 : SLt y z) : SLt x z :=
  ⟨Deriv.cutHead h1.1 h2.1, fun hzx => h2.2 (Deriv.cutHead hzx h1.1)⟩

/-- A pass over a list, keeping a current candidate that only moves down. -/
theorem minimal_pass {L : List PLLFormula} (P : PLLFormula → Prop)
    (hP : ∀ x ∈ L, P x ∨ ¬ P x) (hdec : ∀ x ∈ L, ∀ y ∈ L, SLt x y ∨ ¬ SLt x y) :
    ∀ (l1 : List PLLFormula), (∀ x ∈ l1, x ∈ L) → ∀ m ∈ L, P m →
      ∃ m' ∈ L, P m' ∧ (m' = m ∨ SLt m' m) ∧ ∀ l ∈ l1, P l → ¬ SLt l m'
  | [], _, m, hm, hPm => ⟨m, hm, hPm, Or.inl rfl, fun _ h => nomatch h⟩
  | x :: rest, hsub, m, hm, hPm => by
      have hx : x ∈ L := hsub x (.head _)
      have hrest : ∀ y ∈ rest, y ∈ L := fun y hy => hsub y (.tail _ hy)
      rcases hP x hx with hPx | hPx
      · rcases hdec x hx m hm with hxm | hxm
        · -- move down to `x`
          obtain ⟨m', hm', hPm', hrel, hmin⟩ := minimal_pass P hP hdec rest hrest x hx hPx
          refine ⟨m', hm', hPm', Or.inr ?_, fun l hl hPl => ?_⟩
          · rcases hrel with rfl | hlt
            · exact hxm
            · exact hlt.trans hxm
          · rcases List.mem_cons.mp hl with rfl | hl'
            · intro hlm
              rcases hrel with rfl | hlt
              · exact SLt.irrefl _ hlm
              · exact hlt.2 hlm.1
            · exact hmin l hl' hPl
        · -- keep `m`
          obtain ⟨m', hm', hPm', hrel, hmin⟩ := minimal_pass P hP hdec rest hrest m hm hPm
          refine ⟨m', hm', hPm', hrel, fun l hl hPl => ?_⟩
          rcases List.mem_cons.mp hl with rfl | hl'
          · intro hlm
            rcases hrel with rfl | hlt
            · exact hxm hlm
            · exact hxm (hlm.trans hlt)
          · exact hmin l hl' hPl
      · obtain ⟨m', hm', hPm', hrel, hmin⟩ := minimal_pass P hP hdec rest hrest m hm hPm
        refine ⟨m', hm', hPm', hrel, fun l hl hPl => ?_⟩
        rcases List.mem_cons.mp hl with rfl | hl'
        · exact absurd hPl hPx
        · exact hmin l hl' hPl

/-- A minimal element of a decidable subset of a finite list. -/
theorem exists_minimal {L : List PLLFormula} (P : PLLFormula → Prop)
    (hP : ∀ x ∈ L, P x ∨ ¬ P x) (hdec : ∀ x ∈ L, ∀ y ∈ L, SLt x y ∨ ¬ SLt x y)
    {x0 : PLLFormula} (hx0 : x0 ∈ L) (hP0 : P x0) :
    ∃ m ∈ L, P m ∧ ∀ l ∈ L, P l → ¬ SLt l m :=
  let ⟨m, hm, hPm, _, hmin⟩ := minimal_pass P hP hdec L (fun _ h => h) x0 hx0 hP0
  ⟨m, hm, hPm, hmin⟩

theorem slt_dec {L : List PLLFormula}
    (hdec : ∀ x ∈ L, ∀ y ∈ L, Deriv [x] y ∨ ([x] ⊬ y)) :
    ∀ x ∈ L, ∀ y ∈ L, SLt x y ∨ ¬ SLt x y := fun x hx y hy => by
  rcases hdec x hx y hy with hxy | hxy
  · rcases hdec y hy x hx with hyx | hyx
    · exact Or.inr fun h => h.2 hyx
    · exact Or.inl ⟨hxy, hyx⟩
  · exact Or.inr fun h => hxy h.1

/-- **R3, the cover lemma.**  If `c` has a finite downset table `L` whose
order is decided, and `c ⊬ a`, then `a` has a cover `b` below `a ∨ c`:

    DownTable c L,  [c] ⊬ a  ⟹  ∃ b,  a ⋖ b  ∧  b ⊢ a ∨ c. -/
theorem cover_above {c a : PLLFormula} {L : List PLLFormula} (T : DownTable c L)
    (hdec : ∀ x ∈ L, ∀ y ∈ L, Deriv [x] y ∨ ([x] ⊬ y))
    (ha : atomFree a = true) (hc : atomFree c = true) (hca : [c] ⊬ a) :
    ∃ b : PLLFormula, Covers a b ∧ Deriv [b] (a.or c) := by
  have hac_vf : atomFree (a.and c) = true := by
    show (atomFree a && atomFree c) = true
    rw [ha, hc]
    rfl
  -- `a ∧ c` is a member `l0` of the table
  obtain ⟨l0, hl0, i0⟩ := T.classify_below hac_vf (Deriv.andElim2 (Deriv.iden (.head _)))
  have hl0a : Deriv [l0] a := Deriv.cutHead i0.2 (Deriv.andElim1 (Deriv.iden (.head _)))
  -- the members strictly above `l0`
  let P : PLLFormula → Prop := fun l => SLt l0 l
  have hP : ∀ x ∈ L, P x ∨ ¬ P x := fun x hx => slt_dec hdec l0 hl0 x hx
  have hPc : P c := by
    refine ⟨T.below l0 hl0, fun hcl0 => hca (Deriv.cutHead hcl0 hl0a)⟩
  obtain ⟨m, hm, hPm, hmin⟩ :=
    exists_minimal P hP (slt_dec hdec) T.top_mem hPc
  have hmc : Deriv [m] c := T.below m hm
  -- `a ∧ c ⊢ m`
  have hacm : Deriv [a.and c] m := Deriv.cutHead i0.1 hPm.1
  refine ⟨a.or m, ⟨Deriv.orIntro1 (Deriv.iden (.head _)), ?_, ?_⟩, ?_⟩
  · -- `a ∨ m ⊬ a`
    intro hb
    have hma : Deriv [m] a := Deriv.cutHead (Deriv.orIntro2 (Deriv.iden (.head _))) hb
    exact hPm.2 (Deriv.cutHead (Deriv.andIntro hma hmc) i0.1)
  · intro x hx hax hxb
    have hy_vf : atomFree (x.and c) = true := by
      show (atomFree x && atomFree c) = true
      rw [hx, hc]
      rfl
    obtain ⟨l, hl, il⟩ := T.classify_below hy_vf (Deriv.andElim2 (Deriv.iden (.head _)))
    -- `x ∧ c ⊢ m`
    have hxcm : Deriv [x.and c] m := by
      refine Deriv.orElim (Deriv.cutHead (Deriv.andElim1 (Deriv.iden (.head _))) hxb) ?_
        (Deriv.iden (.head _))
      exact Deriv.cutHead
        (Deriv.andIntro (Deriv.iden (.head _))
          (Deriv.andElim2 (Deriv.iden (.tail _ (.head _)))))
        hacm
    -- `l0 ⊢ l`
    have hl0l : Deriv [l0] l := by
      refine Deriv.cutHead (Deriv.cutHead i0.2 ?_) il.1
      exact Deriv.andIntro (Deriv.cutHead (Deriv.andElim1 (Deriv.iden (.head _))) hax)
        (Deriv.andElim2 (Deriv.iden (.head _)))
    rcases hdec l hl l0 hl0 with hll0 | hll0
    · -- `x ∧ c ≡ a ∧ c`, so `x ⊢ a`
      refine Or.inl ⟨?_, hax⟩
      have hxca : Deriv [x.and c] a :=
        Deriv.cutHead (Deriv.cutHead il.1 hll0) hl0a
      refine Deriv.orElim hxb (Deriv.iden (.head _)) ?_
      exact Deriv.cutHead
        (Deriv.andIntro (Deriv.iden (.tail _ (.head _))) (Deriv.cutHead (Deriv.iden (.head _)) hmc))
        hxca
    · -- `l` is strictly above `l0`, so not strictly below `m`: `m ⊢ l`
      have hPl : P l := ⟨hl0l, hll0⟩
      rcases hdec m hm l hl with hml | hml
      · refine Or.inr ⟨hxb, ?_⟩
        refine Deriv.orElim (Deriv.iden (.head _)) (Deriv.toHead hax) ?_
        exact Deriv.toHead
          (Deriv.cutHead (Deriv.cutHead hml il.2) (Deriv.andElim1 (Deriv.iden (.head _))))
      · exact absurd ⟨Deriv.cutHead il.2 hxcm, hml⟩ (hmin l hl hPl)
  · exact Deriv.orElim (Deriv.iden (.head _))
      (Deriv.orIntro1 (Deriv.iden (.head _)))
      (Deriv.orIntro2 (Deriv.cutHead (Deriv.iden (.head _)) hmc))

/-- R3 without the decision hypothesis, by excluded middle (pin with
`Classical.choice`). -/
theorem cover_above_em {c a : PLLFormula} {L : List PLLFormula} (T : DownTable c L)
    (ha : atomFree a = true) (hc : atomFree c = true) (hca : [c] ⊬ a) :
    ∃ b : PLLFormula, Covers a b ∧ Deriv [b] (a.or c) :=
  cover_above T (fun x _ y _ => Classical.em (Deriv [x] y)) ha hc hca

end F0
end PLLND

/-! ## Axiom pins -/

#axioms_within PLLND.F0.true_entails_ctx [propext, Quot.sound]
#axioms_within PLLND.F0.F_eval_true [propext, Quot.sound]
#axioms_within PLLND.F0.F_eval_false [propext, Quot.sound]
#axioms_within PLLND.F0.F_vars_ge [propext, Quot.sound]
#axioms_within PLLND.F0.odd_odd_cf [propext, Quot.sound]
#axioms_within PLLND.F0.even_odd_cf [propext, Quot.sound]
#axioms_within PLLND.F0.t15_le_formula [propext, Quot.sound]
#axioms_within PLLND.F0.ladder_le_formula [propext, Quot.sound]
#axioms_within PLLND.F0.t4_le_formula [propext, Quot.sound]
#axioms_within PLLND.F0.t6_le_formula [propext, Quot.sound]
#axioms_within PLLND.F0.dnf_derive [propext, Quot.sound]
#axioms_within PLLND.F0.lpoly_deriv_iff [propext, Quot.sound]
#axioms_within PLLND.F0.lpoly_deriv_decide [propext, Quot.sound]
#axioms_within PLLND.F0.nderiv_witness [propext, Quot.sound]
#axioms_within PLLND.F0.copy_mono [propext, Quot.sound]
#axioms_within PLLND.F0.copy_strict [propext, Quot.sound]
#axioms_within PLLND.F0.copy_cross [propext, Quot.sound]
#axioms_within PLLND.F0.copy_zero [propext, Quot.sound]
#axioms_within PLLND.F0.copy_one [propext, Quot.sound]
#axioms_within PLLND.F0.incomparable_copies [propext, Quot.sound]
#axioms_within PLLND.F0.exists_minimal [propext, Quot.sound]
#axioms_within PLLND.F0.cover_above [propext, Quot.sound]
#axioms_within PLLND.F0.cover_above_em [propext, Classical.choice, Quot.sound]
