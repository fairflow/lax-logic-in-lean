import wip.f0FreeIPL
import wip.f0Indep
import Meta.Audit

/-!
# Free Heyting algebras on `n` generators inside the filters `[σᵐ⊥, ⊤]` of F0

Follow-up to `wip/f0FreeIPL.lean` (Matthew, 2026-10-27).  There, `[t3, ⊤]` was
shown to contain no copy of the free Heyting algebra on two generators closed
under F0's own `∧`, `∨`, `↠` with bottom `t3` (`not_FreeIPLInAboveT3`), by a
count: a world maximal among those refuting `t3` has one of only three
variable-free theories, while two free generators need all four sign patterns.

This module states the same question for the bases `σᵐ⊥` (`sigN m ⊥`;
`σ⁰⊥ = ⊥`, `σ¹⊥ = t3`, `σ²⊥ = σ(t3) = ◯t3 ∨ (◯t3 ↠ t3)`) and `n` generators,
and makes the counting criterion precise.

## Statements (committed before any proof, METHOD.md §1)

* `relB b x A = A[a := x a, ⊥ := b]`, the relativisation to the base `b`.
* `FreeHAnAbove b n`: generators `x₀, …, x_{n-1} ≥ b` such that for all ◯-free
  `A`, `B` in the variables `p0, …, p(n-1)`,

      [A] ⊢ B  ⟺  [A[pᵢ := xᵢ, ⊥ := b]] ⊢ B[pᵢ := xᵢ, ⊥ := b].

  `FreeHAωAbove b` is the same with all variables (ℵ₀ generators);
  `FreeIPLInAboveT3` of `wip/f0FreeIPL.lean` is `FreeHAωAbove t3`.
* `BMax b M w`: `w` refutes `b` and no proper successor does.
* `TypeBound b K` (k(b) ≤ K): a function `ty` assigning to every world of every
  finite subframe model one of `K` Boolean valuations `Ts`, such that every
  `b`-maximal world forces exactly the variable-free formulas its valuation
  makes true.  `Distinct b K` (k(b) ≥ K): `K` `b`-maximal worlds, in finite
  subframe models, with pairwise different variable-free theories.
* `Conjecture`: `∀ n ∃ m, FreeHAnAbove (σᵐ⊥) n`.
* `Companion`: for every variable-free `b < ⊤`, `k(b)` is finite
  (`TypesFinite b := ∃ K, TypeBound b K`), so no single `[b, ⊤]` holds free IPL
  on ℵ₀ generators.
* `CountingCriterion`: `FreeHAnAbove b n → TypeBound b K → 2ⁿ ≤ K`.
* `TwoGenPatterns b x₀ x₁`: no signed conjunction of `x₀`, `x₁` lies below `b`,

      ∀ ε,  ⊬ (x₀^ε₁ ∧ x₁^ε₂) ↠ b,     x^true = x, x^false = x ↠ b,

  the two-generator sign-pattern condition (necessary for `FreeHAnAbove b 2`
  with these generators).  The candidate pair high up, in `[σ²⊥, ⊤]`:

      x₀ = ◯σ²⊥ = σ²(◯⊥),     x₁ = σ²⊥ ∨ ((◯Y ↠ t3) ↠ t3),   Y = t4 ∨ ¬t4,

  where `◯Y ↠ t3` is the relative negation of `◯Y` in `[t3, ⊤]`.

## Results

**The sign-pattern condition holds for the candidate pair** over `σ²⊥`
(`twoGenPatterns_x0_x1`, four kernel-checked countermodels, the designed cells
`ZL 0`, `ZL 1` below with their bottom in or out of `S`).  So, unlike at `t3`,
the two-generator necessary condition does not refute `FreeHAnAbove (σ²⊥) 2`.

**`k(σ²⊥)` is unbounded** (`base2_unbounded : ∀ K, Distinct (base 2) K`,
`not_typeBound_base2 : ∀ K, ¬ TypeBound (base 2) K`), so **the companion is
REFUTED** (`not_Companion`).  The reason: inside `[t3, g1]`, `g1 = ◯t3 ↠ t3`,
the worlds forcing `g1` and refuting `t3` carry a Rieger–Nishimura ladder over
the generator `x = ◯Y` with bottom `t3`: the model `ZL n` has two tops `e₀`
(`◯⊥`) and `n₀` (`¬◯⊥`), the ladder worlds `w₀, …, wₙ` (`w_j` sees `w_{j'}` for
`j' + 2 ≤ j`, all in `S`, all seeing `e₀`, and `n₀` from `w₁` up), a world `f`
outside `S` seeing both tops (it forces `◯t3`, refutes `t3`), and a bottom
`m ∈ S` seeing everything.  `x` holds exactly at `w₀` and `f` among the
non-tops, so for one-variable ◯-free `A` the relativisation
`A[p := x, ⊥ := t3]` holds at `w_j` iff `A` holds at `j` on the ladder skeleton
of `wip/rnEmbed.lean` (`transfer`), and at `m` iff `A` holds at `n + 2`.  Every
world but `m` forces `σ²⊥` and `m` does not, so `m` is `σ²⊥`-maximal
(`bmax_m`); the rung `rn (2(n+2)+1)` relativised separates the bottoms of
`ZL n` and `ZL n'` (`cell_sep`, by the choice-free `sat_rn_odd_cf` of
`wip/f0Indep.lean`).  The pigeonhole is on an initial segment of `Nat`
(`nat_pigeon`), choice-free.

So the counting criterion cannot refute the conjecture at any `n`; the
conjecture itself is OPEN (faithfulness of a pair such as `(x₀, x₁)` on all
two-variable formulas is a construction, not a count).

Choice hygiene: `omega` reaches `Classical.propDecidable` whenever it must push
a negation through `∧`, `→` or `↔` (a disjunctive goal with a conjunct, an
`iff` hypothesis in scope); every `omega` here has a goal that is `False`, an
equation, an inequality, or a disjunction of those, and the order facts `Le`
are built by their constructors (`le_top0`, `le_top1`, `le_lad`, `le_m`).

Status note: `wip/f0FreeHAn-STATUS.md`.
-/

open PLLFormula

namespace PLLND
namespace F0
namespace FreeHAn

open SemUI RNEmbed Sig FreeIPL
open PLLND.LaxInfinite (atomFree)
open SubframeModel.CF

/-! ## The relativisation to a base and the `n`-generator statement -/

/-- **The relativisation to the base `b`**, `A[a := x a, ⊥ := b]`. -/
def relB (b : PLLFormula) (x : String → PLLFormula) : PLLFormula → PLLFormula
  | .prop a => x a
  | .falsePLL => b
  | .and A B => .and (relB b x A) (relB b x B)
  | .or A B => .or (relB b x A) (relB b x B)
  | .ifThen A B => .ifThen (relB b x A) (relB b x B)
  | .somehow A => .somehow (relB b x A)

/-- The `i`-th propositional variable, `"p"`, `"pp"`, `"ppp"`, … (`pvar 0 = pv`). -/
def pvar (i : Nat) : String := String.ofList (List.replicate (i + 1) 'p')

/-- Every atom of the formula is among `p0, …, p(n-1)`. -/
def varsBelow (n : Nat) : PLLFormula → Bool
  | .prop a => (List.range n).any fun i => decide (a = pvar i)
  | .falsePLL => true
  | .and A B => varsBelow n A && varsBelow n B
  | .or A B => varsBelow n A && varsBelow n B
  | .ifThen A B => varsBelow n A && varsBelow n B
  | .somehow A => varsBelow n A

/-- **`[b, ⊤]` contains the free Heyting algebra on `n` generators** as a
Heyting subalgebra (F0's `∧`, `∨`, `↠`, bottom `b`):

    ∃ x, (∀ a, atomFree (x a)) ∧ (∀ a, [b] ⊢ x a) ∧
      ∀ A B ◯-free in p0 … p(n-1),  [A] ⊢ B  ⟺  [relB b x A] ⊢ relB b x B. -/
def FreeHAnAbove (b : PLLFormula) (n : Nat) : Prop :=
  ∃ x : String → PLLFormula,
    (∀ a, atomFree (x a) = true) ∧ (∀ a, Deriv [b] (x a)) ∧
    ∀ A B : PLLFormula, boxFree A = true → boxFree B = true →
      varsBelow n A = true → varsBelow n B = true →
      (Deriv [A] B ↔ Deriv [relB b x A] (relB b x B))

/-- **`[b, ⊤]` contains the free Heyting algebra on ℵ₀ generators** (every
variable a generator); `FreeIPLInAboveT3 = FreeHAωAbove t3`. -/
def FreeHAωAbove (b : PLLFormula) : Prop :=
  ∃ x : String → PLLFormula,
    (∀ a, atomFree (x a) = true) ∧ (∀ a, Deriv [b] (x a)) ∧
    ∀ A B : PLLFormula, boxFree A = true → boxFree B = true →
      (Deriv [A] B ↔ Deriv [relB b x A] (relB b x B))

/-- The bases `σᵐ⊥`: `base 0 = ⊥`, `base 1 = t3`, `base 2 = σ(t3) = ◯t3 ∨ (◯t3 ↠ t3)`. -/
def base (m : Nat) : PLLFormula := sigN m .falsePLL

theorem base_zero : base 0 = .falsePLL := rfl
theorem base_one : base 1 = t3 := rfl
theorem base_two : base 2 = (chainF 1).or (gap 1) := rfl
theorem base_two' : base 2 = SigOnto.c1F.or SigOnto.g1F := rfl

/-- **The conjecture**: every free Heyting algebra on finitely many generators
occurs in some `[σᵐ⊥, ⊤]`. -/
def Conjecture : Prop := ∀ n, ∃ m, FreeHAnAbove (base m) n

/-! ## Types of `b`-maximal worlds -/

section Types

variable (b : PLLFormula) (M : SubframeModel)

/-- A world refuting `b` with no proper successor refuting `b`
(`FreeIPL.RMax` is `BMax t3`). -/
def BMax (w : M.W) : Prop := ¬ M.force w b ∧ ∀ v, M.le w v → ¬ M.force v b → M.le v w

/-- The world `w` has the type `T`: it forces exactly the variable-free
formulas `T` makes true. -/
def HasType (w : M.W) (T : PLLFormula → Bool) : Prop :=
  ∀ φ : PLLFormula, atomFree φ = true → (M.force w φ ↔ T φ = true)

end Types

/-- **`k(b) ≤ K`**: `K` valuations `Ts` and a type function `ty` on the worlds
of the finite subframe models, such that every `b`-maximal world has the type
`Ts (ty w)`. -/
def TypeBound (b : PLLFormula) (K : Nat) : Prop :=
  ∃ (Ts : Fin K → PLLFormula → Bool) (ty : ∀ (M : SubframeModel) [FinDec M], M.W → Fin K),
    ∀ (M : SubframeModel) [FinDec M] (w : M.W), BMax b M w → HasType M w (Ts (ty M w))

/-- A cell: a finite subframe model with a `b`-maximal world. -/
structure Cell (b : PLLFormula) where
  M : SubframeModel
  fin : FinDec M
  w : M.W
  max : BMax b M w

/-- Two cells have different theories: some variable-free formula holds at one
and fails at the other. -/
def Cell.Separated {b : PLLFormula} (c c' : Cell b) : Prop :=
  ∃ φ : PLLFormula, atomFree φ = true ∧ ¬ (c.M.force c.w φ ↔ c'.M.force c'.w φ)

/-- **`k(b) ≥ K`**: `K` `b`-maximal worlds with pairwise different
variable-free theories. -/
def Distinct (b : PLLFormula) (K : Nat) : Prop :=
  ∃ cs : Fin K → Cell b, ∀ i j, i ≠ j → (cs i).Separated (cs j)

/-- `k(b)` is finite. -/
def TypesFinite (b : PLLFormula) : Prop := ∃ K, TypeBound b K

/-- **The companion**: for every variable-free `b < ⊤` the type count is finite. -/
def Companion : Prop := ∀ b : PLLFormula, atomFree b = true → ¬ Deriv [] b → TypesFinite b

/-- **The counting criterion**: a copy of free IPL on `n` generators in `[b, ⊤]`
needs at least `2ⁿ` types of `b`-maximal world. -/
def CountingCriterion : Prop :=
  ∀ (b : PLLFormula) (n K : Nat), atomFree b = true → FreeHAnAbove b n → TypeBound b K → 2 ^ n ≤ K

/-- The same, in the form the proof gives: the `2ⁿ` sign patterns are realised
by pairwise separated `b`-maximal cells. -/
def PatternsRealised (b : PLLFormula) (n : Nat) : Prop :=
  ∃ cs : (Fin n → Bool) → Cell b, ∀ ε ε', ε ≠ ε' → (cs ε).Separated (cs ε')

/-! ## The two-generator sign-pattern condition, and the candidate pair -/

/-- The relative negation in `[b, ⊤]`, `x ↦ x ↠ b`. -/
def RnegB (b φ : PLLFormula) : PLLFormula := .ifThen φ b

/-- `x` or `x ↠ b`, by a sign. -/
def sgnB (b : PLLFormula) : Bool → PLLFormula → PLLFormula
  | true, x => x
  | false, x => RnegB b x

/-- **The sign-pattern condition for a pair** over the base `b`:

    ∀ ε : Bool × Bool,  ⊬ (x₀^ε₁ ∧ x₁^ε₂) ↠ b.

Necessary for `x₀`, `x₁` to be free generators over `b`
(`FreeIPL.TwoGenFaithful` is the case `b = t3`). -/
def TwoGenPatterns (b x₀ x₁ : PLLFormula) : Prop :=
  ∀ ε : Bool × Bool, ¬ Deriv [] (RnegB b ((sgnB b ε.1 x₀).and (sgnB b ε.2 x₁)))

/-- `Y = t4 ∨ ¬t4`, `t4 = ¬¬◯⊥`: fails exactly at the worlds that see both a
world forcing `◯⊥` and one forcing `¬◯⊥`. -/
def Yf : PLLFormula := t4.or (t4.ifThen .falsePLL)

/-- `x = ◯Y`, the generator of a Rieger–Nishimura ladder inside `[t3, g1]`. -/
def xf : PLLFormula := .somehow Yf

/-- The candidate pair in `[σ²⊥, ⊤]`: `x₀ = ◯σ²⊥ = σ²(◯⊥)`. -/
def x0 : PLLFormula := .somehow (base 2)

/-- `x₁ = σ²⊥ ∨ ((◯Y ↠ t3) ↠ t3)`. -/
def x1 : PLLFormula := (base 2).or ((xf.ifThen t3).ifThen t3)

theorem x0_eq : x0 = sigN 2 e := rfl

/-! ## The designed cells: the four sign patterns of `(x₀, x₁)` over `σ²⊥`

Countermodels (kernel-checked by `SubTab.no`): the models `ZL 0` and `ZL 1`
below, worlds `0 = e₀`, `1 = n₀`, `2 = w₀`, `3 = w₁`, then `f`, then the root
`m`, with `m ∈ S` for the sign `x₀ = false` and `m ∉ S` for `x₀ = true`;
`x₁` holds at `m` iff `m` does not see `w₁` (`ZL 0`).  Cross-checked by the
subframe tableau (`refbench fact`, independent producer: countermodels of 6, 5,
7, 8 worlds). -/

set_option maxRecDepth 100000

/-- Pattern `(true, true)`: `ZL 0`, `m ∉ S`. -/
theorem cell_11 : ¬ Deriv [] (RnegB (base 2) ((sgnB (base 2) true x0).and (sgnB (base 2) true x1))) :=
  SubTab.no.verdict (RnegB (base 2) ((sgnB (base 2) true x0).and (sgnB (base 2) true x1)))
    { n := 5, root := 4, le := [[true, false, false, false, false], [false, true, false, false, false], [true, false, true, false, false], [true, true, false, true, false], [true, true, true, true, true]], S := [false, true, true, false, false], val := [[], [], [], [], []] }

/-- Pattern `(false, true)`: `ZL 0`, `m ∈ S`. -/
theorem cell_01 : ¬ Deriv [] (RnegB (base 2) ((sgnB (base 2) false x0).and (sgnB (base 2) true x1))) :=
  SubTab.no.verdict (RnegB (base 2) ((sgnB (base 2) false x0).and (sgnB (base 2) true x1)))
    { n := 5, root := 4, le := [[true, false, false, false, false], [false, true, false, false, false], [true, false, true, false, false], [true, true, false, true, false], [true, true, true, true, true]], S := [false, true, true, false, true], val := [[], [], [], [], []] }

/-- Pattern `(true, false)`: `ZL 1`, `m ∉ S`. -/
theorem cell_10 : ¬ Deriv [] (RnegB (base 2) ((sgnB (base 2) true x0).and (sgnB (base 2) false x1))) :=
  SubTab.no.verdict (RnegB (base 2) ((sgnB (base 2) true x0).and (sgnB (base 2) false x1)))
    { n := 6, root := 5, le := [[true, false, false, false, false, false], [false, true, false, false, false, false], [true, false, true, false, false, false], [true, true, false, true, false, false], [true, true, false, false, true, false], [true, true, true, true, true, true]], S := [false, true, true, true, false, false], val := [[], [], [], [], [], []] }

/-- Pattern `(false, false)`: `ZL 1`, `m ∈ S`. -/
theorem cell_00 : ¬ Deriv [] (RnegB (base 2) ((sgnB (base 2) false x0).and (sgnB (base 2) false x1))) :=
  SubTab.no.verdict (RnegB (base 2) ((sgnB (base 2) false x0).and (sgnB (base 2) false x1)))
    { n := 6, root := 5, le := [[true, false, false, false, false, false], [false, true, false, false, false, false], [true, false, true, false, false, false], [true, true, false, true, false, false], [true, true, false, false, true, false], [true, true, true, true, true, true]], S := [false, true, true, true, false, true], val := [[], [], [], [], [], []] }

/-- **The sign-pattern condition holds for `(x₀, x₁)` over `σ²⊥`.** -/
theorem twoGenPatterns_x0_x1 : TwoGenPatterns (base 2) x0 x1 := fun ε =>
  match ε with
  | (false, false) => cell_00
  | (false, true) => cell_01
  | (true, false) => cell_10
  | (true, true) => cell_11

/-! ## The model family `ZL n`, and the unbounded type count at `σ²⊥` -/

namespace ZL

/-- The order on the indices of `ZL n`: `0 = e₀` and `1 = n₀` (tops),
`2 + j = w_j` (the ladder, `j ≤ n`; `w_j` sees `w_{j'}` for `j' + 2 ≤ j`, and
the tops, `n₀` only from `w₁` up), `n + 3 = f` (sees the tops), `n + 4 = m`
(sees everything). -/
def Le (n i j : Nat) : Prop :=
  i = j ∨ (j = 0 ∧ 2 ≤ i) ∨ (j = 1 ∧ 3 ≤ i) ∨ (2 ≤ j ∧ j + 2 ≤ i ∧ i ≤ n + 2) ∨ i = n + 4

instance (n i j : Nat) : Decidable (Le n i j) := by unfold Le; exact inferInstance

theorem Le.refl (n i : Nat) : Le n i i := Or.inl rfl

theorem le_top0 {n i : Nat} (hi : 2 ≤ i) : Le n i 0 := Or.inr (Or.inl ⟨rfl, hi⟩)

theorem le_top1 {n i : Nat} (hi : 3 ≤ i) : Le n i 1 := Or.inr (Or.inr (Or.inl ⟨rfl, hi⟩))

theorem le_lad {n i j : Nat} (hj : 2 ≤ j) (h : j + 2 ≤ i) (hi : i ≤ n + 2) : Le n i j :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨hj, h, hi⟩)))

theorem le_m {n : Nat} (k : Nat) : Le n (n + 4) k := Or.inr (Or.inr (Or.inr (Or.inr rfl)))

theorem Le.trans {n i j k : Nat} (h1 : Le n i j) (h2 : Le n j k) : Le n i k := by
  rcases h1 with rfl | ⟨rfl, hi⟩ | ⟨rfl, hi⟩ | ⟨hj, hji, hin⟩ | rfl
  · exact h2
  · have hk : k = 0 := by
      rcases h2 with h2 | ⟨h2, h2'⟩ | ⟨h2, h2'⟩ | ⟨h2, h2', h2''⟩ | h2 <;> omega
    subst hk
    exact le_top0 hi
  · have hk : k = 1 := by
      rcases h2 with h2 | ⟨h2, h2'⟩ | ⟨h2, h2'⟩ | ⟨h2, h2', h2''⟩ | h2 <;> omega
    subst hk
    exact le_top1 hi
  · rcases h2 with rfl | ⟨rfl, _⟩ | ⟨rfl, hj3⟩ | ⟨hk, hkj, _⟩ | rfl
    · exact le_lad hj hji hin
    · exact le_top0 (by omega)
    · exact le_top1 (by omega)
    · exact le_lad hk (by omega) hin
    · exact absurd hji (by omega)
  · exact le_m k

/-- The model `ZL n`: `S` is everything but `e₀` and `f`; no atoms. -/
def M (n : Nat) : SubframeModel where
  W := {i : Nat // i < n + 5}
  le a b := Le n a.1 b.1
  S := {a | a.1 ≠ 0 ∧ a.1 ≠ n + 3}
  V _ := fun _ => False
  refl a := Le.refl n a.1
  trans h1 h2 := Le.trans h1 h2
  hered _ h := False.elim h

instance instFinDec (n : Nat) : FinDec (M n) where
  elems := (List.range (n + 5)).attach.map fun i => ⟨i.1, List.mem_range.mp i.2⟩
  complete a := List.mem_map.mpr ⟨⟨a.1, List.mem_range.mpr a.2⟩, List.mem_attach _ _, rfl⟩
  decLe a b := inferInstanceAs (Decidable (Le n a.1 b.1))
  decS a := inferInstanceAs (Decidable (a.1 ≠ 0 ∧ a.1 ≠ n + 3))
  decV _ _ := isFalse False.elim

theorem lt0 (n : Nat) : 0 < n + 5 := by omega
theorem lt1 (n : Nat) : 1 < n + 5 := by omega
theorem lt2 (n : Nat) : 2 < n + 5 := by omega
theorem lt3 (n : Nat) : n + 3 < n + 5 := by omega
theorem lt4 (n : Nat) : n + 4 < n + 5 := by omega

variable {n : Nat}

/-! ### The tops -/

theorem force_e_zero (h0 : 0 < n + 5) : (M n).force ⟨0, h0⟩ e := by
  show ∀ v, (M n).le ⟨0, h0⟩ v → v ∈ (M n).S → (M n).force v .falsePLL
  intro v hv hS
  have hv' : Le n 0 v.1 := hv
  have hS' : v.1 ≠ 0 ∧ v.1 ≠ n + 3 := hS
  exfalso; unfold Le at hv'; omega

theorem not_force_e_one (h1 : 1 < n + 5) : ¬ (M n).force ⟨1, h1⟩ e := fun h =>
  h ⟨1, h1⟩ (Le.refl n 1) (show (1 : Nat) ≠ 0 ∧ 1 ≠ n + 3 from ⟨by omega, by omega⟩)

theorem force_ne_one (h1 : 1 < n + 5) : (M n).force ⟨1, h1⟩ ne := by
  show ∀ v, (M n).le ⟨1, h1⟩ v → (M n).force v e → (M n).force v .falsePLL
  intro v hv he
  have hv' : Le n 1 v.1 := hv
  have : v = (⟨1, h1⟩ : (M n).W) := Subtype.ext (show v.1 = 1 by unfold Le at hv'; omega)
  subst this
  exact not_force_e_one h1 he

theorem force_t3_zero (h0 : 0 < n + 5) : (M n).force ⟨0, h0⟩ t3 := Or.inl (force_e_zero h0)

theorem force_t3_one (h1 : 1 < n + 5) : (M n).force ⟨1, h1⟩ t3 := Or.inr (force_ne_one h1)

/-! ### Below the tops `t3` fails -/

theorem not_force_e {i : Nat} (h : i < n + 5) (hi : 2 ≤ i) : ¬ (M n).force ⟨i, h⟩ e := by
  intro he
  rcases Decidable.em (i = n + 3) with hf | hf
  · exact he ⟨1, lt1 n⟩ (show Le n i 1 from le_top1 (by omega))
      (show (1 : Nat) ≠ 0 ∧ 1 ≠ n + 3 from ⟨by omega, by omega⟩)
  · exact he ⟨i, h⟩ (Le.refl n i) (show i ≠ 0 ∧ i ≠ n + 3 from ⟨by omega, hf⟩)

theorem not_force_ne {i : Nat} (h : i < n + 5) (hi : 2 ≤ i) : ¬ (M n).force ⟨i, h⟩ ne := fun hne =>
  hne ⟨0, lt0 n⟩ (le_top0 hi) (force_e_zero _)

theorem not_force_t3 {i : Nat} (h : i < n + 5) (hi : 2 ≤ i) : ¬ (M n).force ⟨i, h⟩ t3 := fun ht => by
  have ht' : (M n).force ⟨i, h⟩ e ∨ (M n).force ⟨i, h⟩ ne := ht
  exact ht'.elim (not_force_e h hi) (not_force_ne h hi)

/-! ### `t4`, `Y = t4 ∨ ¬t4` and `x = ◯Y` -/

theorem force_t4_zero (h0 : 0 < n + 5) : (M n).force ⟨0, h0⟩ t4 := by
  show ∀ v, (M n).le ⟨0, h0⟩ v → (M n).force v t3 → (M n).force v e
  intro v hv _
  have hv' : Le n 0 v.1 := hv
  have : v = (⟨0, h0⟩ : (M n).W) := Subtype.ext (show v.1 = 0 by unfold Le at hv'; omega)
  subst this
  exact force_e_zero h0

theorem force_t4_two (h2 : 2 < n + 5) : (M n).force ⟨2, h2⟩ t4 := by
  show ∀ v, (M n).le ⟨2, h2⟩ v → (M n).force v t3 → (M n).force v e
  intro v hv ht
  have hv' : Le n 2 v.1 := hv
  rcases (by unfold Le at hv'; omega : v.1 = 0 ∨ v.1 = 2) with h0 | h0
  · have : v = (⟨0, lt0 n⟩ : (M n).W) := Subtype.ext h0
    subst this
    exact force_e_zero _
  · have : v = (⟨2, h2⟩ : (M n).W) := Subtype.ext h0
    subst this
    exact absurd ht (not_force_t3 h2 (by omega))

theorem le_one_of {i : Nat} (hi : i = 1 ∨ 3 ≤ i) : Le n i 1 := by
  rcases hi with rfl | hi
  · exact Le.refl n 1
  · exact le_top1 hi

theorem not_force_t4 {i : Nat} (h : i < n + 5) (hi : i = 1 ∨ 3 ≤ i) :
    ¬ (M n).force ⟨i, h⟩ t4 := fun ht =>
  not_force_e_one (lt1 n) (ht ⟨1, lt1 n⟩ (le_one_of hi) (force_t3_one _))

theorem not_force_nt4 {i : Nat} (h : i < n + 5) (hi : 2 ≤ i) :
    ¬ (M n).force ⟨i, h⟩ (t4.ifThen .falsePLL) := fun hn =>
  hn ⟨0, lt0 n⟩ (le_top0 hi) (force_t4_zero _)

theorem force_Y_iff {i : Nat} (h : i < n + 5) : (M n).force ⟨i, h⟩ Yf ↔ i ≤ 2 := by
  constructor
  · intro hY
    have hY' : (M n).force ⟨i, h⟩ t4 ∨ (M n).force ⟨i, h⟩ (t4.ifThen .falsePLL) := hY
    rcases Nat.lt_or_ge 2 i with hgt | hle
    · exfalso
      rcases hY' with ht | hn
      · exact not_force_t4 h (Or.inr hgt) ht
      · exact not_force_nt4 h (by omega) hn
    · exact hle
  · intro hi
    show (M n).force ⟨i, h⟩ t4 ∨ (M n).force ⟨i, h⟩ (t4.ifThen .falsePLL)
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · exact Or.inl (force_t4_zero h)
    · refine Or.inr (fun v hv ht => ?_)
      have hv' : Le n 1 v.1 := hv
      have : v = (⟨1, h⟩ : (M n).W) := Subtype.ext (show v.1 = 1 by unfold Le at hv'; omega)
      subst this
      exact not_force_t4 h (Or.inl rfl) ht
    · exact Or.inl (force_t4_two h)

theorem force_x_iff {i : Nat} (h : i < n + 5) (hi : 2 ≤ i) :
    (M n).force ⟨i, h⟩ xf ↔ (i = 2 ∨ i = n + 3) := by
  constructor
  · intro hx
    rcases Decidable.em (i = n + 3) with h3 | h3
    · exact Or.inr h3
    rcases Nat.lt_or_ge i 3 with hlt | hge
    · exact Or.inl (by omega)
    · exfalso
      have hY := hx ⟨i, h⟩ (Le.refl n i) (show i ≠ 0 ∧ i ≠ n + 3 from ⟨by omega, h3⟩)
      have := (force_Y_iff h).mp hY
      omega
  · intro hi2 v hv hS
    have hv' : Le n i v.1 := hv
    have hS' : v.1 ≠ 0 ∧ v.1 ≠ n + 3 := hS
    have hv5 := v.2
    have hv2 : v.1 ≤ 2 := by unfold Le at hv'; omega
    exact (force_Y_iff v.2).mpr hv2

/-! ### `σ²⊥ = ◯t3 ∨ (◯t3 ↠ t3)` holds everywhere but at `m` -/

theorem force_c1_f (hf : n + 3 < n + 5) : (M n).force ⟨n + 3, hf⟩ SigOnto.c1F := by
  show ∀ v, (M n).le ⟨n + 3, hf⟩ v → v ∈ (M n).S → (M n).force v t3
  intro v hv hS
  have hv' : Le n (n + 3) v.1 := hv
  have hS' : v.1 ≠ 0 ∧ v.1 ≠ n + 3 := hS
  have : v = (⟨1, lt1 n⟩ : (M n).W) := Subtype.ext (show v.1 = 1 by unfold Le at hv'; omega)
  subst this
  exact force_t3_one _

theorem not_force_c1 {i : Nat} (h : i < n + 5) (hi : 2 ≤ i) (hne : i ≠ n + 3) :
    ¬ (M n).force ⟨i, h⟩ SigOnto.c1F := fun hc =>
  not_force_t3 h hi (hc ⟨i, h⟩ (Le.refl n i) (show i ≠ 0 ∧ i ≠ n + 3 from ⟨by omega, hne⟩))

theorem force_g1_top {i : Nat} (h : i < n + 5) (hi : i ≤ 1) : (M n).force ⟨i, h⟩ SigOnto.g1F := by
  show ∀ v, (M n).le ⟨i, h⟩ v → (M n).force v SigOnto.c1F → (M n).force v t3
  intro v hv _
  have hv' : Le n i v.1 := hv
  have : v = (⟨i, h⟩ : (M n).W) := Subtype.ext (show v.1 = i by unfold Le at hv'; omega)
  subst this
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
  · exact force_t3_zero h
  · exact force_t3_one h

theorem force_g1_ladder {i : Nat} (h : i < n + 5) (hi : 2 ≤ i) (hi' : i ≤ n + 2) :
    (M n).force ⟨i, h⟩ SigOnto.g1F := by
  show ∀ v, (M n).le ⟨i, h⟩ v → (M n).force v SigOnto.c1F → (M n).force v t3
  intro v hv hc
  have hv' : Le n i v.1 := hv
  rcases Nat.lt_or_ge v.1 2 with hv1 | hv2
  · rcases (by omega : v.1 = 0 ∨ v.1 = 1) with h0 | h0
    · have : v = (⟨0, lt0 n⟩ : (M n).W) := Subtype.ext h0
      subst this
      exact force_t3_zero _
    · have : v = (⟨1, lt1 n⟩ : (M n).W) := Subtype.ext h0
      subst this
      exact force_t3_one _
  · have hv3 : v.1 ≤ n + 2 := by unfold Le at hv'; omega
    exact absurd hc (not_force_c1 v.2 hv2 (by omega))

theorem force_b2 {i : Nat} (h : i < n + 5) (hi : i ≠ n + 4) : (M n).force ⟨i, h⟩ (base 2) := by
  show (M n).force ⟨i, h⟩ SigOnto.c1F ∨ (M n).force ⟨i, h⟩ SigOnto.g1F
  rcases Nat.lt_or_ge i 2 with h1 | h2
  · exact Or.inr (force_g1_top h (by omega))
  rcases Nat.lt_or_ge i (n + 3) with h3 | h3
  · exact Or.inr (force_g1_ladder h h2 (by omega))
  · have h4 : i = n + 3 := by omega
    subst h4
    exact Or.inl (force_c1_f h)

theorem not_force_b2_m (hm : n + 4 < n + 5) : ¬ (M n).force ⟨n + 4, hm⟩ (base 2) := by
  show ¬ ((M n).force ⟨n + 4, hm⟩ SigOnto.c1F ∨ (M n).force ⟨n + 4, hm⟩ SigOnto.g1F)
  rintro (hc | hg)
  · exact not_force_c1 hm (by omega) (by omega) hc
  · exact not_force_t3 (lt3 n) (by omega)
      (hg ⟨n + 3, lt3 n⟩ (le_m _) (force_c1_f _))

/-- **`m` is `σ²⊥`-maximal in `ZL n`.** -/
theorem bmax_m (hm : n + 4 < n + 5) : BMax (base 2) (M n) ⟨n + 4, hm⟩ := by
  refine ⟨not_force_b2_m hm, fun v _ hv => ?_⟩
  rcases Nat.lt_or_ge v.1 (n + 4) with hlt | hge
  · exact absurd (force_b2 v.2 (by omega)) hv
  · have : v = (⟨n + 4, hm⟩ : (M n).W) := Subtype.ext (show v.1 = n + 4 by have := v.2; omega)
    subst this
    exact Le.refl n _

/-! ### The transfer to the ladder skeleton -/

/-- The relativisation `p ↦ x = ◯Y`, `⊥ ↦ t3` of a one-variable formula. -/
def relX : PLLFormula → PLLFormula
  | .prop _ => xf
  | .falsePLL => t3
  | .and A B => .and (relX A) (relX B)
  | .or A B => .or (relX A) (relX B)
  | .ifThen A B => .ifThen (relX A) (relX B)
  | .somehow A => .somehow (relX A)

theorem relX_vf : ∀ A : PLLFormula, atomFree (relX A) = true
  | .prop _ => rfl
  | .falsePLL => rfl
  | .and A B => by
      show (atomFree (relX A) && atomFree (relX B)) = true
      rw [relX_vf A, relX_vf B]; rfl
  | .or A B => by
      show (atomFree (relX A) && atomFree (relX B)) = true
      rw [relX_vf A, relX_vf B]; rfl
  | .ifThen A B => by
      show (atomFree (relX A) && atomFree (relX B)) = true
      rw [relX_vf A, relX_vf B]; rfl
  | .somehow A => relX_vf A

/-- The skeleton index of a non-top world: `w_j ↦ j`, `f ↦ 0`, `m ↦ n + 2`. -/
def skel (n i : Nat) : Nat := if i = n + 3 then 0 else if i = n + 4 then n + 2 else i - 2

theorem skel_f : skel n (n + 3) = 0 := by
  unfold skel; rw [if_pos rfl]

theorem skel_m : skel n (n + 4) = n + 2 := by
  unfold skel; rw [if_neg (by omega), if_pos rfl]

theorem skel_lad {i : Nat} (h3 : i ≠ n + 3) (h4 : i ≠ n + 4) : skel n i = i - 2 := by
  unfold skel; rw [if_neg h3, if_neg h4]

theorem skel_eq_zero {i : Nat} (hi : 2 ≤ i) : skel n i = 0 ↔ (i = 2 ∨ i = n + 3) := by
  unfold skel
  exact ⟨fun h => by split_ifs at h <;> omega, fun h => by split_ifs <;> omega⟩

theorem ladder_of_le {i v : Nat} (hi : 2 ≤ i) (hv : 2 ≤ v) (hv' : v < n + 5) (h : Le n i v) :
    ladder.le (skel n i) (skel n v) := by
  show skel n v = skel n i ∨ skel n v + 2 ≤ skel n i
  unfold Le at h; unfold skel; split_ifs <;> omega

theorem le_of_ladder {i : Nat} (hi : 2 ≤ i) (hi' : i < n + 5) {j : Nat}
    (h : ladder.le (skel n i) j) :
    ∃ v, ∃ hv : v < n + 5, 2 ≤ v ∧ Le n i v ∧ skel n v = j := by
  have h' : j = skel n i ∨ j + 2 ≤ skel n i := h
  rcases Decidable.em (i = n + 3) with h3 | h3
  · subst h3
    rw [skel_f] at h'
    have hj : j = 0 := by rcases h' with h' | h' <;> omega
    exact ⟨n + 3, hi', hi, Le.refl n _, by rw [skel_f, hj]⟩
  rcases Decidable.em (i = n + 4) with h4 | h4
  · subst h4
    rw [skel_m] at h'
    rcases h' with hj | hj
    · exact ⟨n + 4, hi', hi, Le.refl n _, by rw [skel_m, hj]⟩
    · refine ⟨j + 2, by omega, by omega, le_m _, ?_⟩
      rw [skel_lad (by omega) (by omega)]
      omega
  · rw [skel_lad h3 h4] at h'
    rcases h' with hj | hj
    · exact ⟨i, hi', hi, Le.refl n i, by rw [skel_lad h3 h4, hj]⟩
    · refine ⟨j + 2, by omega, by omega, le_lad (by omega) (by omega) (by omega), ?_⟩
      rw [skel_lad (by omega) (by omega)]
      omega

/-- At the tops every relativised one-variable formula holds. -/
theorem top_relX : ∀ (A : PLLFormula), boxFree A = true → ∀ (i : Nat) (h : i < n + 5), i ≤ 1 →
    (M n).force ⟨i, h⟩ (relX A)
  | .prop _, _, i, h, _ => by
      show ∀ v, (M n).le ⟨i, h⟩ v → v ∈ (M n).S → (M n).force v Yf
      intro v hv _
      have hv' : Le n i v.1 := hv
      exact (force_Y_iff v.2).mpr (by unfold Le at hv'; omega)
  | .falsePLL, _, i, h, hi => by
      show (M n).force ⟨i, h⟩ t3
      rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
      · exact force_t3_zero h
      · exact force_t3_one h
  | .and A B, hb, i, h, hi => by
      have hb' := Bool.and_eq_true_iff.mp (hb : (boxFree A && boxFree B) = true)
      exact ⟨top_relX A hb'.1 i h hi, top_relX B hb'.2 i h hi⟩
  | .or A B, hb, i, h, hi => by
      have hb' := Bool.and_eq_true_iff.mp (hb : (boxFree A && boxFree B) = true)
      exact Or.inl (top_relX A hb'.1 i h hi)
  | .ifThen A B, hb, i, h, hi => by
      have hb' := Bool.and_eq_true_iff.mp (hb : (boxFree A && boxFree B) = true)
      show ∀ v, (M n).le ⟨i, h⟩ v → (M n).force v (relX A) → (M n).force v (relX B)
      intro v hv _
      have hv' : Le n i v.1 := hv
      have : v = (⟨i, h⟩ : (M n).W) := Subtype.ext (show v.1 = i by unfold Le at hv'; omega)
      subst this
      exact top_relX B hb'.2 i h hi
  | .somehow _, hb, _, _, _ => nomatch hb

/-- **The transfer lemma**: below the tops, the relativisation of a one-variable
◯-free formula holds at the world `i` iff the formula holds at `skel n i` on the
Rieger–Nishimura ladder skeleton. -/
theorem transfer : ∀ (A : PLLFormula), boxFree A = true → FreeIPL.onlyP A = true →
    ∀ (i : Nat) (h : i < n + 5), 2 ≤ i →
    ((M n).force ⟨i, h⟩ (relX A) ↔ ladder.sat A (skel n i))
  | .prop a, _, hp, i, h, hi => by
      have ha : a = pv := of_decide_eq_true hp
      subst ha
      show (M n).force ⟨i, h⟩ xf ↔ (pv = pv ∧ skel n i ∈ ladder.U)
      rw [force_x_iff h hi]
      constructor
      · intro h2
        exact ⟨rfl, (skel_eq_zero hi).mpr h2⟩
      · intro h0
        exact (skel_eq_zero hi).mp h0.2
  | .falsePLL, _, _, i, h, hi =>
      ⟨fun ht => absurd ht (not_force_t3 h hi), False.elim⟩
  | .and A B, hb, hp, i, h, hi => by
      have hb' := Bool.and_eq_true_iff.mp (hb : (boxFree A && boxFree B) = true)
      have hp' := Bool.and_eq_true_iff.mp (hp : (FreeIPL.onlyP A && FreeIPL.onlyP B) = true)
      exact and_congr (transfer A hb'.1 hp'.1 i h hi) (transfer B hb'.2 hp'.2 i h hi)
  | .or A B, hb, hp, i, h, hi => by
      have hb' := Bool.and_eq_true_iff.mp (hb : (boxFree A && boxFree B) = true)
      have hp' := Bool.and_eq_true_iff.mp (hp : (FreeIPL.onlyP A && FreeIPL.onlyP B) = true)
      exact or_congr (transfer A hb'.1 hp'.1 i h hi) (transfer B hb'.2 hp'.2 i h hi)
  | .ifThen A B, hb, hp, i, h, hi => by
      have hb' := Bool.and_eq_true_iff.mp (hb : (boxFree A && boxFree B) = true)
      have hp' := Bool.and_eq_true_iff.mp (hp : (FreeIPL.onlyP A && FreeIPL.onlyP B) = true)
      show (∀ v, (M n).le ⟨i, h⟩ v → (M n).force v (relX A) → (M n).force v (relX B)) ↔
        (∀ j, ladder.le (skel n i) j → ladder.sat A j → ladder.sat B j)
      constructor
      · intro hf j hj hA
        obtain ⟨v, hv, hv2, hle, hsk⟩ := le_of_ladder hi h hj
        have hA' : ladder.sat A (skel n v) := by rw [hsk]; exact hA
        have hB := (transfer B hb'.2 hp'.2 v hv hv2).mp
          (hf ⟨v, hv⟩ hle ((transfer A hb'.1 hp'.1 v hv hv2).mpr hA'))
        rw [hsk] at hB
        exact hB
      · intro hf v hv hA
        rcases Nat.lt_or_ge v.1 2 with hv1 | hv2
        · exact top_relX B hb'.2 v.1 v.2 (by omega)
        · have hl := ladder_of_le hi hv2 v.2 hv
          exact (transfer B hb'.2 hp'.2 v.1 v.2 hv2).mpr
            (hf _ hl ((transfer A hb'.1 hp'.1 v.1 v.2 hv2).mp hA))
  | .somehow _, hb, _, _, _, _ => nomatch hb

/-! ### The cells and their separation -/

/-- The cell of `ZL n`: its bottom world `m = n + 4`. -/
def cell (n : Nat) : Cell (base 2) :=
  ⟨M n, instFinDec n, ⟨n + 4, lt4 n⟩, bmax_m (lt4 n)⟩

theorem onlyP_rnP : ∀ k, FreeIPL.onlyP (rnP k).1 = true ∧ FreeIPL.onlyP (rnP k).2 = true := by
  intro k
  induction k with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
      obtain ⟨h1, h2⟩ := ih
      constructor
      · show (FreeIPL.onlyP (rnP k).1 && FreeIPL.onlyP (rnP k).2) = true
        rw [h1, h2]; rfl
      · show ((FreeIPL.onlyP (rnP k).1 && FreeIPL.onlyP (rnP k).2) && FreeIPL.onlyP (rnP k).1) = true
        rw [h1, h2]; rfl

theorem onlyP_rn_odd (k : Nat) : FreeIPL.onlyP (rn (2 * k + 1)) = true := by
  rw [rn_odd_eq]; exact (onlyP_rnP k).1

/-- The bottom of `ZL n` forces the relativised odd rung `rn (2k+1)` iff `n + 2 ≤ k`. -/
theorem cell_force (n k : Nat) :
    (M n).force ⟨n + 4, lt4 n⟩ (relX (rn (2 * k + 1))) ↔ n + 2 ≤ k := by
  have := transfer (rn (2 * k + 1)) (rn_boxFree _) (onlyP_rn_odd k) (n + 4) (lt4 n) (by omega)
  rw [skel_m, sat_rn_odd_cf] at this
  exact this

theorem sep_arith {n n' : Nat} (h : n < n') (h2 : n' + 2 ≤ n + 2) : False := by omega

theorem cell_sep {n n' : Nat} (h : n < n') : (cell n).Separated (cell n') :=
  ⟨relX (rn (2 * (n + 2) + 1)), relX_vf _, fun hiff =>
    sep_arith h ((cell_force n' (n + 2)).mp (hiff.mp ((cell_force n (n + 2)).mpr (Nat.le_refl _))))⟩

theorem cell_sep' {n n' : Nat} (h : n ≠ n') : (cell n).Separated (cell n') := by
  rcases Nat.lt_or_gt_of_ne h with h | h
  · exact cell_sep h
  · obtain ⟨φ, hφ, hne⟩ := cell_sep h
    exact ⟨φ, hφ, fun hiff => hne hiff.symm⟩

end ZL

/-- **`k(σ²⊥)` is unbounded**: for every `K`, `K` `σ²⊥`-maximal worlds with
pairwise different variable-free theories (the bottoms of `ZL 0, …, ZL (K-1)`). -/
theorem base2_unbounded (K : Nat) : Distinct (base 2) K :=
  ⟨fun i => ZL.cell i.1, fun i j hij => ZL.cell_sep' (fun h => hij (Fin.ext h))⟩

/-- Pigeonhole on an initial segment of `Nat`, without choice: `K + 1` values
below `K` repeat. -/
theorem nat_pigeon : ∀ (K : Nat) (g : Nat → Nat), (∀ i, i ≤ K → g i < K) →
    ∃ i j, i ≤ K ∧ j ≤ K ∧ i ≠ j ∧ g i = g j := by
  intro K
  induction K with
  | zero =>
      intro g hg
      exact absurd (hg 0 (Nat.le_refl 0)) (Nat.not_lt_zero _)
  | succ K ih =>
      intro g hg
      rcases Decidable.em (∃ m, m < K + 1 ∧ g m = g (K + 1)) with hex | hex
      · obtain ⟨m, hm, hgm⟩ := hex
        exact ⟨m, K + 1, by omega, Nat.le_refl _, by omega, hgm⟩
      · have hno : ∀ m, m < K + 1 → g m ≠ g (K + 1) := fun m hm h => hex ⟨m, hm, h⟩
        let g' : Nat → Nat := fun i => if g i = K then g (K + 1) else g i
        have hg' : ∀ i, i ≤ K → g' i < K := by
          intro i hi
          have h1 := hg i (by omega)
          have h2 := hg (K + 1) (Nat.le_refl _)
          have h3 := hno i (by omega)
          show (if g i = K then g (K + 1) else g i) < K
          split_ifs with hK
          · omega
          · omega
        obtain ⟨i, j, hi, hj, hij, hgij⟩ := ih g' hg'
        refine ⟨i, j, by omega, by omega, hij, ?_⟩
        have e1 : g' i = (if g i = K then g (K + 1) else g i) := rfl
        have e2 : g' j = (if g j = K then g (K + 1) else g j) := rfl
        rw [e1, e2] at hgij
        have h3i := hno i (by omega)
        have h3j := hno j (by omega)
        split_ifs at hgij <;> omega

/-- **No finite bound on the types at `σ²⊥`.** -/
theorem not_typeBound_base2 (K : Nat) : ¬ TypeBound (base 2) K := by
  rintro ⟨Ts, ty, hty⟩
  let g : Nat → Nat := fun i => (ty (ZL.M i) (ZL.cell i).w).1
  have hg : ∀ i, i ≤ K → g i < K := fun i _ => (ty (ZL.M i) (ZL.cell i).w).2
  obtain ⟨i, j, _, _, hij, hgij⟩ := nat_pigeon K g hg
  obtain ⟨φ, hφ, hne⟩ := ZL.cell_sep' hij
  apply hne
  have hi := hty (ZL.M i) (ZL.cell i).w (ZL.cell i).max φ hφ
  have hj := hty (ZL.M j) (ZL.cell j).w (ZL.cell j).max φ hφ
  have heq : ty (ZL.M i) (ZL.cell i).w = ty (ZL.M j) (ZL.cell j).w :=
    Fin.ext (show (ty (ZL.M i) (ZL.cell i).w).1 = (ty (ZL.M j) (ZL.cell j).w).1 from hgij)
  show (ZL.M i).force (ZL.cell i).w φ ↔ (ZL.M j).force (ZL.cell j).w φ
  rw [hi, hj, heq]

theorem base2_vf : atomFree (base 2) = true := rfl

theorem base2_not_deriv : ¬ Deriv [] (base 2) := Sig.cellS_t3

/-- **The companion is REFUTED**: `σ²⊥` is variable-free, below `⊤`, and has
no finite type count. -/
theorem not_Companion : ¬ Companion := fun h =>
  let ⟨K, hK⟩ := h (base 2) base2_vf base2_not_deriv
  not_typeBound_base2 K hK

end FreeHAn
end F0
end PLLND

/-! ## Axiom pins -/

#axioms_within PLLND.F0.FreeHAn.cell_11 [propext, Quot.sound]
#axioms_within PLLND.F0.FreeHAn.cell_01 [propext, Quot.sound]
#axioms_within PLLND.F0.FreeHAn.cell_10 [propext, Quot.sound]
#axioms_within PLLND.F0.FreeHAn.cell_00 [propext, Quot.sound]
#axioms_within PLLND.F0.FreeHAn.twoGenPatterns_x0_x1 [propext, Quot.sound]
#axioms_within PLLND.F0.FreeHAn.ZL.bmax_m [propext, Quot.sound]
#axioms_within PLLND.F0.FreeHAn.ZL.transfer [propext, Quot.sound]
#axioms_within PLLND.F0.FreeHAn.ZL.cell_sep [propext, Quot.sound]
#axioms_within PLLND.F0.FreeHAn.base2_unbounded [propext, Quot.sound]
#axioms_within PLLND.F0.FreeHAn.nat_pigeon [propext, Quot.sound]
#axioms_within PLLND.F0.FreeHAn.not_typeBound_base2 [propext, Quot.sound]
#axioms_within PLLND.F0.FreeHAn.not_Companion [propext, Quot.sound]
