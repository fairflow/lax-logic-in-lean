import wip.f0MovingTop
import Meta.Audit

/-!
# The colimit of the σ-chain

Spike study S2 (Matthew, 2026-11-02).  `σ = sig = subBot t3`
(`wip/f0SelfSim.lean`, `t3 = ◯⊥ ∨ ¬◯⊥`) preserves `∧`, `∨`, `↠`, `◯` and `⊤`
on closed formulas and sends `⊥` to `t3`.  So `σ` is an injective
homomorphism (`sigN_faithful`) of the `⊥`-free reduct of F0, and this file
computes the colimit of

    F0 →σ F0 →σ F0 →σ ⋯

in that signature.

## The structure

A **nuclear implicative lattice** is a lattice with top `⊤` and a relative
pseudocomplement `↠` (an *implicative lattice* in Curry's terminology,
Rasiowa's *relatively pseudo-complemented lattice*, Birkhoff's
*Brouwerian lattice*), together with a **nucleus** `j`: an inflationary,
idempotent, meet-preserving map.  The axioms proved here are listed in
`NucImpLatPre` (for a preorder) and `NucImpLat` (for a partial order):

    x ≤ x;   x ≤ y → y ≤ z → x ≤ z;   (x ≤ y → y ≤ x → x = y)
    x ≤ ⊤
    x ⊓ y ≤ x;   x ⊓ y ≤ y;   z ≤ x → z ≤ y → z ≤ x ⊓ y
    x ≤ x ⊔ y;   y ≤ x ⊔ y;   x ≤ z → y ≤ z → x ⊔ y ≤ z
    z ⊓ x ≤ y  ↔  z ≤ x ↠ y
    x ≤ j x;   j (j x) ≤ j x;   x ≤ y → j x ≤ j y;   j x ⊓ j y ≤ j (x ⊓ y)

F0 itself (closed formulas, `x ≤ y` iff `[x] ⊢ y`) is one, with `j = ◯`.

## The colimit

A representative is a pair `(n, φ)`: a stage `n` and a closed formula `φ`
(`Pre`).  The order and the operations are computed at a common stage:

    (n, φ) ≤ (m, ψ)   iff   σᵐ φ ⊢ σⁿ ψ                          (leP)
    (n, φ) ~ (m, ψ)   iff   σᵐ φ ⊣⊢ σⁿ ψ                          (rP)
    (n, φ) ⊓ (m, ψ) = (n + m, σᵐ φ ∧ σⁿ ψ),   ⊔, ↠ likewise
    j (n, φ) = (n, ◯φ),   ⊤ = (0, ⊤)

Since `σ` is faithful, `σᵐ φ ⊢ σⁿ ψ` iff `σᵏ φ ⊢ σʲ ψ` whenever
`n + k = m + j`: the stage `n + m` is one common stage, and every larger
one gives the same answer.  `SigCol` is `Quot rP`.  The stage maps are
`ιₙ φ = (n, φ)` (`iota`), the shift is `S (n, φ) = (n, σφ)` (`shiftP`), and
the stage shift `(n, φ) ↦ (n + 1, φ)` (`unshiftP`) is its inverse.

## Statements (stage 1)

Every statement is a `Prop` definition in `Stmt`, committed before its
proof.  They are stated on representatives, with `leP` for the order and
`rP` for equality in `SigCol`; the quotient-level forms are corollaries.

* (C1) `Stmt.C1`: `NucImpLatPre leP opsP`.
* (C2) `Stmt.StageCompat`, `Stmt.StageEmb`, `Stmt.StageHom`,
  `Stmt.Universal`.  The universal property is stated for every type `A`
  and every cocone `fₙ : CF → A` (`⊣⊢`-invariant, `fₙ₊₁ ∘ σ = fₙ`): a
  unique `u : SigCol → A` with `u ∘ ιₙ = fₙ`; `u` preserves the five
  operations whenever every `fₙ` does (any `Ops A`, no axioms needed); and
  `u` is monotone for any `Prop`-valued relation on `A` for which every
  `fₙ` is.
* (C3) `Stmt.ShiftExtends`, `Stmt.ShiftOrderIso`, `Stmt.UnshiftOrderIso`,
  `Stmt.ShiftInverse`, `Stmt.ShiftHom`, `Stmt.UnshiftStage`.
* (C4) `Stmt.BotStrict`, `Stmt.NoLowerBound`, `Stmt.Coinitial`,
  `Stmt.NoLeast`.
* (C5) `Stmt.TopIff`, `Stmt.FixedTop`.
* (C6, conjecture) `Stmt.GradePow`, `Stmt.GradeShift`, `Stmt.GradeNotTop`,
  `Stmt.GradeInj`, `Stmt.GradeSurj`, and the decision statement
  `Stmt.SigImageDec`.  With `grP k y = (0, σᵏ y)` for `k ≥ 0` and
  `(−k, y)` for `k < 0`, `grP k y ~ Sᵏ (ι₀ y)`.
* (C7, question) `Stmt.NotUpset`, `Stmt.NotDownset`, `Stmt.FilterUnion`.

Designed cells (stage 2): `Stmt.CellBot`, `Stmt.CellShiftTop`,
`Stmt.CellT5`.

Target pins `[propext, Quot.sound]`.  `wip/f0InsideOut.lean` is imported
(through `wip/f0MovingTop.lean`) only for choice-free declarations;
`orbits_vs_L0`, which uses excluded middle, is not used.

## Results (stage 3; all PROVED, `[propext, Quot.sound]`, pins at the end)

**(C1)** `c1 : NucImpLatPre leP opsP`; on the quotient
`sigCol_nucImpLat : NucImpLat leQ opsQ`, and `nucQ_meet`:
`j (X ⊓ Y) = j X ⊓ j Y`.  The one lemma behind every law is the
common-stage lemma (`leP_iff_at`): for `n + k = m + j`,

    (n, φ) ≤ (m, ψ)   ⟺   σᵏ φ ⊢ σʲ ψ.

**(C2)** `ιₙ₊₁ ∘ σ = ιₙ` (`iotaQ_compat`); `ιₙ φ ≤ ιₙ ψ ⟺ φ ⊢ ψ`
(`iotaQ_le_iff`), so `ιₙ φ = ιₙ ψ ⟺ φ ⊣⊢ ψ` (`iotaQ_eq_iff`); `ιₙ` is a
homomorphism (`stageHom`); the universal property (`universal`): for every
type `A` and cocone `(fₙ)`, the mediating map `liftU` is the unique `u` with
`u ∘ ιₙ = fₙ`, it preserves `⊤ ∧ ∨ ↠ ◯` for any `Ops A` when every `fₙ`
does, and it is monotone for any `Prop`-valued relation when every `fₙ` is.

**(C3)** `S ∘ ιₙ = ιₙ ∘ σ` (`shiftQ_iotaQ`, by `rfl`); `S⁻¹ ∘ ιₙ = ιₙ₊₁`
(`unshiftQ_iotaQ`); `S S⁻¹ = id = S⁻¹ S` (`shiftQ_unshiftQ`,
`unshiftQ_shiftQ`); `S X ≤ S Y ⟺ X ≤ Y` (`shiftQ_le_iff`); `S` preserves
the five operations (`shiftQ_hom`).  So `S` is an automorphism.

**(C4)** `ιₙ₊₁ ⊥ < ιₙ ⊥` (`iotaQ_bot_strict`); no element lies below every
`ιₙ ⊥` (`no_lower_bound`); no least element (`no_least`).  The finite-model
argument was not needed: `(m, χ) ≤ ιₘ₊₁ ⊥` reduces by faithfulness to
`σχ ⊢ ⊥`, refuted by `t3 ⊢ σχ` (`noLowerBound`).  The stage bottoms are
coinitial: `ιₘ ⊥ ≤ (m, χ)` (`coinitial`).

**(C5)** `S X = X ⟺ X = ⊤` (`shiftQ_fixed_iff`, from `sigFixedTop`).

**(C6)** The conjecture survives and is PROVED, choice-free.  With `L₀`
the closed formulas outside `σ(F0)` (`InL0`):

    X ≠ ⊤  ⟹  ∃ k ∈ ℤ, ∃ y ∈ L₀,  X = Sᵏ (ι₀ y)                 (graded_exists)
    y, y' ∈ L₀,  Sᵏ (ι₀ y) = Sᵏ' (ι₀ y')  ⟹  k = k' ∧ y ⊣⊢ y'      (graded_unique)
    S (Sᵏ (ι₀ y)) = Sᵏ⁺¹ (ι₀ y);   Sᵏ (ι₀ y) ≠ ⊤                   (shiftQ_powQ, graded_ne_top)

so `SigCol ∖ {⊤}` is in bijection with `ℤ × (L₀/⊣⊢)`, `S` acting as
`k ↦ k + 1`.  Existence needs to decide `x ∈ σᵈ(F0)`.  The decision
procedure: `τ` (`tau`), the restriction of a formula to the old worlds of
the two-top extension `ext M` of `wip/f0SelfSim.lean`, is a syntactic left
inverse of `σ` (`tau_sig`: `τ (σψ) ⊣⊢ ψ`), so

    x ∈ σ(F0)  ⟺  σ(τ x) ⊣⊢ x,     x ∈ σᵈ⁺¹(F0)  ⟺  x ∈ σ(F0) ∧ τ x ∈ σᵈ(F0)

(`inSig1_iff`, `inSig_succ_iff`), and `⊣⊢` is decided by
`FRJ.Gbu.W.decideLaxND` (`decInSig`, a `Decidable` instance,
`[propext, Quot.sound]`).  The last `d` with `x ∈ σᵈ(F0)` exists because
`x ∉ σᴺ(F0)` for large `N` (`InsideOut.orbit_order_limit`).  Validation:
`ι₀ t3`, `ι₀ t5`, `ι₁ ⊥` have grades `1`, `0`, `−1` (`grade_t3`,
`grade_t5`, `grade_bot1`, `grades_distinct`).

**(C7)** `ι₀(F0)` is a subalgebra but not convex: `ι₀ ⊥ ≤ ι₁ t5 ≤ ι₀ ⊤`
with `ι₁ t5 ∉ ι₀(F0)` (`iota0_not_convex`), and not a down-set:
`ι₁ ⊥ ≤ ι₀ ⊥` with `ι₁ ⊥ ∉ ι₀(F0)` (`iota0_not_downset`).  So it is not an
up-set, an interval or a principal filter.  What is recognisable: `SigCol`
is the increasing union of the principal filters `↑ιₙ ⊥`, and `S⁻¹` carries
each onto the next (`filter_union`), so all of them are order-isomorphic to
`↑ι₀ ⊥`, which is the colimit of the intervals `[σⁿ⊥, ⊤]` of F0.  OPEN:
whether `↑ι₀ ⊥` is order-isomorphic to F0 (compare the OPEN question
`[t3, ⊤] ≅ F0` of `wip/f0SigOnto.lean`).
-/

open PLLFormula

namespace PLLND
namespace F0
namespace SigmaColimit

open SemUI Sig
open PLLND.LaxInfinite (atomFree)

/-! ## Closed formulas and representatives -/

/-- Closed (variable-free) formulas. -/
abbrev CF : Type := {φ : PLLFormula // atomFree φ = true}

theorem af2 {A B : PLLFormula} (hA : atomFree A = true) (hB : atomFree B = true) :
    (atomFree A && atomFree B) = true := by
  rw [hA, hB]
  rfl

/-- `σ` on closed formulas. -/
def sigCF (φ : CF) : CF := ⟨sig φ.1, sig_vf φ.2⟩

/-- `σᵏ` on closed formulas. -/
def sigNCF (k : ℕ) (φ : CF) : CF := ⟨sigN k φ.1, sigN_vf k φ.2⟩

/-- `⊥`, `⊤`, `◯⊥`, `t5` as closed formulas. -/
def botCF : CF := ⟨.falsePLL, rfl⟩
def topCF : CF := ⟨truePLL, rfl⟩
def oBotCF : CF := ⟨.somehow .falsePLL, rfl⟩
def t5CF : CF := ⟨t5, rfl⟩

/-- **A representative** of an element of the colimit: a stage and a closed
formula. -/
structure Pre where
  st : ℕ
  fm : PLLFormula
  af : atomFree fm = true

/-- **The order on representatives**: `(n, φ) ≤ (m, ψ)` iff `σᵐ φ ⊢ σⁿ ψ`. -/
def leP (x y : Pre) : Prop := Deriv [sigN y.st x.fm] (sigN x.st y.fm)

/-- **The identification**: `(n, φ) ~ (m, ψ)` iff `σᵐ φ ⊣⊢ σⁿ ψ`. -/
def rP (x y : Pre) : Prop := leP x y ∧ leP y x

/-- **The colimit.** -/
def SigCol : Type := Quot rP

/-- The class of a representative. -/
def mk (x : Pre) : SigCol := Quot.mk rP x

/-! ## The signature -/

/-- The `⊥`-free signature: `⊤`, `∧`, `∨`, `↠`, `◯`. -/
structure Ops (A : Type) where
  top : A
  meet : A → A → A
  join : A → A → A
  imp : A → A → A
  nuc : A → A

/-- **Nuclear implicative lattice axioms, for a preorder.** -/
structure NucImpLatPre {A : Type} (le : A → A → Prop) (O : Ops A) : Prop where
  refl : ∀ x, le x x
  trans : ∀ {x y z}, le x y → le y z → le x z
  le_top : ∀ x, le x O.top
  meet_le_left : ∀ x y, le (O.meet x y) x
  meet_le_right : ∀ x y, le (O.meet x y) y
  le_meet : ∀ {x y z}, le z x → le z y → le z (O.meet x y)
  le_join_left : ∀ x y, le x (O.join x y)
  le_join_right : ∀ x y, le y (O.join x y)
  join_le : ∀ {x y z}, le x z → le y z → le (O.join x y) z
  residuation : ∀ x y z, le (O.meet z x) y ↔ le z (O.imp x y)
  nuc_infl : ∀ x, le x (O.nuc x)
  nuc_idem : ∀ x, le (O.nuc (O.nuc x)) (O.nuc x)
  nuc_mono : ∀ {x y}, le x y → le (O.nuc x) (O.nuc y)
  nuc_meet : ∀ x y, le (O.meet (O.nuc x) (O.nuc y)) (O.nuc (O.meet x y))

/-- **A nuclear implicative lattice**: the axioms, for a partial order. -/
structure NucImpLat {A : Type} (le : A → A → Prop) (O : Ops A) : Prop where
  pre : NucImpLatPre le O
  antisymm : ∀ {x y}, le x y → le y x → x = y

/-- The operations of F0 on closed formulas. -/
def opsCF : Ops CF where
  top := topCF
  meet φ ψ := ⟨.and φ.1 ψ.1, af2 φ.2 ψ.2⟩
  join φ ψ := ⟨.or φ.1 ψ.1, af2 φ.2 ψ.2⟩
  imp φ ψ := ⟨.ifThen φ.1 ψ.1, af2 φ.2 ψ.2⟩
  nuc φ := ⟨.somehow φ.1, φ.2⟩

/-! ## The operations on representatives -/

def topP : Pre := ⟨0, truePLL, rfl⟩

def meetP (x y : Pre) : Pre :=
  ⟨x.st + y.st, .and (sigN y.st x.fm) (sigN x.st y.fm), af2 (sigN_vf _ x.af) (sigN_vf _ y.af)⟩

def joinP (x y : Pre) : Pre :=
  ⟨x.st + y.st, .or (sigN y.st x.fm) (sigN x.st y.fm), af2 (sigN_vf _ x.af) (sigN_vf _ y.af)⟩

def impP (x y : Pre) : Pre :=
  ⟨x.st + y.st, .ifThen (sigN y.st x.fm) (sigN x.st y.fm),
    af2 (sigN_vf _ x.af) (sigN_vf _ y.af)⟩

def nucP (x : Pre) : Pre := ⟨x.st, .somehow x.fm, x.af⟩

/-- The operations on representatives. -/
def opsP : Ops Pre := ⟨topP, meetP, joinP, impP, nucP⟩

/-- **The stage maps** `ιₙ φ = (n, φ)`. -/
def iota (n : ℕ) (φ : CF) : Pre := ⟨n, φ.1, φ.2⟩

/-- **The shift** `S (n, φ) = (n, σφ)`. -/
def shiftP (x : Pre) : Pre := ⟨x.st, sig x.fm, sig_vf x.af⟩

/-- **The stage shift** `(n, φ) ↦ (n + 1, φ)`. -/
def unshiftP (x : Pre) : Pre := ⟨x.st + 1, x.fm, x.af⟩

/-- `f` preserves the five operations, up to the relation `R` on the target. -/
def HomRel {A B : Type} (R : B → B → Prop) (OA : Ops A) (OB : Ops B) (f : A → B) : Prop :=
  R (f OA.top) OB.top ∧
  (∀ a b, R (f (OA.meet a b)) (OB.meet (f a) (f b))) ∧
  (∀ a b, R (f (OA.join a b)) (OB.join (f a) (f b))) ∧
  (∀ a b, R (f (OA.imp a b)) (OB.imp (f a) (f b))) ∧
  (∀ a, R (f (OA.nuc a)) (OB.nuc (f a)))

/-- A cocone over the σ-chain in `Set`: `⊣⊢`-invariant maps `fₙ` with
`fₙ₊₁ ∘ σ = fₙ`. -/
def Cocone {A : Type} (f : ℕ → CF → A) : Prop :=
  (∀ n (φ ψ : CF), Interd φ.1 ψ.1 → f n φ = f n ψ) ∧ (∀ n φ, f (n + 1) (sigCF φ) = f n φ)

/-! ## The grading (C6) -/

/-- `y ∈ L₀ = F0 ∖ σ(F0)`. -/
def InL0 (y : PLLFormula) : Prop :=
  atomFree y = true ∧ ¬ ∃ z, atomFree z = true ∧ Interd (sig z) y

/-- `y ∈ σᵈ(F0)`, up to `⊣⊢`. -/
def InSig (d : ℕ) (x : PLLFormula) : Prop := ∃ y, atomFree y = true ∧ Interd (sigN d y) x

/-- **The graded representative**: `(0, σᵏ y)` for `k ≥ 0`, `(−k, y)` for `k < 0`. -/
def grP : ℤ → CF → Pre
  | .ofNat n, y => ⟨0, sigN n y.1, sigN_vf n y.2⟩
  | .negSucc n, y => ⟨n + 1, y.1, y.2⟩

/-- Iteration on representatives. -/
def iterP (f : Pre → Pre) : ℕ → Pre → Pre
  | 0, x => x
  | n + 1, x => iterP f n (f x)

/-- **`Sᵏ`, `k ∈ ℤ`**, on representatives. -/
def powP : ℤ → Pre → Pre
  | .ofNat n => iterP shiftP n
  | .negSucc n => iterP unshiftP (n + 1)

/-! ## Statements (stage 1) -/

namespace Stmt

/-! ### (C1) -/

/-- **(C1)** The representatives form a nuclear implicative preorder; the
quotient by `rP` is then a nuclear implicative lattice. -/
def C1 : Prop := NucImpLatPre leP opsP

/-! ### (C2) -/

/-- `ιₙ₊₁ ∘ σ = ιₙ`. -/
def StageCompat : Prop := ∀ n (φ : CF), rP (iota (n + 1) (sigCF φ)) (iota n φ)

/-- `ιₙ` is an order embedding (so one-to-one on `⊣⊢`-classes). -/
def StageEmb : Prop := ∀ n (φ ψ : CF), leP (iota n φ) (iota n ψ) ↔ Deriv [φ.1] ψ.1

/-- `ιₙ` is a homomorphism. -/
def StageHom : Prop := ∀ n, HomRel rP opsCF opsP (iota n)

/-- **The universal property** of the colimit. -/
def Universal : Prop := ∀ (A : Type) (f : ℕ → CF → A), Cocone f →
  ∃ u : SigCol → A,
    (∀ n φ, u (mk (iota n φ)) = f n φ) ∧
    (∀ u' : SigCol → A, (∀ n φ, u' (mk (iota n φ)) = f n φ) → u' = u) ∧
    (∀ O : Ops A, (∀ n, HomRel Eq opsCF O (f n)) →
      HomRel Eq opsP O (fun x => u (mk x))) ∧
    (∀ leA : A → A → Prop, (∀ n (φ ψ : CF), Deriv [φ.1] ψ.1 → leA (f n φ) (f n ψ)) →
      ∀ x y, leP x y → leA (u (mk x)) (u (mk y)))

/-! ### (C3) -/

/-- `S ∘ ιₙ = ιₙ ∘ σ`. -/
def ShiftExtends : Prop := ∀ n (φ : CF), shiftP (iota n φ) = iota n (sigCF φ)

/-- `S` is an order isomorphism onto its image. -/
def ShiftOrderIso : Prop := ∀ x y, leP x y ↔ leP (shiftP x) (shiftP y)

/-- The stage shift is an order isomorphism onto its image. -/
def UnshiftOrderIso : Prop := ∀ x y, leP x y ↔ leP (unshiftP x) (unshiftP y)

/-- The stage shift is the inverse of `S`. -/
def ShiftInverse : Prop := ∀ x, rP (shiftP (unshiftP x)) x ∧ rP (unshiftP (shiftP x)) x

/-- `S` is a homomorphism. -/
def ShiftHom : Prop := HomRel rP opsP opsP shiftP

/-- The stage shift on a stage image: `ιₙ φ ↦ ιₙ₊₁ φ`. -/
def UnshiftStage : Prop := ∀ n (φ : CF), unshiftP (iota n φ) = iota (n + 1) φ

/-! ### (C4) -/

/-- The stage bottoms strictly decrease: `ιₙ₊₁ ⊥ < ιₙ ⊥`. -/
def BotStrict : Prop := ∀ n,
  leP (iota (n + 1) botCF) (iota n botCF) ∧ ¬ leP (iota n botCF) (iota (n + 1) botCF)

/-- No element lies below all stage bottoms: `(m, χ) ≰ ιₘ₊₁ ⊥`. -/
def NoLowerBound : Prop := ∀ x : Pre, ¬ leP x (iota (x.st + 1) botCF)

/-- The stage bottoms are coinitial: `ιₘ ⊥ ≤ (m, χ)`. -/
def Coinitial : Prop := ∀ x : Pre, leP (iota x.st botCF) x

/-- No least element. -/
def NoLeast : Prop := ¬ ∃ b : Pre, ∀ x, leP b x

/-! ### (C5) -/

/-- `⊤` is the class of the theorems. -/
def TopIff : Prop := ∀ x : Pre, rP x topP ↔ Deriv [] x.fm

/-- **The only fixed point of `S` is `⊤`.** -/
def FixedTop : Prop := ∀ x : Pre, rP (shiftP x) x ↔ rP x topP

/-! ### (C6), a conjecture -/

/-- `grP k y ~ Sᵏ (ι₀ y)`. -/
def GradePow : Prop := ∀ k (y : CF), rP (powP k (iota 0 y)) (grP k y)

/-- `S` acts on grades as `k ↦ k + 1`. -/
def GradeShift : Prop := ∀ k (y : CF), rP (shiftP (grP k y)) (grP (k + 1) y)

/-- Graded elements are not `⊤`. -/
def GradeNotTop : Prop := ∀ k (y : CF), InL0 y.1 → ¬ rP (grP k y) topP

/-- **Uniqueness** of the grade and of the `L₀` part. -/
def GradeInj : Prop := ∀ k k' (y y' : CF), InL0 y.1 → InL0 y'.1 →
  rP (grP k y) (grP k' y') → k = k' ∧ Interd y.1 y'.1

/-- **Existence**: every element other than `⊤` is graded. -/
def GradeSurj : Prop := ∀ x : Pre, ¬ rP x topP → ∃ k : ℤ, ∃ y : CF, InL0 y.1 ∧ rP x (grP k y)

/-- Membership in `σᵈ(F0)` is decided (choice-free). -/
def SigImageDec : Prop := ∀ d x, atomFree x = true → InSig d x ∨ ¬ InSig d x

/-! ### (C7), a question -/

/-- `ι₀(F0)` is not an up-set: `ι₀ ⊥ ≤ ι₁ t5`, and `ι₁ t5 ∉ ι₀(F0)`. -/
def NotUpset : Prop :=
  leP (iota 0 botCF) (iota 1 t5CF) ∧ ¬ ∃ z : CF, rP (iota 0 z) (iota 1 t5CF)

/-- `ι₀(F0)` is not a down-set: `ι₁ ⊥ ≤ ι₀ ⊥`, and `ι₁ ⊥ ∉ ι₀(F0)`. -/
def NotDownset : Prop :=
  leP (iota 1 botCF) (iota 0 botCF) ∧ ¬ ∃ z : CF, rP (iota 0 z) (iota 1 botCF)

/-- The colimit is the increasing union of the principal filters `↑ιₙ ⊥`,
and the stage shift carries `↑ιₙ ⊥` onto `↑ιₙ₊₁ ⊥`. -/
def FilterUnion : Prop :=
  (∀ x : Pre, ∃ n, leP (iota n botCF) x) ∧
  (∀ n (x : Pre), leP (iota n botCF) x ↔ leP (iota (n + 1) botCF) (unshiftP x))

/-! ### Designed cells (stage 2) -/

/-- `ι₁ ⊥ < ι₀ ⊥`. -/
def CellBot : Prop :=
  leP (iota 1 botCF) (iota 0 botCF) ∧ ¬ leP (iota 0 botCF) (iota 1 botCF)

/-- `S` fixes `⊤` and moves `ι₀ (◯⊥)`. -/
def CellShiftTop : Prop :=
  rP (shiftP topP) topP ∧ ¬ rP (shiftP (iota 0 oBotCF)) (iota 0 oBotCF)

/-- `ι₀ t5` is not `S z` for `z` in the stage-0 image, and `t5 ∈ L₀`. -/
def CellT5 : Prop :=
  (¬ ∃ z : CF, rP (shiftP (iota 0 z)) (iota 0 t5CF)) ∧ InL0 t5

end Stmt

/-! ## Designed cells (stage 2)

Each cell is read off the rules and the banked F0 facts; the one new
countermodel (`M1`, one world, in `S`) is checked by `decide +kernel`. -/

/-- One world, in `S`: `◯⊥` fails there and `t3` holds. -/
def M1 : SubTab.SubCM := { n := 1, root := 0, le := [[true]], S := [true], val := [[]] }

/-- One world, not in `S` (the gate's model): every `◯`-formula holds. -/
def M0 : SubTab.SubCM := { n := 1, root := 0, le := [[true]], S := [false], val := [[]] }

/-- **Cell: `ι₁ ⊥ < ι₀ ⊥`** (`sigN_bot_strict 0`). -/
theorem cellBot : Stmt.CellBot := ⟨(sigN_bot_strict 0).1, (sigN_bot_strict 0).2⟩

/-- `◯t3 ⊬ ◯⊥`, refuted at the one-world model `M1`. -/
theorem nd_oT3_oBot : ¬ Deriv [.somehow t3] (.somehow .falsePLL) := fun h =>
  SubTab.SubCM.refutes_sound (m := M1) (by decide +kernel) (Deriv.impIntro h)

/-- **Cell: `S ⊤ ~ ⊤`, and `S (ι₀ ◯⊥) = ι₀ ◯t3 ≁ ι₀ ◯⊥`.** -/
theorem cellShiftTop : Stmt.CellShiftTop :=
  ⟨⟨Deriv.impIntro (Deriv.iden (.head _)), Deriv.impIntro (Deriv.iden (.head _))⟩,
    fun h => nd_oT3_oBot h.1⟩

/-- **Cell: `ι₀ t5` is not `S (ι₀ z)`** (`sig_not_onto`), **and `t5 ∈ L₀`**. -/
theorem cellT5 : Stmt.CellT5 :=
  ⟨fun ⟨z, hz⟩ => SigOnto.sig_not_onto ⟨z.1, z.2, hz⟩,
    ⟨rfl, fun ⟨z, hz, hi⟩ => SigOnto.sig_not_onto ⟨z, hz, hi⟩⟩⟩

/-! ### Gates and controls, watched failing -/

/-- Gate: `M1` does not refute the derivable direction `◯⊥ ↠ ◯t3`. -/
theorem gate_M1 : M1.refutes ((PLLFormula.somehow .falsePLL).ifThen (.somehow t3)) = false := by
  decide +kernel

/-- Gate: the model without `S`-points does not refute `◯t3 ↠ ◯⊥`. -/
theorem gate_M0 : M0.refutes ((PLLFormula.somehow t3).ifThen (.somehow .falsePLL)) = false := by
  decide +kernel

/-- Control: at `t3 = σ⊥` in place of `t5` the statement of `cellT5` fails:
`ι₀ t3 = S (ι₀ ⊥)`. -/
theorem ctrl_t3 : ∃ z : CF, rP (shiftP (iota 0 z)) (iota 0 ⟨t3, rfl⟩) :=
  ⟨botCF, Deriv.iden (.head _), Deriv.iden (.head _)⟩

/-! The swapped `CellBot` is rejected (watched failing). -/

/--
error: Type mismatch
  (sigN_bot_strict 0).left
has type
  Deriv [sigN 0 ⊥] (sigN (0 + 1) ⊥)
but is expected to have type
  leP (iota 0 botCF) (iota 1 botCF)
-/
#guard_msgs in
example : leP (iota 0 botCF) (iota 1 botCF) := (sigN_bot_strict 0).1

/-! ## Stage 3: proofs -/

/-! ### Arithmetic of `σᵏ` -/

theorem sigN_sigN (a b : ℕ) (φ : PLLFormula) : sigN a (sigN b φ) = sigN (a + b) φ :=
  (InsideOut.sigN_add b a φ).symm

theorem sigN_and : ∀ (n : ℕ) (A B : PLLFormula), sigN n (.and A B) = .and (sigN n A) (sigN n B)
  | 0, _, _ => rfl
  | n + 1, A, B => sigN_and n (sig A) (sig B)

/-- Weakening a theorem. -/
theorem weaken {a φ : PLLFormula} (h : Deriv [] φ) : Deriv [a] φ :=
  Deriv.rename (fun _ hx => absurd hx List.not_mem_nil) h

theorem thm_top : Deriv [] truePLL := Deriv.impIntro (Deriv.iden (.head _))

/-- `σᵏ` preserves theorems. -/
theorem deriv_sigN : ∀ (n : ℕ) {φ : PLLFormula}, atomFree φ = true → Deriv [] φ →
    Deriv [] (sigN n φ)
  | 0, _, _, h => h
  | n + 1, _, hφ, h =>
      deriv_sigN n (sig_vf hφ) (subBot_deriv t3 (Γ := []) (fun _ hx => nomatch hx) hφ h)

/-! ### The common-stage lemma -/

/-- **`(n, φ) ≤ (m, ψ)` iff `σᵏ φ ⊢ σʲ ψ`, for any `n + k = m + j`.** -/
theorem leP_iff_at {x y : Pre} {k j : ℕ} (h : x.st + k = y.st + j) :
    leP x y ↔ Deriv [sigN k x.fm] (sigN j y.fm) := by
  have h1 := sigN_faithful k (sigN_vf y.st x.af) (sigN_vf x.st y.af)
  have h2 := sigN_faithful y.st (sigN_vf k x.af) (sigN_vf j y.af)
  rw [sigN_sigN, sigN_sigN] at h1 h2
  have e1 : k + y.st = y.st + k := Nat.add_comm _ _
  have e2 : k + x.st = y.st + j := by omega
  rw [e1, e2] at h1
  exact h1.trans h2.symm

theorem rP_iff_at {x y : Pre} {k j : ℕ} (h : x.st + k = y.st + j) :
    rP x y ↔ Interd (sigN k x.fm) (sigN j y.fm) :=
  and_congr (leP_iff_at h) (leP_iff_at h.symm)

/-- Same stage: the order of the formulas. -/
theorem leP_same {x y : Pre} (h : x.st = y.st) : leP x y ↔ Deriv [x.fm] y.fm :=
  leP_iff_at (k := 0) (j := 0) (by omega)

theorem rP_of_fm {x y : Pre} (hst : x.st = y.st) (hfm : x.fm = y.fm) : rP x y := by
  unfold rP leP
  rw [hst, hfm]
  exact ⟨Deriv.iden (.head _), Deriv.iden (.head _)⟩

/-- Two representatives of theorems are identified. -/
theorem rP_of_thm {x y : Pre} (hx : Deriv [] x.fm) (hy : Deriv [] y.fm) : rP x y :=
  ⟨weaken (deriv_sigN x.st y.af hy), weaken (deriv_sigN y.st x.af hx)⟩

/-! ### (C1): the preorder and the laws -/

theorem leP_refl (x : Pre) : leP x x := Deriv.iden (.head _)

theorem leP_trans {x y z : Pre} (h1 : leP x y) (h2 : leP y z) : leP x z := by
  have a1 := (leP_iff_at (x := x) (y := y) (k := y.st + z.st) (j := x.st + z.st)
    (by omega)).mp h1
  have a2 := (leP_iff_at (x := y) (y := z) (k := x.st + z.st) (j := x.st + y.st)
    (by omega)).mp h2
  exact (leP_iff_at (x := x) (y := z) (k := y.st + z.st) (j := x.st + y.st)
    (by omega)).mpr (Deriv.cutHead a1 a2)

theorem rP_refl (x : Pre) : rP x x := ⟨leP_refl x, leP_refl x⟩

theorem rP_symm {x y : Pre} (h : rP x y) : rP y x := ⟨h.2, h.1⟩

theorem rP_trans {x y z : Pre} (h1 : rP x y) (h2 : rP y z) : rP x z :=
  ⟨leP_trans h1.1 h2.1, leP_trans h2.2 h1.2⟩

theorem sigN_meetP (k : ℕ) (x y : Pre) :
    sigN k (meetP x y).fm = .and (sigN (k + y.st) x.fm) (sigN (k + x.st) y.fm) := by
  show sigN k (.and (sigN y.st x.fm) (sigN x.st y.fm)) = _
  rw [sigN_and, sigN_sigN, sigN_sigN]

theorem sigN_joinP (k : ℕ) (x y : Pre) :
    sigN k (joinP x y).fm = .or (sigN (k + y.st) x.fm) (sigN (k + x.st) y.fm) := by
  show sigN k (.or (sigN y.st x.fm) (sigN x.st y.fm)) = _
  rw [InsideOut.sigN_or, sigN_sigN, sigN_sigN]

theorem sigN_impP (k : ℕ) (x y : Pre) :
    sigN k (impP x y).fm = .ifThen (sigN (k + y.st) x.fm) (sigN (k + x.st) y.fm) := by
  show sigN k (.ifThen (sigN y.st x.fm) (sigN x.st y.fm)) = _
  rw [sigN_imp, sigN_sigN, sigN_sigN]

theorem le_topP (x : Pre) : leP x topP := by
  show Deriv [sigN 0 x.fm] (sigN x.st (PLLFormula.ifThen .falsePLL .falsePLL))
  rw [sigN_imp]
  exact Deriv.impIntro (Deriv.iden (.head _))

theorem meetP_le_left (x y : Pre) : leP (meetP x y) x :=
  (leP_iff_at (x := meetP x y) (y := x) (k := 0) (j := y.st) (by dsimp only [meetP]; omega)).mpr
    (Deriv.andElim1 (Deriv.iden (.head _)))

theorem meetP_le_right (x y : Pre) : leP (meetP x y) y :=
  (leP_iff_at (x := meetP x y) (y := y) (k := 0) (j := x.st) (by dsimp only [meetP]; omega)).mpr
    (Deriv.andElim2 (Deriv.iden (.head _)))

theorem le_meetP {x y z : Pre} (hx : leP z x) (hy : leP z y) : leP z (meetP x y) := by
  have a := (leP_iff_at (x := z) (y := x) (k := x.st + y.st) (j := z.st + y.st)
    (by omega)).mp hx
  have b := (leP_iff_at (x := z) (y := y) (k := x.st + y.st) (j := z.st + x.st)
    (by omega)).mp hy
  refine (leP_iff_at (x := z) (y := meetP x y) (k := x.st + y.st) (j := z.st)
    (by dsimp only [meetP]; omega)).mpr ?_
  rw [sigN_meetP]
  exact Deriv.andIntro a b

theorem le_joinP_left (x y : Pre) : leP x (joinP x y) :=
  (leP_iff_at (x := x) (y := joinP x y) (k := y.st) (j := 0) (by dsimp only [joinP]; omega)).mpr
    (Deriv.orIntro1 (Deriv.iden (.head _)))

theorem le_joinP_right (x y : Pre) : leP y (joinP x y) :=
  (leP_iff_at (x := y) (y := joinP x y) (k := x.st) (j := 0) (by dsimp only [joinP]; omega)).mpr
    (Deriv.orIntro2 (Deriv.iden (.head _)))

theorem joinP_le {x y z : Pre} (hx : leP x z) (hy : leP y z) : leP (joinP x y) z := by
  have a := (leP_iff_at (x := x) (y := z) (k := z.st + y.st) (j := x.st + y.st)
    (by omega)).mp hx
  have b := (leP_iff_at (x := y) (y := z) (k := z.st + x.st) (j := x.st + y.st)
    (by omega)).mp hy
  refine (leP_iff_at (x := joinP x y) (y := z) (k := z.st) (j := x.st + y.st)
    (by dsimp only [joinP]; omega)).mpr ?_
  rw [sigN_joinP]
  exact Deriv.orElim (Deriv.iden (.head _)) a.toHead b.toHead

/-- **Residuation**: `z ⊓ x ≤ y ↔ z ≤ x ↠ y`. -/
theorem residP (x y z : Pre) : leP (meetP z x) y ↔ leP z (impP x y) := by
  rw [leP_iff_at (x := meetP z x) (y := y) (k := y.st) (j := z.st + x.st)
      (by dsimp only [meetP]; omega),
    leP_iff_at (x := z) (y := impP x y) (k := x.st + y.st) (j := z.st)
      (by dsimp only [impP]; omega),
    sigN_meetP, sigN_impP, Nat.add_comm y.st x.st, Nat.add_comm y.st z.st]
  exact ⟨fun h => Deriv.impIntro (Deriv.cutHead
      (Deriv.andIntro (Deriv.iden (.tail _ (.head _))) (Deriv.iden (.head _))) h),
    fun h => Deriv.impElim (Deriv.cutHead (Deriv.andElim1 (Deriv.iden (.head _))) h)
      (Deriv.andElim2 (Deriv.iden (.head _)))⟩

theorem nucP_infl (x : Pre) : leP x (nucP x) := by
  show Deriv [sigN x.st x.fm] (sigN x.st (.somehow x.fm))
  rw [InsideOut.sigN_somehow]
  exact ⟨.laxIntro (.iden (.head _))⟩

theorem nucP_idem (x : Pre) : leP (nucP (nucP x)) (nucP x) := by
  show Deriv [sigN x.st (.somehow (.somehow x.fm))] (sigN x.st (.somehow x.fm))
  rw [InsideOut.sigN_somehow, InsideOut.sigN_somehow]
  exact ⟨.laxElim (.iden (.head _)) (.iden (.head _))⟩

theorem nucP_mono {x y : Pre} (h : leP x y) : leP (nucP x) (nucP y) := by
  show Deriv [sigN y.st (.somehow x.fm)] (sigN x.st (.somehow y.fm))
  rw [InsideOut.sigN_somehow, InsideOut.sigN_somehow]
  exact Deriv.somehowMono h

/-- `◯A ∧ ◯B ⊢ ◯(A ∧ B)`. -/
theorem box_and {A B : PLLFormula} : Deriv [.and (.somehow A) (.somehow B)] (.somehow (.and A B)) :=
  ⟨.laxElim (.andElim1 (.iden (.head _)))
    (.laxElim (.andElim2 (.iden (.tail _ (.head _))))
      (.laxIntro (.andIntro (.iden (.tail _ (.head _))) (.iden (.head _)))))⟩

theorem nucP_meet (x y : Pre) : leP (meetP (nucP x) (nucP y)) (nucP (meetP x y)) := by
  refine (leP_same (x := meetP (nucP x) (nucP y)) (y := nucP (meetP x y)) rfl).mpr ?_
  show Deriv [.and (sigN y.st (.somehow x.fm)) (sigN x.st (.somehow y.fm))]
    (.somehow (.and (sigN y.st x.fm) (sigN x.st y.fm)))
  rw [InsideOut.sigN_somehow, InsideOut.sigN_somehow]
  exact box_and

/-- **(C1) PROVED.** -/
theorem c1 : Stmt.C1 where
  refl := leP_refl
  trans := leP_trans
  le_top := le_topP
  meet_le_left := meetP_le_left
  meet_le_right := meetP_le_right
  le_meet := le_meetP
  le_join_left := le_joinP_left
  le_join_right := le_joinP_right
  join_le := joinP_le
  residuation := residP
  nuc_infl := nucP_infl
  nuc_idem := nucP_idem
  nuc_mono := nucP_mono
  nuc_meet := nucP_meet

/-! ### Monotonicity, hence compatibility with `~` -/

theorem meetP_mono {x x' y y' : Pre} (hx : leP x x') (hy : leP y y') :
    leP (meetP x y) (meetP x' y') :=
  le_meetP (leP_trans (meetP_le_left x y) hx) (leP_trans (meetP_le_right x y) hy)

theorem joinP_mono {x x' y y' : Pre} (hx : leP x x') (hy : leP y y') :
    leP (joinP x y) (joinP x' y') :=
  joinP_le (leP_trans hx (le_joinP_left x' y')) (leP_trans hy (le_joinP_right x' y'))

theorem impP_mono {x x' y y' : Pre} (hx : leP x' x) (hy : leP y y') :
    leP (impP x y) (impP x' y') :=
  (residP x' y' (impP x y)).mp (leP_trans (leP_trans (meetP_mono (leP_refl _) hx)
    ((residP x y (impP x y)).mpr (leP_refl _))) hy)

theorem meet_compat {x x' y y' : Pre} (hx : rP x x') (hy : rP y y') :
    rP (meetP x y) (meetP x' y') := ⟨meetP_mono hx.1 hy.1, meetP_mono hx.2 hy.2⟩

theorem join_compat {x x' y y' : Pre} (hx : rP x x') (hy : rP y y') :
    rP (joinP x y) (joinP x' y') := ⟨joinP_mono hx.1 hy.1, joinP_mono hx.2 hy.2⟩

theorem imp_compat {x x' y y' : Pre} (hx : rP x x') (hy : rP y y') :
    rP (impP x y) (impP x' y') := ⟨impP_mono hx.2 hy.1, impP_mono hx.1 hy.2⟩

theorem nuc_compat {x y : Pre} (h : rP x y) : rP (nucP x) (nucP y) :=
  ⟨nucP_mono h.1, nucP_mono h.2⟩

/-! ### (C3) on representatives -/

theorem shiftExtends : Stmt.ShiftExtends := fun _ _ => rfl

theorem unshiftStage : Stmt.UnshiftStage := fun _ _ => rfl

theorem shift_iff (x y : Pre) : leP x y ↔ leP (shiftP x) (shiftP y) := by
  show _ ↔ Deriv [sigN y.st (sig x.fm)] (sigN x.st (sig y.fm))
  rw [← InsideOut.sig_sigN, ← InsideOut.sig_sigN]
  exact sigN_faithful 1 (sigN_vf _ x.af) (sigN_vf _ y.af)

theorem shiftOrderIso : Stmt.ShiftOrderIso := shift_iff

theorem unshift_iff (x y : Pre) : leP x y ↔ leP (unshiftP x) (unshiftP y) :=
  (leP_iff_at (x := unshiftP x) (y := unshiftP y) (k := y.st) (j := x.st)
    (by dsimp only [unshiftP]; omega)).symm

theorem unshiftOrderIso : Stmt.UnshiftOrderIso := unshift_iff

theorem shift_unshift (x : Pre) : rP (shiftP (unshiftP x)) x :=
  ⟨Deriv.iden (.head _), Deriv.iden (.head _)⟩

theorem shiftInverse : Stmt.ShiftInverse := fun x => ⟨shift_unshift x, shift_unshift x⟩

theorem shift_compat {x y : Pre} (h : rP x y) : rP (shiftP x) (shiftP y) :=
  ⟨(shift_iff x y).mp h.1, (shift_iff y x).mp h.2⟩

theorem unshift_compat {x y : Pre} (h : rP x y) : rP (unshiftP x) (unshiftP y) :=
  ⟨(unshift_iff x y).mp h.1, (unshift_iff y x).mp h.2⟩

theorem shiftHom : Stmt.ShiftHom :=
  ⟨cellShiftTop.1,
   fun x y => rP_of_fm rfl (by
     show PLLFormula.and (sig (sigN y.st x.fm)) (sig (sigN x.st y.fm)) =
       PLLFormula.and (sigN y.st (sig x.fm)) (sigN x.st (sig y.fm))
     rw [InsideOut.sig_sigN, InsideOut.sig_sigN]),
   fun x y => rP_of_fm rfl (by
     show PLLFormula.or (sig (sigN y.st x.fm)) (sig (sigN x.st y.fm)) =
       PLLFormula.or (sigN y.st (sig x.fm)) (sigN x.st (sig y.fm))
     rw [InsideOut.sig_sigN, InsideOut.sig_sigN]),
   fun x y => rP_of_fm rfl (by
     show PLLFormula.ifThen (sig (sigN y.st x.fm)) (sig (sigN x.st y.fm)) =
       PLLFormula.ifThen (sigN y.st (sig x.fm)) (sigN x.st (sig y.fm))
     rw [InsideOut.sig_sigN, InsideOut.sig_sigN]),
   fun x => rP_refl _⟩

/-! ### (C2) on representatives -/

theorem stageCompat : Stmt.StageCompat := fun _ _ => ⟨Deriv.iden (.head _), Deriv.iden (.head _)⟩

theorem stageEmb : Stmt.StageEmb := fun n φ ψ => (sigN_faithful n φ.2 ψ.2).symm

theorem stageHom : Stmt.StageHom := fun n =>
  ⟨rP_of_thm thm_top thm_top,
   fun φ ψ => (rP_iff_at (x := iota n (opsCF.meet φ ψ)) (y := meetP (iota n φ) (iota n ψ))
     (k := n) (j := 0) (by dsimp only [iota, meetP]; omega)).mpr
       (by rw [show sigN n (iota n (opsCF.meet φ ψ)).fm =
           sigN 0 (meetP (iota n φ) (iota n ψ)).fm from sigN_and n φ.1 ψ.1]
           exact Interd.refl _),
   fun φ ψ => (rP_iff_at (x := iota n (opsCF.join φ ψ)) (y := joinP (iota n φ) (iota n ψ))
     (k := n) (j := 0) (by dsimp only [iota, joinP]; omega)).mpr
       (by rw [show sigN n (iota n (opsCF.join φ ψ)).fm =
           sigN 0 (joinP (iota n φ) (iota n ψ)).fm from InsideOut.sigN_or n φ.1 ψ.1]
           exact Interd.refl _),
   fun φ ψ => (rP_iff_at (x := iota n (opsCF.imp φ ψ)) (y := impP (iota n φ) (iota n ψ))
     (k := n) (j := 0) (by dsimp only [iota, impP]; omega)).mpr
       (by rw [show sigN n (iota n (opsCF.imp φ ψ)).fm =
           sigN 0 (impP (iota n φ) (iota n ψ)).fm from sigN_imp n φ.1 ψ.1]
           exact Interd.refl _),
   fun _ => rP_refl _⟩

/-! ### (C2) The universal property -/

theorem cocone_iter {A : Type} {f : ℕ → CF → A} (hf : Cocone f) :
    ∀ (k n : ℕ) (φ : CF), f (n + k) (sigNCF k φ) = f n φ
  | 0, _, _ => rfl
  | k + 1, n, φ => by
      have e : sigNCF (k + 1) φ = sigCF (sigNCF k φ) := Subtype.ext (InsideOut.sigN_succ k φ.1)
      rw [e, show n + (k + 1) = (n + k) + 1 from rfl, hf.2]
      exact cocone_iter hf k n φ

theorem cocone_compat {A : Type} {f : ℕ → CF → A} (hf : Cocone f) {x y : Pre} (h : rP x y) :
    f x.st ⟨x.fm, x.af⟩ = f y.st ⟨y.fm, y.af⟩ := by
  rw [← cocone_iter hf y.st x.st ⟨x.fm, x.af⟩, ← cocone_iter hf x.st y.st ⟨y.fm, y.af⟩,
    Nat.add_comm y.st x.st]
  exact hf.1 _ _ _ ⟨h.1, h.2⟩

/-- The mediating map. -/
def liftU {A : Type} (f : ℕ → CF → A) (hf : Cocone f) : SigCol → A :=
  Quot.lift (fun x : Pre => f x.st ⟨x.fm, x.af⟩) (fun _ _ h => cocone_compat hf h)

/-- **(C2) The universal property, PROVED.** -/
theorem universal : Stmt.Universal := by
  intro A f hf
  refine ⟨liftU f hf, fun _ _ => rfl, ?_, ?_, ?_⟩
  · intro u' hu'
    funext X
    induction X using Quot.ind
    rename_i x
    exact hu' x.st ⟨x.fm, x.af⟩
  · intro O hO
    have e1 : ∀ x y : Pre, f (x.st + y.st) (sigNCF y.st ⟨x.fm, x.af⟩) = f x.st ⟨x.fm, x.af⟩ :=
      fun x y => cocone_iter hf y.st x.st ⟨x.fm, x.af⟩
    have e2 : ∀ x y : Pre, f (x.st + y.st) (sigNCF x.st ⟨y.fm, y.af⟩) = f y.st ⟨y.fm, y.af⟩ :=
      fun x y => by rw [Nat.add_comm]; exact cocone_iter hf x.st y.st ⟨y.fm, y.af⟩
    refine ⟨(hO 0).1, fun x y => ?_, fun x y => ?_, fun x y => ?_, fun x => by exact (hO x.st).2.2.2.2 ⟨x.fm, x.af⟩⟩
    · have h1 := (hO (x.st + y.st)).2.1 (sigNCF y.st ⟨x.fm, x.af⟩) (sigNCF x.st ⟨y.fm, y.af⟩)
      rw [e1, e2] at h1
      exact h1
    · have h1 := (hO (x.st + y.st)).2.2.1 (sigNCF y.st ⟨x.fm, x.af⟩) (sigNCF x.st ⟨y.fm, y.af⟩)
      rw [e1, e2] at h1
      exact h1
    · have h1 := (hO (x.st + y.st)).2.2.2.1 (sigNCF y.st ⟨x.fm, x.af⟩) (sigNCF x.st ⟨y.fm, y.af⟩)
      rw [e1, e2] at h1
      exact h1
  · intro leA hmono x y hxy
    have h1 := hmono (x.st + y.st) (sigNCF y.st ⟨x.fm, x.af⟩) (sigNCF x.st ⟨y.fm, y.af⟩) hxy
    rw [cocone_iter hf y.st x.st ⟨x.fm, x.af⟩, Nat.add_comm x.st y.st,
      cocone_iter hf x.st y.st ⟨y.fm, y.af⟩] at h1
    exact h1

/-! ### (C4) -/

theorem botStrict : Stmt.BotStrict := fun n => ⟨(sigN_bot_strict n).1, (sigN_bot_strict n).2⟩

/-- **No element lies below `ιₘ₊₁ ⊥`**: `(m, χ) ≤ ιₘ₊₁ ⊥` would give `σχ ⊢ ⊥`,
while `t3 ⊢ σχ`. -/
theorem noLowerBound : Stmt.NoLowerBound := fun x h =>
  nd_t3_bot (Deriv.cutHead (subBot_top t3 x.af)
    (sigN_reflects_ctx x.st (φ := sig x.fm) (ψ := .falsePLL) h))

theorem coinitial : Stmt.Coinitial := fun x => sigN_bot_le x.st x.fm x.af

theorem noLeast : Stmt.NoLeast := fun ⟨b, hb⟩ => noLowerBound b (hb _)

/-! ### (C5) -/

theorem topIff : Stmt.TopIff := fun x =>
  ⟨fun h => Deriv.cutHead (deriv_sigN x.st rfl thm_top) h.2, fun h => rP_of_thm h thm_top⟩

/-- **(C5) PROVED: the only fixed point of `S` is `⊤`** (`sigFixedTop`). -/
theorem fixedTop : Stmt.FixedTop := fun x =>
  ⟨fun h => (topIff x).mpr (MovingTop.sigFixedTop x.fm x.af
      ⟨sigN_reflects_ctx x.st (φ := sig x.fm) (ψ := x.fm) h.1,
        sigN_reflects_ctx x.st (φ := x.fm) (ψ := sig x.fm) h.2⟩),
   fun h => rP_of_thm (deriv_sigN 1 x.af ((topIff x).mp h)) ((topIff x).mp h)⟩

/-! ### (C6) A left inverse of `σ`, and the decision of `σᵈ(F0)`

`ext M` (`wip/f0SelfSim.lean`) adds two maximal worlds above every world of
`M`: `nT ∈ S` and `eT ∉ S`.  A formula's truth at `nT` is `valN`, at `eT`
is `valE`, and its truth at an old world is the truth of `τ φ` in `M`
(`orig_tau`).  Since `ext M, w ⊨ σψ ⟺ M, w ⊨ ψ` (`orig_sig`),
`τ (σψ) ⊣⊢ ψ`: `τ` is a left inverse of `σ`, so `x ∈ σ(F0)` iff
`σ(τ x) ⊣⊢ x`, which `decideLaxND` decides. -/

/-- Truth at a maximal point in `S`. -/
def valN : PLLFormula → Bool
  | .prop _ => true
  | .falsePLL => false
  | .and A B => valN A && valN B
  | .or A B => valN A || valN B
  | .ifThen A B => !valN A || valN B
  | .somehow A => valN A

/-- Truth at a maximal point outside `S`. -/
def valE : PLLFormula → Bool
  | .prop _ => true
  | .falsePLL => false
  | .and A B => valE A && valE B
  | .or A B => valE A || valE B
  | .ifThen A B => !valE A || valE B
  | .somehow _ => true

/-- **The restriction `τ`** to the old worlds of `ext M`. -/
def tau : PLLFormula → PLLFormula
  | .prop q => .prop q
  | .falsePLL => .falsePLL
  | .and A B => .and (tau A) (tau B)
  | .or A B => .or (tau A) (tau B)
  | .ifThen A B =>
      cond ((!valN A || valN B) && (!valE A || valE B)) (.ifThen (tau A) (tau B)) .falsePLL
  | .somehow A => cond (valN A) (.somehow (tau A)) .falsePLL

theorem bimp_of {a b : Bool} (h : a = true → b = true) : (!a || b) = true := by
  cases a
  · rfl
  · rw [h rfl]
    rfl

theorem of_bimp {a b : Bool} (h : (!a || b) = true) (ha : a = true) : b = true := by
  rw [ha] at h
  exact h

theorem force_nT (M : SubframeModel) :
    ∀ φ : PLLFormula, (ext M).force XW.nT φ ↔ valN φ = true
  | .prop _ => ⟨fun _ => rfl, fun _ => trivial⟩
  | .falsePLL => ⟨False.elim, fun h => Bool.false_ne_true h⟩
  | .and A B => (and_congr (force_nT M A) (force_nT M B)).trans Bool.and_eq_true_iff.symm
  | .or A B => (or_congr (force_nT M A) (force_nT M B)).trans Bool.or_eq_true_iff.symm
  | .ifThen A B => by
      have hA := force_nT M A
      have hB := force_nT M B
      constructor
      · intro h
        exact bimp_of fun ha => hB.mp (h XW.nT trivial (hA.mpr ha))
      · intro h v hv hAv
        cases v with
        | orig _ => exact False.elim hv
        | nT => exact hB.mpr (of_bimp h (hA.mp hAv))
        | eT => exact False.elim hv
  | .somehow A => by
      have hA := force_nT M A
      constructor
      · intro h
        exact hA.mp (h XW.nT trivial trivial)
      · intro h v hv _
        cases v with
        | orig _ => exact False.elim hv
        | nT => exact hA.mpr h
        | eT => exact False.elim hv

theorem force_eT (M : SubframeModel) :
    ∀ φ : PLLFormula, (ext M).force XW.eT φ ↔ valE φ = true
  | .prop _ => ⟨fun _ => rfl, fun _ => trivial⟩
  | .falsePLL => ⟨False.elim, fun h => Bool.false_ne_true h⟩
  | .and A B => (and_congr (force_eT M A) (force_eT M B)).trans Bool.and_eq_true_iff.symm
  | .or A B => (or_congr (force_eT M A) (force_eT M B)).trans Bool.or_eq_true_iff.symm
  | .ifThen A B => by
      have hA := force_eT M A
      have hB := force_eT M B
      constructor
      · intro h
        exact bimp_of fun ha => hB.mp (h XW.eT trivial (hA.mpr ha))
      · intro h v hv hAv
        cases v with
        | orig _ => exact False.elim hv
        | nT => exact False.elim hv
        | eT => exact hB.mpr (of_bimp h (hA.mp hAv))
  | .somehow _ => ⟨fun _ => rfl, fun _ v hv hS => by
      cases v with
      | orig _ => exact False.elim hv
      | nT => exact False.elim hv
      | eT => exact False.elim hS⟩

/-- **`τ φ` holds at `w` in `M` iff `φ` holds at `w` in `ext M`.** -/
theorem orig_tau (M : SubframeModel) : ∀ (φ : PLLFormula) (x : M.W),
    (ext M).force (XW.orig x) φ ↔ M.force x (tau φ)
  | .prop _, _ => Iff.rfl
  | .falsePLL, _ => Iff.rfl
  | .and A B, x => and_congr (orig_tau M A x) (orig_tau M B x)
  | .or A B, x => or_congr (orig_tau M A x) (orig_tau M B x)
  | .ifThen A B, x => by
      have hA := force_nT M A
      have hB := force_nT M B
      have eA := force_eT M A
      have eB := force_eT M B
      have ihA := orig_tau M A
      have ihB := orig_tau M B
      show (ext M).force (XW.orig x) (.ifThen A B) ↔
        M.force x (cond ((!valN A || valN B) && (!valE A || valE B))
          (.ifThen (tau A) (tau B)) .falsePLL)
      cases hc : ((!valN A || valN B) && (!valE A || valE B)) with
      | true =>
          obtain ⟨hcN, hcE⟩ := Bool.and_eq_true_iff.mp hc
          constructor
          · intro h y hxy hy
            exact (ihB y).mp (h (XW.orig y) hxy ((ihA y).mpr hy))
          · intro h v hv hAv
            cases v with
            | orig y => exact (ihB y).mpr (h y hv ((ihA y).mp hAv))
            | nT => exact hB.mpr (of_bimp hcN (hA.mp hAv))
            | eT => exact eB.mpr (of_bimp hcE (eA.mp hAv))
      | false =>
          constructor
          · intro h
            have hN : (!valN A || valN B) = true :=
              bimp_of fun ha => hB.mp (h XW.nT trivial (hA.mpr ha))
            have hE : (!valE A || valE B) = true :=
              bimp_of fun ha => eB.mp (h XW.eT trivial (eA.mpr ha))
            rw [hN, hE] at hc
            exact absurd hc (by decide)
          · intro h
            exact False.elim h
  | .somehow A, x => by
      have hA := force_nT M A
      have ihA := orig_tau M A
      show (ext M).force (XW.orig x) (.somehow A) ↔
        M.force x (cond (valN A) (.somehow (tau A)) .falsePLL)
      cases hc : valN A with
      | true =>
          constructor
          · intro h y hxy hS
            exact (ihA y).mp (h (XW.orig y) hxy hS)
          · intro h v hv hS
            cases v with
            | orig y => exact (ihA y).mpr (h y hv hS)
            | nT => exact hA.mpr hc
            | eT => exact False.elim hS
      | false =>
          constructor
          · intro h
            have h1 := hA.mp (h XW.nT trivial trivial)
            rw [hc] at h1
            exact absurd h1 (by decide)
          · intro h
            exact False.elim h

theorem tau_af : ∀ φ : PLLFormula, atomFree φ = true → atomFree (tau φ) = true
  | .prop _, h => h
  | .falsePLL, _ => rfl
  | .and A B, h =>
      af2 (tau_af A (Bool.and_eq_true_iff.mp h).1) (tau_af B (Bool.and_eq_true_iff.mp h).2)
  | .or A B, h =>
      af2 (tau_af A (Bool.and_eq_true_iff.mp h).1) (tau_af B (Bool.and_eq_true_iff.mp h).2)
  | .ifThen A B, h => by
      show atomFree (cond ((!valN A || valN B) && (!valE A || valE B))
        (.ifThen (tau A) (tau B)) .falsePLL) = true
      cases ((!valN A || valN B) && (!valE A || valE B))
      · rfl
      · exact af2 (tau_af A (Bool.and_eq_true_iff.mp h).1) (tau_af B (Bool.and_eq_true_iff.mp h).2)
  | .somehow A, h => by
      show atomFree (cond (valN A) (.somehow (tau A)) .falsePLL) = true
      cases valN A
      · rfl
      · exact tau_af A h

/-- **`τ` is a left inverse of `σ`**: `τ (σψ) ⊣⊢ ψ`, for every formula. -/
theorem tau_sig (ψ : PLLFormula) : Interd (tau (sig ψ)) ψ :=
  MovingTop.interd_of_sem fun M w => (orig_tau M (sig ψ) w).symm.trans (orig_sig M ψ w)

/-- `τ` is monotone. -/
theorem tau_mono {x x' : PLLFormula} (h : Deriv [x] x') : Deriv [tau x] (tau x') :=
  Interval.deriv_of_sem fun M _ w hw =>
    (orig_tau M x' w).mp (Interval.sem_of_deriv h (ext M) (XW.orig w) ((orig_tau M x w).mpr hw))

theorem tau_interd {x x' : PLLFormula} (h : Interd x x') : Interd (tau x) (tau x') :=
  ⟨tau_mono h.1, tau_mono h.2⟩

/-- **`x ∈ σ(F0)` iff `σ(τ x) ⊣⊢ x`.** -/
theorem inSig1_iff {x : PLLFormula} (hx : atomFree x = true) :
    InSig 1 x ↔ Interd (sig (tau x)) x := by
  constructor
  · rintro ⟨y, hy, hi⟩
    have h1 : Interd (tau x) y := (tau_interd hi.symm).trans (tau_sig y)
    exact (InsideOut.sig_interd (tau_af x hx) hy h1).trans hi
  · intro h
    exact ⟨tau x, tau_af x hx, h⟩

/-- **`x ∈ σᵈ⁺¹(F0)` iff `x ∈ σ(F0)` and `τ x ∈ σᵈ(F0)`.** -/
theorem inSig_succ_iff (d : ℕ) {x : PLLFormula} (hx : atomFree x = true) :
    InSig (d + 1) x ↔ Interd (sig (tau x)) x ∧ InSig d (tau x) := by
  constructor
  · rintro ⟨y, hy, hi⟩
    rw [InsideOut.sigN_succ] at hi
    have h1 : Interd (tau x) (sigN d y) := (tau_interd hi.symm).trans (tau_sig _)
    exact ⟨(InsideOut.sig_interd (tau_af x hx) (sigN_vf d hy) h1).trans hi, ⟨y, hy, h1.symm⟩⟩
  · rintro ⟨h1, ⟨y, hy, hi⟩⟩
    refine ⟨y, hy, ?_⟩
    rw [InsideOut.sigN_succ]
    exact (InsideOut.sig_interd (sigN_vf d hy) (tau_af x hx) hi).trans h1

/-- Derivability between two formulas is decidable (`decideLaxND`). -/
def decDeriv (a b : PLLFormula) : Decidable (Deriv [a] b) :=
  match FRJ.Gbu.W.decideLaxND (a.ifThen b) with
  | isTrue h => isTrue (MovingTop.ctx_of_imp h)
  | isFalse h => isFalse fun d => h (Deriv.impIntro d)

def decInterd (a b : PLLFormula) : Decidable (Interd a b) :=
  @instDecidableAnd _ _ (decDeriv a b) (decDeriv b a)

/-- **Membership in `σᵈ(F0)` is decidable**, choice-free. -/
def decInSig : (d : ℕ) → (x : PLLFormula) → atomFree x = true → Decidable (InSig d x)
  | 0, x, hx => isTrue ⟨x, hx, Interd.refl x⟩
  | d + 1, x, hx =>
      have := decInterd (sig (tau x)) x
      have := decInSig d (tau x) (tau_af x hx)
      decidable_of_iff _ (inSig_succ_iff d hx).symm

theorem sigImageDec : Stmt.SigImageDec := fun d x hx => @Decidable.em _ (decInSig d x hx)

/-! ### (C6) Existence and uniqueness in F0 -/

theorem exists_last {P : ℕ → Prop} (dec : ∀ n, P n ∨ ¬ P n) (h0 : P 0) :
    ∀ N, ¬ P N → ∃ d, P d ∧ ¬ P (d + 1)
  | 0, hN => absurd h0 hN
  | N + 1, hN => (dec N).elim (fun h => ⟨N, h, hN⟩) (fun h => exists_last dec h0 N h)

theorem not_inSig_eventually {χ : PLLFormula} (hnd : ¬ Deriv [] χ) : ∃ N, ¬ InSig N χ := by
  obtain ⟨N, hN⟩ := InsideOut.orbit_order_limit .falsePLL χ rfl hnd
  exact ⟨N, fun ⟨y, hy, hi⟩ => hN N (Nat.le_refl N) (Deriv.cutHead (sigN_bot_le N y hy) hi.1)⟩

/-- **Every non-theorem is `σᵈ y` with `y ∈ L₀`.** -/
theorem exists_grade {χ : PLLFormula} (hχ : atomFree χ = true) (hnd : ¬ Deriv [] χ) :
    ∃ d y, InL0 y ∧ Interd (sigN d y) χ := by
  obtain ⟨N, hN⟩ := not_inSig_eventually hnd
  obtain ⟨d, ⟨z, hz, hzi⟩, hd⟩ := exists_last (fun n => sigImageDec n χ hχ)
    ⟨χ, hχ, Interd.refl χ⟩ N hN
  refine ⟨d, z, ⟨hz, fun ⟨w, hw, hwi⟩ => hd ⟨w, hw, ?_⟩⟩, hzi⟩
  exact (InsideOut.sigN_interd d (sig_vf hw) hz hwi).trans hzi

theorem grade_key {d d' : ℕ} {y y' : PLLFormula} (hy' : atomFree y' = true) (hs : InL0 y)
    (h : Interd (sigN d y) (sigN d' y')) : ¬ d < d' := by
  intro hlt
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hlt
  rw [show d + k + 1 = d + (k + 1) from rfl, ← sigN_sigN] at h
  have hi := InsideOut.interd_of_sigN d h
  rw [InsideOut.sigN_succ] at hi
  exact hs.2 ⟨sigN k y', sigN_vf k hy', hi.symm⟩

/-- **The grade and the `L₀` part are unique.** -/
theorem grade_unique {d d' : ℕ} {y y' : PLLFormula} (hy : InL0 y) (hy' : InL0 y')
    (h : Interd (sigN d y) (sigN d' y')) : d = d' ∧ Interd y y' := by
  have hdd : d = d' := by
    rcases Nat.lt_trichotomy d d' with hlt | heq | hgt
    · exact absurd hlt (grade_key hy'.1 hy h)
    · exact heq
    · exact absurd hgt (grade_key hy.1 hy' h.symm)
  subst hdd
  exact ⟨rfl, InsideOut.interd_of_sigN d h⟩

theorem thm_not_L0 {y : PLLFormula} (hy : InL0 y) (h : Deriv [] y) : False :=
  hy.2 ⟨truePLL, rfl, weaken h, weaken (Deriv.impIntro (Deriv.iden (.head _)))⟩

/-! ### (C6) In the colimit -/

theorem iter_shift : ∀ (n : ℕ) (x : Pre), iterP shiftP n x = ⟨x.st, sigN n x.fm, sigN_vf n x.af⟩
  | 0, _ => rfl
  | n + 1, x => iter_shift n (shiftP x)

theorem iter_unshift_st : ∀ (n : ℕ) (x : Pre), (iterP unshiftP n x).st = x.st + n
  | 0, _ => rfl
  | n + 1, x => by
      show (iterP unshiftP n (unshiftP x)).st = x.st + (n + 1)
      rw [iter_unshift_st n (unshiftP x)]
      show x.st + 1 + n = x.st + (n + 1)
      omega

theorem iter_unshift_fm : ∀ (n : ℕ) (x : Pre), (iterP unshiftP n x).fm = x.fm
  | 0, _ => rfl
  | n + 1, x => iter_unshift_fm n (unshiftP x)

theorem gradePow : Stmt.GradePow := by
  intro k y
  cases k with
  | ofNat n =>
      have e : powP (.ofNat n) (iota 0 y) = grP (.ofNat n) y := iter_shift n (iota 0 y)
      rw [e]
      exact rP_refl _
  | negSucc n =>
      refine rP_of_fm ?_ (iter_unshift_fm (n + 1) (iota 0 y))
      show (iterP unshiftP (n + 1) (iota 0 y)).st = n + 1
      rw [iter_unshift_st]
      show 0 + (n + 1) = n + 1
      omega

theorem gradeShift : Stmt.GradeShift := by
  intro k y
  cases k with
  | ofNat n => exact rP_of_fm rfl (InsideOut.sig_sigN n y.1)
  | negSucc n =>
      cases n with
      | zero =>
          rw [show Int.negSucc 0 + 1 = Int.ofNat 0 from rfl]
          exact shift_unshift (grP (.ofNat 0) y)
      | succ m =>
          rw [show Int.negSucc (m + 1) + 1 = Int.negSucc m from rfl]
          exact shift_unshift (grP (.negSucc m) y)

theorem gradeNotTop : Stmt.GradeNotTop := by
  intro k y hy h
  have ht := (topIff _).mp h
  cases k with
  | ofNat n => exact thm_not_L0 hy (sigN_reflects n y.1 ht)
  | negSucc n => exact thm_not_L0 hy ht

theorem gradeInj : Stmt.GradeInj := by
  intro k k' y y' hy hy' h
  cases k with
  | ofNat n =>
      cases k' with
      | ofNat n' =>
          obtain ⟨hn, hi⟩ := grade_unique hy hy' (⟨h.1, h.2⟩ : Interd (sigN n y.1) (sigN n' y'.1))
          exact ⟨congrArg Int.ofNat hn, hi⟩
      | negSucc n' =>
          exfalso
          have hi : Interd (sigN (n' + 1) (sigN n y.1)) y'.1 := ⟨h.1, h.2⟩
          rw [InsideOut.sigN_succ] at hi
          exact hy'.2 ⟨sigN n' (sigN n y.1), sigN_vf n' (sigN_vf n y.2), hi⟩
  | negSucc n =>
      cases k' with
      | ofNat n' =>
          exfalso
          have hi : Interd (sigN (n + 1) (sigN n' y'.1)) y.1 := ⟨h.2, h.1⟩
          rw [InsideOut.sigN_succ] at hi
          exact hy.2 ⟨sigN n (sigN n' y'.1), sigN_vf n (sigN_vf n' y'.2), hi⟩
      | negSucc n' =>
          obtain ⟨hn, hi⟩ :=
            grade_unique hy hy' (⟨h.1, h.2⟩ : Interd (sigN (n' + 1) y.1) (sigN (n + 1) y'.1))
          exact ⟨congrArg Int.negSucc (by omega), hi⟩

theorem gradeSurj : Stmt.GradeSurj := by
  intro x hx
  have hnd : ¬ Deriv [] x.fm := fun h => hx ((topIff x).mpr h)
  obtain ⟨d, z, hz, hzi⟩ := exists_grade x.af hnd
  rcases Nat.lt_or_ge d x.st with hlt | hge
  · refine ⟨.negSucc (x.st - d - 1), ⟨z, hz.1⟩, hz, ?_⟩
    refine (rP_iff_at (x := x) (y := grP (.negSucc (x.st - d - 1)) ⟨z, hz.1⟩) (k := 0) (j := d)
      ?_).mpr hzi.symm
    show x.st + 0 = (x.st - d - 1 + 1) + d
    omega
  · refine ⟨.ofNat (d - x.st), ⟨z, hz.1⟩, hz, ?_⟩
    refine (rP_iff_at (x := x) (y := grP (.ofNat (d - x.st)) ⟨z, hz.1⟩) (k := 0) (j := x.st)
      (by show x.st + 0 = 0 + x.st; omega)).mpr ?_
    show Interd (sigN 0 x.fm) (sigN x.st (sigN (d - x.st) z))
    rw [sigN_sigN, show x.st + (d - x.st) = d by omega]
    exact hzi.symm

/-! ### (C7) -/

theorem notUpset : Stmt.NotUpset :=
  ⟨Deriv.orIntro1 (Deriv.iden (.head _)), fun ⟨z, hz⟩ =>
    SigOnto.sig_not_onto ⟨z.1, z.2, hz.1, hz.2⟩⟩

theorem notDownset : Stmt.NotDownset :=
  ⟨cellBot.1, fun ⟨z, hz⟩ => nd_t3_bot (Deriv.cutHead (subBot_top t3 z.2) hz.1)⟩

theorem filterUnion : Stmt.FilterUnion :=
  ⟨fun x => ⟨x.st, coinitial x⟩, fun n x => unshift_iff (iota n botCF) x⟩

/-! ## The quotient

`Quot rP` with the order and the operations lifted; the laws are the
corollaries of the statements above. -/

theorem mk_eq_iff {x y : Pre} : mk x = mk y ↔ rP x y := by
  constructor
  · intro h
    have key : ∀ a b : Pre, rP a b → rP x a = rP x b := fun a b hab =>
      propext ⟨fun h1 => rP_trans h1 hab, fun h1 => rP_trans h1 (rP_symm hab)⟩
    have h3 : rP x x = rP x y := congrArg (Quot.lift (rP x) key) h
    exact cast h3 (rP_refl x)
  · exact Quot.sound

/-- The order on `SigCol`. -/
def leQ (X Y : SigCol) : Prop :=
  Quot.lift (fun x => Quot.lift (fun y => leP x y)
      (fun _ _ h => propext ⟨fun h1 => leP_trans h1 h.1, fun h1 => leP_trans h1 h.2⟩) Y)
    (fun x x' h => by
      induction Y using Quot.ind
      exact propext ⟨fun h1 => leP_trans h.2 h1, fun h1 => leP_trans h.1 h1⟩) X

def lift1 (f : Pre → Pre) (hf : ∀ {x y}, rP x y → rP (f x) (f y)) : SigCol → SigCol :=
  Quot.lift (fun x => mk (f x)) (fun _ _ h => Quot.sound (hf h))

def lift2 (f : Pre → Pre → Pre) (hf : ∀ {x x' y y'}, rP x x' → rP y y' → rP (f x y) (f x' y')) :
    SigCol → SigCol → SigCol := fun X Y =>
  Quot.lift (fun x => Quot.lift (fun y => mk (f x y)) (fun _ _ h => Quot.sound (hf (rP_refl x) h)) Y)
    (fun _ _ h => by
      induction Y using Quot.ind
      exact Quot.sound (hf h (rP_refl _))) X

def topQ : SigCol := mk topP
def meetQ : SigCol → SigCol → SigCol := lift2 meetP meet_compat
def joinQ : SigCol → SigCol → SigCol := lift2 joinP join_compat
def impQ : SigCol → SigCol → SigCol := lift2 impP imp_compat
def nucQ : SigCol → SigCol := lift1 nucP nuc_compat

/-- The operations of the colimit. -/
def opsQ : Ops SigCol := ⟨topQ, meetQ, joinQ, impQ, nucQ⟩

/-- `S` and `S⁻¹` on the colimit. -/
def shiftQ : SigCol → SigCol := lift1 shiftP shift_compat
def unshiftQ : SigCol → SigCol := lift1 unshiftP unshift_compat

/-- `ιₙ` into the colimit. -/
def iotaQ (n : ℕ) (φ : CF) : SigCol := mk (iota n φ)

/-- **(C1) on the quotient, PROVED: `SigCol` is a nuclear implicative lattice.** -/
theorem sigCol_nucImpLat : NucImpLat leQ opsQ where
  pre := {
    refl := by
      intro X
      induction X using Quot.ind
      exact c1.refl _
    trans := by
      intro X Y Z
      induction X using Quot.ind
      induction Y using Quot.ind
      induction Z using Quot.ind
      exact c1.trans
    le_top := by
      intro X
      induction X using Quot.ind
      exact c1.le_top _
    meet_le_left := by
      intro X Y
      induction X using Quot.ind
      induction Y using Quot.ind
      exact c1.meet_le_left _ _
    meet_le_right := by
      intro X Y
      induction X using Quot.ind
      induction Y using Quot.ind
      exact c1.meet_le_right _ _
    le_meet := by
      intro X Y Z
      induction X using Quot.ind
      induction Y using Quot.ind
      induction Z using Quot.ind
      exact c1.le_meet
    le_join_left := by
      intro X Y
      induction X using Quot.ind
      induction Y using Quot.ind
      exact c1.le_join_left _ _
    le_join_right := by
      intro X Y
      induction X using Quot.ind
      induction Y using Quot.ind
      exact c1.le_join_right _ _
    join_le := by
      intro X Y Z
      induction X using Quot.ind
      induction Y using Quot.ind
      induction Z using Quot.ind
      exact c1.join_le
    residuation := by
      intro X Y Z
      induction X using Quot.ind
      induction Y using Quot.ind
      induction Z using Quot.ind
      exact c1.residuation _ _ _
    nuc_infl := by
      intro X
      induction X using Quot.ind
      exact c1.nuc_infl _
    nuc_idem := by
      intro X
      induction X using Quot.ind
      exact c1.nuc_idem _
    nuc_mono := by
      intro X Y
      induction X using Quot.ind
      induction Y using Quot.ind
      exact c1.nuc_mono
    nuc_meet := by
      intro X Y
      induction X using Quot.ind
      induction Y using Quot.ind
      exact c1.nuc_meet _ _ }
  antisymm := by
    intro X Y
    induction X using Quot.ind
    induction Y using Quot.ind
    intro h1 h2
    exact Quot.sound ⟨h1, h2⟩

/-- The nucleus preserves binary meets (equality in the colimit). -/
theorem nucQ_meet (X Y : SigCol) : nucQ (meetQ X Y) = meetQ (nucQ X) (nucQ Y) := by
  induction X using Quot.ind
  induction Y using Quot.ind
  rename_i x y
  exact Quot.sound ⟨le_meetP (nucP_mono (meetP_le_left x y)) (nucP_mono (meetP_le_right x y)),
    nucP_meet x y⟩

/-- **(C2) on the quotient**: `ιₙ₊₁ ∘ σ = ιₙ`; `ιₙ` an order embedding. -/
theorem iotaQ_compat (n : ℕ) (φ : CF) : iotaQ (n + 1) (sigCF φ) = iotaQ n φ :=
  Quot.sound (stageCompat n φ)

theorem iotaQ_le_iff (n : ℕ) (φ ψ : CF) : leQ (iotaQ n φ) (iotaQ n ψ) ↔ Deriv [φ.1] ψ.1 :=
  stageEmb n φ ψ

theorem iotaQ_eq_iff (n : ℕ) (φ ψ : CF) : iotaQ n φ = iotaQ n ψ ↔ Interd φ.1 ψ.1 :=
  mk_eq_iff.trans (and_congr (stageEmb n φ ψ) (stageEmb n ψ φ))

/-- **(C3) on the quotient**: `S` is an automorphism extending `σ`, with
inverse the stage shift. -/
theorem shiftQ_iotaQ (n : ℕ) (φ : CF) : shiftQ (iotaQ n φ) = iotaQ n (sigCF φ) := rfl

theorem unshiftQ_iotaQ (n : ℕ) (φ : CF) : unshiftQ (iotaQ n φ) = iotaQ (n + 1) φ := rfl

theorem shiftQ_unshiftQ (X : SigCol) : shiftQ (unshiftQ X) = X := by
  induction X using Quot.ind
  exact Quot.sound (shift_unshift _)

theorem unshiftQ_shiftQ (X : SigCol) : unshiftQ (shiftQ X) = X := by
  induction X using Quot.ind
  exact Quot.sound (shift_unshift _)

theorem shiftQ_le_iff (X Y : SigCol) : leQ (shiftQ X) (shiftQ Y) ↔ leQ X Y := by
  induction X using Quot.ind
  induction Y using Quot.ind
  exact (shift_iff _ _).symm

theorem shiftQ_hom : HomRel Eq opsQ opsQ shiftQ := by
  refine ⟨Quot.sound shiftHom.1, fun X Y => ?_, fun X Y => ?_, fun X Y => ?_, fun X => ?_⟩
  · induction X using Quot.ind
    induction Y using Quot.ind
    exact Quot.sound (shiftHom.2.1 _ _)
  · induction X using Quot.ind
    induction Y using Quot.ind
    exact Quot.sound (shiftHom.2.2.1 _ _)
  · induction X using Quot.ind
    induction Y using Quot.ind
    exact Quot.sound (shiftHom.2.2.2.1 _ _)
  · induction X using Quot.ind
    exact Quot.sound (shiftHom.2.2.2.2 _)

/-- **(C4) on the quotient**: no least element; no lower bound of the stage
bottoms; the stage bottoms strictly decrease. -/
theorem no_least : ¬ ∃ B : SigCol, ∀ X, leQ B X := by
  rintro ⟨B, hB⟩
  induction B using Quot.ind
  rename_i b
  exact noLowerBound b (hB (iotaQ (b.st + 1) botCF))

theorem no_lower_bound : ¬ ∃ B : SigCol, ∀ n, leQ B (iotaQ n botCF) := by
  rintro ⟨B, hB⟩
  induction B using Quot.ind
  rename_i b
  exact noLowerBound b (hB (b.st + 1))

theorem iotaQ_bot_strict (n : ℕ) :
    leQ (iotaQ (n + 1) botCF) (iotaQ n botCF) ∧ iotaQ (n + 1) botCF ≠ iotaQ n botCF :=
  ⟨(botStrict n).1, fun h => (botStrict n).2 (mk_eq_iff.mp h).2⟩

/-- **(C5) on the quotient: `S X = X ↔ X = ⊤`.** -/
theorem shiftQ_fixed_iff (X : SigCol) : shiftQ X = X ↔ X = topQ := by
  induction X using Quot.ind
  rename_i x
  exact mk_eq_iff.trans ((fixedTop x).trans mk_eq_iff.symm)

/-- `Sᵏ`, `k ∈ ℤ`, on the colimit. -/
def iterQ (f : SigCol → SigCol) : ℕ → SigCol → SigCol
  | 0, X => X
  | n + 1, X => iterQ f n (f X)

def powQ : ℤ → SigCol → SigCol
  | .ofNat n => iterQ shiftQ n
  | .negSucc n => iterQ unshiftQ (n + 1)

theorem iterQ_mk (f : Pre → Pre) (hf : ∀ {x y}, rP x y → rP (f x) (f y)) :
    ∀ (n : ℕ) (x : Pre), iterQ (lift1 f hf) n (mk x) = mk (iterP f n x)
  | 0, _ => rfl
  | n + 1, x => iterQ_mk f hf n (f x)

theorem powQ_mk (k : ℤ) (x : Pre) : powQ k (mk x) = mk (powP k x) := by
  cases k with
  | ofNat n => exact iterQ_mk shiftP shift_compat n x
  | negSucc n => exact iterQ_mk unshiftP unshift_compat (n + 1) x

/-- **(C6) PROVED: every element other than `⊤` is `Sᵏ (ι₀ y)` with `y ∈ L₀`.** -/
theorem graded_exists (X : SigCol) (hX : X ≠ topQ) :
    ∃ k : ℤ, ∃ y : CF, InL0 y.1 ∧ X = powQ k (iotaQ 0 y) := by
  induction X using Quot.ind
  rename_i x
  obtain ⟨k, y, hy, h⟩ := gradeSurj x (fun h => hX (Quot.sound h))
  refine ⟨k, y, hy, ?_⟩
  show mk x = powQ k (mk (iota 0 y))
  rw [powQ_mk]
  exact Quot.sound (rP_trans h (rP_symm (gradePow k y)))

/-- **(C6) PROVED: the grade `k` and the `L₀` part `y` (up to `⊣⊢`) are unique.** -/
theorem graded_unique {k k' : ℤ} {y y' : CF} (hy : InL0 y.1) (hy' : InL0 y'.1)
    (h : powQ k (iotaQ 0 y) = powQ k' (iotaQ 0 y')) : k = k' ∧ Interd y.1 y'.1 := by
  have h1 : mk (powP k (iota 0 y)) = mk (powP k' (iota 0 y')) := by
    rw [← powQ_mk, ← powQ_mk]
    exact h
  exact gradeInj k k' y y' hy hy'
    (rP_trans (rP_symm (gradePow k y)) (rP_trans (mk_eq_iff.mp h1) (gradePow k' y')))

/-- `S` acts on the grade as `k ↦ k + 1`. -/
theorem shiftQ_powQ (k : ℤ) (y : CF) : shiftQ (powQ k (iotaQ 0 y)) = powQ (k + 1) (iotaQ 0 y) := by
  show shiftQ (powQ k (mk (iota 0 y))) = powQ (k + 1) (mk (iota 0 y))
  rw [powQ_mk, powQ_mk]
  exact Quot.sound (rP_trans (shift_compat (gradePow k y))
    (rP_trans (gradeShift k y) (rP_symm (gradePow (k + 1) y))))

/-- Graded elements are not `⊤`. -/
theorem graded_ne_top (k : ℤ) (y : CF) (hy : InL0 y.1) : powQ k (iotaQ 0 y) ≠ topQ := by
  intro h
  have h1 : mk (powP k (iota 0 y)) = mk topP := by
    rw [← powQ_mk]
    exact h
  exact gradeNotTop k y hy (rP_trans (rP_symm (gradePow k y)) (mk_eq_iff.mp h1))

/-! ### (C6) Validation: realised grades `1`, `0`, `−1` -/

/-- `⊥ ∈ L₀` (`σz ⊣⊢ ⊥` would give `t3 ⊢ σz ⊢ ⊥`). -/
theorem bot_L0 : InL0 .falsePLL :=
  ⟨rfl, fun ⟨_, hz, hi⟩ => nd_t3_bot (Deriv.cutHead (subBot_top t3 hz) hi.1)⟩

/-- `ι₀ t3 = S (ι₀ ⊥)`: grade `1`, `L₀` part `⊥`. -/
theorem grade_t3 : iotaQ 0 ⟨t3, rfl⟩ = powQ 1 (iotaQ 0 botCF) := rfl

/-- `ι₀ t5 = S⁰ (ι₀ t5)`: grade `0`, `L₀` part `t5` (`cellT5`). -/
theorem grade_t5 : iotaQ 0 t5CF = powQ 0 (iotaQ 0 t5CF) := rfl

/-- `ι₁ ⊥ = S⁻¹ (ι₀ ⊥)`: grade `−1`, `L₀` part `⊥`. -/
theorem grade_bot1 : iotaQ 1 botCF = powQ (-1) (iotaQ 0 botCF) := rfl

/-- The three grades are distinct, by uniqueness. -/
theorem grades_distinct :
    iotaQ 0 ⟨t3, rfl⟩ ≠ iotaQ 1 botCF ∧ iotaQ 0 ⟨t3, rfl⟩ ≠ iotaQ 0 botCF ∧
      iotaQ 1 botCF ≠ iotaQ 0 botCF := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [grade_t3, grade_bot1] at h
    exact absurd (graded_unique bot_L0 bot_L0 h).1 (by decide)
  · rw [grade_t3, show iotaQ 0 botCF = powQ 0 (iotaQ 0 botCF) from rfl] at h
    exact absurd (graded_unique bot_L0 bot_L0 h).1 (by decide)
  · rw [grade_bot1, show iotaQ 0 botCF = powQ 0 (iotaQ 0 botCF) from rfl] at h
    exact absurd (graded_unique bot_L0 bot_L0 h).1 (by decide)

/-- **(C7) on the quotient**: `ι₀(F0)` is not convex (`ι₀ ⊥ ≤ ι₁ t5 ≤ ι₀ ⊤`
with `ι₁ t5 ∉ ι₀(F0)`), so it is neither an up-set, an interval, nor a
principal filter. -/
theorem iota0_not_convex :
    leQ (iotaQ 0 botCF) (iotaQ 1 t5CF) ∧ leQ (iotaQ 1 t5CF) (iotaQ 0 topCF) ∧
      ¬ ∃ z : CF, iotaQ 0 z = iotaQ 1 t5CF :=
  ⟨notUpset.1, le_topP (iota 1 t5CF), fun ⟨z, hz⟩ => notUpset.2 ⟨z, mk_eq_iff.mp hz⟩⟩

/-- **(C7) on the quotient**: `ι₀(F0)` is not a down-set. -/
theorem iota0_not_downset :
    leQ (iotaQ 1 botCF) (iotaQ 0 botCF) ∧ ¬ ∃ z : CF, iotaQ 0 z = iotaQ 1 botCF :=
  ⟨notDownset.1, fun ⟨z, hz⟩ => notDownset.2 ⟨z, mk_eq_iff.mp hz⟩⟩

/-- **(C7) on the quotient**: the colimit is the union of the principal
filters `↑ιₙ ⊥`, and `S⁻¹` carries `↑ιₙ ⊥` onto `↑ιₙ₊₁ ⊥`. -/
theorem filter_union :
    (∀ X : SigCol, ∃ n, leQ (iotaQ n botCF) X) ∧
      ∀ n (X : SigCol), leQ (iotaQ n botCF) X ↔ leQ (iotaQ (n + 1) botCF) (unshiftQ X) := by
  refine ⟨fun X => ?_, fun n X => ?_⟩
  · induction X using Quot.ind
    rename_i x
    exact ⟨x.st, coinitial x⟩
  · induction X using Quot.ind
    exact filterUnion.2 n _

end SigmaColimit
end F0
end PLLND

/-! ## Axiom pins -/

#axioms_within PLLND.F0.SigmaColimit.cellBot [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.nd_oT3_oBot [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.cellShiftTop [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.cellT5 [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.gate_M1 [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.gate_M0 [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.ctrl_t3 [propext, Quot.sound]

-- stage 3: representatives
#axioms_within PLLND.F0.SigmaColimit.sigN_sigN [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.sigN_and [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.weaken [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.thm_top [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.deriv_sigN [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.leP_iff_at [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.rP_iff_at [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.leP_same [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.rP_of_fm [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.rP_of_thm [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.leP_refl [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.leP_trans [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.rP_refl [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.rP_symm [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.rP_trans [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.sigN_meetP [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.sigN_joinP [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.sigN_impP [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.le_topP [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.meetP_le_left [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.meetP_le_right [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.le_meetP [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.le_joinP_left [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.le_joinP_right [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.joinP_le [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.residP [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.nucP_infl [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.nucP_idem [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.nucP_mono [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.box_and [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.nucP_meet [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.c1 [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.meetP_mono [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.joinP_mono [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.impP_mono [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.meet_compat [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.join_compat [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.imp_compat [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.nuc_compat [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.shiftExtends [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.unshiftStage [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.shift_iff [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.shiftOrderIso [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.unshift_iff [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.unshiftOrderIso [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.shift_unshift [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.shiftInverse [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.shift_compat [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.unshift_compat [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.shiftHom [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.stageCompat [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.stageEmb [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.stageHom [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.cocone_iter [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.cocone_compat [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.liftU [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.universal [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.botStrict [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.noLowerBound [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.coinitial [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.noLeast [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.topIff [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.fixedTop [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.tau [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.bimp_of [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.of_bimp [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.force_nT [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.force_eT [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.orig_tau [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.tau_af [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.tau_sig [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.tau_mono [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.tau_interd [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.inSig1_iff [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.inSig_succ_iff [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.decDeriv [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.decInterd [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.decInSig [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.sigImageDec [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.exists_last [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.not_inSig_eventually [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.exists_grade [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.grade_key [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.grade_unique [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.thm_not_L0 [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.iter_shift [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.iter_unshift_st [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.iter_unshift_fm [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.gradePow [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.gradeShift [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.gradeNotTop [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.gradeInj [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.gradeSurj [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.notUpset [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.notDownset [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.filterUnion [propext, Quot.sound]

-- stage 3: the quotient
#axioms_within PLLND.F0.SigmaColimit.mk_eq_iff [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.leQ [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.opsQ [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.shiftQ [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.unshiftQ [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.powQ [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.sigCol_nucImpLat [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.nucQ_meet [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.iotaQ_compat [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.iotaQ_le_iff [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.iotaQ_eq_iff [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.shiftQ_iotaQ [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.unshiftQ_iotaQ [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.shiftQ_unshiftQ [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.unshiftQ_shiftQ [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.shiftQ_le_iff [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.shiftQ_hom [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.no_least [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.no_lower_bound [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.iotaQ_bot_strict [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.shiftQ_fixed_iff [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.iterQ_mk [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.powQ_mk [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.graded_exists [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.graded_unique [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.shiftQ_powQ [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.graded_ne_top [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.bot_L0 [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.grade_t3 [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.grade_t5 [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.grade_bot1 [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.grades_distinct [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.iota0_not_convex [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.iota0_not_downset [propext, Quot.sound]
#axioms_within PLLND.F0.SigmaColimit.filter_union [propext, Quot.sound]

/-! The pin gate watched failing: `graded_exists` does use `propext` and
`Quot.sound`, so the empty bound is rejected. -/

/--
error: 'PLLND.F0.SigmaColimit.graded_exists' depends on propext, Quot.sound, which the bound does not allow.
  declared: []
Locate the entry with:  #axiom_path propext PLLND.F0.SigmaColimit.graded_exists
-/
#guard_msgs in
#axioms_within PLLND.F0.SigmaColimit.graded_exists []
