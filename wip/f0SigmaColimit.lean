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
Rasiowa's *relatively pseudo-complemented lattice*, also called a
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

end SigmaColimit
end F0
end PLLND
