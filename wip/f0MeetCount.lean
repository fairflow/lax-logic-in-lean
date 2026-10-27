import wip.f0FreeHAn
import Meta.Audit

/-!
# The meet-only counting criterion

Matthew's statement (2026-10-27), on top of `wip/f0FreeHAn.lean`.  Let `Hₙ` be
the free Heyting algebra on `p0 … p(n-1)`, and let `f` act on the ◯-free
formulas in those variables with variable-free values such that

    (faithful)  A ⊣⊢ B  ⟺  f A ⊣⊢ f B
    (meet)      f (A ∧ B) ⊣⊢ f A ∧ f B.

Nothing is assumed about `∨`, `↠` or `⊥`.  With `a := f ⊥`,

    TypeBound a K  ⟹  2ⁿ ≤ K.

Proof: the `2ⁿ` signed conjunctions `d_ε = ⋀ᵢ pᵢ^εᵢ` (`¬p = p ↠ ⊥`) are pairwise
`⊥`-disjoint and none is `⊣⊢ ⊥`; `f` is monotone by (meet) + (faithful), so
`f d_ε ≥ a`, `f d_ε ∧ f d_ε' ⊣⊢ a` for `ε ≠ ε'`, and `f d_ε ≢ a`; hence
`⊬ f d_ε ↠ a`, completeness (`SubTab.complete`, choice-free) gives a finite model
with a world forcing `f d_ε` and refuting `a`, above it an `a`-maximal world
(descent, as `exists_rmax`); no `a`-maximal world forces two of the `f d_ε`
(it would force `a`), so the `2ⁿ` worlds are pairwise separated, and a
relational pigeonhole against `TypeBound` gives `2ⁿ ≤ K`.

## Statements (committed before any proof, METHOD.md §1)

* `MeetEmb n f`: `f` has variable-free values on the ◯-free formulas in
  `p0 … p(n-1)`, is faithful and preserves `∧` (both as `Interd`).
* `MeetCounting := ∀ n K f, MeetEmb n f → TypeBound (f ⊥) K → 2 ^ n ≤ K`.
* `NoMeetCopyH2 b := ¬ ∃ f, MeetEmb 2 f ∧ f ⊥ ⊣⊢ b` (for `b = ⊥`, `t3`).
* `NoFreeHA2AnyNeg`: for variable-free `x₀ x₁` and ANY `y₀ y₁` with
  `[x₀ ∧ y₀] ⊢ t3`, `[x₁ ∧ y₁] ⊢ t3`, some sign pattern `ε` has
  `⊢ (x₀^ε₁ ∧ x₁^ε₂) ↠ t3` where `x^false` is read as `y`.
* `MeetEmbH1 := MeetEmb 1 h₁`, the non-vacuity check (`freeIPL1`'s embedding).
* `typeBound_bot : TypeBound ⊥ 2`, `typeBound_t3 : TypeBound t3 3` restated from
  `f0FreeIPL`; `countingCriterion : CountingCriterion` as a corollary.

Status note: `wip/f0MeetCount-STATUS.md`.
-/

open PLLFormula

namespace PLLND
namespace F0
namespace MeetCount

open SemUI RNEmbed Sig FreeIPL FreeHAn
open PLLND.LaxInfinite (atomFree)
open SubframeModel.CF

/-! ## The signed conjunctions -/

/-- `ε` read on every index, `false` beyond `n`. -/
def padB (n : Nat) (ε : Fin n → Bool) (l : Nat) : Bool :=
  if h : l < n then ε ⟨l, h⟩ else false

/-- `⋀_{l < k} g l`, with `⊤ = ⊥ ↠ ⊥` as the empty conjunction. -/
def conjUpTo (g : Nat → PLLFormula) : Nat → PLLFormula
  | 0 => FreeIPL.topF
  | k + 1 => (conjUpTo g k).and (g k)

/-- **The signed conjunction** `d_ε = ⋀_{i < n} pᵢ^εᵢ`, `p^true = p`, `p^false = p ↠ ⊥`. -/
def signedConj (n : Nat) (ε : Fin n → Bool) : PLLFormula :=
  conjUpTo (fun l => sgnP (padB n ε l) (.prop (pvar l))) n

/-! ## The statements -/

/-- **A meet-embedding of `Hₙ`**: `f` acts on the ◯-free formulas in
`p0 … p(n-1)` with variable-free values,

    (faithful)  A ⊣⊢ B  ⟺  f A ⊣⊢ f B,
    (meet)      f (A ∧ B) ⊣⊢ f A ∧ f B.

Nothing about `∨`, `↠` or `⊥`. -/
structure MeetEmb (n : Nat) (f : PLLFormula → PLLFormula) : Prop where
  vf : ∀ A, boxFree A = true → varsBelow n A = true → atomFree (f A) = true
  faithful : ∀ A B, boxFree A = true → boxFree B = true →
    varsBelow n A = true → varsBelow n B = true → (Interd A B ↔ Interd (f A) (f B))
  meet : ∀ A B, boxFree A = true → boxFree B = true →
    varsBelow n A = true → varsBelow n B = true → Interd (f (A.and B)) ((f A).and (f B))

/-- **The meet counting criterion**: `MeetEmb n f → TypeBound (f ⊥) K → 2ⁿ ≤ K`. -/
def MeetCounting : Prop :=
  ∀ (n K : Nat) (f : PLLFormula → PLLFormula), MeetEmb n f → TypeBound (f .falsePLL) K → 2 ^ n ≤ K

/-- **No ∧-copy of `H₂` with bottom `b`**: `¬ ∃ f, MeetEmb 2 f ∧ f ⊥ ⊣⊢ b`. -/
def NoMeetCopyH2 (b : PLLFormula) : Prop :=
  ¬ ∃ f : PLLFormula → PLLFormula, MeetEmb 2 f ∧ Interd (f .falsePLL) b

/-- `x` for the sign `true`, the given `y` for the sign `false`. -/
def sgnY : Bool → PLLFormula → PLLFormula → PLLFormula
  | true, x, _ => x
  | false, _, y => y

/-- **`noFreeHA2` with any negation**: for variable-free `x₀ x₁` and any `y₀ y₁`
with `[x₀ ∧ y₀] ⊢ t3` and `[x₁ ∧ y₁] ⊢ t3`,

    ∃ ε,  ⊢ (x₀^ε₁ ∧ x₁^ε₂) ↠ t3,     x^true = x,  x^false = y. -/
def NoFreeHA2AnyNeg : Prop :=
  ∀ x₀ x₁ y₀ y₁ : PLLFormula, atomFree x₀ = true → atomFree x₁ = true →
    Deriv [x₀.and y₀] t3 → Deriv [x₁.and y₁] t3 →
    ∃ ε : Bool × Bool, Deriv [] (Rneg ((sgnY ε.1 x₀ y₀).and (sgnY ε.2 x₁ y₁)))

/-- Non-vacuity: `h₁ A = σ(A[p := ◯⊥])` of `freeIPL1` is a meet-embedding of `H₁`. -/
def MeetEmbH1 : Prop := MeetEmb 1 h1

end MeetCount
end F0
end PLLND
