import wip.f0FreeBase3
import Meta.Audit

/-!
# Any family of reader cells over `σ³⊥`; the σ-shift of a free copy

Follow-up to `wip/f0FreeBase3.lean` (brief 2026-10-28).  There the readers of
the generators are the bottoms of the cells `ZL r`.  Here (Goal 1) the
readers are ANY pairwise separated `σ²⊥`-maximal cells, and (Goal 2) a free
copy above a variable-free base `b` is carried by `σᵏ` to a free copy above
`σᵏ b`.

## The statements (committed before any proof, METHOD.md §1)

Goal 1, the choice of reader family does not matter:

    AnyFamily3 :  ∀ n,  Distinct σ²⊥ (n + 1)  →  FreeHAnAbove σ³⊥ n

and the cleaner variant with the two killers inside the family:

    CellsKill n F :  (∀ i j ≤ n, i ≠ j → F i, F j separated) ∧
                     F 0 ⊮ ◯σ²⊥ ∧ F 1 ⊩ ◯σ²⊥            (at the σ²⊥-maximal worlds)
    FromCells3 :  ∀ n F,  CellsKill n F  →  FreeHAnAbove σ³⊥ n

Goal 2, the σ-shift (for variable-free `b`):

    SigShift  :  ∀ b vf, ∀ k n,  FreeHAnAbove b n  →  FreeHAnAbove (σᵏ b) n
    SigShiftω :  ∀ b vf, ∀ k,    FreeHAωAbove b    →  FreeHAωAbove (σᵏ b)
    AllAbove3  :  ∀ m ≥ 3, ∀ n,  FreeHAnAbove σᵐ⊥ n
    AllAbove3ω :  ∀ m ≥ 3,       FreeHAωAbove σᵐ⊥

Fragment first (CLAUDE.md rule 8): as in `f0FreeBase3`, the ◯-free
variable-free fragment is `{⊥, ⊤}`; degenerate.

Status note: `wip/f0FreeAnyFamily-STATUS.md`.
-/

open PLLFormula

namespace PLLND
namespace F0
namespace AnyFamily

open SemUI RNEmbed Sig FreeIPL FreeHAn Pair Base3
open PLLND.LaxInfinite (atomFree)
open SubframeModel.CF (FinDec)

/-! ## The statements -/

/-- **Goal 1**: any `n + 1` pairwise separated `σ²⊥`-maximal cells give a copy
of the free Heyting algebra on `n` generators in `[σ³⊥, ⊤]`. -/
def AnyFamily3 : Prop := ∀ n, Distinct (base 2) (n + 1) → FreeHAnAbove (base 3) n

/-- The hypothesis of the cleaner variant: the cells `F 0, …, F n` pairwise
separated, `F 0` refuting `◯σ²⊥` and `F 1` forcing it at its `σ²⊥`-maximal
world (the two killers; `F 2, …, F n` are the readers). -/
def CellsKill (n : Nat) (F : Nat → Cell (base 2)) : Prop :=
  (∀ i j, i ≤ n → j ≤ n → i ≠ j → (F i).Separated (F j)) ∧
  ¬ (F 0).M.force (F 0).w (.somehow (base 2)) ∧ (F 1).M.force (F 1).w (.somehow (base 2))

/-- **The cleaner variant of Goal 1.** -/
def FromCells3 : Prop := ∀ (n : Nat) (F : Nat → Cell (base 2)), CellsKill n F → FreeHAnAbove (base 3) n

/-- **Goal 2**: the σ-shift of a free copy on `n` generators. -/
def SigShift : Prop :=
  ∀ b : PLLFormula, atomFree b = true → ∀ k n, FreeHAnAbove b n → FreeHAnAbove (sigN k b) n

/-- **Goal 2, every variable a generator.** -/
def SigShiftω : Prop :=
  ∀ b : PLLFormula, atomFree b = true → ∀ k, FreeHAωAbove b → FreeHAωAbove (sigN k b)

/-- **The corollary**: every base `σᵐ⊥`, `m ≥ 3`, carries every finite free copy. -/
def AllAbove3 : Prop := ∀ m, 3 ≤ m → ∀ n, FreeHAnAbove (base m) n

/-- **The corollary, every variable a generator.** -/
def AllAbove3ω : Prop := ∀ m, 3 ≤ m → FreeHAωAbove (base m)

end AnyFamily
end F0
end PLLND
