import wip.f0FreeBase3
import Meta.Audit

/-!
# PLL embeds faithfully into its closed fragment (readers only, `◯` kept)

Follow-up to `wip/f0FreeBase3.lean` (2026-10-28; conjecture approved by
Matthew the same day).  There the generators `x₀ = ◯σ³⊥` and the readers
`x_{r+1} = gen (r+1)` freely generate the free Heyting algebra above
`σ³⊥ = base 3`, for ◯-free formulas.  Here `x₀` is dropped and only the
readers are used; the claim is that the relativisation is then faithful on
ALL formulas, `◯` included, with `◯ ↦ ◯`.

## The statement (committed before any proof, METHOD.md §1)

    y a = gen (code a + 1)                                         (`xr`)
    g = relB σ³⊥ y :  a ↦ y a,  ⊥ ↦ σ³⊥,  ∧ ∨ ↠ ◯ ↦ themselves

    FreeReaders :      ∀ A B,  [A] ⊢ B  ⟺  [relB σ³⊥ y A] ⊢ relB σ³⊥ y B

    FreePLLAbove b :   ∃ x, (∀ a, x a variable-free) ∧ (∀ a, [b] ⊢ x a) ∧
                          ∀ A B,  [A] ⊢ B  ⟺  [relB b x A] ⊢ relB b x B
    target:            FreePLLAbove (σ³⊥)

    FreePLLnAbove b n : the same with A, B over pvar 0, …, pvar (n-1)

Fragment first (CLAUDE.md rule 8): the ◯-free instance is

    FreeReadersIPC :   ∀ A B ◯-free,  [A] ⊢ B  ⟺  [relB σ³⊥ y A] ⊢ relB σ³⊥ y B

proved by the gadget of `f0FreeBase3` without `x₀` and with the `S` of the
copies arbitrary.

## Why `x₀` must go (pen, the manager)

`x₀` reads `S`-membership on the copy of `K`, and `◯` reads `S` too: in the
`x₀` gadget, `◯x₁` at `w_k` holds iff `k ⊩ p₀ ∨ p₁`, so the range is not
closed under `◯`.  Without `x₀` the copy keeps `K`'s own `S`.

## Refutation stage (CLAUDE.md rule 9: designed cells only)

The atoms with codes `0` and `1` are `""` and `"\x00"` (`a0`, `a1`), so that
`y a0 = gen 1`, `y a1 = gen 2` are small enough to evaluate in the kernel.

    O1 = ◯p → p,    O2 = ◯p ∨ ¬◯p,    O3 = ◯(p ∨ q) → ◯p ∨ ◯q

Status note: `wip/f0FreePLL-STATUS.md`.
-/

open PLLFormula

namespace PLLND
namespace F0
namespace FreePLL

open SemUI RNEmbed Sig FreeIPL FreeHAn Pair Base3
open PLLND.LaxInfinite (atomFree)
open SubframeModel.CF (FinDec)

/-! ## The statement -/

/-- **The readers**: `y a = gen (code a + 1)`.  The generator `x₀ = gen 0 = ◯σ³⊥`
of `f0FreeBase3` is not used. -/
def xr (a : String) : PLLFormula := gen (Base3.code a + 1)

/-- **`[b, ⊤]` contains a faithful copy of PLL**: a substitution of
variable-free formulas above `b` for the atoms, `b` for `⊥`, and `◯` for `◯`,
reflects and preserves derivability for ALL formulas. -/
def FreePLLAbove (b : PLLFormula) : Prop :=
  ∃ x : String → PLLFormula, (∀ a, atomFree (x a) = true) ∧ (∀ a, Deriv [b] (x a)) ∧
    ∀ A B : PLLFormula, (Deriv [A] B ↔ Deriv [relB b x A] (relB b x B))

/-- **The `n`-variable form**: formulas over `pvar 0, …, pvar (n-1)`. -/
def FreePLLnAbove (b : PLLFormula) (n : Nat) : Prop :=
  ∃ x : String → PLLFormula, (∀ a, atomFree (x a) = true) ∧ (∀ a, Deriv [b] (x a)) ∧
    ∀ A B : PLLFormula, varsBelow n A = true → varsBelow n B = true →
      (Deriv [A] B ↔ Deriv [relB b x A] (relB b x B))

/-- **FreeReaders**: the readers `xr` give a faithful copy of PLL above `σ³⊥`. -/
def FreeReaders : Prop :=
  ∀ A B : PLLFormula, Deriv [A] B ↔ Deriv [relB b3 xr A] (relB b3 xr B)

/-- **Stage A, the ◯-free fragment**: the readers alone, on ◯-free formulas. -/
def FreeReadersIPC : Prop :=
  ∀ A B : PLLFormula, boxFree A = true → boxFree B = true →
    (Deriv [A] B ↔ Deriv [relB b3 xr A] (relB b3 xr B))

/-! ## The designed cells (Stage B) -/

/-- The atom with code `0`. -/
def a0 : String := ""

/-- The atom with code `1`. -/
def a1 : String := "\x00"

/-- `p`, read by `gen 1`. -/
def pA : PLLFormula := .prop a0

/-- `q`, read by `gen 2`. -/
def qA : PLLFormula := .prop a1

/-- `O1 = ◯p → p`. -/
def O1 : PLLFormula := (PLLFormula.somehow pA).ifThen pA

/-- `O2 = ◯p ∨ ¬◯p`. -/
def O2 : PLLFormula := (PLLFormula.somehow pA).or (negF (PLLFormula.somehow pA))

/-- `O3 = ◯(p ∨ q) → ◯p ∨ ◯q`. -/
def O3 : PLLFormula :=
  (PLLFormula.somehow (pA.or qA)).ifThen ((PLLFormula.somehow pA).or (PLLFormula.somehow qA))

end FreePLL
end F0
end PLLND
