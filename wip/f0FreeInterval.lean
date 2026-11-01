import wip.f0FreeBase3
import Meta.Audit

/-!
# Nested relativisation of the free Heyting algebra inside F0: interval copies

Follow-up to `wip/f0FreeBase3.lean` (campaign approved by Matthew 2026-11-01).
There `freeHAωAbove_base3 : FreeHAωAbove (base 3)` gives a copy of the free
Heyting algebra `H_ω` inside `[σ³⊥, ⊤]`, by `relB σ³⊥ xω`.  Here the copy is
relativised again, to a sub-interval `[rel(ξ), rel(ζ)]`, and the construction
is stated for ANY faithful interval copy, so that it applies to its own output.

## The statements (committed before any proof, METHOD.md §1)

The interval translation for `[a, b]` with generators `x : String → PLLFormula`:

    rel a b x ⊥ = a,   rel a b x p = x p,   ∧, ∨ componentwise,
    rel a b x (A → B) = (rel A ↠ rel B) ∧ b,   rel a b x (◯A) = ◯(rel A) ∧ b

(the `◯` clause is used only by the PLL statement `NestPLL`).

    FreeIn a b x :  (∀ p, [a] ⊢ x p) ∧ (∀ p, [x p] ⊢ b) ∧
                      ∀ A B ◯-free,  [A] ⊢ B  ⟺  [rel a b x A] ⊢ rel a b x B
    FreeHAωIn a b : ∃ x, (∀ p, x p variable-free) ∧ FreeIn a b x

Fresh variables: `Fresh ρ ξ ζ` says that `ρ : String → String` is injective and
no `ρ p` occurs in `ξ` or `ζ`.  The core generators are

    coreGen ξ ζ ρ p = (ρ p ∨ ξ) ∧ ζ,     nestGen a b x ξ ζ ρ p = rel a b x (coreGen ξ ζ ρ p).

    CoreLemma :   ξ, ζ ◯-free,  [ξ] ⊢ ζ,  [ζ] ⊬ ξ,  Fresh ρ ξ ζ   ⟹   FreeIn ξ ζ (coreGen ξ ζ ρ)
    Nest :        FreeIn a b x,  ξ, ζ ◯-free,  [ξ] ⊢ ζ,  [ζ] ⊬ ξ,  Fresh ρ ξ ζ
                    ⟹   FreeIn (rel a b x ξ) (rel a b x ζ) (nestGen a b x ξ ζ ρ)
    MainTheorem : a, b, x variable-free,  FreeIn a b x,  ξ, ζ ◯-free,  [ξ] ⊢ ζ,  [ζ] ⊬ ξ
                    ⟹   FreeHAωIn (rel a b x ξ) (rel a b x ζ)
    Bridge :      (∀ p, [b] ⊢ x p) ∧ (∀ A B ◯-free, [A] ⊢ B ⟺ [relB b x A] ⊢ relB b x B)
                    ⟹   FreeIn b ⊤ x
    Bridge3 :     FreeIn σ³⊥ ⊤ xω
    NestTwo :     depth two inside the base-3 copy (level one by `nestGen`, level two
                    by `MainTheorem`)

OPEN, not in scope (CLAUDE.md rule 8, the PLL stage): `NestPLL`, the same as `Nest`
for all formulas, `◯` included, with the `◯` clause of `rel`.

## Stage 2: the designed cells (all kernel-checked, pins `[propext, Quot.sound]`)

* (i) PASS: inside the base-3 copy, `ξ = p₀ ∧ p₁`, `ζ = p₁`:
  `[rel ⊤] ⊬ rel(p ∨ ¬p)` (`Cells.cell1_neg`, a 12-world table) and
  `[rel ⊤] ⊢ rel((p ∧ ¬p) → q)` (`Cells.cell1_pos`, a derivation).
* (ii) PASS: the interval `[rel₁ ⊥, rel₁ p]` nested in the level-one interval:
  `[rel₂ ⊤] ⊬ rel₂(p ∨ ¬p)` (`Cells.cell2_neg`, a 14-world table).
* (iii) FAIL, as designed: `ξ = ζ` gives `[rel ⊤] ⊢ rel ⊥` while `[⊤] ⊬ ⊥`,
  so `¬ FreeIn a a x` (`cell_diag`), and the core lemma without `[ζ] ⊬ ξ` is
  REFUTED (`not_coreNoStrict`).

Status note: `wip/f0FreeInterval-STATUS.md`.
-/

open PLLFormula

namespace PLLND
namespace F0
namespace Interval

open SemUI FreeHAn Base3
open Pair (negF)
open PLLND.LaxInfinite (atomFree)
open SubframeModel.CF (FinDec)

/-! ## The interval translation and the statements -/

/-- **The interval translation for `[a, b]`** with generators `x`:
`⊥ ↦ a`, `p ↦ x p`, `∧` and `∨` componentwise, `A → B ↦ (rel A ↠ rel B) ∧ b`,
`◯A ↦ ◯(rel A) ∧ b`. -/
def rel (a b : PLLFormula) (x : String → PLLFormula) : PLLFormula → PLLFormula
  | .prop p => x p
  | .falsePLL => a
  | .and A B => .and (rel a b x A) (rel a b x B)
  | .or A B => .or (rel a b x A) (rel a b x B)
  | .ifThen A B => .and (.ifThen (rel a b x A) (rel a b x B)) b
  | .somehow A => .and (.somehow (rel a b x A)) b

/-- `⊤ = ⊥ ↠ ⊥`. -/
abbrev topF : PLLFormula := FreeIPL.topF

/-- **A faithful interval copy of `H_ω` in `[a, b]`**: the generators lie in
`[a, b]`, and the interval translation reflects and preserves derivability of
◯-free sequents,

    (∀ p, [a] ⊢ x p) ∧ (∀ p, [x p] ⊢ b) ∧
      ∀ A B ◯-free,  [A] ⊢ B  ⟺  [rel a b x A] ⊢ rel a b x B. -/
def FreeIn (a b : PLLFormula) (x : String → PLLFormula) : Prop :=
  (∀ p, Deriv [a] (x p)) ∧ (∀ p, Deriv [x p] b) ∧
    ∀ A B : PLLFormula, boxFree A = true → boxFree B = true →
      (Deriv [A] B ↔ Deriv [rel a b x A] (rel a b x B))

/-- **`[a, b]` contains a copy of `H_ω` inside F0**: a faithful interval copy
with variable-free generators. -/
def FreeHAωIn (a b : PLLFormula) : Prop :=
  ∃ x : String → PLLFormula, (∀ p, atomFree (x p) = true) ∧ FreeIn a b x

/-- The atom `c` occurs in the formula. -/
def occ (c : String) : PLLFormula → Bool
  | .prop a => decide (a = c)
  | .falsePLL => false
  | .and A B => occ c A || occ c B
  | .or A B => occ c A || occ c B
  | .ifThen A B => occ c A || occ c B
  | .somehow A => occ c A

/-- **A fresh renaming for `ξ`, `ζ`**: injective, and no image occurs in `ξ` or
`ζ`. -/
def Fresh (ρ : String → String) (ξ ζ : PLLFormula) : Prop :=
  (∀ p q, ρ p = ρ q → p = q) ∧ ∀ p, occ (ρ p) ξ = false ∧ occ (ρ p) ζ = false

/-- **The core generators** `coreGen ξ ζ ρ p = (ρ p ∨ ξ) ∧ ζ`. -/
def coreGen (ξ ζ : PLLFormula) (ρ : String → String) (p : String) : PLLFormula :=
  ((PLLFormula.prop (ρ p)).or ξ).and ζ

/-- **The nested generators**: the core generators of `[ξ, ζ]` carried into
the copy `rel a b x`. -/
def nestGen (a b : PLLFormula) (x : String → PLLFormula) (ξ ζ : PLLFormula)
    (ρ : String → String) (p : String) : PLLFormula :=
  rel a b x (coreGen ξ ζ ρ p)

/-- **The core lemma (★)**: for ◯-free `ξ`, `ζ` with `[ξ] ⊢ ζ` and `[ζ] ⊬ ξ`
and a fresh renaming `ρ`, the generators `(ρ p ∨ ξ) ∧ ζ` give a faithful copy
of `H_ω` in `[ξ, ζ]`. -/
def CoreLemma : Prop :=
  ∀ (ξ ζ : PLLFormula) (ρ : String → String), boxFree ξ = true → boxFree ζ = true →
    Deriv [ξ] ζ → ¬ Deriv [ζ] ξ → Fresh ρ ξ ζ → FreeIn ξ ζ (coreGen ξ ζ ρ)

/-- **Transport and nesting, explicit generators**: a faithful interval copy
carries the core copy of `[ξ, ζ]` to a faithful copy in `[rel ξ, rel ζ]`. -/
def Nest : Prop :=
  ∀ (a b : PLLFormula) (x : String → PLLFormula) (ξ ζ : PLLFormula) (ρ : String → String),
    FreeIn a b x → boxFree ξ = true → boxFree ζ = true →
    Deriv [ξ] ζ → ¬ Deriv [ζ] ξ → Fresh ρ ξ ζ →
    FreeIn (rel a b x ξ) (rel a b x ζ) (nestGen a b x ξ ζ ρ)

/-- **The main theorem**: inside F0, every faithful interval copy with
variable-free data contains a copy of `H_ω` in each strict sub-interval
`[rel ξ, rel ζ]`, ◯-free `ξ`, `ζ`. -/
def MainTheorem : Prop :=
  ∀ (a b : PLLFormula) (x : String → PLLFormula) (ξ ζ : PLLFormula),
    atomFree a = true → atomFree b = true → (∀ p, atomFree (x p) = true) → FreeIn a b x →
    boxFree ξ = true → boxFree ζ = true → Deriv [ξ] ζ → ¬ Deriv [ζ] ξ →
    FreeHAωIn (rel a b x ξ) (rel a b x ζ)

/-- **The bridge**: a faithful copy above a base `b` (the form of
`FreeHAωAbove`) is a faithful interval copy in `[b, ⊤]`. -/
def Bridge : Prop :=
  ∀ (b : PLLFormula) (x : String → PLLFormula), (∀ p, Deriv [b] (x p)) →
    (∀ A B : PLLFormula, boxFree A = true → boxFree B = true →
      (Deriv [A] B ↔ Deriv [relB b x A] (relB b x B))) →
    FreeIn b topF x

/-- **The base-3 copy as an interval copy**: `FreeIn σ³⊥ ⊤ xω`. -/
def Bridge3 : Prop := FreeIn (base 3) topF xω

/-- **Depth-two nesting inside the base-3 copy**: level one `[rel ξ₁, rel ζ₁]`
with the nested generators, level two `[rel₁ ξ₂, rel₁ ζ₂]` inside it. -/
def NestTwo : Prop :=
  ∀ (ξ₁ ζ₁ ξ₂ ζ₂ : PLLFormula) (ρ₁ : String → String),
    boxFree ξ₁ = true → boxFree ζ₁ = true → Deriv [ξ₁] ζ₁ → ¬ Deriv [ζ₁] ξ₁ → Fresh ρ₁ ξ₁ ζ₁ →
    boxFree ξ₂ = true → boxFree ζ₂ = true → Deriv [ξ₂] ζ₂ → ¬ Deriv [ζ₂] ξ₂ →
    FreeHAωIn
      (rel (rel (base 3) topF xω ξ₁) (rel (base 3) topF xω ζ₁) (nestGen (base 3) topF xω ξ₁ ζ₁ ρ₁) ξ₂)
      (rel (rel (base 3) topF xω ξ₁) (rel (base 3) topF xω ζ₁) (nestGen (base 3) topF xω ξ₁ ζ₁ ρ₁) ζ₂)

/-! ## The PLL statement (OPEN, not in scope) -/

/-- A faithful interval copy of PLL in `[a, b]`, `◯ ↦ ◯(·) ∧ b`, all formulas. -/
def FreeInPLL (a b : PLLFormula) (x : String → PLLFormula) : Prop :=
  (∀ p, Deriv [a] (x p)) ∧ (∀ p, Deriv [x p] b) ∧
    ∀ A B : PLLFormula, (Deriv [A] B ↔ Deriv [rel a b x A] (rel a b x B))

/-- **OPEN**: `Nest` for PLL, `◯` included. -/
def NestPLL : Prop :=
  ∀ (a b : PLLFormula) (x : String → PLLFormula) (ξ ζ : PLLFormula) (ρ : String → String),
    FreeInPLL a b x → boxFree ξ = true → boxFree ζ = true →
    Deriv [ξ] ζ → ¬ Deriv [ζ] ξ → Fresh ρ ξ ζ →
    FreeInPLL (rel a b x ξ) (rel a b x ζ) (nestGen a b x ξ ζ ρ)

/-! ## Stage 2: the designed cells (refutation stage, CLAUDE.md rules 7 and 9)

Three designed cells, read off the pen argument, each kernel-checked.

* (i) The generator case inside the base-3 copy: `ξ = p₀ ∧ p₁`, `ζ = p₁` with
  `p₀ = ""`, `p₁ = "\x00"` (codes `0`, `1`, read by `gen 0`, `gen 1`).  The
  renaming `ρc1` sends `""` to `"\x01"` (code `2`, read by `gen 2`) and `"\x00"`
  to `"\x02"` (code `3`).  With `p = ""`, the IPC non-theorem `p ∨ ¬p` stays
  underivable, `[rel ⊤] ⊬ rel(p ∨ ¬p)` (`cell1_neg`), and the IPC theorem
  `(p ∧ ¬p) → q`, `q = "\x00"`, transfers (`cell1_pos`; it uses the lower bound
  `[rel ξ] ⊢ x q`, `bound1`).
* (ii) An interval nested inside that interval: `ξ₂ = ⊥`, `ζ₂ = p` with
  `p = ""`, renaming `ρc2` (`"" ↦ "\x00"`), so the level-two generator is read
  by `gen 3`; `p ∨ ¬p` stays underivable at level two (`cell2_neg`).
* (iii) The negative test `ξ = ζ`: every translation `rel a a x` sends `⊤` and
  `⊥` to interderivable formulas, `[rel ⊤] ⊢ rel ⊥` (`rel_top_bot_diag`), while
  `[⊤] ⊬ ⊥`; so `FreeIn a a x` FAILS for every `a`, `x` (`cell_diag`), the core
  lemma without `[ζ] ⊬ ξ` is REFUTED (`not_coreNoStrict`), and so is its
  base-3 instance `ξ = ζ = p₀ ∧ p₁` (`cell3_base3`).

The countermodels of (i) and (ii) are the pen proof's gluing, then the base-3
gadget of `f0FreeBase3`, as tables (`gadW R rd K`): the upper worlds
`e₀ n₀ L₀ … L_R f m₀ … m_R kn` of the gadget, readers `m_r` for the atoms `rd`
of codes `1 … R`, and one copy `2R + 6 + k` of each world `k` of the IPC
countermodel `K`, in `S` iff `k ⊮ ""`, seeing `m_r` and its cone iff `k`
refutes the atom of code `r`.  `K1`, `K2` are the IPC countermodels obtained by
the gluing of the pen argument (`p ∨ ¬p` refuted on a two-world chain, glued
once for (i), twice for (ii)).  The generators read the valuation at the copies
(`reads_K1`, `reads_K2`).  The table of (i) does not refute the transferred
theorem (`gate_watch`, the check watched failing). -/

section Cells

set_option maxRecDepth 100000

theorem size_empty : ("" : String).utf8ByteSize = 0 := by decide

theorem size_x00 : ("\x00" : String).utf8ByteSize = 1 := by decide

theorem size_x01 : ("\x01" : String).utf8ByteSize = 1 := by decide

theorem size_x02 : ("\x02" : String).utf8ByteSize = 1 := by decide

/-- `pvar` is injective (by the UTF-8 size, choice-free). -/
theorem pvar_inj {i j : Nat} (h : pvar i = pvar j) : i = j := by
  have h1 := congrArg String.utf8ByteSize h
  rw [utf8ByteSize_pvar, utf8ByteSize_pvar] at h1
  exact Nat.succ.inj h1

/-- `pvar (1 + c)` has at least two bytes. -/
theorem pvar_ne_of_size {s : String} (hs : s.utf8ByteSize ≤ 1) (c : Nat) : pvar (1 + c) ≠ s := by
  intro h
  have h1 := congrArg String.utf8ByteSize h
  rw [utf8ByteSize_pvar] at h1
  rw [← h1] at hs
  exact Nat.not_succ_le_self 1 (Nat.le_trans (Nat.succ_le_succ (Nat.le_add_right 1 c)) hs)

namespace Cells

/-- The level-one cell renaming: `"" ↦ "\x01"`, `"\x00" ↦ "\x02"`, otherwise
`p ↦ pvar (1 + code p)`. -/
def ρc1 (p : String) : String :=
  if Base3.code p = 0 then "\x01" else if Base3.code p = 1 then "\x02" else pvar (1 + Base3.code p)

/-- The level-two cell renaming: `"" ↦ "\x00"`, otherwise `p ↦ pvar (1 + code p)`. -/
def ρc2 (p : String) : String :=
  if Base3.code p = 0 then "\x00" else pvar (1 + Base3.code p)

theorem ρc1_ne_empty (p : String) : ρc1 p ≠ "" := by
  unfold ρc1
  split
  · decide
  · split
    · decide
    · exact pvar_ne_of_size (by rw [size_empty]; exact Nat.zero_le 1) _

theorem ρc1_ne_x00 (p : String) : ρc1 p ≠ "\x00" := by
  unfold ρc1
  split
  · decide
  · split
    · decide
    · exact pvar_ne_of_size (Nat.le_of_eq size_x00) _

theorem ρc1_inj {p q : String} (h : ρc1 p = ρc1 q) : p = q := by
  apply Base3.code_inj
  unfold ρc1 at h
  rcases Decidable.em (Base3.code p = 0) with hp0 | hp0
  · rw [if_pos hp0] at h
    rcases Decidable.em (Base3.code q = 0) with hq0 | hq0
    · rw [hp0, hq0]
    · rw [if_neg hq0] at h
      rcases Decidable.em (Base3.code q = 1) with hq1 | hq1
      · rw [if_pos hq1] at h
        exact absurd h (by decide)
      · rw [if_neg hq1] at h
        exact absurd h.symm (pvar_ne_of_size (Nat.le_of_eq size_x01) _)
  · rw [if_neg hp0] at h
    rcases Decidable.em (Base3.code p = 1) with hp1 | hp1
    · rw [if_pos hp1] at h
      rcases Decidable.em (Base3.code q = 0) with hq0 | hq0
      · rw [if_pos hq0] at h
        exact absurd h (by decide)
      · rw [if_neg hq0] at h
        rcases Decidable.em (Base3.code q = 1) with hq1 | hq1
        · rw [hp1, hq1]
        · rw [if_neg hq1] at h
          exact absurd h.symm (pvar_ne_of_size (Nat.le_of_eq size_x02) _)
    · rw [if_neg hp1] at h
      rcases Decidable.em (Base3.code q = 0) with hq0 | hq0
      · rw [if_pos hq0] at h
        exact absurd h (pvar_ne_of_size (Nat.le_of_eq size_x01) _)
      · rw [if_neg hq0] at h
        rcases Decidable.em (Base3.code q = 1) with hq1 | hq1
        · rw [if_pos hq1] at h
          exact absurd h (pvar_ne_of_size (Nat.le_of_eq size_x02) _)
        · rw [if_neg hq1] at h
          exact Nat.add_left_cancel (pvar_inj h)

theorem ρc2_ne_empty (p : String) : ρc2 p ≠ "" := by
  unfold ρc2
  split
  · decide
  · exact pvar_ne_of_size (by rw [size_empty]; exact Nat.zero_le 1) _

theorem ρc2_inj {p q : String} (h : ρc2 p = ρc2 q) : p = q := by
  apply Base3.code_inj
  unfold ρc2 at h
  rcases Decidable.em (Base3.code p = 0) with hp0 | hp0
  · rw [if_pos hp0] at h
    rcases Decidable.em (Base3.code q = 0) with hq0 | hq0
    · rw [hp0, hq0]
    · rw [if_neg hq0] at h
      exact absurd h.symm (pvar_ne_of_size (Nat.le_of_eq size_x00) _)
  · rw [if_neg hp0] at h
    rcases Decidable.em (Base3.code q = 0) with hq0 | hq0
    · rw [if_pos hq0] at h
      exact absurd h (pvar_ne_of_size (Nat.le_of_eq size_x00) _)
    · rw [if_neg hq0] at h
      exact Nat.add_left_cancel (pvar_inj h)

/-- Level one: `ξ = p₀ ∧ p₁`, `p₀ = ""`, `p₁ = "\x00"`. -/
def ξc : PLLFormula := (PLLFormula.prop "").and (PLLFormula.prop "\x00")

/-- Level one: `ζ = p₁`. -/
def ζc : PLLFormula := PLLFormula.prop "\x00"

/-- **`ρc1` is fresh for `ξ = p₀ ∧ p₁`, `ζ = p₁`.** -/
theorem fresh_c1 : Fresh ρc1 ξc ζc :=
  ⟨fun _ _ h => ρc1_inj h, fun p => ⟨by
    show (decide ("" = ρc1 p) || decide ("\x00" = ρc1 p)) = false
    rw [decide_eq_false (fun h => ρc1_ne_empty p h.symm),
      decide_eq_false (fun h => ρc1_ne_x00 p h.symm)]
    rfl, by
    show decide ("\x00" = ρc1 p) = false
    exact decide_eq_false (fun h => ρc1_ne_x00 p h.symm)⟩⟩

/-- **`ρc2` is fresh for `ξ₂ = ⊥`, `ζ₂ = p`.** -/
theorem fresh_c2 : Fresh ρc2 .falsePLL (.prop "") :=
  ⟨fun _ _ h => ρc2_inj h, fun p => ⟨rfl, by
    show decide ("" = ρc2 p) = false
    exact decide_eq_false (fun h => ρc2_ne_empty p h.symm)⟩⟩

/-- The hypotheses of level one: `[p₀ ∧ p₁] ⊢ p₁`. -/
theorem hyp1_le : Deriv [ξc] ζc := Deriv.andElim2 (Deriv.iden (.head _))

theorem hyp1_strict_imp : ¬ Deriv [] (ζc.ifThen ξc) :=
  SubTab.no.verdict (ζc.ifThen ξc)
    { n := 1, root := 0, le := [[true]], S := [false], val := [["\x00"]] }

/-- `[p₁] ⊬ p₀ ∧ p₁` (one world). -/
theorem hyp1_strict : ¬ Deriv [ζc] ξc := fun h => hyp1_strict_imp (Deriv.impIntro h)

/-- The hypotheses of level two: `[⊥] ⊢ p`. -/
theorem hyp2_le : Deriv [.falsePLL] (.prop "") := Deriv.falsoElim _ (Deriv.iden (.head _))

theorem hyp2_strict_imp : ¬ Deriv [] ((PLLFormula.prop "").ifThen .falsePLL) :=
  SubTab.no.verdict ((PLLFormula.prop "").ifThen .falsePLL)
    { n := 1, root := 0, le := [[true]], S := [false], val := [[""]] }

/-- `[p] ⊬ ⊥` (one world). -/
theorem hyp2_strict : ¬ Deriv [.prop ""] .falsePLL := fun h => hyp2_strict_imp (Deriv.impIntro h)

/-- Level one, `a₁ = rel σ³⊥ ⊤ xω (p₀ ∧ p₁)`. -/
def a1F : PLLFormula := rel (base 3) topF xω ξc

/-- Level one, `b₁ = rel σ³⊥ ⊤ xω p₁`. -/
def b1F : PLLFormula := rel (base 3) topF xω ζc

/-- Level one, the nested generators `x₁ = nestGen σ³⊥ ⊤ xω ξ ζ ρc1`. -/
def x1 : String → PLLFormula := nestGen (base 3) topF xω ξc ζc ρc1

/-- Level two, `a₂ = rel a₁ b₁ x₁ ⊥`. -/
def a2F : PLLFormula := rel a1F b1F x1 .falsePLL

/-- Level two, `b₂ = rel a₁ b₁ x₁ p`. -/
def b2F : PLLFormula := rel a1F b1F x1 (.prop "")

/-- Level two, `x₂ = nestGen a₁ b₁ x₁ ⊥ p ρc2`. -/
def x2 : String → PLLFormula := nestGen a1F b1F x1 .falsePLL (.prop "") ρc2

/-- `p = ""`. -/
def pF : PLLFormula := PLLFormula.prop ""

/-- `q = "\x00"`. -/
def qF : PLLFormula := PLLFormula.prop "\x00"

/-- `p ∨ ¬p`. -/
def lemF : PLLFormula := pF.or (negF pF)

/-- `(p ∧ ¬p) → q`. -/
def exfF : PLLFormula := (pF.and (negF pF)).ifThen qF

/-- The order on the upper worlds of the gadget with readers `m₁ … m_R`:
`0 = e₀`, `1 = n₀`, `2 + j = L_j` (`j ≤ R`), `R + 3 = f`, `R + 4 + r = m_r`
(`r ≤ R`), `2R + 5 = kn`; `i` sees `j`. -/
def upSee (R i j : Nat) : Bool :=
  if i = j then true
  else if j = 0 then decide (2 ≤ i)
  else if j = 1 then decide (3 ≤ i)
  else if j ≤ R + 2 then
    (decide (i ≤ R + 2) && decide (j + 2 ≤ i)) ||
    (decide (R + 4 ≤ i) && decide (i ≤ 2 * R + 4) && decide (j - 2 ≤ i - (R + 4))) ||
    (decide (i = 2 * R + 5) && decide (j = 2))
  else if j = R + 3 then decide (R + 4 ≤ i)
  else false

/-- `S` on the upper worlds: all but `e₀`, `f`, `kn`. -/
def upSS (R i : Nat) : Bool := !(decide (i = 0) || decide (i = R + 3) || decide (i = 2 * R + 5))

/-- The atom of code `r` (`1 ≤ r ≤ R`) in the reader list. -/
def rdS (rd : List String) (r : Nat) : String := rd.getD (r - 1) ""

/-- The copy of `k` sees `e₀ n₀ L₀ f m₀ kn` always, `m_r` iff `k` refutes the
atom of code `r`, `L_j` iff it sees some `m_r`, `r ≥ j`. -/
def copySee (R : Nat) (rd : List String) (K : SubTab.SubCM) (k j : Nat) : Bool :=
  if j = 0 ∨ j = 1 ∨ j = 2 ∨ j = R + 3 ∨ j = R + 4 ∨ j = 2 * R + 5 then true
  else if R + 4 < j ∧ j ≤ 2 * R + 4 then !(K.vB (rdS rd (j - (R + 4))) k)
  else if 2 < j ∧ j ≤ R + 2 then
    (List.range (R + 1)).any fun r => decide (j - 2 ≤ r) && decide (1 ≤ r) && !(K.vB (rdS rd r) k)
  else false

/-- **The base-3 gadget over a table `K`**, readers `m₁ … m_R` for the atoms
`rd`, the copies `2R + 6 + k` in `S` iff `k ⊮ ""`. -/
def gadW (R : Nat) (rd : List String) (K : SubTab.SubCM) : SubTab.SubCM :=
  { n := 2 * R + 6 + K.n, root := 2 * R + 6 + K.root,
    le := (List.range (2 * R + 6)).map (fun i =>
        (List.range (2 * R + 6)).map (upSee R i) ++ List.replicate K.n false) ++
      (List.range K.n).map fun k =>
        (List.range (2 * R + 6)).map (copySee R rd K k) ++ (List.range K.n).map fun l => K.leB k l,
    S := (List.range (2 * R + 6)).map (upSS R) ++ (List.range K.n).map fun k => !(K.vB "" k),
    val := List.replicate (2 * R + 6 + K.n) [] }

/-- The generators `gen r`, `r ≤ R`, read the valuation at every copy. -/
def readsW (R : Nat) (rd : List String) (K : SubTab.SubCM) : Bool :=
  (List.range K.n).all fun k => (List.range (R + 1)).all fun r =>
    (gadW R rd K).forceB (2 * R + 6 + k) (gen r) == K.vB (if r = 0 then "" else rdS rd r) k

/-- The IPC countermodel of (i), by the gluing: a two-world chain,
`p₁` everywhere, the fresh atom `"\x01"` at the top. -/
def K1 : SubTab.SubCM :=
  { n := 2, root := 0, le := [[true, true], [false, true]], S := [false, false],
    val := [["\x00"], ["\x00", "\x01"]] }

/-- The IPC countermodel of (ii), by the gluing twice: a two-world chain,
`"\x00"`, `"\x01"` everywhere, `"\x02"` at the top. -/
def K2 : SubTab.SubCM :=
  { n := 2, root := 0, le := [[true, true], [false, true]], S := [false, false],
    val := [["\x00", "\x01"], ["\x00", "\x01", "\x02"]] }

theorem reads_K1 : readsW 2 ["\x00", "\x01"] K1 = true := by decide +kernel

theorem reads_K2 : readsW 3 ["\x00", "\x01", "\x02"] K2 = true := by decide +kernel

/-- Cell (i), the implication form: `⊬ rel ⊤ ↠ rel(p ∨ ¬p)` (12 worlds). -/
theorem cell1 : ¬ Deriv [] ((rel a1F b1F x1 topF).ifThen (rel a1F b1F x1 lemF)) :=
  SubTab.no.verdict _ (gadW 2 ["\x00", "\x01"] K1)

/-- Cell (ii), the implication form: `⊬ rel₂ ⊤ ↠ rel₂(p ∨ ¬p)` (14 worlds). -/
theorem cell2 : ¬ Deriv [] ((rel a2F b2F x2 topF).ifThen (rel a2F b2F x2 lemF)) :=
  SubTab.no.verdict _ (gadW 3 ["\x00", "\x01", "\x02"] K2)

/-- IPC: `[⊤] ⊬ p ∨ ¬p` (a two-world chain). -/
theorem ipc_lem_imp : ¬ Deriv [] (topF.ifThen lemF) :=
  SubTab.no.verdict (topF.ifThen lemF)
    { n := 2, root := 0, le := [[true, true], [false, true]], S := [false, false], val := [[], [""]] }

theorem ipc_lem : ¬ Deriv [topF] lemF := fun h => ipc_lem_imp (Deriv.impIntro h)

/-- **Cell (i) PASSES, the non-theorem**: `[rel ⊤] ⊬ rel(p ∨ ¬p)` in the
level-one interval inside the base-3 copy. -/
theorem cell1_neg : ¬ Deriv [rel a1F b1F x1 topF] (rel a1F b1F x1 lemF) := fun h =>
  cell1 (Deriv.impIntro h)

/-- IPC: `[⊤] ⊢ (p ∧ ¬p) → q`. -/
theorem ipc_exf : Deriv [topF] exfF :=
  Deriv.impIntro (Deriv.falsoElim _ (Deriv.impElim (Deriv.andElim2 (Deriv.iden (.head _)))
    (Deriv.andElim1 (Deriv.iden (.head _)))))

/-- The lower bound at level one: `[a₁] ⊢ x₁ q`. -/
theorem bound1 (q : String) : Deriv [a1F] (x1 q) :=
  Deriv.andIntro (Deriv.orIntro2 (Deriv.iden (.head _))) (Deriv.andElim2 (Deriv.iden (.head _)))

/-- **Cell (i) PASSES, the theorem**: `[rel ⊤] ⊢ rel((p ∧ ¬p) → q)`. -/
theorem cell1_pos : Deriv [rel a1F b1F x1 topF] (rel a1F b1F x1 exfF) :=
  Deriv.andIntro
    (Deriv.impIntro (Deriv.cutHead
      (Deriv.impElim (Deriv.andElim1 (Deriv.andElim2 (Deriv.iden (.head _))))
        (Deriv.andElim1 (Deriv.iden (.head _))))
      (bound1 "\x00")))
    (Deriv.andElim2 (Deriv.iden (.head _)))

/-- The check watched failing: the table of cell (i) does not refute the
transferred theorem. -/
theorem gate_watch : (gadW 2 ["\x00", "\x01"] K1).refutes
    ((rel a1F b1F x1 topF).ifThen (rel a1F b1F x1 exfF)) = false := by decide +kernel

/-- **Cell (ii) PASSES**: `[rel₂ ⊤] ⊬ rel₂(p ∨ ¬p)` in the level-two interval. -/
theorem cell2_neg : ¬ Deriv [rel a2F b2F x2 topF] (rel a2F b2F x2 lemF) := fun h =>
  cell2 (Deriv.impIntro h)

end Cells

/-! ### Cell (iii): the negative test `ξ = ζ` -/

/-- The core lemma without the strictness hypothesis `[ζ] ⊬ ξ`. -/
def CoreNoStrict : Prop :=
  ∀ (ξ ζ : PLLFormula) (ρ : String → String), boxFree ξ = true → boxFree ζ = true →
    Deriv [ξ] ζ → Fresh ρ ξ ζ → FreeIn ξ ζ (coreGen ξ ζ ρ)

theorem ipc_top_bot_imp : ¬ Deriv [] (topF.ifThen .falsePLL) :=
  SubTab.no.verdict (topF.ifThen .falsePLL)
    { n := 1, root := 0, le := [[true]], S := [false], val := [[]] }

/-- IPC: `[⊤] ⊬ ⊥` (one world). -/
theorem ipc_top_bot : ¬ Deriv [topF] .falsePLL := fun h => ipc_top_bot_imp (Deriv.impIntro h)

/-- In `[a, a]` the images of `⊤` and `⊥` coincide: `[rel ⊤] ⊢ rel ⊥`. -/
theorem rel_top_bot_diag (a : PLLFormula) (x : String → PLLFormula) :
    Deriv [rel a a x topF] (rel a a x .falsePLL) := Deriv.andElim2 (Deriv.iden (.head _))

/-- **Cell (iii) FAILS, as designed**: no translation into `[a, a]` is faithful. -/
theorem cell_diag (a : PLLFormula) (x : String → PLLFormula) : ¬ FreeIn a a x := fun ⟨_, _, hf⟩ =>
  ipc_top_bot ((hf topF .falsePLL rfl rfl).mpr (rel_top_bot_diag a x))

/-- **REFUTED: the core lemma without `[ζ] ⊬ ξ`** (`ξ = ζ = ⊥`, `ρ = id`). -/
theorem not_coreNoStrict : ¬ CoreNoStrict := fun h =>
  cell_diag .falsePLL _ (h .falsePLL .falsePLL id rfl rfl (Deriv.iden (.head _))
    ⟨fun _ _ e => e, fun _ => ⟨rfl, rfl⟩⟩)

/-- The base-3 instance of (iii): `ξ = ζ = p₀ ∧ p₁` inside the base-3 copy. -/
theorem cell3_base3 :
    ¬ FreeIn Cells.a1F Cells.a1F (nestGen (base 3) topF xω Cells.ξc Cells.ξc Cells.ρc1) :=
  cell_diag _ _

end Cells

end Interval
end F0
end PLLND

/-! ## Axiom pins -/

#axioms_within PLLND.F0.Interval.pvar_inj [propext, Quot.sound]
#axioms_within PLLND.F0.Interval.pvar_ne_of_size [propext, Quot.sound]
#axioms_within PLLND.F0.Interval.Cells.ρc1_inj [propext, Quot.sound]
#axioms_within PLLND.F0.Interval.Cells.ρc2_inj [propext, Quot.sound]
#axioms_within PLLND.F0.Interval.Cells.fresh_c1 [propext, Quot.sound]
#axioms_within PLLND.F0.Interval.Cells.fresh_c2 [propext, Quot.sound]
#axioms_within PLLND.F0.Interval.Cells.hyp1_le [propext, Quot.sound]
#axioms_within PLLND.F0.Interval.Cells.hyp1_strict [propext, Quot.sound]
#axioms_within PLLND.F0.Interval.Cells.hyp2_le [propext, Quot.sound]
#axioms_within PLLND.F0.Interval.Cells.hyp2_strict [propext, Quot.sound]
#axioms_within PLLND.F0.Interval.Cells.reads_K1 [propext, Quot.sound]
#axioms_within PLLND.F0.Interval.Cells.reads_K2 [propext, Quot.sound]
#axioms_within PLLND.F0.Interval.Cells.cell1 [propext, Quot.sound]
#axioms_within PLLND.F0.Interval.Cells.cell2 [propext, Quot.sound]
#axioms_within PLLND.F0.Interval.Cells.ipc_lem [propext, Quot.sound]
#axioms_within PLLND.F0.Interval.Cells.cell1_neg [propext, Quot.sound]
#axioms_within PLLND.F0.Interval.Cells.ipc_exf [propext, Quot.sound]
#axioms_within PLLND.F0.Interval.Cells.bound1 [propext, Quot.sound]
#axioms_within PLLND.F0.Interval.Cells.cell1_pos [propext, Quot.sound]
#axioms_within PLLND.F0.Interval.Cells.gate_watch [propext, Quot.sound]
#axioms_within PLLND.F0.Interval.Cells.cell2_neg [propext, Quot.sound]
#axioms_within PLLND.F0.Interval.ipc_top_bot [propext, Quot.sound]
#axioms_within PLLND.F0.Interval.rel_top_bot_diag [propext, Quot.sound]
#axioms_within PLLND.F0.Interval.cell_diag [propext, Quot.sound]
#axioms_within PLLND.F0.Interval.not_coreNoStrict [propext, Quot.sound]
#axioms_within PLLND.F0.Interval.cell3_base3 [propext, Quot.sound]
