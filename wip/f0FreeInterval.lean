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

## Stage 3: results (IPC fragment, CLAUDE.md rule 8)

**PROVED**, pins `[propext, Quot.sound]`, no `Classical.choice`, no `sorry`,
no `native_decide`: `CoreLemma` (`coreLemma`), `Nest` (`nest`), `MainTheorem`
(`mainTheorem`), `Bridge` (`bridge`), `Bridge3` (`bridge3`), `NestTwo`
(`nestTwo`); with `freeHAωIn_base3 : FreeHAωIn σ³⊥ ⊤` and the depth-one
corollary `nestOne`.  `NestPLL` stays OPEN (not in scope).

* `rel_iff_relB`: at a world forcing `b`, `rel a b x A ⟺ relB a x A` (◯-free `A`).
* `⟹` (`rel_preserves`): `relB_preservesω` of `f0FreeBase3`, through
  `rel_iff_relB`, since every `rel`-image lies below `b` (`force_rel_b`).
* `⟸` of the core lemma (`core_reflects`), the gluing (`Glue.G`): a finite
  countermodel `N` of `[ζ] ⊢ ξ`, a world `w` maximal among those forcing `ζ`
  and refuting `ξ` (`exists_max_not`), and any finite `K`; the copy of `K`
  sits below the strict successors of `w`, the old atoms take `w`'s values
  (`Glue.collapse`), `ρ p` holds at the copy of `u` iff `u ⊩ p` and at every
  world of `N`.  Then `relB_transferω` reads `K` off the copy.
* Composition (`rel_comp`, all formulas, `◯` included):
  `rel (rel ξ) (rel ζ) (rel ∘ y) A ⟺ rel (rel ξ ζ y A)` in every model.
* Fresh renamings exist (`fresh_freshRen`, `p ↦ pvar (bound + code p)`).
* Cross-check: `Nest` with the cell's renaming gives cell (i) again
  (`cell1_by_theorem`).

## Stage 4: every finite depth, and the operations, hereditarily

**PROVED**, pins `[propext, Quot.sound]`: `NestAll` (`nestAll`; hence
`freeHAωIn_tower`, `[a_d, b_d]` contains `H_ω` inside F0 for every `d`),
`RelConnectives` (`rel_connectives`), `TowerRel` (`tower_rel`),
`IntervalOpsAgree` (`interval_ops_agree`), `TowerOpsAgree` (`tower_ops_agree`),
`HereditaryOps` (`hereditary_ops`).

Connective preservation is built into `rel`: it sends `∧`, `∨` to themselves,
`→` to `(· ↠ ·) ∧ b`, `◯` to `◯(·) ∧ b` and `⊥` to `a` by definition, with
`rel ⊤ ⊣⊢ b` (`rel_connectives`).  `FreeIn` asks only for faithfulness, and
the image is then a Heyting subalgebra of `[a, b]` under F0's interval
operations (meet, join, `(u ↠ v) ∧ b`, bottom `a`, top `b`).  This holds
hereditarily, at every depth.  The depth-`d` translation is a single `rel`
into `[a_d, b_d]` (`tower_rel`).  Each step is a sub-interval
`[a_{d+1}, b_{d+1}] ⊆ [a_d, b_d]`, and its operations computed inside
`[a_d, b_d]` agree with those computed in F0 (`tower_ops_agree`).

Credit: the interval translation is O'Connor's device.  M. O'Connor,
"Embeddings into free Heyting algebras and translations into intuitionistic
propositional logic", 2007, arXiv math/0702651: the proof of Theorem 14 (a
lattice embedding of `H_ω` into `H₂`; the same translation first appears in
the proof of Proposition 6) sends `⊥ ↦ φ`, generators to `(φ′ ∨ φ) ∧ ψ`, and
`→` to `(→) ∧ ψ`, inside `H₂`.  What this file adds is the transport into F0,
the closed fragment of PLL (the base-3 copy and the bridge), and the nesting
at every depth.

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

/-! ## Stage 3 (a): semantics of the interval translation -/

/-- Soundness for a one-hypothesis sequent, `Prop` level. -/
theorem sem_of_deriv {φ ψ : PLLFormula} (h : Deriv [φ] ψ) (M : SubframeModel) (v : M.W)
    (hv : M.force v φ) : M.force v ψ :=
  let ⟨d⟩ := h
  SubframeModel.CF.soundness₁ d M v hv

/-- Completeness for a one-hypothesis sequent, over the finite decidable models. -/
theorem deriv_of_sem {φ ψ : PLLFormula}
    (h : ∀ (M : SubframeModel) [FinDec M] (v : M.W), M.force v φ → M.force v ψ) :
    Deriv [φ] ψ := by
  have h2 : Deriv [] (φ.ifThen ψ) := SubframeModel.CF.completeness_imp h
  exact Deriv.impElim (h2.rename fun _ h => absurd h List.not_mem_nil) (Deriv.iden (.head _))

/-- Derivability respects forcing-equivalence in every model. -/
theorem deriv_congr {φ φ' ψ ψ' : PLLFormula}
    (hφ : ∀ (M : SubframeModel) (v : M.W), M.force v φ ↔ M.force v φ')
    (hψ : ∀ (M : SubframeModel) (v : M.W), M.force v ψ ↔ M.force v ψ') :
    Deriv [φ] ψ ↔ Deriv [φ'] ψ' :=
  ⟨fun h => deriv_of_sem fun M _ v hv => (hψ M v).mp (sem_of_deriv h M v ((hφ M v).mpr hv)),
   fun h => deriv_of_sem fun M _ v hv => (hψ M v).mpr (sem_of_deriv h M v ((hφ M v).mp hv))⟩

section Model

variable (M : SubframeModel) (a b : PLLFormula) (x : String → PLLFormula)

/-- **Every `rel`-image lies below `b`**, given `a ≤ b` and `x p ≤ b`. -/
theorem force_rel_b (hab : ∀ v, M.force v a → M.force v b)
    (hxb : ∀ v p, M.force v (x p) → M.force v b) :
    ∀ (A : PLLFormula) (v : M.W), M.force v (rel a b x A) → M.force v b
  | .prop p, v, h => hxb v p h
  | .falsePLL, v, h => hab v h
  | .and A _, v, h => force_rel_b hab hxb A v h.1
  | .or A B, v, h => h.elim (force_rel_b hab hxb A v) (force_rel_b hab hxb B v)
  | .ifThen _ _, _, h => h.2
  | .somehow _, _, h => h.2

/-- **At a world forcing `b`, `rel` and `relB` agree** on ◯-free formulas:

    v ⊩ b   ⟹   (v ⊩ rel a b x A  ⟺  v ⊩ relB a x A). -/
theorem rel_iff_relB : ∀ (A : PLLFormula), boxFree A = true → ∀ (v : M.W), M.force v b →
    (M.force v (rel a b x A) ↔ M.force v (relB a x A))
  | .prop _, _, _, _ => Iff.rfl
  | .falsePLL, _, _, _ => Iff.rfl
  | .and A B, hf, v, hv => by
      have hf' := Bool.and_eq_true_iff.mp (hf : (boxFree A && boxFree B) = true)
      exact and_congr (rel_iff_relB A hf'.1 v hv) (rel_iff_relB B hf'.2 v hv)
  | .or A B, hf, v, hv => by
      have hf' := Bool.and_eq_true_iff.mp (hf : (boxFree A && boxFree B) = true)
      exact or_congr (rel_iff_relB A hf'.1 v hv) (rel_iff_relB B hf'.2 v hv)
  | .ifThen A B, hf, v, hv => by
      have hf' := Bool.and_eq_true_iff.mp (hf : (boxFree A && boxFree B) = true)
      show ((∀ u, M.le v u → M.force u (rel a b x A) → M.force u (rel a b x B)) ∧ M.force v b) ↔
        (∀ u, M.le v u → M.force u (relB a x A) → M.force u (relB a x B))
      constructor
      · intro h u hu hA
        have hub := SubframeModel.force_mono M b hu hv
        exact (rel_iff_relB B hf'.2 u hub).mp (h.1 u hu ((rel_iff_relB A hf'.1 u hub).mpr hA))
      · intro h
        refine ⟨fun u hu hA => ?_, hv⟩
        have hub := SubframeModel.force_mono M b hu hv
        exact (rel_iff_relB B hf'.2 u hub).mpr (h u hu ((rel_iff_relB A hf'.1 u hub).mp hA))
  | .somehow _, hf, _, _ => nomatch hf

/-- **Composition**: carrying the interval `[ξ, ζ]` with generators `y` into the
copy `rel a b x` is, up to forcing-equivalence, the interval translation for
`[rel ξ, rel ζ]` with the generators `rel a b x ∘ y`, for ALL formulas (`◯`
included):

    v ⊩ rel (rel ξ) (rel ζ) (rel ∘ y) A   ⟺   v ⊩ rel (rel ξ ζ y A). -/
theorem rel_comp (ξ ζ : PLLFormula) (y : String → PLLFormula)
    (hab : ∀ v, M.force v a → M.force v b) (hxb : ∀ v p, M.force v (x p) → M.force v b) :
    ∀ (A : PLLFormula) (v : M.W),
      M.force v (rel (rel a b x ξ) (rel a b x ζ) (fun p => rel a b x (y p)) A) ↔
        M.force v (rel a b x (rel ξ ζ y A))
  | .prop _, _ => Iff.rfl
  | .falsePLL, _ => Iff.rfl
  | .and A B, v => and_congr (rel_comp ξ ζ y hab hxb A v) (rel_comp ξ ζ y hab hxb B v)
  | .or A B, v => or_congr (rel_comp ξ ζ y hab hxb A v) (rel_comp ξ ζ y hab hxb B v)
  | .ifThen A B, v => by
      have hb := force_rel_b M a b x hab hxb ζ v
      show ((∀ u, M.le v u →
          M.force u (rel (rel a b x ξ) (rel a b x ζ) (fun p => rel a b x (y p)) A) →
          M.force u (rel (rel a b x ξ) (rel a b x ζ) (fun p => rel a b x (y p)) B)) ∧
          M.force v (rel a b x ζ)) ↔
        (((∀ u, M.le v u → M.force u (rel a b x (rel ξ ζ y A)) →
          M.force u (rel a b x (rel ξ ζ y B))) ∧ M.force v b) ∧ M.force v (rel a b x ζ))
      constructor
      · intro h
        refine ⟨⟨fun u hu hA => ?_, hb h.2⟩, h.2⟩
        exact (rel_comp ξ ζ y hab hxb B u).mp (h.1 u hu ((rel_comp ξ ζ y hab hxb A u).mpr hA))
      · intro h
        refine ⟨fun u hu hA => ?_, h.2⟩
        exact (rel_comp ξ ζ y hab hxb B u).mpr (h.1.1 u hu ((rel_comp ξ ζ y hab hxb A u).mp hA))
  | .somehow A, v => by
      have hb := force_rel_b M a b x hab hxb ζ v
      show ((∀ u, M.le v u → u ∈ M.S →
          M.force u (rel (rel a b x ξ) (rel a b x ζ) (fun p => rel a b x (y p)) A)) ∧
          M.force v (rel a b x ζ)) ↔
        (((∀ u, M.le v u → u ∈ M.S → M.force u (rel a b x (rel ξ ζ y A))) ∧ M.force v b) ∧
          M.force v (rel a b x ζ))
      constructor
      · intro h
        exact ⟨⟨fun u hu hS => (rel_comp ξ ζ y hab hxb A u).mp (h.1 u hu hS), hb h.2⟩, h.2⟩
      · intro h
        exact ⟨fun u hu hS => (rel_comp ξ ζ y hab hxb A u).mpr (h.1.1 u hu hS), h.2⟩

end Model

/-- **Preservation (`⟹`)**: for `a ≤ x p ≤ b` in every model, the interval
translation of a derivable ◯-free sequent is derivable (through
`relB_preservesω` of `f0FreeBase3`, the relativisation lemma). -/
theorem rel_preserves (a b : PLLFormula) (x : String → PLLFormula)
    (hax : ∀ (M : SubframeModel) v p, M.force v a → M.force v (x p))
    (hxb : ∀ (M : SubframeModel) v p, M.force v (x p) → M.force v b)
    {A B : PLLFormula} (hA : boxFree A = true) (hB : boxFree B = true) (hd : Deriv [A] B) :
    Deriv [rel a b x A] (rel a b x B) := by
  have hR := relB_preservesω a x (fun M v p hv => hax M v p hv) hA hB hd
  refine deriv_of_sem fun M _ v hv => ?_
  have hb := force_rel_b M a b x (fun u hu => hxb M u "" (hax M u "" hu)) (hxb M) A v hv
  exact (rel_iff_relB M a b x B hB v hb).mpr
    (sem_of_deriv hR M v ((rel_iff_relB M a b x A hA v hb).mp hv))

/-! ## Stage 3 (b): syntactic side conditions -/

theorem or_eq_false_split {p q : Bool} (h : (p || q) = false) : p = false ∧ q = false := by
  cases p <;> cases q <;> first | exact ⟨rfl, rfl⟩ | exact absurd h (by decide)

theorem boxFree_coreGen {ξ ζ : PLLFormula} (hξ : boxFree ξ = true) (hζ : boxFree ζ = true)
    (ρ : String → String) (p : String) : boxFree (coreGen ξ ζ ρ p) = true := by
  show ((true && boxFree ξ) && boxFree ζ) = true
  rw [hξ, hζ]
  rfl

theorem boxFree_rel {a b : PLLFormula} {x : String → PLLFormula} (hb : boxFree b = true)
    (ha : boxFree a = true) (hx : ∀ p, boxFree (x p) = true) :
    ∀ A : PLLFormula, boxFree A = true → boxFree (rel a b x A) = true
  | .prop p, _ => hx p
  | .falsePLL, _ => ha
  | .and A B, hf => by
      have hf' := Bool.and_eq_true_iff.mp (hf : (boxFree A && boxFree B) = true)
      show (boxFree (rel a b x A) && boxFree (rel a b x B)) = true
      rw [boxFree_rel hb ha hx A hf'.1, boxFree_rel hb ha hx B hf'.2]
      rfl
  | .or A B, hf => by
      have hf' := Bool.and_eq_true_iff.mp (hf : (boxFree A && boxFree B) = true)
      show (boxFree (rel a b x A) && boxFree (rel a b x B)) = true
      rw [boxFree_rel hb ha hx A hf'.1, boxFree_rel hb ha hx B hf'.2]
      rfl
  | .ifThen A B, hf => by
      have hf' := Bool.and_eq_true_iff.mp (hf : (boxFree A && boxFree B) = true)
      show ((boxFree (rel a b x A) && boxFree (rel a b x B)) && boxFree b) = true
      rw [boxFree_rel hb ha hx A hf'.1, boxFree_rel hb ha hx B hf'.2, hb]
      rfl
  | .somehow _, hf => nomatch hf

theorem atomFree_rel {a b : PLLFormula} {x : String → PLLFormula} (ha : atomFree a = true)
    (hb : atomFree b = true) (hx : ∀ p, atomFree (x p) = true) :
    ∀ A : PLLFormula, atomFree (rel a b x A) = true
  | .prop p => hx p
  | .falsePLL => ha
  | .and A B => by
      show (atomFree (rel a b x A) && atomFree (rel a b x B)) = true
      rw [atomFree_rel ha hb hx A, atomFree_rel ha hb hx B]
      rfl
  | .or A B => by
      show (atomFree (rel a b x A) && atomFree (rel a b x B)) = true
      rw [atomFree_rel ha hb hx A, atomFree_rel ha hb hx B]
      rfl
  | .ifThen A B => by
      show ((atomFree (rel a b x A) && atomFree (rel a b x B)) && atomFree b) = true
      rw [atomFree_rel ha hb hx A, atomFree_rel ha hb hx B, hb]
      rfl
  | .somehow A => by
      show (atomFree (rel a b x A) && atomFree b) = true
      rw [atomFree_rel ha hb hx A, hb]
      rfl

/-! ## Stage 3 (c): a maximal world refuting `ξ` -/

/-- **Above every world refuting `ξ` there is one maximal among them**: every
successor either forces `ξ` or lies below it (descent on the number of proper
successors, as `FreeIPL.exists_rmax_aux`). -/
theorem exists_max_not (M : SubframeModel) [FinDec M] (ξ : PLLFormula) :
    ∀ (n : Nat) (w : M.W), Normal.nProper M w ≤ n → ¬ M.force w ξ →
      ∃ m, M.le w m ∧ ¬ M.force m ξ ∧ ∀ v, M.le m v → M.force v ξ ∨ M.le v m := by
  intro n
  induction n with
  | zero =>
      intro w hn hw
      refine ⟨w, M.refl w, hw, fun v hv => ?_⟩
      rcases Decidable.em (M.le v w) with hvw | hvw
      · exact Or.inr hvw
      · exact absurd (Nat.lt_of_lt_of_le (Normal.nProper_lt M hv hvw) hn) (Nat.not_lt_zero _)
  | succ k ih =>
      intro w hn hw
      rcases Decidable.em (∃ v ∈ FinDec.elems (M := M), M.le w v ∧ ¬ M.force v ξ ∧ ¬ M.le v w)
        with hex | hno
      · obtain ⟨v, _, hv, hvξ, hvw⟩ := hex
        obtain ⟨m, hvm, hm⟩ :=
          ih v (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (Normal.nProper_lt M hv hvw) hn)) hvξ
        exact ⟨m, M.trans hv hvm, hm⟩
      · refine ⟨w, M.refl w, hw, fun v hv => ?_⟩
        rcases Decidable.em (M.force v ξ) with hvξ | hvξ
        · exact Or.inl hvξ
        · rcases Decidable.em (M.le v w) with hvw | hvw
          · exact Or.inr hvw
          · exact absurd ⟨v, FinDec.complete v, hv, hvξ, hvw⟩ hno

/-! ## Stage 3 (d): the gluing

`N` a model, `w` a world maximal among those refuting `ξ` (`hmax`), `K` any
model, `ρ` a renaming.  The glued model has a copy `inl u` of each world of
`K` and a copy `inr n` of each world of `N`; `inl u ≤ inr n` iff `n ≥ w` and
`n ⊩ ξ` (the strict successors of `w`).  The old atoms take `w`'s values on the
copy of `K`; the atom `ρ p` holds at `inl u` iff `u ⊩ p`, and at every `inr n`.
`S` is `K`'s on the copy and `N`'s on `N` (the copy keeps `K`'s `S`, which the
`◯` case of the PLL stage will read). -/

namespace Glue

variable (N : SubframeModel) (w : N.W) (ξ : PLLFormula) (K : SubframeModel)
  (ρ : String → String)

/-- The order of the glued model. -/
def Le : K.W ⊕ N.W → K.W ⊕ N.W → Prop
  | .inl u, .inl u' => K.le u u'
  | .inl _, .inr n => N.le w n ∧ N.force n ξ
  | .inr n, .inr n' => N.le n n'
  | .inr _, .inl _ => False

/-- `S`: `K`'s on the copy, `N`'s on `N`. -/
def SG : K.W ⊕ N.W → Prop
  | .inl u => u ∈ K.S
  | .inr n => n ∈ N.S

/-- The valuation of the glued model. -/
def VG (c : String) : K.W ⊕ N.W → Prop
  | .inl u => (∃ p, ρ p = c ∧ u ∈ K.V p) ∨ ((∀ p, ρ p ≠ c) ∧ w ∈ N.V c)
  | .inr n => (∃ p, ρ p = c) ∨ n ∈ N.V c

theorem Le.refl : ∀ g : K.W ⊕ N.W, Le N w ξ K g g
  | .inl u => K.refl u
  | .inr n => N.refl n

theorem Le.trans : ∀ {g₁ g₂ g₃ : K.W ⊕ N.W}, Le N w ξ K g₁ g₂ → Le N w ξ K g₂ g₃ →
    Le N w ξ K g₁ g₃
  | .inl _, .inl _, .inl _, h₁, h₂ => K.trans h₁ h₂
  | .inl _, .inl _, .inr _, _, h₂ => h₂
  | .inl _, .inr _, .inr _, h₁, h₂ =>
      ⟨N.trans h₁.1 h₂, SubframeModel.force_mono N ξ h₂ h₁.2⟩
  | .inr _, .inr _, .inr _, h₁, h₂ => N.trans h₁ h₂
  | .inl _, .inr _, .inl _, _, h₂ => False.elim h₂
  | .inr _, .inl _, _, h₁, _ => False.elim h₁
  | .inr _, .inr _, .inl _, _, h₂ => False.elim h₂

theorem VG.hered {c : String} : ∀ {g g' : K.W ⊕ N.W}, Le N w ξ K g g' →
    VG N w K ρ c g → VG N w K ρ c g'
  | .inl _, .inl _, h, hg => hg.elim (fun ⟨p, e, hu⟩ => Or.inl ⟨p, e, K.hered h hu⟩) Or.inr
  | .inl _, .inr _, h, hg =>
      hg.elim (fun ⟨p, e, _⟩ => Or.inl ⟨p, e⟩) (fun ⟨_, hw⟩ => Or.inr (N.hered h.1 hw))
  | .inr _, .inr _, h, hg => hg.elim Or.inl (fun hn => Or.inr (N.hered h hn))
  | .inr _, .inl _, h, _ => False.elim h

/-- **The glued model.** -/
def G : SubframeModel where
  W := K.W ⊕ N.W
  le := Le N w ξ K
  S := fun g => SG N K g
  V c := fun g => VG N w K ρ c g
  refl := Le.refl N w ξ K
  trans h₁ h₂ := Le.trans N w ξ K h₁ h₂
  hered h hg := VG.hered N w ξ K ρ h hg

/-- The collapse map: the copy of `K` to `w`, the copy of `N` to itself. -/
def fG : K.W ⊕ N.W → N.W
  | .inl _ => w
  | .inr n => n

variable {N w ξ K ρ}

/-- **The collapse lemma**: on ◯-free formulas without the fresh atoms, the
glued model at `g` agrees with `N` at its collapse (`w` maximal among the
worlds refuting `ξ`). -/
theorem collapse (hmax : ∀ v, N.le w v → N.force v ξ ∨ N.le v w) :
    ∀ (φ : PLLFormula), boxFree φ = true → (∀ p, occ (ρ p) φ = false) →
      ∀ g, ((G N w ξ K ρ).force g φ ↔ N.force (fG N w K g) φ)
  | .prop c, _, ho, g => by
      have hc : ∀ p, ρ p ≠ c := fun p e => by
        have h1 : decide (c = ρ p) = false := ho p
        exact absurd e.symm (of_decide_eq_false h1)
      cases g with
      | inl u =>
          show VG N w K ρ c (.inl u) ↔ w ∈ N.V c
          exact ⟨fun h => h.elim (fun ⟨p, e, _⟩ => absurd e (hc p)) (fun h => h.2),
            fun h => Or.inr ⟨hc, h⟩⟩
      | inr n =>
          show VG N w K ρ c (.inr n) ↔ n ∈ N.V c
          exact ⟨fun h => h.elim (fun ⟨p, e⟩ => absurd e (hc p)) id, Or.inr⟩
  | .falsePLL, _, _, _ => Iff.rfl
  | .and A B, hf, ho, g => by
      have hf' := Bool.and_eq_true_iff.mp (hf : (boxFree A && boxFree B) = true)
      have hoA : ∀ p, occ (ρ p) A = false := fun p => (or_eq_false_split (ho p)).1
      have hoB : ∀ p, occ (ρ p) B = false := fun p => (or_eq_false_split (ho p)).2
      exact and_congr (collapse hmax A hf'.1 hoA g) (collapse hmax B hf'.2 hoB g)
  | .or A B, hf, ho, g => by
      have hf' := Bool.and_eq_true_iff.mp (hf : (boxFree A && boxFree B) = true)
      have hoA : ∀ p, occ (ρ p) A = false := fun p => (or_eq_false_split (ho p)).1
      have hoB : ∀ p, occ (ρ p) B = false := fun p => (or_eq_false_split (ho p)).2
      exact or_congr (collapse hmax A hf'.1 hoA g) (collapse hmax B hf'.2 hoB g)
  | .ifThen A B, hf, ho, g => by
      have hf' := Bool.and_eq_true_iff.mp (hf : (boxFree A && boxFree B) = true)
      have hoA : ∀ p, occ (ρ p) A = false := fun p => (or_eq_false_split (ho p)).1
      have hoB : ∀ p, occ (ρ p) B = false := fun p => (or_eq_false_split (ho p)).2
      have ihA := collapse hmax A hf'.1 hoA
      have ihB := collapse hmax B hf'.2 hoB
      cases g with
      | inl u =>
          show (∀ g', Le N w ξ K (.inl u) g' → (G N w ξ K ρ).force g' A →
              (G N w ξ K ρ).force g' B) ↔ (∀ v, N.le w v → N.force v A → N.force v B)
          constructor
          · intro h v hv hA
            rcases hmax v hv with hvξ | hvw
            · exact (ihB (.inr v)).mp (h (.inr v) ⟨hv, hvξ⟩ ((ihA (.inr v)).mpr hA))
            · have hwA : N.force w A := SubframeModel.force_mono N A hvw hA
              have hwB : N.force w B :=
                (ihB (.inl u)).mp (h (.inl u) (K.refl u) ((ihA (.inl u)).mpr hwA))
              exact SubframeModel.force_mono N B hv hwB
          · intro h g' hg' hA
            cases g' with
            | inl u' => exact (ihB (.inl u')).mpr (h w (N.refl w) ((ihA (.inl u')).mp hA))
            | inr n => exact (ihB (.inr n)).mpr (h n hg'.1 ((ihA (.inr n)).mp hA))
      | inr n =>
          show (∀ g', Le N w ξ K (.inr n) g' → (G N w ξ K ρ).force g' A →
              (G N w ξ K ρ).force g' B) ↔ (∀ v, N.le n v → N.force v A → N.force v B)
          constructor
          · intro h v hv hA
            exact (ihB (.inr v)).mp (h (.inr v) hv ((ihA (.inr v)).mpr hA))
          · intro h g' hg' hA
            cases g' with
            | inl _ => exact False.elim hg'
            | inr n' => exact (ihB (.inr n')).mpr (h n' hg' ((ihA (.inr n')).mp hA))
  | .somehow _, hf, _, _ => nomatch hf

end Glue

/-! ## Stage 3 (e): the core lemma -/

section Core

variable {ξ ζ : PLLFormula} {ρ : String → String}

/-- The core generators lie in `[ξ, ζ]`. -/
theorem core_bounds (hle : Deriv [ξ] ζ) (p : String) :
    Deriv [ξ] (coreGen ξ ζ ρ p) ∧ Deriv [coreGen ξ ζ ρ p] ζ :=
  ⟨Deriv.andIntro (Deriv.orIntro2 (Deriv.iden (.head _))) hle,
   Deriv.andElim2 (Deriv.iden (.head _))⟩

/-- **The core lemma, `⟸`, by the gluing**: a finite countermodel `N` of
`[ζ] ⊢ ξ` with a world `w` maximal among those forcing `ζ` and refuting `ξ`,
and any finite model `K`; in the glued model the copy of `u` forces
`rel ξ ζ y A` iff `u ⊩ A` (`relB_transferω` of `f0FreeBase3`, after
`rel_iff_relB` at the `ζ`-worlds). -/
theorem core_reflects (hξ : boxFree ξ = true) (hζ : boxFree ζ = true) (hle : Deriv [ξ] ζ)
    (hstrict : ¬ Deriv [ζ] ξ) (hfr : Fresh ρ ξ ζ) {A B : PLLFormula} (hA : boxFree A = true)
    (hB : boxFree B = true)
    (hd : Deriv [rel ξ ζ (coreGen ξ ζ ρ) A] (rel ξ ζ (coreGen ξ ζ ρ) B)) : Deriv [A] B := by
  have h0 : ¬ Deriv [] (ζ.ifThen ξ) := fun h =>
    hstrict (Deriv.impElim (h.rename fun _ h => absurd h List.not_mem_nil) (Deriv.iden (.head _)))
  obtain ⟨N, hN, k, hk⟩ := SubframeModel.CF.exists_countermodel h0
  obtain ⟨w₁, hkw₁, hw₁ζ, hw₁ξ⟩ := SubframeModel.CF.exists_of_not_force_imp hk
  obtain ⟨w, hw₁w, hwξ, hmax⟩ := exists_max_not N ξ _ w₁ (Nat.le_refl _) hw₁ξ
  have hwζ : N.force w ζ := SubframeModel.force_mono N ζ hw₁w hw₁ζ
  have hoξ : ∀ p, occ (ρ p) ξ = false := fun p => (hfr.2 p).1
  have hoζ : ∀ p, occ (ρ p) ζ = false := fun p => (hfr.2 p).2
  refine deriv_of_sem fun K _ u hu => ?_
  let Gm := Glue.G N w ξ K ρ
  have cξ := Glue.collapse (K := K) (ρ := ρ) hmax ξ hξ hoξ
  have cζ := Glue.collapse (K := K) (ρ := ρ) hmax ζ hζ hoζ
  have hb : ∀ u' : K.W, ¬ Gm.force (.inl u') ξ := fun u' h => hwξ ((cξ (.inl u')).mp h)
  have hz : ∀ u' : K.W, Gm.force (.inl u') ζ := fun u' => (cζ (.inl u')).mpr hwζ
  have hbx : ∀ (v : Gm.W) p, Gm.force v ξ → Gm.force v (coreGen ξ ζ ρ p) := fun v _ hv =>
    ⟨Or.inr hv, sem_of_deriv hle Gm v hv⟩
  have hback : ∀ (u' : K.W) (v : Gm.W), Gm.le (.inl u') v →
      Gm.force v ξ ∨ ∃ j, K.le u' j ∧ Sum.inl j = v := by
    intro u' v hv
    cases v with
    | inl j => exact Or.inr ⟨j, hv, rfl⟩
    | inr n => exact Or.inl ((cξ (.inr n)).mpr hv.2)
  have hatom : ∀ (u' : K.W) p, (Gm.force (.inl u') (coreGen ξ ζ ρ p) ↔ u' ∈ K.V p) := by
    intro u' p
    constructor
    · intro h
      rcases h.1 with hv | hv
      · rcases hv with ⟨p', e, hu'⟩ | ⟨hne, _⟩
        · rw [hfr.1 p' p e] at hu'
          exact hu'
        · exact absurd rfl (hne p)
      · exact absurd hv (hb u')
    · intro h
      exact ⟨Or.inl (Or.inl ⟨p, rfl, h⟩), hz u'⟩
  have htr := relB_transferω Gm ξ (coreGen ξ ζ ρ) K Sum.inl hbx hb (fun h => h) hback hatom
  have hrA : Gm.force (.inl u) (rel ξ ζ (coreGen ξ ζ ρ) A) :=
    (rel_iff_relB Gm ξ ζ _ A hA (.inl u) (hz u)).mpr ((htr A hA u).mpr hu)
  have hrB := sem_of_deriv hd Gm (.inl u) hrA
  exact (htr B hB u).mp ((rel_iff_relB Gm ξ ζ _ B hB (.inl u) (hz u)).mp hrB)

/-- **PROVED: the core lemma (★).** -/
theorem coreLemma : CoreLemma := by
  intro ξ ζ ρ hξ hζ hle hstrict hfr
  refine ⟨fun p => (core_bounds hle p).1, fun p => (core_bounds hle p).2, fun A B hA hB => ?_⟩
  refine ⟨rel_preserves ξ ζ (coreGen ξ ζ ρ)
      (fun M v _ hv => ⟨Or.inr hv, sem_of_deriv hle M v hv⟩) (fun _ _ _ hv => hv.2) hA hB,
    core_reflects hξ hζ hle hstrict hfr hA hB⟩

end Core

/-! ## Stage 3 (f): fresh renamings exist -/

/-- A bound on the UTF-8 sizes of the atoms of a formula. -/
def atomBound : PLLFormula → Nat
  | .prop c => c.utf8ByteSize
  | .falsePLL => 0
  | .and A B => atomBound A + atomBound B
  | .or A B => atomBound A + atomBound B
  | .ifThen A B => atomBound A + atomBound B
  | .somehow A => atomBound A

theorem occ_size (c : String) : ∀ φ : PLLFormula, occ c φ = true → c.utf8ByteSize ≤ atomBound φ
  | .prop a, h => by
      have e : a = c := of_decide_eq_true h
      subst e
      exact Nat.le_refl _
  | .falsePLL, h => Bool.noConfusion h
  | .and A B, h => by
      have h' : (occ c A || occ c B) = true := h
      rw [Bool.or_eq_true] at h'
      rcases h' with hA | hB
      · exact Nat.le_trans (occ_size c A hA) (Nat.le_add_right _ _)
      · exact Nat.le_trans (occ_size c B hB) (Nat.le_add_left _ _)
  | .or A B, h => by
      have h' : (occ c A || occ c B) = true := h
      rw [Bool.or_eq_true] at h'
      rcases h' with hA | hB
      · exact Nat.le_trans (occ_size c A hA) (Nat.le_add_right _ _)
      · exact Nat.le_trans (occ_size c B hB) (Nat.le_add_left _ _)
  | .ifThen A B, h => by
      have h' : (occ c A || occ c B) = true := h
      rw [Bool.or_eq_true] at h'
      rcases h' with hA | hB
      · exact Nat.le_trans (occ_size c A hA) (Nat.le_add_right _ _)
      · exact Nat.le_trans (occ_size c B hB) (Nat.le_add_left _ _)
  | .somehow A, h => occ_size c A h

/-- **A fresh renaming**: `p ↦ pvar (atomBound ξ + atomBound ζ + code p)`. -/
def freshRen (ξ ζ : PLLFormula) (p : String) : String :=
  pvar (atomBound ξ + atomBound ζ + Base3.code p)

theorem freshRen_occ {ξ ζ : PLLFormula} (p : String) {φ : PLLFormula}
    (hφ : atomBound φ ≤ atomBound ξ + atomBound ζ) : occ (freshRen ξ ζ p) φ = false := by
  cases h : occ (freshRen ξ ζ p) φ with
  | false => rfl
  | true =>
      have h1 := occ_size _ φ h
      unfold freshRen at h1
      rw [utf8ByteSize_pvar] at h1
      exact absurd (Nat.le_trans h1 (Nat.le_trans hφ (Nat.le_add_right _ _)))
        (Nat.not_succ_le_self _)

/-- **PROVED: every pair has a fresh renaming.** -/
theorem fresh_freshRen (ξ ζ : PLLFormula) : Fresh (freshRen ξ ζ) ξ ζ :=
  ⟨fun _ _ h => Base3.code_inj (Nat.add_left_cancel (pvar_inj h)),
   fun p => ⟨freshRen_occ p (Nat.le_add_right _ _), freshRen_occ p (Nat.le_add_left _ _)⟩⟩

/-! ## Stage 3 (g): transport, nesting, the main theorem -/

/-- **PROVED: `Nest`** (transport through `rel_comp`, the core lemma, and the
faithfulness of the outer copy). -/
theorem nest : Nest := by
  intro a b x ξ ζ ρ hF hξ hζ hle hstrict hfr
  obtain ⟨hax, hxb, hfaith⟩ := hF
  obtain ⟨hyl, hyu, hyf⟩ := coreLemma ξ ζ ρ hξ hζ hle hstrict hfr
  have sax : ∀ (M : SubframeModel) v p, M.force v a → M.force v (x p) := fun M v p h =>
    sem_of_deriv (hax p) M v h
  have sxb : ∀ (M : SubframeModel) v p, M.force v (x p) → M.force v b := fun M v p h =>
    sem_of_deriv (hxb p) M v h
  have sab : ∀ (M : SubframeModel) v, M.force v a → M.force v b := fun M v h =>
    sxb M v "" (sax M v "" h)
  refine ⟨fun p => rel_preserves a b x sax sxb hξ (boxFree_coreGen hξ hζ ρ p) (hyl p),
    fun p => rel_preserves a b x sax sxb (boxFree_coreGen hξ hζ ρ p) hζ (hyu p),
    fun A B hA hB => ?_⟩
  have hyb : ∀ p, boxFree (coreGen ξ ζ ρ p) = true := boxFree_coreGen hξ hζ ρ
  refine (hyf A B hA hB).trans ((hfaith _ _ (boxFree_rel hζ hξ hyb A hA)
    (boxFree_rel hζ hξ hyb B hB)).trans (deriv_congr ?_ ?_))
  · exact fun M v => (rel_comp M a b x ξ ζ (coreGen ξ ζ ρ) (sab M) (sxb M) A v).symm
  · exact fun M v => (rel_comp M a b x ξ ζ (coreGen ξ ζ ρ) (sab M) (sxb M) B v).symm

/-- **PROVED: the main theorem.** -/
theorem mainTheorem : MainTheorem := by
  intro a b x ξ ζ ha hb hx hF hξ hζ hle hstrict
  exact ⟨nestGen a b x ξ ζ (freshRen ξ ζ), fun p => atomFree_rel ha hb hx _,
    nest a b x ξ ζ _ hF hξ hζ hle hstrict (fresh_freshRen ξ ζ)⟩

/-! ## Stage 3 (h): the bridge from the base-3 copy, and depth two -/

theorem force_topF (M : SubframeModel) (v : M.W) : M.force v topF := fun _ _ h => h

/-- **PROVED: the bridge.** -/
theorem bridge : Bridge := by
  intro b x hbx hf
  refine ⟨hbx, fun _ => Deriv.impIntro (Deriv.iden (.head _)), fun A B hA hB => ?_⟩
  exact (hf A B hA hB).trans (deriv_congr
    (fun M v => (rel_iff_relB M b topF x A hA v (force_topF M v)).symm)
    (fun M v => (rel_iff_relB M b topF x B hB v (force_topF M v)).symm))

/-- **PROVED: `FreeIn σ³⊥ ⊤ xω`** (from `freeOmega3` of `f0FreeBase3`). -/
theorem bridge3 : Bridge3 := bridge (base 3) xω (fun _ => b3_le_gen _) freeOmega3

/-- `FreeHAωAbove b` gives `FreeHAωIn b ⊤`. -/
theorem freeHAωIn_of_above {b : PLLFormula} (h : FreeHAωAbove b) : FreeHAωIn b topF :=
  let ⟨x, hvf, hle, hf⟩ := h
  ⟨x, hvf, bridge b x hle hf⟩

/-- **PROVED: `FreeHAωIn σ³⊥ ⊤`**, from `freeHAωAbove_base3`. -/
theorem freeHAωIn_base3 : FreeHAωIn (base 3) topF := freeHAωIn_of_above freeHAωAbove_base3

/-- **PROVED, depth one inside the base-3 copy**: for ◯-free `ξ`, `ζ` with
`[ξ] ⊢ ζ` and `[ζ] ⊬ ξ`, `[rel σ³⊥ ⊤ xω ξ, rel σ³⊥ ⊤ xω ζ]` contains `H_ω`. -/
theorem nestOne (ξ ζ : PLLFormula) (hξ : boxFree ξ = true) (hζ : boxFree ζ = true)
    (hle : Deriv [ξ] ζ) (hstrict : ¬ Deriv [ζ] ξ) :
    FreeHAωIn (rel (base 3) topF xω ξ) (rel (base 3) topF xω ζ) :=
  mainTheorem _ _ _ ξ ζ b3_vf rfl (fun _ => gen_vf _) bridge3 hξ hζ hle hstrict

/-- **PROVED: `NestTwo`**, depth two inside the base-3 copy. -/
theorem nestTwo : NestTwo := by
  intro ξ₁ ζ₁ ξ₂ ζ₂ ρ₁ h1 h2 h3 h4 h5 h6 h7 h8 h9
  have hx : ∀ p, atomFree (xω p) = true := fun _ => gen_vf _
  exact mainTheorem _ _ _ ξ₂ ζ₂ (atomFree_rel b3_vf rfl hx ξ₁) (atomFree_rel b3_vf rfl hx ζ₁)
    (fun p => atomFree_rel b3_vf rfl hx _) (nest _ _ _ ξ₁ ζ₁ ρ₁ bridge3 h1 h2 h3 h4 h5) h6 h7 h8 h9

/-- Cross-check of cell (i) against the theorem: the PROVED `Nest`, with the
cell's own renaming, gives `cell1_neg` again from the IPC fact `ipc_lem`. -/
theorem cell1_by_theorem :
    ¬ Deriv [rel Cells.a1F Cells.b1F Cells.x1 topF] (rel Cells.a1F Cells.b1F Cells.x1 Cells.lemF) :=
  fun h => Cells.ipc_lem (((nest _ _ _ Cells.ξc Cells.ζc Cells.ρc1 bridge3 rfl rfl Cells.hyp1_le
    Cells.hyp1_strict Cells.fresh_c1).2.2 topF Cells.lemF rfl rfl).mpr h)

/-! ## Stage 4: every finite depth, and the operations, hereditarily

Statements committed before any proof (Matthew, 2026-11-01).

The tower over a sequence of pairs `(ξ_d, ζ_d)`:

    (a₀, b₀, x₀) = (σ³⊥, ⊤, xω)
    (a_{d+1}, b_{d+1}, x_{d+1}) = (rel_d ξ_d, rel_d ζ_d, nestGen a_d b_d x_d ξ_d ζ_d (freshRen ξ_d ζ_d)),
    rel_d = rel a_d b_d x_d.

    NestAll :          ∀ d,  FreeIn a_d b_d x_d  ∧  ∀ p, x_d p variable-free
    RelConnectives :   rel commutes with ∧, ∨, → ↦ (· ↠ ·) ∧ b, ◯ ↦ ◯(·) ∧ b, ⊥ ↦ a (by rfl),
                         and rel ⊤ ⊣⊢ b
    TowerRel :         rel_d A ⊣⊢ compT d A,  compT d = rel σ³⊥ ⊤ xω ∘ coreT 0 ∘ … ∘ coreT (d-1)
    IntervalOpsAgree : [b'] ⊢ b  ⟹  ((u ↠ v) ∧ b) ∧ b' ⊣⊢ (u ↠ v) ∧ b'  and  (◯u ∧ b) ∧ b' ⊣⊢ ◯u ∧ b'
    TowerOpsAgree :    [a_d] ⊢ a_{d+1},  [a_{d+1}] ⊢ b_{d+1},  [b_{d+1}] ⊢ b_d, and the interval
                         operations of [a_{d+1}, b_{d+1}] computed inside [a_d, b_d] agree with
                         those computed in F0
    HereditaryOps :    RelConnectives ∧ TowerRel ∧ IntervalOpsAgree ∧ TowerOpsAgree

`IntervalOpsAgree` needs only `[b'] ⊢ b`; the hypotheses `[u] ⊢ b'`, `[v] ⊢ b'`
of the brief are not used. -/

/-- An interval copy: bottom `a`, top `b`, generators `x`. -/
structure ICopy where
  a : PLLFormula
  b : PLLFormula
  x : String → PLLFormula

/-- One nesting step, with the internally chosen fresh renaming `freshRen ξ ζ`. -/
def ICopy.step (c : ICopy) (ξ ζ : PLLFormula) : ICopy :=
  ⟨rel c.a c.b c.x ξ, rel c.a c.b c.x ζ, nestGen c.a c.b c.x ξ ζ (freshRen ξ ζ)⟩

/-- **The tower** over the pairs `(ξs d, ζs d)`, starting from the base-3 copy
`(σ³⊥, ⊤, xω)`. -/
def tower (ξs ζs : Nat → PLLFormula) : Nat → ICopy
  | 0 => ⟨base 3, topF, xω⟩
  | d + 1 => (tower ξs ζs d).step (ξs d) (ζs d)

/-- The hypotheses on the pairs: ◯-free, `[ξ_d] ⊢ ζ_d`, `[ζ_d] ⊬ ξ_d`. -/
def TowerHyp (ξs ζs : Nat → PLLFormula) : Prop :=
  ∀ d, boxFree (ξs d) = true ∧ boxFree (ζs d) = true ∧ Deriv [ξs d] (ζs d) ∧
    ¬ Deriv [ζs d] (ξs d)

/-- **NestAll**: at every depth the tower is a faithful interval copy of `H_ω`
with variable-free generators. -/
def NestAll : Prop :=
  ∀ ξs ζs : Nat → PLLFormula, TowerHyp ξs ζs → ∀ d : Nat,
    FreeIn (tower ξs ζs d).a (tower ξs ζs d).b (tower ξs ζs d).x ∧
      ∀ p, atomFree ((tower ξs ζs d).x p) = true

/-- **(a) The interval translation commutes with the connectives**, the
implication and `◯` of `[a, b]` being `(· ↠ ·) ∧ b` and `◯(·) ∧ b`; `⊥ ↦ a`,
and `rel ⊤ ⊣⊢ b`. -/
def RelConnectives : Prop :=
  ∀ (a b : PLLFormula) (x : String → PLLFormula),
    (∀ A B, rel a b x (A.and B) = (rel a b x A).and (rel a b x B)) ∧
    (∀ A B, rel a b x (A.or B) = (rel a b x A).or (rel a b x B)) ∧
    (∀ A B, rel a b x (A.ifThen B) = ((rel a b x A).ifThen (rel a b x B)).and b) ∧
    (∀ A, rel a b x (PLLFormula.somehow A) = (PLLFormula.somehow (rel a b x A)).and b) ∧
    rel a b x .falsePLL = a ∧
    Deriv [rel a b x topF] b ∧ Deriv [b] (rel a b x topF)

/-- The core translation at depth `d`, `rel ξ_d ζ_d (coreGen ξ_d ζ_d (freshRen ξ_d ζ_d))`. -/
def coreT (ξs ζs : Nat → PLLFormula) (d : Nat) : PLLFormula → PLLFormula :=
  rel (ξs d) (ζs d) (coreGen (ξs d) (ζs d) (freshRen (ξs d) (ζs d)))

/-- The composite `rel σ³⊥ ⊤ xω ∘ coreT 0 ∘ … ∘ coreT (d-1)`. -/
def compT (ξs ζs : Nat → PLLFormula) : Nat → PLLFormula → PLLFormula
  | 0 => rel (base 3) topF xω
  | d + 1 => fun A => compT ξs ζs d (coreT ξs ζs d A)

/-- **(b) The depth-`d` translation is one interval translation**, into
`[a_d, b_d]`, up to `⊣⊢`, for every formula. -/
def TowerRel : Prop :=
  ∀ ξs ζs : Nat → PLLFormula, TowerHyp ξs ζs → ∀ (d : Nat) (A : PLLFormula),
    Deriv [rel (tower ξs ζs d).a (tower ξs ζs d).b (tower ξs ζs d).x A] (compT ξs ζs d A) ∧
    Deriv [compT ξs ζs d A] (rel (tower ξs ζs d).a (tower ξs ζs d).b (tower ξs ζs d).x A)

/-- **(c) The interval operations of a sub-interval agree**: for `[b'] ⊢ b`,
the implication and `◯` of `[·, b']` computed inside `[·, b]` are those
computed in F0. -/
def IntervalOpsAgree : Prop :=
  ∀ b b' u v : PLLFormula, Deriv [b'] b →
    (Deriv [((u.ifThen v).and b).and b'] ((u.ifThen v).and b') ∧
      Deriv [(u.ifThen v).and b'] (((u.ifThen v).and b).and b')) ∧
    (Deriv [((PLLFormula.somehow u).and b).and b'] ((PLLFormula.somehow u).and b') ∧
      Deriv [(PLLFormula.somehow u).and b'] (((PLLFormula.somehow u).and b).and b'))

/-- **(c) on the tower**: `[a_{d+1}, b_{d+1}] ⊆ [a_d, b_d]`, and its interval
operations computed inside `[a_d, b_d]` agree with those computed in F0. -/
def TowerOpsAgree : Prop :=
  ∀ ξs ζs : Nat → PLLFormula, TowerHyp ξs ζs → ∀ d : Nat,
    Deriv [(tower ξs ζs d).a] (tower ξs ζs (d + 1)).a ∧
    Deriv [(tower ξs ζs (d + 1)).a] (tower ξs ζs (d + 1)).b ∧
    Deriv [(tower ξs ζs (d + 1)).b] (tower ξs ζs d).b ∧
    ∀ u v : PLLFormula,
      (Deriv [((u.ifThen v).and (tower ξs ζs d).b).and (tower ξs ζs (d + 1)).b]
          ((u.ifThen v).and (tower ξs ζs (d + 1)).b) ∧
        Deriv [(u.ifThen v).and (tower ξs ζs (d + 1)).b]
          (((u.ifThen v).and (tower ξs ζs d).b).and (tower ξs ζs (d + 1)).b)) ∧
      (Deriv [((PLLFormula.somehow u).and (tower ξs ζs d).b).and (tower ξs ζs (d + 1)).b]
          ((PLLFormula.somehow u).and (tower ξs ζs (d + 1)).b) ∧
        Deriv [(PLLFormula.somehow u).and (tower ξs ζs (d + 1)).b]
          (((PLLFormula.somehow u).and (tower ξs ζs d).b).and (tower ξs ζs (d + 1)).b))

/-- **The hereditary operations**: (a), (b), (c) and (c) on the tower. -/
def HereditaryOps : Prop := RelConnectives ∧ TowerRel ∧ IntervalOpsAgree ∧ TowerOpsAgree

/-! ## Stage 4: the proofs -/

/-- What the induction on the depth carries: faithfulness, variable-free
generators, variable-free bounds. -/
theorem tower_props (ξs ζs : Nat → PLLFormula) (h : TowerHyp ξs ζs) : ∀ d : Nat,
    FreeIn (tower ξs ζs d).a (tower ξs ζs d).b (tower ξs ζs d).x ∧
    (∀ p, atomFree ((tower ξs ζs d).x p) = true) ∧
    atomFree (tower ξs ζs d).a = true ∧ atomFree (tower ξs ζs d).b = true
  | 0 => ⟨bridge3, fun _ => gen_vf _, b3_vf, rfl⟩
  | d + 1 => by
      obtain ⟨hF, hx, ha, hb⟩ := tower_props ξs ζs h d
      obtain ⟨h1, h2, h3, h4⟩ := h d
      exact ⟨nest _ _ _ _ _ _ hF h1 h2 h3 h4 (fresh_freshRen _ _),
        fun _ => atomFree_rel ha hb hx _, atomFree_rel ha hb hx _, atomFree_rel ha hb hx _⟩

/-- **PROVED: `NestAll`**, every finite depth. -/
theorem nestAll : NestAll := fun ξs ζs h d =>
  ⟨(tower_props ξs ζs h d).1, (tower_props ξs ζs h d).2.1⟩

/-- **PROVED: `[a_d, b_d]` contains `H_ω` inside F0, for every `d`.** -/
theorem freeHAωIn_tower (ξs ζs : Nat → PLLFormula) (h : TowerHyp ξs ζs) (d : Nat) :
    FreeHAωIn (tower ξs ζs d).a (tower ξs ζs d).b :=
  ⟨(tower ξs ζs d).x, (tower_props ξs ζs h d).2.1, (tower_props ξs ζs h d).1⟩

/-- **PROVED: (a)**, `rel` commutes with the connectives (`rfl`), `rel ⊤ ⊣⊢ b`. -/
theorem rel_connectives : RelConnectives := fun _ _ _ =>
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl, rfl,
   Deriv.andElim2 (Deriv.iden (.head _)),
   Deriv.andIntro (Deriv.impIntro (Deriv.iden (.head _))) (Deriv.iden (.head _))⟩

/-- The bounds of a faithful copy, read in a model: `a ≤ b`, `x p ≤ b`. -/
theorem freeIn_sem {a b : PLLFormula} {x : String → PLLFormula} (hF : FreeIn a b x)
    (M : SubframeModel) :
    (∀ v, M.force v a → M.force v b) ∧ (∀ v p, M.force v (x p) → M.force v b) :=
  ⟨fun v h => sem_of_deriv (hF.2.1 "") M v (sem_of_deriv (hF.1 "") M v h),
   fun v p h => sem_of_deriv (hF.2.1 p) M v h⟩

/-- The depth-`d` translation is the composite, in every model (`rel_comp`,
iterated):

    v ⊩ rel a_d b_d x_d A   ⟺   v ⊩ compT d A. -/
theorem tower_rel_force (ξs ζs : Nat → PLLFormula) (h : TowerHyp ξs ζs) :
    ∀ (d : Nat) (A : PLLFormula) (M : SubframeModel) (v : M.W),
      M.force v (rel (tower ξs ζs d).a (tower ξs ζs d).b (tower ξs ζs d).x A) ↔
        M.force v (compT ξs ζs d A)
  | 0, _, _, _ => Iff.rfl
  | d + 1, A, M, v => by
      have hs := freeIn_sem (tower_props ξs ζs h d).1 M
      exact (rel_comp M (tower ξs ζs d).a (tower ξs ζs d).b (tower ξs ζs d).x (ξs d) (ζs d)
        (coreGen (ξs d) (ζs d) (freshRen (ξs d) (ζs d))) hs.1 hs.2 A v).trans
        (tower_rel_force ξs ζs h d (coreT ξs ζs d A) M v)

/-- **PROVED: (b)**, the depth-`d` translation is one interval translation,
up to `⊣⊢`. -/
theorem tower_rel : TowerRel := fun ξs ζs h d A =>
  ⟨deriv_of_sem fun M _ v hv => (tower_rel_force ξs ζs h d A M v).mp hv,
   deriv_of_sem fun M _ v hv => (tower_rel_force ξs ζs h d A M v).mpr hv⟩

/-- **PROVED: (c)**, the operations of a sub-interval agree. -/
theorem interval_ops_agree : IntervalOpsAgree := fun _ _ _ _ hb =>
  ⟨⟨Deriv.andIntro (Deriv.andElim1 (Deriv.andElim1 (Deriv.iden (.head _))))
      (Deriv.andElim2 (Deriv.iden (.head _))),
    Deriv.andIntro (Deriv.andIntro (Deriv.andElim1 (Deriv.iden (.head _)))
      (Deriv.cutHead (Deriv.andElim2 (Deriv.iden (.head _))) hb)) (Deriv.andElim2 (Deriv.iden (.head _)))⟩,
   ⟨Deriv.andIntro (Deriv.andElim1 (Deriv.andElim1 (Deriv.iden (.head _))))
      (Deriv.andElim2 (Deriv.iden (.head _))),
    Deriv.andIntro (Deriv.andIntro (Deriv.andElim1 (Deriv.iden (.head _)))
      (Deriv.cutHead (Deriv.andElim2 (Deriv.iden (.head _))) hb)) (Deriv.andElim2 (Deriv.iden (.head _)))⟩⟩

/-- **PROVED: (c) on the tower.** -/
theorem tower_ops_agree : TowerOpsAgree := by
  intro ξs ζs h d
  obtain ⟨hF, _, _, _⟩ := tower_props ξs ζs h d
  obtain ⟨h1, h2, h3, _⟩ := h d
  obtain ⟨hax, hxb, _⟩ := hF
  have sax : ∀ (M : SubframeModel) v p, M.force v (tower ξs ζs d).a →
      M.force v ((tower ξs ζs d).x p) := fun M v p hv => sem_of_deriv (hax p) M v hv
  have sxb : ∀ (M : SubframeModel) v p, M.force v ((tower ξs ζs d).x p) →
      M.force v (tower ξs ζs d).b := fun M v p hv => sem_of_deriv (hxb p) M v hv
  have hbb : Deriv [(tower ξs ζs (d + 1)).b] (tower ξs ζs d).b :=
    deriv_of_sem fun M _ v hv => force_rel_b M _ _ _ (fun u hu => sxb M u "" (sax M u "" hu))
      (sxb M) (ζs d) v hv
  exact ⟨rel_preserves _ _ _ sax sxb rfl h1 (Deriv.falsoElim _ (Deriv.iden (.head _))),
    rel_preserves _ _ _ sax sxb h1 h2 h3, hbb, fun u v => interval_ops_agree _ _ u v hbb⟩

/-- **PROVED: the hereditary operations.** -/
theorem hereditary_ops : HereditaryOps :=
  ⟨rel_connectives, tower_rel, interval_ops_agree, tower_ops_agree⟩

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
#axioms_within PLLND.F0.Interval.sem_of_deriv [propext, Quot.sound]
#axioms_within PLLND.F0.Interval.deriv_of_sem [propext, Quot.sound]
#axioms_within PLLND.F0.Interval.deriv_congr [propext, Quot.sound]
#axioms_within PLLND.F0.Interval.force_rel_b [propext, Quot.sound]
#axioms_within PLLND.F0.Interval.rel_iff_relB [propext, Quot.sound]
#axioms_within PLLND.F0.Interval.rel_comp [propext, Quot.sound]
#axioms_within PLLND.F0.Interval.rel_preserves [propext, Quot.sound]
#axioms_within PLLND.F0.Interval.or_eq_false_split [propext, Quot.sound]
#axioms_within PLLND.F0.Interval.boxFree_coreGen [propext, Quot.sound]
#axioms_within PLLND.F0.Interval.boxFree_rel [propext, Quot.sound]
#axioms_within PLLND.F0.Interval.atomFree_rel [propext, Quot.sound]
#axioms_within PLLND.F0.Interval.exists_max_not [propext, Quot.sound]
#axioms_within PLLND.F0.Interval.Glue.Le.trans [propext, Quot.sound]
#axioms_within PLLND.F0.Interval.Glue.VG.hered [propext, Quot.sound]
#axioms_within PLLND.F0.Interval.Glue.collapse [propext, Quot.sound]
#axioms_within PLLND.F0.Interval.core_bounds [propext, Quot.sound]
#axioms_within PLLND.F0.Interval.core_reflects [propext, Quot.sound]
#axioms_within PLLND.F0.Interval.coreLemma [propext, Quot.sound]
#axioms_within PLLND.F0.Interval.occ_size [propext, Quot.sound]
#axioms_within PLLND.F0.Interval.freshRen_occ [propext, Quot.sound]
#axioms_within PLLND.F0.Interval.fresh_freshRen [propext, Quot.sound]
#axioms_within PLLND.F0.Interval.nest [propext, Quot.sound]
#axioms_within PLLND.F0.Interval.mainTheorem [propext, Quot.sound]
#axioms_within PLLND.F0.Interval.bridge [propext, Quot.sound]
#axioms_within PLLND.F0.Interval.bridge3 [propext, Quot.sound]
#axioms_within PLLND.F0.Interval.freeHAωIn_of_above [propext, Quot.sound]
#axioms_within PLLND.F0.Interval.freeHAωIn_base3 [propext, Quot.sound]
#axioms_within PLLND.F0.Interval.nestOne [propext, Quot.sound]
#axioms_within PLLND.F0.Interval.nestTwo [propext, Quot.sound]
#axioms_within PLLND.F0.Interval.cell1_by_theorem [propext, Quot.sound]
#axioms_within PLLND.F0.Interval.tower_props [propext, Quot.sound]
#axioms_within PLLND.F0.Interval.nestAll [propext, Quot.sound]
#axioms_within PLLND.F0.Interval.freeHAωIn_tower [propext, Quot.sound]
#axioms_within PLLND.F0.Interval.rel_connectives [propext, Quot.sound]
#axioms_within PLLND.F0.Interval.freeIn_sem [propext, Quot.sound]
#axioms_within PLLND.F0.Interval.tower_rel_force [propext, Quot.sound]
#axioms_within PLLND.F0.Interval.tower_rel [propext, Quot.sound]
#axioms_within PLLND.F0.Interval.interval_ops_agree [propext, Quot.sound]
#axioms_within PLLND.F0.Interval.tower_ops_agree [propext, Quot.sound]
#axioms_within PLLND.F0.Interval.hereditary_ops [propext, Quot.sound]
