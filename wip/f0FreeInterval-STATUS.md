# wip/f0FreeInterval.lean — status

The nested relativisation of the free Heyting algebra `H_ω` inside F0, the
closed fragment of PLL.  Campaign approved by Matthew 2026-11-01; brief from
the LaxLogic manager the same day.  Follow-up to `wip/f0FreeBase3.lean`
(`freeHAωAbove_base3 : FreeHAωAbove (base 3)`, the copy `relB σ³⊥ xω` of `H_ω`
in `[σ³⊥, ⊤]`).  Public order theory about F0.

## Stage 1: the statements (committed before any proof, METHOD.md §1)

Interval translation for `[a, b]` with generators `x : String → PLLFormula`:

    rel a b x ⊥ = a,   rel a b x p = x p,   ∧, ∨ componentwise,
    rel a b x (A → B) = (rel A ↠ rel B) ∧ b,   rel a b x (◯A) = ◯(rel A) ∧ b

    FreeIn a b x :  (∀ p, [a] ⊢ x p) ∧ (∀ p, [x p] ⊢ b) ∧
                      ∀ A B ◯-free,  [A] ⊢ B  ⟺  [rel a b x A] ⊢ rel a b x B
    FreeHAωIn a b : ∃ x, (∀ p, x p variable-free) ∧ FreeIn a b x

    Fresh ρ ξ ζ :   ρ injective, no ρ p occurs in ξ or ζ
    coreGen ξ ζ ρ p = (ρ p ∨ ξ) ∧ ζ
    nestGen a b x ξ ζ ρ p = rel a b x (coreGen ξ ζ ρ p)

    CoreLemma :   ξ, ζ ◯-free, [ξ] ⊢ ζ, [ζ] ⊬ ξ, Fresh ρ ξ ζ  ⟹  FreeIn ξ ζ (coreGen ξ ζ ρ)
    Nest :        FreeIn a b x, ξ, ζ ◯-free, [ξ] ⊢ ζ, [ζ] ⊬ ξ, Fresh ρ ξ ζ
                    ⟹  FreeIn (rel a b x ξ) (rel a b x ζ) (nestGen a b x ξ ζ ρ)
    MainTheorem : a, b, x variable-free, FreeIn a b x, ξ, ζ ◯-free, [ξ] ⊢ ζ, [ζ] ⊬ ξ
                    ⟹  FreeHAωIn (rel a b x ξ) (rel a b x ζ)
    Bridge :      (∀ p, [b] ⊢ x p), relB b x faithful on ◯-free sequents  ⟹  FreeIn b ⊤ x
    Bridge3 :     FreeIn σ³⊥ ⊤ xω
    NestTwo :     depth two inside the base-3 copy

    OPEN (PLL stage, not in scope):  NestPLL, `Nest` for all formulas, ◯ included

## Status table

| statement | declaration | status |
|-----------|-------------|--------|
| `CoreLemma` | `CoreLemma` (Prop) | OPEN (stage 1) |
| `Nest` | `Nest` (Prop) | OPEN (stage 1) |
| `MainTheorem` | `MainTheorem` (Prop) | OPEN (stage 1) |
| `Bridge`, `Bridge3` | `Bridge`, `Bridge3` (Props) | OPEN (stage 1) |
| `NestTwo` | `NestTwo` (Prop) | OPEN (stage 1) |
| `NestPLL` | `NestPLL` (Prop) | OPEN, not in scope |

No theorem is sorried; every open statement is a `Prop` definition.

## Stage 2: the designed cells (refutation stage, CLAUDE.md rules 7 and 9)

Three cells read off the pen argument; no sweep.  Every cell kernel-checked,
pins `[propext, Quot.sound]`.  Atoms with small codes keep the base-3
generators `xω a = gen (code a)` evaluable: `"" ↦ gen 0`, `"\x00" ↦ gen 1`,
`"\x01" ↦ gen 2`, `"\x02" ↦ gen 3`.

| cell | statement | declaration | verdict |
|------|-----------|-------------|---------|
| (i) hypotheses | `ξ = p₀ ∧ p₁`, `ζ = p₁` (`p₀ = ""`, `p₁ = "\x00"`): `[ξ] ⊢ ζ`, `[ζ] ⊬ ξ`, `Fresh ρc1 ξ ζ` | `Cells.hyp1_le`, `Cells.hyp1_strict`, `Cells.fresh_c1` | PROVED |
| (i) non-theorem | `[⊤] ⊬ p ∨ ¬p` and `[rel₁ ⊤] ⊬ rel₁(p ∨ ¬p)`, `rel₁ = rel a₁ b₁ x₁`, `[a₁, b₁] = [rel σ³⊥ ⊤ xω ξ, rel σ³⊥ ⊤ xω ζ]`, `x₁ = nestGen σ³⊥ ⊤ xω ξ ζ ρc1` | `Cells.ipc_lem`, `Cells.cell1_neg` | **PASS** (12-world table `gadW 2 _ K1`) |
| (i) theorem | `[⊤] ⊢ (p ∧ ¬p) → q` and `[rel₁ ⊤] ⊢ rel₁((p ∧ ¬p) → q)` | `Cells.ipc_exf`, `Cells.cell1_pos` | **PASS** (a derivation; uses `[a₁] ⊢ x₁ q`, `Cells.bound1`) |
| (i) gate | the table of (i) does not refute the transferred theorem | `Cells.gate_watch` | watched failing |
| (ii) hypotheses | `ξ₂ = ⊥`, `ζ₂ = p`: `[⊥] ⊢ p`, `[p] ⊬ ⊥`, `Fresh ρc2 ⊥ p` | `Cells.hyp2_le`, `Cells.hyp2_strict`, `Cells.fresh_c2` | PROVED |
| (ii) non-theorem | `[rel₂ ⊤] ⊬ rel₂(p ∨ ¬p)`, `rel₂ = rel a₂ b₂ x₂`, `[a₂, b₂] = [rel₁ ⊥, rel₁ p]`, `x₂ = nestGen a₁ b₁ x₁ ⊥ p ρc2` | `Cells.cell2_neg` | **PASS** (14-world table `gadW 3 _ K2`) |
| readings | `gen r` reads the atom of code `r` at every copy | `Cells.reads_K1`, `Cells.reads_K2` | PROVED |
| (iii) negative | `ξ = ζ`: `[rel a a x ⊤] ⊢ rel a a x ⊥`, `[⊤] ⊬ ⊥`, hence `¬ FreeIn a a x` | `rel_top_bot_diag`, `ipc_top_bot`, `cell_diag` | **FAIL, as designed** |
| (iii) the core lemma without `[ζ] ⊬ ξ` | `CoreNoStrict` | `not_coreNoStrict` | **REFUTED** (`ξ = ζ = ⊥`, `ρ = id`) |
| (iii) base-3 instance | `ξ = ζ = p₀ ∧ p₁` nested in the base-3 copy is not faithful | `cell3_base3` | **FAIL, as designed** |

The tables are the pen proof's construction: the IPC countermodel `K1` of
`[rel ξ ζ y ⊤] ⊢ rel ξ ζ y (p ∨ ¬p)` is the gluing of the two-world chain
refuting `p ∨ ¬p` into the one-world countermodel of `[ζ] ⊢ ξ`; `K2` is the
gluing done twice.  Then the base-3 gadget of `f0FreeBase3` over `K`, written
as a table (`gadW R rd K`: upper worlds `e₀ n₀ L₀ … L_R f m₀ … m_R kn`, copies
of `K` in `S` iff `k ⊮ ""`, seeing the reader `m_r` iff `k` refutes the atom
of code `r`).

No cell refutes a statement of stage 1: proceed to stage 3.

## Builds

Registered in `lakefile.toml` (the `wip` glob list, after `wip.f0FreePLL`).
Bare `lake build` skips `wip` modules: build with
`gtimeout 3600 lake build wip.f0FreeInterval`.
