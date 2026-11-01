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

Status after stage 3 (2026-11-01).  Every pin `#axioms_within … [propext, Quot.sound]`.

| statement | theorem | status |
|-----------|---------|--------|
| **`CoreLemma`** (★) | `coreLemma` | **PROVED** |
| **`Nest`** | `nest` | **PROVED** |
| **`MainTheorem`** | `mainTheorem` | **PROVED** |
| **`Bridge`** | `bridge` | **PROVED** |
| **`Bridge3`**, `FreeIn σ³⊥ ⊤ xω` | `bridge3` | **PROVED** |
| `FreeHAωAbove b → FreeHAωIn b ⊤`; `FreeHAωIn σ³⊥ ⊤` | `freeHAωIn_of_above`, `freeHAωIn_base3` | PROVED |
| depth one inside the base-3 copy | `nestOne` | PROVED |
| **`NestTwo`**, depth two inside the base-3 copy | `nestTwo` | **PROVED** |
| `NestPLL` (◯ included) | `NestPLL` (Prop) | OPEN, not in scope |
| `CoreNoStrict` (the core lemma without `[ζ] ⊬ ξ`) | `not_coreNoStrict` | REFUTED |

Supporting lemmas, all PROVED:

| lemma | declaration |
|-------|-------------|
| soundness / completeness for `[φ] ⊢ ψ`; derivability respects forcing-equivalence | `sem_of_deriv`, `deriv_of_sem`, `deriv_congr` |
| every `rel`-image lies below `b` | `force_rel_b` |
| `v ⊩ b ⟹ (v ⊩ rel a b x A ⟺ v ⊩ relB a x A)`, ◯-free `A` | `rel_iff_relB` |
| `v ⊩ rel (rel ξ) (rel ζ) (rel ∘ y) A ⟺ v ⊩ rel (rel ξ ζ y A)`, ALL `A` | `rel_comp` |
| `a ≤ x p ≤ b`, `[A] ⊢ B ⟹ [rel A] ⊢ rel B` (◯-free) | `rel_preserves` |
| a world maximal among those refuting `ξ` | `exists_max_not` |
| the glued model; collapse to `N` on formulas without fresh atoms | `Glue.G`, `Glue.collapse` |
| `⟸` of the core lemma | `core_reflects` |
| fresh renamings exist | `fresh_freshRen` |
| side conditions | `boxFree_coreGen`, `boxFree_rel`, `atomFree_rel` |
| cross-check: `Nest` gives cell (i) again | `cell1_by_theorem` |

No theorem is sorried; the one open statement (`NestPLL`) is a `Prop` definition.

Estate check of the module: `#axiom_sweep [wip.f0FreeInterval] allowing [propext, Quot.sound]`
passes on all 138 declarations; the same sweep with `allowing []` rejects 54
of 138 (the gate watched failing).  No `Classical.choice`, no `sorry`, no
`native_decide`, no `omega`, no `simp` in the module.

## Stage 3: the proof (IPC fragment, CLAUDE.md rule 8)

The pen argument of the brief, mechanised as planned:

* `rel ξ ζ x A` against `relB`: they agree at every world forcing the top
  (`rel_iff_relB`), and every `rel`-image forces the top (`force_rel_b`).
* `⟹`: `relB_preservesω` (`f0FreeBase3`), through `rel_iff_relB`.
* `⟸` (gluing): `N` a finite countermodel of `[ζ] ⊢ ξ`, `w` maximal among the
  worlds forcing `ζ` and refuting `ξ`, `K` a finite model of `A`.  The glued
  model `Glue.G` keeps all of `N` and adds a copy of `K` below the strict
  successors of `w` (the worlds above `w` forcing `ξ`), with the old atoms at
  `w`'s values, `ρ p` true at the copy of `u` iff `u ⊩ p` and true on `N`, `S`
  as in `K` and `N`.  The collapse map (copy ↦ `w`) preserves ξ, ζ
  (`Glue.collapse`; maximality is used in the `→` case at the copy).  The
  generators `(ρ p ∨ ξ) ∧ ζ` read `K`'s valuation at the copy, and
  `relB_transferω` (`f0FreeBase3`) gives `copy(u) ⊩ rel A ⟺ u ⊩ A`.  The
  predecessors of `w` are not needed: only the cone above the copy matters.
* Transport (`nest`): `rel_comp` and the faithfulness of the outer copy.  The
  outer bounds give `a ≤ b` (through any generator).
* Main theorem: `nest` with the fresh renaming `freshRen ξ ζ`
  (`p ↦ pvar (atomBound ξ + atomBound ζ + code p)`, injective by `code_inj`
  and the UTF-8 size of `pvar`).
* Bridge: at every world `⊤` holds, so `rel b ⊤ x ≡ relB b x`.

Design for the PLL stage (METHOD.md §5): the copy of `K` keeps `K`'s own `S`
(no generator reads `S`), and `rel_comp` already holds for every formula,
`◯` included.  What `NestPLL` still needs: the collapse and the transfer with
the `◯` clause, and preservation through `relB_preservesO` of `f0FreePLL`.
It is not attempted here.

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

## Stage 4: every finite depth, and the operations, hereditarily (Matthew, 2026-11-01)

Statements committed before any proof.  The tower over a sequence of pairs
`(ξ_d, ζ_d)`, each ◯-free with `[ξ_d] ⊢ ζ_d` and `[ζ_d] ⊬ ξ_d` (`TowerHyp`):

    (a₀, b₀, x₀) = (σ³⊥, ⊤, xω)
    (a_{d+1}, b_{d+1}, x_{d+1}) = (rel_d ξ_d, rel_d ζ_d, nestGen a_d b_d x_d ξ_d ζ_d (freshRen ξ_d ζ_d))

| statement | content | status |
|-----------|---------|--------|
| `NestAll` | `∀ d, FreeIn a_d b_d x_d ∧ ∀ p, x_d p variable-free` | OPEN (statement) |
| `RelConnectives` | `rel` commutes with `∧ ∨`, `→ ↦ (· ↠ ·) ∧ b`, `◯ ↦ ◯(·) ∧ b`, `⊥ ↦ a`; `rel ⊤ ⊣⊢ b` | OPEN (statement) |
| `TowerRel` | `rel_d A ⊣⊢ compT d A`, `compT d = rel σ³⊥ ⊤ xω ∘ coreT 0 ∘ … ∘ coreT (d-1)` | OPEN (statement) |
| `IntervalOpsAgree` | `[b'] ⊢ b ⟹ ((u ↠ v) ∧ b) ∧ b' ⊣⊢ (u ↠ v) ∧ b'`, `(◯u ∧ b) ∧ b' ⊣⊢ ◯u ∧ b'` | OPEN (statement) |
| `TowerOpsAgree` | `[a_{d+1}, b_{d+1}] ⊆ [a_d, b_d]`, and the two agreements with `b = b_d`, `b' = b_{d+1}` | OPEN (statement) |
| `HereditaryOps` | the conjunction of the four above | OPEN (statement) |

`IntervalOpsAgree` uses only `[b'] ⊢ b`; the brief's `[u] ⊢ b'`, `[v] ⊢ b'` are
not needed.

## Builds

Registered in `lakefile.toml` (the `wip` glob list, after `wip.f0FreePLL`).
Bare `lake build` skips `wip` modules: build with
`gtimeout 3600 lake build wip.f0FreeInterval`.

Build cache seeded by `cp -Rc` from `~/Lean/nightly/lax-logic-in-lean/.lake`
(v4.31.0 at `d5dcf0e`); no other module rebuilt.

| stage | command | exit | wall time | free disk before |
|-------|---------|------|-----------|------------------|
| 1 | `gtimeout 3600 lake build wip.f0FreeInterval` | 0 | 14.9 s | 106,104 MB |
| 2 | `gtimeout 3600 lake build wip.f0FreeInterval` | 0 | 15.6 s | 106,088 MB |
| 3 | `gtimeout 3600 lake build wip.f0FreeInterval` | 0 | 14.3 s | 106,107 MB |

Proof bodies were developed first with `gtimeout … lake env lean` on scratch
copies (about 12 s each).  Skips and caps: none.  No `lake exe` and no tool
runs: the countermodels are designed tables, checked by `decide +kernel`.
