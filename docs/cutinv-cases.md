# `CutInv`: the polarisation case list, and the cells that test it

Route (B), WP `CutInv`, refutation stage.  Worktree
`.claude/worktrees/agent-a0ff6eba1fe2c70ba`, base `6db8f98`.
Started 2026-09-06 00:35 BST.

This file answers the `CutInv` obligation of `docs/ui-ljfo-clause-table.md`
§4.19 **from the rules of LJF◯**, with designed witness cells, not by
enumeration.  Every cell is a `def`/`example` in `wip/cutinv_cells.lean`.

## 0. The obligation and the statement under test

    CutInv := ∀ (Γ Δ : List Neg) (j : JD) (N ψ : Neg),
                Inv Γ [] .tru N → Inv (N :: Δ) [] j ψ → Inv (Γ ++ Δ) [] j ψ

Erasure is sound (`LJFO.Inv.sound`) and `LaxND` composes derivations without
cut (`LJFO.subst1` = `impIntro` then `impElim`), so the bridge route through
PLL closes `CutInv` as soon as the converse arrow is available at the
polarised sequents route (B) actually writes down.  That converse is

    PolInv := ∀ (Γ : List Neg) (j : JD) (ψ : Neg),
                Nonempty (LaxND (eraseCtx Γ) (goal j (eraseNeg ψ))) →
                Nonempty (Inv Γ [] j ψ)

`LJFO.FocalizationPLL` gives `PolInv` only on the image of `negOfO`:

    FocalizationPLL : ∀ Γ φ, Nonempty (LaxND Γ φ) →
                        Nonempty (Inv (Γ.map negOfO) [] .tru (negOfO φ))

— context and goal canonically polarised, and `j = .tru` only.

## 1. The canonical polarisation invariant (CPI)

Read off `posOfO`/`negOfO` (`LJF/OBridge.lean` §4b).  For every
`φ : PLLFormula`, exactly one of:

* **positive head** (`φ = a`, `⊥`, `φ₁ ∨ φ₂`):
  `negOfO φ = ↑(posOfO φ)` and `posOfO φ ∈ {a, ⊥, posOfO φ₁ ∨ posOfO φ₂}`;
* **negative head** (`φ = φ₁ ∧ φ₂`, `φ₁ ⊃ φ₂`, `◯φ₁`):
  `posOfO φ = ↓(negOfO φ)` and `negOfO φ ∈ {∧, ⊃, ◯}`.

Hence in the image of the polarisation **`↑` never wraps a `↓` and `↓` never
wraps an `↑`**: there is no double shift.  The two shapes outside the image
are therefore exactly

    ↓↑P   the POSITIVE DELAY      (a `Pos`; `invertPos (↓↑P) = [[↑P]]`)
    ↑↓N   the NEGATIVE DELAY      (a `Neg`)

Route (B) writes both: `interpP`'s parked shapes (`LJF/OFuelP.lean` 60–110)
include `simp : ↓↑P′ ⊃ N` and `dyk : ↓(Q′ ⊃ N′) ⊃ N`, and the ∃p read-off
(lines 160–210) builds row goals `↑↓(Q′ ⊃ N′)`, `↑↓◯Q′`, and boxes
`◯↓(…)`.  So `CutInv`'s bridge route is applied off the image of `negOfO`,
and `PolInv` is exactly what has to be checked.

## 2. The step list

A **step** is one place where `focalizeSCO`/`focalizeO` (`LJF/OBridge.lean`
lines 380–441) relies on CPI — a hypothesis or goal having literally the
shape `negOfO`/`posOfO` produce.  Steps S1–S10 are ◯-free (the LJF/IPC
rules, judgment `tru`); S11–S14 are the ◯ steps.

### The ◯-free steps

| # | rule of `SCh` | what `focalizeSCO` uses | reliance on CPI | a delay at that position |
|---|---|---|---|---|
| **S1** | `init` | `.stable (.rfoc (.init …))` | goal `negOfO a = ↑(atom a)` is a shift, so `Inv … (.up _)` closes by `stable`; hypothesis is **literally** `↑(atom a)`, which is what `RFocus.init` demands | hypothesis `↑↓↑a`: `init` cannot fire |
| **S2** | `botL` | `nBotElim (negOfO C) …` | `negOfO ⊥ = ↑⊥ = nBot`, a **shifted** hypothesis, so `upMerge` applies with the empty branch family | hypothesis `↑↓↑⊥`: not `↑R`-shaped, `upMerge` does not apply |
| **S3** | `andR` | `.andR d₁ d₂` | `negOfO (φ∧ψ) = negOfO φ ∧ negOfO ψ`: goal is a **negative** conjunction, `andR` applies directly | goal `↑↓(M∧N)`: `andR` cannot apply (goal is `.up _`) |
| **S4** | `andL` | `simHyp` ×2 with `.and1`/`.and2` | the hypothesis is a negative conjunction, **focusable** by `and1`/`and2` | hypothesis `↑↓(M∧N)`: `LFoc … (↑↓(M∧N))` can only be `rel` |
| **S5** | `orR1`/`orR2` | `.stable (stabOr1 (stabOfInvO A d))` | `negOfO (φ∨ψ) = ↑(posOfO φ ∨ posOfO ψ)`; **`stabOfInvO` is the goal-side shift-transfer lemma**, proved by a six-way split on `φ` that is exactly CPI | disjunct `↓↑P`: no `φ` polarises to it, so no arm of `stabOfInvO` fits |
| **S6** | `orL` | `upMerge` + `branchInO`/`branchLFocO` | **`branchLFocO` is the hypothesis-side shift-transfer lemma**, split into `upBranchLFocO` (positive head) and `downBranchLFocO` (negative head) — the two CPI families | disjunct `↓↑P`: in neither family; and `invertPos (↓↑P) = [[↑P]]` differs from `invertPos (posOfO ⌊P⌋)` |
| **S7** | `impR` | `.impR (shiftInO A d)` | `shiftInO` turns the hypothesis `negOfO φ` into the pending positive `posOfO φ`; `invBranches (posOfO φ)` + `branchInO` | antecedent `↓↑P` — route (B)'s `simp` shape `↓↑P′ ⊃ N` |
| **S8** | `impL` | `.impL (stabOfInvO A (d₁.wk hs)) lf` under `simHyp` | `LFoc.impL`'s left premise is `Stab Γ .tru (posOfO φ)`, produced from `Inv Γ [] .tru (negOfO φ)` by `stabOfInvO` | antecedent `↓↑P`; succedent `↑↓M` — route (B)'s `dyk` shape |
| **S9** | — (the positive delay) | — | `invertPos` and `stabOfInvO`/`branchLFocO` are the only consumers of positive shape | `↓↑P` as a focused positive, as a pending positive, and as an antecedent |
| **S10** | — (the negative delay) | — | `stabOfInvO`, `unStable`, `andROf`/`impROf` | `↑↓N` as a goal and as a hypothesis |

### The ◯ steps

| # | rule | what `focalizeSCO` uses | reliance on CPI | a delay at that position |
|---|---|---|---|---|
| **S11** | `laxR` ↦ `circR` | `.circR (.stable (.laxOf (stabOfInvO A d)))` | `negOfO (◯φ) = ◯(posOfO φ)`: the box body is a **positive**, so after `circR` the goal is `↑(posOfO φ)` and `stable` applies | body `↓↑P` — route (B)'s `◯↓↑P`; and goal `↑↓N` under `circR` |
| **S12** | `laxL` ↦ `circL` | `.circR (.stable (.lfoc hA (.circL (shiftInO A (circInv d)))))` | the hypothesis is **literally** `◯(posOfO φ)`, which is what `LFoc.circL` demands; `circInv` needs the goal to be `.circ _` | hypothesis `↑↓◯Q`: `circL` cannot fire; body `↓↑P` |
| **S13** | `laxOf` | inside S11 | `laxOf : Stab Γ .tru P → Stab Γ .lax P` is the only route from truth into the lax phase | a negative delay `↑↓N` at a lax goal is reachable ONLY through `laxOf` or `circL` |
| **S14** | the `lax` judgment itself | `circR` always sets a `↑P` goal | **`Inv Γ Ω .lax N` is used by the calculus only for `N = ↑P` / `◯P`** | a naked `↑`-free negative goal at `lax` |

