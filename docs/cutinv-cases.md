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

## 3. The cells, and the hand analysis — the ◯-free block (S1–S10)

Notation: `Γ ⇒ᵗ ψ` is `Inv Γ [] .tru ψ`, `Γ ⇒ˡ ψ` is `Inv Γ [] .lax ψ`;
`↑`/`↓` are `Neg.up`/`Pos.down`; `a b c` are atoms.  Lean names are the
`def`s of `wip/cutinv_cells.lean`.

### S1 — `init` / identity

| cell | sequent | erasure | verdict |
|---|---|---|---|
| 1.1 `s1_hyp_delay` | `↑↓↑a ⇒ᵗ ↑a` | `a ⊢ a` | **PASS** |
| 1.2 `s1_goal_delay` | `↑a ⇒ᵗ ↑↓↑a` | `a ⊢ a` | **PASS** |
| 1.3 `s1_under_ant` | `↓↑a ⊃ ↑b, ↑a ⇒ᵗ ↑b` | `a ⊃ b, a ⊢ b` | **PASS** |

*Analysis.*  In 1.1 `RFocus.init` **cannot** fire: it demands
`↑(atom a) ∈ Γ` and the context holds `↑↓↑a`.  The derivation goes
`stable`, `lfoc` on `↑↓↑a`, `LFoc.rel` (the only `LFoc` rule for a shifted
hypothesis), which puts `↓↑a` in the inversion queue, then `downL`, which
puts `↑a` in the context, and now `init` fires.  So the shift-insertion
lemma of S1 is *left delay elimination*: a hypothesis `↑↓M` is turned into
the hypothesis `M` by `lfoc`/`rel`/`downL`.  In 1.2 the dual holds by
`stable`/`rfoc`/`rel`: `Stab Γ j (↓N)` is introduced from `Inv Γ [] j N`.
1.3 is route (B)'s `simp` shape `↓↑P′ ⊃ N` as a hypothesis: `LFoc.impL`'s
left premise `Stab Γ .tru (↓↑a)` is discharged by `rfoc`/`rel`/`stable`
over the ordinary `init`.

### S2 — `botL`

| cell | sequent | erasure | verdict |
|---|---|---|---|
| 2.1 `s2_bot_delay` | `↑↓↑⊥ ⇒ᵗ ↑a` | `⊥ ⊢ a` | **PASS** |
| 2.2 `s2_bot_delay_imp` | `↑↓↑⊥ ⇒ᵗ (↓↑a ⊃ ↑b)` | `⊥ ⊢ a ⊃ b` | **PASS** |

*Analysis.*  `nBotElim` demands `nBot = ↑⊥ ∈ Γ` and does not apply.  Both
derivations first eliminate the negative delay (as in 1.1), reaching a
context with `↑⊥`, and then use `LFoc.rel` + `flsL`: the branch family of
`invertPos .fls` is empty, which is `upMerge`'s ex-falso case done by hand.
2.2 additionally shows the delay elimination commuting past `impR`/`downL`,
i.e. that the lemma must be stated with a non-empty inversion queue.

### S3 — `andR`

| cell | sequent | erasure | verdict |
|---|---|---|---|
| 3.1 `s3_and_goal_delay` | `↑a ⇒ᵗ ↑↓(↑a ∧ ↑a)` | `a ⊢ a ∧ a` | **PASS** |
| 3.2 `s3_and_conj_delay` | `↑a ⇒ᵗ (↑↓↑a ∧ ↑a)` | `a ⊢ a ∧ a` | **PASS** |

*Analysis.*  In 3.1 `andR` is **not** applicable — the goal is `↑P`, so
inversion is already over and the sequent is stable.  The derivation is
`stable`, `rfoc`, `rel`, and only then `andR`.  This is the goal-side
delay-elimination lemma `Inv Γ [] j N → Inv Γ [] j (↑↓N)`, whose converse
(needed when the delay sits in the *hypothesis* of `CutInv`) is the
`routeStab` traversal, not a pattern match: a `Stab Γ j (↓N)` may be built
by `lfoc` rather than `rfoc`.

### S4 — `andL`

| cell | sequent | erasure | verdict |
|---|---|---|---|
| 4.1 `s4_andL_delay` | `↑↓(↑a ∧ ↑b) ⇒ᵗ ↑a` | `a ∧ b ⊢ a` | **PASS** |
| 4.2 `s4_andL_inner` | `(↑a ∧ ↑↓↑b) ⇒ᵗ ↑b` | `a ∧ b ⊢ b` | **PASS** |

*Analysis.*  4.1: `and1`/`and2` cannot fire on `↑↓(M∧N)` — `LFoc` on a
shifted hypothesis is `rel` only — so the conjunction has to be re-inverted
through the queue (`rel`, `downL`) before it becomes focusable.  4.2 shows
the dual: the delay inside a conjunct is eliminated *after* the projection,
so the two eliminations interleave and the lemma must be mutual with the
`LFoc` traversal.

### S5 — `orR`

| cell | sequent | erasure | verdict |
|---|---|---|---|
| 5.1 `s5_or_disj_delay` | `↑a ⇒ᵗ ↑(↓↑a ∨ b)` | `a ⊢ a ∨ b` | **PASS** |
| 5.2 `s5_or_delay_both` | `↑b ⇒ᵗ ↑(↓↑a ∨ ↓↑b)` | `b ⊢ a ∨ b` | **PASS** |

*Analysis.*  This is the step where `stabOfInvO` is consumed.  Its six arms
are indexed by `φ : PLLFormula`; `↓↑a` is the polarisation of no `φ`, so no
arm fits.  The replacement is a general lemma
`Stab Γ j P → Stab Γ j (↓↑P)`, provable by `routeStab` with the
continuation `fun _ r => .rfoc (.rel (.stable (.rfoc r)))` — every right
focus on `P` is rewrapped, and the `lfoc`/`laxOf` spine is traversed.  The
cells above are its two-atom instances, written directly.

### S6 — `orL`, and S7 — `impR`

| cell | sequent | erasure | verdict |
|---|---|---|---|
| 6.1 `s6_delay_hides_split` | `⇒ᵗ ↓↑(a ∨ b) ⊃ ↑(b ∨ a)` | `⊢ (a∨b) ⊃ (b∨a)` | **PASS** |
| 6.2 `s6_delay_ant_choice` | `↓↑(a ∨ b) ⊃ ↑c, ↑a ⇒ᵗ ↑c` | `(a∨b) ⊃ c, a ⊢ c` | **PASS** |
| 6.3 `s6_delay_ant_hyp` | `↓↑(a ∨ b) ⊃ ↑c, ↑(a ∨ b) ⇒ᵗ ↑c` | `(a∨b) ⊃ c, a∨b ⊢ c` | **PASS** |

*Analysis.*  6.1 is the cell that shows what a positive delay actually
does.  Canonically, `(a∨b) ⊃ (b∨a)` polarises to `.imp (a ∨ b) (↑(b∨a))`
and `impR` puts the disjunction straight into the inversion queue, where
`orL` splits it.  With the delay, `impR` puts `↓↑(a∨b)` into the queue,
`downL` fires and the *hypothesis* `↑(a∨b)` appears; the case split is then
recovered by **left focus**: `lfoc` on `↑(a∨b)` with `LFoc.rel`, which
returns the disjunction to the queue, and `orL` splits it there.  That
recovery is exactly `stableFire`/`upMerge`, and it is the shift-insertion
lemma of S6/S7:

    invertPos (↓↑P) = [[↑P]]        one branch, the shifted hypothesis
    invertPos (posOfO ⌊P⌋)          the branches of P itself

    stableFire : ↑R ∈ Δ → (∀ b ∈ invertPos R, Stab (b ++ Δ) j P₀) → Stab Δ j P₀

so the single delayed branch **covers** every canonical branch.  6.2/6.3
put the delay in an antecedent (route (B)'s `simp` shape) and confirm that
`LFoc.impL`'s left premise `Stab Γ .tru (↓↑(a∨b))` is discharged either by
choosing a disjunct (6.2) or by left-focusing a shifted hypothesis (6.3) —
i.e. the delay does not force an early choice.

### S8 — `impL`

| cell | sequent | erasure | verdict |
|---|---|---|---|
| 8.1 `s8_dyk_delay` | `↓(↓↑a ⊃ ↑b) ⊃ ↑c, ↑b ⇒ᵗ ↑c` | `((a ⊃ b) ⊃ c), b ⊢ c` | **PASS** |
| 8.2 `s8_succ_delay` | `↓↑a ⊃ ↑↓↑b, ↑a ⇒ᵗ ↑b` | `a ⊃ b, a ⊢ b` | **PASS** |

*Analysis.*  8.1 is route (B)'s `dyk` shape `↓(Q′ ⊃ N′) ⊃ N` with a delayed
inner antecedent; the left premise of `impL` is `Stab Γ .tru (↓(↓↑a ⊃ ↑b))`,
discharged by `rfoc`/`rel`/`impR`/`downL` — a whole inversion phase inside
a focus, which is what makes the `dyk` row expensive but not blocked.  8.2
puts the negative delay in the *succedent* of the focused implication, where
`LFoc.rel` re-enters inversion after the focus.

### S9/S10 — the two delays in isolation

| cell | sequent | erasure | verdict |
|---|---|---|---|
| 9.1 | `Stab Γ j P → Stab Γ j (↓↑P)` — instance `s1_goal_delay` | `a ⊢ a` | **PASS** (= 1.2) |
| 10.1 | `↑↓N` as hypothesis — instances `s1_hyp_delay`, `s2_bot_delay`, `s4_andL_delay` | — | **PASS** |
| 10.2 `s10_double_delay` | `↑↓↑↓↑a ⇒ᵗ ↑a` | `a ⊢ a` | **PASS** |

*Analysis.*  10.2 is the "slightly larger than minimal" cell asked for: two
stacked negative delays, eliminated by two `lfoc`/`rel`/`downL` rounds.  It
confirms that the elimination is a recursion on the formula, not a single
unfolding.

## 4. The ◯ block (S11–S14)

| cell | sequent | erasure | verdict |
|---|---|---|---|
| 11.1 `s11_box_delay_body` | `↑a ⇒ᵗ ◯↓↑a` | `a ⊢ ◯a` | **PASS** |
| 11.2 `s11_box_from_box` | `◯a ⇒ᵗ ◯↓↑a` | `◯a ⊢ ◯a` | **PASS** |
| 11.3 `s11_lax_neg_delay` | `⇒ᵗ ◯↓(↑⊥ ⊃ ↑⊥)` | `⊢ ◯(⊥ ⊃ ⊥)` | **PASS** |
| 12.1 `s12_circL_delay_body` | `◯↓↑a ⇒ᵗ ◯a` | `◯a ⊢ ◯a` | **PASS** |
| 12.2 `s12_circL_then_imp` | `◯a, ↓↑a ⊃ ↑b ⇒ᵗ ◯b` | `◯a, a ⊃ b ⊢ ◯b` | **PASS** |
| 12.3 `s12_box_behind_delay` | `↑↓◯a ⇒ᵗ ◯a` | `◯a ⊢ ◯a` | **PASS** |
| 13.1 `s13_laxOf` | `↑a ⇒ᵗ ◯a` | `a ⊢ ◯a` | **PASS** |
| 13.2 `s13_cimp` | `↓◯a ⊃ ↑b, ◯a ⇒ᵗ ↑b` | `(◯a ⊃ b), ◯a ⊢ b` | **PASS** |
| 13.3 `s13_lax_direct` | `↑a ⇒ˡ ↑a` | `a ⊢ ◯a` | **PASS** |
| **14.1** `s14_refute_nTop` | `⇒ˡ (↑⊥ ⊃ ↑⊥)` | `⊢ ◯(⊥ ⊃ ⊥)` | **REFUTES `PolInv`** |
| **14.2** `s14_refute_and` | `↑a ⇒ˡ (↑a ∧ ↑a)` | `a ⊢ ◯(a ∧ a)` | **REFUTES `PolInv`** |
| 14.3 `s14_contrast` | `⇒ˡ ↑↓(↑⊥ ⊃ ↑⊥)` | `⊢ ◯(⊥ ⊃ ⊥)` | **PASS** |

*Analysis of S11–S13.*  11.2 is the composite route (B) actually walks:
`circR` opens the lax phase with goal `↑↓↑a`, the box `◯a` is left-focused
by `circL` (available only at `lax`), its body `a` enters the queue,
`atomL` puts `↑a` in the context, and the delayed goal is closed by
`laxOf` over the ordinary `init`.  11.3 and 12.3 are the two shapes where a
delay meets a modal rule and the rule cannot fire directly: a *negative*
delay at a lax goal (`↑↓(Q ⊃ N)`) is closed only through `laxOf`, and a box
behind a negative delay (`↑↓◯a`) must be un-delayed by `lfoc`/`rel`/`downL`
before `circL` can fire.  Both are derivable; neither is a counterexample.

*Analysis of S14 — the refutation.*  Inspect the constructors of `Inv` with
`Ω = []`, `j = .lax` and a goal that is neither `↑P` nor `◯P`:

* `impR` concludes at `.tru` — the flag is written into the rule;
* `andR` concludes at `.tru`;
* `circR` concludes `.circ _`;
* `stable` concludes `.up _`;
* `orL`, `flsL`, `downL`, `atomL` all require `Ω = _ :: _`.

No constructor applies, so

    Inv Γ [] .lax (M ∧ N)   and   Inv Γ [] .lax (Q ⊃ N)   are EMPTY.

Their erasures are not.  `eraseNeg (↑⊥ ⊃ ↑⊥) = ⊥ ⊃ ⊥` and
`goal .lax (⊥ ⊃ ⊥) = ◯(⊥ ⊃ ⊥)`, and `LaxND [] (◯(⊥ ⊃ ⊥))` is inhabited by
`laxIntro (impIntro (iden …))`.  So **`PolInv` as stated is REFUTED**, with
both parts kernel-checked: the `LaxND` term, and `IsEmpty` by an exhaustive
`cases` on the would-be derivation.

This is not a defect of the calculus and not a counterexample to
`CutInv`.  The development already knows the fact — `upMergeJ`'s docstring
(`LJF/OCore.lean` 2132) reads "at `lax` the goal can only be a shift or a
box — `⊃` and `∧` have no lax right rules".  What the cells establish is
that the *statement* `PolInv` overshoots: `Inv.sound` types
`Inv Γ Ω .lax N` at `◯⌊N⌋` for every `N`, but the calculus only ever enters
`lax` with an `↑P` goal (`circR`'s premise) or a `◯P` goal (`circR` again).
Cell 14.3 makes the point exactly: the *same* erasure `◯(⊥ ⊃ ⊥)` IS
derivable at `lax` once the goal carries its shift, `↑↓(↑⊥ ⊃ ↑⊥)`.

**Consequence for `CutInv`.**  `CutInv`'s second premise and its conclusion
carry the *same* `j` and the *same* `ψ`.  At `j = .lax` with `ψ` an `imp` or
an `and`, the premise `Inv (N :: Δ) [] .lax ψ` is itself empty, so `CutInv`
holds vacuously there (`s14_cutinv_vacuous`).  `CutInv` therefore does not
need `PolInv`; it needs the two restricted forms

    PolInvT := ∀ Γ ψ,   Nonempty (LaxND (eraseCtx Γ) (eraseNeg ψ)) →
                        Nonempty (Inv Γ [] .tru ψ)
    PolInvL := ∀ Γ P,   Nonempty (LaxND (eraseCtx Γ) (◯ (erasePos P))) →
                        Nonempty (Inv Γ [] .lax (↑P))

(the `ψ = ◯P` case of `lax` reduces to `PolInvL` by `circR`/`circInv`).

## 5. Conclusion

**On `PolInv`.**  REFUTED as stated (cells 14.1, 14.2), for a reason that has
nothing to do with double shifts: the `lax` flag admits only shifted and
boxed goals.  Restricted to `PolInvT` + `PolInvL` the twelve remaining steps
all PASS: every designed cell carrying a positive delay `↓↑P` or a negative
delay `↑↓N`, at every position the completeness proof is sensitive to, has a
kernel-checked focused derivation.  So the cells give no evidence against
polarisation invariance for LJF◯, and positive evidence for it at each step
— including the three modal steps, which is where the Liang–Miller argument
had not been checked.

**The ◯-free fragment as a result in its own right.**  S1–S10, judgment
`tru`, ◯ absent: seventeen designed cells, all PASS, all kernel-checked at
`[]` (no axioms whatever — they are closed terms of an inductive type).  This
is Liang–Miller's "delays are inert" for the ◯-free part of LJF◯, confirmed
cell by cell; the pattern of every derivation is one of exactly two moves —
*left delay elimination* (`lfoc`/`rel`/`downL` on `↑↓M`; `downL` on a queued
`↓↑P`) and *right delay introduction* (`stable`/`rfoc`/`rel`) — with
`routeStab`/`stableFire` supplying them when the shift sits under a focus
rather than at the root.

**Route recommendation: (a), prove `PolInvT` + `PolInvL`.**  Reasons drawn
from the cells: (i) every cell's derivation is one of the two delay moves
above, so the lemmas are uniform in the formula and do not need a
cut-elimination measure; (ii) `LJF/OCore.lean` already contains every
traversal the proof needs (`routeStab`/`routeLFoc`/`routeInv`, `simHyp`,
`extract`, `invBranches`, `stableFire`, `upMerge`/`upMergeJ`), all proved
and all flag-threaded; (iii) direct cut admissibility (route b) would have
to re-prove those traversals with a cut measure and would additionally have
to handle the `lax` flag's asymmetry, which route (a) gets for free from
`PolInvL`'s restricted shape.

### The lemma list a route-(a) proof consists of

Write `⟦N⟧ := negOfO (eraseNeg N)` and `⟦P⟧ := posOfO (erasePos P)` for the
canonical form (`erase_polarise` gives `⌊⟦N⟧⌋ = ⌊N⌋`).  One mutual block,
recursion on the formula with the derivation as the inner measure:

    (A)  Inv Γ Ω j ⟦N⟧      → Inv Γ Ω j N            goal transfer
    (A′) Inv Γ Ω j N        → Inv Γ Ω j ⟦N⟧
    (B)  Inv (⟦N⟧ :: Γ) Ω j C → Inv (N :: Γ) Ω j C   hypothesis transfer
    (B′) Inv (N :: Γ) Ω j C   → Inv (⟦N⟧ :: Γ) Ω j C
    (C)  Inv Γ (⟦P⟧ :: Ω) j C → Inv Γ (P :: Ω) j C   pending-positive transfer
    (C′) Inv Γ (P :: Ω) j C   → Inv Γ (⟦P⟧ :: Ω) j C
    (D)  Stab Γ j ⟦P⟧       → Stab Γ j P             focused-positive transfer
    (D′) Stab Γ j P         → Stab Γ j ⟦P⟧

with the delay cases discharged as the cells do them:

* (D) at `P = ↓↑P′`: `routeStab (fun _ r => .rfoc (.rel (.stable (.rfoc r))))`
  — cells 1.2, 5.1, 5.2, 9.1;
* (C) at `P = ↓↑P′`: `invBranches` + `extract` + `stableFire` — cell 6.1;
* (B) at `N = ↑↓M`: `lfoc`/`rel`/`downL` then (B) at `M` — cells 1.1, 4.1,
  10.2, 12.3;
* (A) at `N = ↑↓M`: `stable`/`rfoc`/`rel` then (A) at `M` — cells 3.1, 11.3;
* (A) at `N = ◯P`: `circR` then (A) at `↑P` with `j := .lax` — cells 11.1,
  11.2, 12.1;
* the `lax` flag: (A)'s `impR`/`andR` arms are unreachable at `j = .lax`
  (S14), so the block is total by the same case analysis that refutes
  `PolInv`.

Then two assembly lemmas:

    laxAdm  : Inv Γ [] .lax (Q ⊃ N) → False,  Inv Γ [] .lax (M ∧ N) → False
    PolInvT : FocalizationPLL, then (B) down the context and (A) on the goal
    PolInvL : FocalizationPLL at ◯⌊P⌋, then circInv, then (A)/(B)

and `CutInv` follows: erase both premises by `Inv.sound`, compose with
`subst1`, split on `j` (at `lax` use `laxAdm` for the two vacuous shapes),
and re-focalise with `PolInvT`/`PolInvL`.

## 6. Pins, gates, and what was NOT run

**Pins.**  Every cell in `wip/cutinv_cells.lean` measures at `[]` —
including the two refutations, whose `cases` proofs need no axiom at all.
The pins are `#axioms_within <cell> []` throughout, with
`#axioms_within_pin` used to measure `lax_imp_empty`, `lax_and_empty`,
`not_polInv`, `not_polInv'` (all four print `[]`).  One boundary pin records
what the cells are testing against:

    #axioms_within LJFO.Inv.sound [propext, Quot.sound]

**Gate 1 — a wrong rule, watched failing.**  Cell 4.1's `.and1` (project
the left conjunct `↑a`) replaced by `.and2` (project `↑b`).  Rebuild:

    error: wip/cutinv_cells.lean:122:15: Application type mismatch: The argument
      List.mem_cons_self
    has type
      ?m.57 ∈ ?m.57 :: ?m.58
    but is expected to have type
      Neg.up (Pos.atom "a") ∈ [Neg.up (Pos.atom "b"), na.and nb,
                               Neg.up (Pos.down (na.and nb))]
    in the application
      RFocus.init ⋯

and the cell's own pin caught the fallout:

    error: wip/cutinv_cells.lean:427:0: 'CutInvCells.s4_andL_delay'
      depends on sorryAx, which the bound does not allow.
      declared: []

Restored, rebuilt, `Build completed successfully`.

**Gate 2 — a pin, watched failing.**  `#axioms_within LJFO.Inv.sound []`:

    error: wip/cutinv_cells.lean:418:0: 'LJFO.Inv.sound' depends on
      propext, Quot.sound, which the bound does not allow.
      declared: []
    Locate the entry with:  #axiom_path propext LJFO.Inv.sound

Restored to `[propext, Quot.sound]`, which passes.

**`LJFO.LSeq.search` was not run.**  The brief allows it as a check on a
cell already analysed by hand.  It was not needed and would add nothing:
every PASS cell's hand analysis terminated in an explicit `Inv` term, which
the kernel checks — strictly stronger than a `search … = true`; and both
REFUTED cells carry an exhaustive `cases`, a proof of emptiness, whereas a
`search … = false` certifies nothing.  No enumerator, no `lean_exe`, no
runner script, no results table was written.
