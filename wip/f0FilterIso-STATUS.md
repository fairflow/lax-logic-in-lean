# f0FilterIso: is a proper filter of F0 order-isomorphic to F0?

Status note for `wip/f0FilterIso.lean` (Paper III, open question 1).
Agent worktree `agent-a8a8f327dcc3226c5`, branch `worktree-agent-a8a8f327dcc3226c5`,
cut from main `0a8cfeb`.  Stage: refutation stage (METHOD.md §1), before the
checkpoint.

## 2026-10-25 16:58 GMT: statement and plan of the cells

The question, as a `def … : Prop`:

    FilterIsoQ :=  ∀ p : RNClass,  p ≠ ⊥  →  ¬ Nonempty (Set.Ici p ≃o RNClass)

Structure used: `F0 = {⊥, t1, t2, t4} ∪ ↑t3` (from `low_trichotomy` and the
tables `D3`, `D4`), so every `p ≠ ⊥` is `t1`, `t2`, `t4`, or dense (`t3 ⊢ p`).

Designed cells (each with its reason):

* `p = t2 = ¬◯⊥`: an atom with a unique upper cover; `[t2, ⊤] = {t2} ∪ ↑t3`
  has no disjoint pair, F0 has one (`(t1, t2)`).
* `p = t4`: the same shape, `[t4, ⊤] = {t4} ∪ ↑t5`.
* `p = t1 = ◯⊥`: the ◯-fixed atom.  In the ◯-free instance (the
  Rieger–Nishimura lattice) `[p, ⊤] ≅ RN` holds, by the shift `tₙ ↦ tₙ₊₂`;
  so this is the cell where PLL must differ from IPC.  `[t1, ⊤] = {t1, t4} ∪ ↑t3`,
  and an isomorphism must send the unique "big atom" `t1` of F0 to `t3`, so
  `[t1, ⊤] ≅ F0` would give `[t3, ⊤] ≅ F0`, against `t3_filter_not_iso`.
* `p = σⁿ⁺¹(⊥) = σⁿ(t3)`: the bases of the σ-copies, the candidates the
  self-similarity suggests; the two disjoint pairs of `[t3, ⊤]` are carried by
  `σⁿ`, which preserves `∧` and reflects the order (semantic reflection over
  constraint models with decidable fallibility, so no completeness theorem).

Not attempted: the general dense case (see the plan in the checkpoint report).

Note: the Edit/Write tools refuse this worktree (a PreToolUse hook takes the
manager's worktree `verso-paper-9a382c` as this session's root); files here are
written from the shell, inside this worktree only.

## 2026-10-25 17:26 GMT: checkpoint (refutation stage done)

Built: `lake build wip.f0FilterIso` (about 12 s for the module), clean, no
warnings.  Every pin passes and was watched failing at a strictly tighter set
(scratch `_out/pinwatch.lean`, 23 failures as expected; `_out/pinwatch2.lean`).

PROVED (pins in the file):

* `classify_low`: `F0 = {⊥, t1, t2, t4} ∪ ↑t3`, constructive.
* `filterIsoQ_iff_dense : FilterIsoQ ↔ DenseResidue`.
* Cells, each `¬ Nonempty (Set.Ici p ≃o RNClass)`:
  `t2` (`ne_filter_not_iso`, no disjoint pair), `t4` (`t4_filter_not_iso`),
  `t1` (`e_filter_not_iso`, big-atom descent to `t3_filter_not_iso`),
  `σⁿ(t3) = σⁿ⁺¹(⊥)` for every `n` (`sigN_filter_not_iso`; `refutes_sig`, σ
  reflects refutation on constraint models with decidable fallibility, pin
  `[propext]`), `c1 = ◯t3` (`c1_filter_not_iso`, three pairwise disjoint
  elements, countermodels `K_al`, `K_be`, `K_ga` built by hand).
* `obstructionA_F0_case`: F0 itself satisfies the second alternative of
  `ObstructionA`, as it must.

OPEN: `DenseResidue` for the remaining dense `p`.  Stated, not proved:
`ObstructionA` (one model construction: a new root below a `d`-world whose
only `Rₘ`-successor is itself).  The residual cases after it are recorded in
the checkpoint report.

Not done: the ◯-free instance (Rieger–Nishimura: `[p, ⊤] ≅ RN` by the shift
`tₙ ↦ tₙ₊₂`, a YES answer) is a pen remark only.

## 2026-10-25 18:05 GMT: round 2 (after PR #92 at 72871ff)

Commits on top of `72871ff` only; nothing rewritten, nothing pushed.

PROVED (pins in the file, each watched failing at a tighter set,
`_out/pinwatch3.lean`, 30 failures as expected):

* Transport (§9): for `f : F0 ≃o [p, ⊤]`, `iso_split` (`[p,⊤] = {p,d} ∪ ↑a`),
  `iso_split_a` (`↑a = {a,d₄} ∪ ↑a₃`), `iso_cover`, `iso_prime`,
  `iso_himp` (an order isomorphism onto `[p,⊤]` carries `⇨`), `Di_himp`
  (`d ⇨ p = d₄`), `D4i_himp` (`d₄ ⇨ p = d`).  `[propext, Quot.sound]`.
* `obstructionA : ObstructionA`, as stated, `[propext]`: one new root below a
  `d`-world, its only `Rₘ`-successor itself (`RootExt`).
* `iso_cases` (every `p`, no density): `◯p = p ∨ ◯p = d ∨ ◯p = d₄ ∨
  (◯p = a ∧ ◯d₄ = d₄)`; the shapes `case_d_shape`, `case_d4_shape`,
  `case_a_shape`.
* Cells: `C1n_filter_not_iso n` (`σⁿ(c1)`, dense and `◯`-fixed, case (i)
  realised, refuted by three pairwise disjoint elements, every `n`);
  `t5_filter_not_iso`; `box_t3_not_meetPrime`, `box_t5_not_cover` (case ii);
  `gap_t3_not_cover` (case iii); `box_t3_not_bigAtom`, `box_t5_not_bigAtom`
  (case iv).  Semantic A-translation: `subBot_le`, `sigN_le` (`[propext]`).

OPEN: `DenseResidue` in each of the four cases.  Skipped: the cell `g1`.
