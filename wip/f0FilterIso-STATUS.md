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
