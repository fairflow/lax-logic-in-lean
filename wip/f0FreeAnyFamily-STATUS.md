# wip/f0FreeAnyFamily.lean — status

Two follow-ups to `wip/f0FreeBase3.lean` (brief 2026-10-28).  Public order
theory about F0.  Target pins `[propext, Quot.sound]`; no `Classical.choice`,
no `sorry`, no `native_decide`.

## The statements (committed before any proof, METHOD.md §1)

Goal 1, the choice of reader family does not matter:

    AnyFamily3 :  ∀ n,  Distinct σ²⊥ (n + 1)  →  FreeHAnAbove σ³⊥ n

Cleaner variant, the two killers inside the family:

    CellsKill n F :  (∀ i j ≤ n, i ≠ j → (F i).Separated (F j)) ∧
                     (F 0).w ⊮ ◯σ²⊥ ∧ (F 1).w ⊩ ◯σ²⊥
    FromCells3 :  ∀ n F,  CellsKill n F  →  FreeHAnAbove σ³⊥ n

Goal 2, the σ-shift, for variable-free `b`:

    SigShift   :  ∀ b vf, ∀ k n,  FreeHAnAbove b n  →  FreeHAnAbove (σᵏ b) n
    SigShiftω  :  ∀ b vf, ∀ k,    FreeHAωAbove b    →  FreeHAωAbove (σᵏ b)
    AllAbove3  :  ∀ m ≥ 3, ∀ n,  FreeHAnAbove σᵐ⊥ n
    AllAbove3ω :  ∀ m ≥ 3,       FreeHAωAbove σᵐ⊥

Fragment first (CLAUDE.md rule 8): degenerate, as in `f0FreeBase3` (the
◯-free variable-free fragment is `{⊥, ⊤}`).

## Status table

| statement | theorem | status |
|-----------|---------|--------|
| `AnyFamily3` | — | OPEN (Stage 0) |
| `FromCells3` | — | OPEN (Stage 0) |
| `SigShift`, `SigShiftω` | — | OPEN (Stage 0) |
| `AllAbove3`, `AllAbove3ω` | — | OPEN (Stage 0) |

## Log

* 2026-10-28: Stage 0, statements written and built
  (`lake build wip.f0FreeAnyFamily`), committed before any proof.
