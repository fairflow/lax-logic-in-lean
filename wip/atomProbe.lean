import wip.uiObstruct

/-!
# The `Gmeet` descent is blind to the interval `[⊥, ◯⊥]`

Question (Matthew, 2026-08-19): the gap meets `Gmeet n = g 1 ∧ … ∧ g (n+1)`
descend strictly forever (`Gmeet_desc_strict`).  Do `◯⊥` and `¬◯⊥` collapse
that chain under `∧`?

**Yes, and immediately** — not "eventually constant" but constant from
`n = 0`.  The reason is already proved in `wip/uiObstruct.lean`:

    t3_below_gap :  1 ≤ k →  Deriv [rnSub 3] (gap k)

the WHOLE gap antichain sits above `rnSub 3 = ◯⊥ ∨ ¬◯⊥`.  Both `◯⊥`
(`rnSub 1`) and `¬◯⊥` (`rnSub 2`) are below `rnSub 3` in the rung order, hence
below every `gap k`, hence below every `Gmeet n`.  So each meet is absorbed.

**Consequence.**  The infinite strict descent happens entirely STRICTLY ABOVE
`◯⊥ ∨ ¬◯⊥`.  It therefore carries no information whatever about whether
`⊥ ≺ ◯⊥` or `⊥ ≺ ¬◯⊥`: no member of the chain, and no meet of the chain with
`◯⊥` or `¬◯⊥`, ever lands strictly inside `[⊥, ◯⊥]` or `[⊥, ¬◯⊥]`.
-/

namespace PLLND
namespace RNEmbed

open SemUI PLLND.SemUI.RND

/-! ## 1. `◯⊥` and `¬◯⊥` are below `◯⊥ ∨ ¬◯⊥` -/

/-- `◯⊥ ⊢ ◯⊥ ∨ ¬◯⊥` — rung 1 ≤ rung 3, by the decidable rung arithmetic. -/
theorem oBot_le_t3 : Deriv [rnSub 1] (rnSub 3) := rungD (by decide)

/-- `¬◯⊥ ⊢ ◯⊥ ∨ ¬◯⊥` — rung 2 ≤ rung 3. -/
theorem nBot_le_t3 : Deriv [rnSub 2] (rnSub 3) := rungD (by decide)

/-! ## 2. Hence both are below every gap, and every gap meet -/

theorem oBot_le_gap {k : Nat} (hk : 1 ≤ k) : Deriv [rnSub 1] (gap k) :=
  Deriv.cutHead oBot_le_t3 (t3_below_gap hk)

theorem nBot_le_gap {k : Nat} (hk : 1 ≤ k) : Deriv [rnSub 2] (gap k) :=
  Deriv.cutHead nBot_le_t3 (t3_below_gap hk)

/-- `◯⊥ ⊢ Gmeet n` for every `n`. -/
theorem oBot_le_Gmeet : ∀ n : Nat, Deriv [rnSub 1] (Gmeet n)
  | 0 => oBot_le_gap (by omega)
  | n + 1 => Deriv.andIntro (oBot_le_Gmeet n) (oBot_le_gap (by omega))

/-- `¬◯⊥ ⊢ Gmeet n` for every `n`. -/
theorem nBot_le_Gmeet : ∀ n : Nat, Deriv [rnSub 2] (Gmeet n)
  | 0 => nBot_le_gap (by omega)
  | n + 1 => Deriv.andIntro (nBot_le_Gmeet n) (nBot_le_gap (by omega))

/-! ## 3. The collapse, stated as interderivability -/

/-- **`◯⊥ ∧ Gmeet n ⊣⊢ ◯⊥`, for every `n`.**  Constant, not eventually
constant. -/
theorem oBot_meet_Gmeet (n : Nat) :
    Interd ((rnSub 1).and (Gmeet n)) (rnSub 1) :=
  ⟨Deriv.andElim1 (Deriv.iden (.head _)),
   Deriv.andIntro (Deriv.iden (.head _)) (oBot_le_Gmeet n)⟩

/-- **`¬◯⊥ ∧ Gmeet n ⊣⊢ ¬◯⊥`, for every `n`.** -/
theorem nBot_meet_Gmeet (n : Nat) :
    Interd ((rnSub 2).and (Gmeet n)) (rnSub 2) :=
  ⟨Deriv.andElim1 (Deriv.iden (.head _)),
   Deriv.andIntro (Deriv.iden (.head _)) (nBot_le_Gmeet n)⟩

/-- The same for the join `◯⊥ ∨ ¬◯⊥` itself, which is what actually does the
absorbing. -/
theorem t3_meet_Gmeet (n : Nat) :
    Interd ((rnSub 3).and (Gmeet n)) (rnSub 3) :=
  ⟨Deriv.andElim1 (Deriv.iden (.head _)),
   Deriv.andIntro (Deriv.iden (.head _)) (t3_le_Gmeet n)⟩
where
  t3_le_Gmeet : ∀ n : Nat, Deriv [rnSub 3] (Gmeet n)
    | 0 => t3_below_gap (by omega)
    | n + 1 => Deriv.andIntro (t3_le_Gmeet n) (t3_below_gap (by omega))

/-! ## 4. What a strict interpolant in `(⊥, ◯⊥)` would have to look like

`◯` is monotone and `⊥ ⊢ ψ`, so **every `◯`-formula lies above `◯⊥`**.  A
formula strictly inside `[⊥, ◯⊥]` therefore cannot be interderivable with any
`◯ψ`.  It cannot be `◯`-free either: the `◯`-free closed IPC fragment collapses
to `{⊥, ⊤}` and `⊤ ⊬ ◯⊥`.  So a strict interpolant must contain `◯` while being
headed by `∧`, `∨` or `→`.  That is a constraint, not a proof; the cover
`⊥ ≺ ◯⊥` remains OPEN. -/

/-- **Every `◯`-formula is above `◯⊥`**: `◯⊥ ⊢ ◯ψ` for every `ψ`. -/
theorem oBot_le_box (ψ : PLLFormula) : Deriv [rnSub 1] ψ.somehow :=
  Deriv.somehowMono (Γ := []) (Deriv.falsoElim ψ (Deriv.iden (.head _)))

/-! ## Axiom audit -/

#print axioms oBot_meet_Gmeet
#print axioms nBot_meet_Gmeet
#print axioms oBot_le_box

end RNEmbed
end PLLND
