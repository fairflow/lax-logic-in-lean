import wip.goalDesc

/-!
# The universal table at an atom goal forces the atom

## Where this comes from

`wip/boxedBranchS1.lean` closes the descent's residual branch at one
configuration by case analysis on the second component
(`EnvDesc.branch_of_cases`), and every case closes the same way: the case's
*second conjunct* is a universal table at a **larger** context with the same
goal, and at the larger context that table collapses to the goal clause.  On the
two-γ-clause configuration all three cases go through for exactly that reason —
`wip/sealprobe6.lean` and the direct inspection behind PROGRESS §90 show the
cases are

    z ,      (u ∨ ⊥) ∧ (z ∨ ⊥) ,      ◯((s ∧ ⊤) ⊃ ⊥) ∧ (z ∨ ⊥)

and each contains `z ∨ ⊥`.

That is not an accident of the example.  Reading the environment clause table
(`itpAenv`, `LaxLogic/PLLG4UITrunc.lean`) at an **atom** goal `q ≠ p`, every
clause either produces nothing or produces a disjunct with a conjunct

    itpA p S f b Γ' (prop q)      with `Γ'` of strictly smaller defect,

with one exception: the `∨`-clause, whose disjunct is a *conjunction of
implications* and whose consequents cannot be extracted without their guards.
So over contexts with no `∨`-shaped member the whole table collapses, by
induction on the defect.

## The theorem

    itpA_atom_forces :
      (∀ A B, A.or B ∉ S) → q ≠ p → (∀ Y ∈ Γ, Y ∈ S) →
      G4c [itpA p S f b Γ (prop q)] (prop q)

It holds at **every** fuel and **every** budget — the budget plays no role,
which is what makes it usable at the floor where the descent itself fails.

## What it is for

It is the engine of the case analysis at atom goals: in each case the second
conjunct is a table at a larger context, and this lemma turns it into the atom,
which is the target table's own goal clause.  So the residual branch closes at
atom goals over `∨`-free contexts, uniformly in the configuration — the first
general statement of that kind about the residue.
-/

open PLLFormula

namespace PLLND
namespace AtomForce

open GoalDesc

/-! ## 1. A defect witness -/

/-- If `Γ'` contains everything in `Γ` and also some `w ∈ S ∖ Γ`, its defect is
strictly smaller. -/
theorem defect_lt_of_witness {S : Finset PLLFormula} {Γ Γ' : List PLLFormula}
    (hsub : ∀ y ∈ Γ, y ∈ Γ') {w : PLLFormula}
    (hwS : w ∈ S) (hwΓ' : w ∈ Γ') (hwΓ : w ∉ Γ) :
    defect S Γ' < defect S Γ := by
  have hsubset : S \ Γ'.toFinset ⊆ S \ Γ.toFinset := by
    intro y hy
    simp only [Finset.mem_sdiff, List.mem_toFinset] at hy ⊢
    exact ⟨hy.1, fun h => hy.2 (hsub y h)⟩
  refine Finset.card_lt_card ?_
  rw [Finset.ssubset_iff_of_subset hsubset]
  refine ⟨w, ?_, ?_⟩
  · simp only [Finset.mem_sdiff, List.mem_toFinset]
    exact ⟨hwS, hwΓ⟩
  · simp only [Finset.mem_sdiff, List.mem_toFinset, not_and, not_not]
    exact fun _ => hwΓ'

/-! ## 2. The theorem -/

/-- The recursion is on the defect; the statement is quantified over fuel,
budget and context so that the induction hypothesis applies at the grown
contexts the clauses produce. -/
theorem atom_forces_aux (p : String) (S : Finset PLLFormula)
    (hOr : ∀ A B : PLLFormula, A.or B ∉ S) (q : String) (hq : q ≠ p) :
    ∀ (d : Nat) (f b : Nat) (Γ : List PLLFormula),
      defect S Γ ≤ d → (∀ Y ∈ Γ, Y ∈ S) →
      G4c [itpA p S f b Γ (prop q)] (prop q) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ihd =>
  intro f b Γ hd hΓS
  cases f with
  | zero =>
      simp only [itpA]
      exact G4c.botL (.head _)
  | succ f' =>
      rw [itpA_succ]
      refine G4c.orAll_elim ?_
      intro φ hφ
      -- `prop q` is not `◯`-shaped, so the full table is goal ++ env
      simp only [itpAfull, itpAoth] at hφ
      rcases List.mem_append.mp hφ with hg | he
      · -- the goal clause: `[prop q]`
        simp only [itpAgoal] at hg
        rw [if_neg hq] at hg
        rcases List.mem_singleton.mp hg with rfl
        exact G4c.init (.head _)
      · -- an environment clause
        simp only [itpAenv] at he
        obtain ⟨F, hFΓ, hin⟩ := List.mem_flatMap.mp he
        have hFS : F ∈ S := hΓS F hFΓ
        -- the recursive step, packaged: a table at a context that contains Γ
        -- and one fresh member of S
        have step : ∀ (Γ' : List PLLFormula) (w : PLLFormula),
            (∀ y ∈ Γ, y ∈ Γ') → (∀ y ∈ Γ', y ∈ S) →
            w ∈ S → w ∈ Γ' → w ∉ Γ →
            G4c [itpA p S f' b Γ' (prop q)] (prop q) := by
          intro Γ' w hsub hΓ'S hwS hwΓ' hwΓ
          have hlt : defect S Γ' < defect S Γ :=
            defect_lt_of_witness hsub hwS hwΓ' hwΓ
          exact ihd (defect S Γ') (by omega) f' b Γ' (Nat.le_refl _) hΓ'S
        cases F with
        | prop q' =>
            simp only at hin
            split at hin
            next hc =>
              -- needs `prop q = prop p`, impossible
              exfalso
              have h2 : q = p := by simpa using hc.2
              exact hq h2
            next => cases hin
        | falsePLL => cases hin
        | somehow χ => simp only at hin; cases hin
        | or A B => exact absurd hFS (hOr A B)
        | and A B =>
            simp only at hin
            split at hin
            next => cases hin
            next h1 =>
              split at hin
              next h2 =>
                rcases List.mem_singleton.mp hin with rfl
                -- a fresh witness among A, B
                by_cases hA : A ∈ Γ
                · have hB : B ∉ Γ := fun hB => h1 ⟨hA, hB⟩
                  have hBS : B ∈ S := h2.2.resolve_left hB
                  exact step (A :: B :: Γ) B
                    (fun y hy => .tail _ (.tail _ hy))
                    (by
                      intro y hy
                      rcases List.mem_cons.mp hy with rfl | hy
                      · exact hΓS _ hA
                      rcases List.mem_cons.mp hy with rfl | hy
                      · exact hBS
                      · exact hΓS y hy)
                    hBS (.tail _ (.head _)) hB
                · have hAS : A ∈ S := h2.1.resolve_left hA
                  exact step (A :: B :: Γ) A
                    (fun y hy => .tail _ (.tail _ hy))
                    (by
                      intro y hy
                      rcases List.mem_cons.mp hy with rfl | hy
                      · exact hAS
                      rcases List.mem_cons.mp hy with rfl | hy
                      · exact (h2.2.elim (fun h => hΓS _ h) id)
                      · exact hΓS y hy)
                    hAS (.head _) hA
              next => cases hin
        | ifThen A D =>
            cases A with
            | prop q' =>
                simp only at hin
                split at hin
                next => cases hin
                next h1 =>
                  split at hin
                  next h2 =>
                    split at hin
                    next h3 =>
                      rcases List.mem_singleton.mp hin with rfl
                      exact step (D :: Γ) D (fun y hy => .tail _ hy)
                        (by
                          intro y hy
                          rcases List.mem_cons.mp hy with rfl | hy
                          · exact h2
                          · exact hΓS y hy)
                        h2 (.head _) h1
                    next h3 =>
                      split at hin
                      next => cases hin
                      next h4 =>
                        rcases List.mem_singleton.mp hin with rfl
                        refine consume₁ (projAnd₂ (G4c.iden (.head _))) ?_
                        exact step (D :: Γ) D (fun y hy => .tail _ hy)
                          (by
                            intro y hy
                            rcases List.mem_cons.mp hy with rfl | hy
                            · exact h2
                            · exact hΓS y hy)
                          h2 (.head _) h1
                  next => cases hin
            | falsePLL => cases hin
            | and A₁ B₁ =>
                simp only at hin
                split at hin
                next => cases hin
                next h1 =>
                  split at hin
                  next h2 =>
                    rcases List.mem_singleton.mp hin with rfl
                    exact step (A₁.ifThen (B₁.ifThen D) :: Γ)
                      (A₁.ifThen (B₁.ifThen D)) (fun y hy => .tail _ hy)
                      (by
                        intro y hy
                        rcases List.mem_cons.mp hy with rfl | hy
                        · exact h2
                        · exact hΓS y hy)
                      h2 (.head _) h1
                  next => cases hin
            | or A₁ B₁ =>
                simp only at hin
                split at hin
                next => cases hin
                next h1 =>
                  split at hin
                  next h2 =>
                    rcases List.mem_singleton.mp hin with rfl
                    by_cases hAD : A₁.ifThen D ∈ Γ
                    · have hBD : B₁.ifThen D ∉ Γ := fun h => h1 ⟨hAD, h⟩
                      have hBDS : B₁.ifThen D ∈ S := h2.2.resolve_left hBD
                      exact step (A₁.ifThen D :: B₁.ifThen D :: Γ)
                        (B₁.ifThen D) (fun y hy => .tail _ (.tail _ hy))
                        (by
                          intro y hy
                          rcases List.mem_cons.mp hy with rfl | hy
                          · exact hΓS _ hAD
                          rcases List.mem_cons.mp hy with rfl | hy
                          · exact hBDS
                          · exact hΓS y hy)
                        hBDS (.tail _ (.head _)) hBD
                    · have hADS : A₁.ifThen D ∈ S := h2.1.resolve_left hAD
                      exact step (A₁.ifThen D :: B₁.ifThen D :: Γ)
                        (A₁.ifThen D) (fun y hy => .tail _ (.tail _ hy))
                        (by
                          intro y hy
                          rcases List.mem_cons.mp hy with rfl | hy
                          · exact hADS
                          rcases List.mem_cons.mp hy with rfl | hy
                          · exact (h2.2.elim (fun h => hΓS _ h) id)
                          · exact hΓS y hy)
                        hADS (.head _) hAD
                  next => cases hin
            | ifThen A₁ B₁ =>
                simp only at hin
                split at hin
                next => cases hin
                next h1 =>
                  split at hin
                  next h2 =>
                    repeat' split at hin
                    all_goals (try fin_cases hin)
                    all_goals refine consume₁ (projAnd₂ (G4c.iden (.head _))) ?_
                    all_goals exact step (D :: Γ) D (fun y hy => .tail _ hy) (by intro y hy; rcases List.mem_cons.mp hy with rfl | hy; exacts [h2, hΓS y hy]) h2 (.head _) h1
                  next => cases hin
            | somehow A₁ =>
                simp only at hin
                split at hin
                next => cases hin
                next h1 =>
                  split at hin
                  next h2 =>
                    rcases List.mem_append.mp hin with hL | hR
                    · -- the gated part (i): two disjuncts, both `_ ∧ A@b(D::Γ)`
                      repeat' split at hL
                      all_goals (try fin_cases hL)
                      all_goals refine consume₁ (projAnd₂ (G4c.iden (.head _))) ?_
                      all_goals exact step (D :: Γ) D (fun y hy => .tail _ hy) (by intro y hy; rcases List.mem_cons.mp hy with rfl | hy; exacts [h2, hΓS y hy]) h2 (.head _) h1
                    · -- part (ii): the per-`◯x` continuation, also `_ ∧ A@b(D::Γ)`
                      obtain ⟨X, hXΓ, hXin⟩ := List.mem_filterMap.mp hR
                      cases X with
                      | somehow x =>
                          simp only at hXin
                          split at hXin
                          next => cases hXin
                          next hx =>
                            rcases Option.some_inj.mp hXin with rfl
                            refine consume₁ (projAnd₂ (G4c.iden (.head _))) ?_
                            exact step (D :: Γ) D (fun y hy => .tail _ hy)
                              (by
                                intro y hy
                                rcases List.mem_cons.mp hy with rfl | hy
                                · exact h2
                                · exact hΓS y hy)
                              h2 (.head _) h1
                      | prop _ => cases hXin
                      | falsePLL => cases hXin
                      | and _ _ => cases hXin
                      | or _ _ => cases hXin
                      | ifThen _ _ => cases hXin
                  next => cases hin

/-- **The universal table at an atom goal forces the atom**, over a context
with no `∨`-shaped member, at every fuel and every budget. -/
theorem itpA_atom_forces (p : String) (S : Finset PLLFormula)
    (hOr : ∀ A B : PLLFormula, A.or B ∉ S) {q : String} (hq : q ≠ p)
    (f b : Nat) (Γ : List PLLFormula) (hΓS : ∀ Y ∈ Γ, Y ∈ S) :
    G4c [itpA p S f b Γ (prop q)] (prop q) :=
  atom_forces_aux p S hOr q hq (defect S Γ) f b Γ (Nat.le_refl _) hΓS

end AtomForce
end PLLND

/-! ### Axiom audit -/

/--
info: 'PLLND.AtomForce.itpA_atom_forces' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.AtomForce.itpA_atom_forces

/--
info: 'PLLND.AtomForce.defect_lt_of_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.AtomForce.defect_lt_of_witness
