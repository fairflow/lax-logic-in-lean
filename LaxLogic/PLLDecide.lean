import LaxLogic.PLLG4
import Mathlib.Data.Multiset.DershowitzManna

/-!
# Backward proof search for G4iLL: rule-instance enumeration

Chunk 3a of the decision procedure (F&M Theorem 2.8).  A sequent `(Γ, C)`
has a *finite* list of backward rule instances, `succs Γ C`: each instance
is the list of premise sequents of one way of applying one G4 rule with
conclusion `(Γ, C)`.  Left rules pick their principal formula `P ∈ Γ` and
use `Δ := Γ.erase P` as the side context — `G4`'s `Perm` hypothesis
(`List.perm_cons_erase`) absorbs the bookkeeping, and `G4.perm` transports
derivations between a rule's own side context and the canonical `erase`
representative.

* `succs_sound` : if some instance has all premises derivable, the
  conclusion is derivable — each instance really is a rule application.
* `succs_complete` (next chunk): every derivation ends with one of the
  enumerated instances, premises derivable.
* the Dershowitz–Manna decrease of `smeasure` along every instance, and
  the resulting `Decidable (G4 Γ C)` by well-founded recursion.
-/

open PLLFormula

namespace PLLND

/-- A sequent: context and goal. -/
abbrev Sequent : Type := List PLLFormula × PLLFormula

/-- The termination measure of a sequent: the multiset of Dyckhoff weights
of all formulas in it (context and goal).  A `List ℕ` coerced to
`Multiset ℕ`, so permutation facts transfer by `Multiset.coe_eq_coe`. -/
def smeasure (s : Sequent) : Multiset ℕ :=
  (s.2.weight :: s.1.map PLLFormula.weight : List ℕ)

/-- The backward rule instances contributed by principal formula `P` with
side context `Δ := Γ.erase P`.  Each element is the premise list of one
rule application. -/
def instsFor (Γ : List PLLFormula) (C : PLLFormula) (P : PLLFormula) :
    List (List Sequent) :=
  let Δ := Γ.erase P
  match P with
  | .and A B => [[(A :: B :: Δ, C)]]
  | .or A B => [[(A :: Δ, C), (B :: Δ, C)]]
  | .somehow A =>
      match C with
      | .somehow _ => [[(A :: Δ, C)]]
      | _ => []
  | .ifThen (.prop a) B => if prop a ∈ Δ then [[(B :: Δ, C)]] else []
  | .ifThen .falsePLL _ => [[(Δ, C)]]
  | .ifThen (.and A B) D => [[(A.ifThen (B.ifThen D) :: Δ, C)]]
  | .ifThen (.or A B) D => [[(A.ifThen D :: B.ifThen D :: Δ, C)]]
  | .ifThen (.ifThen A B) D => [[(B.ifThen D :: Δ, A.ifThen B), (D :: Δ, C)]]
  | .ifThen (.somehow A) B =>
      [(Δ, A), (B :: Δ, C)] ::
      Δ.filterMap fun Q =>
        match Q with
        | .somehow X => some [(X :: Δ.erase Q, A.somehow), (B :: Q :: Δ.erase Q, C)]
        | _ => none
  | _ => []

/-- Backward rule instances from the goal (leaves and right rules). -/
def rightInsts (Γ : List PLLFormula) : PLLFormula → List (List Sequent)
  | .prop a => if prop a ∈ Γ then [[]] else []
  | .falsePLL => []
  | .and A B => [[(Γ, A), (Γ, B)]]
  | .or A B => [[(Γ, A)], [(Γ, B)]]
  | .ifThen A B => [[(A :: Γ, B)]]
  | .somehow A => [[(Γ, A)]]

/-- All backward rule instances of the sequent `(Γ, C)`. -/
def succs (Γ : List PLLFormula) (C : PLLFormula) : List (List Sequent) :=
  (if falsePLL ∈ Γ then [[]] else []) ++ rightInsts Γ C
    ++ Γ.flatMap (instsFor Γ C)

namespace G4

/-- **Soundness of the enumeration**: every instance in `succs Γ C` with
all premises derivable yields `G4 Γ C`. -/
theorem succs_sound : ∀ {Γ : List PLLFormula} {C : PLLFormula}
    {inst : List Sequent}, inst ∈ succs Γ C →
    (∀ s ∈ inst, G4 s.1 s.2) → G4 Γ C := by
  intro Γ C inst hi hp
  simp only [succs, List.mem_append] at hi
  rcases hi with (hi | hi) | hi
  · -- botL
    split at hi
    · exact .botL ‹_›
    · cases hi
  · -- right rules: split on the goal
    cases C with
    | prop a =>
        simp only [rightInsts] at hi
        split at hi
        · exact .init ‹_›
        · cases hi
    | falsePLL => cases hi
    | and A B =>
        cases hi with
        | head => exact .andR (hp _ (.head _)) (hp _ (.tail _ (.head _)))
        | tail _ h => cases h
    | or A B =>
        cases hi with
        | head => exact .orR1 (hp _ (.head _))
        | tail _ h =>
            cases h with
            | head => exact .orR2 (hp _ (.head _))
            | tail _ h => cases h
    | ifThen A B =>
        cases hi with
        | head => exact .impR (hp _ (.head _))
        | tail _ h => cases h
    | somehow A =>
        cases hi with
        | head => exact .laxR (hp _ (.head _))
        | tail _ h => cases h
  · -- left rules
    obtain ⟨P, hP, hi⟩ := List.mem_flatMap.mp hi
    have hperm := List.perm_cons_erase hP
    cases P with
    | prop a => cases hi
    | falsePLL => cases hi
    | and A B =>
        cases hi with
        | head => exact .andL hperm (hp _ (.head _))
        | tail _ h => cases h
    | or A B =>
        cases hi with
        | head => exact .orL hperm (hp _ (.head _)) (hp _ (.tail _ (.head _)))
        | tail _ h => cases h
    | somehow A =>
        cases C with
        | somehow B =>
            cases hi with
            | head => exact .laxL hperm (hp _ (.head _))
            | tail _ h => cases h
        | prop a => cases hi
        | falsePLL => cases hi
        | and _ _ => cases hi
        | or _ _ => cases hi
        | ifThen _ _ => cases hi
    | ifThen A' B =>
        cases A' with
        | prop a =>
            simp only [instsFor] at hi
            split at hi
            · cases hi with
              | head => exact .impLProp hperm ‹_› (hp _ (.head _))
              | tail _ h => cases h
            · cases hi
        | falsePLL =>
            cases hi with
            | head => exact .impLBot hperm (hp _ (.head _))
            | tail _ h => cases h
        | and A₁ A₂ =>
            cases hi with
            | head => exact .impLAnd hperm (hp _ (.head _))
            | tail _ h => cases h
        | or A₁ A₂ =>
            cases hi with
            | head => exact .impLOr hperm (hp _ (.head _))
            | tail _ h => cases h
        | ifThen A₁ A₂ =>
            cases hi with
            | head =>
                exact .impLImp hperm (hp _ (.head _)) (hp _ (.tail _ (.head _)))
            | tail _ h => cases h
        | somehow A₁ =>
            cases hi with
            | head =>
                exact .impLLax hperm (hp _ (.head _)) (hp _ (.tail _ (.head _)))
            | tail _ hi =>
                obtain ⟨Q, hQ, hf⟩ := List.mem_filterMap.mp hi
                cases Q with
                | somehow X =>
                    simp only [Option.some_inj] at hf; subst hf
                    exact .impLLaxLax
                      (hperm.trans ((List.perm_cons_erase hQ).cons _))
                      (hp _ (.head _)) (hp _ (.tail _ (.head _)))
                | prop _ => cases hf
                | falsePLL => cases hf
                | and _ _ => cases hf
                | or _ _ => cases hf
                | ifThen _ _ => cases hf

end G4

end PLLND
