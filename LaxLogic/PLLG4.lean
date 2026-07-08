import LaxLogic.PLLSequent

/-!
# G4iLL: a terminating, contraction-free sequent calculus for PLL

Towards F&M Theorem 2.8 (decidability) as a *computable, verified* decision
procedure.  The calculus `G4` below is Iemhoff's **G4iLL** — Dyckhoff's
contraction-free G4ip for intuitionistic propositional logic extended with
four lax rules — from

* R. Iemhoff, *Proof Theory for Lax Logic*, in: Dick de Jongh on
  Intuitionistic and Provability Logics, Outstanding Contributions to
  Logic, Springer 2024 (arXiv:2209.08976);
* R. Dyckhoff, *Contraction-free sequent calculi for intuitionistic
  logic*, JSL 57(3), 1992.

As in G4ip, the left implication rule is split by the shape of the
antecedent of the implication; the two rules for `◯A ⊃ B` are Iemhoff's
`R#→` (`impLLax`) and `L#→` (`impLLaxLax`).  The latter keeps `◯X` in the
context, which is exactly what absorbs Howe's duplication example
(`B⊃(◯A⊃C)⊃◯A, ◯B, ◯A⊃C ⇒ C`) — Howe (MSCS 11(4), 2001) conjectured no
contraction-free calculus for lax logic exists; Iemhoff's calculus
refutes this.

Every premise is smaller than its conclusion in the Dershowitz–Manna
multiset extension of `PLLFormula.weight` (Dyckhoff's weight with
`weight (◯A) = weight A + 1`), so naive backward proof search terminates;
that measure drives the prover (later in this development), not the
inductive definition itself.

## Design notes (slime discipline)

Contexts are **shared lists** (additive rules) and each left rule takes its
principal formula **at the head** of the conclusion context: conclusion
indices are built from `::` and constructor forms only — no `++`, no
`List.erase`, no multisets — so `cases`/inversion iota-reduce cleanly.
Exchange is recovered once and for all as an admissible permutation lemma
(with the prover, not needed for soundness).  The weight measure is a
*function of* the index, evaluated but never unified against, so it lives
harmlessly outside the inductive.

This file, chunk 1: the weight, the calculus, and **soundness** into the
cut-free G3 calculus `SCh`/`SC` (which has admissible cut, `SC.cut`).
Completeness (`SC Γ C → G4 Γ C`, the Dyckhoff/Iemhoff equivalence) and the
prover are follow-on chunks.
-/

open PLLFormula

namespace PLLFormula

/-- Dyckhoff's weight, extended to `◯` à la Iemhoff: like `sizeOf`, except
that a conjunction weighs `2` more than its parts, which is what makes the
`impLAnd` premise strictly smaller.  Drives the termination of G4 proof
search under the Dershowitz–Manna multiset order. -/
def weight : PLLFormula → Nat
  | prop _ => 1
  | falsePLL => 1
  | and A B => A.weight + B.weight + 2
  | or A B => A.weight + B.weight + 1
  | ifThen A B => A.weight + B.weight + 1
  | somehow A => A.weight + 1

theorem weight_pos : ∀ φ : PLLFormula, 0 < φ.weight
  | prop _ => Nat.one_pos
  | falsePLL => Nat.one_pos
  | and _ _ => Nat.succ_pos _
  | or _ _ => Nat.succ_pos _
  | ifThen _ _ => Nat.succ_pos _
  | somehow _ => Nat.succ_pos _

end PLLFormula

namespace PLLND

/-- **G4iLL** (Iemhoff): contraction-free, terminating sequent calculus for
PLL.  Single succedent, shared-context (additive) rules; every left rule
consumes its principal formula, which sits at the **head** of the conclusion
context (exchange is admissible, proved separately).  `init` and `botL` are
the leaves and use membership, as does the side condition of `impLProp`. -/
inductive G4 : List PLLFormula → PLLFormula → Prop
  | init {Γ : List PLLFormula} {a : String}
      (h : prop a ∈ Γ) : G4 Γ (prop a)
  | botL {Γ : List PLLFormula} {C : PLLFormula}
      (h : falsePLL ∈ Γ) : G4 Γ C
  -- right rules, exactly as in G3
  | andR {Γ : List PLLFormula} {A B : PLLFormula} :
      G4 Γ A → G4 Γ B → G4 Γ (A.and B)
  | orR1 {Γ : List PLLFormula} {A B : PLLFormula} :
      G4 Γ A → G4 Γ (A.or B)
  | orR2 {Γ : List PLLFormula} {A B : PLLFormula} :
      G4 Γ B → G4 Γ (A.or B)
  | impR {Γ : List PLLFormula} {A B : PLLFormula} :
      G4 (A :: Γ) B → G4 Γ (A.ifThen B)
  | laxR {Γ : List PLLFormula} {A : PLLFormula} :
      G4 Γ A → G4 Γ A.somehow
  -- left rules for ∧, ∨, ◯: principal formula consumed
  | andL {Γ : List PLLFormula} {A B C : PLLFormula} :
      G4 (A :: B :: Γ) C → G4 (A.and B :: Γ) C
  | orL {Γ : List PLLFormula} {A B C : PLLFormula} :
      G4 (A :: Γ) C → G4 (B :: Γ) C → G4 (A.or B :: Γ) C
  | laxL {Γ : List PLLFormula} {A B : PLLFormula} :
      G4 (A :: Γ) B.somehow → G4 (A.somehow :: Γ) B.somehow
  -- left implication, split by the antecedent of the implication
  | impLProp {Γ : List PLLFormula} {a : String} {B C : PLLFormula}
      (h : prop a ∈ Γ) :
      G4 (B :: Γ) C → G4 ((prop a).ifThen B :: Γ) C
  | impLBot {Γ : List PLLFormula} {B C : PLLFormula} :
      G4 Γ C → G4 (falsePLL.ifThen B :: Γ) C
  | impLAnd {Γ : List PLLFormula} {A B D E : PLLFormula} :
      G4 (A.ifThen (B.ifThen D) :: Γ) E → G4 ((A.and B).ifThen D :: Γ) E
  | impLOr {Γ : List PLLFormula} {A B D E : PLLFormula} :
      G4 (A.ifThen D :: B.ifThen D :: Γ) E → G4 ((A.or B).ifThen D :: Γ) E
  | impLImp {Γ : List PLLFormula} {A B D E : PLLFormula} :
      G4 (B.ifThen D :: Γ) (A.ifThen B) → G4 (D :: Γ) E →
      G4 ((A.ifThen B).ifThen D :: Γ) E
  -- Iemhoff's two rules for a ◯-antecedent implication
  | impLLax {Γ : List PLLFormula} {A B C : PLLFormula} :
      G4 Γ A → G4 (B :: Γ) C → G4 (A.somehow.ifThen B :: Γ) C
  | impLLaxLax {Γ : List PLLFormula} {A B X C : PLLFormula} :
      G4 (X :: Γ) A.somehow → G4 (B :: X.somehow :: Γ) C →
      G4 (A.somehow.ifThen B :: X.somehow :: Γ) C

namespace G4

/-- **Soundness of G4iLL** into the cut-free G3 calculus: every G4 rule is
admissible in `SC`.  The only rules needing `SC.cut` are `impLAnd`,
`impLOr` (cutting the decomposed implications) and `impLImp` (cutting
`A ⊃ B`, obtained from the first premise and the derivable `B ⊃ D`). -/
theorem toSC : ∀ {Γ : List PLLFormula} {C : PLLFormula}, G4 Γ C → SC Γ C := by
  intro Γ C d
  induction d with
  | init h => exact SC.init h
  | botL h => exact SC.botL h
  | andR _ _ ih₁ ih₂ => exact SC.andR ih₁ ih₂
  | orR1 _ ih => exact SC.orR1 ih
  | orR2 _ ih => exact SC.orR2 ih
  | impR _ ih => exact SC.impR ih
  | laxR _ ih => exact SC.laxR ih
  | andL _ ih =>
      refine SC.andL (.head _) (ih.rename ?_)
      intro ψ h; simp only [List.mem_cons] at h ⊢; tauto
  | orL _ _ ih₁ ih₂ =>
      refine SC.orL (.head _) (ih₁.rename ?_) (ih₂.rename ?_) <;>
        (intro ψ h; simp only [List.mem_cons] at h ⊢; tauto)
  | laxL _ ih =>
      refine SC.laxL (.head _) (ih.rename ?_)
      intro ψ h; simp only [List.mem_cons] at h ⊢; tauto
  | impLProp h _ ih =>
      refine SC.impL (.head _) (SC.init (.tail _ h)) (ih.rename ?_)
      intro ψ h'; simp only [List.mem_cons] at h' ⊢; tauto
  | impLBot _ ih => exact ih.rename (fun ψ h => .tail _ h)
  | @impLAnd Γ' A B D E _ ih =>
      -- cut the derivable `A ⊃ (B ⊃ D)` into the premise
      have p : SC ((A.and B).ifThen D :: Γ') (A.ifThen (B.ifThen D)) := by
        refine SC.impR (SC.impR ?_)
        refine SC.impL (A := A.and B) (.tail _ (.tail _ (.head _)))
          (SC.andR (SC.iden _ (.tail _ (.head _))) (SC.iden _ (.head _))) ?_
        exact SC.iden _ (.head _)
      refine SC.cut p (ih.rename ?_)
      intro ψ h; simp only [List.mem_cons] at h ⊢; tauto
  | @impLOr Γ' A B D E _ ih =>
      -- cut the two derivable decomposed implications into the premise
      have p₁ : SC ((A.or B).ifThen D :: Γ') (A.ifThen D) := by
        refine SC.impR ?_
        refine SC.impL (A := A.or B) (.tail _ (.head _))
          (SC.orR1 (SC.iden _ (.head _))) (SC.iden _ (.head _))
      have p₂ : SC ((A.or B).ifThen D :: Γ') (B.ifThen D) := by
        refine SC.impR ?_
        refine SC.impL (A := A.or B) (.tail _ (.head _))
          (SC.orR2 (SC.iden _ (.head _))) (SC.iden _ (.head _))
      refine SC.cut p₁ (SC.cut (p₂.rename (fun ψ h => .tail _ h)) (ih.rename ?_))
      intro ψ h; simp only [List.mem_cons] at h ⊢; tauto
  | @impLImp Γ' A B D E _ _ ih₁ ih₂ =>
      -- `B ⊃ D` is derivable outright, so the first premise cuts to `A ⊃ B`
      have hBD : SC ((A.ifThen B).ifThen D :: Γ') (B.ifThen D) := by
        refine SC.impR ?_
        refine SC.impL (A := A.ifThen B) (.tail _ (.head _)) ?_
          (SC.iden _ (.head _))
        exact SC.impR (SC.iden _ (.tail _ (.head _)))
      have hAB : SC ((A.ifThen B).ifThen D :: Γ') (A.ifThen B) := by
        refine SC.cut hBD (ih₁.rename ?_)
        intro ψ h; simp only [List.mem_cons] at h ⊢; tauto
      refine SC.impL (.head _) hAB (ih₂.rename ?_)
      intro ψ h; simp only [List.mem_cons] at h ⊢; tauto
  | impLLax _ _ ih₁ ih₂ =>
      refine SC.impL (.head _)
        (SC.laxR (ih₁.rename (fun ψ h => .tail _ h))) (ih₂.rename ?_)
      intro ψ h; simp only [List.mem_cons] at h ⊢; tauto
  | @impLLaxLax Γ' A B X C' _ _ ih₁ ih₂ =>
      -- `◯A` follows from `◯X` by `laxL` on the first premise
      have hOA : SC (A.somehow.ifThen B :: X.somehow :: Γ') A.somehow := by
        refine SC.laxL (A := X) (.tail _ (.head _)) (ih₁.rename ?_)
        intro ψ h; simp only [List.mem_cons] at h ⊢; tauto
      refine SC.impL (.head _) hOA (ih₂.rename ?_)
      intro ψ h; simp only [List.mem_cons] at h ⊢; tauto

end G4

/-! ### Smoke tests: the lax axioms, searched bottom-up in G4 -/

example : G4 [] ((prop "A").ifThen (prop "A").somehow) :=
  .impR (.laxR (.init (.head _)))

example : G4 [] ((prop "A").somehow.somehow.ifThen (prop "A").somehow) :=
  .impR (.laxL (.laxL (.laxR (.init (.head _)))))

-- Howe's duplication sequent (`B ⊃ ((◯A ⊃ C) ⊃ ◯A), ◯B, ◯A ⊃ C ⊢ C`) is
-- provable in G4iLL via `impLLaxLax`, but its derivation needs left rules
-- applied below the head of the context — it returns as a regression test
-- once the exchange (permutation) lemma lands with the prover chunk.

end PLLND
