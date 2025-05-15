import LaxLogic.PLLFormula
import LaxLogic.PLLAxiom

open PLLFormula

inductive  PLLProof where
 | emptyProof
 | axiomStep (prev:  PLLProof) (ax: PLLAxiom)
 | modusPonens (prev:  PLLProof) (conditional: Conditional)
  deriving Inhabited, DecidableEq

namespace PLLProof
-- Gets a list of PLL formulas that are in the proof, no validation here
def  formulas (proof:  PLLProof): List PLLFormula :=
  match proof with
  | emptyProof => []
  | axiomStep prev ax =>  prev.formulas ++ [ax.get]
  | modusPonens prev conditional =>  prev.formulas ++ [conditional.consequent]


-- Proposition that a proof is valid
def  isValid (proof:  PLLProof) : Prop :=
  match proof with
  | emptyProof => True
  -- Any axiom step is valid
  | axiomStep prev _  => isValid prev
  -- Modus ponens is valid if both the antecedant and the consequent at in the previous steps.
  | modusPonens prev conditional => conditional.antecedant ∈ prev.formulas ∧ conditional.consequent ∈ prev.formulas

def  isEmpty (proof:  PLLProof):= proof = emptyProof

lemma  non_empty_formulas (proof:  PLLProof) (h: ¬proof.isEmpty) : proof.formulas ≠ [] := by
    induction proof with
    | emptyProof => contradiction
    | axiomStep prev ax => simp [formulas]
    | modusPonens prev conditional => simp [formulas]

def  NonEmpty := {p: PLLProof // ¬ p.isEmpty}

def  NonEmpty.conclusion (p: NonEmpty) : PLLFormula :=
    let h := non_empty_formulas p.val p.prop
    p.val.formulas.getLast h


-- Helper for when the proof is non-empty
private def  isProofOf_ (proof : NonEmpty) (target: PLLFormula)   : Prop :=
  proof.conclusion = target ∧ proof.val.isValid


-- Check that a given proof is a proof of a given formula
def  isProofOf (proof :  PLLProof)  (target: PLLFormula)  : Prop :=
  match proof with
  | emptyProof => False
  | axiomStep prev ax => isProofOf_  ⟨ axiomStep prev ax, by simp [isEmpty]⟩ target
  | modusPonens prev ax => isProofOf_  ⟨ modusPonens prev ax, by simp [isEmpty] ⟩ target
