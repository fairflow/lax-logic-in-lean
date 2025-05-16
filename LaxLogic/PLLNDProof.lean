import LaxLogic.PLLFormula
import LaxLogic.PLLAxiom

open PLLFormula

inductive LaxND : (List PLLFormula)→ PLLFormula → Prop -- Natural deduction for PLL
--  | atom : (Γ Δ : List PLLFormula) → (a : String) → LaxND (Γ ++ [prop a] ++ Δ) (prop a)
-- this first is not sufficiently general
  | iden : (Γ Δ : List PLLFormula) → (φ : PLLFormula) → LaxND (Γ ++ [φ] ++ Δ) φ
  | falsoElim : {Γ : List PLLFormula} → (φ : PLLFormula) → LaxND Γ falsePLL → LaxND Γ φ
  | impIntro : {Γ Δ : List PLLFormula} → {φ ψ : PLLFormula} → LaxND (Γ ++ [φ] ++ Δ) ψ → LaxND (Γ ++ Δ) (ifThen φ ψ)
  | impElim : {Γ : List PLLFormula} → {φ ψ : PLLFormula} → LaxND Γ (ifThen φ ψ) → LaxND Γ φ → LaxND Γ ψ
  | laxIntro : {Γ : List PLLFormula} → {φ : PLLFormula} → LaxND Γ φ → LaxND Γ (somehow φ)
  | laxElim : {Γ Δ : List PLLFormula} → {φ ψ : PLLFormula} → LaxND (Γ ++ Δ) (somehow φ)→ LaxND (Γ ++ [φ] ++ Δ) (somehow ψ) → LaxND (Γ ++ Δ) (somehow ψ)
--  | laxFlatten : {Γ : List PLLFormula} → {φ : PLLFormula} → LaxND Γ (somehow (somehow φ)) → LaxND Γ (somehow φ)
-- this last is derivable

infix:70 "⊢⋆" => LaxND -- turnstile

def LaxValid (φ : PLLFormula) : Prop := ([] : List PLLFormula) ⊢⋆ φ
