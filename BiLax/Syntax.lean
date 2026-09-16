/-
BiLax round 1 — syntax.

`BiForm`: PLL's connectives plus co-implication `⤙` (Rauszer
subtraction) and the co-lax modality `◯∃` (the left adjoint of `◯∀`).
Notation per docs/bilax-plan.md §2 (locked 2026-08-13, scratch-tested
against the repo's import surface: `⟶` belongs to mathlib's Quiver and
is never used here).

`emb` embeds `PLLFormula`; `IsForward` is the forward fragment (no
retrospective connective anywhere) — the fragment on which fallible
worlds force everything and on which exfalso is sound
(docs/bilax-plan.md §4(b): fallibility trivialises the future, the
retrospective connectives see the past).
-/
import LaxLogic.PLLNDCore

namespace BiLax

/-- Bi-lax formulas. -/
inductive BiForm where
  | prop : String → BiForm
  | bot : BiForm
  | and : BiForm → BiForm → BiForm
  | or : BiForm → BiForm → BiForm
  | imp : BiForm → BiForm → BiForm
  | coimp : BiForm → BiForm → BiForm
  | lax : BiForm → BiForm
  | colax : BiForm → BiForm
deriving DecidableEq, Repr

@[inherit_doc] scoped infixr:56 " ⇾ " => BiForm.imp
@[inherit_doc] scoped infixl:55 " ⤙ " => BiForm.coimp
@[inherit_doc] scoped prefix:75 "◯∀" => BiForm.lax
@[inherit_doc] scoped prefix:75 "◯∃" => BiForm.colax
/-- Implication with the arguments flipped (`B ⇽ A` = `A ⇾ B`). -/
scoped infixr:55 " ⇽ " => fun a b => BiForm.imp b a
/-- Co-implication with the arguments flipped (`B ⤚ A` = `A ⤙ B`). -/
scoped infixl:56 " ⤚ " => fun a b => BiForm.coimp b a

/-- `⊤ := ⊥ ⇾ ⊥`. -/
def BiForm.top : BiForm := .imp .bot .bot

/-- **The absolute falsum** `ff := ⊤ ⤙ ⊤`: forced nowhere in any
model (it needs a predecessor refuting `⊤`), in contrast with the
local falsum `⊥`, forced exactly at the fallible worlds. -/
def BiForm.ff : BiForm := .coimp .top .top

/-- The embedding of PLL. -/
def emb : PLLFormula → BiForm
  | .prop a => .prop a
  | .falsePLL => .bot
  | .and φ ψ => .and (emb φ) (emb ψ)
  | .or φ ψ => .or (emb φ) (emb ψ)
  | .ifThen φ ψ => .imp (emb φ) (emb ψ)
  | .somehow φ => .lax (emb φ)

/-- **The forward fragment**: no retrospective connective (`⤙`, `◯∃`)
anywhere.  Coincides with the image of `emb`. -/
def IsForward : BiForm → Prop
  | .prop _ => True
  | .bot => True
  | .and φ ψ => IsForward φ ∧ IsForward ψ
  | .or φ ψ => IsForward φ ∧ IsForward ψ
  | .imp φ ψ => IsForward φ ∧ IsForward ψ
  | .coimp _ _ => False
  | .lax φ => IsForward φ
  | .colax _ => False

theorem isForward_emb (φ : PLLFormula) : IsForward (emb φ) := by
  induction φ <;> simp_all [emb, IsForward]

theorem exists_emb_of_isForward :
    ∀ {A : BiForm}, IsForward A → ∃ φ, emb φ = A := by
  intro A
  induction A with
  | prop a => exact fun _ => ⟨.prop a, rfl⟩
  | bot => exact fun _ => ⟨.falsePLL, rfl⟩
  | and φ ψ ihφ ihψ =>
      rintro ⟨h1, h2⟩
      obtain ⟨a, rfl⟩ := ihφ h1
      obtain ⟨b, rfl⟩ := ihψ h2
      exact ⟨.and a b, rfl⟩
  | or φ ψ ihφ ihψ =>
      rintro ⟨h1, h2⟩
      obtain ⟨a, rfl⟩ := ihφ h1
      obtain ⟨b, rfl⟩ := ihψ h2
      exact ⟨.or a b, rfl⟩
  | imp φ ψ ihφ ihψ =>
      rintro ⟨h1, h2⟩
      obtain ⟨a, rfl⟩ := ihφ h1
      obtain ⟨b, rfl⟩ := ihψ h2
      exact ⟨.ifThen a b, rfl⟩
  | coimp φ ψ _ _ => exact fun h => absurd h not_false
  | lax φ ih =>
      intro h
      obtain ⟨a, rfl⟩ := ih h
      exact ⟨.somehow a, rfl⟩
  | colax φ _ => exact fun h => absurd h not_false

end BiLax
