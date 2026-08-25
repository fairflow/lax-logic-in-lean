/-
BiLax round 1 — the Hilbert/ND reference system `BiLaxND`.

Local consequence (wBIL-style; docs/bilax-plan.md §5).  The FORWARD
rules are PLL's `LaxND` verbatim over `BiForm`, with exfalso
FRAGMENT-RELATIVE (§4(b)): `⊥ ⊢ φ` only for forward `φ`.

The RETROSPECTIVE rules (`⤙`, `◯∃`) are THEOREM-LEVEL (empty
context): a context forced at `w` need not be forced at a predecessor,
so context-ful retrospective rules are unsound — the same
future/past asymmetry as fragment-relative exfalso, appearing on the
proof-theory side.  The four rules are the residuation pairs:

    coimpMin  / coimpMax :  ⊢ A ⇾ B ∨ C   ⟷   ⊢ (A ⤙ B) ⇾ C
    adjL      / adjR     :  ⊢ ◯∃A ⇾ B     ⟷   ⊢ A ⇾ ◯∀B

plus the axiom `A ⇾ (B ∨ (A ⤙ B))` and `◯∃`-monotonicity.  Unit and
counit are DERIVED (`biLax_unit`, `biLax_counit`) — nothing of the
shape `◯∃A ⊢ A` appears anywhere (the corrected-counit lesson,
handoff §4.1).
-/
import BiLax.Frames

namespace BiLax

/-- The bi-lax Hilbert/ND system, local consequence. -/
inductive BiLaxND : List BiForm → BiForm → Type
  | iden {Γ : List BiForm} {φ : BiForm} (h : φ ∈ Γ) : BiLaxND Γ φ
  | falsoElim {Γ : List BiForm} (φ : BiForm) (hf : IsForward φ)
      (p : BiLaxND Γ .bot) : BiLaxND Γ φ
  | impIntro {Γ : List BiForm} {φ ψ : BiForm}
      (p : BiLaxND (φ :: Γ) ψ) : BiLaxND Γ (φ ⇾ ψ)
  | impElim {Γ : List BiForm} {φ ψ : BiForm}
      (p₁ : BiLaxND Γ (φ ⇾ ψ)) (p₂ : BiLaxND Γ φ) : BiLaxND Γ ψ
  | andIntro {Γ : List BiForm} {φ ψ : BiForm}
      (p₁ : BiLaxND Γ φ) (p₂ : BiLaxND Γ ψ) : BiLaxND Γ (.and φ ψ)
  | andElim1 {Γ : List BiForm} {φ ψ : BiForm}
      (p : BiLaxND Γ (.and φ ψ)) : BiLaxND Γ φ
  | andElim2 {Γ : List BiForm} {φ ψ : BiForm}
      (p : BiLaxND Γ (.and φ ψ)) : BiLaxND Γ ψ
  | orIntro1 {Γ : List BiForm} {φ ψ : BiForm}
      (p : BiLaxND Γ φ) : BiLaxND Γ (.or φ ψ)
  | orIntro2 {Γ : List BiForm} {φ ψ : BiForm}
      (p : BiLaxND Γ ψ) : BiLaxND Γ (.or φ ψ)
  | orElim {Γ : List BiForm} {φ ψ χ : BiForm}
      (p₀ : BiLaxND Γ (.or φ ψ))
      (p₁ : BiLaxND (φ :: Γ) χ) (p₂ : BiLaxND (ψ :: Γ) χ) : BiLaxND Γ χ
  | laxIntro {Γ : List BiForm} {φ : BiForm}
      (p : BiLaxND Γ φ) : BiLaxND Γ (◯∀φ)
  | laxElim {Γ : List BiForm} {φ ψ : BiForm}
      (p₁ : BiLaxND Γ (◯∀φ)) (p₂ : BiLaxND (φ :: Γ) (◯∀ψ)) :
      BiLaxND Γ (◯∀ψ)
  -- the retrospective fragment: theorem-level rules
  | coimpDisj {Γ : List BiForm} (φ ψ : BiForm) :
      BiLaxND Γ (φ ⇾ (.or ψ (φ ⤙ ψ)))
  | coimpMin {φ ψ χ : BiForm}
      (p : BiLaxND [] (φ ⇾ (.or ψ χ))) : BiLaxND [] ((φ ⤙ ψ) ⇾ χ)
  | coimpMax {φ ψ χ : BiForm}
      (p : BiLaxND [] ((φ ⤙ ψ) ⇾ χ)) : BiLaxND [] (φ ⇾ (.or ψ χ))
  | colaxMono {φ ψ : BiForm}
      (p : BiLaxND [] (φ ⇾ ψ)) : BiLaxND [] ((◯∃φ) ⇾ (◯∃ψ))
  | adjL {φ ψ : BiForm}
      (p : BiLaxND [] ((◯∃φ) ⇾ ψ)) : BiLaxND [] (φ ⇾ (◯∀ψ))
  | adjR {φ ψ : BiForm}
      (p : BiLaxND [] (φ ⇾ (◯∀ψ))) : BiLaxND [] ((◯∃φ) ⇾ ψ)

/-- The identity implication. -/
def BiLaxND.impSelf (φ : BiForm) : BiLaxND [] (φ ⇾ φ) :=
  .impIntro (.iden (by simp))

/-- **Unit, derived**: `⊢ A ⇾ ◯∀◯∃A` — `adjL` on the identity. -/
def biLax_unit (φ : BiForm) : BiLaxND [] (φ ⇾ (◯∀(◯∃φ))) :=
  .adjL (.impSelf _)

/-- **Counit, derived**: `⊢ ◯∃◯∀A ⇾ A` — `adjR` on the identity. -/
def biLax_counit (φ : BiForm) : BiLaxND [] ((◯∃(◯∀φ)) ⇾ φ) :=
  .adjR (.impSelf _)

/-- The co-negation of `⊤` is refuted: `⊢ ff ⇾ ⊥` (via `coimpMin` on
`⊤ ⇾ ⊤ ∨ ⊥`). -/
def biLax_ff_bot : BiLaxND [] (BiForm.ff ⇾ .bot) :=
  .coimpMin (.impIntro (.orIntro1 (.iden (by simp))))

end BiLax
