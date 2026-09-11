/-
# `LaxLogic.QLL.CLP` — §3's two lax resolution rules, and what they compute

Section 3 extends resolution with two derived rules that move a constraint
through a conjunction and through an implication:

    Γ ⊢ p : ◯_Q A   Γ ⊢ q : ◯_Q B          Γ ⊢ p : ◯_Q A   Γ ⊢ r : A ⊃ B
    ─────────────────────────────  ∧◯      ─────────────────────────────  ⊃◯
      Γ ⊢ ∧◯(p, q) : ◯_Q(A ∧ B)                 Γ ⊢ ⊃◯(r, p) : ◯_Q B

and states what the resulting constraints are:

    ∧◯(p, q) = λ(w, z). p w ∧ q z
    ⊃◯(r, p) = λz. ∃m. p m ∧ z = r m

Neither is a new rule: both are *derived*, and the derivation is the same in
each case — bind the constraint with `let_Q` and return with `val_Q`.  So this
module adds nothing to the calculus.  What it does is check the two claims:
each rule is built from Fig. 5, and each stated constraint is what Fig. 6
computes for it.

`⊃◯` comes out on the nose — `Iff.rfl` — which is the sharpest form the claim
could take.  `∧◯` needs the one step the report leaves implicit, that a pair is
its own components.

## Why the premises are assumptions

The second premise of each rule is used *under* the binder the first one
introduces, so it must hold in the extended context.  Getting there from
`Γ ⊢ q : ◯_Q B` is weakening, and weakening is not available: the freshness
conditions here name a specific eigenvariable, so extending the context can
invalidate one, and repairing it needs a renaming lemma for `Derives` that is
**OPEN**.

Stating the rules over a context of assumptions avoids the question entirely
and is what resolution does anyway — `r : A ⊃ B` is a program clause.  The
interpretation results below are nonetheless fully general: they hold for every
model and every pair of constraints the environment supplies.
-/
import LaxLogic.QLL.Sound
import LaxLogic.QLL.Judgement

namespace LaxLogic.QLL.CLP

open LaxLogic.QLL LaxLogic.QLL.Surface

variable (q : Q) (A B : Form)

/-! ## `⊃◯` — propagating a constraint through an implication -/

/-- `p : ◯_Q A, r : A ⊃ B`. -/
def ctxImp : Ctx := [(.fvar "p", .circ q A), (.fvar "r", .imp A B)]

/-- `⊃◯(r, p) = let_Q z ⇐ p in val_Q (r z)`. -/
def tmImp : Pf := .letQ q (.fvar "p") (.val q (.app (.fvar "r") (.bvar 0)))

/-- The rule, derived.  Nothing outside Fig. 5 is used. -/
def impCirc : Derives (tmImp q) (ctxImp q A B) (.circ q B) :=
  .circE "z" ⟨by simp only [ctxImp, Ctx.fvP, Pf.fvP] <;> decide,
      by simp only [Pf.fvP] <;> decide⟩
    (.var (.head _))
    (.circI (.impE (.var (.tail _ (.tail _ (.head _)))) (.var (.head _))))

/-- What §3 says it computes: `⊃◯(r, p) = λz. ∃m. p m ∧ z = r m`.

On the nose — the clause of `denote` *is* the equation. -/
theorem impCirc_denote (𝔐 : Model) (φ : Val 𝔐 A → Prop) (f : Val 𝔐 A → Val 𝔐 B)
    (ρ : String → 𝔐.D) (z : Val 𝔐 B) :
    denote 𝔐 (impCirc q A B) (.cons φ (.cons f .nil)) ρ z
      ↔ ∃ m, φ m ∧ f m = z := by
  simp [impCirc, ctxImp, denote, PEnv.lookup_head, PEnv.lookup_tail]

/-- info: 'LaxLogic.QLL.CLP.impCirc' depends on axioms: [propext] -/
#guard_msgs in #print axioms impCirc

/-! ## `∧◯` — combining two constraints -/

/-- `p : ◯_Q A, q : ◯_Q B`. -/
def ctxAnd : Ctx := [(.fvar "p", .circ q A), (.fvar "q", .circ q B)]

/-- `∧◯(p, q) = let_Q w ⇐ p in let_Q z ⇐ q in val_Q (w, z)`. -/
def tmAnd : Pf :=
  .letQ q (.fvar "p")
    (.letQ q (.fvar "q") (.val q (.pair (.bvar 1) (.bvar 0))))

/-- The rule, derived. -/
def andCirc : Derives (tmAnd q) (ctxAnd q A B) (.circ q (.and A B)) :=
  .circE "w" ⟨by simp only [ctxAnd, Ctx.fvP, Pf.fvP] <;> decide,
      by simp only [Pf.fvP] <;> decide⟩
    (.var (.head _))
    (.circE "z" ⟨by simp only [ctxAnd, Ctx.fvP, Pf.fvP] <;> decide,
        by simp only [Pf.openP, Pf.fvP] <;> decide⟩
      (.var (.tail _ (.tail _ (.head _))))
      (.circI (.andI (.var (.tail _ (.head _))) (.var (.head _)))))

/-- info: 'LaxLogic.QLL.CLP.andCirc' depends on axioms: [propext] -/
#guard_msgs in #print axioms andCirc

/-- What §3 says it computes: `∧◯(p, q) = λ(w, z). p w ∧ q z`.

Not `rfl`: `denote` produces `∃w. p w ∧ ∃z. q z ∧ (w, z) = x`, and getting to
the pattern `λ(w, z)` is exactly the step of saying a pair is its own
components. -/
theorem andCirc_denote (𝔐 : Model) (φ : Val 𝔐 A → Prop) (ψ : Val 𝔐 B → Prop)
    (ρ : String → 𝔐.D) (x : Val 𝔐 A × Val 𝔐 B) :
    denote 𝔐 (andCirc q A B) (.cons φ (.cons ψ .nil)) ρ x
      ↔ φ x.1 ∧ ψ x.2 := by
  simp only [andCirc, ctxAnd, denote, PEnv.lookup_head, PEnv.lookup_tail, Prod.mk.injEq, Pf.fvar.injEq, String.reduceEq, false_and, not_false_eq_true]
  constructor
  · rintro ⟨w, hw, z, hz, rfl⟩; exact ⟨hw, hz⟩
  · rintro ⟨h1, h2⟩; exact ⟨x.1, h1, x.2, h2, rfl⟩

/-! ## Both rules are sound

Nothing is proved here: `soundness` applies, because the two proof terms
contain no individual term at all and so are trivially locally closed. -/

theorem impCirc_sound (𝔐 : Model) (η : PEnv 𝔐 (ctxImp q A B)) (ρ : String → 𝔐.D)
    (hη : CtxRefines 𝔐 ρ (ctxImp q A B) η) :
    Refines 𝔐 [] ρ (.circ q B) (denote 𝔐 (impCirc q A B) η ρ) :=
  soundness 𝔐 (impCirc q A B) ⟨trivial, trivial, trivial⟩ η ρ hη

theorem andCirc_sound (𝔐 : Model) (η : PEnv 𝔐 (ctxAnd q A B)) (ρ : String → 𝔐.D)
    (hη : CtxRefines 𝔐 ρ (ctxAnd q A B) η) :
    Refines 𝔐 [] ρ (.circ q (.and A B)) (denote 𝔐 (andCirc q A B) η ρ) :=
  soundness 𝔐 (andCirc q A B) ⟨trivial, trivial, trivial, trivial⟩ η ρ hη

/-! ## The proof terms, in surface syntax -/

#guard renderPf (tmImp Q.all) == "let∀ u ⇐ p in val∀ (r u)"
#guard renderPf (tmAnd Q.ex)  == "let∃ u ⇐ p in let∃ v ⇐ q in val∃ (u, v)"

end LaxLogic.QLL.CLP
