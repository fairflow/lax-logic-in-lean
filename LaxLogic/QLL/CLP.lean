/-
# `LaxLogic.QLL.CLP` — §3's two lax resolution rules, and what they compute

Section 3 extends resolution with two derived rules that move a constraint
through a conjunction and through an implication:

    Γ ⊢ p : ◯_Q M   Γ ⊢ q : ◯_Q N          Γ ⊢ p : ◯_Q M   Γ ⊢ r : M ⊃ N
    ─────────────────────────────  ∧◯      ─────────────────────────────  ⊃◯
      Γ ⊢ ∧◯(p, q) : ◯_Q(M ∧ N)                 Γ ⊢ ⊃◯(r, p) : ◯_Q N

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
`Γ ⊢ q : ◯_Q N` is weakening, and weakening is not available: the freshness
conditions here name a specific eigenvariable, so extending the context can
invalidate one, and repairing it needs a renaming lemma for `Derives` that is
**OPEN**.

Stating the rules over a context of assumptions avoids the question entirely
and is what resolution does anyway — `r : M ⊃ N` is a program clause.  The
interpretation results below are nonetheless fully general: they hold for every
model and every pair of constraints the environment supplies.
-/
import LaxLogic.QLL.Sound
import LaxLogic.QLL.Judgement

namespace LaxLogic.QLL.CLP

open LaxLogic.QLL LaxLogic.QLL.Surface

variable (q : Q) (M N : Form)

/-! ## `⊃◯` — propagating a constraint through an implication -/

/-- `p : ◯_Q M, r : M ⊃ N`. -/
def ctxImp : Ctx := [(.fvar "p", .circ q M), (.fvar "r", .imp M N)]

/-- `⊃◯(r, p) = let_Q z ⇐ p in val_Q (r z)`. -/
def tmImp : Pf := .letQ q (.fvar "p") (.val q (.app (.fvar "r") (.bvar 0)))

/-- The rule, derived.  Nothing outside Fig. 5 is used. -/
def impCirc : Derives (tmImp q) (ctxImp q M N) (.circ q N) :=
  .circE "z" ⟨by simp [ctxImp, Ctx.fvP, Pf.fvP], by simp [Pf.fvP]⟩
    (.var (.head _))
    (.circI (.impE (.var (.tail _ (.tail _ (.head _)))) (.var (.head _))))

/-- What §3 says it computes: `⊃◯(r, p) = λz. ∃m. p m ∧ z = r m`.

On the nose — the clause of `denote` *is* the equation. -/
theorem impCirc_denote (𝔐 : Model) (φ : Val 𝔐 M → Prop) (f : Val 𝔐 M → Val 𝔐 N)
    (ρ : String → 𝔐.D) (z : Val 𝔐 N) :
    denote 𝔐 (impCirc q M N) (.cons φ (.cons f .nil)) ρ z
      ↔ ∃ m, φ m ∧ f m = z := by
  simp [impCirc, ctxImp, denote, PEnv.lookup_head, PEnv.lookup_tail]

/-! ## `∧◯` — combining two constraints -/

/-- `p : ◯_Q M, q : ◯_Q N`. -/
def ctxAnd : Ctx := [(.fvar "p", .circ q M), (.fvar "q", .circ q N)]

/-- `∧◯(p, q) = let_Q w ⇐ p in let_Q z ⇐ q in val_Q (w, z)`. -/
def tmAnd : Pf :=
  .letQ q (.fvar "p")
    (.letQ q (.fvar "q") (.val q (.pair (.bvar 1) (.bvar 0))))

/-- The rule, derived. -/
def andCirc : Derives (tmAnd q) (ctxAnd q M N) (.circ q (.and M N)) :=
  .circE "w" ⟨by simp [ctxAnd, Ctx.fvP, Pf.fvP], by simp [Pf.fvP]⟩
    (.var (.head _))
    (.circE "z" ⟨by simp [ctxAnd, Ctx.fvP, Pf.fvP], by simp [Pf.openP, Pf.fvP]⟩
      (.var (.tail _ (.tail _ (.head _))))
      (.circI (.andI (.var (.tail _ (.head _))) (.var (.head _)))))

/-- What §3 says it computes: `∧◯(p, q) = λ(w, z). p w ∧ q z`.

Not `rfl`: `denote` produces `∃w. p w ∧ ∃z. q z ∧ (w, z) = x`, and getting to
the pattern `λ(w, z)` is exactly the step of saying a pair is its own
components. -/
theorem andCirc_denote (𝔐 : Model) (φ : Val 𝔐 M → Prop) (ψ : Val 𝔐 N → Prop)
    (ρ : String → 𝔐.D) (x : Val 𝔐 M × Val 𝔐 N) :
    denote 𝔐 (andCirc q M N) (.cons φ (.cons ψ .nil)) ρ x
      ↔ φ x.1 ∧ ψ x.2 := by
  simp only [andCirc, ctxAnd, denote, PEnv.lookup_head, PEnv.lookup_tail, Prod.mk.injEq, Pf.fvar.injEq, String.reduceEq, false_and, not_false_eq_true]
  constructor
  · rintro ⟨w, hw, z, hz, rfl⟩; exact ⟨hw, hz⟩
  · rintro ⟨h1, h2⟩; exact ⟨x.1, h1, x.2, h2, rfl⟩

/-! ## Both rules are sound

Nothing is proved here: `soundness` applies, because the two proof terms
contain no individual term at all and so are trivially locally closed. -/

theorem impCirc_sound (𝔐 : Model) (η : PEnv 𝔐 (ctxImp q M N)) (ρ : String → 𝔐.D)
    (hη : PSat 𝔐 ρ (ctxImp q M N) η) :
    Sat 𝔐 [] ρ (.circ q N) (denote 𝔐 (impCirc q M N) η ρ) :=
  soundness 𝔐 (impCirc q M N) ⟨trivial, trivial, trivial⟩ η ρ hη

theorem andCirc_sound (𝔐 : Model) (η : PEnv 𝔐 (ctxAnd q M N)) (ρ : String → 𝔐.D)
    (hη : PSat 𝔐 ρ (ctxAnd q M N) η) :
    Sat 𝔐 [] ρ (.circ q (.and M N)) (denote 𝔐 (andCirc q M N) η ρ) :=
  soundness 𝔐 (andCirc q M N) ⟨trivial, trivial, trivial, trivial⟩ η ρ hη

/-! ## The proof terms, in surface syntax -/

#guard renderPf (tmImp Q.all) == "let∀ u ⇐ p in val∀ (r u)"
#guard renderPf (tmAnd Q.ex)  == "let∃ u ⇐ p in let∃ v ⇐ q in val∃ (u, v)"

end LaxLogic.QLL.CLP
