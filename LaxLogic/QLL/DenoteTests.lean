/-
# `LaxLogic.QLL.DenoteTests` — Fig. 6 as it is written

Each of Fig. 6's equations, stated at full generality and proved by `rfl`.  Not
examples on chosen terms: these say that the *clause* of `denote` is the
equation, for every derivation.

The three `cast`s are `Val_openWith` — the report's "`|M| = |M{σ}|`" — and they
are written out rather than hidden, so what is being claimed stays visible.
-/
import LaxLogic.QLL.Denote
import LaxLogic.QLL.Judgement

namespace LaxLogic.QLL.DenoteTests

open LaxLogic.QLL LaxLogic.QLL.Surface

variable (𝔐 : Model)

/-! ## The six equations of Fig. 6 -/

/-- `val_Q(x) = λy. x = y` — the singleton constraint. -/
theorem eq_val {Γ : Ctx} {q : Q} {p : Pf} {M : Form}
    (d : Derives p Γ M) (η : PEnv 𝔐 Γ) (ρ : String → 𝔐.D) :
    denote 𝔐 (.circI (q := q) d) η ρ = fun y => denote 𝔐 d η ρ = y := rfl

/-- `(let_Q z ⇐ p in q) = λx. ∃z. p z ∧ q x` — the union over the constraint. -/
theorem eq_let {Γ : Ctx} {q : Q} {p b : Pf} {M N : Form} (z : String)
    (hz : FreshP z Γ b)
    (dp : Derives p Γ (.circ q M))
    (db : Derives (b.openPWith z) ((Pf.fvar z, M) :: Γ) (.circ q N))
    (η : PEnv 𝔐 Γ) (ρ : String → 𝔐.D) :
    denote 𝔐 (.circE z hz dp db) η ρ
      = fun x => ∃ w, denote 𝔐 dp η ρ w ∧ denote 𝔐 db (.cons w η) ρ x := rfl

/-- `⟨p | x⟩ = λx. p`. -/
theorem eq_gen {Γ : Ctx} {p : Pf} {M : Form} (a : String) (ha : FreshI a Γ p M)
    (d : Derives (p.openIWith a) Γ (M.openWith a))
    (η : PEnv 𝔐 Γ) (ρ : String → 𝔐.D) :
    denote 𝔐 (.allI a ha d) η ρ
      = fun e => cast (Val_openWith 𝔐 a M) (denote 𝔐 d η (upd 𝔐 ρ a e)) := rfl

/-- `π_t(p) = p t`. -/
theorem eq_inst {Γ : Ctx} {p : Pf} {M N : Form} (t : Tm)
    (d : Derives p Γ (.forall_ M)) (h : N = M.openAt 0 t)
    (η : PEnv 𝔐 Γ) (ρ : String → 𝔐.D) :
    denote 𝔐 (.allE t d h) η ρ
      = cast ((congrArg (Val 𝔐) h).trans (Val_openAt 𝔐 t M 0)).symm
          (denote 𝔐 d η ρ (evalTm 𝔐 [] ρ t)) := rfl

/-- `ι_t(p) = (t, p)`. -/
theorem eq_pack {Γ : Ctx} {p : Pf} {M : Form} (t : Tm)
    (d : Derives p Γ (M.openAt 0 t)) (η : PEnv 𝔐 Γ) (ρ : String → 𝔐.D) :
    denote 𝔐 (.exI t d) η ρ
      = (evalTm 𝔐 [] ρ t, cast (Val_openAt 𝔐 t M 0) (denote 𝔐 d η ρ)) := rfl

/-- `case r of [ι_x(z) → p] = p{π₁(r)/x, π₂(r)/z}` — the two projections go to
the individual and the proof variable respectively. -/
theorem eq_caseEx {Γ : Ctx} {r p : Pf} {M K : Form} (a z : String)
    (ha : FreshI a Γ p M) (hK : a ∉ K.fv) (hz : FreshP z Γ p)
    (dr : Derives r Γ (.exists_ M))
    (db : Derives ((p.openIWith a).openPWith z) ((Pf.fvar z, M.openWith a) :: Γ) K)
    (η : PEnv 𝔐 Γ) (ρ : String → 𝔐.D) :
    denote 𝔐 (.exE a z ha hK hz dr db) η ρ
      = denote 𝔐 db
          (.cons (cast (Val_openWith 𝔐 a M).symm (denote 𝔐 dr η ρ).2) η)
          (upd 𝔐 ρ a (denote 𝔐 dr η ρ).1) := rfl

/-! ## The clauses Fig. 6 leaves to HOL

Pairing, projection, injection, `case`, `λ` and application are already HOL
terms in the report, so the figure does not list them.  They are still choices
here, and these say which. -/

theorem eq_pair {Γ : Ctx} {p q : Pf} {M N : Form}
    (d : Derives p Γ M) (e : Derives q Γ N) (η : PEnv 𝔐 Γ) (ρ : String → 𝔐.D) :
    denote 𝔐 (.andI d e) η ρ = (denote 𝔐 d η ρ, denote 𝔐 e η ρ) := rfl

theorem eq_fst {Γ : Ctx} {r : Pf} {M N : Form}
    (d : Derives r Γ (.and M N)) (η : PEnv 𝔐 Γ) (ρ : String → 𝔐.D) :
    denote 𝔐 (.andE₁ d) η ρ = (denote 𝔐 d η ρ).1 := rfl

theorem eq_lam {Γ : Ctx} {p : Pf} {M N : Form} (z : String) (hz : FreshP z Γ p)
    (d : Derives (p.openPWith z) ((Pf.fvar z, M) :: Γ) N)
    (η : PEnv 𝔐 Γ) (ρ : String → 𝔐.D) :
    denote 𝔐 (.impI z hz d) η ρ = fun v => denote 𝔐 d (.cons v η) ρ := rfl

theorem eq_app {Γ : Ctx} {p q : Pf} {M N : Form}
    (d : Derives p Γ (.imp M N)) (e : Derives q Γ M)
    (η : PEnv 𝔐 Γ) (ρ : String → 𝔐.D) :
    denote 𝔐 (.impE d e) η ρ = denote 𝔐 d η ρ (denote 𝔐 e η ρ) := rfl

/-! ## `val` is the unit of `let`

Fig. 6's two special equations are the unit and bind of the powerset monad on
`|M| ⇒ 𝔹`.  Left unit, pointwise, so no function extensionality is needed:
binding a singleton is the same as substituting into it. -/

theorem let_val_left_unit {α β : Type} (a : α) (f : α → β → Prop) (x : β) :
    (∃ z, (fun y => a = y) z ∧ f z x) ↔ f a x :=
  ⟨fun ⟨_, hz, hf⟩ => hz ▸ hf, fun h => ⟨a, rfl, h⟩⟩

/-! ## Computed, in a concrete model

`𝔅` has one individual and `Bool` for atoms.  `⟦val∀ *⟧` is the singleton on
`|⊤| = Unit`, so it admits `()` and nothing else — there is nothing else. -/

def 𝔅 : Model where
  D := Unit
  C := Bool
  fn := fun _ _ => ()
  atom := fun _ _ c => c = true
  d₀ := ()
  c₀ := false

def ρ₀ : String → 𝔅.D := fun _ => ()

def d_val : qd[⊢ val∀ * : ◯∀ ⊤] := .circI .topI

example : denoteC 𝔅 d_val ρ₀ () := rfl

/-- And the derivation of `⊤ ⊃ ⊤` denotes the identity on `|⊤|`. -/
def d_id : qd[⊢ λu. u : ⊤ ⊃ ⊤] := .impI "u" ⟨by decide, by decide⟩ (.var (by decide))

example : denoteC 𝔅 d_id ρ₀ () = () := rfl

/-! ## Axioms

Pinned, not asserted clean.  Two sources, neither of them the interpretation:

* `Quot.sound` enters `denote` at exactly one point — `PEnv.lookup` compares two
  `Pf × Form` values, and the derived `DecidableEq Form` / `DecidableEq Pf` rest
  on `Tm.beq_iff`, whose nine cases are `simp` proofs.  Removing it means
  rebuilding `DecidableEq Tm` as a direct structural decision procedure instead
  of `decidable_of_iff ∘ beq_iff`; that is a change to `Syntax.lean`, and it is
  not made here.
* `propext` reaches `evalTm` and `Sat` through the equation compiler's own
  machinery, so it is below anything this development chose.

What *is* clean is everything proved or defined here by structural recursion
alone: the transport `Val_openAt` and the default `Val.default`.  Neither the
refinement types nor the report's `|M| = |M{σ}|` costs an axiom. -/

/-- info: 'LaxLogic.QLL.denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms denote

/-- info: 'LaxLogic.QLL.PEnv.lookup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms PEnv.lookup

/-- info: 'LaxLogic.QLL.Val_openAt' does not depend on any axioms -/
#guard_msgs in #print axioms Val_openAt

/-- info: 'LaxLogic.QLL.Val.default' does not depend on any axioms -/
#guard_msgs in #print axioms Val.default

/-- info: 'LaxLogic.QLL.evalTm' depends on axioms: [propext] -/
#guard_msgs in #print axioms evalTm

/-- info: 'LaxLogic.QLL.Sat' depends on axioms: [propext] -/
#guard_msgs in #print axioms Sat

end LaxLogic.QLL.DenoteTests
