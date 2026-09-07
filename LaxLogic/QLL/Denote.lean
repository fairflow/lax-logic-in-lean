/-
# `LaxLogic.QLL.Denote` — Fig. 6: the interpretation of proof terms

Fig. 6 reads as six equations between terms:

    ⟨p | x⟩   = λx. p                 π_t(p)                = p t
    ι_t(p)    = (t, p)                case r of [ι_x(z)→p]  = p{π₁(r)/x, π₂(r)/z}
    val_Q(x)  = λy. x = y             (let_Q z ⇐ p in q)    = λx. ∃z. p z ∧ q x

    c = d      (c, d ∈ Φ,  ⊢_B c ⟺ d)

In the report they *are* equations, because a proof term there is already a HOL
term and these constructors are notation for HOL terms.  Here `Pf` is a
separate inductive, so the same content becomes a **function** — and it cannot
be a function of the proof term alone, since `Val 𝔐 M` depends on the formula.
It is a function of the derivation:

    ⟦·⟧ : Derives p Γ M → PEnv 𝔐 Γ → (String → 𝔐.D) → Val 𝔐 M

Each of Fig. 6's equations reappears below as one defining clause, and
`DenoteTests.lean` checks each by `rfl` against the equation as written.

## What the six equations say

`val_Q` and `let_Q` are the two that are not already HOL.  With `|◯_Q M| =
|M| ⇒ 𝔹`, a constraint *is* a predicate on `|M|`, and then

    ⟦val_Q p⟧ = fun y => ⟦p⟧ = y                       the singleton {⟦p⟧}
    ⟦let_Q z ⇐ p in q⟧ = fun x => ∃ z, ⟦p⟧ z ∧ ⟦q⟧ z x  the union ⋃_{z ∈ p} q z

— unit and bind of the powerset monad.  Fig. 6 gives one pair of equations for
both modalities, exactly as Fig. 5 gives one pair of rules: the whole of the
`◯∀`/`◯∃` distinction sits in Fig. 4's *reading* of a constraint, never in how
constraints are built.  `InterpTests.lean` separates them there.

The last equation, `c = d` for base-provably-equivalent constraint formulas, is
about the constraint language Φ, which this development does not embed: `Φ` is
Lean itself here, and the equation holds of `Prop` by `propext`.  Nothing in
this module needs it.

## Two transports, both forced by the locally nameless representation

`∀I` concludes `∀.M` from a premise about `M.openWith a`, and `∃E` puts
`M.openWith a` into the context.  `Val` must not notice, and it does not —
`Val_openWith` is the report's "`|M| = |M{σ}|`" — but the equation is not
definitional, so it appears as a `cast`.  That is the whole cost of the
representation, and it is confined to three clauses.

## OPEN

Soundness — if the environment satisfies `Γ` then `Sat 𝔐 [] ρ M ⟦d⟧` — is
statable now and is **not proved here**.  It needs the opening lemma relating
`Sat env ρ[a↦e] (M.openWith a)` to `Sat (e :: env) ρ M`, which is the standard
locally nameless substitution lemma and has not been done.
-/
import LaxLogic.QLL.Interp
import LaxLogic.QLL.Deriv

namespace LaxLogic.QLL

variable (𝔐 : Model)

/-! ## Environments for the proof variables

One value per context entry, at that entry's refinement type.  A list rather
than a function of a membership proof: `e ∈ Γ` is a `Prop` with two
constructors, so it cannot be eliminated into `Type`. -/

/-- A value for every entry of `Γ`, at that entry's refinement type. -/
inductive PEnv : Ctx → Type where
  | nil : PEnv []
  | cons {e : Pf × Form} {Γ : Ctx} : Val 𝔐 e.2 → PEnv Γ → PEnv (e :: Γ)

/--
The value of an entry.

Decided by equality on the *pair*, not the name, and so it agrees with
`Ctx.lookup?` on the shadowing case.  It cannot depend on the membership proof
— `e ∈ Γ` is a `Prop` — and it does not: the proof is used only to rule out the
empty context.
-/
def PEnv.lookup : {Γ : Ctx} → PEnv 𝔐 Γ → (e : Pf × Form) → e ∈ Γ → Val 𝔐 e.2
  | [],      .nil,        _, h => absurd h (fun hh => nomatch hh)
  | (a :: _), .cons v η, e, h =>
      if he : e = a then
        cast (congrArg (fun x : Pf × Form => Val 𝔐 x.2) he).symm v
      else
        PEnv.lookup η e (by
          cases h with
          | head => exact absurd rfl he
          | tail _ h' => exact h')

/-! `lookup` decides an equality of `Pf × Form`, which does not *compute* when
the formulas are variables — `Form.decEq M M` is stuck on an opaque `M`.  These
two say what it returns anyway, by `dif_pos`/`dif_neg` rather than by
evaluation, and are what makes a derivation with symbolic formulas unfold. -/

theorem PEnv.lookup_head {e : Pf × Form} {Γ : Ctx}
    (v : Val 𝔐 e.2) (η : PEnv 𝔐 Γ) (h : e ∈ e :: Γ) :
    PEnv.lookup 𝔐 (.cons v η) e h = v := by
  simp [PEnv.lookup]

theorem PEnv.lookup_tail {a e : Pf × Form} {Γ : Ctx}
    (v : Val 𝔐 a.2) (η : PEnv 𝔐 Γ) (h : e ∈ a :: Γ) (hne : ¬ (e = a)) :
    PEnv.lookup 𝔐 (.cons v η) e h
      = PEnv.lookup 𝔐 η e ((List.mem_cons.mp h).resolve_left hne) := by
  simp [PEnv.lookup, hne]

/-- `ρ` with the individual `a` sent to `e`. -/
def upd (ρ : String → 𝔐.D) (a : String) (e : 𝔐.D) : String → 𝔐.D :=
  fun y => if y = a then e else ρ y

/-! ## Fig. 6 -/

/--
The constraint a derivation denotes.

One clause per rule of Fig. 5; the six clauses that are Fig. 6's own equations
are marked.  The three `cast`s are `Val_openWith`, the report's `|M| = |M{σ}|`.
-/
def denote : {Γ : Ctx} → {p : Pf} → {M : Form} →
    Derives p Γ M → PEnv 𝔐 Γ → (String → 𝔐.D) → Val 𝔐 M
  | _, _, _, .var h,      η, _ => PEnv.lookup 𝔐 η _ h
  | _, _, _, .topI,       _, _ => ()
  -- ex falso: our addition, and the reason `Model` carries `d₀`/`c₀`
  | _, _, _, .botE _,     _, _ => Val.default 𝔐 _
  | _, _, _, .andI d e,   η, ρ => (denote d η ρ, denote e η ρ)
  | _, _, _, .andE₁ d,    η, ρ => (denote d η ρ).1
  | _, _, _, .andE₂ d,    η, ρ => (denote d η ρ).2
  | _, _, _, .orI₁ d,     η, ρ => Sum.inl (denote d η ρ)
  | _, _, _, .orI₂ d,     η, ρ => Sum.inr (denote d η ρ)
  | _, _, _, .orE _ _ _ _ dr d₁ d₂, η, ρ =>
      match denote dr η ρ with
      | .inl a => denote d₁ (.cons a η) ρ
      | .inr b => denote d₂ (.cons b η) ρ
  | _, _, _, .impI _ _ d, η, ρ => fun v => denote d (.cons v η) ρ
  | _, _, _, .impE d e,   η, ρ => (denote d η ρ) (denote e η ρ)
  -- Fig. 6: val_Q(x) = λy. x = y
  | _, _, _, .circI d,    η, ρ => fun y => denote d η ρ = y
  -- Fig. 6: (let_Q z ⇐ p in q) = λx. ∃z. p z ∧ q x
  | _, _, _, .circE _ _ dp db, η, ρ =>
      fun x => ∃ z, denote dp η ρ z ∧ denote db (.cons z η) ρ x
  -- Fig. 6: ⟨p | x⟩ = λx. p
  | _, _, _, .allI a _ d, η, ρ =>
      fun e => cast (Val_openWith 𝔐 a _) (denote d η (upd 𝔐 ρ a e))
  -- Fig. 6: π_t(p) = p t
  | _, _, _, .allE t d h, η, ρ =>
      cast ((congrArg (Val 𝔐) h).trans (Val_openAt 𝔐 t _ 0)).symm
        (denote d η ρ (evalTm 𝔐 [] ρ t))
  -- Fig. 6: ι_t(p) = (t, p)
  | _, _, _, .exI t d,    η, ρ =>
      (evalTm 𝔐 [] ρ t, cast (Val_openAt 𝔐 t _ 0) (denote d η ρ))
  -- Fig. 6: case r of [ι_x(z) → p] = p{π₁(r)/x, π₂(r)/z}
  | _, _, _, .exE a _ _ _ _ dr db, η, ρ =>
      let w := denote dr η ρ
      denote db (.cons (cast (Val_openWith 𝔐 a _).symm w.2) η) (upd 𝔐 ρ a w.1)

@[inherit_doc] notation "⟦" d "⟧(" η ", " ρ ")" => denote _ d η ρ

/-- A derivation from the empty context denotes a constraint outright. -/
def denoteC {p : Pf} {M : Form} (d : Derives p [] M) (ρ : String → 𝔐.D) : Val 𝔐 M :=
  denote 𝔐 d .nil ρ

end LaxLogic.QLL
