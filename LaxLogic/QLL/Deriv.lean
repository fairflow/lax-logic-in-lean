/-
# `LaxLogic.QLL.Deriv` — Fig. 5 as an inductive family

The natural deduction rules of

> A. Fairtlough, A. Mendler and X. Cheng, *Abstraction and refinement in higher
> order logic*, TPHOLs 2001, LNCS 2152, 201–216, Fig. 5,

one constructor per rule, transcribed from the page.  The figure is a *term
assignment* system, so this is a typing relation on `Pf` rather than an
intrinsically typed family: proof terms stay plain data that a checker can
validate and that the Fig. 6 interpretation can consume.

## No green slime

Every constructor's *conclusion* has variable or constructor indices only.
One would otherwise have a computed one — `allE` (`Form.openAt 0 t A`) — and it
is written instead with a fresh index variable and an equational premise.  Computation in a *premise* is harmless;
in a conclusion it is not invertible, so `cases` and dependent matching cannot
decompose it and every proof over the family has to transport across an
equation the unifier will not solve.  `#slime LaxLogic.QLL.Derives` reports
17 clean constructors.

This matters more here than it would for a `Prop`-valued family.  `Derives` is
`Type`-valued, so derivations are data that gets taken apart, and an
uninvertible index blocks the taking apart rather than merely making a proof
awkward.

## Fig. 5's `Subst` is deliberately absent

The figure lists `Subst` among the deduction rules:

    Γ, z:A, Γ' ⊢ q : B
    ─────────────────────────  (p :: |A|)
    Γ, p:A, Γ' ⊢ q{p/z} : B

It is not a rule of this family, for three reasons that agree.

*It is not admissible, and it establishes nothing.*  Its side condition is
`p :: |A|`, HOL typing, not `p : A`, refinement.  Replacing the entry turns
every use of `var` on `z` into an occurrence of `p` that would need
`Γ ⊢ p : A` — exactly what is not available.  So removing it removes no
derivable judgement.

*It is invisible in the proof term.*  It produces `q.substP x p`, which is just
some term, so no checker driven by the term could ever be complete for a family
containing it.  With it gone, `check` is complete for all of `Derivable` rather
than for a fragment, and no statement needs an `isSubstFree` precondition.

*Its content is semantic, and reappears there.*  What `Subst` records is

    Derivable (Γ ++ (x,A) :: Γ') q B → p ⊨ A → q{p/x} ⊨ B

— the substitution is justified exactly when the obligation is discharged.
That is a lemma about the Fig. 4 refinement reading, not a rule of the
calculus, and it matches the paper's own Fig. 9 picture in which abstraction
and refinement are the outer loop *around* deduction rather than steps inside
it.  `Pf.substP` is kept in `Syntax.lean` for that lemma.

(Matthew's call, 2026-09-06, before the soundness proof was written against the
larger family.)

Two further departures, both deliberate and both flagged at the constructor.

* **`botE`.**  Fig. 5 has `false` in the syntax and no rule for it.  Ex falso
  is added.

* **Exists-fresh side conditions.**  The figure's "`x` not free in `Γ`" becomes
  a named witness plus a freshness hypothesis.  This is the exists-fresh
  discipline rather than cofinite quantification: it is exactly what a checker
  implements, since the checker picks one canonical fresh name.  The price is
  that renaming is a lemma rather than free, and that lemma is harness work.

The modal rules are `Q`-parametric, as printed: the figure's side condition
reads only "if `Q = ∀` or `Q = ∃`", so `circI` and `circE` are one rule each,
with `Q` inert.  What tells the two modalities apart is the Fig. 4 refinement
reading, which is not part of this judgement.
-/
import LaxLogic.QLL.Syntax

namespace LaxLogic.QLL

/-- A proof variable usable to open a binder: absent from the context and from
the body being opened, so opening cannot capture. -/
def FreshP (z : String) (Γ : Ctx) (p : Pf) : Prop :=
  z ∉ Ctx.fvP Γ ∧ z ∉ p.fvP

/-- An individual usable to open a binder. -/
def FreshI (a : String) (Γ : Ctx) (p : Pf) (A : Form) : Prop :=
  a ∉ Ctx.fvI Γ ∧ a ∉ p.fvI ∧ a ∉ A.fv

/--
`Derives p Γ A` is the figure's `Γ ⊢ p : A`, with the realiser first.

`Γ` is a list of the paper's refinement pairs.  Rule `var` fires only on a
*variable* entry and `impI` can abstract only a variable entry, so no rule here
can use a non-variable one: `Derives` is insensitive to them, and they are
carried purely as the residual obligations the semantics will quantify over.
-/
inductive Derives : Pf → Ctx → Form → Type where
  /-- `I`.  Γ, z:A, Γ' ⊢ z : A — a variable entry, looked up by name. -/
  | var {Γ : Ctx} {x : String} {A : Form} :
      (Pf.fvar x, A) ∈ Γ →
      Derives (.fvar x) Γ A
  /-- `true_I`. -/
  | topI {Γ : Ctx} :
      Derives .star Γ .top
  /-- Ex falso.  **Not in Fig. 5**; the figure has `false` in the syntax with
  no elimination rule. -/
  | botE {Γ : Ctx} {p : Pf} {A : Form} :
      Derives p Γ .bot →
      Derives (.exf A p) Γ A
  /-- `∧I`. -/
  | andI {Γ : Ctx} {p q : Pf} {A B : Form} :
      Derives p Γ A → Derives q Γ B →
      Derives (.pair p q) Γ (.and A B)
  /-- `∧E`, first projection. -/
  | andE₁ {Γ : Ctx} {r : Pf} {A B : Form} :
      Derives r Γ (.and A B) →
      Derives (.fst r) Γ A
  /-- `∧E`, second projection. -/
  | andE₂ {Γ : Ctx} {r : Pf} {A B : Form} :
      Derives r Γ (.and A B) →
      Derives (.snd r) Γ B
  /-- `∨I`, left. -/
  | orI₁ {Γ : Ctx} {p : Pf} {A B : Form} :
      Derives p Γ A →
      Derives (.inl p) Γ (.or A B)
  /-- `∨I`, right. -/
  | orI₂ {Γ : Ctx} {q : Pf} {A B : Form} :
      Derives q Γ B →
      Derives (.inr q) Γ (.or A B)
  /-- `∨E`.  Two branches, each binding its own proof variable. -/
  | orE {Γ : Ctx} {r p q : Pf} {A B K : Form} (y z : String) :
      FreshP y Γ p → FreshP z Γ q →
      Derives r Γ (.or A B) →
      Derives (p.openPWith y) ((Pf.fvar y, A) :: Γ) K →
      Derives (q.openPWith z) ((Pf.fvar z, B) :: Γ) K →
      Derives (.caseOr r p q) Γ K
  /-- `⊃I`.  Abstracts a *variable* entry; `λp.…` for non-variable `p` is not
  a term, which is why a substituted entry could never be discharged. -/
  | impI {Γ : Ctx} {p : Pf} {A B : Form} (z : String) :
      FreshP z Γ p →
      Derives (p.openPWith z) ((Pf.fvar z, A) :: Γ) B →
      Derives (.lam p) Γ (.imp A B)
  /-- `⊃E`. -/
  | impE {Γ : Ctx} {p q : Pf} {A B : Form} :
      Derives p Γ (.imp A B) → Derives q Γ A →
      Derives (.app p q) Γ B
  /-- `◯I`, for either modality: the figure's side condition is only
  "if `Q = ∀` or `Q = ∃`". -/
  | circI {Γ : Ctx} {q : Q} {p : Pf} {A : Form} :
      Derives p Γ A →
      Derives (.val q p) Γ (.circ q A)
  /-- `◯E`, for either modality.  Both premises and the conclusion carry the
  *same* `Q`; the figure permits no mixing. -/
  | circE {Γ : Ctx} {q : Q} {p b : Pf} {A B : Form} (z : String) :
      FreshP z Γ b →
      Derives p Γ (.circ q A) →
      Derives (b.openPWith z) ((Pf.fvar z, A) :: Γ) (.circ q B) →
      Derives (.letQ q p b) Γ (.circ q B)
  /-- `∀I`, written `⟨p | x⟩`.  Binds an *individual*, and so uses a different
  abstraction from `⊃I`'s `λ`. -/
  | allI {Γ : Ctx} {p : Pf} {A : Form} (a : String) :
      FreshI a Γ p A →
      Derives (p.openIWith a) Γ (A.openWith a) →
      Derives (.gen p) Γ (.forall_ A)
  /-- `∀E`, written `π_t(p)`.  The equational premise keeps the conclusion's
  index a variable; see the note on green slime above. -/
  | allE {Γ : Ctx} {p : Pf} {A B : Form} (t : Tm) :
      Derives p Γ (.forall_ A) →
      B = A.openAt 0 t →
      Derives (.inst t p) Γ B
  /-- `∃I`, written `ι_t(p)`. -/
  | exI {Γ : Ctx} {p : Pf} {A : Form} (t : Tm) :
      Derives p Γ (A.openAt 0 t) →
      Derives (.pack t p) Γ (.exists_ A)
  /-- `∃E`.  Binds an individual *and* a proof variable in the one branch —
  the only rule that binds in both sorts at once. -/
  | exE {Γ : Ctx} {r p : Pf} {A K : Form} (a z : String) :
      FreshI a Γ p A → a ∉ K.fv → FreshP z Γ p →
      Derives r Γ (.exists_ A) →
      Derives ((p.openIWith a).openPWith z) ((Pf.fvar z, A.openWith a) :: Γ) K →
      Derives (.caseEx r p) Γ K

@[inherit_doc] notation:40 Γ " ⊢qll " p " : " A => Derives p Γ A

/-! ## The `Prop`-valued view

`Derives` is `Type`-valued, so a derivation is *data*: it can be transformed,
normalised, and — the point, for this paper — it determines the constraint.
Proof irrelevance would identify derivations that extract different
constraints, so collapsing into `Prop` at the definition would have been wrong.

Where irrelevance IS wanted, `Nonempty` supplies it and every rule lifts in one
line.  There is only ever one family, so there is no equivalence to prove.
(Matthew's design, 2026-09-06.)

Note the asymmetry that makes this the right way round: `Derives → Derivable`
is `Nonempty.intro`, while the reverse does not exist, and `Nonempty`
eliminates only into `Prop`.  So the data is available exactly when it is
sound to have it. -/

/-- Derivability as a proposition: some derivation exists. -/
abbrev Derivable (p : Pf) (Γ : Ctx) (A : Form) : Prop := Nonempty (Derives p Γ A)

namespace Derivable

theorem var {Γ x A} (h : (Pf.fvar x, A) ∈ Γ) : Derivable (.fvar x) Γ A := ⟨.var h⟩

theorem topI {Γ} : Derivable .star Γ .top := ⟨.topI⟩

theorem botE {Γ p A} : Derivable p Γ .bot → Derivable (.exf A p) Γ A
  | ⟨d⟩ => ⟨.botE d⟩

theorem andI {Γ p q A B} : Derivable p Γ A → Derivable q Γ B →
    Derivable (.pair p q) Γ (.and A B)
  | ⟨d⟩, ⟨e⟩ => ⟨.andI d e⟩

theorem andE₁ {Γ r A B} : Derivable r Γ (.and A B) → Derivable (.fst r) Γ A
  | ⟨d⟩ => ⟨.andE₁ d⟩

theorem andE₂ {Γ r A B} : Derivable r Γ (.and A B) → Derivable (.snd r) Γ B
  | ⟨d⟩ => ⟨.andE₂ d⟩

theorem orI₁ {Γ p A B} : Derivable p Γ A → Derivable (.inl p) Γ (.or A B)
  | ⟨d⟩ => ⟨.orI₁ d⟩

theorem orI₂ {Γ q A B} : Derivable q Γ B → Derivable (.inr q) Γ (.or A B)
  | ⟨d⟩ => ⟨.orI₂ d⟩

theorem orE {Γ r p q A B K} (y z : String) (hy : FreshP y Γ p) (hz : FreshP z Γ q) :
    Derivable r Γ (.or A B) →
    Derivable (p.openPWith y) ((Pf.fvar y, A) :: Γ) K →
    Derivable (q.openPWith z) ((Pf.fvar z, B) :: Γ) K →
    Derivable (.caseOr r p q) Γ K
  | ⟨d⟩, ⟨e⟩, ⟨f⟩ => ⟨.orE y z hy hz d e f⟩

theorem impI {Γ p A B} (z : String) (hz : FreshP z Γ p) :
    Derivable (p.openPWith z) ((Pf.fvar z, A) :: Γ) B →
    Derivable (.lam p) Γ (.imp A B)
  | ⟨d⟩ => ⟨.impI z hz d⟩

theorem impE {Γ p q A B} : Derivable p Γ (.imp A B) → Derivable q Γ A →
    Derivable (.app p q) Γ B
  | ⟨d⟩, ⟨e⟩ => ⟨.impE d e⟩

theorem circI {Γ q p A} : Derivable p Γ A → Derivable (.val q p) Γ (.circ q A)
  | ⟨d⟩ => ⟨.circI d⟩

theorem circE {Γ q p b A B} (z : String) (hz : FreshP z Γ b) :
    Derivable p Γ (.circ q A) →
    Derivable (b.openPWith z) ((Pf.fvar z, A) :: Γ) (.circ q B) →
    Derivable (.letQ q p b) Γ (.circ q B)
  | ⟨d⟩, ⟨e⟩ => ⟨.circE z hz d e⟩

theorem allI {Γ p A} (a : String) (ha : FreshI a Γ p A) :
    Derivable (p.openIWith a) Γ (A.openWith a) → Derivable (.gen p) Γ (.forall_ A)
  | ⟨d⟩ => ⟨.allI a ha d⟩

theorem allE {Γ p A B} (t : Tm) (h : B = A.openAt 0 t) :
    Derivable p Γ (.forall_ A) → Derivable (.inst t p) Γ B
  | ⟨d⟩ => ⟨.allE t d h⟩

theorem exI {Γ p A} (t : Tm) : Derivable p Γ (A.openAt 0 t) →
    Derivable (.pack t p) Γ (.exists_ A)
  | ⟨d⟩ => ⟨.exI t d⟩

theorem exE {Γ r p A K} (a z : String) (ha : FreshI a Γ p A) (hK : a ∉ K.fv)
    (hz : FreshP z Γ p) :
    Derivable r Γ (.exists_ A) →
    Derivable ((p.openIWith a).openPWith z) ((Pf.fvar z, A.openWith a) :: Γ) K →
    Derivable (.caseEx r p) Γ K
  | ⟨d⟩, ⟨e⟩ => ⟨.exE a z ha hK hz d e⟩

end Derivable

end LaxLogic.QLL
