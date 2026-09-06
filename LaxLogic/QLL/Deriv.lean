/-
# `LaxLogic.QLL.Deriv` — Fig. 5 as an inductive family

The natural deduction rules of

> M. Fairtlough, M. Mendler and X. Cheng, *Abstraction and refinement in higher
> order logic*, TPHOLs 2001, LNCS 2152, 201–216, Fig. 5,

one constructor per rule, transcribed from the page.  The figure is a *term
assignment* system, so this is a typing relation on `Pf` rather than an
intrinsically typed family: proof terms stay plain data that a checker can
validate and that the Fig. 6 interpretation can consume.

## No green slime

Every constructor's *conclusion* has variable or constructor indices only.
One would otherwise have a computed one — `allE` (`Form.openAt 0 t M`) — and it
is written instead with a fresh index variable and an equational premise.  Computation in a *premise* is harmless;
in a conclusion it is not invertible, so `cases` and dependent matching cannot
decompose it and every proof over the family has to transport across an
equation the unifier will not solve.  `#slime LaxLogic.QLL.Derivable` reports
17 clean constructors.

The family is `Prop`-valued, so nothing computes with a derivation, which
limits the damage — but the soundness proof is case analysis on derivations
and nothing else, so it is exactly where the damage would land.

## Fig. 5's `Subst` is deliberately absent

The figure lists `Subst` among the deduction rules:

    Γ, z:M, Γ' ⊢ q : N
    ─────────────────────────  (p :: |M|)
    Γ, p:M, Γ' ⊢ q{p/z} : N

It is not a rule of this family, for three reasons that agree.

*It is not admissible, and it establishes nothing.*  Its side condition is
`p :: |M|`, HOL typing, not `p : M`, refinement.  Replacing the entry turns
every use of `var` on `z` into an occurrence of `p` that would need
`Γ ⊢ p : M` — exactly what is not available.  So removing it removes no
derivable judgement.

*It is invisible in the proof term.*  It produces `q.substP x p`, which is just
some term, so no checker driven by the term could ever be complete for a family
containing it.  With it gone, `check` is complete for all of `Derivable` rather
than for a fragment, and no statement needs an `isSubstFree` precondition.

*Its content is semantic, and reappears there.*  What `Subst` records is

    Derivable (Γ ++ (x,M) :: Γ') q N → p ⊨ M → q{p/x} ⊨ N

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
def FreshI (a : String) (Γ : Ctx) (p : Pf) (M : Form) : Prop :=
  a ∉ Ctx.fvI Γ ∧ a ∉ p.fvI ∧ a ∉ M.fv

/--
`Derivable Γ p M` is the figure's `Γ ⊢ p : M`.

`Γ` is a list of the paper's refinement pairs.  Rule `var` fires only on a
*variable* entry and `impI` can abstract only a variable entry, so no rule here
can use a non-variable one: `Derivable` is insensitive to them, and they are
carried purely as the residual obligations the semantics will quantify over.
-/
inductive Derives : Pf → Ctx → Form → Type where
  /-- `I`.  Γ, z:M, Γ' ⊢ z : M — a variable entry, looked up by name. -/
  | var {Γ : Ctx} {x : String} {M : Form} :
      (Pf.fvar x, M) ∈ Γ →
      Derives (.fvar x) Γ M
  /-- `true_I`. -/
  | topI {Γ : Ctx} :
      Derives .star Γ .top
  /-- Ex falso.  **Not in Fig. 5**; the figure has `false` in the syntax with
  no elimination rule. -/
  | botE {Γ : Ctx} {p : Pf} {M : Form} :
      Derives p Γ .bot →
      Derives (.exf M p) Γ M
  /-- `∧I`. -/
  | andI {Γ : Ctx} {p q : Pf} {M N : Form} :
      Derives p Γ M → Derives q Γ N →
      Derives (.pair p q) Γ (.and M N)
  /-- `∧E`, first projection. -/
  | andE₁ {Γ : Ctx} {r : Pf} {M N : Form} :
      Derives r Γ (.and M N) →
      Derives (.fst r) Γ M
  /-- `∧E`, second projection. -/
  | andE₂ {Γ : Ctx} {r : Pf} {M N : Form} :
      Derives r Γ (.and M N) →
      Derives (.snd r) Γ N
  /-- `∨I`, left. -/
  | orI₁ {Γ : Ctx} {p : Pf} {M N : Form} :
      Derives p Γ M →
      Derives (.inl p) Γ (.or M N)
  /-- `∨I`, right. -/
  | orI₂ {Γ : Ctx} {q : Pf} {M N : Form} :
      Derives q Γ N →
      Derives (.inr q) Γ (.or M N)
  /-- `∨E`.  Two branches, each binding its own proof variable. -/
  | orE {Γ : Ctx} {r p q : Pf} {M N K : Form} (y z : String) :
      FreshP y Γ p → FreshP z Γ q →
      Derives r Γ (.or M N) →
      Derives (p.openPWith y) ((Pf.fvar y, M) :: Γ) K →
      Derives (q.openPWith z) ((Pf.fvar z, N) :: Γ) K →
      Derives (.caseOr r p q) Γ K
  /-- `⊃I`.  Abstracts a *variable* entry; `λp.…` for non-variable `p` is not
  a term, which is why a substituted entry could never be discharged. -/
  | impI {Γ : Ctx} {p : Pf} {M N : Form} (z : String) :
      FreshP z Γ p →
      Derives (p.openPWith z) ((Pf.fvar z, M) :: Γ) N →
      Derives (.lam p) Γ (.imp M N)
  /-- `⊃E`. -/
  | impE {Γ : Ctx} {p q : Pf} {M N : Form} :
      Derives p Γ (.imp M N) → Derives q Γ M →
      Derives (.app p q) Γ N
  /-- `◯I`, for either modality: the figure's side condition is only
  "if `Q = ∀` or `Q = ∃`". -/
  | circI {Γ : Ctx} {q : Q} {p : Pf} {M : Form} :
      Derives p Γ M →
      Derives (.val q p) Γ (.circ q M)
  /-- `◯E`, for either modality.  Both premises and the conclusion carry the
  *same* `Q`; the figure permits no mixing. -/
  | circE {Γ : Ctx} {q : Q} {p b : Pf} {M N : Form} (z : String) :
      FreshP z Γ b →
      Derives p Γ (.circ q M) →
      Derives (b.openPWith z) ((Pf.fvar z, M) :: Γ) (.circ q N) →
      Derives (.letQ q p b) Γ (.circ q N)
  /-- `∀I`, written `⟨p | x⟩`.  Binds an *individual*, and so uses a different
  abstraction from `⊃I`'s `λ`. -/
  | allI {Γ : Ctx} {p : Pf} {M : Form} (a : String) :
      FreshI a Γ p M →
      Derives (p.openIWith a) Γ (M.openWith a) →
      Derives (.gen p) Γ (.forall_ M)
  /-- `∀E`, written `π_t(p)`.  The equational premise keeps the conclusion's
  index a variable; see the note on green slime above. -/
  | allE {Γ : Ctx} {p : Pf} {M N : Form} (t : Tm) :
      Derives p Γ (.forall_ M) →
      N = M.openAt 0 t →
      Derives (.inst t p) Γ N
  /-- `∃I`, written `ι_t(p)`. -/
  | exI {Γ : Ctx} {p : Pf} {M : Form} (t : Tm) :
      Derives p Γ (M.openAt 0 t) →
      Derives (.pack t p) Γ (.exists_ M)
  /-- `∃E`.  Binds an individual *and* a proof variable in the one branch —
  the only rule that binds in both sorts at once. -/
  | exE {Γ : Ctx} {r p : Pf} {M K : Form} (a z : String) :
      FreshI a Γ p M → a ∉ K.fv → FreshP z Γ p →
      Derives r Γ (.exists_ M) →
      Derives ((p.openIWith a).openPWith z) ((Pf.fvar z, M.openWith a) :: Γ) K →
      Derives (.caseEx r p) Γ K

@[inherit_doc] notation:40 Γ " ⊢qll " p " : " M => Derives p Γ M

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
abbrev Derivable (p : Pf) (Γ : Ctx) (M : Form) : Prop := Nonempty (Derives p Γ M)

namespace Derivable

theorem var {Γ x M} (h : (Pf.fvar x, M) ∈ Γ) : Derivable (.fvar x) Γ M := ⟨.var h⟩

theorem topI {Γ} : Derivable .star Γ .top := ⟨.topI⟩

theorem botE {Γ p M} : Derivable p Γ .bot → Derivable (.exf M p) Γ M
  | ⟨d⟩ => ⟨.botE d⟩

theorem andI {Γ p q M N} : Derivable p Γ M → Derivable q Γ N →
    Derivable (.pair p q) Γ (.and M N)
  | ⟨d⟩, ⟨e⟩ => ⟨.andI d e⟩

theorem andE₁ {Γ r M N} : Derivable r Γ (.and M N) → Derivable (.fst r) Γ M
  | ⟨d⟩ => ⟨.andE₁ d⟩

theorem andE₂ {Γ r M N} : Derivable r Γ (.and M N) → Derivable (.snd r) Γ N
  | ⟨d⟩ => ⟨.andE₂ d⟩

theorem orI₁ {Γ p M N} : Derivable p Γ M → Derivable (.inl p) Γ (.or M N)
  | ⟨d⟩ => ⟨.orI₁ d⟩

theorem orI₂ {Γ q M N} : Derivable q Γ N → Derivable (.inr q) Γ (.or M N)
  | ⟨d⟩ => ⟨.orI₂ d⟩

theorem orE {Γ r p q M N K} (y z : String) (hy : FreshP y Γ p) (hz : FreshP z Γ q) :
    Derivable r Γ (.or M N) →
    Derivable (p.openPWith y) ((Pf.fvar y, M) :: Γ) K →
    Derivable (q.openPWith z) ((Pf.fvar z, N) :: Γ) K →
    Derivable (.caseOr r p q) Γ K
  | ⟨d⟩, ⟨e⟩, ⟨f⟩ => ⟨.orE y z hy hz d e f⟩

theorem impI {Γ p M N} (z : String) (hz : FreshP z Γ p) :
    Derivable (p.openPWith z) ((Pf.fvar z, M) :: Γ) N →
    Derivable (.lam p) Γ (.imp M N)
  | ⟨d⟩ => ⟨.impI z hz d⟩

theorem impE {Γ p q M N} : Derivable p Γ (.imp M N) → Derivable q Γ M →
    Derivable (.app p q) Γ N
  | ⟨d⟩, ⟨e⟩ => ⟨.impE d e⟩

theorem circI {Γ q p M} : Derivable p Γ M → Derivable (.val q p) Γ (.circ q M)
  | ⟨d⟩ => ⟨.circI d⟩

theorem circE {Γ q p b M N} (z : String) (hz : FreshP z Γ b) :
    Derivable p Γ (.circ q M) →
    Derivable (b.openPWith z) ((Pf.fvar z, M) :: Γ) (.circ q N) →
    Derivable (.letQ q p b) Γ (.circ q N)
  | ⟨d⟩, ⟨e⟩ => ⟨.circE z hz d e⟩

theorem allI {Γ p M} (a : String) (ha : FreshI a Γ p M) :
    Derivable (p.openIWith a) Γ (M.openWith a) → Derivable (.gen p) Γ (.forall_ M)
  | ⟨d⟩ => ⟨.allI a ha d⟩

theorem allE {Γ p M N} (t : Tm) (h : N = M.openAt 0 t) :
    Derivable p Γ (.forall_ M) → Derivable (.inst t p) Γ N
  | ⟨d⟩ => ⟨.allE t d h⟩

theorem exI {Γ p M} (t : Tm) : Derivable p Γ (M.openAt 0 t) →
    Derivable (.pack t p) Γ (.exists_ M)
  | ⟨d⟩ => ⟨.exI t d⟩

theorem exE {Γ r p M K} (a z : String) (ha : FreshI a Γ p M) (hK : a ∉ K.fv)
    (hz : FreshP z Γ p) :
    Derivable r Γ (.exists_ M) →
    Derivable ((p.openIWith a).openPWith z) ((Pf.fvar z, M.openWith a) :: Γ) K →
    Derivable (.caseEx r p) Γ K
  | ⟨d⟩, ⟨e⟩ => ⟨.exE a z ha hK hz d e⟩

end Derivable

end LaxLogic.QLL
