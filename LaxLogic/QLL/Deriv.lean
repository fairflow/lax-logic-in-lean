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
inductive Derivable : Ctx → Pf → Form → Prop where
  /-- `I`.  Γ, z:M, Γ' ⊢ z : M — a variable entry, looked up by name. -/
  | var {Γ : Ctx} {x : String} {M : Form} :
      (Pf.fvar x, M) ∈ Γ →
      Derivable Γ (.fvar x) M
  /-- `true_I`. -/
  | topI {Γ : Ctx} :
      Derivable Γ .star .top
  /-- Ex falso.  **Not in Fig. 5**; the figure has `false` in the syntax with
  no elimination rule. -/
  | botE {Γ : Ctx} {p : Pf} {M : Form} :
      Derivable Γ p .bot →
      Derivable Γ (.exf M p) M
  /-- `∧I`. -/
  | andI {Γ : Ctx} {p q : Pf} {M N : Form} :
      Derivable Γ p M → Derivable Γ q N →
      Derivable Γ (.pair p q) (.and M N)
  /-- `∧E`, first projection. -/
  | andE₁ {Γ : Ctx} {r : Pf} {M N : Form} :
      Derivable Γ r (.and M N) →
      Derivable Γ (.fst r) M
  /-- `∧E`, second projection. -/
  | andE₂ {Γ : Ctx} {r : Pf} {M N : Form} :
      Derivable Γ r (.and M N) →
      Derivable Γ (.snd r) N
  /-- `∨I`, left. -/
  | orI₁ {Γ : Ctx} {p : Pf} {M N : Form} :
      Derivable Γ p M →
      Derivable Γ (.inl p) (.or M N)
  /-- `∨I`, right. -/
  | orI₂ {Γ : Ctx} {q : Pf} {M N : Form} :
      Derivable Γ q N →
      Derivable Γ (.inr q) (.or M N)
  /-- `∨E`.  Two branches, each binding its own proof variable. -/
  | orE {Γ : Ctx} {r p q : Pf} {M N K : Form} (y z : String) :
      FreshP y Γ p → FreshP z Γ q →
      Derivable Γ r (.or M N) →
      Derivable ((Pf.fvar y, M) :: Γ) (p.openPWith y) K →
      Derivable ((Pf.fvar z, N) :: Γ) (q.openPWith z) K →
      Derivable Γ (.caseOr r p q) K
  /-- `⊃I`.  Abstracts a *variable* entry; `λp.…` for non-variable `p` is not
  a term, which is why a substituted entry can never be discharged. -/
  | impI {Γ : Ctx} {p : Pf} {M N : Form} (z : String) :
      FreshP z Γ p →
      Derivable ((Pf.fvar z, M) :: Γ) (p.openPWith z) N →
      Derivable Γ (.lam p) (.imp M N)
  /-- `⊃E`. -/
  | impE {Γ : Ctx} {p q : Pf} {M N : Form} :
      Derivable Γ p (.imp M N) → Derivable Γ q M →
      Derivable Γ (.app p q) N
  /-- `◯I`, for either modality: the figure's side condition is only
  "if `Q = ∀` or `Q = ∃`". -/
  | circI {Γ : Ctx} {q : Q} {p : Pf} {M : Form} :
      Derivable Γ p M →
      Derivable Γ (.val q p) (.circ q M)
  /-- `◯E`, for either modality.  Both premises and the conclusion carry the
  *same* `Q`; the figure permits no mixing. -/
  | circE {Γ : Ctx} {q : Q} {p b : Pf} {M N : Form} (z : String) :
      FreshP z Γ b →
      Derivable Γ p (.circ q M) →
      Derivable ((Pf.fvar z, M) :: Γ) (b.openPWith z) (.circ q N) →
      Derivable Γ (.letQ q p b) (.circ q N)
  /-- `∀I`, written `⟨p | x⟩`.  Binds an *individual*, and so uses a different
  abstraction from `⊃I`'s `λ`. -/
  | allI {Γ : Ctx} {p : Pf} {M : Form} (a : String) :
      FreshI a Γ p M →
      Derivable Γ (p.openIWith a) (M.openWith a) →
      Derivable Γ (.gen p) (.forall_ M)
  /-- `∀E`, written `π_t(p)`. -/
  | allE {Γ : Ctx} {p : Pf} {M N : Form} (t : Tm) :
      Derivable Γ p (.forall_ M) →
      N = M.openAt 0 t →
      Derivable Γ (.inst t p) N
  /-- `∃I`, written `ι_t(p)`. -/
  | exI {Γ : Ctx} {p : Pf} {M : Form} (t : Tm) :
      Derivable Γ p (M.openAt 0 t) →
      Derivable Γ (.pack t p) (.exists_ M)
  /-- `∃E`.  Binds an individual *and* a proof variable in the one branch —
  the only rule that binds in both sorts at once. -/
  | exE {Γ : Ctx} {r p : Pf} {M K : Form} (a z : String) :
      FreshI a Γ p M → a ∉ K.fv → FreshP z Γ p →
      Derivable Γ r (.exists_ M) →
      Derivable ((Pf.fvar z, M.openWith a) :: Γ) ((p.openIWith a).openPWith z) K →
      Derivable Γ (.caseEx r p) K

@[inherit_doc] notation:40 Γ " ⊢qll " p " : " M => Derivable Γ p M

end LaxLogic.QLL
