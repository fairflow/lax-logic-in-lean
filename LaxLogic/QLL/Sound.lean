/-
# `LaxLogic.QLL.Sound` — Fig. 5 is sound for the refinement relation of Fig. 4

## What is proved, with every binder written out

For every model `𝔐`, every derivation `d` of `Γ ⊢ p : A` in Fig. 5 whose
embedded individual terms are closed, every constraint environment `η` for `Γ`
and every valuation `ρ`:

    (d : Derives p Γ A) → Pf.lcI 0 p →
      CtxRefines 𝔐 ρ Γ η → Refines 𝔐 [] ρ A (denote 𝔐 d η ρ)

`d` is the subject of the theorem, not a free variable: it is bound first, and
`p`, `Γ` and `A` are its indices.  It appears only on the right because that is
where the object it produces lives — `denote 𝔐 d η ρ` is the constraint Fig. 6
*extracts from the derivation*, so the statement cannot be made without naming
the derivation.  The left-hand side constrains only the context.

## What this is soundness *of*, and *against*

Three things must be named or the word "soundness" says nothing.

| | |
| :-- | :-- |
| the system | Fig. 5, `Derives` — the deep-embedded proof system |
| the interpretation | Fig. 6, `denote` — the constraint extracted from a derivation |
| the semantics | Fig. 4, `Refines` — the refinement relation, "this constraint refines that formula" |

So: **Fig. 5 is sound for the refinement relation, under Fig. 6's
extraction**.  In the report's own words (p. 207, of Fig. 5) the rules "are a
variant of QLL [FW97] and derivable in the base logic from the equations of
Fig. 4" — asserted there, discharged here.  The report can assert it because
`p : A` is an abbreviation in HOL and each rule is then a HOL-derivable
implication; in a deep embedding the same content is an induction over
derivations.

Standard names for a theorem of this shape, "if `Γ ⊢ e : τ` then `⟦e⟧ ∈ ⟦τ⟧`":

* **soundness of the refinement system** — the usual phrase in refinement-type
  work, where the semantics is a refinement of an underlying interpretation;
* the **Fundamental Theorem** of a unary logical relation — `Refines` is a logical
  predicate defined by recursion on the formula, `CtxRefines` is its extension to
  environments, and the theorem is "every syntactically well-typed term is
  semantically well-typed";
* **soundness of a realizability interpretation** — the classical name, since
  `Val A` is the type of potential realisers, `Refines A v` reads "`v` realises
  `A`", and `denote` extracts a realiser from a proof.

## What it is NOT

* It is **not** soundness of QLL against a model-theoretic semantics of the lax
  modalities, `Γ ⊢ φ ⟹ Γ ⊨ φ`.  There is no Kripke semantics here at all;
  `Refines` is a shallow embedding into Lean's own logic, indexed by a witness, so
  it is a realizability relation and not a satisfaction relation.  That
  soundness is a different statement about a different semantics, and is OPEN.
* It is **not** the report's Theorem 1, conservativity of `p : A` over HOL.
  Ours is relative to Lean in the same way theirs is relative to HOL.
* Its converse — every constraint that refines `A` comes from a derivation —
  is completeness of the refinement system, and is OPEN.

## The one hypothesis, and why it is not avoidable

`Pf.lcI 0 p`: the individual terms written into the proof term — the `t` of
`π_t(p)` and `ι_t(p)` — carry no loose de Bruijn index.

`Derives` does not require this, and it should not: Fig. 5 has no such side
condition, and a loose index is a malformed *term*, not a bad inference.  But
`A{t/x}` is meaningless when `t` has a loose index (it captures), so no
semantics can validate `∀E` there.  The hypothesis says exactly that the terms
are terms.  It costs the two propagation lemmas below and nothing else.

Notably **no** local closedness of formulas or contexts is needed, and no
regularity lemma.  That is not luck: `Refines_openAt` is stated for the
environments soundness actually uses — the opened variable is the *last* one —
and there an index past the end is out of range on both sides and evaluates to
`d₀` either way.  Stated for a general environment the lemma would be false
without `Form.lcAt (k+1) A`, and a regularity lemma to supply it would fail
anyway: `∨I` guesses the other disjunct, so a derivable formula need not be
locally closed. It is never inspected, which is why nothing here needs it.

## Casts

`Val_openAt` is a propositional equality, so every clause of the induction that
crosses a binder carries a `cast`.  The six lemmas in the first section push a
`cast` through a pair, a sum, a function and a pair with fixed first component;
each is `subst`, then `rfl` — definitional proof irrelevance does the rest.
-/
import LaxLogic.QLL.Denote
import LaxLogic.QLL.Lc

namespace LaxLogic.QLL

/-! ## Pushing a cast through a type former -/

theorem cast_fst {X Y X' Y' : Type} (hX : X = X') (hY : Y = Y')
    (h : (X × Y) = (X' × Y')) (v : X × Y) : (cast h v).1 = cast hX v.1 := by
  subst hX; subst hY; rfl

theorem cast_snd {X Y X' Y' : Type} (hX : X = X') (hY : Y = Y')
    (h : (X × Y) = (X' × Y')) (v : X × Y) : (cast h v).2 = cast hY v.2 := by
  subst hX; subst hY; rfl

theorem cast_inl {X Y X' Y' : Type} (hX : X = X') (hY : Y = Y')
    (h : (X ⊕ Y) = (X' ⊕ Y')) (a : X) : cast h (.inl a) = Sum.inl (cast hX a) := by
  subst hX; subst hY; rfl

theorem cast_inr {X Y X' Y' : Type} (hX : X = X') (hY : Y = Y')
    (h : (X ⊕ Y) = (X' ⊕ Y')) (b : Y) : cast h (.inr b) = Sum.inr (cast hY b) := by
  subst hX; subst hY; rfl

theorem cast_app {X Y X' Y' : Type} (hX : X = X') (hY : Y = Y')
    (h : (X → Y) = (X' → Y')) (f : X → Y) (x : X') :
    (cast h f) x = cast hY (f (cast hX.symm x)) := by
  subst hX; subst hY; rfl

theorem cast_pred {X X' : Type} (hX : X = X')
    (h : (X → Prop) = (X' → Prop)) (φ : X → Prop) (x : X') :
    (cast h φ) x = φ (cast hX.symm x) := by
  subst hX; rfl

theorem cast_dfun {D X X' : Type} (hX : X = X')
    (h : (D → X) = (D → X')) (f : D → X) (d : D) :
    (cast h f) d = cast hX (f d) := by
  subst hX; rfl

theorem cast_dpair_fst {D X X' : Type} (hX : X = X')
    (h : (D × X) = (D × X')) (v : D × X) : (cast h v).1 = v.1 := by
  subst hX; rfl

theorem cast_dpair_snd {D X X' : Type} (hX : X = X')
    (h : (D × X) = (D × X')) (v : D × X) : (cast h v).2 = cast hX v.2 := by
  subst hX; rfl

theorem cast_left {X X' : Type} (h : X = X') (x : X) : cast h.symm (cast h x) = x := by
  subst h; rfl

theorem cast_right {X X' : Type} (h : X = X') (x : X') : cast h (cast h.symm x) = x := by
  subst h; rfl

variable (𝔐 : Model)

/-! ## X closed term does not read the environment

`Tm.lcAt 0 t` says no index occurs at all — there are no binders inside a term
— so `evalTm` never reaches `env`. -/

mutual
theorem evalTm_lc (ρ : String → 𝔐.D) (env env' : List 𝔐.D) :
    ∀ (t : Tm), Tm.lcAt 0 t → evalTm 𝔐 env ρ t = evalTm 𝔐 env' ρ t
  | .bvar i,  h => absurd h (Nat.not_lt_zero i)
  | .fvar _,  _ => rfl
  | .fn _ ts, h => by
      simp [evalTm, evalTms_lc ρ env env' ts h]
theorem evalTms_lc (ρ : String → 𝔐.D) (env env' : List 𝔐.D) :
    ∀ (ts : List Tm), Tm.lcAtList 0 ts → evalTms 𝔐 env ρ ts = evalTms 𝔐 env' ρ ts
  | [],      _ => rfl
  | t :: ts, h => by
      simp [evalTms, evalTm_lc ρ env env' t h.1, evalTms_lc ρ env env' ts h.2]
end

/-! ## The environment, indexed

Two facts about looking up in `env ++ [e]`.  The second is the whole reason
this development needs no local closedness of formulas: past the end of `env`,
both environments are out of range and both answer `d₀`. -/

theorem getElem?_append_last {α : Type} (env : List α) (e : α) :
    (env ++ [e])[env.length]? = some e := by
  induction env with
  | nil => rfl
  | cons _ env ih => simp

theorem getD_append_last {α : Type} (d e : α) :
    ∀ (env : List α) (i : Nat), i ≠ env.length →
      (env ++ [e])[i]?.getD d = env[i]?.getD d
  | [],       0,     h => absurd rfl h
  | [],       _ + 1, _ => rfl
  | _ :: _,   0,     _ => rfl
  | a :: env, i + 1, h => by
      simpa using getD_append_last d e env i (fun hi => h (by simp [hi]))

/-! ## Opening a term

Substituting `u` for the outermost bound individual is the same as evaluating
in an environment extended with `u`'s value — provided `u` is closed, which is
what stops it reading the very environment it is being placed in. -/

mutual
theorem evalTm_openAt (ρ : String → 𝔐.D) (u : Tm) (hu : Tm.lcAt 0 u) (env : List 𝔐.D) :
    ∀ (t : Tm),
      evalTm 𝔐 env ρ (Tm.openAt env.length u t)
        = evalTm 𝔐 (env ++ [evalTm 𝔐 [] ρ u]) ρ t
  | .bvar i => by
      by_cases h : i = env.length
      · subst h
        simp only [Tm.openAt, evalTm, getElem?_append_last]
        exact evalTm_lc 𝔐 ρ env [] u hu
      · simp only [Tm.openAt, if_neg h, evalTm]
        exact (getD_append_last 𝔐.d₀ _ env i h).symm
  | .fvar _ => rfl
  | .fn _ ts => by simp [Tm.openAt, evalTm, evalTms_openAt ρ u hu env ts]
theorem evalTms_openAt (ρ : String → 𝔐.D) (u : Tm) (hu : Tm.lcAt 0 u) (env : List 𝔐.D) :
    ∀ (ts : List Tm),
      evalTms 𝔐 env ρ (Tm.openAtList env.length u ts)
        = evalTms 𝔐 (env ++ [evalTm 𝔐 [] ρ u]) ρ ts
  | []      => rfl
  | t :: ts => by
      simp [Tm.openAtList, evalTms, evalTm_openAt ρ u hu env t,
            evalTms_openAt ρ u hu env ts]
end

/-! ## The same six, specialised to `Val_openAt`

`rw` matches syntactically, and `cast` carries its two types as implicit
arguments, so the generic lemmas above never match a goal in which the cast is
written at `Val 𝔐 (A.and B)` rather than at a product.  These say the same
thing with the arguments spelled the way the induction produces them; each is
the generic lemma accepted up to definitional unfolding of `Val`. -/

section Push
variable (u : Tm) (k : Nat)

theorem cast_and_fst (A B : Form) (v : Val 𝔐 (Form.and A B)) :
    (cast (Val_openAt 𝔐 u (Form.and A B) k).symm v).1
      = cast (Val_openAt 𝔐 u A k).symm v.1 :=
  cast_fst _ (Val_openAt 𝔐 u B k).symm _ v

theorem cast_and_snd (A B : Form) (v : Val 𝔐 (Form.and A B)) :
    (cast (Val_openAt 𝔐 u (Form.and A B) k).symm v).2
      = cast (Val_openAt 𝔐 u B k).symm v.2 :=
  cast_snd (Val_openAt 𝔐 u A k).symm _ _ v

theorem cast_or_inl (A B : Form) (a : Val 𝔐 A) :
    cast (Val_openAt 𝔐 u (Form.or A B) k).symm (Sum.inl a)
      = Sum.inl (cast (Val_openAt 𝔐 u A k).symm a) :=
  cast_inl _ (Val_openAt 𝔐 u B k).symm _ a

theorem cast_or_inr (A B : Form) (b : Val 𝔐 B) :
    cast (Val_openAt 𝔐 u (Form.or A B) k).symm (Sum.inr b)
      = Sum.inr (cast (Val_openAt 𝔐 u B k).symm b) :=
  cast_inr (Val_openAt 𝔐 u A k).symm _ _ b

theorem cast_imp_app (A B : Form) (v : Val 𝔐 (Form.imp A B))
    (z : Val 𝔐 (A.openAt k u)) :
    (cast (Val_openAt 𝔐 u (Form.imp A B) k).symm v) z
      = cast (Val_openAt 𝔐 u B k).symm (v (cast (Val_openAt 𝔐 u A k) z)) :=
  cast_app (Val_openAt 𝔐 u A k).symm (Val_openAt 𝔐 u B k).symm _ v z

theorem cast_circ_app (q : Q) (A : Form) (v : Val 𝔐 (Form.circ q A))
    (z : Val 𝔐 (A.openAt k u)) :
    (cast (Val_openAt 𝔐 u (Form.circ q A) k).symm v) z
      = v (cast (Val_openAt 𝔐 u A k) z) :=
  cast_pred (Val_openAt 𝔐 u A k).symm _ v z

theorem cast_all_app (A : Form) (v : Val 𝔐 (Form.forall_ A)) (d : 𝔐.D) :
    (cast (Val_openAt 𝔐 u (Form.forall_ A) k).symm v) d
      = cast (Val_openAt 𝔐 u A (k + 1)).symm (v d) :=
  cast_dfun (Val_openAt 𝔐 u A (k + 1)).symm _ v d

theorem cast_ex_fst (A : Form) (v : Val 𝔐 (Form.exists_ A)) :
    (cast (Val_openAt 𝔐 u (Form.exists_ A) k).symm v).1 = v.1 :=
  cast_dpair_fst (Val_openAt 𝔐 u A (k + 1)).symm _ v

theorem cast_ex_snd (A : Form) (v : Val 𝔐 (Form.exists_ A)) :
    (cast (Val_openAt 𝔐 u (Form.exists_ A) k).symm v).2
      = cast (Val_openAt 𝔐 u A (k + 1)).symm v.2 :=
  cast_dpair_snd (Val_openAt 𝔐 u A (k + 1)).symm _ v

end Push

/-! ## Opening a formula

The lemma the whole proof turns on.  Read from the right: to satisfy `A` in an
environment whose *last* entry is `⟦u⟧` is to satisfy `A{u/x}` without it.

Stated at the environments soundness uses — the opened variable last — so no
`Form.lcAt` hypothesis is needed; see the header. -/

theorem Refines_openAt (ρ : String → 𝔐.D) (u : Tm) (hu : Tm.lcAt 0 u) :
    ∀ (A : Form) (env : List 𝔐.D) (v : Val 𝔐 A),
      Refines 𝔐 env ρ (A.openAt env.length u) (cast (Val_openAt 𝔐 u A env.length).symm v)
      ↔ Refines 𝔐 (env ++ [evalTm 𝔐 [] ρ u]) ρ A v := by
  intro A
  induction A with
  | top => intro _ _; exact Iff.rfl
  | bot => intro _ _; exact Iff.rfl
  | pred P ts =>
      intro env v
      show 𝔐.atom P (evalTms 𝔐 env ρ (Tm.openAtList env.length u ts)) _ ↔ _
      rw [evalTms_openAt 𝔐 ρ u hu env ts]
      exact Iff.rfl
  | and A B ihM ihN =>
      intro env v
      show Refines 𝔐 env ρ (A.openAt env.length u)
             (cast (Val_openAt 𝔐 u (Form.and A B) env.length).symm v).1
         ∧ Refines 𝔐 env ρ (B.openAt env.length u)
             (cast (Val_openAt 𝔐 u (Form.and A B) env.length).symm v).2 ↔ _
      rw [cast_and_fst, cast_and_snd]
      exact and_congr (ihM env v.1) (ihN env v.2)
  | or A B ihM ihN =>
      intro env v
      match v with
      | Sum.inl a =>
          show Refines 𝔐 env ρ ((Form.or A B).openAt env.length u)
                 (cast (Val_openAt 𝔐 u (Form.or A B) env.length).symm (Sum.inl a)) ↔ _
          rw [cast_or_inl]
          exact ihM env a
      | Sum.inr b =>
          show Refines 𝔐 env ρ ((Form.or A B).openAt env.length u)
                 (cast (Val_openAt 𝔐 u (Form.or A B) env.length).symm (Sum.inr b)) ↔ _
          rw [cast_or_inr]
          exact ihN env b
  | imp A B ihM ihN =>
      intro env v
      show (∀ z, Refines 𝔐 env ρ (A.openAt env.length u) z
              → Refines 𝔐 env ρ (B.openAt env.length u)
                  ((cast (Val_openAt 𝔐 u (Form.imp A B) env.length).symm v) z)) ↔ _
      simp only [cast_imp_app]
      have eM := Val_openAt 𝔐 u A env.length
      constructor
      · intro H w hw
        refine (ihN env (v w)).mp ?_
        have hz : Refines 𝔐 env ρ (A.openAt env.length u) (cast eM.symm w) :=
          (ihM env w).mpr hw
        have := H (cast eM.symm w) hz
        rwa [cast_right eM w] at this
      · intro H z hz
        have hw : Refines 𝔐 (env ++ [evalTm 𝔐 [] ρ u]) ρ A (cast eM z) := by
          refine (ihM env (cast eM z)).mp ?_
          rwa [cast_left eM z]
        exact (ihN env (v (cast eM z))).mpr (H (cast eM z) hw)
  | circ q A ih =>
      intro env v
      cases q with
      | all =>
          show (∀ z, (cast (Val_openAt 𝔐 u (Form.circ Q.all A) env.length).symm v) z
                  → Refines 𝔐 env ρ (A.openAt env.length u) z) ↔ _
          simp only [cast_circ_app]
          have eM := Val_openAt 𝔐 u A env.length
          constructor
          · intro H w hw
            refine (ih env w).mp (H (cast eM.symm w) ?_)
            rwa [cast_right eM w]
          · intro H z hz
            have := (ih env (cast eM z)).mpr (H (cast eM z) hz)
            rwa [cast_left eM z] at this
      | ex =>
          show (∃ z, (cast (Val_openAt 𝔐 u (Form.circ Q.ex A) env.length).symm v) z
                  ∧ Refines 𝔐 env ρ (A.openAt env.length u) z) ↔ _
          simp only [cast_circ_app]
          have eM := Val_openAt 𝔐 u A env.length
          constructor
          · rintro ⟨z, hz, hs⟩
            refine ⟨cast eM z, hz, (ih env (cast eM z)).mp ?_⟩
            rwa [cast_left eM z]
          · rintro ⟨w, hw, hs⟩
            refine ⟨cast eM.symm w, ?_, ?_⟩
            · rwa [cast_right eM w]
            · exact (ih env w).mpr hs
  | forall_ A ih =>
      intro env v
      show (∀ d, Refines 𝔐 (d :: env) ρ (A.openAt (env.length + 1) u)
              ((cast (Val_openAt 𝔐 u (Form.forall_ A) env.length).symm v) d)) ↔ _
      simp only [cast_all_app]
      exact forall_congr' fun d => ih (d :: env) (v d)
  | exists_ A ih =>
      intro env v
      show Refines 𝔐 ((cast (Val_openAt 𝔐 u (Form.exists_ A) env.length).symm v).1 :: env) ρ
             (A.openAt (env.length + 1) u)
             ((cast (Val_openAt 𝔐 u (Form.exists_ A) env.length).symm v).2) ↔ _
      rw [cast_ex_fst, cast_ex_snd]
      exact ih (v.1 :: env) v.2

/-! ## Changing the valuation off a formula's free individuals

`∀I` and `∃E` interpret their premise under `ρ` updated at the eigenvariable.
Everything else in sight must not notice, and the freshness conditions the
rules already carry are exactly what says so. -/

mutual
theorem evalTm_upd (ρ : String → 𝔐.D) (a : String) (e : 𝔐.D) (env : List 𝔐.D) :
    ∀ (t : Tm), a ∉ Tm.fv t → evalTm 𝔐 env (upd 𝔐 ρ a e) t = evalTm 𝔐 env ρ t
  | .bvar _,  _ => rfl
  | .fvar x,  h => by
      have : x ≠ a := fun hx => h (by simp [Tm.fv, hx])
      simp [evalTm, upd, this]
  | .fn _ ts, h => by simp [evalTm, evalTms_upd ρ a e env ts h]
theorem evalTms_upd (ρ : String → 𝔐.D) (a : String) (e : 𝔐.D) (env : List 𝔐.D) :
    ∀ (ts : List Tm), a ∉ Tm.fvList ts →
      evalTms 𝔐 env (upd 𝔐 ρ a e) ts = evalTms 𝔐 env ρ ts
  | [],      _ => rfl
  | t :: ts, h => by
      simp only [Tm.fvList, List.mem_append, not_or] at h
      simp [evalTms, evalTm_upd ρ a e env t h.1, evalTms_upd ρ a e env ts h.2]
end

theorem Refines_upd (ρ : String → 𝔐.D) (a : String) (e : 𝔐.D) :
    ∀ (A : Form) (env : List 𝔐.D) (v : Val 𝔐 A), a ∉ A.fv →
      (Refines 𝔐 env (upd 𝔐 ρ a e) A v ↔ Refines 𝔐 env ρ A v) := by
  intro A
  induction A with
  | top => intro _ _ _; exact Iff.rfl
  | bot => intro _ _ _; exact Iff.rfl
  | pred P ts =>
      intro env v h
      show 𝔐.atom P (evalTms 𝔐 env (upd 𝔐 ρ a e) ts) v ↔ _
      rw [evalTms_upd 𝔐 ρ a e env ts h]
      exact Iff.rfl
  | and A B ihM ihN =>
      intro env v h
      simp only [Form.fv, List.mem_append, not_or] at h
      exact and_congr (ihM env v.1 h.1) (ihN env v.2 h.2)
  | or A B ihM ihN =>
      intro env v h
      simp only [Form.fv, List.mem_append, not_or] at h
      match v with
      | Sum.inl x => exact ihM env x h.1
      | Sum.inr y => exact ihN env y h.2
  | imp A B ihM ihN =>
      intro env v h
      simp only [Form.fv, List.mem_append, not_or] at h
      exact forall_congr' fun z => imp_congr (ihM env z h.1) (ihN env (v z) h.2)
  | circ q A ih =>
      intro env v h
      cases q with
      | all => exact forall_congr' fun z => imp_congr Iff.rfl (ih env z h)
      | ex  => exact exists_congr fun z => and_congr Iff.rfl (ih env z h)
  | forall_ A ih => intro env v h; exact forall_congr' fun d => ih (d :: env) (v d) h
  | exists_ A ih => intro env v h; exact ih (v.1 :: env) v.2 h

end LaxLogic.QLL

namespace LaxLogic.QLL

/-! ## Local closedness survives both openings

The soundness hypothesis is about the proof term the derivation *concludes*
with; every rule hands its premises an opened term, so the hypothesis has to
travel.  Opening a proof variable leaves the individual indices alone; opening
an individual lowers the bound by one, which is what these say. -/

mutual
theorem Tm.lcAt_mono : ∀ {k k' : Nat}, k ≤ k' → ∀ (t : Tm), Tm.lcAt k t → Tm.lcAt k' t
  | _, _, hk, .bvar i, h => by
      have : i < _ := h
      show i < _
      omega
  | _, _, _,  .fvar _, _ => trivial
  | _, _, hk, .fn _ ts, h => Tm.lcAtList_mono hk ts h
theorem Tm.lcAtList_mono : ∀ {k k' : Nat}, k ≤ k' →
    ∀ (ts : List Tm), Tm.lcAtList k ts → Tm.lcAtList k' ts
  | _, _, _,  [],      _ => trivial
  | _, _, hk, _ :: ts, h => ⟨Tm.lcAt_mono hk _ h.1, Tm.lcAtList_mono hk ts h.2⟩
end

mutual
theorem Tm.lcAt_openAt : ∀ (k : Nat) (u : Tm), Tm.lcAt k u →
    ∀ (t : Tm), Tm.lcAt (k + 1) t → Tm.lcAt k (Tm.openAt k u t)
  | k, u, hu, .bvar i, h => by
      by_cases hi : i = k
      · subst hi; simpa [Tm.openAt] using hu
      · have h' : i < k + 1 := h
        simp only [Tm.openAt, if_neg hi]
        show i < k
        omega
  | _, _, _,  .fvar _, _ => trivial
  | k, u, hu, .fn _ ts, h => Tm.lcAtList_openAtList k u hu ts h
theorem Tm.lcAtList_openAtList : ∀ (k : Nat) (u : Tm), Tm.lcAt k u →
    ∀ (ts : List Tm), Tm.lcAtList (k + 1) ts → Tm.lcAtList k (Tm.openAtList k u ts)
  | _, _, _,  [],      _ => trivial
  | k, u, hu, _ :: ts, h =>
      ⟨Tm.lcAt_openAt k u hu _ h.1, Tm.lcAtList_openAtList k u hu ts h.2⟩
end

theorem Form.lcAt_openAt : ∀ (A : Form) (k : Nat) (u : Tm), Tm.lcAt k u →
    Form.lcAt (k + 1) A → Form.lcAt k (Form.openAt k u A) := by
  intro A
  induction A with
  | top | bot => intro _ _ _ _; trivial
  | pred _ ts => intro k u hu h; exact Tm.lcAtList_openAtList k u hu ts h
  | and A B ihM ihN | or A B ihM ihN | imp A B ihM ihN =>
      intro k u hu h; exact ⟨ihM k u hu h.1, ihN k u hu h.2⟩
  | circ _ A ih => intro k u hu h; exact ih k u hu h
  | forall_ A ih | exists_ A ih =>
      intro k u hu h; exact ih (k + 1) u (Tm.lcAt_mono (Nat.le_succ k) u hu) h

theorem Pf.lcI_openP (z : String) : ∀ (p : Pf) (j k : Nat),
    Pf.lcI k p → Pf.lcI k (Pf.openP j (.fvar z) p) := by
  intro p
  induction p with
  | bvar i => intro j _ _; by_cases h : i = j <;> simp [Pf.openP, h, Pf.lcI]
  | fvar _ | star => intro _ _ _; trivial
  | pair _ _ ih₁ ih₂ | app _ _ ih₁ ih₂ | letQ _ _ _ ih₁ ih₂ =>
      intro j k h; exact ⟨ih₁ _ k h.1, ih₂ _ k h.2⟩
  | fst _ ih | snd _ ih | inl _ ih | inr _ ih | lam _ ih | val _ _ ih =>
      intro j k h; exact ih _ k h
  | gen _ ih => intro j k h; exact ih j (k + 1) h
  | caseOr _ _ _ ih₁ ih₂ ih₃ =>
      intro j k h; exact ⟨ih₁ _ k h.1, ih₂ _ k h.2.1, ih₃ _ k h.2.2⟩
  | inst _ _ ih | pack _ _ ih => intro j k h; exact ⟨h.1, ih _ k h.2⟩
  | exf _ _ ih => intro j k h; exact ⟨h.1, ih _ k h.2⟩
  | caseEx _ _ ih₁ ih₂ => intro j k h; exact ⟨ih₁ _ k h.1, ih₂ _ (k + 1) h.2⟩

theorem Pf.lcI_openI : ∀ (p : Pf) (k : Nat) (u : Tm), Tm.lcAt k u →
    Pf.lcI (k + 1) p → Pf.lcI k (Pf.openI k u p) := by
  intro p
  induction p with
  | bvar _ | fvar _ | star => intro _ _ _ _; trivial
  | pair _ _ ih₁ ih₂ | app _ _ ih₁ ih₂ | letQ _ _ _ ih₁ ih₂ =>
      intro k u hu h; exact ⟨ih₁ k u hu h.1, ih₂ k u hu h.2⟩
  | fst _ ih | snd _ ih | inl _ ih | inr _ ih | lam _ ih | val _ _ ih =>
      intro k u hu h; exact ih k u hu h
  | caseOr _ _ _ ih₁ ih₂ ih₃ =>
      intro k u hu h; exact ⟨ih₁ k u hu h.1, ih₂ k u hu h.2.1, ih₃ k u hu h.2.2⟩
  | gen _ ih =>
      intro k u hu h; exact ih (k + 1) u (Tm.lcAt_mono (Nat.le_succ k) u hu) h
  | inst t _ ih | pack t _ ih =>
      intro k u hu h; exact ⟨Tm.lcAt_openAt k u hu t h.1, ih k u hu h.2⟩
  | exf A _ ih =>
      intro k u hu h; exact ⟨Form.lcAt_openAt A k u hu h.1, ih k u hu h.2⟩
  | caseEx _ _ ih₁ ih₂ =>
      intro k u hu h
      exact ⟨ih₁ k u hu h.1, ih₂ (k + 1) u (Tm.lcAt_mono (Nat.le_succ k) u hu) h.2⟩

end LaxLogic.QLL

namespace LaxLogic.QLL

variable (𝔐 : Model)

/-! ## An environment that satisfies its context -/

/-- Every entry's value refines that entry's formula. -/
inductive CtxRefines (ρ : String → 𝔐.D) : (Γ : Ctx) → PEnv 𝔐 Γ → Prop where
  | nil : CtxRefines ρ [] .nil
  | cons {e : Pf × Form} {Γ : Ctx} {v : Val 𝔐 e.2} {η : PEnv 𝔐 Γ} :
      Refines 𝔐 [] ρ e.2 v → CtxRefines ρ Γ η → CtxRefines ρ (e :: Γ) (.cons v η)

theorem CtxRefines_lookup (ρ : String → 𝔐.D) : ∀ {Γ : Ctx} {η : PEnv 𝔐 Γ}, CtxRefines 𝔐 ρ Γ η →
    ∀ (e : Pf × Form) (h : e ∈ Γ), Refines 𝔐 [] ρ e.2 (PEnv.lookup 𝔐 η e h) := by
  intro Γ η hη
  induction hη with
  | nil => intro e h; exact absurd h (fun hh => nomatch hh)
  | @cons a Γ v η hv _ ih =>
      intro e h
      by_cases he : e = a
      · subst he; simpa [PEnv.lookup] using hv
      · simpa [PEnv.lookup, he] using ih e ((List.mem_cons.mp h).resolve_left he)

theorem CtxRefines_upd (ρ : String → 𝔐.D) (a : String) (e : 𝔐.D) :
    ∀ {Γ : Ctx} {η : PEnv 𝔐 Γ}, a ∉ Ctx.fvI Γ → CtxRefines 𝔐 ρ Γ η →
      CtxRefines 𝔐 (upd 𝔐 ρ a e) Γ η := by
  intro Γ η ha hη
  induction hη with
  | nil => exact .nil
  | @cons b Γ v η hv _ ih =>
      have hb : a ∉ (b.1).fvI ++ (b.2).fv ++ Ctx.fvI Γ := by
        cases b; exact ha
      simp only [List.mem_append, not_or] at hb
      exact .cons ((Refines_upd 𝔐 ρ a e b.2 [] v hb.1.2).mpr hv) (ih hb.2)

/-! ## Soundness

The constraint a derivation produces refines the formula it concludes, given
that the assumptions' constraints refine theirs. -/

theorem soundness : ∀ {Γ : Ctx} {p : Pf} {A : Form} (d : Derives p Γ A),
    Pf.lcI 0 p → ∀ (η : PEnv 𝔐 Γ) (ρ : String → 𝔐.D), CtxRefines 𝔐 ρ Γ η →
      Refines 𝔐 [] ρ A (denote 𝔐 d η ρ) := by
  intro Γ p A d
  induction d with
  | var h => intro _ η ρ hη; exact CtxRefines_lookup 𝔐 ρ hη _ h
  | topI => intro _ _ _ _; trivial
  | botE _ ih => intro hlc η ρ hη; exact (ih hlc.2 η ρ hη).elim
  | andI _ _ ih₁ ih₂ =>
      intro hlc η ρ hη; exact ⟨ih₁ hlc.1 η ρ hη, ih₂ hlc.2 η ρ hη⟩
  | andE₁ _ ih => intro hlc η ρ hη; exact (ih hlc η ρ hη).1
  | andE₂ _ ih => intro hlc η ρ hη; exact (ih hlc η ρ hη).2
  | orI₁ _ ih => intro hlc η ρ hη; exact ih hlc η ρ hη
  | orI₂ _ ih => intro hlc η ρ hη; exact ih hlc η ρ hη
  | @orE Γ r p q A B K y z hy hz dr d₁ d₂ ihr ih₁ ih₂ =>
      intro hlc η ρ hη
      show Refines 𝔐 [] ρ K (match denote 𝔐 dr η ρ with
        | .inl a => denote 𝔐 d₁ (.cons a η) ρ
        | .inr b => denote 𝔐 d₂ (.cons b η) ρ)
      have hr := ihr hlc.1 η ρ hη
      cases hw : denote 𝔐 dr η ρ with
      | inl a =>
          rw [hw] at hr
          exact ih₁ (Pf.lcI_openP y p 0 0 hlc.2.1) (.cons a η) ρ (.cons hr hη)
      | inr b =>
          rw [hw] at hr
          exact ih₂ (Pf.lcI_openP z q 0 0 hlc.2.2) (.cons b η) ρ (.cons hr hη)
  | @impI Γ p A B z hz _ ih =>
      intro hlc η ρ hη v hv
      exact ih (Pf.lcI_openP z p 0 0 hlc) (.cons v η) ρ (.cons hv hη)
  | impE _ _ ih₁ ih₂ =>
      intro hlc η ρ hη; exact ih₁ hlc.1 η ρ hη _ (ih₂ hlc.2 η ρ hη)
  | @circI Γ q p A _ ih =>
      intro hlc η ρ hη
      cases q with
      | all => intro z hz; exact hz ▸ ih hlc η ρ hη
      | ex  => exact ⟨_, rfl, ih hlc η ρ hη⟩
  | @circE Γ q p b A B z hz dp db ihp ihb =>
      intro hlc η ρ hη
      have hp := ihp hlc.1 η ρ hη
      have hlb := Pf.lcI_openP z b 0 0 hlc.2
      cases q with
      | all =>
          intro x hx
          obtain ⟨w, hw, hqx⟩ := hx
          exact ihb hlb (.cons w η) ρ (.cons (hp w hw) hη) x hqx
      | ex =>
          obtain ⟨w, hw, hsw⟩ := hp
          obtain ⟨x, hx, hsx⟩ := ihb hlb (.cons w η) ρ (.cons hsw hη)
          exact ⟨x, ⟨w, hw, hx⟩, hsx⟩
  | @allI Γ p A a ha d ih =>
      intro hlc η ρ hη e
      have hd := ih (Pf.lcI_openI p 0 (.fvar a) trivial hlc) η (upd 𝔐 ρ a e)
        (CtxRefines_upd 𝔐 ρ a e ha.1 hη)
      have key := (Refines_openAt 𝔐 (upd 𝔐 ρ a e) (.fvar a) trivial A []
        (cast (Val_openWith 𝔐 a A) (denote 𝔐 d η (upd 𝔐 ρ a e)))).mp
        (by rw [cast_left (Val_openWith 𝔐 a A)]; exact hd)
      have : evalTm 𝔐 [] (upd 𝔐 ρ a e) (.fvar a) = e := by simp [evalTm, upd]
      rw [this] at key
      exact (Refines_upd 𝔐 ρ a e A [e] _ ha.2.2).mp key
  | @allE Γ p A B t d h ih =>
      intro hlc η ρ hη
      subst h
      exact (Refines_openAt 𝔐 ρ t hlc.1 A [] (denote 𝔐 d η ρ (evalTm 𝔐 [] ρ t))).mpr
        (ih hlc.2 η ρ hη (evalTm 𝔐 [] ρ t))
  | @exI Γ p A t d ih =>
      intro hlc η ρ hη
      exact (Refines_openAt 𝔐 ρ t hlc.1 A [] (cast (Val_openAt 𝔐 t A 0) (denote 𝔐 d η ρ))).mp
        (by rw [cast_left (Val_openAt 𝔐 t A 0)]; exact ih hlc.2 η ρ hη)
  | @exE Γ r p A K a z ha hK hz dr db ihr ihb =>
      intro hlc η ρ hη
      have hr := ihr hlc.1 η ρ hη
      have hw : Refines 𝔐 [] (upd 𝔐 ρ a (denote 𝔐 dr η ρ).1) (A.openWith a)
          (cast (Val_openWith 𝔐 a A).symm (denote 𝔐 dr η ρ).2) := by
        refine (Refines_openAt 𝔐 (upd 𝔐 ρ a (denote 𝔐 dr η ρ).1) (.fvar a) trivial A []
          ((denote 𝔐 dr η ρ).2)).mpr ?_
        have he : evalTm 𝔐 [] (upd 𝔐 ρ a (denote 𝔐 dr η ρ).1) (.fvar a)
            = (denote 𝔐 dr η ρ).1 := by simp [evalTm, upd]
        rw [he]
        exact (Refines_upd 𝔐 ρ a _ A _ _ ha.2.2).mpr hr
      have hlb := Pf.lcI_openP z (p.openIWith a) 0 0
        (Pf.lcI_openI p 0 (.fvar a) trivial hlc.2)
      have := ihb hlb (.cons (cast (Val_openWith 𝔐 a A).symm (denote 𝔐 dr η ρ).2) η)
        (upd 𝔐 ρ a (denote 𝔐 dr η ρ).1) (.cons hw (CtxRefines_upd 𝔐 ρ a _ ha.1 hη))
      exact (Refines_upd 𝔐 ρ a _ K [] _ hK).mp this

end LaxLogic.QLL
