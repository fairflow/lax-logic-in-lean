import LaxLogic.PLLFiniteModel
import LaxLogic.PLLTheorems

/-!
# Context-completeness for PLL (Fairtlough–Mendler, TYPES 2000, Theorem 6)

Reference: Matt Fairtlough & Michael Mendler, *On the Logical Content of
Computational Type Theory: A Solution to Curry's Problem*, TYPES 2000,
LNCS 2277, pp. 63–78.

## Phase-1 target statement (located)

**Theorem 6.**  For every lax proposition `φ`,
  `PLL ⊢ φ   ⟺   ∀ C ∈ 𝕊,  IPL ⊢ φ^C`
where
* a *basic constraint* is `[K,L]φ := K ⊃ (φ ∨ L)` (`K,L` arbitrary IPL formulas);
* a *standard constraint* `C ∈ 𝕊` is a finite conjunction `⨅_{i<n} [Kᵢ,Lᵢ]`
  (depth `n`; depth-0 = `⊤ = [false,false]`);
* `φ^C` is `φ` with **every** subformula `◯ψ` replaced by `C[ψ^C]` — the *same*
  `C` at every `◯` (independent expansion is unsound, paper footnote p.2).

## What the codebase already provides (verified in Phase 1)

* `PLLND.ConstraintModel` (`LaxLogic/PLLKripke.lean`) is **exactly** the paper's
  Def 3/4: `(W, Ri, Rm, F, V)` with `Rm ⊆ Ri`, `F` `Ri`-hereditary, `V`
  hereditary and full on `F`, and the ◯-clause
  `force w (◯φ) = ∀ v, Ri w v → ∃ u, Rm v u ∧ force u φ`.
  (Codebase uses *preorders*, the paper *partial orders*; immaterial for
  soundness/completeness/FMP.)
* `PLLND.soundness`, `PLLND.completeness`, `PLLND.consequence_iff_derivable`
  (`LaxLogic/PLLCompleteness.lean`) = the paper's cited **Theorem 5** (F&M 1997).
* `PLLND.finite_model_property` (`LaxLogic/PLLFiniteModel.lean`) = **finite**
  constraint-model completeness (F&M Thm 4.6) — the finite-model input Theorem 6's
  completeness direction needs.
* `LaxND.rename`/`weaken` (structural), `iff_congr_*`, `strong_extensionality`,
  `conservativity` (PLL conservative over IPL) — `PLLNDCore`/`PLLTheorems`.

## This file

The **soundness direction** of Theorem 6 (the reusable tool, priority 1):
`PLL ⊢ φ  ⟹  IPL ⊢ φ^C` for every standard constraint `C`, in full sequent form
`LaxND Γ φ → LaxND (Γ.map (·^C)) (φ^C)` (`translate`).  This is the "each context
provides a sound interpretation of CTT" content, mechanised for arbitrary standard
constraints.  Because `φ^C` is `◯`-free when `C`'s `K,L` are, it is a genuine IPL
proof (via `conservativity`).

The **completeness direction** (Lemma 7: express `◯` over a finite model as a single
standard constraint) is the harder half; its status is tracked at the end of the file.
-/

open PLLFormula

namespace PLLND
namespace Ctx

/-! ## Standard constraints and the constraint substitution `φ^C` -/

/-- A basic constraint `[K,L]` acts on `x` as `K ⊃ (x ∨ L)`. -/
def basic (K L x : PLLFormula) : PLLFormula := K.ifThen (x.or L)

/-- A standard constraint is a finite list of `(K,L)` pairs.  It acts on `x` as the
conjunction `⋀ᵢ (Kᵢ ⊃ (x ∨ Lᵢ))`; the empty list is depth-0 `⊤`. -/
abbrev StdCtx := List (PLLFormula × PLLFormula)

/-- `C[x]` — the standard constraint `C` applied to `x`. -/
def applyC : StdCtx → PLLFormula → PLLFormula
  | [], _ => truePLL
  | (K, L) :: rest, x => (basic K L x).and (applyC rest x)

/-- The constraint substitution `φ^C`: replace every `◯ψ` by `C[ψ^C]`. -/
def subC (C : StdCtx) : PLLFormula → PLLFormula
  | .prop a     => .prop a
  | .falsePLL   => .falsePLL
  | .and φ ψ    => .and (subC C φ) (subC C ψ)
  | .or φ ψ     => .or (subC C φ) (subC C ψ)
  | .ifThen φ ψ => .ifThen (subC C φ) (subC C ψ)
  | .somehow φ  => applyC C (subC C φ)

/-! ## The C-monad structure of a standard constraint in IPL

Each standard constraint `C` is a strong monad on IPL: it supports a `unit`
`A ⊢ C[A]` and a Kleisli `bind` `Γ ⊢ C[A]`, `A::Γ ⊢ C[B]` ⟹ `Γ ⊢ C[B]`.  These
are exactly what the `◯`-rules (`laxIntro`, `laxElim`) translate to. -/

/-- `⊤` is derivable in any context. -/
def truePLL_intro (Δ : List PLLFormula) : LaxND Δ truePLL :=
  .impIntro (.iden (List.mem_cons_self ..))

/-- **Unit** `A ⊢ C[A]`: the translation of `◯I`.  (Paper's `C_I`.) -/
def unitC (C : StdCtx) {Δ : List PLLFormula} {A : PLLFormula}
    (p : LaxND Δ A) : LaxND Δ (applyC C A) := by
  induction C with
  | nil => exact truePLL_intro Δ
  | cons hd tl ih =>
      obtain ⟨K, L⟩ := hd
      exact .andIntro (.impIntro (.orIntro1 (p.weaken K))) ih

/-- **Bind** `Γ ⊢ C[A]`, `A::Γ ⊢ C[B]`  ⟹  `Γ ⊢ C[B]`: the translation of `◯E`.
For a conjunction of basic constraints the bind is componentwise. -/
def bindC (C : StdCtx) {Δ : List PLLFormula} {A B : PLLFormula}
    (h1 : LaxND Δ (applyC C A)) (h2 : LaxND (A :: Δ) (applyC C B)) :
    LaxND Δ (applyC C B) := by
  induction C with
  | nil => exact truePLL_intro Δ
  | cons hd tl ih =>
      obtain ⟨K, L⟩ := hd
      refine .andIntro ?_ (ih h1.andElim2 h2.andElim2)
      -- goal: LaxND Δ (basic K L B) = LaxND Δ (K ⊃ (B ∨ L))
      apply LaxND.impIntro
      -- context K :: Δ, goal B ∨ L
      have hA : LaxND (K :: Δ) (A.or L) :=
        .impElim (h1.andElim1.weaken K) (.iden (List.mem_cons_self ..))
      refine .orElim hA ?_ ?_
      · -- case A: context A :: K :: Δ
        have hKB : LaxND (A :: K :: Δ) (K.ifThen (B.or L)) :=
          h2.andElim1.rename (by
            intro ψ hψ
            rcases List.mem_cons.mp hψ with rfl | h
            · exact List.mem_cons_self ..
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))
        exact .impElim hKB (.iden (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      · -- case L: context L :: K :: Δ
        exact .orIntro2 (.iden (List.mem_cons_self ..))

/-! ## Soundness direction of Theorem 6 -/

/-- **Theorem 6, soundness direction (sequent form).**  Every standard constraint
`C` gives a sound interpretation of PLL in IPL: a PLL derivation `Γ ⊢ φ` translates
to an IPL derivation `Γ^C ⊢ φ^C`. -/
def translate (C : StdCtx) : {Γ : List PLLFormula} → {φ : PLLFormula} →
    LaxND Γ φ → LaxND (Γ.map (subC C)) (subC C φ)
  | _, _, .iden h        => .iden (List.mem_map_of_mem h)
  | _, _, .falsoElim φ p => .falsoElim (subC C φ) (translate C p)
  | _, _, .impIntro p    => .impIntro (translate C p)
  | _, _, .impElim p₁ p₂ => .impElim (translate C p₁) (translate C p₂)
  | _, _, .andIntro p₁ p₂ => .andIntro (translate C p₁) (translate C p₂)
  | _, _, .andElim1 p    => .andElim1 (translate C p)
  | _, _, .andElim2 p    => .andElim2 (translate C p)
  | _, _, .orIntro1 p    => .orIntro1 (translate C p)
  | _, _, .orIntro2 p    => .orIntro2 (translate C p)
  | _, _, .orElim p₀ p₁ p₂ => .orElim (translate C p₀) (translate C p₁) (translate C p₂)
  | _, _, .laxIntro p    => unitC C (translate C p)
  | _, _, .laxElim p₁ p₂ => bindC C (translate C p₁) (translate C p₂)

/-- **Theorem 6, soundness direction (closed form).**  If `PLL ⊢ φ` then
`IPL ⊢ φ^C` for every standard constraint `C`. -/
theorem thm6_soundness (C : StdCtx) {φ : PLLFormula}
    (h : Nonempty (LaxND [] φ)) : Nonempty (LaxND [] (subC C φ)) :=
  h.elim fun p => ⟨translate C p⟩

/-- Contrapositive, the form used to refute PLL-entailments: if some standard
constraint `C` makes `φ^C` IPL-**un**provable, then `φ` is not a PLL theorem. -/
theorem not_provable_of_subC (C : StdCtx) {φ : PLLFormula}
    (h : ¬ Nonempty (LaxND [] (subC C φ))) : ¬ Nonempty (LaxND [] φ) :=
  fun hp => h (thm6_soundness C hp)

/-! ## `φ^C` is genuinely IPL (◯-free) when `C` is

The paper's `K,L` range over IPL formulas.  When they do, `φ^C` contains no `◯`,
so `LaxND [] (subC C φ)` is a genuine IPL proof (via `PLLND.conservativity`). -/

/-- A standard constraint is IPL when all its `K,L` are `◯`-free. -/
def CtxIsIPL (C : StdCtx) : Prop := ∀ p ∈ C, isIPL p.1 ∧ isIPL p.2

theorem applyC_isIPL {C : StdCtx} (hC : CtxIsIPL C) {x : PLLFormula}
    (hx : isIPL x) : isIPL (applyC C x) := by
  induction C with
  | nil => exact ⟨trivial, trivial⟩
  | cons hd tl ih =>
      obtain ⟨K, L⟩ := hd
      have hKL := hC (K, L) (List.mem_cons_self ..)
      refine ⟨⟨hKL.1, hx, hKL.2⟩, ih (fun p hp => hC p (List.mem_cons_of_mem _ hp))⟩

/-- If every `K,L` in `C` is `◯`-free, then `φ^C` is `◯`-free for every `φ`. -/
theorem subC_isIPL {C : StdCtx} (hC : CtxIsIPL C) : ∀ φ, isIPL (subC C φ)
  | .prop _     => trivial
  | .falsePLL   => trivial
  | .and φ ψ    => ⟨subC_isIPL hC φ, subC_isIPL hC ψ⟩
  | .or φ ψ     => ⟨subC_isIPL hC φ, subC_isIPL hC ψ⟩
  | .ifThen φ ψ => ⟨subC_isIPL hC φ, subC_isIPL hC ψ⟩
  | .somehow φ  => applyC_isIPL hC (subC_isIPL hC φ)

end Ctx
end PLLND

#print axioms PLLND.Ctx.thm6_soundness

/-! ============================================================================
# Completeness direction of Theorem 6

The plan (Fairtlough–Mendler, TYPES 2000, Lemma 7 + Thm 6 completeness):

1. `PLL ⊬ φ` ⟹ (FMP) a **finite** constraint model `M` with a world refuting `φ`.
2. **Semantic completion** `M*`: adjoin a fresh atom `α_w` per world `w`, forced
   at `x` iff `Ri w x` (or `x` fallible).  `M*` agrees with `M` on old atoms.
3. **Lemma 7**: over `M*`, `◯ψ` is forced exactly where the single standard
   constraint `C = ⨅_{u∈Stab} [α_u , ⋁_{u'∈iSucc u} α_{u'}]` applied to `ψ` is.
4. **Congruence**: replacing every `◯` by `C[·]` (i.e. `subC C`) preserves forcing
   in `M*`.  Hence `M* ⊭ subC C φ`, so `PLL ⊬ subC C φ` (soundness), and since
   `subC C φ` is `◯`-free this is `IPL ⊬ φ^C`.

The definitions are adapted to the codebase's **preorders** (the paper uses
partial orders): `Stab` = `Rm`-maximal *cluster* (`∀ t, Rm u t → Rm t u`) and
`iSucc` carries an explicit strictness clause (`¬ Ri v u`).  With these, Lemma 7
needs only **finiteness**, no antisymmetry.
============================================================================ -/

namespace PLLND
namespace Ctx

open Classical

/-! ## Section A — finite-preorder combinatorics (antisymmetry-free)

Two facts about a reflexive-transitive relation `R` on a finite type:
reaching a maximal cluster, and factoring a strict step through a cover. -/

/-- In a finite preorder, every nonempty set has an `R`-minimal *cluster*
element: some `m ∈ S` with no element of `S` strictly below it. -/
theorem exists_min_strict {W : Type} [Finite W] (R : W → W → Prop)
    (hrefl : ∀ x, R x x) (htrans : ∀ {a b c}, R a b → R b c → R a c)
    (S : Set W) (hS : S.Nonempty) :
    ∃ m ∈ S, ∀ x ∈ S, R x m → R m x := by
  classical
  let Rlt : W → W → Prop := fun a b => R a b ∧ ¬ R b a
  haveI : IsTrans W Rlt :=
    ⟨fun a b c ⟨hab, hba⟩ ⟨hbc, _⟩ => ⟨htrans hab hbc, fun hca => hba (htrans hbc hca)⟩⟩
  haveI : IsIrrefl W Rlt := ⟨fun _ ⟨h, hn⟩ => hn h⟩
  have hwf : WellFounded Rlt := Finite.wellFounded_of_trans_of_irrefl Rlt
  obtain ⟨m, hmS, hmin⟩ := hwf.has_min S hS
  refine ⟨m, hmS, fun x hxS hxm => ?_⟩
  by_contra hmx
  exact hmin x hxS ⟨hxm, hmx⟩

/-- From any `v`, a maximal cluster is reachable: `∃ u, R v u ∧ ∀ t, R u t → R t u`. -/
theorem exists_max_cluster {W : Type} [Finite W] (R : W → W → Prop)
    (hrefl : ∀ x, R x x) (htrans : ∀ {a b c}, R a b → R b c → R a c) (v : W) :
    ∃ u, R v u ∧ ∀ t, R u t → R t u := by
  obtain ⟨m, hmS, hmin⟩ :=
    exists_min_strict (W := W) (fun a b => R b a) hrefl
      (fun hab hbc => htrans hbc hab) {u | R v u} ⟨v, hrefl v⟩
  refine ⟨m, hmS, fun t hmt => ?_⟩
  exact hmin t (htrans hmS hmt) hmt

/-- A strict `R`-step `R u v`, `¬ R v u` factors through a *cover* of `u`: an
immediate strict successor `u'` (in the cluster sense) with `R u' v`. -/
theorem exists_cover {W : Type} [Finite W] (R : W → W → Prop)
    (hrefl : ∀ x, R x x) (htrans : ∀ {a b c}, R a b → R b c → R a c)
    (u v : W) (huv : R u v) (hvu : ¬ R v u) :
    ∃ u', (R u u' ∧ ¬ R u' u ∧ ∀ t, R u t → R t u' → R t u ∨ R u' t) ∧ R u' v := by
  obtain ⟨m, hmB, hmin⟩ :=
    exists_min_strict (W := W) R hrefl htrans
      {t | R u t ∧ ¬ R t u ∧ R t v} ⟨v, huv, hvu, hrefl v⟩
  obtain ⟨hum, hmu, hmv⟩ := hmB
  refine ⟨m, ⟨hum, hmu, fun t hut htm => ?_⟩, hmv⟩
  by_cases htu : R t u
  · exact Or.inl htu
  · exact Or.inr (hmin t ⟨hut, htu, htrans htm hmv⟩ htm)

/-! ## Section B — the semantic completion `M*` -/

/-- The propositional atoms occurring in a formula. -/
def atoms : PLLFormula → Finset String
  | .prop a     => {a}
  | .falsePLL   => ∅
  | .and φ ψ    => atoms φ ∪ atoms ψ
  | .or φ ψ     => atoms φ ∪ atoms ψ
  | .ifThen φ ψ => atoms φ ∪ atoms ψ
  | .somehow φ  => atoms φ

/-- A finite type admits an injective naming by strings avoiding any given finite
set — the fresh atoms `α_w` of the completion. -/
theorem exists_freshNames (M : ConstraintModel) [Finite M.W] (A : Finset String) :
    ∃ f : M.W → String, Function.Injective f ∧ ∀ w, f w ∉ A := by
  classical
  have hInf : Infinite {s : String // s ∉ A} := by
    have h : ({s : String | s ∈ A}).Finite := A.finite_toSet
    exact (h.infinite_compl).to_subtype
  letI := Fintype.ofFinite M.W
  let e : M.W ≃ Fin (Fintype.card M.W) := Fintype.equivFin M.W
  let g : M.W → ℕ := fun w => (e w).val
  have hg : Function.Injective g := fun a b hab => e.injective (Fin.val_injective hab)
  let ne : ℕ ↪ {s : String // s ∉ A} := Infinite.natEmbedding _
  refine ⟨fun w => (ne (g w)).val, fun a b hab => ?_, fun w => (ne (g w)).property⟩
  exact hg (ne.injective (Subtype.ext hab))

section Completion

open Classical

variable (M : ConstraintModel) [Finite M.W] (φ₀ : PLLFormula)

/-- The fresh naming `α_·` for the completion, avoiding `atoms φ₀`. -/
noncomputable def nm : M.W → String := (exists_freshNames M (atoms φ₀)).choose

theorem nm_inj : Function.Injective (nm M φ₀) :=
  (exists_freshNames M (atoms φ₀)).choose_spec.1

theorem nm_fresh (w : M.W) : nm M φ₀ w ∉ atoms φ₀ :=
  (exists_freshNames M (atoms φ₀)).choose_spec.2 w

/-- Valuation of the completion: at fresh names `nm w`, force `{x | Ri w x} ∪ F`
(the up-set of `w`, closed under `F` for fullness); elsewhere unchanged. -/
noncomputable def Vstar : String → Set M.W := fun s =>
  if h : ∃ w, nm M φ₀ w = s then {x | M.Ri h.choose x ∨ x ∈ M.F} else M.V s

theorem Vstar_name (w : M.W) :
    Vstar M φ₀ (nm M φ₀ w) = {x | M.Ri w x ∨ x ∈ M.F} := by
  have hex : ∃ w', nm M φ₀ w' = nm M φ₀ w := ⟨w, rfl⟩
  have hw : hex.choose = w := nm_inj M φ₀ hex.choose_spec
  simp only [Vstar, dif_pos hex, hw]

theorem Vstar_eq_of_not_range {a : String} (h : ¬ ∃ w, nm M φ₀ w = a) :
    Vstar M φ₀ a = M.V a := by
  simp only [Vstar, dif_neg h]

theorem Vstar_hered : ∀ {a : String} {x y : M.W},
    M.Ri x y → x ∈ Vstar M φ₀ a → y ∈ Vstar M φ₀ a := by
  intro a x y hxy hx
  by_cases h : ∃ w, nm M φ₀ w = a
  · rw [Vstar, dif_pos h] at hx ⊢
    rcases hx with h1 | h2
    · exact Or.inl (M.trans_i h1 hxy)
    · exact Or.inr (M.hered_F hxy h2)
  · rw [Vstar, dif_neg h] at hx ⊢
    exact M.hered_V hxy hx

theorem Vstar_full : ∀ {a : String} {x : M.W}, x ∈ M.F → x ∈ Vstar M φ₀ a := by
  intro a x hx
  by_cases h : ∃ w, nm M φ₀ w = a
  · rw [Vstar, dif_pos h]; exact Or.inr hx
  · rw [Vstar, dif_neg h]; exact M.full_F hx

/-- The semantic completion `M*`: `M` with the enriched valuation. -/
noncomputable def Mstar : ConstraintModel :=
  { M with V := Vstar M φ₀, hered_V := Vstar_hered M φ₀, full_F := Vstar_full M φ₀ }

@[simp] theorem Mstar_W : (Mstar M φ₀).W = M.W := rfl
@[simp] theorem Mstar_Ri : (Mstar M φ₀).Ri = M.Ri := rfl
@[simp] theorem Mstar_Rm : (Mstar M φ₀).Rm = M.Rm := rfl
@[simp] theorem Mstar_F : (Mstar M φ₀).F = M.F := rfl

/-- The fresh propositional variable `α_w`. -/
noncomputable def alpha (w : M.W) : PLLFormula := PLLFormula.prop (nm M φ₀ w)

/-- Characterisation of `α_w` in `M*` (`property (a)`): forced at `x` iff `Ri w x`
(or `x` fallible). -/
theorem force_alpha (w x : M.W) :
    (Mstar M φ₀).force x (alpha M φ₀ w) ↔ M.Ri w x ∨ x ∈ M.F := by
  have h1 : (Mstar M φ₀).force x (alpha M φ₀ w) = (x ∈ Vstar M φ₀ (nm M φ₀ w)) := rfl
  rw [h1, Vstar_name]
  exact Iff.rfl

/-- Coincidence (`property (b)`): `M*` agrees with `M` on any formula whose atoms
avoid the fresh names — in particular on `φ₀` and its subformulas. -/
theorem force_coincide : ∀ (ψ : PLLFormula), (∀ w, nm M φ₀ w ∉ atoms ψ) →
    ∀ (x : M.W), ((Mstar M φ₀).force x ψ ↔ M.force x ψ) := by
  intro ψ
  induction ψ with
  | prop a =>
      intro hψ x
      have hnr : ¬ ∃ w, nm M φ₀ w = a := by
        rintro ⟨w, rfl⟩
        exact hψ w (Finset.mem_singleton_self _)
      have h1 : (Mstar M φ₀).force x (.prop a) = (x ∈ Vstar M φ₀ a) := rfl
      have h2 : M.force x (.prop a) = (x ∈ M.V a) := rfl
      rw [h1, h2, Vstar_eq_of_not_range M φ₀ hnr]
  | falsePLL => intro hψ x; exact Iff.rfl
  | and φ ψ ihφ ihψ =>
      intro hψ x
      have hφ : ∀ w, nm M φ₀ w ∉ atoms φ := fun w hw =>
        hψ w (Finset.mem_union_left _ hw)
      have hψ' : ∀ w, nm M φ₀ w ∉ atoms ψ := fun w hw =>
        hψ w (Finset.mem_union_right _ hw)
      exact and_congr (ihφ hφ x) (ihψ hψ' x)
  | or φ ψ ihφ ihψ =>
      intro hψ x
      have hφ : ∀ w, nm M φ₀ w ∉ atoms φ := fun w hw =>
        hψ w (Finset.mem_union_left _ hw)
      have hψ' : ∀ w, nm M φ₀ w ∉ atoms ψ := fun w hw =>
        hψ w (Finset.mem_union_right _ hw)
      exact or_congr (ihφ hφ x) (ihψ hψ' x)
  | ifThen φ ψ ihφ ihψ =>
      intro hψ x
      have hφ : ∀ w, nm M φ₀ w ∉ atoms φ := fun w hw =>
        hψ w (Finset.mem_union_left _ hw)
      have hψ' : ∀ w, nm M φ₀ w ∉ atoms ψ := fun w hw =>
        hψ w (Finset.mem_union_right _ hw)
      exact forall_congr' fun v => imp_congr Iff.rfl (imp_congr (ihφ hφ v) (ihψ hψ' v))
  | somehow φ ih =>
      intro hψ x
      exact forall_congr' fun v =>
        imp_congr Iff.rfl (exists_congr fun u => and_congr Iff.rfl (ih hψ u))

end Completion

/-! ## Section C — Lemma 7 -/

/-- Forcing of a constraint conjunction `C[x]` is the conjunction of the basic
constraints, over any model. -/
theorem force_applyC_iff (D : ConstraintModel) (C : StdCtx) (x : PLLFormula)
    (w : D.W) :
    D.force w (applyC C x) ↔ ∀ p ∈ C, D.force w (basic p.1 p.2 x) := by
  induction C with
  | nil =>
      constructor
      · intro _ p hp; exact (List.not_mem_nil hp).elim
      · intro _; exact fun v _ hv => hv
  | cons hd tl ih =>
      obtain ⟨K, L⟩ := hd
      have hstep : D.force w (applyC ((K, L) :: tl) x) ↔
          D.force w (basic K L x) ∧ D.force w (applyC tl x) := Iff.rfl
      rw [hstep, ih]
      constructor
      · rintro ⟨hb, hrest⟩ p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact hb
        · exact hrest p hp
      · intro h
        exact ⟨h (K, L) (List.mem_cons_self ..), fun p hp => h p (List.mem_cons_of_mem _ hp)⟩

/-- Finite disjunction of a list of formulas (empty = `⊥`). -/
def bigOr : List PLLFormula → PLLFormula
  | []       => .falsePLL
  | q :: rest => q.or (bigOr rest)

/-- Forcing of `bigOr L`: some disjunct is forced, or the world is fallible
(the empty disjunction `⊥` is still forced at fallible worlds). -/
theorem force_bigOr_iff (D : ConstraintModel) (L : List PLLFormula) (w : D.W) :
    D.force w (bigOr L) ↔ (∃ q ∈ L, D.force w q) ∨ w ∈ D.F := by
  induction L with
  | nil =>
      constructor
      · intro h; exact Or.inr h
      · rintro (⟨q, hq, _⟩ | h)
        · exact (List.not_mem_nil hq).elim
        · exact h
  | cons q rest ih =>
      have hstep : D.force w (bigOr (q :: rest)) ↔
          D.force w q ∨ D.force w (bigOr rest) := Iff.rfl
      rw [hstep, ih]
      constructor
      · rintro (hq | (⟨q', hq', hf'⟩ | hF))
        · exact Or.inl ⟨q, List.mem_cons_self .., hq⟩
        · exact Or.inl ⟨q', List.mem_cons_of_mem _ hq', hf'⟩
        · exact Or.inr hF
      · rintro (⟨q', hq', hf'⟩ | hF)
        · rcases List.mem_cons.mp hq' with rfl | hq'
          · exact Or.inl hf'
          · exact Or.inr (Or.inl ⟨q', hq', hf'⟩)
        · exact Or.inr (Or.inr hF)

section Lemma7

open Classical

attribute [local instance] Classical.propDecidable

variable (M : ConstraintModel) [Fintype M.W] (φ₀ : PLLFormula)

/-- A world is **stable** if it is `Rm`-maximal *up to cluster*: every `Rm`-successor
maps back.  (Preorder-correct form of the paper's "no proper modal successor".) -/
def Stab (u : M.W) : Prop := ∀ t, M.Rm u t → M.Rm t u

/-- `v` is an **immediate successor** (cover) of `u`: strictly `Ri`-above with
nothing strictly in between (up to cluster). -/
def iSucc (u v : M.W) : Prop :=
  M.Ri u v ∧ ¬ M.Ri v u ∧ ∀ t, M.Ri u t → M.Ri t v → M.Ri t u ∨ M.Ri v t

/-- The disjunction `⋁_{u'∈iSucc u} α_{u'}` (empty = `⊥`). -/
noncomputable def Ldis (u : M.W) : PLLFormula :=
  bigOr ((Finset.univ.filter (iSucc M u)).toList.map (alpha M φ₀))

/-- The single standard constraint `C = ⨅_{u∈Stab} [α_u , ⋁_{u'∈iSucc u} α_{u'}]`. -/
noncomputable def C0 : StdCtx :=
  (Finset.univ.filter (Stab M)).toList.map (fun u => (alpha M φ₀ u, Ldis M φ₀ u))

/-- Forcing of `Ldis u` in `M*`: some cover's variable is forced, or fallible. -/
theorem force_Ldis (u w : M.W) :
    (Mstar M φ₀).force w (Ldis M φ₀ u) ↔
      (∃ u', iSucc M u u' ∧ (Mstar M φ₀).force w (alpha M φ₀ u')) ∨ w ∈ M.F := by
  rw [Ldis, force_bigOr_iff]
  constructor
  · rintro (⟨q, hq, hfq⟩ | hF)
    · rw [List.mem_map] at hq
      obtain ⟨u', hu', rfl⟩ := hq
      simp only [Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and] at hu'
      exact Or.inl ⟨u', hu', hfq⟩
    · exact Or.inr hF
  · rintro (⟨u', hu', hf⟩ | hF)
    · refine Or.inl ⟨alpha M φ₀ u', ?_, hf⟩
      rw [List.mem_map]
      have hmem : u' ∈ (Finset.univ.filter (iSucc M u)).toList := by
        simp only [Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and]; exact hu'
      exact ⟨u', hmem, rfl⟩
    · exact Or.inr hF

/-- Forcing of `C[ψ]` in `M*`, unfolded over stable worlds. -/
theorem force_applyC_C0 (ψ : PLLFormula) (w : M.W) :
    (Mstar M φ₀).force w (applyC (C0 M φ₀) ψ) ↔
      ∀ u, Stab M u →
        (Mstar M φ₀).force w (basic (alpha M φ₀ u) (Ldis M φ₀ u) ψ) := by
  rw [force_applyC_iff]
  constructor
  · intro h u hu
    apply h (alpha M φ₀ u, Ldis M φ₀ u)
    rw [C0, List.mem_map]
    have hmem : u ∈ (Finset.univ.filter (Stab M)).toList := by
      simp only [Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and]; exact hu
    exact ⟨u, hmem, rfl⟩
  · intro h p hp
    rw [C0, List.mem_map] at hp
    obtain ⟨u, hu, rfl⟩ := hp
    simp only [Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and] at hu
    exact h u hu

/-- **Lemma 7.**  Over the completion `M*`, the modality `◯ψ` is forced exactly
where the single standard constraint `C0` applied to `ψ` is forced.  Uses only
finiteness (reachable maximal cluster + cover factorization), no antisymmetry. -/
theorem lemma7 (ψ : PLLFormula) (w : M.W) :
    (Mstar M φ₀).force w (.somehow ψ) ↔
      (Mstar M φ₀).force w (applyC (C0 M φ₀) ψ) := by
  constructor
  · -- (⟹)
    intro hSom
    rw [force_applyC_C0]
    intro u hu v hwv hav
    rw [force_alpha] at hav
    show (Mstar M φ₀).force v ψ ∨ (Mstar M φ₀).force v (Ldis M φ₀ u)
    rcases hav with hRiuv | hvF
    · by_cases hvu : M.Ri v u
      · -- v is in u's cluster: use stability of u
        have hRiwu : M.Ri w u := M.trans_i hwv hvu
        obtain ⟨z, hzrm, hzf⟩ := hSom u hRiwu
        have hzu : M.Ri z u := M.sub_mi (hu z hzrm)
        have hfu : (Mstar M φ₀).force u ψ := (Mstar M φ₀).force_hered hzu hzf
        exact Or.inl ((Mstar M φ₀).force_hered hRiuv hfu)
      · -- v strictly above u: factor through a cover
        obtain ⟨u', hcov, hu'v⟩ := exists_cover M.Ri M.refl_i M.trans_i u v hRiuv hvu
        refine Or.inr ?_
        rw [force_Ldis]
        refine Or.inl ⟨u', hcov, ?_⟩
        rw [force_alpha]
        exact Or.inl hu'v
    · exact Or.inl ((Mstar M φ₀).force_of_fallible hvF)
  · -- (⟸)
    intro hC
    rw [force_applyC_C0] at hC
    intro v hwv
    -- reach a stable world u above v
    obtain ⟨u, hvu_rm, hStab_u⟩ :=
      exists_max_cluster M.Rm M.refl_m M.trans_m v
    have hRiwu : M.Ri w u := M.trans_i hwv (M.sub_mi hvu_rm)
    have hau : (Mstar M φ₀).force u (alpha M φ₀ u) := by
      rw [force_alpha]; exact Or.inl (M.refl_i u)
    have hstep : (Mstar M φ₀).force u ψ ∨ (Mstar M φ₀).force u (Ldis M φ₀ u) :=
      hC u hStab_u u hRiwu hau
    have hfin : (Mstar M φ₀).force u ψ := by
      rcases hstep with hψ | hLdis
      · exact hψ
      · rw [force_Ldis] at hLdis
        rcases hLdis with ⟨u', hisucc, halpha⟩ | huF
        · rw [force_alpha] at halpha
          rcases halpha with hriu' | huF
          · exact absurd hriu' hisucc.2.1
          · exact (Mstar M φ₀).force_of_fallible huF
        · exact (Mstar M φ₀).force_of_fallible huF
    exact ⟨u, hvu_rm, hfin⟩

/-- **Congruence under uniform `◯`-replacement.**  Substituting `C0[·]` for every
`◯` (i.e. `subC (C0 M φ₀)`) preserves forcing in `M*` — structural induction with
Lemma 7 at each `◯`. -/
theorem force_subC_C0 : ∀ (ψ : PLLFormula) (w : M.W),
    (Mstar M φ₀).force w (subC (C0 M φ₀) ψ) ↔ (Mstar M φ₀).force w ψ := by
  intro ψ
  induction ψ with
  | prop a => intro w; exact Iff.rfl
  | falsePLL => intro w; exact Iff.rfl
  | and φ ψ ihφ ihψ => intro w; exact and_congr (ihφ w) (ihψ w)
  | or φ ψ ihφ ihψ => intro w; exact or_congr (ihφ w) (ihψ w)
  | ifThen φ ψ ihφ ihψ =>
      intro w
      exact forall_congr' fun v => imp_congr Iff.rfl (imp_congr (ihφ v) (ihψ v))
  | somehow φ ih =>
      intro w
      have h1 : (Mstar M φ₀).force w (subC (C0 M φ₀) (.somehow φ)) ↔
          (Mstar M φ₀).force w (.somehow (subC (C0 M φ₀) φ)) :=
        (lemma7 M φ₀ (subC (C0 M φ₀) φ) w).symm
      rw [h1]
      exact forall_congr' fun v =>
        imp_congr Iff.rfl (exists_congr fun u => and_congr Iff.rfl (ih u))

end Lemma7

/-! ## Section D — the completeness direction of Theorem 6 -/

/-- **Theorem 6, completeness direction.**  If every standard-constraint expansion
`φ^C` is IPL-provable, then `φ` is a PLL theorem.  (Contrapositive: a finite
countermodel `M ⊭ φ`, completed to `M*`, refutes the single constraint `C0`, and
`subC C0 φ` being `◯`-free this is an IPL refutation.) -/
theorem thm6_completeness {φ : PLLFormula}
    (h : ∀ C : StdCtx, Nonempty (LaxND [] (subC C φ))) : Nonempty (LaxND [] φ) := by
  by_contra hnp
  rw [finite_model_property] at hnp
  push_neg at hnp
  obtain ⟨M, hMfin, w₀, hw₀⟩ := hnp
  haveI : Finite M.W := hMfin
  haveI : Fintype M.W := Fintype.ofFinite M.W
  -- `M*` agrees with `M` on `φ`, so `M* ⊭ φ`:
  have hcoin : (Mstar M φ).force w₀ φ ↔ M.force w₀ φ :=
    force_coincide M φ φ (fun w => nm_fresh M φ w) w₀
  have hMstar_nf : ¬ (Mstar M φ).force w₀ φ := fun hf => hw₀ (hcoin.mp hf)
  -- congruence: `M* ⊭ subC C0 φ`:
  have hsub : ¬ (Mstar M φ).force w₀ (subC (C0 M φ) φ) := fun hf =>
    hMstar_nf ((force_subC_C0 M φ φ w₀).mp hf)
  -- but the hypothesis makes `subC C0 φ` provable, hence valid in `M*` — contradiction:
  obtain ⟨p⟩ := h (C0 M φ)
  exact hsub (soundness_valid p (Mstar M φ) w₀)

/-- **Theorem 6** (full context-completeness).  `PLL ⊢ φ` iff every standard
constraint expansion `φ^C` is IPL-provable.  (`subC C φ` is `◯`-free when `C`'s
`K,L` are — `subC_isIPL` — so `Nonempty (LaxND [] (subC C φ))` is genuine IPL
provability via `conservativity`; the witness `C0` built in the completeness proof
has propositional `K,L`, so `CtxIsIPL (C0 M φ)` holds.) -/
theorem thm6 {φ : PLLFormula} :
    Nonempty (LaxND [] φ) ↔ ∀ C : StdCtx, Nonempty (LaxND [] (subC C φ)) :=
  ⟨fun h C => thm6_soundness C h, thm6_completeness⟩

end Ctx
end PLLND

#print axioms PLLND.Ctx.thm6
