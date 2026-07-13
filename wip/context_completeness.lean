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
