/-
# `Gbu(G)`, transcribed — the calculus dual to `FRJ(G)`

Stage 2 of `docs/gbu-adoption-plan.md`.  Source: Fiorentini & Ferrari,
*Duality between Unprovability and Provability in Forward
Refutation-search for IPL*, ACM TOCL 21(3) Art. 22 (2020); transcribed
from the LaTeX of arXiv:1804.06689, parked at
`LaxLogic/papers/frj-corr-arxiv-1804.06689.tex` (git-ignored — a
copyrighted preprint, and this repository is public).  Line numbers
below are that file's.

`Gbu(G)` derives the VALIDITY of `G`; `FRJ(G)` derives its refutability.
The point of the pair is the duality (their Theorem 9): a saturated
`FRJ(G)` database that fails to derive `G` can be read back as a
`Gbu(G)`-derivation of `G`.  This file is only the calculus and its
soundness — the read-back is later stages.

**Two judgments** (source 3084–3089), `Ψ ⊆ Sf^L(G)`, `A ∈ Sf^R(G)`:
regular `Ψ ⇒g A` (`GbuR`) and irregular `Ψ →g A` (`GbuI`).  The
irregular judgment has NO left rules: it is the right-focused phase, and
that is what makes backward search backtracking-free.  The two
non-invertible rules are `R∨ₖ` and `L⊃`, and the paper's `Search`
resolves both by querying the `FRJ` database rather than by guessing
(source 3396, 3416).

**Validity of a sequent** (source 3102): `τ` is valid iff
`(⋀ Lhs τ) ⊃ Rhs τ` is, with `⋀∅ = ⊥ ⊃ ⊥`.  `⊢_Gbu(G) G` abbreviates
`⊢_Gbu(G) (∅ ⇒g G)` (source 3107).

**Divergences, logged as made:**

* D1 — `R∨ₖ` (and its focused twin) is split into two constructors
  `rorR1`/`rorR2`, as `FRJ/CalculusV.lean` already splits `∧R`; the
  paper writes one rule with `k ∈ {1,2}`.
* D2 — the blanket well-formedness condition `Lhs ⊆ Sf^L(G)`,
  `Rhs ∈ Sf^R(G)` (source 3084) is NOT carried as a field on every
  constructor.  It is a condition on the sequent LANGUAGE, not a
  per-rule side condition, and soundness does not use it.  It becomes a
  separate predicate when the later stages need it (they will: it bounds
  the search space).
* D3 — left zones are `List Form` with a `CtxEq` (`≐`) field on each
  conclusion that names a member, so the paper's set reading of `A,Ψ`
  survives.  House style, as `FRJ/CalculusV.lean`.
* D4 — soundness is proved SEMANTICALLY, against `Kripke`, where the
  paper maps `Gbu(G)`-derivations into `GJ` (source 3113).  Same
  statement, different route, and the semantic one is stronger: it needs
  no infallibility, so it yields `PLL`-validity, of which the paper's
  `IPL`-validity is a corollary.
-/
import FRJ.Basic
import Meta.Slime

namespace FRJ.Gbu

open Form

/-! ## The calculus (Fig. `fig:GBU`, source 2960–3078) -/

mutual

/-- Regular sequents `Ψ ⇒g A`. -/
inductive GbuR (G : Form) : List Form → Form → Type
  /-- `Ax`, source 2967. -/
  | ax {Γ Ψ : List Form} (A : Form) (hΓ : Γ ≐ A :: Ψ) : GbuR G Γ A
  /-- `L⊥`, source 2975. -/
  | lbot {Γ Ψ : List Form} (C : Form) (hΓ : Γ ≐ .bot :: Ψ) : GbuR G Γ C
  /-- `L∧`, source 2982. -/
  | landL {Γ Ψ : List Form} {A B C : Form}
      (d : GbuR G (A :: B :: Ψ) C) (hΓ : Γ ≐ .and A B :: Ψ) : GbuR G Γ C
  /-- `R∧`, source 2991. -/
  | randR {Γ : List Form} {A B : Form}
      (d₁ : GbuR G Γ A) (d₂ : GbuR G Γ B) : GbuR G Γ (.and A B)
  /-- `L∨`, source 3000. -/
  | lorL {Γ Ψ : List Form} {A B C : Form}
      (d₁ : GbuR G (A :: Ψ) C) (d₂ : GbuR G (B :: Ψ) C)
      (hΓ : Γ ≐ .or A B :: Ψ) : GbuR G Γ C
  /-- `R∨₁`, source 3006 (D1). -/
  | rorR1 {Γ : List Form} {C₁ C₂ : Form}
      (d : GbuI G Γ C₁) : GbuR G Γ (.or C₁ C₂)
  /-- `R∨₂`, source 3006 (D1). -/
  | rorR2 {Γ : List Form} {C₁ C₂ : Form}
      (d : GbuI G Γ C₂) : GbuR G Γ (.or C₁ C₂)
  /-- `L⊃`, source 3012.  The left premise is FOCUSED. -/
  | limpL {Γ Ψ : List Form} {A B C : Form}
      (d₁ : GbuI G (.imp A B :: Ψ) A) (d₂ : GbuR G (B :: Ψ) C)
      (hΓ : Γ ≐ .imp A B :: Ψ) : GbuR G Γ C
  /-- `R⊃ᵢ`, source 3019; side condition `A ∈ Cl(Ψ)`. -/
  | rimpI {Γ : List Form} {A B : Form}
      (d : GbuR G Γ B) (hA : Clo Γ A) : GbuR G Γ (.imp A B)
  /-- `R⊃ₙᵢ`, source 3028; side condition `A ∉ Cl(Ψ)`. -/
  | rimpNI {Γ : List Form} {A B : Form}
      (d : GbuR G (A :: Γ) B) (hA : ¬ Clo Γ A) : GbuR G Γ (.imp A B)

/-- Irregular (right-focused) sequents `Ψ →g A`.  No left rules. -/
inductive GbuI (G : Form) : List Form → Form → Type
  /-- `Ax`, source 3036. -/
  | ax {Γ Ψ : List Form} (A : Form) (hΓ : Γ ≐ A :: Ψ) : GbuI G Γ A
  /-- `R∧`, source 3044. -/
  | randI {Γ : List Form} {A B : Form}
      (d₁ : GbuI G Γ A) (d₂ : GbuI G Γ B) : GbuI G Γ (.and A B)
  /-- `R∨₁`, source 3054 (D1). -/
  | rorI1 {Γ : List Form} {C₁ C₂ : Form}
      (d : GbuI G Γ C₁) : GbuI G Γ (.or C₁ C₂)
  /-- `R∨₂`, source 3054 (D1). -/
  | rorI2 {Γ : List Form} {C₁ C₂ : Form}
      (d : GbuI G Γ C₂) : GbuI G Γ (.or C₁ C₂)
  /-- `R⊃ᵢ`, source 3061; side condition `A ∈ Cl(Ψ)`. -/
  | rimpII {Γ : List Form} {A B : Form}
      (d : GbuI G Γ B) (hA : Clo Γ A) : GbuI G Γ (.imp A B)
  /-- `R⊃ₙᵢ`, source 3070; side condition `A ∉ Cl(Ψ)`.  The premise is
  REGULAR — focus is released here. -/
  | rimpNII {Γ : List Form} {A B : Form}
      (d : GbuR G (A :: Γ) B) (hA : ¬ Clo Γ A) : GbuI G Γ (.imp A B)

end

/-- `⊢_Gbu(G) G` (source 3107). -/
def ProvableGbu (G : Form) : Prop := Nonempty (GbuR G [] G)

/-! ## `⋀`, and the paper's validity reading of a sequent -/

/-- `⋀ Ψ`, with `⋀ [] = ⊥ ⊃ ⊥` (source 3102). -/
def bigAnd : List Form → Form
  | [] => .imp .bot .bot
  | A :: Ψ => .and A (bigAnd Ψ)

theorem forces_bigAnd {K : Kripke} {w : K.W} :
    ∀ {Ψ : List Form}, K.forces w Ψ → K.force w (bigAnd Ψ)
  | [], _ => fun _ _ h => h
  | A :: Ψ, h => ⟨h A List.mem_cons_self,
      forces_bigAnd (fun X hX => h X (List.mem_cons_of_mem _ hX))⟩

theorem bigAnd_forces {K : Kripke} {w : K.W} :
    ∀ {Ψ : List Form}, K.force w (bigAnd Ψ) → K.forces w Ψ
  | [], _ => fun _ hX => absurd hX List.not_mem_nil
  | A :: Ψ, h => fun X hX => by
      rcases List.mem_cons.mp hX with rfl | hX'
      · exact h.1
      · exact bigAnd_forces h.2 X hX'

/-- A sequent is VALID when `(⋀ Lhs) ⊃ Rhs` is (source 3102). -/
def SeqValid (Ψ : List Form) (C : Form) : Prop := PLL (.imp (bigAnd Ψ) C)

/-! ## Soundness (Lemma 7, `lemma:GBUsound`, source 3117)

The local form: a derivation transports forcing of the left zone to
forcing of the right formula, at EVERY world of EVERY model.  No
infallibility is used — `L⊥` closes because a fallible world forces
every formula (`Kripke.fal_force`). -/

theorem forces_ctxEq {K : Kripke} {w : K.W} {Γ Γ' : List Form}
    (h : Γ ≐ Γ') (hf : K.forces w Γ) : K.forces w Γ' :=
  fun X hX => hf X ((h X).mpr hX)

mutual

theorem soundR {G : Form} {K : Kripke} :
    ∀ {Ψ : List Form} {C : Form}, GbuR G Ψ C →
      ∀ w : K.W, K.forces w Ψ → K.force w C
  | _, _, .ax A hΓ, w, h => (forces_ctxEq hΓ h) A List.mem_cons_self
  | _, _, .lbot C hΓ, w, h =>
      K.fal_force C ((forces_ctxEq hΓ h) .bot List.mem_cons_self)
  | _, _, .landL d hΓ, w, h => by
      have h' := forces_ctxEq hΓ h
      have hab := h' _ List.mem_cons_self
      refine soundR d w (fun X hX => ?_)
      rcases List.mem_cons.mp hX with rfl | hX'
      · exact hab.1
      rcases List.mem_cons.mp hX' with rfl | hX''
      · exact hab.2
      · exact h' X (List.mem_cons_of_mem _ hX'')
  | _, _, .randR d₁ d₂, w, h => ⟨soundR d₁ w h, soundR d₂ w h⟩
  | _, _, .lorL d₁ d₂ hΓ, w, h => by
      have h' := forces_ctxEq hΓ h
      have hor := h' _ List.mem_cons_self
      have tail : ∀ X ∈ _, K.force w X := fun X hX =>
        h' X (List.mem_cons_of_mem _ hX)
      rcases hor with hA | hB
      · exact soundR d₁ w (fun X hX => by
          rcases List.mem_cons.mp hX with rfl | hX'
          · exact hA
          · exact tail X hX')
      · exact soundR d₂ w (fun X hX => by
          rcases List.mem_cons.mp hX with rfl | hX'
          · exact hB
          · exact tail X hX')
  | _, _, .rorR1 d, w, h => Or.inl (soundI d w h)
  | _, _, .rorR2 d, w, h => Or.inr (soundI d w h)
  | _, _, .limpL d₁ d₂ hΓ, w, h => by
      have h' := forces_ctxEq hΓ h
      have himp := h' _ List.mem_cons_self
      have hA := soundI d₁ w h'
      have hB := himp w (K.le_refl w) hA
      refine soundR d₂ w (fun X hX => ?_)
      rcases List.mem_cons.mp hX with rfl | hX'
      · exact hB
      · exact h' X (List.mem_cons_of_mem _ hX')
  | _, _, .rimpI d _, w, h => fun v hwv hA =>
      soundR d v (K.forces_mono hwv h)
  | _, _, .rimpNI d _, w, h => fun v hwv hA =>
      soundR d v (fun X hX => by
        rcases List.mem_cons.mp hX with rfl | hX'
        · exact hA
        · exact K.force_mono hwv (h X hX'))

theorem soundI {G : Form} {K : Kripke} :
    ∀ {Ψ : List Form} {C : Form}, GbuI G Ψ C →
      ∀ w : K.W, K.forces w Ψ → K.force w C
  | _, _, .ax A hΓ, w, h => (forces_ctxEq hΓ h) A List.mem_cons_self
  | _, _, .randI d₁ d₂, w, h => ⟨soundI d₁ w h, soundI d₂ w h⟩
  | _, _, .rorI1 d, w, h => Or.inl (soundI d w h)
  | _, _, .rorI2 d, w, h => Or.inr (soundI d w h)
  | _, _, .rimpII d _, w, h => fun v hwv hA =>
      soundI d v (K.forces_mono hwv h)
  | _, _, .rimpNII d _, w, h => fun v hwv hA =>
      soundR d v (fun X hX => by
        rcases List.mem_cons.mp hX with rfl | hX'
        · exact hA
        · exact K.force_mono hwv (h X hX'))

end

/-- **Lemma 7** (`lemma:GBUsound`, source 3117): a derivable sequent is
valid.  Proved against every `Kripke` model, so the conclusion is
`PLL`-validity; the paper's `IPL` reading follows. -/
theorem seqValid_of_GbuR {G : Form} {Ψ : List Form} {C : Form}
    (d : GbuR G Ψ C) : SeqValid Ψ C :=
  fun K => fun _ _ hbig => soundR d _ (bigAnd_forces hbig)

theorem seqValid_of_GbuI {G : Form} {Ψ : List Form} {C : Form}
    (d : GbuI G Ψ C) : SeqValid Ψ C :=
  fun K => fun _ _ hbig => soundI d _ (bigAnd_forces hbig)

/-- **Theorem 6** (Soundness of `Gbu(G)`, `theo:GBUsound`, source 3125):
`⊢_Gbu(G) G` implies `G ∈ IPL`.  Stated against the wider `PLL` class,
which is stronger. -/
theorem pll_of_provableGbu {G : Form} (h : ProvableGbu G) : PLL G := by
  obtain ⟨d⟩ := h
  intro K
  exact soundR d K.root (fun _ hX => absurd hX List.not_mem_nil)

theorem ipl_of_provableGbu {G : Form} (h : ProvableGbu G) : IPL G :=
  IPL_of_PLL (pll_of_provableGbu h)

/-! ## The weight, and Lemma 8 (`lemma:wggbu`, source 3216)

    Wg(τ) = ⟨ |Sf^L(G) \ Cl(Ψ)| , tp(τ) , |τ| ⟩,   Ψ = Lhs(τ),
    tp(τ) = 1 if τ regular, 0 otherwise,

ordered lexicographically (source 3196–3212).  The paper proves three
properties and reads the triple off them; they are `unclosed_mono`
(its 1), `unclosed_lt` (its 2) and the `size` arithmetic (its 3).

Why the middle component exists: `L⊃`'s leftmost premise and `R∨ₖ`'s
premise keep the left zone unchanged, so component 1 cannot drop — but
they pass from a regular conclusion to an IRREGULAR premise, and
`1 → 0` is the decrease.  Conversely `GbuI`'s `R⊃ₙᵢ` goes the other way,
irregular conclusion to REGULAR premise, so there component 1 must do
the work — which is exactly the case the paper's property 2 covers. -/

/-- `|Sf^L(G) \ Cl(Ψ)|`. -/
def unclosed (G : Form) (Ψ : List Form) : Nat :=
  (sfL G).countP (fun X => !cloB Ψ X)

/-- **Property 1** (source 3200): the left zone's closure only grows
along a rule, so the count of unclosed left subformulas does not. -/
theorem unclosed_mono {G : Form} {Ψ Ψ' : List Form}
    (h : ∀ X, Clo Ψ X → Clo Ψ' X) : unclosed G Ψ' ≤ unclosed G Ψ := by
  refine countP_mono (fun X _ hX => ?_)
  simp only [Bool.not_eq_true'] at hX ⊢
  exact Bool.eq_false_iff.mpr
    (fun hc => Bool.eq_false_iff.mp hX (cloB_iff.mpr (h X (cloB_iff.mp hc))))

/-- **Property 2** (source 3205): `R⊃ₙᵢ` adds an `A` that was NOT in the
closure, so the count strictly drops.  This is where the blanket
well-formedness condition (divergence D2) is load-bearing: `A` must be a
left subformula of `G` to be counted at all. -/
theorem unclosed_lt {G : Form} {Ψ : List Form} {A : Form}
    (hA : A ∈ sfL G) (hnc : ¬ Clo Ψ A) :
    unclosed G (A :: Ψ) < unclosed G Ψ := by
  refine countP_lt_countP (fun X _ hX => ?_) hA ?_ ?_
  · simp only [Bool.not_eq_true'] at hX ⊢
    exact Bool.eq_false_iff.mpr (fun hc => Bool.eq_false_iff.mp hX
      (cloB_iff.mpr (clo_mono (List.subset_cons_self _ _) (cloB_iff.mp hc))))
  · simp only [Bool.not_eq_true']
    exact Bool.eq_false_iff.mpr (fun hc => hnc (cloB_iff.mp hc))
  · simp only [Bool.not_eq_true', Bool.not_eq_false']
    exact cloB_iff.mpr (.base List.mem_cons_self)

/-- The size of a sequent: the logical symbols of both zones
(source 3145). -/
def seqSize (Ψ : List Form) (C : Form) : Nat :=
  (Ψ.map Form.size).sum + C.size

/-- `tp`: `1` for a regular sequent, `0` for an irregular one. -/
def tp : Bool → Nat
  | true => 1
  | false => 0

/-- `Wg(τ)`. -/
def wg (G : Form) (reg : Bool) (Ψ : List Form) (C : Form) : Nat × Nat × Nat :=
  (unclosed G Ψ, tp reg, seqSize Ψ C)

/-- The lexicographic order `≺` on triples, written out. -/
def WgLt (x y : Nat × Nat × Nat) : Prop :=
  x.1 < y.1 ∨ (x.1 = y.1 ∧
    (x.2.1 < y.2.1 ∨ (x.2.1 = y.2.1 ∧ x.2.2 < y.2.2)))

/-- `⟨0,0,0⟩ ⪯ Wg(τ)` — the lower bound of Lemma 8, which holds because
all three components are `Nat`s. -/
theorem wg_nonneg {G : Form} {reg : Bool} {Ψ : List Form} {C : Form} :
    0 ≤ (wg G reg Ψ C).1 ∧ 0 ≤ (wg G reg Ψ C).2.1 ∧ 0 ≤ (wg G reg Ψ C).2.2 :=
  ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩

/-! ### Size arithmetic

Written out rather than left to `simp`, which pulls `Classical.choice`
here (checked: a probe closing one of these goals by `simp` pins
`[propext, Classical.choice, Quot.sound]`). -/

private theorem size_lt_binL {A B : Form} :
    A.size < A.size + B.size + 1 :=
  Nat.lt_succ_of_le (Nat.le_add_right _ _)

private theorem size_lt_binR {A B : Form} :
    B.size < A.size + B.size + 1 :=
  Nat.lt_succ_of_le (Nat.le_add_left _ _)

private theorem seqSize_lt_right {Ψ : List Form} {X Y : Form}
    (h : X.size < Y.size) : seqSize Ψ X < seqSize Ψ Y :=
  Nat.add_lt_add_left h _

private theorem seqSize_lt_and {Ψ : List Form} {A B C : Form} :
    seqSize (A :: B :: Ψ) C < seqSize (.and A B :: Ψ) C := by
  simp only [seqSize, List.map_cons, List.sum_cons, Form.size]
  rw [← Nat.add_assoc]
  exact Nat.add_lt_add_right (Nat.add_lt_add_right (Nat.lt_succ_self _) _) _

private theorem seqSize_lt_left {Ψ : List Form} {X Y C : Form}
    (h : X.size < Y.size) : seqSize (X :: Ψ) C < seqSize (Y :: Ψ) C := by
  simp only [seqSize, List.map_cons, List.sum_cons]
  exact Nat.add_lt_add_right (Nat.add_lt_add_right h _) _

/-! ### The backward step relation

One constructor per (rule, premise) pair of Fig. `fig:GBU` — the object
"backward proof-search in `Gbu(G)`" acts on, and what Lemma 8 is about.
The two `R⊃ₙᵢ` steps carry `A ∈ Sf^L(G)`, from the sequent language's
blanket condition (D2). -/

inductive Step (G : Form) : (Bool × List Form × Form) →
    (Bool × List Form × Form) → Prop
  | landL {Ψ A B C} : Step G (true, A :: B :: Ψ, C) (true, .and A B :: Ψ, C)
  | randR1 {Ψ A B} : Step G (true, Ψ, A) (true, Ψ, .and A B)
  | randR2 {Ψ A B} : Step G (true, Ψ, B) (true, Ψ, .and A B)
  | lorL1 {Ψ A B C} : Step G (true, A :: Ψ, C) (true, .or A B :: Ψ, C)
  | lorL2 {Ψ A B C} : Step G (true, B :: Ψ, C) (true, .or A B :: Ψ, C)
  | rorR1 {Ψ C₁ C₂} : Step G (false, Ψ, C₁) (true, Ψ, .or C₁ C₂)
  | rorR2 {Ψ C₁ C₂} : Step G (false, Ψ, C₂) (true, Ψ, .or C₁ C₂)
  | limpL1 {Ψ A B C} :
      Step G (false, .imp A B :: Ψ, A) (true, .imp A B :: Ψ, C)
  | limpL2 {Ψ A B C} : Step G (true, B :: Ψ, C) (true, .imp A B :: Ψ, C)
  | rimpI {Ψ A B} : Step G (true, Ψ, B) (true, Ψ, .imp A B)
  | rimpNI {Ψ A B} (hA : A ∈ sfL G) (hnc : ¬ Clo Ψ A) :
      Step G (true, A :: Ψ, B) (true, Ψ, .imp A B)
  | randI1 {Ψ A B} : Step G (false, Ψ, A) (false, Ψ, .and A B)
  | randI2 {Ψ A B} : Step G (false, Ψ, B) (false, Ψ, .and A B)
  | rorI1 {Ψ C₁ C₂} : Step G (false, Ψ, C₁) (false, Ψ, .or C₁ C₂)
  | rorI2 {Ψ C₁ C₂} : Step G (false, Ψ, C₂) (false, Ψ, .or C₁ C₂)
  | rimpII {Ψ A B} : Step G (false, Ψ, B) (false, Ψ, .imp A B)
  | rimpNII {Ψ A B} (hA : A ∈ sfL G) (hnc : ¬ Clo Ψ A) :
      Step G (true, A :: Ψ, B) (false, Ψ, .imp A B)

/-! ### The three closure facts the `≤` component needs -/

theorem clo_and_cons {Ψ : List Form} {A B : Form} :
    ∀ X, Clo (.and A B :: Ψ) X → Clo (A :: B :: Ψ) X := by
  intro X h
  induction h with
  | @base C hC =>
      rcases List.mem_cons.mp hC with rfl | hC'
      · exact .and (.base List.mem_cons_self)
          (.base (List.mem_cons_of_mem _ List.mem_cons_self))
      · exact .base (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hC'))
  | and _ _ ih₁ ih₂ => exact .and ih₁ ih₂
  | orR _ ih => exact .orR ih
  | orL _ ih => exact .orL ih
  | imp _ ih => exact .imp ih
  | circ _ ih => exact .circ ih

theorem clo_or_cons {Ψ : List Form} {A B : Form} :
    ∀ X, Clo (.or A B :: Ψ) X → Clo (A :: Ψ) X := by
  intro X h
  induction h with
  | @base C hC =>
      rcases List.mem_cons.mp hC with rfl | hC'
      · exact .orL (.base List.mem_cons_self)
      · exact .base (List.mem_cons_of_mem _ hC')
  | and _ _ ih₁ ih₂ => exact .and ih₁ ih₂
  | orR _ ih => exact .orR ih
  | orL _ ih => exact .orL ih
  | imp _ ih => exact .imp ih
  | circ _ ih => exact .circ ih

theorem clo_or_cons' {Ψ : List Form} {A B : Form} :
    ∀ X, Clo (.or A B :: Ψ) X → Clo (B :: Ψ) X := by
  intro X h
  induction h with
  | @base C hC =>
      rcases List.mem_cons.mp hC with rfl | hC'
      · exact .orR (.base List.mem_cons_self)
      · exact .base (List.mem_cons_of_mem _ hC')
  | and _ _ ih₁ ih₂ => exact .and ih₁ ih₂
  | orR _ ih => exact .orR ih
  | orL _ ih => exact .orL ih
  | imp _ ih => exact .imp ih
  | circ _ ih => exact .circ ih

theorem clo_imp_cons {Ψ : List Form} {A B : Form} :
    ∀ X, Clo (.imp A B :: Ψ) X → Clo (B :: Ψ) X := by
  intro X h
  induction h with
  | @base C hC =>
      rcases List.mem_cons.mp hC with rfl | hC'
      · exact .imp (.base List.mem_cons_self)
      · exact .base (List.mem_cons_of_mem _ hC')
  | and _ _ ih₁ ih₂ => exact .and ih₁ ih₂
  | orR _ ih => exact .orR ih
  | orL _ ih => exact .orL ih
  | imp _ ih => exact .imp ih
  | circ _ ih => exact .circ ih

/-- **Lemma 8** (`lemma:wggbu`, source 3216): every backward step
strictly decreases `Wg` in the lexicographic order. -/
theorem wg_step {G : Form} {p q : Bool × List Form × Form} (h : Step G p q) :
    WgLt (wg G p.1 p.2.1 p.2.2) (wg G q.1 q.2.1 q.2.2) := by
  -- the component-1 cases: `≤` by property 1, then component 3 decides
  have keep : ∀ {Ψ Ψ' : List Form} {C C' : Form},
      (∀ X, Clo Ψ X → Clo Ψ' X) → seqSize Ψ' C' < seqSize Ψ C →
      WgLt (wg G true Ψ' C') (wg G true Ψ C) := by
    intro Ψ Ψ' C C' hclo hsz
    rcases Nat.lt_or_ge (unclosed G Ψ') (unclosed G Ψ) with hlt | hge
    · exact Or.inl hlt
    · exact Or.inr ⟨Nat.le_antisymm (unclosed_mono hclo) hge,
        Or.inr ⟨rfl, hsz⟩⟩
  cases h with
  | landL => exact keep clo_and_cons seqSize_lt_and
  | randR1 => exact Or.inr ⟨rfl, Or.inr ⟨rfl, seqSize_lt_right size_lt_binL⟩⟩
  | randR2 => exact Or.inr ⟨rfl, Or.inr ⟨rfl, seqSize_lt_right size_lt_binR⟩⟩
  | lorL1 => exact keep clo_or_cons (seqSize_lt_left size_lt_binL)
  | lorL2 => exact keep clo_or_cons' (seqSize_lt_left size_lt_binR)
  | rorR1 | rorR2 | limpL1 => exact Or.inr ⟨rfl, Or.inl Nat.zero_lt_one⟩
  | limpL2 => exact keep clo_imp_cons (seqSize_lt_left size_lt_binR)
  | rimpI => exact Or.inr ⟨rfl, Or.inr ⟨rfl, seqSize_lt_right size_lt_binR⟩⟩
  | rimpNI hA hnc => exact Or.inl (unclosed_lt hA hnc)
  | randI1 => exact Or.inr ⟨rfl, Or.inr ⟨rfl, seqSize_lt_right size_lt_binL⟩⟩
  | randI2 => exact Or.inr ⟨rfl, Or.inr ⟨rfl, seqSize_lt_right size_lt_binR⟩⟩
  | rorI1 => exact Or.inr ⟨rfl, Or.inr ⟨rfl, seqSize_lt_right size_lt_binL⟩⟩
  | rorI2 => exact Or.inr ⟨rfl, Or.inr ⟨rfl, seqSize_lt_right size_lt_binR⟩⟩
  | rimpII => exact Or.inr ⟨rfl, Or.inr ⟨rfl, seqSize_lt_right size_lt_binR⟩⟩
  | rimpNII hA hnc => exact Or.inl (unclosed_lt hA hnc)

/-- info: 'FRJ.Gbu.wg_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms wg_step

/-! ## Stage-2 gate: no computed index in any constructor's return type -/

#slime FRJ.Gbu.GbuR FRJ.Gbu.GbuI

/-- info: 'FRJ.Gbu.soundR' depends on axioms: [propext] -/
#guard_msgs in
#print axioms soundR

/-- info: 'FRJ.Gbu.pll_of_provableGbu' depends on axioms: [propext] -/
#guard_msgs in
#print axioms pll_of_provableGbu

/-- info: 'FRJ.Gbu.ipl_of_provableGbu' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ipl_of_provableGbu

end FRJ.Gbu
