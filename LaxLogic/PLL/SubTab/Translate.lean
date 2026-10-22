import LaxLogic.PLL.SubTab.Complete

/-!
# Closed subframe tableaux as derivations

2026-10-20.  Statements approved by Matthew before the proofs (lean-certify
R10).

A closed tableau (`TCert`, checked by `check`) is translated directly into a
natural-deduction derivation, under the reading

    ⌈⟨false, Γ, Δ⟩⌉ = ⋁Δ          (a world outside S)
    ⌈⟨true,  Γ, Δ⟩⌉ = ◯⋁Δ         (an S-point),        ⋁[] = ⊥

so the yes side of the subframe tableau no longer goes through a completeness
theorem (`SubframeModel.CF.completeness`, i.e. FRJW), and completeness for
finite subframe models follows from the tableau's own dichotomy (`dich`, as in
`complete`, restated here without the certifiers so that no constant of the
old route is reached).
Nothing existing is changed: `yes`, `CF.completeness` and FRJW stay as they
are; `yes'` is an alternative.

Each tableau rule is one definition below (`r_bot`, …, `r_boxR`), stated for
both kinds of world at once through `gl b Δ` (`⋁Δ`, or `◯⋁Δ` when `b`).
Fragment first (CLAUDE.md rule 8): the ◯-free instance (`deriveOf_boxFree`,
`derive_of_check_boxFree`, `completeness_fin_boxFree`) uses the nine ◯-free
rules only.

**The translation is data** (2026-10-22, statements approved by Matthew).  The
derived rules, the tableau rules and the translation are `def`s into `Γ ⊢ A`,
after `LJFO.provable_of_checkDeriv` (`LJF/OCheckDeriv.lean`), with the
recursion and the witnesses of the earlier `Nonempty` proofs, so that a closed
tableau computes its derivation:

    deriveOf : (c : TCert) → (s : SSeq) → check s c = true → (s.ant ⊢ s.goal)
    termOf (φ : PLLFormula) (c : TCert) (h : check ⟨false, [], [φ]⟩ c = true) : [] ⊢ φ

`derive_of_check` is `⟨deriveOf c s h⟩`, its statement and pin unchanged.  Where
a proof split a disjunction (`δ ∈ Δ ++ [A]`, `A ∈ δ :: Δ`), the definition
decides the case instead (`splitApp1`, `splitApp2`, `injBig`), since a
disjunction cannot be eliminated into data.
-/

open PLLFormula

namespace PLLND
namespace SubTab

open SubframeModel.CF

/-! ## The reading of a signed sequent -/

/-- `⋁Δ`, with `⋁[] = ⊥`. -/
def bigOr : List PLLFormula → PLLFormula
  | [] => .falsePLL
  | δ :: Δ => .or δ (bigOr Δ)

/-- What a signed sequent asserts when it has a closed tableau. -/
def SSeq.goal (s : SSeq) : PLLFormula :=
  if s.isS then .somehow (bigOr s.suc) else bigOr s.suc

/-- The reading by the kind of world. -/
def gl : Bool → List PLLFormula → PLLFormula
  | true, Δ => .somehow (bigOr Δ)
  | false, Δ => bigOr Δ

theorem goal_eq (s : SSeq) : s.goal = gl s.isS s.suc := by
  obtain ⟨b, Γ, Δ⟩ := s
  cases b <;> rfl

/-- No ◯ rule anywhere in the certificate. -/
def TCert.boxFree : TCert → Bool
  | .bot | .ax _ => true
  | .andL _ _ c | .orR _ _ c | .impLoc _ _ c | .impR _ _ c => c.boxFree
  | .orL _ _ c₁ c₂ | .impL _ _ c₁ c₂ | .andR _ _ c₁ c₂ => c₁.boxFree && c₂.boxFree
  | .boxL _ _ | .boxLoc _ _ | .boxR _ _ => false

/-! ## Derived rules, as data -/

/-- Weakening, exchange, contraction (`LaxND.rename`). -/
def rn {Γ Γ' : List PLLFormula} {φ : PLLFormula} (H : ∀ ψ, ψ ∈ Γ → ψ ∈ Γ')
    (d : Γ ⊢ φ) : Γ' ⊢ φ :=
  d.rename H

theorem sub_cons {Γ : List PLLFormula} {A : PLLFormula} : ∀ ψ, ψ ∈ Γ → ψ ∈ A :: Γ :=
  fun _ h => List.mem_cons_of_mem _ h

theorem app_cons {Γ : List PLLFormula} {A : PLLFormula} : ∀ ψ, ψ ∈ Γ ++ [A] → ψ ∈ A :: Γ :=
  fun _ h => (List.mem_append.mp h).elim (List.mem_cons_of_mem _)
    fun h => List.mem_singleton.mp h ▸ List.mem_cons_self

theorem cons_cons {Γ : List PLLFormula} {A B : PLLFormula} :
    ∀ ψ, ψ ∈ B :: Γ → ψ ∈ B :: A :: Γ := fun _ h =>
  (List.mem_cons.mp h).elim (fun e => e ▸ List.mem_cons_self)
    fun h => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)

/-- Cut on an appended hypothesis. -/
def cutApp {Γ : List PLLFormula} {A G : PLLFormula} (hA : Γ ⊢ A)
    (d : (Γ ++ [A]) ⊢ G) : Γ ⊢ G :=
  .impElim (.impIntro (rn app_cons d)) hA

/-- Elimination of a big disjunction. -/
def orElimBig {G : PLLFormula} : ∀ (L : List PLLFormula) {Γ : List PLLFormula},
    (Γ ⊢ bigOr L) → (∀ δ ∈ L, (δ :: Γ) ⊢ G) → Γ ⊢ G
  | [], _, d, _ => .falsoElim G d
  | δ :: L, Γ, d, h =>
      .orElim d (h δ List.mem_cons_self)
        (orElimBig L (Γ := bigOr L :: Γ) (.iden List.mem_cons_self)
          fun δ' hδ' => rn cons_cons (h δ' (List.mem_cons_of_mem _ hδ')))

/-- Introduction into a big disjunction, at the first position holding `A`. -/
def injBig {Γ : List PLLFormula} {A : PLLFormula} (d : Γ ⊢ A) :
    ∀ {Δ : List PLLFormula}, A ∈ Δ → Γ ⊢ bigOr Δ
  | [], h => absurd h List.not_mem_nil
  | δ :: _, h =>
      if e : A = δ then .orIntro1 (e ▸ d)
      else .orIntro2 (injBig d ((List.mem_cons.mp h).resolve_left e))

/-- A member of `Δ` gives the reading (with the ◯-unit at an S-point). -/
def injGl {b : Bool} {Γ Δ : List PLLFormula} {A : PLLFormula} (d : Γ ⊢ A)
    (h : A ∈ Δ) : Γ ⊢ gl b Δ :=
  match b with
  | false => injBig d h
  | true => .laxIntro (injBig d h)

/-- **Transfer**: from the reading of `L`, the reading of `Δ`, when each member
of `L` gives the reading of `Δ` (at an S-point by ◯-elimination first). -/
def transfer {b : Bool} {Γ L Δ : List PLLFormula} (d : Γ ⊢ gl b L)
    (h : ∀ δ ∈ L, (δ :: Γ) ⊢ gl b Δ) : Γ ⊢ gl b Δ :=
  match b, d, h with
  | false, d, h => orElimBig L d h
  | true, d, h =>
      .laxElim d (orElimBig L (Γ := bigOr L :: Γ) (.iden List.mem_cons_self)
        fun δ hδ => rn cons_cons (h δ hδ))

theorem mem_app1 {Δ : List PLLFormula} {A δ : PLLFormula} (h : δ ∈ Δ ++ [A]) :
    δ ∈ Δ ∨ δ = A :=
  (List.mem_append.mp h).imp_right List.mem_singleton.mp

theorem mem_app2 {Δ : List PLLFormula} {A B δ : PLLFormula} (h : δ ∈ Δ ++ [A, B]) :
    δ ∈ Δ ∨ δ = A ∨ δ = B :=
  (List.mem_append.mp h).imp_right fun h =>
    (List.mem_cons.mp h).imp_right List.mem_singleton.mp

theorem mem_head_one {Γ : List PLLFormula} {δ B : PLLFormula} (h : δ ∈ [B]) : B ∈ δ :: Γ := by
  rw [List.mem_singleton.mp h]
  exact List.mem_cons_self

/-- A member of `Δ` taken as hypothesis gives the reading of `Δ`. -/
def selfGl {b : Bool} {Γ Δ : List PLLFormula} {δ : PLLFormula} (h : δ ∈ Δ) :
    (δ :: Γ) ⊢ gl b Δ :=
  injGl (.iden List.mem_cons_self) h

/-- The case split on `δ ∈ Δ ++ [A]`, decided: a member of `Δ` gives the
reading of `Δ` (`selfGl`), the new member `A` is handled by `k`. -/
def splitApp1 {b : Bool} {Γ Δ : List PLLFormula} {A δ : PLLFormula}
    (hδ : δ ∈ Δ ++ [A]) (k : (A :: Γ) ⊢ gl b Δ) : (δ :: Γ) ⊢ gl b Δ :=
  if h : δ ∈ Δ then selfGl h
  else ((mem_app1 hδ).resolve_left h) ▸ k

/-- The case split on `δ ∈ Δ ++ [A, B]`, decided. -/
def splitApp2 {b : Bool} {Γ Δ : List PLLFormula} {A B δ : PLLFormula}
    (hδ : δ ∈ Δ ++ [A, B]) (kA : (A :: Γ) ⊢ gl b Δ) (kB : (B :: Γ) ⊢ gl b Δ) :
    (δ :: Γ) ⊢ gl b Δ :=
  if h : δ ∈ Δ then selfGl h
  else if hA : δ = A then hA ▸ kA
  else (((mem_app2 hδ).resolve_left h).resolve_left hA) ▸ kB

/-! ## The rules, one definition each -/

section Rules
variable {b : Bool} {Γ Δ : List PLLFormula} {A B : PLLFormula}

def r_bot (h : PLLFormula.falsePLL ∈ Γ) : Γ ⊢ gl b Δ :=
  .falsoElim _ (.iden h)

def r_ax (hΓ : A ∈ Γ) (hΔ : A ∈ Δ) : Γ ⊢ gl b Δ :=
  injGl (.iden hΓ) hΔ

def r_andL (h : PLLFormula.and A B ∈ Γ) (d : (Γ ++ [A, B]) ⊢ gl b Δ) : Γ ⊢ gl b Δ :=
  let dAB : Γ ⊢ PLLFormula.and A B := .iden h
  let d' : ((Γ ++ [A]) ++ [B]) ⊢ gl b Δ := rn (fun ψ hψ => by
    rcases mem_app2 hψ with hψ | e | e
    · exact List.mem_append_left _ (List.mem_append_left _ hψ)
    · exact List.mem_append_left _ (List.mem_append_right _ (e ▸ List.mem_singleton_self A))
    · exact List.mem_append_right _ (e ▸ List.mem_singleton_self B)) d
  cutApp (.andElim1 dAB) (cutApp (rn (fun _ h => List.mem_append_left _ h) (.andElim2 dAB)) d')

def r_orL (h : PLLFormula.or A B ∈ Γ) (d₁ : (Γ ++ [A]) ⊢ gl b Δ)
    (d₂ : (Γ ++ [B]) ⊢ gl b Δ) : Γ ⊢ gl b Δ :=
  .orElim (.iden h) (rn app_cons d₁) (rn app_cons d₂)

def r_impL (h : PLLFormula.ifThen A B ∈ Γ) (d₁ : Γ ⊢ gl b (Δ ++ [A]))
    (d₂ : (Γ ++ [B]) ⊢ gl b Δ) : Γ ⊢ gl b Δ :=
  transfer d₁ fun _ hδ => splitApp1 hδ
    (cutApp (.impElim (.iden (List.mem_cons_of_mem _ h)) (.iden List.mem_cons_self))
      (rn (fun _ hψ => (List.mem_append.mp hψ).elim
        (fun hψ => List.mem_append_left _ (List.mem_cons_of_mem _ hψ))
        (List.mem_append_right _)) d₂))

def r_andR (h : PLLFormula.and A B ∈ Δ) (d₁ : Γ ⊢ gl b (Δ ++ [A]))
    (d₂ : Γ ⊢ gl b (Δ ++ [B])) : Γ ⊢ gl b Δ :=
  transfer d₁ fun _ hδ => splitApp1 hδ
    (transfer (rn sub_cons d₂) fun _ hδ' => splitApp1 hδ'
      (injGl (.andIntro (.iden (List.mem_cons_of_mem _ List.mem_cons_self))
        (.iden List.mem_cons_self)) h))

def r_orR (h : PLLFormula.or A B ∈ Δ) (d : Γ ⊢ gl b (Δ ++ [A, B])) : Γ ⊢ gl b Δ :=
  transfer d fun _ hδ => splitApp2 hδ
    (injGl (.orIntro1 (.iden List.mem_cons_self)) h)
    (injGl (.orIntro2 (.iden List.mem_cons_self)) h)

def r_impLoc (h : PLLFormula.ifThen A B ∈ Δ) (d : Γ ⊢ gl b (Δ ++ [B])) : Γ ⊢ gl b Δ :=
  transfer d fun _ hδ => splitApp1 hδ
    (injGl (.impIntro (.iden (List.mem_cons_of_mem _ List.mem_cons_self))) h)

def r_impR (h : PLLFormula.ifThen A B ∈ Δ) (d : (Γ ++ [A]) ⊢ gl false [B]) :
    Γ ⊢ gl b Δ :=
  injGl (.impIntro (rn app_cons (orElimBig [B] d fun _ hδ => .iden (mem_head_one hδ)))) h

end Rules

/-! ## (T₀) The translation, ◯-free instance -/

def derive_bf : (c : TCert) → (Γ Δ : List PLLFormula) → c.boxFree = true →
    check ⟨false, Γ, Δ⟩ c = true → Γ ⊢ gl false Δ
  | .bot, Γ, _, _, h =>
    have h : mem .falsePLL Γ = true := by simpa only [check] using h
    r_bot (mem_of h)
  | .ax A, Γ, Δ, _, h =>
    have h : mem A Γ = true ∧ mem A Δ = true := by
      simpa only [check, Bool.and_eq_true] using h
    r_ax (mem_of h.1) (mem_of h.2)
  | .andL A B c, Γ, Δ, hb, h =>
    have h : mem (.and A B) Γ = true ∧ check ⟨false, Γ ++ [A, B], Δ⟩ c = true := by
      simpa only [check, Bool.and_eq_true] using h
    r_andL (mem_of h.1) (derive_bf c _ _ hb h.2)
  | .orL A B c₁ c₂, Γ, Δ, hb, h =>
    have h : (mem (.or A B) Γ = true ∧ check ⟨false, Γ ++ [A], Δ⟩ c₁ = true) ∧
        check ⟨false, Γ ++ [B], Δ⟩ c₂ = true := by
      simpa only [check, Bool.and_eq_true] using h
    have hb : c₁.boxFree = true ∧ c₂.boxFree = true := by
      simpa only [TCert.boxFree, Bool.and_eq_true] using hb
    r_orL (mem_of h.1.1) (derive_bf c₁ _ _ hb.1 h.1.2) (derive_bf c₂ _ _ hb.2 h.2)
  | .impL A B c₁ c₂, Γ, Δ, hb, h =>
    have h : (mem (.ifThen A B) Γ = true ∧ check ⟨false, Γ, Δ ++ [A]⟩ c₁ = true) ∧
        check ⟨false, Γ ++ [B], Δ⟩ c₂ = true := by
      simpa only [check, Bool.and_eq_true] using h
    have hb : c₁.boxFree = true ∧ c₂.boxFree = true := by
      simpa only [TCert.boxFree, Bool.and_eq_true] using hb
    r_impL (mem_of h.1.1) (derive_bf c₁ _ _ hb.1 h.1.2) (derive_bf c₂ _ _ hb.2 h.2)
  | .boxL _ _, _, _, hb, _ => absurd hb Bool.false_ne_true
  | .andR A B c₁ c₂, Γ, Δ, hb, h =>
    have h : (mem (.and A B) Δ = true ∧ check ⟨false, Γ, Δ ++ [A]⟩ c₁ = true) ∧
        check ⟨false, Γ, Δ ++ [B]⟩ c₂ = true := by
      simpa only [check, Bool.and_eq_true] using h
    have hb : c₁.boxFree = true ∧ c₂.boxFree = true := by
      simpa only [TCert.boxFree, Bool.and_eq_true] using hb
    r_andR (mem_of h.1.1) (derive_bf c₁ _ _ hb.1 h.1.2) (derive_bf c₂ _ _ hb.2 h.2)
  | .orR A B c, Γ, Δ, hb, h =>
    have h : mem (.or A B) Δ = true ∧ check ⟨false, Γ, Δ ++ [A, B]⟩ c = true := by
      simpa only [check, Bool.and_eq_true] using h
    r_orR (mem_of h.1) (derive_bf c _ _ hb h.2)
  | .impLoc A B c, Γ, Δ, hb, h =>
    have h : (mem (.ifThen A B) Δ = true ∧ mem A Γ = true) ∧
        check ⟨false, Γ, Δ ++ [B]⟩ c = true := by
      simpa only [check, Bool.and_eq_true] using h
    r_impLoc (mem_of h.1.1) (derive_bf c _ _ hb h.2)
  | .boxLoc _ _, _, _, hb, _ => absurd hb Bool.false_ne_true
  | .impR A B c, Γ, Δ, hb, h =>
    have h : mem (.ifThen A B) Δ = true ∧ check ⟨false, Γ ++ [A], [B]⟩ c = true := by
      simpa only [check, Bool.and_eq_true] using h
    r_impR (mem_of h.1) (derive_bf c _ _ hb h.2)
  | .boxR _ _, _, _, hb, _ => absurd hb Bool.false_ne_true

/-- **(T₀) Translation, ◯-free instance, as data.** -/
def deriveOf_boxFree : (c : TCert) → (s : SSeq) → c.boxFree = true → s.isS = false →
    check s c = true → (s.ant ⊢ bigOr s.suc)
  | c, ⟨false, Γ, Δ⟩, hb, _, h => derive_bf c Γ Δ hb h
  | _, ⟨true, _, _⟩, _, hs, _ => absurd hs.symm Bool.false_ne_true

/-- **(T₀) Translation, ◯-free instance.** -/
theorem derive_of_check_boxFree : ∀ (c : TCert) (s : SSeq),
    c.boxFree = true → s.isS = false → check s c = true → Nonempty (s.ant ⊢ bigOr s.suc) :=
  fun c s hb hs h => ⟨deriveOf_boxFree c s hb hs h⟩

/-! ## Completeness for finite subframe models, ◯-free instance -/

/-- A finite countermodel contradicts validity in finite decidable models. -/
theorem refutes_valid {φ : PLLFormula} {m : SubCM} (hm : m.refutes φ = true)
    (h : ∀ (M : SubframeModel) [FinDec M] (x : M.W), M.force x φ) : False := by
  simp only [SubCM.refutes, Bool.and_eq_true, Bool.not_eq_true'] at hm
  have hr := (SubCM.ok_parts hm.1).1
  have := (SubCM.forceB_iff hm.1 φ ⟨m.root, hr⟩).mpr (h (m.toModel hm.1) ⟨m.root, hr⟩)
  rw [hm.2] at this
  exact Bool.false_ne_true this

/-- Over a closed universe without ◯, a certificate that checks uses no ◯ rule. -/
theorem boxFree_of_check {U : List PLLFormula} (hU : Closed U) (hB : NoBox U) :
    ∀ (c : TCert) (s : SSeq), s.ant ⊆ U → s.suc ⊆ U → check s c = true → c.boxFree = true := by
  intro c
  induction c with
  | bot => intros; rfl
  | ax _ => intros; rfl
  | andL A B c ih =>
    intro s hΓ hΔ h
    simp only [check, Bool.and_eq_true] at h
    have hAB := hU.and A B (hΓ (mem_of h.1))
    exact ih ⟨s.isS, s.ant ++ [A, B], s.suc⟩ (app_sub hΓ (all_two hAB.1 hAB.2)) hΔ h.2
  | orL A B c₁ c₂ ih₁ ih₂ =>
    intro s hΓ hΔ h
    simp only [check, Bool.and_eq_true] at h
    have hAB := hU.or A B (hΓ (mem_of h.1.1))
    simp only [TCert.boxFree, Bool.and_eq_true]
    exact ⟨ih₁ ⟨s.isS, s.ant ++ [A], s.suc⟩ (app_sub hΓ (all_one hAB.1)) hΔ h.1.2,
      ih₂ ⟨s.isS, s.ant ++ [B], s.suc⟩ (app_sub hΓ (all_one hAB.2)) hΔ h.2⟩
  | impL A B c₁ c₂ ih₁ ih₂ =>
    intro s hΓ hΔ h
    simp only [check, Bool.and_eq_true] at h
    have hAB := hU.imp A B (hΓ (mem_of h.1.1))
    simp only [TCert.boxFree, Bool.and_eq_true]
    exact ⟨ih₁ ⟨s.isS, s.ant, s.suc ++ [A]⟩ hΓ (app_sub hΔ (all_one hAB.1)) h.1.2,
      ih₂ ⟨s.isS, s.ant ++ [B], s.suc⟩ (app_sub hΓ (all_one hAB.2)) hΔ h.2⟩
  | boxL A c _ =>
    intro s hΓ _ h
    simp only [check, Bool.and_eq_true] at h
    exact absurd (hΓ (mem_of h.1.2)) (hB A)
  | andR A B c₁ c₂ ih₁ ih₂ =>
    intro s hΓ hΔ h
    simp only [check, Bool.and_eq_true] at h
    have hAB := hU.and A B (hΔ (mem_of h.1.1))
    simp only [TCert.boxFree, Bool.and_eq_true]
    exact ⟨ih₁ ⟨s.isS, s.ant, s.suc ++ [A]⟩ hΓ (app_sub hΔ (all_one hAB.1)) h.1.2,
      ih₂ ⟨s.isS, s.ant, s.suc ++ [B]⟩ hΓ (app_sub hΔ (all_one hAB.2)) h.2⟩
  | orR A B c ih =>
    intro s hΓ hΔ h
    simp only [check, Bool.and_eq_true] at h
    have hAB := hU.or A B (hΔ (mem_of h.1))
    exact ih ⟨s.isS, s.ant, s.suc ++ [A, B]⟩ hΓ (app_sub hΔ (all_two hAB.1 hAB.2)) h.2
  | impLoc A B c ih =>
    intro s hΓ hΔ h
    simp only [check, Bool.and_eq_true] at h
    have hAB := hU.imp A B (hΔ (mem_of h.1.1))
    exact ih ⟨s.isS, s.ant, s.suc ++ [B]⟩ hΓ (app_sub hΔ (all_one hAB.2)) h.2
  | boxLoc A c _ =>
    intro s _ hΔ h
    simp only [check, Bool.and_eq_true] at h
    exact absurd (hΔ (mem_of h.1.2)) (hB A)
  | impR A B c ih =>
    intro s hΓ hΔ h
    simp only [check, Bool.and_eq_true] at h
    have hAB := hU.imp A B (hΔ (mem_of h.1))
    exact ih ⟨false, s.ant ++ [A], [B]⟩ (app_sub hΓ (all_one hAB.1)) (all_one hAB.2) h.2
  | boxR A c _ =>
    intro s _ hΔ h
    simp only [check, Bool.and_eq_true] at h
    exact absurd (hΔ (mem_of h.1)) (hB A)

/-- `⋁[φ]` gives `φ`. -/
def of_bigOr_one {Γ : List PLLFormula} {φ : PLLFormula} (d : Γ ⊢ bigOr [φ]) : Γ ⊢ φ :=
  orElimBig [φ] d fun _ hδ => .iden (mem_head_one hδ)

/-- The dichotomy of `complete_boxFree`, stated with `check` and `refutes`
directly: the certifier `yes` carries the old soundness proof (through
`CF.completeness`), and a statement that names it would put FRJW among the
constants the new route depends on.  Same proof as `complete_boxFree`. -/
theorem dichotomy_boxFree (φ : PLLFormula) (hφ : NoBox (subs φ)) :
    (∃ c, check ⟨false, [], [φ]⟩ c = true) ∨ (∃ m : SubCM, m.refutes φ = true) := by
  rcases dich_boxFree (subs φ) (subs_closed φ) hφ _ ⟨false, [], [φ]⟩ rfl
      (fun _ h => absurd h List.not_mem_nil) (all_one (self_mem_subs φ)) with
    ⟨c, hc⟩ | ⟨t, hg, hcov⟩
  · exact .inl ⟨c, hc⟩
  · exact .inr ⟨extract (model t hg) (rootW t hg) φ,
      extract_refutes ((root_refutes t hg hcov).2.2 φ List.mem_cons_self)⟩

/-- The dichotomy of `complete`, stated with `check` and `refutes` directly
(see `dichotomy_boxFree`).  Same proof as `complete`. -/
theorem dichotomy (φ : PLLFormula) :
    (∃ c, check ⟨false, [], [φ]⟩ c = true) ∨ (∃ m : SubCM, m.refutes φ = true) := by
  rcases dich (subs φ) (subs_closed φ) _ ⟨false, [], [φ]⟩ rfl
      (fun _ h => absurd h List.not_mem_nil) (all_one (self_mem_subs φ)) with
    ⟨c, hc⟩ | ⟨t, hg, hcov⟩
  · exact .inl ⟨c, hc⟩
  · exact .inr ⟨extract (model t hg) (rootW t hg) φ,
      extract_refutes ((root_refutes t hg hcov).2.2 φ List.mem_cons_self)⟩

/-- **Completeness for finite subframe models, ◯-free instance**, from the
tableau: the dichotomy and (T₀). -/
theorem completeness_fin_boxFree (φ : PLLFormula) (hφ : NoBox (subs φ))
    (h : ∀ (M : SubframeModel) [FinDec M] (x : M.W), M.force x φ) : Holds φ := by
  rcases dichotomy_boxFree φ hφ with ⟨c, hc⟩ | ⟨m, hm⟩
  · have hbf := boxFree_of_check (subs_closed φ) hφ c ⟨false, [], [φ]⟩
      (fun _ h => absurd h List.not_mem_nil) (all_one (self_mem_subs φ)) hc
    exact ⟨of_bigOr_one (deriveOf_boxFree c ⟨false, [], [φ]⟩ hbf rfl hc)⟩
  · exact (refutes_valid hm h).elim

/-! ## The three ◯ rules -/

section BoxRules
variable {Γ Δ : List PLLFormula} {A : PLLFormula}

def r_boxL (h : PLLFormula.somehow A ∈ Γ) (d : (Γ ++ [A]) ⊢ gl true Δ) :
    Γ ⊢ gl true Δ :=
  .laxElim (.iden h) (rn app_cons d)

def r_boxLoc (h : PLLFormula.somehow A ∈ Δ) (d : Γ ⊢ gl true (Δ ++ [A])) :
    Γ ⊢ gl true Δ :=
  transfer d fun _ hδ => splitApp1 hδ (injGl (.laxIntro (.iden List.mem_cons_self)) h)

def r_boxR {b : Bool} (h : PLLFormula.somehow A ∈ Δ) (d : Γ ⊢ gl true [A]) :
    Γ ⊢ gl b Δ :=
  injGl (.laxElim d (orElimBig [A] (G := .somehow A) (Γ := bigOr [A] :: Γ)
    (.iden List.mem_cons_self) fun _ hδ => .laxIntro (.iden (mem_head_one hδ)))) h

end BoxRules

/-! ## (T) The translation, PLL -/

def derive_gl : (c : TCert) → (b : Bool) → (Γ Δ : List PLLFormula) →
    check ⟨b, Γ, Δ⟩ c = true → Γ ⊢ gl b Δ
  | .bot, _, Γ, _, h =>
    have h : mem .falsePLL Γ = true := by simpa only [check] using h
    r_bot (mem_of h)
  | .ax A, _, Γ, Δ, h =>
    have h : mem A Γ = true ∧ mem A Δ = true := by
      simpa only [check, Bool.and_eq_true] using h
    r_ax (mem_of h.1) (mem_of h.2)
  | .andL A B c, b, Γ, Δ, h =>
    have h : mem (.and A B) Γ = true ∧ check ⟨b, Γ ++ [A, B], Δ⟩ c = true := by
      simpa only [check, Bool.and_eq_true] using h
    r_andL (mem_of h.1) (derive_gl c _ _ _ h.2)
  | .orL A B c₁ c₂, b, Γ, Δ, h =>
    have h : (mem (.or A B) Γ = true ∧ check ⟨b, Γ ++ [A], Δ⟩ c₁ = true) ∧
        check ⟨b, Γ ++ [B], Δ⟩ c₂ = true := by
      simpa only [check, Bool.and_eq_true] using h
    r_orL (mem_of h.1.1) (derive_gl c₁ _ _ _ h.1.2) (derive_gl c₂ _ _ _ h.2)
  | .impL A B c₁ c₂, b, Γ, Δ, h =>
    have h : (mem (.ifThen A B) Γ = true ∧ check ⟨b, Γ, Δ ++ [A]⟩ c₁ = true) ∧
        check ⟨b, Γ ++ [B], Δ⟩ c₂ = true := by
      simpa only [check, Bool.and_eq_true] using h
    r_impL (mem_of h.1.1) (derive_gl c₁ _ _ _ h.1.2) (derive_gl c₂ _ _ _ h.2)
  | .boxL A c, b, Γ, Δ, h =>
    have h : (b = true ∧ mem (.somehow A) Γ = true) ∧ check ⟨b, Γ ++ [A], Δ⟩ c = true := by
      simpa only [check, Bool.and_eq_true] using h
    match b, h with
    | true, h => r_boxL (mem_of h.1.2) (derive_gl c _ _ _ h.2)
    | false, h => absurd h.1.1 Bool.false_ne_true
  | .andR A B c₁ c₂, b, Γ, Δ, h =>
    have h : (mem (.and A B) Δ = true ∧ check ⟨b, Γ, Δ ++ [A]⟩ c₁ = true) ∧
        check ⟨b, Γ, Δ ++ [B]⟩ c₂ = true := by
      simpa only [check, Bool.and_eq_true] using h
    r_andR (mem_of h.1.1) (derive_gl c₁ _ _ _ h.1.2) (derive_gl c₂ _ _ _ h.2)
  | .orR A B c, b, Γ, Δ, h =>
    have h : mem (.or A B) Δ = true ∧ check ⟨b, Γ, Δ ++ [A, B]⟩ c = true := by
      simpa only [check, Bool.and_eq_true] using h
    r_orR (mem_of h.1) (derive_gl c _ _ _ h.2)
  | .impLoc A B c, b, Γ, Δ, h =>
    have h : (mem (.ifThen A B) Δ = true ∧ mem A Γ = true) ∧
        check ⟨b, Γ, Δ ++ [B]⟩ c = true := by
      simpa only [check, Bool.and_eq_true] using h
    r_impLoc (mem_of h.1.1) (derive_gl c _ _ _ h.2)
  | .boxLoc A c, b, Γ, Δ, h =>
    have h : (b = true ∧ mem (.somehow A) Δ = true) ∧ check ⟨b, Γ, Δ ++ [A]⟩ c = true := by
      simpa only [check, Bool.and_eq_true] using h
    match b, h with
    | true, h => r_boxLoc (mem_of h.1.2) (derive_gl c _ _ _ h.2)
    | false, h => absurd h.1.1 Bool.false_ne_true
  | .impR A B c, _, Γ, Δ, h =>
    have h : mem (.ifThen A B) Δ = true ∧ check ⟨false, Γ ++ [A], [B]⟩ c = true := by
      simpa only [check, Bool.and_eq_true] using h
    r_impR (mem_of h.1) (derive_gl c _ _ _ h.2)
  | .boxR A c, _, Γ, Δ, h =>
    have h : mem (.somehow A) Δ = true ∧ check ⟨true, Γ, [A]⟩ c = true := by
      simpa only [check, Bool.and_eq_true] using h
    r_boxR (mem_of h.1) (derive_gl c _ _ _ h.2)

/-- **(T) Translation, PLL, as data.**  A closed tableau for a signed sequent
is a natural-deduction derivation of its reading. -/
def deriveOf : (c : TCert) → (s : SSeq) → check s c = true → (s.ant ⊢ s.goal)
  | c, ⟨b, Γ, Δ⟩, h => (goal_eq ⟨b, Γ, Δ⟩) ▸ derive_gl c b Γ Δ h

/-- **(T) Translation, PLL.** -/
theorem derive_of_check : ∀ (c : TCert) (s : SSeq),
    check s c = true → Nonempty (s.ant ⊢ s.goal) :=
  fun c s h => ⟨deriveOf c s h⟩

/-! ## (Y) The yes side without a completeness theorem -/

/-- **The proof term of a closed tableau**: a closed tableau for `⊢ φ` is a
natural-deduction derivation of `φ`, by the tableau's own rules. -/
def termOf (φ : PLLFormula) (c : TCert) (h : check ⟨false, [], [φ]⟩ c = true) : [] ⊢ φ :=
  of_bigOr_one (derive_gl c false [] [φ] h)

/-- **(Y)** A closed tableau for `⊢ φ` proves `φ`, by the tableau's own rules. -/
theorem holds_of_check' {φ : PLLFormula} {c : TCert}
    (h : check ⟨false, [], [φ]⟩ c = true) : Holds φ :=
  ⟨termOf φ c h⟩

/-- The yes side, justified by the tableau's own rules (an alternative to `yes`;
both kept and pinned). -/
def yes' : Certify.Certifier PLLFormula TCert Holds where
  check φ c := check ⟨false, [], [φ]⟩ c
  sound _ _ h := holds_of_check' h

/-! ## (C) Completeness for finite subframe models -/

/-- **(C) Completeness for finite subframe models**, from the tableau: the
dichotomy and (Y). -/
theorem completeness_fin (φ : PLLFormula)
    (h : ∀ (M : SubframeModel) [FinDec M] (x : M.W), M.force x φ) : Holds φ := by
  rcases dichotomy φ with ⟨c, hc⟩ | ⟨m, hm⟩
  · exact holds_of_check' hc
  · exact (refutes_valid hm h).elim

end SubTab
end PLLND

#axioms_within PLLND.SubTab.deriveOf_boxFree [propext, Quot.sound]
#axioms_within PLLND.SubTab.derive_of_check_boxFree [propext, Quot.sound]
#axioms_within PLLND.SubTab.completeness_fin_boxFree [propext, Quot.sound]
#axioms_within PLLND.SubTab.deriveOf [propext, Quot.sound]
#axioms_within PLLND.SubTab.termOf [propext, Quot.sound]
#axioms_within PLLND.SubTab.derive_of_check [propext, Quot.sound]
#axioms_within PLLND.SubTab.holds_of_check' [propext, Quot.sound]
#axioms_within PLLND.SubTab.yes' [propext, Quot.sound]
#axioms_within PLLND.SubTab.completeness_fin [propext, Quot.sound]
