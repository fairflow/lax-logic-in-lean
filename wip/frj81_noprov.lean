/-
# FRJ(◯) incompleteness witness #81

    G81  =  ((¬¬◯⊥ ⊃ ◯⊥) ⊃ (◯⊥ ∨ ¬◯⊥))  ⊃  (¬◯⊥ ∨ ¬¬◯⊥)

Two machine-checked facts:

  * `not_PLL_G81`      :  ¬ PLL G81   — a 5-world constraint countermodel;
  * `not_provable_G81` :  ¬ Provable G81  — no `FRJ(G81)`-derivation of G81
    exists, by a simultaneous induction over the two derivation families
    with three invariants (INV-R, INV-ι, INV-β below).

Together (`frj_incompleteness_81`) they exhibit a PLL-invalid formula the
calculus cannot refute: a calculus-level incompleteness witness.

Abbreviations used throughout:  β = ◯⊥, ν = ¬◯⊥, δ = ¬¬◯⊥, ι = ¬¬◯⊥ ⊃ ◯⊥,
ρ13 = ι ⊃ (β ∨ ν), ρ6 = ν ∨ δ, G81 = ρ13 ⊃ ρ6.
-/
import FRJ.Sound
import FRJ.Search.Pin

namespace FRJ81

open FRJ Form

def β : Form := .circ .bot            -- ◯⊥
def ν : Form := .imp β .bot           -- ¬◯⊥
def δ : Form := .imp ν .bot           -- ¬¬◯⊥
def ι : Form := .imp δ β              -- ¬¬◯⊥ ⊃ ◯⊥
def ρ13 : Form := .imp ι (.or β ν)    -- (¬¬◯⊥ ⊃ ◯⊥) ⊃ (◯⊥ ∨ ¬◯⊥)
def ρ6 : Form := .or ν δ              -- ¬◯⊥ ∨ ¬¬◯⊥
def G81 : Form := .imp ρ13 ρ6

/-! ## Semantic refutation lemmas

Each regular derivation `d : FRJr G t Γ C` extracts a model `modR d` whose
root forces every member of `Γ` and refutes `C` (Lemma 3.9).  The lemmas
below turn specific membership patterns in `Γ` into contradictions with
that refutation.  They are stated for an arbitrary goal formula `G`. -/

/-- The root of the extracted model forces the derivation's own context. -/
theorem root_forces {G : Form} {t : Tag} {Γ : List Form} {C : Form}
    (d : FRJr G t Γ C) {X : Form} (h : X ∈ Γ) :
    (modR d).force (modR d).root X :=
  (lemma39R d).1 (preR d).root X ((preR_root_lbl d X).mpr h)

/-- `⊥ ∈ Γ` is impossible: the root would be fallible and hence force `C`,
which the root refutes. -/
theorem kill_bot {G : Form} {t : Tag} {Γ : List Form} {C : Form}
    (d : FRJr G t Γ C) (h : Form.bot ∈ Γ) : False :=
  (lemma39R d).2 ((modR d).fal_force C (root_forces d h))

/-- `C ∈ Γ` is impossible: the root forces `Γ` and refutes `C`. -/
theorem kill_mem {G : Form} {t : Tag} {Γ : List Form} {C : Form}
    (d : FRJr G t Γ C) (h : C ∈ Γ) : False :=
  (lemma39R d).2 (root_forces d h)

/-- A disjunct of a refuted disjunction cannot lie in `Γ`. -/
theorem kill_or_mem {G : Form} {t : Tag} {Γ : List Form} {C₁ C₂ : Form}
    (d : FRJr G t Γ (.or C₁ C₂)) (h : C₁ ∈ Γ ∨ C₂ ∈ Γ) : False := by
  rcases h with h | h
  · exact (lemma39R d).2 (Or.inl (root_forces d h))
  · exact (lemma39R d).2 (Or.inr (root_forces d h))

/-- `ν ∈ Γ` together with `δ ∈ Γ` is impossible for any refuted `C`:
`δ = ¬ν` instantiated at the root itself makes the root fallible. -/
theorem kill_nu_delta {G : Form} {t : Tag} {Γ : List Form} {C : Form}
    (d : FRJr G t Γ C) (hν : ν ∈ Γ) (hδ : δ ∈ Γ) : False := by
  have hfal : (modR d).Fal (modR d).root :=
    root_forces d hδ (modR d).root ((modR d).le_refl _) (root_forces d hν)
  exact (lemma39R d).2 ((modR d).fal_force C hfal)

/-- A world forcing `β = ◯⊥` forces `δ = ¬¬◯⊥`: given `b ≥ w` forcing
`ν = ¬◯⊥`, instantiate `ν` at `b` itself against `β` (monotone) to get
`b` fallible. -/
theorem force_delta_of_beta {K : Kripke} {w : K.W} (h : K.force w β) :
    K.force w δ := by
  intro b hb hbν
  exact hbν b (K.le_refl b) (K.force_mono hb h)

/-- `β ∈ Γ` is impossible when the refuted right formula is `ν ∨ δ`:
the root would force the `δ`-disjunct. -/
theorem kill_beta_or {G : Form} {t : Tag} {Γ : List Form}
    (d : FRJr G t Γ (.or ν δ)) (h : β ∈ Γ) : False := by
  have hδ : (modR d).force (modR d).root δ :=
    force_delta_of_beta (root_forces d h)
  exact (lemma39R d).2 (Or.inr hδ)

/-- `β ∈ Γ` is impossible for a derivation of `Γ ⇒ ⊥` whose tag certifies
the pledge for `⊥`: forcing `◯⊥` at the root yields a fallible world `c`
in the root's modal cone, contradicting the root's own infallibility if
`c` is the root and `tag_cone` otherwise.  (The right formula is carried
as `Z` with `Z = ⊥` so that call sites need not cast the derivation.) -/
theorem kill_beta_tag {G : Form} {t : Tag} {Γ : List Form} {Z : Form}
    (d : FRJr G t Γ Z) (hZ : Z = .bot)
    (htag : t = .barren ∨ ∃ W, t = .chain W ∧ Covers Γ W Z)
    (h : β ∈ Γ) : False := by
  subst hZ
  have hf : (modR d).force (modR d).root (.circ .bot) := root_forces d h
  obtain ⟨c, hrc, hc⟩ := hf (modR d).root ((modR d).le_refl _)
  by_cases hcr : c = (modR d).root
  · exact (lemma39R d).2 (hcr ▸ hc)
  · exact tag_cone d .bot htag c hrc hcr hc

/-! ## Closure inversions

`Cl(Γ)`-membership of each formula of interest reduces, by the shape of
the closure grammar, to plain membership of finitely many formulas. -/

theorem clo_bot {Γ : List Form} (h : Clo Γ .bot) : Form.bot ∈ Γ := by
  cases h with | base h => exact h

theorem clo_beta {Γ : List Form} (h : Clo Γ β) : β ∈ Γ ∨ Form.bot ∈ Γ :=
  match h with
  | .base hm => Or.inl hm
  | .circ hb => Or.inr (clo_bot hb)

theorem clo_nu {Γ : List Form} (h : Clo Γ ν) : ν ∈ Γ ∨ Form.bot ∈ Γ :=
  match h with
  | .base hm => Or.inl hm
  | .imp hb => Or.inr (clo_bot hb)

theorem clo_delta {Γ : List Form} (h : Clo Γ δ) : δ ∈ Γ ∨ Form.bot ∈ Γ :=
  match h with
  | .base hm => Or.inl hm
  | .imp hb => Or.inr (clo_bot hb)

theorem clo_rho13 {Γ : List Form} (h : Clo Γ ρ13) :
    ρ13 ∈ Γ ∨ Form.or β ν ∈ Γ ∨ β ∈ Γ ∨ ν ∈ Γ ∨ Form.bot ∈ Γ :=
  match h with
  | .base hm => Or.inl hm
  | .imp hor =>
      match hor with
      | .base hm => Or.inr (Or.inl hm)
      | .orL hb =>
          match clo_beta hb with
          | Or.inl h => Or.inr (Or.inr (Or.inl h))
          | Or.inr h => Or.inr (Or.inr (Or.inr (Or.inr h)))
      | .orR hn =>
          match clo_nu hn with
          | Or.inl h => Or.inr (Or.inr (Or.inr (Or.inl h)))
          | Or.inr h => Or.inr (Or.inr (Or.inr (Or.inr h)))

/-! ## The shape of regular contexts

Every member of a regular sequent's context is a variable, an implication
or a `◯`-formula: the axiom context is atomic and every join-conclusion
context is assembled from `isPV`/`isImp`/`isCirc` filters.  In particular
no `∨`-formula ever inhabits a regular context. -/

theorem shape_joinCtxAt {n : Nat} {stab th : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form} {F X : Form}
    (h : X ∈ joinCtxAt stab th rhs F) : (X.isPV || X.isImp) = true := by
  simp only [joinCtxAt, List.mem_append] at h
  rcases h with ((h | h) | h) | h
  · obtain ⟨i, hi⟩ := mem_unionAll.mp h
    simp [(List.mem_filter.mp hi).2]
  · simp [(List.mem_filter.mp (interAll_subset 0 (rm_subset h))).2]
  · obtain ⟨i, hi⟩ := mem_unionAll.mp h
    simp [(List.mem_filter.mp hi).2]
  · simp [(List.mem_filter.mp (interAll_subset 0 (restrict_subset h))).2]

theorem shape_joinCtxOr {n : Nat} {stab th : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form} {X : Form}
    (h : X ∈ joinCtxOr stab th rhs) : (X.isPV || X.isImp) = true := by
  simp only [joinCtxOr, List.mem_append] at h
  rcases h with ((h | h) | h) | h
  · obtain ⟨i, hi⟩ := mem_unionAll.mp h
    simp [(List.mem_filter.mp hi).2]
  · simp [(List.mem_filter.mp (interAll_subset 0 h)).2]
  · obtain ⟨i, hi⟩ := mem_unionAll.mp h
    simp [(List.mem_filter.mp hi).2]
  · simp [(List.mem_filter.mp (interAll_subset 0 (restrict_subset h))).2]

theorem shape_circP {n k : Nat} {stab th : Fin (n + 1) → List Form}
    {Δs : Fin (k + 1) → List Form} {X : Form}
    (h : X ∈ joinCtxCircP stab th Δs) : X.isCirc = true := by
  rcases List.mem_append.mp h with h | h
  · obtain ⟨i, hi⟩ := mem_unionAll.mp h
    exact (List.mem_filter.mp hi).2
  · exact isCirc_of_mem_restrictC h

theorem shape_circF {n : Nat} {stab th : Fin (n + 1) → List Form} {X : Form}
    (h : X ∈ joinCtxCircF stab th) : X.isCirc = true := by
  rcases List.mem_append.mp h with h | h
  · obtain ⟨i, hi⟩ := mem_unionAll.mp h
    exact (List.mem_filter.mp hi).2
  · exact (List.mem_filter.mp (interAll_subset 0 h)).2

theorem shape_ctx {G : Form} : ∀ {t : Tag} {Γ : List Form} {C : Form}
    (_d : FRJr G t Γ C) {X : Form}, X ∈ Γ →
    (X.isPV || X.isImp || X.isCirc) = true
  | _, _, _, .axR _ _ _ hΓ, X, hmem => by
      have hpv := (List.mem_filter.mp (rm_subset ((hΓ X).mp hmem))).2
      simp [hpv]
  | _, _, _, .andR1 d _, _, hmem => shape_ctx d hmem
  | _, _, _, .andR2 d _, _, hmem => shape_ctx d hmem
  | _, _, _, .impIn d _ _, _, hmem => shape_ctx d hmem
  | _, _, _, .circIn d _ _, _, hmem => shape_ctx d hmem
  | _, _, _, .joinAt _ _ _ _ _ _ _ hΓ, X, hmem => by
      simp [shape_joinCtxAt ((hΓ X).mp hmem)]
  | _, _, _, .joinAtP _ _ _ _ _ _ _ _ _ _ hΓ, X, hmem => by
      rcases List.mem_append.mp (restrictP_subset ((hΓ X).mp hmem)) with h | h
      · simp [shape_joinCtxAt h]
      · simp [shape_circP h]
  | _, _, _, .joinAtF _ _ _ _ _ _ hΓ, X, hmem => by
      rcases List.mem_append.mp ((hΓ X).mp hmem) with h | h
      · simp [shape_joinCtxAt h]
      · simp [shape_circF h]
  | _, _, _, .joinOr _ _ _ _ _ _ hΓ, X, hmem => by
      simp [shape_joinCtxOr ((hΓ X).mp hmem)]
  | _, _, _, .joinOrP _ _ _ _ _ _ _ _ _ hΓ, X, hmem => by
      rcases List.mem_append.mp (restrictP_subset ((hΓ X).mp hmem)) with h | h
      · simp [shape_joinCtxOr h]
      · simp [shape_circP h]
  | _, _, _, .joinOrF _ _ _ _ _ hΓ, X, hmem => by
      rcases List.mem_append.mp ((hΓ X).mp hmem) with h | h
      · simp [shape_joinCtxOr h]
      · simp [shape_circF h]
  | _, _, _, .joinCirc _ _ _ _ _ _ hΓ, X, hmem => by
      simp [shape_joinCtxOr ((hΓ X).mp hmem)]
  | _, _, _, .joinCircP _ _ _ _ _ _ _ _ _ hΓ, X, hmem => by
      rcases List.mem_append.mp (restrictP_subset ((hΓ X).mp hmem)) with h | h
      · simp [shape_joinCtxOr h]
      · simp [shape_circP h]

/-- No `∨`-formula inhabits a regular context. -/
theorem or_not_mem {G : Form} {t : Tag} {Γ : List Form} {C : Form}
    (d : FRJr G t Γ C) {A B : Form} (h : Form.or A B ∈ Γ) : False := by
  have := shape_ctx d h
  simp [Form.isPV, Form.isImp, Form.isCirc] at this

/-! ## Locating `ρ13` in a join-conclusion context

An implication in a join context lies either in `Σ^⊃` or in the restricted
`Θ^⊃`; in both cases its antecedent lies in `Υ`, so some premise `j₀` has
right formula `ι`, and the formula itself lies in that premise's zones
(directly, or through the (J1) inclusion). -/

theorem rho13_impzones {n : Nat} {stab th : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form}
    (hJ1 : ∀ i j, i ≠ j → stab i ⊆ stab j ++ th j)
    (hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (stab j)) →
      A ∈ upsilon rhs)
    (h : ρ13 ∈ unionAll (fun j => impPart (stab j)) ∨
         ρ13 ∈ restrict (interAll (fun j => impPart (th j))) (upsilon rhs)) :
    ∃ j₀, rhs j₀ = ι ∧ ρ13 ∈ stab j₀ ++ th j₀ := by
  have hι : ι ∈ upsilon rhs := by
    rcases h with h | h
    · exact hJ2 ι (.or β ν) h
    · exact (mem_restrict.mp h).2
  obtain ⟨j₀, -, hj₀⟩ := List.mem_map.mp hι
  refine ⟨j₀, hj₀, ?_⟩
  rcases h with h | h
  · obtain ⟨i, hi⟩ := mem_unionAll.mp h
    have hs : ρ13 ∈ stab i := (List.mem_filter.mp hi).1
    by_cases hij : i = j₀
    · exact List.mem_append_left _ (hij ▸ hs)
    · exact hJ1 i j₀ hij hs
  · have hmem := mem_interAll.mp (restrict_subset h) j₀
    exact List.mem_append_right _ ((List.mem_filter.mp hmem).1)

theorem rho13_joinCtxAt {n : Nat} {stab th : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form} {F : Form}
    (hJ1 : ∀ i j, i ≠ j → stab i ⊆ stab j ++ th j)
    (hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (stab j)) →
      A ∈ upsilon rhs)
    (h : ρ13 ∈ joinCtxAt stab th rhs F) :
    ∃ j₀, rhs j₀ = ι ∧ ρ13 ∈ stab j₀ ++ th j₀ := by
  simp only [joinCtxAt, List.mem_append] at h
  rcases h with ((h | h) | h) | h
  · obtain ⟨i, hi⟩ := mem_unionAll.mp h
    exact absurd (List.mem_filter.mp hi).2 (by decide)
  · exact absurd (List.mem_filter.mp (interAll_subset 0 (rm_subset h))).2 (by decide)
  · exact rho13_impzones hJ1 hJ2 (Or.inl h)
  · exact rho13_impzones hJ1 hJ2 (Or.inr h)

theorem rho13_joinCtxOr {n : Nat} {stab th : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form}
    (hJ1 : ∀ i j, i ≠ j → stab i ⊆ stab j ++ th j)
    (hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (stab j)) →
      A ∈ upsilon rhs)
    (h : ρ13 ∈ joinCtxOr stab th rhs) :
    ∃ j₀, rhs j₀ = ι ∧ ρ13 ∈ stab j₀ ++ th j₀ := by
  simp only [joinCtxOr, List.mem_append] at h
  rcases h with ((h | h) | h) | h
  · obtain ⟨i, hi⟩ := mem_unionAll.mp h
    exact absurd (List.mem_filter.mp hi).2 (by decide)
  · exact absurd (List.mem_filter.mp (interAll_subset 0 h)).2 (by decide)
  · exact rho13_impzones hJ1 hJ2 (Or.inl h)
  · exact rho13_impzones hJ1 hJ2 (Or.inr h)

/-- `classForce` refutes `δ` over EVERY valuation: `◯⊥` collapses to `⊥`
at a final world, so `ν` holds and `δ = ¬ν` fails there. -/
theorem classForce_delta (ats : List Form) : classForce ats δ = false := rfl

/-! ## The three invariants

By simultaneous induction on the two derivation families:

  * INV-R (`invR`)     : no regular context of an `FRJ(G81)`-derivation
    contains `ρ13`;
  * INV-ι (`(invI _).1`): no irregular sequent with right formula `ι` has
    `ρ13` among its zones;
  * INV-β (`(invI _).2`): no irregular sequent with right formula `β` has
    both `ρ13` and (`δ` or `⊥`) among its zones.

The two irregular invariants are packaged as one conjunction over an
arbitrary right formula `C`, guarded by equations on `C`, so that the
recursion stays structural over the mutual derivation families. -/

mutual

theorem invR : ∀ {t : Tag} {Γ : List Form} {C : Form}
    (_d : FRJr G81 t Γ C), ρ13 ∉ Γ
  | _, _, _, .axR _ _ _ hΓ => fun hmem => by
      have hpv := (List.mem_filter.mp (rm_subset ((hΓ ρ13).mp hmem))).2
      exact absurd hpv (by decide)
  | _, _, _, .andR1 d _ => invR d
  | _, _, _, .andR2 d _ => invR d
  | _, _, _, .impIn d _ _ => invR d
  | _, _, _, .circIn d _ _ => invR d
  | _, _, _, @FRJr.joinAt _ n stab th rhs F prem hJ1 hJ2 hcirc hF hFnot hg _ hΓ =>
      fun hmem => by
        obtain ⟨j₀, hj, hz⟩ := rho13_joinCtxAt hJ1 hJ2 ((hΓ ρ13).mp hmem)
        exact (invI (prem j₀)).1 hj hz
  | _, _, _, @FRJr.joinAtP _ n k stab th rhs F t' tps Δs Ds prem dps hJ1 hJ2 hJ5 hJ7 htag hF hFnot hg _ hΓ =>
      fun hmem => by
        rcases List.mem_append.mp (restrictP_subset ((hΓ ρ13).mp hmem)) with h | h
        · obtain ⟨j₀, hj, hz⟩ := rho13_joinCtxAt hJ1 hJ2 h
          exact (invI (prem j₀)).1 hj hz
        · exact imp_not_mem_joinCtxCircP (A := ι) (B := .or β ν) h
  | _, _, _, @FRJr.joinAtF _ n stab th rhs F prem hJ1 hJ2 hF hFnot hg _ hΓ =>
      fun hmem => by
        rcases List.mem_append.mp ((hΓ ρ13).mp hmem) with h | h
        · obtain ⟨j₀, hj, hz⟩ := rho13_joinCtxAt hJ1 hJ2 h
          exact (invI (prem j₀)).1 hj hz
        · exact imp_not_mem_joinCtxCircF (A := ι) (B := .or β ν) h
  | _, _, _, @FRJr.joinOr _ n stab th rhs C₁ C₂ prem hJ1 hJ2 hcirc hC hg _ hΓ =>
      fun hmem => by
        obtain ⟨j₀, hj, hz⟩ := rho13_joinCtxOr hJ1 hJ2 ((hΓ ρ13).mp hmem)
        exact (invI (prem j₀)).1 hj hz
  | _, _, _, @FRJr.joinOrP _ n k stab th rhs C₁ C₂ t' tps Δs Ds prem dps hJ1 hJ2 hJ5 hJ7 htag hC hg _ hΓ =>
      fun hmem => by
        rcases List.mem_append.mp (restrictP_subset ((hΓ ρ13).mp hmem)) with h | h
        · obtain ⟨j₀, hj, hz⟩ := rho13_joinCtxOr hJ1 hJ2 h
          exact (invI (prem j₀)).1 hj hz
        · exact imp_not_mem_joinCtxCircP (A := ι) (B := .or β ν) h
  | _, _, _, @FRJr.joinOrF _ n stab th rhs C₁ C₂ prem hJ1 hJ2 hC hg _ hΓ =>
      fun hmem => by
        rcases List.mem_append.mp ((hΓ ρ13).mp hmem) with h | h
        · obtain ⟨j₀, hj, hz⟩ := rho13_joinCtxOr hJ1 hJ2 h
          exact (invI (prem j₀)).1 hj hz
        · exact imp_not_mem_joinCtxCircF (A := ι) (B := .or β ν) h
  | _, _, _, @FRJr.joinCirc _ n stab th rhs Z prem hJ1 hJ2 hcirc hZ hg _ hΓ =>
      fun hmem => by
        obtain ⟨j₀, hj, hz⟩ := rho13_joinCtxOr hJ1 hJ2 ((hΓ ρ13).mp hmem)
        exact (invI (prem j₀)).1 hj hz
  | _, _, _, @FRJr.joinCircP _ n k stab th rhs Z tps Δs Ds prem dps hJ1 hJ2 hJ5 hJ7 hDs hZ hg _ hΓ =>
      fun hmem => by
        rcases List.mem_append.mp (restrictP_subset ((hΓ ρ13).mp hmem)) with h | h
        · obtain ⟨j₀, hj, hz⟩ := rho13_joinCtxOr hJ1 hJ2 h
          exact (invI (prem j₀)).1 hj hz
        · exact imp_not_mem_joinCtxCircP (A := ι) (B := .or β ν) h

theorem invI : ∀ {St Th : List Form} {C : Form} (_e : FRJi G81 St Th C),
    (C = ι → ρ13 ∉ St ++ Th) ∧
    (C = β → ¬ (ρ13 ∈ St ++ Th ∧ (δ ∈ St ++ Th ∨ Form.bot ∈ St ++ Th)))
  | _, _, _, .axI F hF _ _ =>
      ⟨fun hC => absurd (hC ▸ hF) (by decide),
       fun hC => absurd (hC ▸ hF) (by decide)⟩
  | _, _, _, .andI1 _ _ => ⟨(fun hC => nomatch hC), fun hC => nomatch hC⟩
  | _, _, _, .andI2 _ _ => ⟨(fun hC => nomatch hC), fun hC => nomatch hC⟩
  | _, _, _, .orI _ _ _ _ _ _ _ => ⟨(fun hC => nomatch hC), fun hC => nomatch hC⟩
  | _, _, _, @FRJi.impInI _ S0 T0 Lam ThLam A B d hpre hdisj hA hg _ _ hSt hTh =>
      ⟨fun hC => by
        rw [show ι = Form.imp δ β from rfl] at hC
        injection hC with hA' hB'
        intro hmem
        -- every zone member of the conclusion lies in the premise's zones
        have hmem' : ρ13 ∈ S0 ++ ThLam := by
          rcases List.mem_append.mp hmem with h | h
          · rcases List.mem_append.mp ((hSt ρ13).mp h) with h' | h'
            · exact List.mem_append_left _ h'
            · exact List.mem_append_right _
                ((hpre ρ13).mpr (List.mem_append_right _ h'))
          · exact List.mem_append_right _
              ((hpre ρ13).mpr (List.mem_append_left _ ((hTh ρ13).mp h)))
        -- the side condition A ∈ Cl(Σ,Λ) with A = δ supplies δ or ⊥ there too
        have hd : δ ∈ S0 ++ ThLam ∨ Form.bot ∈ S0 ++ ThLam := by
          rcases clo_delta (hA' ▸ hA) with h | h
          · rcases List.mem_append.mp h with h' | h'
            · exact Or.inl (List.mem_append_left _ h')
            · exact Or.inl (List.mem_append_right _
                ((hpre δ).mpr (List.mem_append_right _ h')))
          · rcases List.mem_append.mp h with h' | h'
            · exact Or.inr (List.mem_append_left _ h')
            · exact Or.inr (List.mem_append_right _
                ((hpre Form.bot).mpr (List.mem_append_right _ h')))
        exact (invI d).2 hB' ⟨hmem', hd⟩,
       fun hC => nomatch hC⟩
  | _, _, _, @FRJi.impNotIn _ t Γ Th A B d hTh hA hAnot hg =>
      ⟨fun hC => by
        rw [show ι = Form.imp δ β from rfl] at hC
        injection hC with hA' hB'
        intro hmem
        have hclo : Clo Γ ρ13 := (hTh ρ13 hmem).1
        rcases clo_rho13 hclo with h | h | h | h | h
        · exact invR d h
        · exact or_not_mem d h
        · exact kill_mem d (hB'.symm ▸ h)
        · rcases clo_delta (hA' ▸ hA) with h' | h'
          · exact kill_nu_delta d h h'
          · exact kill_bot d h'
        · exact kill_bot d h,
       fun hC => nomatch hC⟩
  | _, _, _, @FRJi.circNotIn _ t Γ Th Z d htag hTh hg =>
      ⟨(fun hC => nomatch hC),
       fun hC => by
        rw [show β = Form.circ .bot from rfl] at hC
        injection hC with hZ
        rintro ⟨h1, h2⟩
        have hclo : Clo Γ ρ13 := (hTh ρ13 h1).1
        rcases clo_rho13 hclo with h | h | h | h | h
        · exact invR d h
        · exact or_not_mem d h
        · exact kill_beta_tag d hZ htag h
        · -- ν ∈ Γ; use the second zone member δ or ⊥
          rcases h2 with h2 | h2
          · rcases clo_delta (hTh δ h2).1 with h' | h'
            · exact kill_nu_delta d h h'
            · exact kill_mem d (hZ.symm ▸ h')
          · exact kill_mem d (hZ.symm ▸ clo_bot (hTh Form.bot h2).1)
        · exact kill_mem d (hZ.symm ▸ h)⟩
  | _, _, _, @FRJi.axIC _ F ats hats hFf hg _ hTh =>
      ⟨(fun hC => nomatch hC),
       fun _ => by
        rintro ⟨-, h2⟩
        rcases h2 with h2 | h2
        · -- δ never survives the classForce filter of the modal axiom zone
          have hc := (List.mem_filter.mp ((hTh δ).mp h2)).2
          rw [classForce_delta ats] at hc
          exact Bool.noConfusion hc
        · have hc := (List.mem_filter.mp ((hTh Form.bot).mp h2)).2
          exact Bool.noConfusion hc⟩

end

/-! ## Underivability -/

/-- **Witness #81, calculus half.**  `G81 = ρ13 ⊃ ρ6` has no
`FRJ(G81)`-derivation: the only applicable rule is the regular `⊃∈`, and
its side condition `ρ13 ∈ Cl(Γ)` dies against the invariants and the
semantic refutation lemmas in every branch of the closure inversion. -/
theorem not_provable_G81 : ¬ FRJ.Provable G81 := by
  rintro ⟨t, Γ, ⟨d⟩⟩
  have d' : FRJr G81 t Γ (Form.imp ρ13 ρ6) := d
  cases d' with
  | axR F hF hg hΓ => exact absurd hF (by decide)
  | impIn d hA hg =>
      rcases clo_rho13 hA with h | h | h | h | h
      · exact invR d h
      · exact or_not_mem d h
      · exact kill_beta_or d h
      · exact kill_or_mem d (Or.inl h)
      · exact kill_bot d h
  | joinAt prem hJ1 hJ2 hcirc hF hFnot hg hΓ => exact absurd hF (by decide)
  | joinAtP prem dps hJ1 hJ2 hJ5 hJ7 htag hF hFnot hg hΓ => exact absurd hF (by decide)
  | joinAtF prem hJ1 hJ2 hF hFnot hg hΓ => exact absurd hF (by decide)

/-! ## The countermodel

The 5-world table shared with witness #80: worlds `0 < 1 < 2 < 3`,
`0 < 4`, modal accessibility the identity except `2 Rm 3`, world 3
fallible, no atoms.  Its root refutes `G81`. -/

def sepT : FRJ.Search.Tab where
  n := 5
  root := 0
  leT := [[true,true,true,true,true],[false,true,true,true,false],[false,false,true,true,false],[false,false,false,true,false],[false,false,false,false,true]]
  rmT := [[true,false,false,false,false],[false,true,false,false,false],[false,false,true,true,false],[false,false,false,true,false],[false,false,false,false,true]]
  falT := [false,false,false,true,false]
  atomsT := [[],[],[],[],[]]

theorem sepT_ok : sepT.okB = true := by decide

theorem sepT_root : sepT.root < sepT.n := by decide

def sepK : Kripke := sepT.toKripke sepT_ok sepT_root

set_option maxRecDepth 1000000 in
theorem sepK_refutes : ¬ sepK.force sepK.root G81 := by decide

/-- Control: the refutation is at the root itself and the model is not
degenerate — the root forces the antecedent `ρ13` and refutes the
consequent `ρ6`, so `G81 = ρ13 ⊃ ρ6` fails at the root. -/
theorem sepK_control : sepK.force sepK.root ρ13 ∧ ¬ sepK.force sepK.root ρ6 := by
  constructor <;> decide

/-- **Witness #81, semantic half.**  `G81` is not valid in all constraint
models: `sepK` refutes it at the root. -/
theorem not_PLL_G81 : ¬ FRJ.PLL G81 := fun h => sepK_refutes (h sepK)

/-- **Calculus-level incompleteness witness #81.**  `G81` is PLL-invalid,
yet `FRJ(G81)` cannot derive it — the calculus misses this refutation. -/
theorem frj_incompleteness_81 : ¬ FRJ.PLL G81 ∧ ¬ FRJ.Provable G81 :=
  ⟨not_PLL_G81, not_provable_G81⟩

/-! ## Axiom pins -/

/-- info: 'FRJ81.not_provable_G81' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms not_provable_G81

/-- info: 'FRJ81.not_PLL_G81' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms not_PLL_G81

/-- info: 'FRJ81.frj_incompleteness_81' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms frj_incompleteness_81

end FRJ81
