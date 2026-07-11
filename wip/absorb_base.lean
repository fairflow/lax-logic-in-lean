import LaxLogic.PLLG4UITrunc

/-!
# WIP: the absorption base, ambient-relative form

Hand-executing the pure `gamma_box_map` obligations showed every
boxed γ-position demanding an E-glue one budget below the band — an
infinite regress.  The resolution: the pure statement was stronger
than anything the adequacy landing needs.  The landing always holds
the ambient `E(Γ)`, and with ambient E:

* budget-mono (`E@b ⊢ E@(b-1)`, the easy direction) matches any
  lower guard;
* `box_guard_collapse` opens a guarded box against a ◯-goal;
* `laxL` re-imports ambient at every box crossing, so the inner value
  lands IN CONTEXT — exactly what the pigeonhole/splice shortcut
  consumes (`itp_budget_mono_le` from the repeated state's low value
  into the spliced target slot).

Crux statement (mutual, fuel-inducted; the E-half needs no extra
ambient because E is its own):

    STAB(b):  [E@(b-1)] ⊢ E@b   ∧   E@b, A@b(Γ,C) ⊢ A@(b-1)(Γ,C)

for `b` past the jump-state count.  The cascade lives in the A-half's
jump/γ disjuncts; everything else is the fuel induction.
-/

open PLLFormula

namespace PLLND

/-- Jump-state threshold (overcount). -/
def kcap (S : Finset PLLFormula) : Nat := 2 * S.card + 4

/-!
Case analysis, hand-executed 2026-07-11 (all against the actual
clause tables; the compiler adjudicates next):

E-half `[E@(b-1)] ⊢ E@b` — closes at the fuel level, every case:
* atoms/⊥: project.
* growth conjuncts: E-half fuel-IH at the grown context, composed
  through `andAll_elim`.
* jump conjuncts `(A@(b-1)(A_F) ⇢ E@b(B::Γ))`: impR, fire the
  source's jump conjunct after converting its antecedent by the
  A-half at the (b-1)-pair (IN CONTEXT: the impR antecedent plus the
  source E-value as ambient), then lift the consequent by the E-half
  fuel-IH at the grown context.
* γ conjuncts (the former barrier): impR introduces the target's box
  `◯(E@(b-1) ⇢ A@(b-1)(◯A_F))`; its guard EXACTLY matches the
  in-context source value `E@(b-1)`, so `box_guard_collapse` opens
  it; `laxL` on the result puts `A@(b-1)(◯A_F)` in context; `laxR` +
  impR rebuild the source's γ-antecedent, closing with the A-half at
  the (b-1)-pair.  No regress: ambient is re-imported at the
  crossing.

A-half `[E@b, A@b(Γ,C)] ⊢ A@(b-1)(Γ,C)` — orAll-elim on the source
value with E-ambient:
* goal decomposition: A-half fuel-IH (ambient stepped down by
  `itp_fuel_mono` + `itp_budget_mono`).
* growth disjuncts: impR-texture — introduce the target's guard,
  derive the source's by the E-half at the grown context, fire, then
  A-half at the grown context with the just-derived grown-E as
  ambient.
* SECOND components of jump/γ disjuncts (`A@b(B::Γ, C)`): unlock the
  grown ambient by firing the ambient E-value's own jump conjunct
  with the in-context first component (the adequacy case-map's
  `hfire` pattern), then A-half at the grown context.
* FIRST components of jump/γ disjuncts: the b-descent — THE CASCADE.
  Each jump/γ-first-component map is an A-half instance at the
  (b-1)-pair, whose own jump cases descend again: the descent chain
  carries jump goals (≤ kcap distinct) WITH their values in context
  (andL keeps them).  At a goal repeat: `itp_budget_mono_le` lifts
  the deep in-context value into the spliced (higher-budget) target
  slot.  Pigeonhole bounds the descent by kcap+1, which is what the
  threshold pays for; below it, jump-free target values make the map
  genuinely false.
* trunc: collapse via guard-match, laxL, orAll-elim, reuse the
  per-disjunct bundle (as in itp_sound's trunc case).

Lean plan: outer fuel induction (mutual halves as the ∧); the A-half
jump-first-components via an inner descent lemma carrying
`seen : List (PLLFormula × Nat)` (goal, budget-at-first-visit) with
their values as explicit context hypotheses; repeats close by
mono-splice, fresh states recurse with the budget slack decreasing;
`kcap S < b` supplies the room.

MECHANISATION NOTE (2026-07-11, this file): the compiler adjudicated
the header's claim that the E-half closes at the fuel level.  It does
NOT for the three budget-gated shapes: their antecedent conversions
are (b-1)-pair A-half instances, i.e. instances of the SAME descent
interface the A-half first components need — with the threshold
hypothesis one below what the fuel induction can supply.  So the
cascade interface (the three sorried lemmas below) is consumed from
BOTH halves; everything else closes exactly as the header describes.
-/

/-! ### Sequent-level glue

Cut/weakening plumbing that lets a two-hypothesis lemma be consumed
inside any context that derives both hypotheses; the fire patterns
for context implications and boxed guards. -/

/-- List-level subset weakening (through the set calculus). -/
private theorem weaken_sub {Γ Γ' : List PLLFormula} {C : PLLFormula}
    (h : ∀ ψ ∈ Γ, ψ ∈ Γ') (d : G4c Γ C) : G4c Γ' C := by
  rw [G4c.iff_set] at d ⊢
  refine d.weaken_subset ?_
  intro y hy
  rw [List.mem_toFinset] at hy ⊢
  exact h y hy

/-- Consume a one-hypothesis lemma under a deriving context. -/
private theorem consume₁ {Δ : List PLLFormula} {X Z : PLLFormula}
    (dX : G4c Δ X) (L : G4c [X] Z) : G4c Δ Z :=
  G4c.cut dX (weaken_sub (by
    intro ψ hψ
    rcases List.mem_singleton.mp hψ with rfl
    exact .head _) L)

/-- Consume a two-hypothesis lemma under a deriving context. -/
private theorem consume₂ {Δ : List PLLFormula} {X Y Z : PLLFormula}
    (dX : G4c Δ X) (dY : G4c Δ Y) (L : G4c [X, Y] Z) : G4c Δ Z :=
  G4c.cut dX (G4c.cut (dY.weaken X) (weaken_sub (by
    intro ψ hψ
    rcases List.mem_cons.mp hψ with rfl | hψ
    · exact .tail _ (.head _)
    · rcases List.mem_singleton.mp hψ with rfl
      exact .head _) L))

/-- Fire a derivable implication with a derivable antecedent. -/
private theorem fire {Δ : List PLLFormula} {X Y : PLLFormula}
    (dImp : G4c Δ (X.ifThen Y)) (dX : G4c Δ X) : G4c Δ Y :=
  consume₂ dX dImp (G4c.mp X Y [])

/-- Project a conjunct out of a derivable bundle. -/
private theorem projE {Δ l : List PLLFormula} {φ : PLLFormula}
    (dE : G4c Δ (andAll l)) (hmem : φ ∈ l) : G4c Δ φ :=
  G4c.cut dE (G4c.andAll_elim hmem (G4c.identity_mem (.head _)))

/-- Open a derivable boxed guarded implication against a ◯-goal:
fire the guard (re-derived under the opening) and continue with the
value in context — the generalized-context `box_guard_collapse`. -/
private theorem box_fire {Δ : List PLLFormula} {X Y W : PLLFormula}
    (dBox : G4c Δ ((X.ifThen Y).somehow)) (dX : G4c Δ X)
    (k : G4c (Y :: Δ) W.somehow) : G4c Δ W.somehow := by
  refine G4c.cut dBox (G4c.laxL (.head _) ?_)
  have dY : G4c ((X.ifThen Y) :: (X.ifThen Y).somehow :: Δ) Y :=
    fire (G4c.identity_mem (.head _))
      (weaken_sub (fun ψ hψ => .tail _ (.tail _ hψ)) dX)
  refine G4c.cut dY (weaken_sub ?_ k)
  intro ψ hψ
  rcases List.mem_cons.mp hψ with rfl | hψ
  · exact .head _
  · exact .tail _ (.tail _ (.tail _ hψ))

/-- From the packaged ambient at `(fuel+1, b)` in context, the
fuel-level E-value at any budget `b' ≤ b`. -/
private theorem amb_step {p : String} {S : Finset PLLFormula}
    {fuel b b' : Nat} {Γ Δ : List PLLFormula}
    (hmem : itpE p S (fuel + 1) b Γ ∈ Δ) (hle : b' ≤ b) :
    G4c Δ (itpE p S fuel b' Γ) :=
  consume₁ (consume₁ (G4c.identity_mem hmem) ((itp_fuel_mono p S fuel).1 b Γ))
    ((itp_budget_mono_le p S hle fuel).1 Γ)

/-- Packaged ambient at a lower budget, fuel intact. -/
private theorem amb_pack_step {p : String} {S : Finset PLLFormula}
    {fuel b b' : Nat} {Γ Δ : List PLLFormula}
    (hmem : itpE p S (fuel + 1) b Γ ∈ Δ) (hle : b' ≤ b) :
    G4c Δ (itpE p S (fuel + 1) b' Γ) :=
  consume₁ (G4c.identity_mem hmem) ((itp_budget_mono_le p S hle (fuel + 1)).1 Γ)

/-- Shift a derivable E-value onto a set-equal cons context. -/
private theorem amb_congr {p : String} {S : Finset PLLFormula} {fuel b : Nat}
    {Γ Δ : List PLLFormula} {X : PLLFormula}
    (d : G4c Δ (itpE p S fuel b Γ)) (hX : X ∈ Γ) :
    G4c Δ (itpE p S fuel b (X :: Γ)) :=
  consume₁ d ((itp_congr p S fuel).1 b Γ (X :: Γ) (by
    rw [List.toFinset_cons]
    exact (Finset.insert_eq_self.mpr (List.mem_toFinset.mpr hX)).symm))

/-! ### The cascade interface

The b-descent proper, one sorried lemma per gated clause shape.  Each
captures exactly the goal state at its call sites (both halves land on
the same normal form): the source's first-component value one budget
below the band, the packaged theorem-grade ambient at that same
budget, and the target slot one further down.  The membership facts
are the clause guards in force at every site — the descent argument
(seen-list pigeonhole + `itp_budget_mono_le` splice) needs them to
know its jump goals range over the space. -/

/-- Cascade, `impLImp`-at-present-piece shape: the guarded-implication
first component descends one budget. -/
private theorem cascade_impLImp (p : String) (S : Finset PLLFormula)
    (fuel c : Nat) (hb : kcap S < c + 2) (Γ : List PLLFormula)
    (A₁ B₁ D : PLLFormula)
    (hFΓ : (A₁.ifThen B₁).ifThen D ∈ Γ) (hDΓ : D ∉ Γ) (hDS : D ∈ S)
    (hBD : B₁.ifThen D ∈ Γ) (hABD : (A₁.ifThen B₁).ifThen D ∈ S) :
    G4c [itpA p S fuel (c + 1) Γ (A₁.ifThen B₁),
         itpE p S (fuel + 1) (c + 1) Γ]
      (itpA p S fuel c Γ (A₁.ifThen B₁)) := by
  sorry

/-- Cascade, `impLLax`-jump shape: the bare A-value first component
descends one budget. -/
private theorem cascade_jump (p : String) (S : Finset PLLFormula)
    (fuel c : Nat) (hb : kcap S < c + 2) (Γ : List PLLFormula)
    (A B : PLLFormula)
    (hFΓ : A.somehow.ifThen B ∈ Γ) (hBΓ : B ∉ Γ) (hBS : B ∈ S)
    (hAS : A.somehow.ifThen B ∈ S) :
    G4c [itpA p S fuel (c + 1) Γ A, itpE p S (fuel + 1) (c + 1) Γ]
      (itpA p S fuel c Γ A) := by
  sorry

/-- Cascade, `impLLax`-γ-head shape: the ◯-goal A-value inside the
boxed guard descends one budget (the landing after the laxL/laxR
re-crossing of `cascade_gamma_box`). -/
private theorem cascade_gamma (p : String) (S : Finset PLLFormula)
    (fuel c : Nat) (hb : kcap S < c + 2) (Γ : List PLLFormula)
    (A B : PLLFormula)
    (hFΓ : A.somehow.ifThen B ∈ Γ) (hBΓ : B ∉ Γ) (hBS : B ∈ S)
    (hAS : A.somehow.ifThen B ∈ S) :
    G4c [itpA p S fuel (c + 1) Γ A.somehow, itpE p S (fuel + 1) (c + 1) Γ]
      (itpA p S fuel c Γ A.somehow) := by
  sorry

/-! ### Derived cascade consumers

The two composite shapes both halves actually land on, reduced to the
interface above.  `Δ`-parametric so the same consumer serves the
E-half (ambient = the source value itself) and the A-half (ambient
stepped down from the `b`-level hypothesis by `itp_budget_mono_le`). -/

/-- Antecedent conversion for the gated `impLImp` clause: from the
target-side guard implication and the packaged ambient, the
source-side guard implication one budget down. -/
private theorem cascade_impLImp_ant (p : String) (S : Finset PLLFormula)
    (fuel c : Nat) (hb : kcap S < c + 2) (Γ : List PLLFormula)
    (A₁ B₁ D : PLLFormula)
    (hFΓ : (A₁.ifThen B₁).ifThen D ∈ Γ) (hDΓ : D ∉ Γ) (hDS : D ∈ S)
    (hBD : B₁.ifThen D ∈ Γ) (hABD : (A₁.ifThen B₁).ifThen D ∈ S)
    {Δ : List PLLFormula}
    (dJ : G4c Δ ((itpE p S fuel (c + 1) Γ).ifThen
      (itpA p S fuel (c + 1) Γ (A₁.ifThen B₁))))
    (dE : G4c Δ (itpE p S (fuel + 1) (c + 1) Γ)) :
    G4c Δ ((itpE p S fuel c Γ).ifThen (itpA p S fuel c Γ (A₁.ifThen B₁))) := by
  refine G4c.impR ?_
  have dE' : G4c (itpE p S fuel c Γ :: Δ) (itpE p S (fuel + 1) (c + 1) Γ) :=
    dE.weaken _
  have dA1 : G4c (itpE p S fuel c Γ :: Δ)
      (itpA p S fuel (c + 1) Γ (A₁.ifThen B₁)) :=
    fire (dJ.weaken _) (consume₁ dE' ((itp_fuel_mono p S fuel).1 (c + 1) Γ))
  exact consume₂ dA1 dE'
    (cascade_impLImp p S fuel c hb Γ A₁ B₁ D hFΓ hDΓ hDS hBD hABD)

/-- Boxed-guard descent for the gated `impLLax` γ-head component:
laxL opens the target-side box, the guard fires against the ambient,
laxR/impR re-cross, and the landing is the γ cascade. -/
private theorem cascade_gamma_box (p : String) (S : Finset PLLFormula)
    (fuel c : Nat) (hb : kcap S < c + 2) (Γ : List PLLFormula)
    (A B : PLLFormula)
    (hFΓ : A.somehow.ifThen B ∈ Γ) (hBΓ : B ∉ Γ) (hBS : B ∈ S)
    (hAS : A.somehow.ifThen B ∈ S) {Δ : List PLLFormula}
    (dG : G4c Δ (((itpE p S fuel (c + 1) Γ).ifThen
      (itpA p S fuel (c + 1) Γ A.somehow)).somehow))
    (dE : G4c Δ (itpE p S (fuel + 1) (c + 1) Γ)) :
    G4c Δ (((itpE p S fuel c Γ).ifThen
      (itpA p S fuel c Γ A.somehow)).somehow) := by
  refine box_fire dG (consume₁ dE ((itp_fuel_mono p S fuel).1 (c + 1) Γ)) ?_
  refine G4c.laxR (G4c.impR ?_)
  refine consume₂ (G4c.identity_mem (.tail _ (.head _)))
    (weaken_sub (fun ψ hψ => .tail _ (.tail _ hψ)) dE)
    (cascade_gamma p S fuel c hb Γ A B hFΓ hBΓ hBS hAS)

/-! ### The ambient full-table mapping

`itpAfull_map` with the ambient E-value carried in the sequents: the
truncation disjunct maps by guard-fire against the ambient feed and
re-crossing, then reuses the per-disjunct bundle — the list-level
counterpart of `itp_sound`'s trunc case. -/

private theorem itpAfull_map_amb {p : String} {S : Finset PLLFormula}
    {f b₁ b₂ : Nat} {Γ : List PLLFormula} {C : PLLFormula} {Eamb : PLLFormula}
    (hoth : ∀ φ ∈ itpAoth p S f b₁ Γ C,
        ∃ ψ ∈ itpAoth p S f b₂ Γ C, G4c [φ, Eamb] ψ)
    (htr : ∀ b₁', b₁ = b₁' + 1 → ∃ b₂', b₂ = b₂' + 1 ∧
        G4c [Eamb] (itpE p S f b₁' Γ)) :
    G4c [Eamb, orAll (itpAfull p S f b₁ Γ C)]
        (orAll (itpAfull p S f b₂ Γ C)) := by
  refine G4c.perm ?_ (List.Perm.swap _ _ _)
  refine G4c.orAll_elim ?_
  intro φ hφ
  cases C with
  | somehow D =>
      simp only [itpAfull] at hφ ⊢
      rcases List.mem_append.mp hφ with hφ | hφ
      · obtain ⟨ψ, hψ, hd⟩ := hoth φ hφ
        exact G4c.orAll_intro (List.mem_append.mpr (Or.inl hψ)) hd
      · by_cases h1 : (itpAoth p S f b₁ Γ (D.somehow)).isEmpty = true
        · rw [if_pos h1] at hφ; cases hφ
        · rw [if_neg h1] at hφ
          cases b₁ with
          | zero => cases hφ
          | succ b₁' =>
              rcases List.mem_singleton.mp hφ with rfl
              obtain ⟨b₂', rfl, hfeed⟩ := htr b₁' rfl
              have h2 : ¬ (itpAoth p S f (b₂' + 1) Γ (D.somehow)).isEmpty
                  = true := by
                intro h2
                have h2' : itpAoth p S f (b₂' + 1) Γ (D.somehow) = [] := by
                  simpa using h2
                cases hl : itpAoth p S f (b₁' + 1) Γ (D.somehow) with
                | nil => rw [hl] at h1; simp at h1
                | cons a t =>
                    obtain ⟨ψ, hψ, -⟩ := hoth a (by rw [hl]; exact .head _)
                    rw [h2'] at hψ; cases hψ
              refine G4c.orAll_intro (φ := ((itpE p S f b₂' Γ).ifThen
                  (orAll (itpAoth p S f (b₂' + 1) Γ (D.somehow)))).somehow)
                (List.mem_append.mpr (Or.inr ?_)) ?_
              · rw [if_neg h2]
                exact .head _
              · refine box_fire (W := (itpE p S f b₂' Γ).ifThen
                    (orAll (itpAoth p S f (b₂' + 1) Γ (D.somehow))))
                  (G4c.identity_mem (.head _))
                  (weaken_sub (fun ψ hψ => .tail _ hψ) hfeed) ?_
                refine G4c.laxR (G4c.impR ?_)
                refine G4c.perm (Γ := orAll (itpAoth p S f (b₁' + 1) Γ
                    (D.somehow)) :: itpE p S f b₂' Γ ::
                    [((itpE p S f b₁' Γ).ifThen (orAll (itpAoth p S f
                      (b₁' + 1) Γ (D.somehow)))).somehow, Eamb])
                  (G4c.orAll_elim ?_) (List.Perm.swap _ _ _)
                intro χ hχ
                obtain ⟨ψ, hψ, hd⟩ := hoth χ hχ
                refine G4c.orAll_intro hψ (weaken_sub ?_ hd)
                intro ξ hξ
                rcases List.mem_cons.mp hξ with rfl | hξ
                · exact .head _
                · rcases List.mem_singleton.mp hξ with rfl
                  exact .tail _ (.tail _ (.tail _ (.head _)))
  | prop q =>
      simp only [itpAfull] at hφ ⊢
      obtain ⟨ψ, hψ, hd⟩ := hoth φ hφ
      exact G4c.orAll_intro hψ hd
  | falsePLL =>
      simp only [itpAfull] at hφ ⊢
      obtain ⟨ψ, hψ, hd⟩ := hoth φ hφ
      exact G4c.orAll_intro hψ hd
  | and C₁ C₂ =>
      simp only [itpAfull] at hφ ⊢
      obtain ⟨ψ, hψ, hd⟩ := hoth φ hφ
      exact G4c.orAll_intro hψ hd
  | or C₁ C₂ =>
      simp only [itpAfull] at hφ ⊢
      obtain ⟨ψ, hψ, hd⟩ := hoth φ hφ
      exact G4c.orAll_intro hψ hd
  | ifThen C₁ C₂ =>
      simp only [itpAfull] at hφ ⊢
      obtain ⟨ψ, hψ, hd⟩ := hoth φ hφ
      exact G4c.orAll_intro hψ hd

/-! ### The stabilization core, successor form

`b = c + 2` throughout, so every budget index in scope is a literal
successor and the gated clause tables reduce definitionally. -/

set_option maxHeartbeats 4000000 in
private theorem itp_stab_aux (p : String) (S : Finset PLLFormula) :
    ∀ (fuel : Nat), ∀ (c : Nat), kcap S < c + 2 →
    (∀ Γ, G4c [itpE p S fuel (c + 1) Γ] (itpE p S fuel (c + 2) Γ)) ∧
    (∀ Γ C, G4c [itpE p S fuel (c + 2) Γ, itpA p S fuel (c + 2) Γ C]
      (itpA p S fuel (c + 1) Γ C)) := by
  intro fuel
  induction fuel with
  | zero =>
      intro c hb
      constructor
      · intro Γ
        simp only [itpE]
        exact G4c.truePLL_intro _
      · intro Γ C
        simp only [itpA]
        exact G4c.botL (.tail _ (.head _))
  | succ fuel ih =>
      intro c hb
      have ihE : ∀ Γ', G4c [itpE p S fuel (c + 1) Γ']
          (itpE p S fuel (c + 2) Γ') := fun Γ' => (ih c hb).1 Γ'
      have ihA : ∀ Γ' C', G4c [itpE p S fuel (c + 2) Γ',
          itpA p S fuel (c + 2) Γ' C'] (itpA p S fuel (c + 1) Γ' C') :=
        fun Γ' C' => (ih c hb).2 Γ' C'
      constructor
      · -- E-half: [E@(fuel+1)@(c+1)] ⊢ E@(fuel+1)@(c+2)
        intro Γ
        rw [itpE_succ p S fuel (c + 2) Γ]
        refine G4c.andAll_intro ?_
        intro φ hφ
        -- per-conjunct goal: G4c [itpE p S (fuel+1) (c+1) Γ] φ
        simp only [itpEcls] at hφ
        rcases List.mem_append.mp hφ with hφ | hφ
        · rcases List.mem_append.mp hφ with hφ | hφ
          · -- the ⊥ clause: project the source's
            split at hφ
            next hbot =>
              rcases List.mem_singleton.mp hφ with rfl
              refine projE (l := itpEcls p S fuel (c + 1) Γ)
                (G4c.identity_mem (.head _)) ?_
              simp only [itpEcls]
              exact List.mem_append.mpr (Or.inl (List.mem_append.mpr
                (Or.inl (by rw [if_pos hbot]; exact .head _))))
            next => cases hφ
          · -- the atom clauses: project the source's
            obtain ⟨F, hFΓ, heq⟩ := List.mem_filterMap.mp hφ
            cases F with
            | prop q =>
                simp only at heq
                split at heq
                next => cases heq
                next hq =>
                  injection heq with heq'
                  subst heq'
                  refine projE (l := itpEcls p S fuel (c + 1) Γ)
                    (G4c.identity_mem (.head _)) ?_
                  simp only [itpEcls]
                  refine List.mem_append.mpr (Or.inl (List.mem_append.mpr
                    (Or.inr (List.mem_filterMap.mpr ⟨prop q, hFΓ, ?_⟩))))
                  simp only
                  rw [if_neg hq]
            | falsePLL => cases heq
            | and _ _ => cases heq
            | or _ _ => cases heq
            | ifThen _ _ => cases heq
            | somehow _ => cases heq
        · -- the rule clauses
          obtain ⟨F, hFΓ, hin⟩ := List.mem_flatMap.mp hφ
          cases F with
          | prop _ => cases hin
          | falsePLL => cases hin
          | and A B =>
              simp only at hin
              split at hin
              next => cases hin
              next h1 =>
                split at hin
                next h2 =>
                  rcases List.mem_singleton.mp hin with rfl
                  refine consume₁ (projE (l := itpEcls p S fuel (c + 1) Γ)
                    (G4c.identity_mem (.head _)) ?_) (ihE (A :: B :: Γ))
                  simp only [itpEcls]
                  refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                    ⟨A.and B, hFΓ, ?_⟩))
                  simp only
                  rw [if_neg h1, if_pos h2]
                  exact .head _
                next => cases hin
          | or A B =>
              simp only at hin
              split at hin
              next => cases hin
              next h1 =>
                split at hin
                next h2 =>
                  rcases List.mem_singleton.mp hin with rfl
                  refine consume₁ (projE (l := itpEcls p S fuel (c + 1) Γ)
                    (G4c.identity_mem (.head _)) ?_)
                    (or_mono (ihE (A :: Γ)) (ihE (B :: Γ)))
                  simp only [itpEcls]
                  refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                    ⟨A.or B, hFΓ, ?_⟩))
                  simp only
                  rw [if_neg h1, if_pos h2]
                  exact .head _
                next => cases hin
          | somehow χ =>
              simp only at hin
              split at hin
              next => cases hin
              next hg =>
                rcases List.mem_singleton.mp hin with rfl
                refine consume₁ (projE (l := itpEcls p S fuel (c + 1) Γ)
                  (G4c.identity_mem (.head _)) ?_) (box_mono (ihE (χ :: Γ)))
                simp only [itpEcls]
                refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                  ⟨χ.somehow, hFΓ, ?_⟩))
                simp only
                rw [if_neg hg]
                exact .head _
          | ifThen A' B =>
              cases A' with
              | prop q =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next hBΓ =>
                    split at hin
                    next hBS =>
                      split at hin
                      next hq =>
                        rcases List.mem_singleton.mp hin with rfl
                        refine consume₁ (projE
                          (l := itpEcls p S fuel (c + 1) Γ)
                          (G4c.identity_mem (.head _)) ?_) (ihE (B :: Γ))
                        simp only [itpEcls]
                        refine List.mem_append.mpr (Or.inr
                          (List.mem_flatMap.mpr ⟨(prop q).ifThen B, hFΓ, ?_⟩))
                        simp only
                        rw [if_neg hBΓ, if_pos hBS, if_pos hq]
                        exact .head _
                      next hq =>
                        split at hin
                        next => cases hin
                        next hqp =>
                          rcases List.mem_singleton.mp hin with rfl
                          refine consume₁ (projE
                            (l := itpEcls p S fuel (c + 1) Γ)
                            (G4c.identity_mem (.head _)) ?_)
                            (imp_mono (G4c.init (.head _)) (ihE (B :: Γ)))
                          simp only [itpEcls]
                          refine List.mem_append.mpr (Or.inr
                            (List.mem_flatMap.mpr
                              ⟨(prop q).ifThen B, hFΓ, ?_⟩))
                          simp only
                          rw [if_neg hBΓ, if_pos hBS, if_neg hq, if_neg hqp]
                          exact .head _
                    next => cases hin
              | falsePLL => cases hin
              | and A₁ B₁ =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next h1 =>
                    split at hin
                    next h2 =>
                      rcases List.mem_singleton.mp hin with rfl
                      refine consume₁ (projE
                        (l := itpEcls p S fuel (c + 1) Γ)
                        (G4c.identity_mem (.head _)) ?_)
                        (ihE (A₁.ifThen (B₁.ifThen B) :: Γ))
                      simp only [itpEcls]
                      refine List.mem_append.mpr (Or.inr
                        (List.mem_flatMap.mpr ⟨(A₁.and B₁).ifThen B, hFΓ, ?_⟩))
                      simp only
                      rw [if_neg h1, if_pos h2]
                      exact .head _
                    next => cases hin
              | or A₁ B₁ =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next h1 =>
                    split at hin
                    next h2 =>
                      rcases List.mem_singleton.mp hin with rfl
                      refine consume₁ (projE
                        (l := itpEcls p S fuel (c + 1) Γ)
                        (G4c.identity_mem (.head _)) ?_)
                        (ihE (A₁.ifThen B :: B₁.ifThen B :: Γ))
                      simp only [itpEcls]
                      refine List.mem_append.mpr (Or.inr
                        (List.mem_flatMap.mpr ⟨(A₁.or B₁).ifThen B, hFΓ, ?_⟩))
                      simp only
                      rw [if_neg h1, if_pos h2]
                      exact .head _
                    next => cases hin
              | ifThen A₁ B₁ =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next hDΓ =>
                    split at hin
                    next hDS =>
                      split at hin
                      next hBD =>
                        split at hin
                        next hABD =>
                          -- gated at (c+2): the jump-imp conjunct
                          rcases List.mem_singleton.mp hin with rfl
                          refine G4c.impR ?_
                          -- [J@(c+1), E_src] ⊢ E@fuel@(c+2)(B::Γ)
                          refine consume₁ (fire (projE
                              (l := itpEcls p S fuel (c + 1) Γ)
                              (G4c.identity_mem (.tail _ (.head _))) ?_)
                              (cascade_impLImp_ant p S fuel c hb Γ A₁ B₁ B
                                hFΓ hDΓ hDS hBD hABD
                                (G4c.identity_mem (.head _))
                                (G4c.identity_mem (.tail _ (.head _)))))
                            (ihE (B :: Γ))
                          simp only [itpEcls]
                          refine List.mem_append.mpr (Or.inr
                            (List.mem_flatMap.mpr
                              ⟨(A₁.ifThen B₁).ifThen B, hFΓ, ?_⟩))
                          simp only
                          rw [if_neg hDΓ, if_pos hDS, if_pos hBD, if_pos hABD]
                          exact .head _
                        next => cases hin
                      next hBD =>
                        split at hin
                        next hBDS =>
                          -- fresh piece: impR-texture, no cascade
                          rcases List.mem_singleton.mp hin with rfl
                          refine G4c.impR ?_
                          -- [J'@(c+2), E_src] ⊢ E@fuel@(c+2)(B::Γ)
                          refine consume₁ (fire
                            (X := (itpE p S fuel (c + 1)
                                (B₁.ifThen B :: Γ)).ifThen
                              (itpA p S fuel (c + 1) (B₁.ifThen B :: Γ)
                                (A₁.ifThen B₁)))
                            (projE (l := itpEcls p S fuel (c + 1) Γ)
                              (G4c.identity_mem (.tail _ (.head _))) ?_) ?_)
                            (ihE (B :: Γ))
                          · simp only [itpEcls]
                            refine List.mem_append.mpr (Or.inr
                              (List.mem_flatMap.mpr
                                ⟨(A₁.ifThen B₁).ifThen B, hFΓ, ?_⟩))
                            simp only
                            rw [if_neg hDΓ, if_pos hDS, if_neg hBD,
                              if_pos hBDS]
                            exact .head _
                          · -- the source guard-implication, by impR-texture
                            refine G4c.impR ?_
                            refine consume₂ (consume₁
                                (G4c.identity_mem (.head _))
                                (ihE (B₁.ifThen B :: Γ))) ?_
                              (ihA (B₁.ifThen B :: Γ) (A₁.ifThen B₁))
                            exact fire (G4c.identity_mem (.tail _ (.head _)))
                              (consume₁ (G4c.identity_mem (.head _))
                                (ihE (B₁.ifThen B :: Γ)))
                        next => cases hin
                    next => cases hin
              | somehow A₁ =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next hBΓ =>
                    split at hin
                    next hBS =>
                      rcases List.mem_append.mp hin with hin | hin
                      · split at hin
                        next hAS =>
                          rcases List.mem_cons.mp hin with rfl | hin'
                          · -- the jump conjunct (gated): cascade on the
                            -- introduced antecedent
                            refine G4c.impR ?_
                            -- [A@(c+1)Γ(A₁), E_src] ⊢ E@fuel@(c+2)(B::Γ)
                            refine consume₁ (fire (projE
                                (l := itpEcls p S fuel (c + 1) Γ)
                                (G4c.identity_mem (.tail _ (.head _))) ?_)
                                (consume₂ (G4c.identity_mem (.head _))
                                  (G4c.identity_mem (.tail _ (.head _)))
                                  (cascade_jump p S fuel c hb Γ A₁ B
                                    hFΓ hBΓ hBS hAS)))
                              (ihE (B :: Γ))
                            simp only [itpEcls]
                            refine List.mem_append.mpr (Or.inr
                              (List.mem_flatMap.mpr
                                ⟨A₁.somehow.ifThen B, hFΓ, ?_⟩))
                            simp only
                            rw [if_neg hBΓ, if_pos hBS, if_pos hAS]
                            exact List.mem_append.mpr (Or.inl (.head _))
                          · -- the γ-head conjunct (gated): boxed cascade
                            rcases List.mem_singleton.mp hin' with rfl
                            refine G4c.impR ?_
                            -- [◯(E@(c+1) ⇢ A@(c+1)◯A₁), E_src] ⊢ E@(c+2)(B::Γ)
                            refine consume₁ (fire (projE
                                (l := itpEcls p S fuel (c + 1) Γ)
                                (G4c.identity_mem (.tail _ (.head _))) ?_)
                                (cascade_gamma_box p S fuel c hb Γ A₁ B
                                  hFΓ hBΓ hBS hAS
                                  (G4c.identity_mem (.head _))
                                  (G4c.identity_mem (.tail _ (.head _)))))
                              (ihE (B :: Γ))
                            simp only [itpEcls]
                            refine List.mem_append.mpr (Or.inr
                              (List.mem_flatMap.mpr
                                ⟨A₁.somehow.ifThen B, hFΓ, ?_⟩))
                            simp only
                            rw [if_neg hBΓ, if_pos hBS, if_pos hAS]
                            exact List.mem_append.mpr
                              (Or.inl (.tail _ (.head _)))
                        next => cases hin
                      · -- the γ-context conjuncts (ungated): fuel level
                        obtain ⟨X, hXΓ, heq⟩ := List.mem_filterMap.mp hin
                        cases X with
                        | somehow x =>
                            simp only at heq
                            split at heq
                            next => cases heq
                            next hg =>
                              injection heq with heq'
                              subst heq'
                              refine G4c.impR ?_
                              -- [◯(E@(c+2)(x::Γ) ⇢ A@(c+2)(x::Γ)◯A₁), E_src]
                              --   ⊢ E@fuel@(c+2)(B::Γ)
                              refine consume₁ (fire
                                (X := ((itpE p S fuel (c + 1)
                                    (x :: Γ)).ifThen
                                  (itpA p S fuel (c + 1) (x :: Γ)
                                    A₁.somehow)).somehow)
                                (projE (l := itpEcls p S fuel (c + 1) Γ)
                                  (G4c.identity_mem (.tail _ (.head _))) ?_)
                                  ?_)
                                (ihE (B :: Γ))
                              · simp only [itpEcls]
                                refine List.mem_append.mpr (Or.inr
                                  (List.mem_flatMap.mpr
                                    ⟨A₁.somehow.ifThen B, hFΓ, ?_⟩))
                                simp only
                                rw [if_neg hBΓ, if_pos hBS]
                                refine List.mem_append.mpr (Or.inr
                                  (List.mem_filterMap.mpr ⟨x.somehow, hXΓ, ?_⟩))
                                simp only
                                rw [if_neg hg]
                              · -- derive the source's γ-antecedent: open the
                                -- source's ◯E-growth conjunct, ascend, cross
                                refine G4c.cut
                                  (A := (itpE p S fuel (c + 1) (x :: Γ)).somehow)
                                  (projE (l := itpEcls p S fuel (c + 1) Γ)
                                    (G4c.identity_mem (.tail _ (.head _))) ?_) ?_
                                · simp only [itpEcls]
                                  refine List.mem_append.mpr (Or.inr
                                    (List.mem_flatMap.mpr
                                      ⟨x.somehow, hXΓ, ?_⟩))
                                  simp only
                                  rw [if_neg hg]
                                  exact .head _
                                · refine G4c.laxL (.head _) ?_
                                  refine box_fire
                                    (X := itpE p S fuel (c + 2) (x :: Γ))
                                    (Y := itpA p S fuel (c + 2) (x :: Γ)
                                      A₁.somehow)
                                    (G4c.identity_mem
                                      (.tail _ (.tail _ (.head _))))
                                    (consume₁ (G4c.identity_mem (.head _))
                                      (ihE (x :: Γ))) ?_
                                  refine G4c.laxR (G4c.impR ?_)
                                  exact consume₂ (consume₁
                                      (G4c.identity_mem (.head _))
                                      (ihE (x :: Γ)))
                                    (G4c.identity_mem (.tail _ (.head _)))
                                    (ihA (x :: Γ) A₁.somehow)
                        | prop _ => cases heq
                        | falsePLL => cases heq
                        | and _ _ => cases heq
                        | or _ _ => cases heq
                        | ifThen _ _ => cases heq
                    next => cases hin
      · -- A-half: [E@(fuel+1)@(c+2), A@(fuel+1)@(c+2)] ⊢ A@(fuel+1)@(c+1)
        intro Γ C
        rw [itpA_succ p S fuel (c + 2) Γ C, itpA_succ p S fuel (c + 1) Γ C]
        -- the goal-directed disjuncts, mapped under the ambient
        have hGOAL : ∀ φ ∈ itpAgoal p S fuel (c + 2) Γ C,
            ∃ ψ ∈ itpAgoal p S fuel (c + 1) Γ C,
              G4c [φ, itpE p S (fuel + 1) (c + 2) Γ] ψ := by
          intro φ hφ
          cases C with
          | prop q =>
              simp only [itpAgoal] at hφ ⊢
              split at hφ
              next => cases hφ
              next hq =>
                rcases List.mem_singleton.mp hφ with rfl
                refine ⟨prop q, ?_, G4c.init (.head _)⟩
                rw [if_neg hq]
                exact .head _
          | falsePLL =>
              simp only [itpAgoal] at hφ
              cases hφ
          | and C₁ C₂ =>
              simp only [itpAgoal] at hφ ⊢
              rcases List.mem_singleton.mp hφ with rfl
              refine ⟨(itpA p S fuel (c + 1) Γ C₁).and
                (itpA p S fuel (c + 1) Γ C₂), .head _, ?_⟩
              refine G4c.andL (List.Perm.refl _) (G4c.andR ?_ ?_)
              · exact consume₂ (amb_step (.tail _ (.tail _ (.head _)))
                  (Nat.le_refl _)) (G4c.identity_mem (.head _)) (ihA Γ C₁)
              · exact consume₂ (amb_step (.tail _ (.tail _ (.head _)))
                  (Nat.le_refl _)) (G4c.identity_mem (.tail _ (.head _)))
                  (ihA Γ C₂)
          | or C₁ C₂ =>
              simp only [itpAgoal] at hφ ⊢
              rcases List.mem_cons.mp hφ with rfl | hφ'
              · refine ⟨itpA p S fuel (c + 1) Γ C₁, .head _, ?_⟩
                exact consume₂ (amb_step (.tail _ (.head _)) (Nat.le_refl _))
                  (G4c.identity_mem (.head _)) (ihA Γ C₁)
              · rcases List.mem_singleton.mp hφ' with rfl
                refine ⟨itpA p S fuel (c + 1) Γ C₂, .tail _ (.head _), ?_⟩
                exact consume₂ (amb_step (.tail _ (.head _)) (Nat.le_refl _))
                  (G4c.identity_mem (.head _)) (ihA Γ C₂)
          | ifThen C₁ C₂ =>
              simp only [itpAgoal] at hφ ⊢
              split at hφ
              next hpres =>
                -- present antecedent (gated): guard restep by set-congruence
                rcases List.mem_singleton.mp hφ with rfl
                refine ⟨(itpE p S fuel c (C₁ :: Γ)).ifThen
                  (itpA p S fuel (c + 1) (C₁ :: Γ) C₂), ?_, ?_⟩
                · rw [if_pos hpres]
                  exact .head _
                · refine G4c.impR ?_
                  -- [E@c(C₁::Γ), φ, Eamb]
                  refine consume₂ (amb_congr (amb_step
                      (.tail _ (.tail _ (.head _))) (Nat.le_refl _)) hpres) ?_
                    (ihA (C₁ :: Γ) C₂)
                  refine fire (G4c.identity_mem (.tail _ (.head _))) ?_
                  exact consume₁ (amb_congr (amb_step
                      (.tail _ (.tail _ (.head _))) (Nat.le_refl _)) hpres)
                    ((itp_budget_mono p S fuel).1 (c + 1) (C₁ :: Γ))
              next hpres =>
                -- fresh antecedent: impR-texture on the introduced guard
                rcases List.mem_singleton.mp hφ with rfl
                refine ⟨(itpE p S fuel (c + 1) (C₁ :: Γ)).ifThen
                  (itpA p S fuel (c + 1) (C₁ :: Γ) C₂), ?_, ?_⟩
                · rw [if_neg hpres]
                  exact .head _
                · refine G4c.impR ?_
                  -- [E@(c+1)(C₁::Γ), φ, Eamb]
                  refine consume₂ (consume₁ (G4c.identity_mem (.head _))
                      (ihE (C₁ :: Γ))) ?_ (ihA (C₁ :: Γ) C₂)
                  exact fire (G4c.identity_mem (.tail _ (.head _)))
                    (consume₁ (G4c.identity_mem (.head _)) (ihE (C₁ :: Γ)))
          | somehow D =>
              simp only [itpAgoal] at hφ ⊢
              rcases List.mem_singleton.mp hφ with rfl
              refine ⟨((itpE p S fuel c Γ).ifThen
                (itpA p S fuel (c + 1) Γ D)).somehow, .head _, ?_⟩
              refine box_fire (G4c.identity_mem (.head _))
                (amb_step (.tail _ (.head _)) (Nat.le_succ _)) ?_
              refine G4c.laxR (G4c.impR ?_)
              exact consume₂ (amb_step (.tail _ (.tail _ (.tail _ (.head _))))
                  (Nat.le_refl _))
                (G4c.identity_mem (.tail _ (.head _))) (ihA Γ D)
        -- the context-directed disjuncts, mapped under the ambient
        have hENV : ∀ φ ∈ itpAenv p S fuel (c + 2) Γ C,
            ∃ ψ ∈ itpAenv p S fuel (c + 1) Γ C,
              G4c [φ, itpE p S (fuel + 1) (c + 2) Γ] ψ := by
          intro φ hφ
          simp only [itpAenv] at hφ
          obtain ⟨F, hFΓ, hin⟩ := List.mem_flatMap.mp hφ
          cases F with
          | prop q =>
              simp only at hin
              split at hin
              next hg =>
                rcases List.mem_singleton.mp hin with rfl
                refine ⟨truePLL, ?_, G4c.truePLL_intro _⟩
                simp only [itpAenv]
                refine List.mem_flatMap.mpr ⟨prop q, hFΓ, ?_⟩
                simp only
                rw [if_pos hg]
                exact .head _
              next => cases hin
          | falsePLL => cases hin
          | and A B =>
              simp only at hin
              split at hin
              next => cases hin
              next h1 =>
                split at hin
                next h2 =>
                  rcases List.mem_singleton.mp hin with rfl
                  refine ⟨itpA p S fuel (c + 1) (A :: B :: Γ) C, ?_, ?_⟩
                  · simp only [itpAenv]
                    refine List.mem_flatMap.mpr ⟨A.and B, hFΓ, ?_⟩
                    simp only
                    rw [if_neg h1, if_pos h2]
                    exact .head _
                  · refine consume₂ (projE (l := itpEcls p S fuel (c + 2) Γ)
                      (G4c.identity_mem (.tail _ (.head _))) ?_)
                      (G4c.identity_mem (.head _)) (ihA (A :: B :: Γ) C)
                    simp only [itpEcls]
                    refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                      ⟨A.and B, hFΓ, ?_⟩))
                    simp only
                    rw [if_neg h1, if_pos h2]
                    exact .head _
                next => cases hin
          | or A B =>
              simp only at hin
              split at hin
              next => cases hin
              next h1 =>
                split at hin
                next h2 =>
                  rcases List.mem_singleton.mp hin with rfl
                  refine ⟨((itpE p S fuel (c + 1) (A :: Γ)).ifThen
                      (itpA p S fuel (c + 1) (A :: Γ) C)).and
                    ((itpE p S fuel (c + 1) (B :: Γ)).ifThen
                      (itpA p S fuel (c + 1) (B :: Γ) C)), ?_, ?_⟩
                  · simp only [itpAenv]
                    refine List.mem_flatMap.mpr ⟨A.or B, hFΓ, ?_⟩
                    simp only
                    rw [if_neg h1, if_pos h2]
                    exact .head _
                  · refine G4c.andL (List.Perm.refl _) (G4c.andR ?_ ?_)
                    · refine G4c.impR ?_
                      -- [E@(c+1)(A::Γ), φ₁, φ₂, Eamb]
                      refine consume₂ (consume₁ (G4c.identity_mem (.head _))
                          (ihE (A :: Γ))) ?_ (ihA (A :: Γ) C)
                      exact fire (G4c.identity_mem (.tail _ (.head _)))
                        (consume₁ (G4c.identity_mem (.head _)) (ihE (A :: Γ)))
                    · refine G4c.impR ?_
                      -- [E@(c+1)(B::Γ), φ₁, φ₂, Eamb]
                      refine consume₂ (consume₁ (G4c.identity_mem (.head _))
                          (ihE (B :: Γ))) ?_ (ihA (B :: Γ) C)
                      exact fire (G4c.identity_mem
                          (.tail _ (.tail _ (.head _))))
                        (consume₁ (G4c.identity_mem (.head _)) (ihE (B :: Γ)))
                next => cases hin
          | somehow χ =>
              simp only at hin
              cases C with
              | somehow D =>
                  simp only at hin
                  by_cases hg : χ ∈ Γ ∨ χ ∉ S
                  · rw [if_pos hg] at hin
                    cases hin
                  · rw [if_neg hg] at hin
                    rcases List.mem_singleton.mp hin with rfl
                    refine ⟨((itpE p S fuel (c + 1) (χ :: Γ)).ifThen
                      (itpA p S fuel (c + 1) (χ :: Γ) D.somehow)).somehow,
                      ?_, ?_⟩
                    · simp only [itpAenv]
                      refine List.mem_flatMap.mpr ⟨χ.somehow, hFΓ, ?_⟩
                      simp only
                      rw [if_neg hg]
                      exact .head _
                    · -- open the ambient's ◯E-growth conjunct, cross, land
                      refine G4c.cut
                        (A := (itpE p S fuel (c + 2) (χ :: Γ)).somehow)
                        (projE (l := itpEcls p S fuel (c + 2) Γ)
                          (G4c.identity_mem (.tail _ (.head _))) ?_) ?_
                      · simp only [itpEcls]
                        refine List.mem_append.mpr (Or.inr
                          (List.mem_flatMap.mpr ⟨χ.somehow, hFΓ, ?_⟩))
                        simp only
                        rw [if_neg hg]
                        exact .head _
                      · refine G4c.laxL (.head _) ?_
                        -- E' :: ◯E' :: [φ, Eamb]
                        refine box_fire
                          (X := itpE p S fuel (c + 2) (χ :: Γ))
                          (Y := itpA p S fuel (c + 2) (χ :: Γ) D.somehow)
                          (G4c.identity_mem (.tail _ (.tail _ (.head _))))
                          (G4c.identity_mem (.head _)) ?_
                        refine G4c.laxR (G4c.impR ?_)
                        -- E@(c+1)(χ::Γ) :: Y :: E' :: ◯E' :: [φ, Eamb]
                        exact consume₂
                          (G4c.identity_mem (.tail _ (.tail _ (.head _))))
                          (G4c.identity_mem (.tail _ (.head _)))
                          (ihA (χ :: Γ) D.somehow)
              | prop q => cases hin
              | falsePLL => cases hin
              | and C₁ C₂ => cases hin
              | or C₁ C₂ => cases hin
              | ifThen C₁ C₂ => cases hin
          | ifThen A' B =>
              cases A' with
              | prop q =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next hBΓ =>
                    split at hin
                    next hBS =>
                      split at hin
                      next hq =>
                        rcases List.mem_singleton.mp hin with rfl
                        refine ⟨itpA p S fuel (c + 1) (B :: Γ) C, ?_, ?_⟩
                        · simp only [itpAenv]
                          refine List.mem_flatMap.mpr
                            ⟨(prop q).ifThen B, hFΓ, ?_⟩
                          simp only
                          rw [if_neg hBΓ, if_pos hBS, if_pos hq]
                          exact .head _
                        · refine consume₂
                            (projE (l := itpEcls p S fuel (c + 2) Γ)
                              (G4c.identity_mem (.tail _ (.head _))) ?_)
                            (G4c.identity_mem (.head _)) (ihA (B :: Γ) C)
                          simp only [itpEcls]
                          refine List.mem_append.mpr (Or.inr
                            (List.mem_flatMap.mpr ⟨(prop q).ifThen B, hFΓ, ?_⟩))
                          simp only
                          rw [if_neg hBΓ, if_pos hBS, if_pos hq]
                          exact .head _
                      next hq =>
                        split at hin
                        next => cases hin
                        next hqp =>
                          rcases List.mem_singleton.mp hin with rfl
                          refine ⟨(prop q).and
                            (itpA p S fuel (c + 1) (B :: Γ) C), ?_, ?_⟩
                          · simp only [itpAenv]
                            refine List.mem_flatMap.mpr
                              ⟨(prop q).ifThen B, hFΓ, ?_⟩
                            simp only
                            rw [if_neg hBΓ, if_pos hBS, if_neg hq, if_neg hqp]
                            exact .head _
                          · refine G4c.andL (List.Perm.refl _)
                              (G4c.andR (G4c.init (.head _)) ?_)
                            -- [prop q, K, Eamb] ⊢ A@(c+1)(B::Γ)C
                            refine consume₂ ?_
                              (G4c.identity_mem (.tail _ (.head _)))
                              (ihA (B :: Γ) C)
                            refine fire
                              (projE (l := itpEcls p S fuel (c + 2) Γ)
                                (G4c.identity_mem
                                  (.tail _ (.tail _ (.head _)))) ?_)
                              (G4c.init (.head _))
                            simp only [itpEcls]
                            refine List.mem_append.mpr (Or.inr
                              (List.mem_flatMap.mpr
                                ⟨(prop q).ifThen B, hFΓ, ?_⟩))
                            simp only
                            rw [if_neg hBΓ, if_pos hBS, if_neg hq, if_neg hqp]
                            exact .head _
                    next => cases hin
              | falsePLL => cases hin
              | and A₁ B₁ =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next h1 =>
                    split at hin
                    next h2 =>
                      rcases List.mem_singleton.mp hin with rfl
                      refine ⟨itpA p S fuel (c + 1)
                        (A₁.ifThen (B₁.ifThen B) :: Γ) C, ?_, ?_⟩
                      · simp only [itpAenv]
                        refine List.mem_flatMap.mpr
                          ⟨(A₁.and B₁).ifThen B, hFΓ, ?_⟩
                        simp only
                        rw [if_neg h1, if_pos h2]
                        exact .head _
                      · refine consume₂
                          (projE (l := itpEcls p S fuel (c + 2) Γ)
                            (G4c.identity_mem (.tail _ (.head _))) ?_)
                          (G4c.identity_mem (.head _))
                          (ihA (A₁.ifThen (B₁.ifThen B) :: Γ) C)
                        simp only [itpEcls]
                        refine List.mem_append.mpr (Or.inr
                          (List.mem_flatMap.mpr ⟨(A₁.and B₁).ifThen B, hFΓ, ?_⟩))
                        simp only
                        rw [if_neg h1, if_pos h2]
                        exact .head _
                    next => cases hin
              | or A₁ B₁ =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next h1 =>
                    split at hin
                    next h2 =>
                      rcases List.mem_singleton.mp hin with rfl
                      refine ⟨itpA p S fuel (c + 1)
                        (A₁.ifThen B :: B₁.ifThen B :: Γ) C, ?_, ?_⟩
                      · simp only [itpAenv]
                        refine List.mem_flatMap.mpr
                          ⟨(A₁.or B₁).ifThen B, hFΓ, ?_⟩
                        simp only
                        rw [if_neg h1, if_pos h2]
                        exact .head _
                      · refine consume₂
                          (projE (l := itpEcls p S fuel (c + 2) Γ)
                            (G4c.identity_mem (.tail _ (.head _))) ?_)
                          (G4c.identity_mem (.head _))
                          (ihA (A₁.ifThen B :: B₁.ifThen B :: Γ) C)
                        simp only [itpEcls]
                        refine List.mem_append.mpr (Or.inr
                          (List.mem_flatMap.mpr ⟨(A₁.or B₁).ifThen B, hFΓ, ?_⟩))
                        simp only
                        rw [if_neg h1, if_pos h2]
                        exact .head _
                    next => cases hin
              | ifThen A₁ B₁ =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next hDΓ =>
                    split at hin
                    next hDS =>
                      split at hin
                      next hBD =>
                        split at hin
                        next hABD =>
                          -- present piece (gated): first = cascade,
                          -- second = identity-fire of the ambient's conjunct
                          rcases List.mem_singleton.mp hin with rfl
                          refine ⟨((itpE p S fuel c Γ).ifThen
                              (itpA p S fuel c Γ (A₁.ifThen B₁))).and
                            (itpA p S fuel (c + 1) (B :: Γ) C), ?_, ?_⟩
                          · simp only [itpAenv]
                            refine List.mem_flatMap.mpr
                              ⟨(A₁.ifThen B₁).ifThen B, hFΓ, ?_⟩
                            simp only
                            rw [if_neg hDΓ, if_pos hDS, if_pos hBD,
                              if_pos hABD]
                            exact .head _
                          · refine G4c.andL (List.Perm.refl _)
                              (G4c.andR ?_ ?_)
                            · -- [J, K, Eamb] ⊢ E@c ⇢ A@c(A₁⇢B₁)
                              exact cascade_impLImp_ant p S fuel c hb Γ
                                A₁ B₁ B hFΓ hDΓ hDS hBD hABD
                                (G4c.identity_mem (.head _))
                                (amb_pack_step (.tail _ (.tail _ (.head _)))
                                  (Nat.le_succ _))
                            · -- [J, K, Eamb] ⊢ A@(c+1)(B::Γ)C
                              refine consume₂ ?_
                                (G4c.identity_mem (.tail _ (.head _)))
                                (ihA (B :: Γ) C)
                              refine fire
                                (projE (l := itpEcls p S fuel (c + 2) Γ)
                                  (G4c.identity_mem
                                    (.tail _ (.tail _ (.head _)))) ?_)
                                (G4c.identity_mem (.head _))
                              simp only [itpEcls]
                              refine List.mem_append.mpr (Or.inr
                                (List.mem_flatMap.mpr
                                  ⟨(A₁.ifThen B₁).ifThen B, hFΓ, ?_⟩))
                              simp only
                              rw [if_neg hDΓ, if_pos hDS, if_pos hBD,
                                if_pos hABD]
                              exact .head _
                        next => cases hin
                      next hBD =>
                        split at hin
                        next hBDS =>
                          -- fresh piece: impR-texture, no cascade
                          rcases List.mem_singleton.mp hin with rfl
                          refine ⟨((itpE p S fuel (c + 1)
                                (B₁.ifThen B :: Γ)).ifThen
                              (itpA p S fuel (c + 1) (B₁.ifThen B :: Γ)
                                (A₁.ifThen B₁))).and
                            (itpA p S fuel (c + 1) (B :: Γ) C), ?_, ?_⟩
                          · simp only [itpAenv]
                            refine List.mem_flatMap.mpr
                              ⟨(A₁.ifThen B₁).ifThen B, hFΓ, ?_⟩
                            simp only
                            rw [if_neg hDΓ, if_pos hDS, if_neg hBD,
                              if_pos hBDS]
                            exact .head _
                          · refine G4c.andL (List.Perm.refl _)
                              (G4c.andR ?_ ?_)
                            · -- [J', K, Eamb] ⊢ E@(c+1)grown ⇢ A@(c+1)grown
                              refine G4c.impR ?_
                              refine consume₂ (consume₁
                                  (G4c.identity_mem (.head _))
                                  (ihE (B₁.ifThen B :: Γ))) ?_
                                (ihA (B₁.ifThen B :: Γ) (A₁.ifThen B₁))
                              exact fire
                                (G4c.identity_mem (.tail _ (.head _)))
                                (consume₁ (G4c.identity_mem (.head _))
                                  (ihE (B₁.ifThen B :: Γ)))
                            · -- second: identity-fire of the ambient's conjunct
                              refine consume₂ ?_
                                (G4c.identity_mem (.tail _ (.head _)))
                                (ihA (B :: Γ) C)
                              refine fire
                                (projE (l := itpEcls p S fuel (c + 2) Γ)
                                  (G4c.identity_mem
                                    (.tail _ (.tail _ (.head _)))) ?_)
                                (G4c.identity_mem (.head _))
                              simp only [itpEcls]
                              refine List.mem_append.mpr (Or.inr
                                (List.mem_flatMap.mpr
                                  ⟨(A₁.ifThen B₁).ifThen B, hFΓ, ?_⟩))
                              simp only
                              rw [if_neg hDΓ, if_pos hDS, if_neg hBD,
                                if_pos hBDS]
                              exact .head _
                        next => cases hin
                    next => cases hin
              | somehow A₁ =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next hBΓ =>
                    split at hin
                    next hBS =>
                      rcases List.mem_append.mp hin with hin | hin
                      · split at hin
                        next hAS =>
                          rcases List.mem_cons.mp hin with rfl | hin'
                          · -- jump disjunct (gated): first = cascade,
                            -- second = identity-fire
                            refine ⟨(itpA p S fuel c Γ A₁).and
                              (itpA p S fuel (c + 1) (B :: Γ) C), ?_, ?_⟩
                            · simp only [itpAenv]
                              refine List.mem_flatMap.mpr
                                ⟨A₁.somehow.ifThen B, hFΓ, ?_⟩
                              simp only
                              rw [if_neg hBΓ, if_pos hBS, if_pos hAS]
                              exact List.mem_append.mpr (Or.inl (.head _))
                            · refine G4c.andL (List.Perm.refl _)
                                (G4c.andR ?_ ?_)
                              · -- [V, K, Eamb] ⊢ A@cΓ(A₁): the jump cascade
                                exact consume₂ (G4c.identity_mem (.head _))
                                  (amb_pack_step
                                    (.tail _ (.tail _ (.head _)))
                                    (Nat.le_succ _))
                                  (cascade_jump p S fuel c hb Γ A₁ B
                                    hFΓ hBΓ hBS hAS)
                              · -- second: fire the ambient's jump conjunct
                                refine consume₂ ?_
                                  (G4c.identity_mem (.tail _ (.head _)))
                                  (ihA (B :: Γ) C)
                                refine fire
                                  (projE (l := itpEcls p S fuel (c + 2) Γ)
                                    (G4c.identity_mem
                                      (.tail _ (.tail _ (.head _)))) ?_)
                                  (G4c.identity_mem (.head _))
                                simp only [itpEcls]
                                refine List.mem_append.mpr (Or.inr
                                  (List.mem_flatMap.mpr
                                    ⟨A₁.somehow.ifThen B, hFΓ, ?_⟩))
                                simp only
                                rw [if_neg hBΓ, if_pos hBS, if_pos hAS]
                                exact List.mem_append.mpr (Or.inl (.head _))
                          · -- γ-head disjunct (gated): first = boxed cascade,
                            -- second = identity-fire
                            rcases List.mem_singleton.mp hin' with rfl
                            refine ⟨(((itpE p S fuel c Γ).ifThen
                                (itpA p S fuel c Γ A₁.somehow)).somehow).and
                              (itpA p S fuel (c + 1) (B :: Γ) C), ?_, ?_⟩
                            · simp only [itpAenv]
                              refine List.mem_flatMap.mpr
                                ⟨A₁.somehow.ifThen B, hFΓ, ?_⟩
                              simp only
                              rw [if_neg hBΓ, if_pos hBS, if_pos hAS]
                              exact List.mem_append.mpr
                                (Or.inl (.tail _ (.head _)))
                            · refine G4c.andL (List.Perm.refl _)
                                (G4c.andR ?_ ?_)
                              · -- [G, K, Eamb] ⊢ ◯(E@c ⇢ A@c ◯A₁)
                                exact cascade_gamma_box p S fuel c hb Γ A₁ B
                                  hFΓ hBΓ hBS hAS
                                  (G4c.identity_mem (.head _))
                                  (amb_pack_step
                                    (.tail _ (.tail _ (.head _)))
                                    (Nat.le_succ _))
                              · -- second: fire the ambient's γ-head conjunct
                                refine consume₂ ?_
                                  (G4c.identity_mem (.tail _ (.head _)))
                                  (ihA (B :: Γ) C)
                                refine fire
                                  (projE (l := itpEcls p S fuel (c + 2) Γ)
                                    (G4c.identity_mem
                                      (.tail _ (.tail _ (.head _)))) ?_)
                                  (G4c.identity_mem (.head _))
                                simp only [itpEcls]
                                refine List.mem_append.mpr (Or.inr
                                  (List.mem_flatMap.mpr
                                    ⟨A₁.somehow.ifThen B, hFΓ, ?_⟩))
                                simp only
                                rw [if_neg hBΓ, if_pos hBS, if_pos hAS]
                                exact List.mem_append.mpr
                                  (Or.inl (.tail _ (.head _)))
                        next => cases hin
                      · -- γ-context disjuncts (ungated): fuel level
                        obtain ⟨X, hXΓ, heq⟩ := List.mem_filterMap.mp hin
                        cases X with
                        | somehow x =>
                            simp only at heq
                            split at heq
                            next => cases heq
                            next hg =>
                              injection heq with heq'
                              subst heq'
                              refine ⟨(((itpE p S fuel (c + 1)
                                    (x :: Γ)).ifThen
                                  (itpA p S fuel (c + 1) (x :: Γ)
                                    A₁.somehow)).somehow).and
                                (itpA p S fuel (c + 1) (B :: Γ) C), ?_, ?_⟩
                              · simp only [itpAenv]
                                refine List.mem_flatMap.mpr
                                  ⟨A₁.somehow.ifThen B, hFΓ, ?_⟩
                                simp only
                                rw [if_neg hBΓ, if_pos hBS]
                                refine List.mem_append.mpr (Or.inr
                                  (List.mem_filterMap.mpr
                                    ⟨x.somehow, hXΓ, ?_⟩))
                                simp only
                                rw [if_neg hg]
                              · refine G4c.andL (List.Perm.refl _)
                                  (G4c.andR ?_ ?_)
                                · -- [Gx, K, Eamb] ⊢ ◯(E@(c+1)(x::Γ) ⇢ ...):
                                  -- open the ambient's ◯E-growth conjunct
                                  refine G4c.cut
                                    (A := (itpE p S fuel (c + 2)
                                      (x :: Γ)).somehow)
                                    (projE (l := itpEcls p S fuel (c + 2) Γ)
                                      (G4c.identity_mem
                                        (.tail _ (.tail _ (.head _)))) ?_) ?_
                                  · simp only [itpEcls]
                                    refine List.mem_append.mpr (Or.inr
                                      (List.mem_flatMap.mpr
                                        ⟨x.somehow, hXΓ, ?_⟩))
                                    simp only
                                    rw [if_neg hg]
                                    exact .head _
                                  · refine G4c.laxL (.head _) ?_
                                    -- E' :: ◯E' :: [Gx, K, Eamb]
                                    refine box_fire
                                      (X := itpE p S fuel (c + 2) (x :: Γ))
                                      (Y := itpA p S fuel (c + 2) (x :: Γ)
                                        A₁.somehow)
                                      (G4c.identity_mem
                                        (.tail _ (.tail _ (.head _))))
                                      (G4c.identity_mem (.head _)) ?_
                                    refine G4c.laxR (G4c.impR ?_)
                                    -- E@(c+1)(x::Γ) :: Y :: E' :: ◯E' :: ...
                                    exact consume₂
                                      (G4c.identity_mem
                                        (.tail _ (.tail _ (.head _))))
                                      (G4c.identity_mem (.tail _ (.head _)))
                                      (ihA (x :: Γ) A₁.somehow)
                                · -- second: fire the ambient's γ-context
                                  -- conjunct with the first component
                                  refine consume₂ ?_
                                    (G4c.identity_mem (.tail _ (.head _)))
                                    (ihA (B :: Γ) C)
                                  refine fire
                                    (projE (l := itpEcls p S fuel (c + 2) Γ)
                                      (G4c.identity_mem
                                        (.tail _ (.tail _ (.head _)))) ?_)
                                    (G4c.identity_mem (.head _))
                                  simp only [itpEcls]
                                  refine List.mem_append.mpr (Or.inr
                                    (List.mem_flatMap.mpr
                                      ⟨A₁.somehow.ifThen B, hFΓ, ?_⟩))
                                  simp only
                                  rw [if_neg hBΓ, if_pos hBS]
                                  refine List.mem_append.mpr (Or.inr
                                    (List.mem_filterMap.mpr
                                      ⟨x.somehow, hXΓ, ?_⟩))
                                  simp only
                                  rw [if_neg hg]
                        | prop _ => cases heq
                        | falsePLL => cases heq
                        | and _ _ => cases heq
                        | or _ _ => cases heq
                        | ifThen _ _ => cases heq
                    next => cases hin
        -- bundle and close through the ambient full-table mapping
        have hOTH : ∀ φ ∈ itpAoth p S fuel (c + 2) Γ C,
            ∃ ψ ∈ itpAoth p S fuel (c + 1) Γ C,
              G4c [φ, itpE p S (fuel + 1) (c + 2) Γ] ψ := by
          intro φ hφ
          simp only [itpAoth] at hφ ⊢
          rcases List.mem_append.mp hφ with hφ | hφ
          · obtain ⟨ψ, hψ, hd⟩ := hGOAL φ hφ
            exact ⟨ψ, List.mem_append.mpr (Or.inl hψ), hd⟩
          · obtain ⟨ψ, hψ, hd⟩ := hENV φ hφ
            exact ⟨ψ, List.mem_append.mpr (Or.inr hψ), hd⟩
        refine itpAfull_map_amb hOTH ?_
        intro b₁' hb₁
        refine ⟨c, rfl, ?_⟩
        obtain rfl : b₁' = c + 1 := by omega
        exact amb_step (.head _) (Nat.le_succ _)

/-- Ambient-relative budget stabilization, the crux of uniformity.
`b` ranges one past the threshold so that both `b` and `b-1` carry
every jump clause. -/
theorem itp_stab (p : String) (S : Finset PLLFormula) : ∀ (fuel : Nat)
    (b : Nat), kcap S < b →
    (∀ Γ, G4c [itpE p S fuel (b - 1) Γ] (itpE p S fuel b Γ)) ∧
    (∀ Γ C, G4c [itpE p S fuel b Γ, itpA p S fuel b Γ C]
      (itpA p S fuel (b - 1) Γ C)) := by
  intro fuel b hb
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 2 :=
    ⟨b - 2, by simp only [kcap] at hb; omega⟩
  exact itp_stab_aux p S fuel c hb

/-- Consumption form for the adequacy landing: under the theorem's own
ambient `E`, the packaged-budget value feeds any lower slot above the
threshold. -/
theorem itp_stab_le (p : String) (S : Finset PLLFormula)
    {fuel b b' : Nat} (hk : kcap S < b') (hle : b' ≤ b) :
    (∀ Γ, G4c [itpE p S fuel b' Γ] (itpE p S fuel b Γ)) ∧
    (∀ Γ C, G4c [itpE p S fuel b Γ, itpA p S fuel b Γ C]
      (itpA p S fuel b' Γ C)) := by
  induction hle with
  | refl =>
      exact ⟨fun Γ => G4c.iden (.head _),
        fun Γ C => G4c.identity_mem (.tail _ (.head _))⟩
  | @step m hm ih =>
      obtain ⟨ihE, ihA⟩ := ih
      have hm' : b' ≤ m := hm
      have hkm : kcap S < m + 1 := by omega
      constructor
      · intro Γ
        refine consume₁ (ihE Γ) ?_
        exact (itp_stab p S fuel (m + 1) hkm).1 Γ
      · intro Γ C
        have d1 : G4c [itpE p S fuel (m + 1) Γ, itpA p S fuel (m + 1) Γ C]
            (itpA p S fuel m Γ C) := (itp_stab p S fuel (m + 1) hkm).2 Γ C
        have d2 : G4c [itpE p S fuel (m + 1) Γ, itpA p S fuel (m + 1) Γ C]
            (itpE p S fuel m Γ) :=
          consume₁ (G4c.identity_mem (.head _))
            ((itp_budget_mono p S fuel).1 m Γ)
        exact consume₂ d2 d1 (ihA Γ C)

end PLLND
