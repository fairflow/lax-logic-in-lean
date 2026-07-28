import LaxLogic.PLLG4UITrunc

/-!
# The ◯-involving low-budget descent: the others-descent build

The kernel `cascade_low_pos_box` (wip/absorb_base.lean) asks, for a
piece-closed space `S` with goal and context inside `S`:

    from  Δ ⊢ itpE p S fuel (c+1) Γ   (the ambient existential table)
    and   Δ ⊢ itpA p S fh (c+1) Γ g   (the universal table, head fuel)
    infer Δ ⊢ itpA p S fuel c Γ g     (one budget down).

This file builds that descent by the organisation fixed in PROGRESS
§§71–77: a lexicographic induction on (defect `S Γ` strong, budget
strong, fuel structural) whose inner statement is the **others-descent**

    [E-ambient@(c+1), orAll (itpAoth @(c+1))] ⊢ orAll (itpAoth @c)

— both disjunct tables stripped of their truncation disjunct — with the
full-table descent recovered by a two-branch wrapper (`desc_of_oth`):
the source truncation disjunct commits the *target* truncation, opens
the source box against it (`box_open`), and the residual obligation is
again the others-descent; every undecorated source disjunct maps
through the others-descent directly.

Branch mechanisms inside the others-descent (the §71/§77 table):

* goal decomposition, present-antecedent goals — head-fuel descent
  (the fuel induction, through the wrapper);
* growth disjuncts (`∧`, atom-`⊃`, `⊃∧`, `⊃∨`, jump/γ second
  components) — the defect strong induction, ambient re-supplied from
  the matching conjunct of the ambient table;
* `◯χ`-environment disjuncts of a `◯`-goal — the ambient's own bare
  box `◯ itpE (χ::Γ)` is opened against the committed target box, and
  the boxed pair remaps by `box_remap_free` with the defect induction
  at the `χ`-grown context;
* goal-γ (`◯`-goal clause) — same-budget remap, value slot by the
  head-fuel descent at the unboxed goal;
* clause-γ and jump-family first components — the budget strong
  induction one budget down (`c ≥ 2`);
* at target budget `1` the gated first components sit at budget `0`,
  where the descent statement is false at `◯`-goals (the battery's
  false point): those branch instances, together with the one-step
  guard ascent at a fresh space piece (the fresh-antecedent equality
  law, battery-exact but unproven), are the OPEN interfaces stated as
  `Prop`s below; the assembly consumes them as hypotheses, so every
  theorem in this file is sorry-free except the clearly-marked stubs
  in the final section.

Sequent-level glue is replicated from `wip/absorb_base.lean`'s private
helpers and `wip/starve.lean`'s public versions (wip files are outside
the module path, so they cannot be imported).
-/

open PLLFormula

namespace PLLND

/-! ### Sequent-level glue (replicated) -/

/-- General subset weakening for `G4c` (through the set calculus). -/
private theorem wksub {Γ Γ' : List PLLFormula} {C : PLLFormula}
    (h : ∀ ψ ∈ Γ, ψ ∈ Γ') (d : G4c Γ C) : G4c Γ' C := by
  rw [G4c.iff_set] at d ⊢
  refine d.weaken_subset ?_
  intro y hy
  rw [List.mem_toFinset] at hy ⊢
  exact h y hy

/-- Consume a one-hypothesis lemma under a deriving context. -/
private theorem consume₁ {Δ : List PLLFormula} {X Z : PLLFormula}
    (dX : G4c Δ X) (L : G4c [X] Z) : G4c Δ Z :=
  G4c.cut dX (wksub (by
    intro ψ hψ
    rcases List.mem_singleton.mp hψ with rfl
    exact .head _) L)

/-- Consume a two-hypothesis lemma under a deriving context. -/
private theorem consume₂ {Δ : List PLLFormula} {X Y Z : PLLFormula}
    (dX : G4c Δ X) (dY : G4c Δ Y) (L : G4c [X, Y] Z) : G4c Δ Z :=
  G4c.cut dX (G4c.cut (dY.weaken X) (wksub (by
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

/-- Open a derivable boxed guarded implication against a `◯`-goal:
fire the guard and continue with the value in context (`wip/starve.lean`'s
public `box_open`, replicated). -/
private theorem box_open {Δ : List PLLFormula} {X Y W : PLLFormula}
    (dBox : G4c Δ ((X.ifThen Y).somehow)) (dX : G4c Δ X)
    (k : G4c (Y :: Δ) W.somehow) : G4c Δ W.somehow := by
  refine G4c.cut dBox (G4c.laxL (.head _) ?_)
  have dX' : G4c ((X.ifThen Y) :: (X.ifThen Y).somehow :: Δ) X :=
    wksub (by intro ψ h; simp only [List.mem_cons] at h ⊢; tauto) dX
  refine G4c.cut (G4c.cut dX' (G4c.mp X Y ((X.ifThen Y).somehow :: Δ))) ?_
  exact wksub (by intro ψ h; simp only [List.mem_cons] at h ⊢; tauto) k

/-- Open a derivable bare box against a `◯`-goal, keeping the body. -/
private theorem box_elim {Δ : List PLLFormula} {X W : PLLFormula}
    (dBox : G4c Δ X.somehow) (k : G4c (X :: Δ) W.somehow) :
    G4c Δ W.somehow := by
  refine G4c.cut dBox (G4c.laxL (.head _) ?_)
  exact wksub (by intro ψ h; simp only [List.mem_cons] at h ⊢; tauto) k

/-- The free-directions box remap (`wip/starve.lean`'s public version,
replicated): from a boxed guarded implication, a guard conversion, and
a value conversion — both as derivations in the extended context — the
remapped box follows. -/
private theorem box_remap_free {Δ : List PLLFormula} {E E' A A' : PLLFormula}
    (dBox : G4c Δ ((E.ifThen A).somehow))
    (dE : G4c (E' :: Δ) E)
    (dA : G4c (A :: E' :: Δ) A') :
    G4c Δ ((E'.ifThen A').somehow) := by
  refine G4c.cut dBox (G4c.laxL (.head _) ?_)
  refine G4c.laxR (G4c.impR ?_)
  have dE' : G4c (E' :: (E.ifThen A) :: (E.ifThen A).somehow :: Δ) E :=
    wksub (by intro ψ h; simp only [List.mem_cons] at h ⊢; tauto) dE
  have dmp : G4c (E :: E' :: (E.ifThen A) :: (E.ifThen A).somehow :: Δ) A :=
    wksub (by intro ψ h; simp only [List.mem_cons] at h ⊢; tauto)
      (G4c.mp E A (E' :: (E.ifThen A).somehow :: Δ))
  refine G4c.cut (G4c.cut dE' dmp) ?_
  exact wksub (by intro ψ h; simp only [List.mem_cons] at h ⊢; tauto) dA

/-- A boxed guarded implication whose value slot is `⊥`, with a
derivable guard, yields any `◯`-conclusion (`wip/starve.lean`'s public
`box_absurd`, replicated): open the box, fire the guard, explode. -/
private theorem box_absurd {Δ : List PLLFormula} {X : PLLFormula}
    (W : PLLFormula) (dBox : G4c Δ ((X.ifThen falsePLL).somehow))
    (dX : G4c Δ X) : G4c Δ W.somehow :=
  box_open dBox dX (G4c.botL (.head _))

/-! ### Monotonicity plumbing (replicated) -/

/-- Multi-step fuel monotonicity (`itp_fuel_mono` composed). -/
private theorem itp_fuel_mono_le (p : String) (S : Finset PLLFormula)
    {f f' : Nat} (h : f ≤ f') :
    (∀ b Γ, G4c [itpE p S f' b Γ] (itpE p S f b Γ)) ∧
    (∀ b Γ C, G4c [itpA p S f b Γ C] (itpA p S f' b Γ C)) := by
  induction h with
  | refl => exact ⟨fun b Γ => G4c.iden (.head _), fun b Γ C => G4c.iden (.head _)⟩
  | @step m _ ih =>
      obtain ⟨ihE, ihA⟩ := ih
      constructor
      · intro b Γ
        exact consume₁ (consume₁ (G4c.identity_mem (.head _))
          ((itp_fuel_mono p S m).1 b Γ)) (ihE b Γ)
      · intro b Γ C
        exact consume₁ (consume₁ (G4c.identity_mem (.head _)) (ihA b Γ C))
          ((itp_fuel_mono p S m).2 b Γ C)

/-- Lower a derivable existential table in fuel and budget (both free
directions on the `E`-side). -/
private theorem amb_down {p : String} {S : Finset PLLFormula}
    {f f' b b' : Nat} {Γ Δ : List PLLFormula}
    (d : G4c Δ (itpE p S f b Γ)) (hf : f' ≤ f) (hb : b' ≤ b) :
    G4c Δ (itpE p S f' b' Γ) :=
  consume₁ (consume₁ d ((itp_fuel_mono_le p S hf).1 _ _))
    ((itp_budget_mono_le p S hb f').1 Γ)

/-- Lift a derivable universal value in fuel and budget (both free
directions on the `A`-side). -/
private theorem val_lift {p : String} {S : Finset PLLFormula}
    {f f' b b' : Nat} {Γ Δ : List PLLFormula} {C : PLLFormula}
    (d : G4c Δ (itpA p S f b Γ C)) (hf : f ≤ f') (hb : b ≤ b') :
    G4c Δ (itpA p S f' b' Γ C) :=
  consume₁ (consume₁ d ((itp_fuel_mono_le p S hf).2 b Γ C))
    ((itp_budget_mono_le p S hb f').2 Γ C)

/-- Shift a derivable existential table onto a set-equal cons context. -/
private theorem amb_congr {p : String} {S : Finset PLLFormula} {f b : Nat}
    {Γ Δ : List PLLFormula} {X : PLLFormula}
    (d : G4c Δ (itpE p S f b Γ)) (hX : X ∈ Γ) :
    G4c Δ (itpE p S f b (X :: Γ)) :=
  consume₁ d ((itp_congr p S f).1 b Γ (X :: Γ) (by
    rw [List.toFinset_cons]
    exact (Finset.insert_eq_self.mpr (List.mem_toFinset.mpr hX)).symm))

/-- Free fuel lift of a boxed guarded pair: the guard converts
downward, the value upward — both fuel monotonicities. -/
private theorem box_fuel_lift {p : String} {S : Finset PLLFormula}
    {f f' b : Nat} {Γ : List PLLFormula} {gs : PLLFormula}
    (h : f ≤ f') {Δ : List PLLFormula}
    (dBox : G4c Δ (((itpE p S f b Γ).ifThen (itpA p S f b Γ gs)).somehow)) :
    G4c Δ (((itpE p S f' b Γ).ifThen (itpA p S f' b Γ gs)).somehow) :=
  box_remap_free dBox
    (consume₁ (G4c.identity_mem (.head _)) ((itp_fuel_mono_le p S h).1 _ _))
    (consume₁ (G4c.identity_mem (.head _)) ((itp_fuel_mono_le p S h).2 _ _ _))

/-- Free fuel lift of a guarded implication pair (the jump-conjunct
shape): guard downward, value upward. -/
private theorem imp_fuel_lift {p : String} {S : Finset PLLFormula}
    {f f' b : Nat} {Γ : List PLLFormula} {gs : PLLFormula}
    (h : f ≤ f') {Δ : List PLLFormula}
    (d : G4c Δ ((itpE p S f b Γ).ifThen (itpA p S f b Γ gs))) :
    G4c Δ ((itpE p S f' b Γ).ifThen (itpA p S f' b Γ gs)) :=
  consume₁ d (imp_mono ((itp_fuel_mono_le p S h).1 _ _)
    ((itp_fuel_mono_le p S h).2 _ _ _))

/-! ### Table facts -/

/-- Undecorated disjuncts always sit in the full table. -/
private theorem mem_itpAfull_of_oth {p : String} {S : Finset PLLFormula}
    {f b : Nat} {Γ : List PLLFormula} {C ψ : PLLFormula}
    (h : ψ ∈ itpAoth p S f b Γ C) : ψ ∈ itpAfull p S f b Γ C := by
  cases C <;> simp only [itpAfull] <;>
    first
      | exact h
      | exact List.mem_append.mpr (Or.inl h)

/-- At positive budget a `◯`-goal's undecorated table is nonempty: the
goal clause is present. -/
private theorem itpAoth_obGoal_isEmpty (p : String) (S : Finset PLLFormula)
    (f b : Nat) (Γ : List PLLFormula) (D : PLLFormula) :
    (itpAoth p S f (b + 1) Γ (D.somehow)).isEmpty = false := rfl

/-- Strict defect drop from a fresh space piece landing anywhere in a
grown context. -/
private theorem defect_lt_of_mem {S : Finset PLLFormula}
    {Γ Γ' : List PLLFormula} {x : PLLFormula}
    (hsub : Γ.toFinset ⊆ Γ'.toFinset) (hxS : x ∈ S) (hxΓ : x ∉ Γ)
    (hxΓ' : x ∈ Γ') : defect S Γ' < defect S Γ := by
  refine Finset.card_lt_card ⟨?_, ?_⟩
  · intro y hy
    rw [Finset.mem_sdiff] at hy ⊢
    exact ⟨hy.1, fun h => hy.2 (hsub h)⟩
  · intro hsub2
    have h2 := hsub2 (Finset.mem_sdiff.mpr
      ⟨hxS, fun h => hxΓ (List.mem_toFinset.mp h)⟩)
    rw [Finset.mem_sdiff] at h2
    exact h2.2 (List.mem_toFinset.mpr hxΓ')

/-! ### The head-fuel floor of the descent -/

/-- At head fuel `0` the descent is vacuous: the source table is `⊥`. -/
private theorem desc_zero (p : String) (S : Finset PLLFormula)
    {fuel c : Nat} {Γ Δ : List PLLFormula} {g : PLLFormula}
    (hhead : G4c Δ (itpA p S 0 (c + 1) Γ g)) :
    G4c Δ (itpA p S fuel c Γ g) := by
  simp only [itpA] at hhead
  exact G4c.cut hhead (G4c.botL (.head _))

/-! ### The two-branch wrapper (§77)

The full-table descent from the others-descent.  Truncations pair
across the descent: the source truncation disjunct commits the
*target* truncation `◯(itpE@(c−1) ⇢ ⋁ others@c)` — a `◯`-goal — and
opens the source box against it, the guard fired from the ambient by
downward monotonicity; the residual obligation inside is exactly the
others-descent, which also absorbs every undecorated source disjunct
directly.  No truncation strip is ever performed (§77's correction:
the strip's conclusion is not `◯`-shaped, so `laxL` could never open
the source box for it). -/

/-- The full-table descent at head fuel `F + 1`, target fuel `fl + 1`,
budgets `c + 1 → c`, from the others-descent at inner fuels `(F, fl)`
(supplied context-polymorphically). -/
private theorem desc_of_oth (p : String) (S : Finset PLLFormula)
    {F fl c : Nat} {Γ : List PLLFormula} {g : PLLFormula}
    (hF : F ≤ fl) (hc : 1 ≤ c)
    (hoth : ∀ (Δ' : List PLLFormula),
      G4c Δ' (itpE p S (fl + 1) (c + 1) Γ) →
      G4c Δ' (orAll (itpAoth p S F (c + 1) Γ g)) →
      G4c Δ' (orAll (itpAoth p S fl c Γ g)))
    {Δ : List PLLFormula}
    (hamb : G4c Δ (itpE p S (fl + 1) (c + 1) Γ))
    (hhead : G4c Δ (itpA p S (F + 1) (c + 1) Γ g)) :
    G4c Δ (itpA p S (fl + 1) c Γ g) := by
  obtain ⟨c'', rfl⟩ : ∃ c'', c = c'' + 1 := ⟨c - 1, by omega⟩
  rw [itpA_succ] at hhead ⊢
  refine G4c.cut hhead (G4c.orAll_elim ?_)
  intro φ hφ
  cases g with
  | somehow D =>
      simp only [itpAfull] at hφ ⊢
      rcases List.mem_append.mp hφ with hφ | hφ
      · -- undecorated source disjunct: through the others-descent,
        -- then inject the target others-table into the full table
        refine consume₁ (hoth (φ :: Δ) (hamb.weaken φ)
          (G4c.orAll_intro hφ (G4c.identity_mem (.head _)))) ?_
        exact orAll_map (fun ψ h => ⟨ψ, List.mem_append.mpr (Or.inl h),
          G4c.iden (.head _)⟩)
      · -- the truncation disjunct: commit the target truncation, open
        -- the source box inside it, finish by the others-descent
        by_cases h1 : (itpAoth p S F (c'' + 2) Γ (D.somehow)).isEmpty = true
        · rw [if_pos h1] at hφ; cases hφ
        · rw [if_neg h1] at hφ
          rcases List.mem_singleton.mp hφ with rfl
          refine G4c.orAll_intro
            (φ := ((itpE p S fl c'' Γ).ifThen
              (orAll (itpAoth p S fl (c'' + 1) Γ (D.somehow)))).somehow)
            (List.mem_append.mpr (Or.inr ?_)) ?_
          · rw [if_neg (by
              rw [itpAoth_obGoal_isEmpty]; exact Bool.false_ne_true)]
            exact .head _
          · refine box_open (W := (itpE p S fl c'' Γ).ifThen
                (orAll (itpAoth p S fl (c'' + 1) Γ (D.somehow))))
              (G4c.identity_mem (.head _))
              (amb_down (hamb.weaken _) (by omega) (by omega)) ?_
            refine G4c.laxR (G4c.impR ?_)
            refine hoth _ ?_ (G4c.identity_mem (.tail _ (.head _)))
            exact ((hamb.weaken _).weaken _).weaken _
  | prop q =>
      simp only [itpAfull] at hφ ⊢
      exact hoth (φ :: Δ) (hamb.weaken φ)
        (G4c.orAll_intro hφ (G4c.identity_mem (.head _)))
  | falsePLL =>
      simp only [itpAfull] at hφ ⊢
      exact hoth (φ :: Δ) (hamb.weaken φ)
        (G4c.orAll_intro hφ (G4c.identity_mem (.head _)))
  | and C₁ C₂ =>
      simp only [itpAfull] at hφ ⊢
      exact hoth (φ :: Δ) (hamb.weaken φ)
        (G4c.orAll_intro hφ (G4c.identity_mem (.head _)))
  | or C₁ C₂ =>
      simp only [itpAfull] at hφ ⊢
      exact hoth (φ :: Δ) (hamb.weaken φ)
        (G4c.orAll_intro hφ (G4c.identity_mem (.head _)))
  | ifThen C₁ C₂ =>
      simp only [itpAfull] at hφ ⊢
      exact hoth (φ :: Δ) (hamb.weaken φ)
        (G4c.orAll_intro hφ (G4c.identity_mem (.head _)))

end PLLND
