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

/-- The jump goals of the space: the goals whose values the gated
clauses of any context Γ can put in first-component position.  Both
gated shapes carry an `∈ S` side condition on the driving formula, so
this S-only set overcounts every context's live jump goals. -/
def jumpGoals (S : Finset PLLFormula) : Finset PLLFormula :=
  S.biUnion (fun F => match F with
    | .ifThen (.ifThen A B) _ => {A.ifThen B}
    | .ifThen (.somehow A) _ => {A, A.somehow}
    | _ => ∅)

theorem jumpGoals_card_le (S : Finset PLLFormula) :
    (jumpGoals S).card ≤ 2 * S.card := by
  refine le_trans (Finset.card_biUnion_le) ?_
  rw [two_mul]
  refine le_trans (Finset.sum_le_sum (g := fun _ => 2) ?_) ?_
  · intro F _
    match F with
    | .ifThen (.ifThen A B) _ => simp
    | .ifThen (.somehow A) _ => exact Finset.card_insert_le _ _
    | .prop _ => simp
    | .falsePLL => simp
    | .and _ _ => simp
    | .or _ _ => simp
    | .somehow _ => simp
    | .ifThen (.prop _) _ => simp
    | .ifThen .falsePLL _ => simp
    | .ifThen (.and _ _) _ => simp
    | .ifThen (.or _ _) _ => simp
  · simp only [Finset.sum_const, smul_eq_mul]
    omega

theorem mem_jumpGoals_imp {S : Finset PLLFormula} {A B D : PLLFormula}
    (h : (A.ifThen B).ifThen D ∈ S) : A.ifThen B ∈ jumpGoals S :=
  Finset.mem_biUnion.mpr ⟨_, h, by simp⟩

theorem mem_jumpGoals_jump {S : Finset PLLFormula} {A B : PLLFormula}
    (h : A.somehow.ifThen B ∈ S) : A ∈ jumpGoals S :=
  Finset.mem_biUnion.mpr ⟨_, h, by simp⟩

theorem mem_jumpGoals_gamma {S : Finset PLLFormula} {A B : PLLFormula}
    (h : A.somehow.ifThen B ∈ S) : A.somehow ∈ jumpGoals S :=
  Finset.mem_biUnion.mpr ⟨_, h, by simp⟩

/-- Jump-state threshold (overcount): a full descent allotment of
`J + 2` per defect level, `J = |jumpGoals S| ≤ 2·|S|` many chain
steps plus slack per level, with one spare level. -/
def kcap (S : Finset PLLFormula) : Nat :=
  (2 * S.card + 4) * (S.card + 2)

/-- The room inequality the cascade actually consumes, at entry:
`kcap S < c + 2` funds a fresh descent at any context. -/
theorem kcap_room {S : Finset PLLFormula} {c : Nat}
    (hb : kcap S < c + 2) (Γ : List PLLFormula) :
    (jumpGoals S).card + 1 +
      defect S Γ * ((jumpGoals S).card + 2) ≤ c := by
  have hJ : (jumpGoals S).card ≤ 2 * S.card := jumpGoals_card_le S
  have hd : defect S Γ ≤ S.card :=
    Finset.card_le_card (Finset.sdiff_subset)
  have h1 : defect S Γ * ((jumpGoals S).card + 2) ≤
      S.card * (2 * S.card + 2) :=
    Nat.mul_le_mul hd (by omega)
  have h2 : (2 * S.card + 4) * (S.card + 2) =
      S.card * (2 * S.card + 2) + (6 * S.card + 8) := by
    ring
  simp only [kcap] at hb
  omega

theorem kcap_ge {S : Finset PLLFormula} : 8 ≤ kcap S := by
  have : 4 * 2 ≤ (2 * S.card + 4) * (S.card + 2) :=
    Nat.mul_le_mul (by omega) (by omega)
  simpa [kcap] using this

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
cascade interface (the three lemmas below) is consumed from BOTH
halves; everything else closes exactly as the header describes.

MECHANISATION NOTE 2 (2026-07-11, later): the cascade itself is now
mechanised (`cascade_main`), with `kcap` enlarged to the defect-tower
form and the three interface lemmas derived as corollaries.  The
seen-set design survived the compiler with one systematic correction:
the descent must be run in continuation form (the conclusion is a
fixed `R`, each seen goal owns a continuation closing `R` from a
value at the current budget), because the target chain above a splice
cannot be rebuilt after the fact.  The four *sealed* branch shapes —
γ-goal, clause-γ-head, truncation, unpaid fresh antecedent — cannot
carry the continuations across their box/impR introduction and funnel
through `cascade_low`, which splits by saturation: the `defect = 0`
band is proved (`cascade_zero` — every space-guarded clause is dead),
and the `defect ≥ 1` band splits again by box-freeness: the box-free
closed covered instance is proved (`cascade_main_bf`, the shifted
ledger — no ◯-clauses means no seals), leaving the ◯-involving band
as the single sorried holdout `cascade_low_pos_box` (its docstring
records the failure analysis; at those sites only the defect-tower
room survives).
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

/-- **Deferred-commit seal crossing** (consumed form; 2026-07-12
guarded-reshaping campaign, zoo runs in `wip/refute4.lean`): a sealed
source box `◯(E ⇢ Z)` converts to the re-guarded target box
`◯(E' ⇢ Z')` given the old guard from the new one in context and the
inner value map — which receives the opened body `Z`, the target
guard `E'`, and the ENTIRE outer context `Δ`.  `laxL` retains
contexts, so every formula-shaped resource crosses a seal; this
engine makes that boundary machine-checked: what cannot cross is
exactly the meta-level material (the seen-set continuations, which
conclude the outer `R`).  It is the MOST a seal crossing can carry. -/
private theorem box_remap {Δ : List PLLFormula} {E E' Z Z' : PLLFormula}
    (dBox : G4c Δ ((E.ifThen Z).somehow))
    (dE : G4c (E' :: Δ) E)
    (k : G4c (Z :: E' :: Δ) Z') :
    G4c Δ ((E'.ifThen Z').somehow) := by
  refine G4c.cut dBox (G4c.laxL (.head _) ?_)
  refine G4c.laxR (G4c.impR ?_)
  -- context: E' :: (E ⇢ Z) :: ◯(E ⇢ Z) :: Δ  ⊢  Z'
  have dE₂ : G4c (E' :: (E.ifThen Z) :: (E.ifThen Z).somehow :: Δ) E :=
    weaken_sub (by
      intro ψ hψ
      rcases List.mem_cons.mp hψ with rfl | hψ
      · exact .head _
      · exact .tail _ (.tail _ (.tail _ hψ))) dE
  have dZ : G4c (E' :: (E.ifThen Z) :: (E.ifThen Z).somehow :: Δ) Z :=
    fire (G4c.identity_mem (.tail _ (.head _))) dE₂
  refine G4c.cut dZ (weaken_sub ?_ k)
  intro ψ hψ
  rcases List.mem_cons.mp hψ with rfl | hψ
  · exact .head _
  · rcases List.mem_cons.mp hψ with rfl | hψ
    · exact .tail _ (.head _)
    · exact .tail _ (.tail _ (.tail _ (.tail _ hψ)))

/-- **Re-guard a sealed box one budget down** (the `Z2b` survivor of
the refute4 adjudication: with the ambient outside the box,
`fails=0`; its ambient-free mirror `Z2a` is zoo-refuted).  At the
seals: `E := itpE@c`, `E' := itpE@(c−1)`, `dE` supplied by the
ambient through budget-mono — never by an in-box ascent, which is the
refuted direction.  Note the guard family is ambient-DOMINATED at
same-context seals (`E@(c+1) ⊢ E@c ⊢ E@(c−1)` pointwise), so this
discharges only guard plumbing; the inner value map is untouched. -/
private theorem box_reguard {Δ : List PLLFormula} {E E' Z : PLLFormula}
    (dBox : G4c Δ ((E.ifThen Z).somehow))
    (dE : G4c (E' :: Δ) E) :
    G4c Δ ((E'.ifThen Z).somehow) :=
  box_remap dBox dE (G4c.identity_mem (.head _))

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

/-- Lift a derivable A-value in both fuel and budget (both are the
easy directions on the A-side). -/
private theorem val_lift {p : String} {S : Finset PLLFormula}
    {f f' b b' : Nat} {Γ Δ : List PLLFormula} {C : PLLFormula}
    (d : G4c Δ (itpA p S f b Γ C)) (hf : f ≤ f') (hb : b ≤ b') :
    G4c Δ (itpA p S f' b' Γ C) :=
  consume₁ (consume₁ d ((itp_fuel_mono_le p S hf).2 b Γ C))
    ((itp_budget_mono_le p S hb f').2 Γ C)

/-- Step a derivable packaged ambient down in budget and fuel to a
fuel-level E-value. -/
private theorem amb_low {p : String} {S : Finset PLLFormula}
    {fuel f' b b' : Nat} {Γ Δ : List PLLFormula}
    (d : G4c Δ (itpE p S (fuel + 1) b Γ)) (hf : f' ≤ fuel) (hb : b' ≤ b) :
    G4c Δ (itpE p S f' b' Γ) :=
  consume₁ (consume₁ (consume₁ d ((itp_fuel_mono p S fuel).1 b Γ))
    ((itp_fuel_mono_le p S hf).1 b Γ)) ((itp_budget_mono_le p S hb f').1 Γ)

/-! ### The cascade proper

The b-descent, mechanised 2026-07-11.  `cascade_main` is the
generalized lemma (see its docstring): a mutual pair — the lazy
source-side descent in continuation form, and the one-step E-ascent —
by strong induction on the defect with an inner induction on the head
fuel.  The three interface lemmas the stabilization layer consumes
(`cascade_impLImp`, `cascade_jump`, `cascade_gamma`) are corollaries
of the entry wrapper `cascade_entry` at a singleton seen-set; their
statements are unchanged.  Everything is proved except the four
sealed positions, which funnel through the single sorried holdout
`cascade_low` below. -/

/-! #### The generalized descent

`cascade_main` is the lazy source-side cascade in continuation form.
Parameters: `d` bounds the defect (strong induction: grown-context
descents recurse at strictly smaller defect); `fh` is the head fuel
(inner induction: every same-context step peels one table level);
`fuel` is the reference fuel of the continuation interface and of the
packaged ambient; `seen` is the set of jump goals already carrying a
pending target slot, each represented by a continuation `hcls g'` that
closes the fixed conclusion `R` from any `g'`-value at the current
budget `c`.  The current goal `g` is itself in `seen` — its
continuation plays the role of "fill my own slot".  A repeat leaf
invokes the continuation directly on the freshly exposed low value
(mono-lifted); a fresh jump goal recurses with `c − 1`, the new
continuation assembling the enclosing target disjunct (its second
component paid by defect descent) before deferring to the current
goal's continuation.  `hroom` is the ledger: remaining fresh jump
goals + 1 + a full `J+2` allotment per remaining defect level. -/
/-- Undecorated disjuncts always sit in the full table. -/
private theorem mem_itpAfull_of_oth {p : String} {S : Finset PLLFormula}
    {f b : Nat} {Γ : List PLLFormula} {C ψ : PLLFormula}
    (h : ψ ∈ itpAoth p S f b Γ C) : ψ ∈ itpAfull p S f b Γ C := by
  cases C <;> simp only [itpAfull] <;>
    first
      | exact h
      | exact List.mem_append.mpr (Or.inl h)

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

/-! #### The saturated tier

At `defect S Γ = 0` the space is absorbed (`S ⊆ Γ` as sets): every
space-guarded clause of both tables is dead, the `E`-value is a
budget-independent conjunction of atoms, and the `A`-descent closes by
a plain fuel induction — no jumps, no pigeonhole.  This tier settles
the sealed sites whenever their context is saturated; the holdout
below then only claims the `defect ≥ 1` band. -/

private theorem sat_of_defect_zero {S : Finset PLLFormula}
    {Γ : List PLLFormula} (h : defect S Γ = 0) : ∀ x ∈ S, x ∈ Γ := by
  intro x hx
  by_contra hxΓ
  have hmem : x ∈ S \ Γ.toFinset := Finset.mem_sdiff.mpr
    ⟨hx, fun h' => hxΓ (List.mem_toFinset.mp h')⟩
  rw [defect, Finset.card_eq_zero] at h
  rw [h] at hmem
  cases hmem

/-- At a saturated context the `E`-value is budget-free: only the
atom and ⊥ clauses survive, and they do not mention the budget. -/
private theorem easc_zero (p : String) (S : Finset PLLFormula)
    (fh : Nat) (Γ : List PLLFormula) (b b' : Nat)
    (hsat : ∀ x ∈ S, x ∈ Γ) {Δ : List PLLFormula}
    (hsrc : G4c Δ (itpE p S fh b Γ)) :
    G4c Δ (itpE p S fh b' Γ) := by
  cases fh with
  | zero =>
      simp only [itpE]
      exact G4c.truePLL_intro _
  | succ FE =>
      rw [itpE_succ p S FE b' Γ]
      refine G4c.andAll_intro ?_
      intro ψ hψ
      simp only [itpEcls] at hψ
      rcases List.mem_append.mp hψ with hψ | hψ
      · rcases List.mem_append.mp hψ with hψ | hψ
        · split at hψ
          next hbot =>
            rcases List.mem_singleton.mp hψ with rfl
            refine projE (l := itpEcls p S FE b Γ) hsrc ?_
            simp only [itpEcls]
            exact List.mem_append.mpr (Or.inl (List.mem_append.mpr
              (Or.inl (by rw [if_pos hbot]; exact .head _))))
          next => cases hψ
        · obtain ⟨F', hF'Γ, heq⟩ := List.mem_filterMap.mp hψ
          cases F' with
          | prop q =>
              simp only at heq
              split at heq
              next => cases heq
              next hq =>
                injection heq with heq'
                subst heq'
                refine projE (l := itpEcls p S FE b Γ) hsrc ?_
                simp only [itpEcls]
                refine List.mem_append.mpr (Or.inl (List.mem_append.mpr
                  (Or.inr (List.mem_filterMap.mpr ⟨prop q, hF'Γ, ?_⟩))))
                simp only
                rw [if_neg hq]
          | falsePLL => cases heq
          | and _ _ => cases heq
          | or _ _ => cases heq
          | ifThen _ _ => cases heq
          | somehow _ => cases heq
      · obtain ⟨F', hF'Γ, hin⟩ := List.mem_flatMap.mp hψ
        exfalso
        cases F' with
        | prop _ => cases hin
        | falsePLL => cases hin
        | and A B =>
            simp only at hin
            split at hin
            next => cases hin
            next h1 =>
              split at hin
              next h2 =>
                exact h1 ⟨h2.1.elim id (hsat A), h2.2.elim id (hsat B)⟩
              next => cases hin
        | or A B =>
            simp only at hin
            split at hin
            next => cases hin
            next h1 =>
              split at hin
              next h2 => exact h1 (Or.inl (hsat A h2.1))
              next => cases hin
        | somehow χ =>
            simp only at hin
            split at hin
            next => cases hin
            next hg =>
              exact hg (by
                by_cases hχ : χ ∈ S
                · exact Or.inl (hsat χ hχ)
                · exact Or.inr hχ)
        | ifThen A' B =>
            cases A' with
            | prop q =>
                simp only at hin
                split at hin
                next => cases hin
                next hBΓ =>
                  split at hin
                  next hBS => exact hBΓ (hsat B hBS)
                  next => cases hin
            | falsePLL => cases hin
            | and A₁ B₁ =>
                simp only at hin
                split at hin
                next => cases hin
                next h1 =>
                  split at hin
                  next h2 => exact h1 (hsat _ h2)
                  next => cases hin
            | or A₁ B₁ =>
                simp only at hin
                split at hin
                next => cases hin
                next h1 =>
                  split at hin
                  next h2 =>
                    exact h1 ⟨h2.1.elim id (hsat _), h2.2.elim id (hsat _)⟩
                  next => cases hin
            | ifThen A₁ B₁ =>
                simp only at hin
                split at hin
                next => cases hin
                next hDΓ =>
                  split at hin
                  next hDS => exact hDΓ (hsat B hDS)
                  next => cases hin
            | somehow A₁ =>
                simp only at hin
                split at hin
                next => cases hin
                next hBΓ =>
                  split at hin
                  next hBS => exact hBΓ (hsat B hBS)
                  next => cases hin

/-- The saturated descent: at `defect S Γ = 0` the pair descent holds
at every budget `c ≥ 1`, by a plain fuel induction — the jump, growth
and γ-context clauses are all dead, so the only recursive positions
are goal-directed, and the fresh-antecedent guard ascends for free
(`easc_zero`). -/
private theorem cascade_zero (p : String) (S : Finset PLLFormula) :
    ∀ (fh : Nat) (Γ : List PLLFormula), (∀ x ∈ S, x ∈ Γ) →
    ∀ (fuel c : Nat) (g : PLLFormula) (Δ : List PLLFormula),
    1 ≤ c →
    G4c Δ (itpE p S fuel (c + 1) Γ) →
    G4c Δ (itpA p S fh (c + 1) Γ g) →
    fh ≤ fuel →
    G4c Δ (itpA p S fuel c Γ g) := by
  intro fh
  induction fh with
  | zero =>
      intro Γ hsat fuel c g Δ hc hamb hhead hfh
      simp only [itpA] at hhead
      exact G4c.cut hhead (G4c.botL (.head _))
  | succ F' ihf =>
      intro Γ hsat fuel c g Δ hc hamb hhead hfh
      obtain ⟨c₀, rfl⟩ : ∃ c₀, c = c₀ + 1 := ⟨c - 1, by omega⟩
      obtain ⟨fl, rfl⟩ : ∃ fl, fuel = fl + 1 := ⟨fuel - 1, by omega⟩
      have hF : F' ≤ fl := Nat.succ_le_succ_iff.mp hfh
      -- map the whole table at the head fuel, then lift
      have hmap : G4c [itpE p S (fl + 1) (c₀ + 2) Γ,
          orAll (itpAfull p S F' (c₀ + 2) Γ g)]
          (orAll (itpAfull p S F' (c₀ + 1) Γ g)) := by
        refine itpAfull_map_amb ?_ ?_
        · -- the undecorated disjuncts
          intro φ hφ
          simp only [itpAoth] at hφ ⊢
          rcases List.mem_append.mp hφ with hφ | hφ
          · -- goal-directed
            cases g with
            | prop q =>
                simp only [itpAgoal] at hφ ⊢
                split at hφ
                next => cases hφ
                next hq =>
                  rcases List.mem_singleton.mp hφ with rfl
                  refine ⟨prop q, List.mem_append.mpr (Or.inl ?_),
                    G4c.init (.head _)⟩
                  rw [if_neg hq]
                  exact .head _
            | falsePLL => simp only [itpAgoal] at hφ; cases hφ
            | and C₁ C₂ =>
                simp only [itpAgoal] at hφ ⊢
                rcases List.mem_singleton.mp hφ with rfl
                refine ⟨(itpA p S F' (c₀ + 1) Γ C₁).and
                  (itpA p S F' (c₀ + 1) Γ C₂),
                  List.mem_append.mpr (Or.inl (.head _)), ?_⟩
                refine G4c.andL (List.Perm.refl _) (G4c.andR ?_ ?_)
                · exact ihf Γ hsat F' (c₀ + 1) C₁ _ (by omega)
                    (consume₁ (G4c.identity_mem
                      (.tail _ (.tail _ (.head _))))
                      ((itp_fuel_mono_le p S
                        (le_trans hF (Nat.le_succ _))).1 _ _))
                    (G4c.identity_mem (.head _)) (Nat.le_refl _)
                · exact ihf Γ hsat F' (c₀ + 1) C₂ _ (by omega)
                    (consume₁ (G4c.identity_mem
                      (.tail _ (.tail _ (.head _))))
                      ((itp_fuel_mono_le p S
                        (le_trans hF (Nat.le_succ _))).1 _ _))
                    (G4c.identity_mem (.tail _ (.head _))) (Nat.le_refl _)
            | or C₁ C₂ =>
                simp only [itpAgoal] at hφ ⊢
                rcases List.mem_cons.mp hφ with rfl | hφ'
                · refine ⟨itpA p S F' (c₀ + 1) Γ C₁,
                    List.mem_append.mpr (Or.inl (.head _)), ?_⟩
                  exact ihf Γ hsat F' (c₀ + 1) C₁ _ (by omega)
                    (consume₁ (G4c.identity_mem (.tail _ (.head _)))
                      ((itp_fuel_mono_le p S
                        (le_trans hF (Nat.le_succ _))).1 _ _))
                    (G4c.identity_mem (.head _)) (Nat.le_refl _)
                · rcases List.mem_singleton.mp hφ' with rfl
                  refine ⟨itpA p S F' (c₀ + 1) Γ C₂,
                    List.mem_append.mpr (Or.inl (.tail _ (.head _))), ?_⟩
                  exact ihf Γ hsat F' (c₀ + 1) C₂ _ (by omega)
                    (consume₁ (G4c.identity_mem (.tail _ (.head _)))
                      ((itp_fuel_mono_le p S
                        (le_trans hF (Nat.le_succ _))).1 _ _))
                    (G4c.identity_mem (.head _)) (Nat.le_refl _)
            | ifThen C₁ C₂ =>
                simp only [itpAgoal] at hφ ⊢
                have hsat' : ∀ x ∈ S, x ∈ C₁ :: Γ :=
                  fun x hx => .tail _ (hsat x hx)
                split at hφ
                next hpres =>
                  rcases List.mem_singleton.mp hφ with rfl
                  refine ⟨(itpE p S F' c₀ (C₁ :: Γ)).ifThen
                    (itpA p S F' (c₀ + 1) (C₁ :: Γ) C₂),
                    List.mem_append.mpr (Or.inl ?_), ?_⟩
                  · rw [if_pos hpres]
                    exact .head _
                  · refine G4c.impR ?_
                    have hEg : G4c (itpE p S F' c₀ (C₁ :: Γ) ::
                        (itpE p S F' (c₀ + 1) (C₁ :: Γ)).ifThen
                          (itpA p S F' (c₀ + 2) (C₁ :: Γ) C₂) ::
                        [itpE p S (fl + 1) (c₀ + 2) Γ])
                        (itpE p S F' (c₀ + 1) (C₁ :: Γ)) :=
                      amb_congr (consume₁ (G4c.identity_mem
                          (.tail _ (.tail _ (.head _))))
                        (consume₁ ((itp_fuel_mono_le p S
                            (le_trans hF (Nat.le_succ _))).1 _ Γ)
                          ((itp_budget_mono p S F').1 (c₀ + 1) Γ)))
                        hpres
                    refine ihf (C₁ :: Γ) hsat' F' (c₀ + 1) C₂ _ (by omega)
                      (easc_zero p S F' (C₁ :: Γ) (c₀ + 1) (c₀ + 2)
                        hsat' hEg) ?_ (Nat.le_refl _)
                    exact fire (G4c.identity_mem (.tail _ (.head _))) hEg
                next hpres =>
                  rcases List.mem_singleton.mp hφ with rfl
                  refine ⟨(itpE p S F' (c₀ + 1) (C₁ :: Γ)).ifThen
                    (itpA p S F' (c₀ + 1) (C₁ :: Γ) C₂),
                    List.mem_append.mpr (Or.inl ?_), ?_⟩
                  · rw [if_neg hpres]
                    exact .head _
                  · refine G4c.impR ?_
                    have hEg : G4c (itpE p S F' (c₀ + 1) (C₁ :: Γ) ::
                        (itpE p S F' (c₀ + 2) (C₁ :: Γ)).ifThen
                          (itpA p S F' (c₀ + 2) (C₁ :: Γ) C₂) ::
                        [itpE p S (fl + 1) (c₀ + 2) Γ])
                        (itpE p S F' (c₀ + 2) (C₁ :: Γ)) :=
                      easc_zero p S F' (C₁ :: Γ) (c₀ + 1) (c₀ + 2) hsat'
                        (G4c.identity_mem (.head _))
                    refine ihf (C₁ :: Γ) hsat' F' (c₀ + 1) C₂ _ (by omega)
                      hEg ?_ (Nat.le_refl _)
                    exact fire (G4c.identity_mem (.tail _ (.head _))) hEg
            | somehow D =>
                simp only [itpAgoal] at hφ ⊢
                rcases List.mem_singleton.mp hφ with rfl
                refine ⟨((itpE p S F' c₀ Γ).ifThen
                  (itpA p S F' (c₀ + 1) Γ D)).somehow,
                  List.mem_append.mpr (Or.inl (.head _)), ?_⟩
                refine box_fire (W := (itpE p S F' c₀ Γ).ifThen
                    (itpA p S F' (c₀ + 1) Γ D))
                  (G4c.identity_mem (.head _))
                  (consume₁ (G4c.identity_mem (.tail _ (.head _)))
                    (consume₁ ((itp_fuel_mono_le p S
                        (le_trans hF (Nat.le_succ _))).1 _ Γ)
                      ((itp_budget_mono p S F').1 (c₀ + 1) Γ))) ?_
                refine G4c.laxR (G4c.impR ?_)
                refine ihf Γ hsat F' (c₀ + 1) D _ (by omega) ?_
                  (G4c.identity_mem (.tail _ (.head _))) (Nat.le_refl _)
                exact consume₁ (G4c.identity_mem
                  (.tail _ (.tail _ (.tail _ (.head _)))))
                  ((itp_fuel_mono_le p S (le_trans hF (Nat.le_succ _))).1 _ Γ)
          · -- context-directed: only the p-atom clause survives saturation
            simp only [itpAenv] at hφ ⊢
            obtain ⟨F0, hF0Γ, hin⟩ := List.mem_flatMap.mp hφ
            cases F0 with
            | prop q =>
                simp only at hin
                split at hin
                next hq =>
                  rcases List.mem_singleton.mp hin with rfl
                  refine ⟨truePLL, List.mem_append.mpr (Or.inr ?_),
                    G4c.truePLL_intro _⟩
                  refine List.mem_flatMap.mpr ⟨prop q, hF0Γ, ?_⟩
                  simp only
                  rw [if_pos hq]
                  exact .head _
                next => cases hin
            | falsePLL => cases hin
            | and A B =>
                simp only at hin
                exfalso
                split at hin
                next => cases hin
                next h1 =>
                  split at hin
                  next h2 =>
                    exact h1 ⟨h2.1.elim id (hsat A), h2.2.elim id (hsat B)⟩
                  next => cases hin
            | or A B =>
                simp only at hin
                exfalso
                split at hin
                next => cases hin
                next h1 =>
                  split at hin
                  next h2 => exact h1 (Or.inl (hsat A h2.1))
                  next => cases hin
            | somehow χ =>
                simp only at hin
                exfalso
                cases g with
                | somehow D =>
                    simp only at hin
                    split at hin
                    next => cases hin
                    next hg2 =>
                      exact hg2 (by
                        by_cases hχ : χ ∈ S
                        · exact Or.inl (hsat χ hχ)
                        · exact Or.inr hχ)
                | prop _ => cases hin
                | falsePLL => cases hin
                | and _ _ => cases hin
                | or _ _ => cases hin
                | ifThen _ _ => cases hin
            | ifThen A' B =>
                exfalso
                cases A' with
                | prop q =>
                    simp only at hin
                    split at hin
                    next => cases hin
                    next hBΓ =>
                      split at hin
                      next hBS => exact hBΓ (hsat B hBS)
                      next => cases hin
                | falsePLL => cases hin
                | and A₁ B₁ =>
                    simp only at hin
                    split at hin
                    next => cases hin
                    next h1 =>
                      split at hin
                      next h2 => exact h1 (hsat _ h2)
                      next => cases hin
                | or A₁ B₁ =>
                    simp only at hin
                    split at hin
                    next => cases hin
                    next h1 =>
                      split at hin
                      next h2 =>
                        exact h1 ⟨h2.1.elim id (hsat _),
                          h2.2.elim id (hsat _)⟩
                      next => cases hin
                | ifThen A₁ B₁ =>
                    simp only at hin
                    split at hin
                    next => cases hin
                    next hDΓ =>
                      split at hin
                      next hDS => exact hDΓ (hsat B hDS)
                      next => cases hin
                | somehow A₁ =>
                    simp only at hin
                    split at hin
                    next => cases hin
                    next hBΓ =>
                      split at hin
                      next hBS => exact hBΓ (hsat B hBS)
                      next => cases hin
        · -- the truncation feed
          intro b₁' hb₁
          obtain rfl : b₁' = c₀ + 1 := by omega
          refine ⟨c₀, rfl, ?_⟩
          exact consume₁ (consume₁ (G4c.identity_mem (.head _))
            ((itp_fuel_mono_le p S (le_trans hF (Nat.le_succ _))).1 _ Γ))
            ((itp_budget_mono p S F').1 (c₀ + 1) Γ)
      -- assemble: cut in the head, map, lift the result
      have hres : G4c Δ (itpA p S (F' + 1) (c₀ + 1) Γ g) := by
        refine G4c.cut hamb (G4c.cut (hhead.weaken _) ?_)
        exact weaken_sub (by
          intro ψ hψ
          rcases List.mem_cons.mp hψ with rfl | hψ
          · exact .tail _ (.head _)
          · rcases List.mem_singleton.mp hψ with rfl
            exact .head _) hmap
      exact val_lift hres hfh (Nat.le_refl _)

/-- No `◯` anywhere in the formula. -/
def boxFree : PLLFormula → Prop
  | .prop _ => True
  | .falsePLL => True
  | .and A B => boxFree A ∧ boxFree B
  | .or A B => boxFree A ∧ boxFree B
  | .ifThen A B => boxFree A ∧ boxFree B
  | .somehow _ => False

instance boxFree.dec : (φ : PLLFormula) → Decidable (boxFree φ)
  | .prop _ => .isTrue trivial
  | .falsePLL => .isTrue trivial
  | .and A B => @instDecidableAnd _ _ (boxFree.dec A) (boxFree.dec B)
  | .or A B => @instDecidableAnd _ _ (boxFree.dec A) (boxFree.dec B)
  | .ifThen A B => @instDecidableAnd _ _ (boxFree.dec A) (boxFree.dec B)
  | .somehow _ => .isFalse id

/-! #### The box-free tier

With `S` piece-closed and every formula of `S`, `Γ` and the goal
box-free, all four sealed positions are dead code, and the shifted
ledger (`… ≤ c + (J+2)`: the fresh-chain allotment paid out of the
first defect level) lets the full CPS machinery run from the holdout
sites' own room.  The clone below is `cascade_main` with the seal
branches replaced by gate contradictions and the goal/context
invariants threaded. -/

private theorem cascade_main_bf (p : String) (S : Finset PLLFormula)
    (hSbf : ∀ F ∈ S, boxFree F)
    (hand : ∀ {A B : PLLFormula}, A.and B ∈ S → A ∈ S ∧ B ∈ S)
    (hor : ∀ {A B : PLLFormula}, A.or B ∈ S → A ∈ S ∧ B ∈ S)
    (himp : ∀ {A B : PLLFormula}, A.ifThen B ∈ S → A ∈ S ∧ B ∈ S) :
    ∀ (d fh : Nat),
    (∀ (Γ : List PLLFormula) (fuel c : Nat) (g : PLLFormula)
       (seen : Finset PLLFormula) (Δ : List PLLFormula) (R : PLLFormula),
     defect S Γ ≤ d → g ∈ S → (∀ F ∈ Γ, F ∈ S) → g ∈ seen → 1 ≤ c →
     ((jumpGoals S \ seen).card + 1 + defect S Γ * ((jumpGoals S).card + 2)
       ≤ c + ((jumpGoals S).card + 2)) →
     (∀ g' ∈ seen, ∀ Δ', (∀ ψ ∈ Δ, ψ ∈ Δ') →
       G4c Δ' (itpA p S fuel c Γ g') → G4c Δ' R) →
     G4c Δ (itpE p S fuel (c + 1) Γ) →
     G4c Δ (itpA p S fh (c + 1) Γ g) →
     fh ≤ fuel →
     G4c Δ R) ∧
    (∀ (Γ : List PLLFormula) (c : Nat) (Δ : List PLLFormula),
     defect S Γ ≤ d → (∀ F ∈ Γ, F ∈ S) →
     ((jumpGoals S).card + 3 + defect S Γ * ((jumpGoals S).card + 2)
       ≤ c + ((jumpGoals S).card + 2)) →
     G4c Δ (itpE p S fh c Γ) →
     G4c Δ (itpE p S fh (c + 1) Γ)) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ihd =>
  intro fh
  induction fh with
  | zero =>
      constructor
      · intro Γ fuel c g seen Δ R hd hgS hΓS hg hc hroom hcls hamb hhead hfh
        have hΓbf : ∀ F ∈ Γ, boxFree F := fun F h => hSbf _ (hΓS _ h)
        simp only [itpA] at hhead
        exact G4c.cut hhead (G4c.botL (.head _))
      · intro Γ c Δ hd hΓS hroom hsrc
        have hΓbf : ∀ F ∈ Γ, boxFree F := fun F h => hSbf _ (hΓS _ h)
        simp only [itpE]
        exact G4c.truePLL_intro _
  | succ F ihf =>
      obtain ⟨ihfA, ihfE⟩ := ihf
      constructor
      · -- A-half: the descent cascade
        intro Γ fuel c g seen Δ R hd hgS hΓS hg hc hroom hcls hamb hhead hfh
        have hΓbf : ∀ F ∈ Γ, boxFree F := fun F h => hSbf _ (hΓS _ h)
        obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
        obtain ⟨fl, rfl⟩ : ∃ fl, fuel = fl + 1 := ⟨fuel - 1, by omega⟩
        rw [itpA_succ p S F (c' + 2) Γ g] at hhead
        have hF : F ≤ fl := Nat.succ_le_succ_iff.mp hfh
        have hSor : ∀ {X : PLLFormula}, X ∈ Γ ∨ X ∈ S → X ∈ S :=
          fun h => h.elim (fun h' => hΓS _ h') id
        have hScons : ∀ {X : PLLFormula}, X ∈ S →
            ∀ F' ∈ X :: Γ, F' ∈ S := by
          intro X hX F' hF'
          rcases List.mem_cons.mp hF' with rfl | hF'
          · exact hX
          · exact hΓS _ hF'
        -- lowered ambient at any weaker fuel/budget
        have hambL : ∀ (f' b' : Nat), f' ≤ fl + 1 → b' ≤ c' + 2 →
            G4c Δ (itpE p S f' b' Γ) := fun f' b' hf hb =>
          consume₁ (consume₁ hamb ((itp_fuel_mono_le p S hf).1 _ Γ))
            ((itp_budget_mono_le p S hb f').1 Γ)
        -- weak rooms for the sealed sites
        -- target-disjunct introduction at the reference-fuel table: a
        -- derivation of any member of the target table closes R
        have hfinT : ∀ (Δ' : List PLLFormula), (∀ ψ ∈ Δ, ψ ∈ Δ') →
            ∀ (ψ : PLLFormula), ψ ∈ itpAfull p S fl (c' + 1) Γ g →
            G4c Δ' ψ → G4c Δ' R := by
          intro Δ' hs ψ hmem dψ
          refine hcls g hg Δ' hs ?_
          rw [itpA_succ]
          exact G4c.orAll_intro hmem dψ
        -- room after a neutral seen-insertion (nested same-pair calls)
        have hroomI : ∀ (x : PLLFormula),
            (jumpGoals S \ insert x seen).card + 1 +
              defect S Γ * ((jumpGoals S).card + 2)
              ≤ c' + 1 + ((jumpGoals S).card + 2) :=
          fun x => le_trans (Nat.add_le_add_right (Nat.add_le_add_right
            (Finset.card_le_card (Finset.sdiff_subset_sdiff
              (Finset.Subset.refl _) (Finset.subset_insert _ _))) 1) _) hroom
        -- room after a paying seen-insertion (jump recursion, c drops)
        have hroomJ : ∀ (x : PLLFormula), x ∈ jumpGoals S → x ∉ seen →
            (jumpGoals S \ insert x seen).card + 1 +
              defect S Γ * ((jumpGoals S).card + 2)
              ≤ c' + ((jumpGoals S).card + 2) := by
          intro x hxJ hxs
          have h1 : (jumpGoals S \ insert x seen).card <
              (jumpGoals S \ seen).card := by
            refine Finset.card_lt_card ⟨Finset.sdiff_subset_sdiff
              (Finset.Subset.refl _) (Finset.subset_insert _ _), ?_⟩
            intro hsub
            have h2 := hsub (Finset.mem_sdiff.mpr ⟨hxJ, hxs⟩)
            rw [Finset.mem_sdiff] at h2
            exact h2.2 (Finset.mem_insert_self _ _)
          omega
        -- restated continuations for same-context nested calls
        have hclsR : ∀ (Δ₀ : List PLLFormula), (∀ ψ ∈ Δ, ψ ∈ Δ₀) →
            ∀ g' ∈ seen, ∀ Δ', (∀ ψ ∈ Δ₀, ψ ∈ Δ') →
            G4c Δ' (itpA p S fl (c' + 1) Γ g') → G4c Δ' R :=
          fun Δ₀ h0 g' hg' Δ' hs val =>
            hcls g' hg' Δ' (fun ψ h => hs ψ (h0 ψ h))
              (val_lift val (Nat.le_succ fl) (Nat.le_refl _))
        -- grown-context full descent: the strong induction on defect
        have hgrown : ∀ (Γ' : List PLLFormula), defect S Γ' < defect S Γ →
            ∀ (fw c₂ : Nat) (h : PLLFormula) (Δ' : List PLLFormula),
            h ∈ S → (∀ F' ∈ Γ', F' ∈ S) → 1 ≤ c₂ →
            ((jumpGoals S).card + 1 +
              defect S Γ' * ((jumpGoals S).card + 2)
              ≤ c₂ + ((jumpGoals S).card + 2)) →
            G4c Δ' (itpE p S fw (c₂ + 1) Γ') →
            G4c Δ' (itpA p S fw (c₂ + 1) Γ' h) →
            G4c Δ' (itpA p S fw c₂ Γ' h) := by
          intro Γ' hlt fw c₂ h Δ' hgS' hΓS' hc' hroom' hamb' hhead'
          refine (ihd (defect S Γ') (lt_of_lt_of_le hlt hd) fw).1 Γ' fw c₂ h
            {h} Δ' _ (Nat.le_refl _) hgS' hΓS'
            (Finset.mem_singleton_self h) hc' ?_ ?_
            hamb' hhead' (Nat.le_refl _)
          · exact le_trans (Nat.add_le_add_right (Nat.add_le_add_right
              (Finset.card_le_card Finset.sdiff_subset) 1) _) hroom'
          · intro g' hg' Δ'' _ hval
            rcases Finset.mem_singleton.mp hg' with rfl
            exact hval
        -- room arithmetic for a defect-paying descent
        have hroomG : ∀ (Γ' : List PLLFormula), defect S Γ' < defect S Γ →
            (jumpGoals S).card + 1 +
              defect S Γ' * ((jumpGoals S).card + 2)
              ≤ c' + 1 + ((jumpGoals S).card + 2) := by
          intro Γ' hlt
          have hexp : (defect S Γ' + 1) * ((jumpGoals S).card + 2) =
              defect S Γ' * ((jumpGoals S).card + 2) +
              ((jumpGoals S).card + 2) := by ring
          have hmul : (defect S Γ' + 1) * ((jumpGoals S).card + 2) ≤
              defect S Γ * ((jumpGoals S).card + 2) :=
            Nat.mul_le_mul_right _ (by omega)
          omega
        have hroomE : ∀ (Γ' : List PLLFormula), defect S Γ' < defect S Γ →
            (jumpGoals S).card + 3 +
              defect S Γ' * ((jumpGoals S).card + 2)
              ≤ c' + 1 + ((jumpGoals S).card + 2) := by
          intro Γ' hlt
          have hexp : (defect S Γ' + 1) * ((jumpGoals S).card + 2) =
              defect S Γ' * ((jumpGoals S).card + 2) +
              ((jumpGoals S).card + 2) := by ring
          have hmul : (defect S Γ' + 1) * ((jumpGoals S).card + 2) ≤
              defect S Γ * ((jumpGoals S).card + 2) :=
            Nat.mul_le_mul_right _ (by omega)
          omega
        -- guarded-implication component descent at a paying piece: the
        -- introduced target guard ascends by the E-half, fires the
        -- source, and the value descends by the defect induction
        have himpX : ∀ (X h : PLLFormula) (Δ' : List PLLFormula),
            defect S (X :: Γ) < defect S Γ →
            h ∈ S → X ∈ S →
            G4c Δ' ((itpE p S F (c' + 2) (X :: Γ)).ifThen
              (itpA p S F (c' + 2) (X :: Γ) h)) →
            G4c Δ' ((itpE p S fl (c' + 1) (X :: Γ)).ifThen
              (itpA p S fl (c' + 1) (X :: Γ) h)) := by
          intro X h Δ' hlt hgS' hXS dJ
          have hΓS' : ∀ F' ∈ X :: Γ, F' ∈ S := hScons hXS
          refine G4c.impR ?_
          have hE2 : G4c (itpE p S fl (c' + 1) (X :: Γ) :: Δ')
              (itpE p S fl (c' + 2) (X :: Γ)) :=
            (ihd (defect S (X :: Γ)) (lt_of_lt_of_le hlt hd) fl).2 (X :: Γ)
              (c' + 1) _ (Nat.le_refl _) hΓS' (hroomE (X :: Γ) hlt)
              (G4c.identity_mem (.head _))
          refine hgrown (X :: Γ) hlt fl (c' + 1) h _ hgS' hΓS' (by omega)
            (hroomG (X :: Γ) hlt) hE2 ?_
          refine val_lift (b := c' + 2) ?_ hF (Nat.le_refl _)
          exact fire (dJ.weaken _) (consume₁ hE2
            ((itp_fuel_mono_le p S hF).1 _ _))
        -- the per-disjunct branch analysis
        have hGOAL : ∀ φ ∈ itpAgoal p S F (c' + 2) Γ g, G4c (φ :: Δ) R := by
          intro φ hφ
          cases g with
          | prop q =>
              simp only [itpAgoal] at hφ
              split at hφ
              next => cases hφ
              next hq =>
                rcases List.mem_singleton.mp hφ with rfl
                refine hfinT _ (fun χ h => .tail _ h) (prop q) ?_
                  (G4c.init (.head _))
                simp only [itpAfull, itpAoth, itpAgoal]
                rw [if_neg hq]
                exact List.mem_append.mpr (Or.inl (.head _))
          | falsePLL => simp only [itpAgoal] at hφ; cases hφ
          | and C₁ C₂ =>
              simp only [itpAgoal] at hφ
              rcases List.mem_singleton.mp hφ with rfl
              refine G4c.andL (List.Perm.refl _) ?_
              -- V₁ :: V₂ :: Δ ⊢ R, CPS-chained through both components
              refine ihfA Γ fl (c' + 1) C₁ (insert C₁ seen) _ R hd
                (hand hgS).1 hΓS
                (Finset.mem_insert_self _ _) hc (hroomI C₁) ?_
                (((hambL fl (c' + 2) (Nat.le_succ _)
                  (Nat.le_refl _)).weaken _).weaken _)
                (G4c.identity_mem (.head _)) hF
              intro g' hg' Δ' hs' val₁
              rcases Finset.mem_insert.mp hg' with rfl | hg'
              · -- C₁ landed: chain into C₂
                refine ihfA Γ fl (c' + 1) C₂ (insert C₂ seen) Δ' R hd
                  (hand hgS).2 hΓS
                  (Finset.mem_insert_self _ _) hc (hroomI C₂) ?_
                  (weaken_sub (fun ψ h => hs' ψ (.tail _ (.tail _ h)))
                    (hambL fl (c' + 2) (Nat.le_succ _) (Nat.le_refl _)))
                  (G4c.identity_mem (hs' _ (.tail _ (.head _)))) hF
                intro g'' hg'' Δ'' hs'' val₂
                rcases Finset.mem_insert.mp hg'' with rfl | hg''
                · -- both landed: assemble the target conjunction
                  refine hfinT Δ''
                    (fun ψ h => hs'' ψ (hs' ψ (.tail _ (.tail _ h)))) _ ?_
                    (G4c.andR (weaken_sub hs'' val₁) val₂)
                  simp only [itpAfull, itpAoth, itpAgoal]
                  exact List.mem_append.mpr (Or.inl (.head _))
                · exact hclsR Δ' (fun ψ h => hs' ψ (.tail _ (.tail _ h)))
                    g'' hg'' Δ'' hs'' val₂
              · exact hclsR _ (fun ψ h => .tail _ (.tail _ h)) g' hg' Δ' hs'
                  val₁
          | or C₁ C₂ =>
              simp only [itpAgoal] at hφ
              rcases List.mem_cons.mp hφ with rfl | hφ'
              · refine ihfA Γ fl (c' + 1) C₁ (insert C₁ seen) _ R hd
                  (hor hgS).1 hΓS
                  (Finset.mem_insert_self _ _) hc (hroomI C₁) ?_
                  ((hambL fl (c' + 2) (Nat.le_succ _)
                    (Nat.le_refl _)).weaken _)
                  (G4c.identity_mem (.head _)) hF
                intro g' hg' Δ' hs' val
                rcases Finset.mem_insert.mp hg' with rfl | hg'
                · refine hfinT Δ' (fun ψ h => hs' ψ (.tail _ h)) _ ?_ val
                  simp only [itpAfull, itpAoth, itpAgoal]
                  exact List.mem_append.mpr (Or.inl (.head _))
                · exact hclsR _ (fun ψ h => .tail _ h) g' hg' Δ' hs' val
              · rcases List.mem_singleton.mp hφ' with rfl
                refine ihfA Γ fl (c' + 1) C₂ (insert C₂ seen) _ R hd
                  (hor hgS).2 hΓS
                  (Finset.mem_insert_self _ _) hc (hroomI C₂) ?_
                  ((hambL fl (c' + 2) (Nat.le_succ _)
                    (Nat.le_refl _)).weaken _)
                  (G4c.identity_mem (.head _)) hF
                intro g' hg' Δ' hs' val
                rcases Finset.mem_insert.mp hg' with rfl | hg'
                · refine hfinT Δ' (fun ψ h => hs' ψ (.tail _ h)) _ ?_ val
                  simp only [itpAfull, itpAoth, itpAgoal]
                  exact List.mem_append.mpr (Or.inl (.tail _ (.head _)))
                · exact hclsR _ (fun ψ h => .tail _ h) g' hg' Δ' hs' val
          | ifThen C₁ C₂ =>
              simp only [itpAgoal] at hφ
              split at hφ
              next hpres =>
                -- present antecedent: congr-transferred CPS descent
                rcases List.mem_singleton.mp hφ with rfl
                have hset : (C₁ :: Γ).toFinset = Γ.toFinset := by
                  rw [List.toFinset_cons]
                  exact Finset.insert_eq_self.mpr (List.mem_toFinset.mpr hpres)
                have hdef : defect S (C₁ :: Γ) = defect S Γ :=
                  defect_cons_eq hpres
                have hΓS' : ∀ F' ∈ C₁ :: Γ, F' ∈ S := hScons (himp hgS).1
                refine ihfA (C₁ :: Γ) fl (c' + 1) C₂ (insert C₂ seen) _ R
                  (by rw [hdef]; exact hd) (himp hgS).2 hΓS'
                  (Finset.mem_insert_self _ _) hc
                  (by rw [hdef]; exact hroomI C₂) ?_
                  ((amb_congr (hambL fl (c' + 2) (Nat.le_succ _)
                    (Nat.le_refl _)) hpres).weaken _)
                  (fire (G4c.identity_mem (.head _))
                    ((amb_congr (hambL F (c' + 1)
                      (le_trans hF (Nat.le_succ _))
                      (Nat.le_succ _)) hpres).weaken _)) hF
                intro g' hg' Δ' hs' val
                rcases Finset.mem_insert.mp hg' with rfl | hg'
                · refine hfinT Δ' (fun ψ h => hs' ψ (.tail _ h)) _ ?_
                    (G4c.impR (val.weaken (itpE p S fl c' (C₁ :: Γ))))
                  simp only [itpAfull, itpAoth, itpAgoal]
                  rw [if_pos hpres]
                  exact List.mem_append.mpr (Or.inl (.head _))
                · exact hclsR _ (fun ψ h => .tail _ h) g' hg' Δ' hs'
                    (consume₁ val ((itp_congr p S fl).2 (c' + 1)
                      (C₁ :: Γ) Γ g' hset))
              next hpres =>
                -- fresh antecedent
                rcases List.mem_singleton.mp hφ with rfl
                by_cases hC₁S : C₁ ∈ S
                · -- the new piece pays: guard ascent by the E-half,
                  -- component descent by the defect induction
                  have hlt : defect S (C₁ :: Γ) < defect S Γ :=
                    defect_cons_lt hC₁S hpres
                  have hΓS' : ∀ F' ∈ C₁ :: Γ, F' ∈ S := hScons hC₁S
                  refine hfinT _ (fun χ h => .tail _ h)
                    ((itpE p S fl (c' + 1) (C₁ :: Γ)).ifThen
                      (itpA p S fl (c' + 1) (C₁ :: Γ) C₂)) ?_ (G4c.impR ?_)
                  · simp only [itpAfull, itpAoth, itpAgoal]
                    rw [if_neg hpres]
                    exact List.mem_append.mpr (Or.inl (.head _))
                  · -- W :: φ :: Δ ⊢ the descended component at C₁ :: Γ
                    have hE2 : G4c (itpE p S fl (c' + 1) (C₁ :: Γ) ::
                        (itpE p S F (c' + 2) (C₁ :: Γ)).ifThen
                          (itpA p S F (c' + 2) (C₁ :: Γ) C₂) :: Δ)
                        (itpE p S fl (c' + 2) (C₁ :: Γ)) :=
                      (ihd (defect S (C₁ :: Γ))
                          (lt_of_lt_of_le hlt hd) fl).2 (C₁ :: Γ) (c' + 1) _
                        (Nat.le_refl _) hΓS' (hroomE _ hlt)
                        (G4c.identity_mem (.head _))
                    have hV : G4c (itpE p S fl (c' + 1) (C₁ :: Γ) ::
                        (itpE p S F (c' + 2) (C₁ :: Γ)).ifThen
                          (itpA p S F (c' + 2) (C₁ :: Γ) C₂) :: Δ)
                        (itpA p S F (c' + 2) (C₁ :: Γ) C₂) :=
                      fire (G4c.identity_mem (.tail _ (.head _)))
                        (consume₁ hE2 ((itp_fuel_mono_le p S hF).1 _ _))
                    exact hgrown (C₁ :: Γ) hlt fl (c' + 1) C₂ _
                      (himp hgS).2 hΓS' (by omega)
                      (hroomG _ hlt) hE2 (val_lift hV hF (Nat.le_refl _))
                · -- impossible: closure keeps goal antecedents in S
                  exact absurd (himp hgS).1 hC₁S
          | somehow D =>
              exact absurd (hSbf _ hgS) (by simp [boxFree])
        have hENV : ∀ φ ∈ itpAenv p S F (c' + 2) Γ g, G4c (φ :: Δ) R := by
          intro φ hφ
          simp only [itpAenv] at hφ
          obtain ⟨F', hF'Γ, hin⟩ := List.mem_flatMap.mp hφ
          have hsub1 : ∀ ψ ∈ Δ, ψ ∈ φ :: Δ := fun ψ h => .tail _ h
          cases F' with
          | prop q =>
              simp only at hin
              split at hin
              next hq =>
                rcases List.mem_singleton.mp hin with rfl
                refine hfinT _ hsub1 truePLL ?_ (G4c.truePLL_intro _)
                refine mem_itpAfull_of_oth ?_
                simp only [itpAoth]
                refine List.mem_append.mpr (Or.inr ?_)
                simp only [itpAenv]
                refine List.mem_flatMap.mpr ⟨prop q, hF'Γ, ?_⟩
                simp only
                rw [if_pos hq]
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
                  have hlt : defect S (A :: B :: Γ) < defect S Γ := by
                    by_cases hA : A ∈ Γ
                    · have hB : B ∉ Γ := fun hB => h1 ⟨hA, hB⟩
                      exact defect_lt_of_mem (Γ' := A :: B :: Γ)
                        (by intro y hy; simp only [List.toFinset_cons,
                          Finset.mem_insert]; exact Or.inr (Or.inr hy))
                        (h2.2.resolve_left hB) hB
                        (.tail _ (.head _))
                    · exact defect_lt_of_mem (Γ' := A :: B :: Γ)
                        (by intro y hy; simp only [List.toFinset_cons,
                          Finset.mem_insert]; exact Or.inr (Or.inr hy))
                        (h2.1.resolve_left hA) hA (.head _)
                  refine hfinT _ hsub1 (itpA p S fl (c' + 1) (A :: B :: Γ) g)
                    ?_ ?_
                  · refine mem_itpAfull_of_oth ?_
                    simp only [itpAoth]
                    refine List.mem_append.mpr (Or.inr ?_)
                    simp only [itpAenv]
                    refine List.mem_flatMap.mpr ⟨A.and B, hF'Γ, ?_⟩
                    simp only
                    rw [if_neg h1, if_pos h2]
                    exact .head _
                  · refine hgrown (A :: B :: Γ) hlt fl (c' + 1) g _ hgS
                      (by
                        intro F' hF'
                        rcases List.mem_cons.mp hF' with rfl | hF'
                        · exact hSor h2.1
                        · exact hScons (hSor h2.2) _ hF')
                      (by omega) (hroomG _ hlt) ?_
                      (val_lift (G4c.identity_mem (.head _)) hF
                        (Nat.le_refl _))
                    refine projE (l := itpEcls p S fl (c' + 2) Γ)
                      (hamb.weaken _) ?_
                    simp only [itpEcls]
                    refine List.mem_append.mpr (Or.inr
                      (List.mem_flatMap.mpr ⟨A.and B, hF'Γ, ?_⟩))
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
                  have hA : A ∉ Γ := fun h => h1 (Or.inl h)
                  have hB : B ∉ Γ := fun h => h1 (Or.inr h)
                  refine hfinT _ hsub1
                    (((itpE p S fl (c' + 1) (A :: Γ)).ifThen
                        (itpA p S fl (c' + 1) (A :: Γ) g)).and
                      ((itpE p S fl (c' + 1) (B :: Γ)).ifThen
                        (itpA p S fl (c' + 1) (B :: Γ) g))) ?_
                    (G4c.andL (List.Perm.refl _) (G4c.andR ?_ ?_))
                  · refine mem_itpAfull_of_oth ?_
                    simp only [itpAoth]
                    refine List.mem_append.mpr (Or.inr ?_)
                    simp only [itpAenv]
                    refine List.mem_flatMap.mpr ⟨A.or B, hF'Γ, ?_⟩
                    simp only
                    rw [if_neg h1, if_pos h2]
                    exact .head _
                  · exact (himpX A g _ (defect_cons_lt h2.1 hA) hgS
                      h2.1
                      (G4c.identity_mem (.head _))).perm
                      (List.Perm.refl _)
                  · exact himpX B g _ (defect_cons_lt h2.2 hB) hgS
                      h2.2
                      (G4c.identity_mem (.tail _ (.head _)))
                next => cases hin
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
                        -- present prop antecedent: bare growth
                        rcases List.mem_singleton.mp hin with rfl
                        refine hfinT _ hsub1
                          (itpA p S fl (c' + 1) (B :: Γ) g) ?_ ?_
                        · refine mem_itpAfull_of_oth ?_
                          simp only [itpAoth]
                          refine List.mem_append.mpr (Or.inr ?_)
                          simp only [itpAenv]
                          refine List.mem_flatMap.mpr
                            ⟨(prop q).ifThen B, hF'Γ, ?_⟩
                          simp only
                          rw [if_neg hBΓ, if_pos hBS, if_pos hq]
                          exact .head _
                        · refine hgrown (B :: Γ) (defect_cons_lt hBS hBΓ)
                            fl (c' + 1) g _ hgS (hScons hBS)
                            (by omega)
                            (hroomG _ (defect_cons_lt hBS hBΓ)) ?_
                            (val_lift (G4c.identity_mem (.head _)) hF
                              (Nat.le_refl _))
                          refine projE (l := itpEcls p S fl (c' + 2) Γ)
                            (hamb.weaken _) ?_
                          simp only [itpEcls]
                          refine List.mem_append.mpr (Or.inr
                            (List.mem_flatMap.mpr
                              ⟨(prop q).ifThen B, hF'Γ, ?_⟩))
                          simp only
                          rw [if_neg hBΓ, if_pos hBS, if_pos hq]
                          exact .head _
                      next hq =>
                        split at hin
                        next => cases hin
                        next hqp =>
                          -- fresh prop antecedent: atom-guarded growth
                          rcases List.mem_singleton.mp hin with rfl
                          refine hfinT _ hsub1 ((prop q).and
                            (itpA p S fl (c' + 1) (B :: Γ) g)) ?_ ?_
                          · refine mem_itpAfull_of_oth ?_
                            simp only [itpAoth]
                            refine List.mem_append.mpr (Or.inr ?_)
                            simp only [itpAenv]
                            refine List.mem_flatMap.mpr
                              ⟨(prop q).ifThen B, hF'Γ, ?_⟩
                            simp only
                            rw [if_neg hBΓ, if_pos hBS, if_neg hq, if_neg hqp]
                            exact .head _
                          · refine G4c.andL (List.Perm.refl _)
                              (G4c.andR (G4c.init (.head _)) ?_)
                            refine hgrown (B :: Γ) (defect_cons_lt hBS hBΓ)
                              fl (c' + 1) g _ hgS (hScons hBS)
                              (by omega)
                              (hroomG _ (defect_cons_lt hBS hBΓ)) ?_
                              (val_lift (G4c.identity_mem
                                (.tail _ (.head _))) hF (Nat.le_refl _))
                            refine fire (projE
                              (l := itpEcls p S fl (c' + 2) Γ)
                              (weaken_sub (fun ψ h =>
                                .tail _ (.tail _ h)) hamb) ?_)
                              (G4c.init (.head _))
                            simp only [itpEcls]
                            refine List.mem_append.mpr (Or.inr
                              (List.mem_flatMap.mpr
                                ⟨(prop q).ifThen B, hF'Γ, ?_⟩))
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
                      refine hfinT _ hsub1 (itpA p S fl (c' + 1)
                        (A₁.ifThen (B₁.ifThen B) :: Γ) g) ?_ ?_
                      · refine mem_itpAfull_of_oth ?_
                        simp only [itpAoth]
                        refine List.mem_append.mpr (Or.inr ?_)
                        simp only [itpAenv]
                        refine List.mem_flatMap.mpr
                          ⟨(A₁.and B₁).ifThen B, hF'Γ, ?_⟩
                        simp only
                        rw [if_neg h1, if_pos h2]
                        exact .head _
                      · refine hgrown _ (defect_cons_lt h2 h1) fl (c' + 1)
                          g _ hgS (hScons h2) (by omega)
                          (hroomG _ (defect_cons_lt h2 h1)) ?_
                          (val_lift (G4c.identity_mem (.head _)) hF
                            (Nat.le_refl _))
                        refine projE (l := itpEcls p S fl (c' + 2) Γ)
                          (hamb.weaken _) ?_
                        simp only [itpEcls]
                        refine List.mem_append.mpr (Or.inr
                          (List.mem_flatMap.mpr
                            ⟨(A₁.and B₁).ifThen B, hF'Γ, ?_⟩))
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
                      have hlt : defect S (A₁.ifThen B :: B₁.ifThen B :: Γ) <
                          defect S Γ := by
                        by_cases hA : A₁.ifThen B ∈ Γ
                        · have hBn : B₁.ifThen B ∉ Γ := fun hB => h1 ⟨hA, hB⟩
                          exact defect_lt_of_mem
                            (Γ' := A₁.ifThen B :: B₁.ifThen B :: Γ)
                            (by intro y hy; simp only [List.toFinset_cons,
                              Finset.mem_insert]; exact Or.inr (Or.inr hy))
                            (h2.2.resolve_left hBn) hBn (.tail _ (.head _))
                        · exact defect_lt_of_mem
                            (Γ' := A₁.ifThen B :: B₁.ifThen B :: Γ)
                            (by intro y hy; simp only [List.toFinset_cons,
                              Finset.mem_insert]; exact Or.inr (Or.inr hy))
                            (h2.1.resolve_left hA) hA (.head _)
                      refine hfinT _ hsub1 (itpA p S fl (c' + 1)
                        (A₁.ifThen B :: B₁.ifThen B :: Γ) g) ?_ ?_
                      · refine mem_itpAfull_of_oth ?_
                        simp only [itpAoth]
                        refine List.mem_append.mpr (Or.inr ?_)
                        simp only [itpAenv]
                        refine List.mem_flatMap.mpr
                          ⟨(A₁.or B₁).ifThen B, hF'Γ, ?_⟩
                        simp only
                        rw [if_neg h1, if_pos h2]
                        exact .head _
                      · refine hgrown _ hlt fl (c' + 1) g _ hgS
                          (by
                            intro F' hF'
                            rcases List.mem_cons.mp hF' with rfl | hF'
                            · exact hSor h2.1
                            · exact hScons (hSor h2.2) _ hF')
                          (by omega) (hroomG _ hlt) ?_
                          (val_lift (G4c.identity_mem (.head _)) hF
                            (Nat.le_refl _))
                        refine projE (l := itpEcls p S fl (c' + 2) Γ)
                          (hamb.weaken _) ?_
                        simp only [itpEcls]
                        refine List.mem_append.mpr (Or.inr
                          (List.mem_flatMap.mpr
                            ⟨(A₁.or B₁).ifThen B, hF'Γ, ?_⟩))
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
                        next hABS =>
                          -- gated present piece: the impLImp jump chain
                          rcases List.mem_singleton.mp hin with rfl
                          refine G4c.andL (List.Perm.refl _) ?_
                          -- J_s :: W :: Δ ⊢ R
                          have dHead : G4c
                              (((itpE p S F (c' + 1) Γ).ifThen
                                (itpA p S F (c' + 1) Γ (A₁.ifThen B₁))) ::
                               itpA p S F (c' + 2) (B :: Γ) g :: Δ)
                              (itpA p S F (c' + 1) Γ (A₁.ifThen B₁)) :=
                            fire (G4c.identity_mem (.head _))
                              (weaken_sub (fun ψ h => .tail _ (.tail _ h))
                                (hambL F (c' + 1)
                                  (le_trans hF (Nat.le_succ _))
                                  (Nat.le_succ _)))
                          have hgJ : A₁.ifThen B₁ ∈ jumpGoals S :=
                            mem_jumpGoals_imp hABS
                          have hd1s : 1 ≤ defect S Γ :=
                            Finset.card_pos.mpr ⟨B, Finset.mem_sdiff.mpr
                              ⟨hDS, fun h => hDΓ (List.mem_toFinset.mp h)⟩⟩
                          have hmul1 : 1 * ((jumpGoals S).card + 2) ≤
                              defect S Γ * ((jumpGoals S).card + 2) :=
                            Nat.mul_le_mul_right _ hd1s
                          by_cases hseen : A₁.ifThen B₁ ∈ seen
                          · -- repeat leaf: the mono-splice
                            exact hcls _ hseen _
                              (fun ψ h => .tail _ (.tail _ h))
                              (val_lift dHead
                                (le_trans hF (Nat.le_succ _))
                                (Nat.le_refl _))
                          · -- fresh jump goal: descend
                            have hxf : 1 ≤ (jumpGoals S \ seen).card :=
                              Finset.card_pos.mpr ⟨_, Finset.mem_sdiff.mpr
                                ⟨hgJ, hseen⟩⟩
                            refine ihfA Γ fl c' (A₁.ifThen B₁)
                              (insert (A₁.ifThen B₁) seen) _ R hd
                              (himp hABS).1 hΓS
                              (Finset.mem_insert_self _ _) (by omega)
                              (hroomJ _ hgJ hseen) ?_
                              (weaken_sub (fun ψ h => .tail _ (.tail _ h))
                                (hambL fl (c' + 1) (Nat.le_succ _)
                                  (Nat.le_succ _)))
                              dHead hF
                            intro g'' hg'' Δ' hs' val
                            rcases Finset.mem_insert.mp hg'' with rfl | hg''
                            · -- the new continuation: assemble the target
                              -- jump disjunct around the returned value
                              refine hfinT Δ'
                                (fun ψ h => hs' ψ (.tail _ (.tail _ h)))
                                (((itpE p S fl c' Γ).ifThen
                                    (itpA p S fl c' Γ (A₁.ifThen B₁))).and
                                  (itpA p S fl (c' + 1) (B :: Γ) g))
                                ?_ (G4c.andR
                                  (G4c.impR (val.weaken (itpE p S fl c' Γ)))
                                  ?_)
                              · refine mem_itpAfull_of_oth ?_
                                simp only [itpAoth]
                                refine List.mem_append.mpr (Or.inr ?_)
                                simp only [itpAenv]
                                refine List.mem_flatMap.mpr
                                  ⟨(A₁.ifThen B₁).ifThen B, hF'Γ, ?_⟩
                                simp only
                                rw [if_neg hDΓ, if_pos hDS, if_pos hBD,
                                  if_pos hABS]
                                exact .head _
                              · -- second component: grown descent, ambient
                                -- unlocked by firing the packaged jump conjunct
                                refine hgrown (B :: Γ)
                                  (defect_cons_lt hDS hDΓ) fl (c' + 1) g Δ'
                                  hgS (hScons hDS) (by omega)
                                  (hroomG _ (defect_cons_lt hDS hDΓ)) ?_
                                  (val_lift (G4c.identity_mem
                                    (A := itpA p S F (c' + 2) (B :: Γ) g)
                                    (hs' _ (.tail _ (.head _)))) hF
                                    (Nat.le_refl _))
                                refine fire
                                  (X := (itpE p S fl (c' + 1) Γ).ifThen
                                    (itpA p S fl (c' + 1) Γ (A₁.ifThen B₁)))
                                  (projE
                                  (l := itpEcls p S fl (c' + 2) Γ)
                                  (weaken_sub (fun ψ h =>
                                    hs' ψ (.tail _ (.tail _ h))) hamb) ?_)
                                  (G4c.impR ((val_lift val (Nat.le_refl _)
                                    (Nat.le_succ _)).weaken _))
                                simp only [itpEcls]
                                refine List.mem_append.mpr (Or.inr
                                  (List.mem_flatMap.mpr
                                    ⟨(A₁.ifThen B₁).ifThen B, hF'Γ, ?_⟩))
                                simp only
                                rw [if_neg hDΓ, if_pos hDS, if_pos hBD,
                                  if_pos hABS]
                                exact .head _
                            · exact hcls g'' hg'' Δ'
                                (fun ψ h => hs' ψ (.tail _ (.tail _ h)))
                                (val_lift val (Nat.le_succ _)
                                  (Nat.le_succ _))
                        next => cases hin
                      next hBD =>
                        split at hin
                        next hBDS =>
                          -- fresh piece: guarded growth on both components
                          rcases List.mem_singleton.mp hin with rfl
                          refine G4c.andL (List.Perm.refl _) ?_
                          refine hfinT _
                            (fun ψ h => .tail _ (.tail _ h))
                            (((itpE p S fl (c' + 1) (B₁.ifThen B :: Γ)).ifThen
                                (itpA p S fl (c' + 1) (B₁.ifThen B :: Γ)
                                  (A₁.ifThen B₁))).and
                              (itpA p S fl (c' + 1) (B :: Γ) g)) ?_
                            (G4c.andR ?_ ?_)
                          · refine mem_itpAfull_of_oth ?_
                            simp only [itpAoth]
                            refine List.mem_append.mpr (Or.inr ?_)
                            simp only [itpAenv]
                            refine List.mem_flatMap.mpr
                              ⟨(A₁.ifThen B₁).ifThen B, hF'Γ, ?_⟩
                            simp only
                            rw [if_neg hDΓ, if_pos hDS, if_neg hBD,
                              if_pos hBDS]
                            exact .head _
                          · exact himpX (B₁.ifThen B) (A₁.ifThen B₁) _
                              (defect_cons_lt hBDS hBD)
                              (himp (hΓS _ hF'Γ)).1 hBDS
                              (G4c.identity_mem (.head _))
                          · refine hgrown (B :: Γ)
                              (defect_cons_lt hDS hDΓ) fl (c' + 1) g _
                              hgS (hScons hDS) (by omega)
                              (hroomG _ (defect_cons_lt hDS hDΓ)) ?_
                              (val_lift (G4c.identity_mem
                                (.tail _ (.head _))) hF (Nat.le_refl _))
                            refine fire (projE
                              (l := itpEcls p S fl (c' + 2) Γ)
                              (weaken_sub (fun ψ h =>
                                .tail _ (.tail _ h)) hamb) ?_)
                              (G4c.impR (val_lift (fire
                                ((G4c.identity_mem (A := (itpE p S F (c' + 2)
                                    (B₁.ifThen B :: Γ)).ifThen
                                  (itpA p S F (c' + 2) (B₁.ifThen B :: Γ)
                                    (A₁.ifThen B₁)))
                                  (.tail _ (.head _))))
                                (consume₁ (G4c.identity_mem (.head _))
                                  ((itp_fuel_mono_le p S hF).1 _ _)))
                                hF (Nat.le_refl _)))
                            simp only [itpEcls]
                            refine List.mem_append.mpr (Or.inr
                              (List.mem_flatMap.mpr
                                ⟨(A₁.ifThen B₁).ifThen B, hF'Γ, ?_⟩))
                            simp only
                            rw [if_neg hDΓ, if_pos hDS, if_neg hBD,
                              if_pos hBDS]
                            exact .head _
                        next => cases hin
                    next => cases hin
              | somehow A₁ =>
                  exact absurd (hΓbf _ hF'Γ) (by simp [boxFree])
          | somehow χ =>
              exact absurd (hΓbf _ hF'Γ) (by simp [boxFree])
        have hOTH : ∀ φ ∈ itpAoth p S F (c' + 2) Γ g, G4c (φ :: Δ) R := by
          intro φ hφ
          simp only [itpAoth] at hφ
          rcases List.mem_append.mp hφ with hφ | hφ
          · exact hGOAL φ hφ
          · exact hENV φ hφ
        refine G4c.cut hhead (G4c.orAll_elim ?_)
        intro φ hφ
        cases g with
        | somehow D =>
            exact absurd (hSbf _ hgS) (by simp [boxFree])
        | prop q => exact hOTH φ hφ
        | falsePLL => exact hOTH φ hφ
        | and C₁ C₂ => exact hOTH φ hφ
        | or C₁ C₂ => exact hOTH φ hφ
        | ifThen C₁ C₂ => exact hOTH φ hφ
      · -- E-half: the one-step ascent
        intro Γ c Δ hd hΓS hroom hsrc
        have hΓbf : ∀ F ∈ Γ, boxFree F := fun F h => hSbf _ (hΓS _ h)
        obtain ⟨c'', rfl⟩ : ∃ c'', c = c'' + 1 := ⟨c - 1, by omega⟩
        rw [itpE_succ p S F (c'' + 2) Γ]
        refine G4c.andAll_intro ?_
        intro ψ hψ
        -- fuel-level source at any weaker budget
        have hsrcF : ∀ (b' : Nat), b' ≤ c'' + 1 → G4c Δ (itpE p S F b' Γ) :=
          fun b' hb' => consume₁ (consume₁ hsrc
            ((itp_fuel_mono p S F).1 _ Γ))
            ((itp_budget_mono_le p S hb' F).1 Γ)
        have hSor : ∀ {X : PLLFormula}, X ∈ Γ ∨ X ∈ S → X ∈ S :=
          fun h => h.elim (fun h' => hΓS _ h') id
        have hScons : ∀ {X : PLLFormula}, X ∈ S →
            ∀ F' ∈ X :: Γ, F' ∈ S := by
          intro X hX F' hF'
          rcases List.mem_cons.mp hF' with rfl | hF'
          · exact hX
          · exact hΓS _ hF'
        -- entry room for same-context A-descents
        have hroomA : ∀ (x : PLLFormula), (jumpGoals S \ {x}).card + 1 +
            defect S Γ * ((jumpGoals S).card + 2)
            ≤ c'' + ((jumpGoals S).card + 2) := by
          intro x
          have hc := Finset.card_le_card
            (Finset.sdiff_subset (s := jumpGoals S) (t := {x}))
          omega
        -- one-step ascent at a defect-paying grown context
        have hEg : ∀ (Γ' : List PLLFormula), defect S Γ' < defect S Γ →
            (∀ F' ∈ Γ', F' ∈ S) →
            ∀ (Δ' : List PLLFormula), G4c Δ' (itpE p S F (c'' + 1) Γ') →
            G4c Δ' (itpE p S F (c'' + 2) Γ') := by
          intro Γ' hlt hΓS' Δ' hsrc'
          refine ihfE Γ' (c'' + 1) Δ' (le_trans (le_of_lt hlt) hd) hΓS'
            ?_ hsrc'
          have hexp : (defect S Γ' + 1) * ((jumpGoals S).card + 2) =
              defect S Γ' * ((jumpGoals S).card + 2) +
              ((jumpGoals S).card + 2) := by ring
          have hmul : (defect S Γ' + 1) * ((jumpGoals S).card + 2) ≤
              defect S Γ * ((jumpGoals S).card + 2) :=
            Nat.mul_le_mul_right _ (by omega)
          omega
        -- entry-shaped same-context A-descent
        have hAd : ∀ (β : Nat) (h : PLLFormula) (Δ' : List PLLFormula),
            h ∈ S → 1 ≤ β →
            ((jumpGoals S \ {h}).card + 1 +
              defect S Γ * ((jumpGoals S).card + 2)
              ≤ β + ((jumpGoals S).card + 2)) →
            G4c Δ' (itpE p S F (β + 1) Γ) →
            G4c Δ' (itpA p S F (β + 1) Γ h) →
            G4c Δ' (itpA p S F β Γ h) := by
          intro β h Δ' hgS' hβ hr hamb' hhead'
          refine ihfA Γ F β h {h} Δ' _ hd hgS' hΓS
            (Finset.mem_singleton_self h) hβ hr
            ?_ hamb' hhead' (Nat.le_refl _)
          intro g' hg' Δ'' _ hval
          rcases Finset.mem_singleton.mp hg' with rfl
          exact hval
        -- entry-shaped A-descent at a defect-paying grown context
        have hAg : ∀ (Γ' : List PLLFormula), defect S Γ' < defect S Γ →
            ∀ (β : Nat) (h : PLLFormula) (Δ' : List PLLFormula),
            h ∈ S → (∀ F' ∈ Γ', F' ∈ S) → 1 ≤ β → c'' ≤ β →
            G4c Δ' (itpE p S F (β + 1) Γ') →
            G4c Δ' (itpA p S F (β + 1) Γ' h) →
            G4c Δ' (itpA p S F β Γ' h) := by
          intro Γ' hlt β h Δ' hgS' hΓS' hβ1 hβ hamb' hhead'
          refine ihfA Γ' F β h {h} Δ' _ (le_trans (le_of_lt hlt) hd)
            hgS' hΓS' (Finset.mem_singleton_self h) hβ1 ?_ ?_ hamb'
            hhead' (Nat.le_refl _)
          · have hc := Finset.card_le_card
              (Finset.sdiff_subset (s := jumpGoals S) (t := {h}))
            have hexp : (defect S Γ' + 1) * ((jumpGoals S).card + 2) =
                defect S Γ' * ((jumpGoals S).card + 2) +
                ((jumpGoals S).card + 2) := by ring
            have hmul : (defect S Γ' + 1) * ((jumpGoals S).card + 2) ≤
                defect S Γ * ((jumpGoals S).card + 2) :=
              Nat.mul_le_mul_right _ (by omega)
            omega
          · intro g' hg' Δ'' _ hval
            rcases Finset.mem_singleton.mp hg' with rfl
            exact hval
        simp only [itpEcls] at hψ
        rcases List.mem_append.mp hψ with hψ | hψ
        · rcases List.mem_append.mp hψ with hψ | hψ
          · -- the ⊥ clause
            split at hψ
            next hbot =>
              rcases List.mem_singleton.mp hψ with rfl
              refine projE (l := itpEcls p S F (c'' + 1) Γ) hsrc ?_
              simp only [itpEcls]
              exact List.mem_append.mpr (Or.inl (List.mem_append.mpr
                (Or.inl (by rw [if_pos hbot]; exact .head _))))
            next => cases hψ
          · -- the atom clauses
            obtain ⟨F', hF'Γ, heq⟩ := List.mem_filterMap.mp hψ
            cases F' with
            | prop q =>
                simp only at heq
                split at heq
                next => cases heq
                next hq =>
                  injection heq with heq'
                  subst heq'
                  refine projE (l := itpEcls p S F (c'' + 1) Γ) hsrc ?_
                  simp only [itpEcls]
                  refine List.mem_append.mpr (Or.inl (List.mem_append.mpr
                    (Or.inr (List.mem_filterMap.mpr ⟨prop q, hF'Γ, ?_⟩))))
                  simp only
                  rw [if_neg hq]
            | falsePLL => cases heq
            | and _ _ => cases heq
            | or _ _ => cases heq
            | ifThen _ _ => cases heq
            | somehow _ => cases heq
        · -- the rule clauses
          obtain ⟨F', hF'Γ, hin⟩ := List.mem_flatMap.mp hψ
          cases F' with
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
                  have hlt : defect S (A :: B :: Γ) < defect S Γ := by
                    by_cases hA : A ∈ Γ
                    · have hB : B ∉ Γ := fun hB => h1 ⟨hA, hB⟩
                      exact defect_lt_of_mem (Γ' := A :: B :: Γ)
                        (by intro y hy; simp only [List.toFinset_cons,
                          Finset.mem_insert]; exact Or.inr (Or.inr hy))
                        (h2.2.resolve_left hB) hB (.tail _ (.head _))
                    · exact defect_lt_of_mem (Γ' := A :: B :: Γ)
                        (by intro y hy; simp only [List.toFinset_cons,
                          Finset.mem_insert]; exact Or.inr (Or.inr hy))
                        (h2.1.resolve_left hA) hA (.head _)
                  refine hEg _ hlt (by
                      intro F' hF'
                      rcases List.mem_cons.mp hF' with rfl | hF'
                      · exact hSor h2.1
                      · exact hScons (hSor h2.2) _ hF') Δ (projE
                    (l := itpEcls p S F (c'' + 1) Γ) hsrc ?_)
                  simp only [itpEcls]
                  refine List.mem_append.mpr (Or.inr
                    (List.mem_flatMap.mpr ⟨A.and B, hF'Γ, ?_⟩))
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
                  have hA : A ∉ Γ := fun h => h1 (Or.inl h)
                  have hB : B ∉ Γ := fun h => h1 (Or.inr h)
                  refine consume₁ (projE
                    (l := itpEcls p S F (c'' + 1) Γ) hsrc ?_)
                    (or_mono
                      (hEg _ (defect_cons_lt h2.1 hA)
                        (hScons h2.1) _
                        (G4c.identity_mem (.head _)))
                      (hEg _ (defect_cons_lt h2.2 hB)
                        (hScons h2.2) _
                        (G4c.identity_mem (.head _))))
                  simp only [itpEcls]
                  refine List.mem_append.mpr (Or.inr
                    (List.mem_flatMap.mpr ⟨A.or B, hF'Γ, ?_⟩))
                  simp only
                  rw [if_neg h1, if_pos h2]
                  exact .head _
                next => cases hin
          | somehow χ =>
              exact absurd (hΓbf _ hF'Γ) (by simp [boxFree])
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
                        refine hEg _ (defect_cons_lt hBS hBΓ)
                          (hScons hBS) Δ (projE
                          (l := itpEcls p S F (c'' + 1) Γ) hsrc ?_)
                        simp only [itpEcls]
                        refine List.mem_append.mpr (Or.inr
                          (List.mem_flatMap.mpr ⟨(prop q).ifThen B, hF'Γ, ?_⟩))
                        simp only
                        rw [if_neg hBΓ, if_pos hBS, if_pos hq]
                        exact .head _
                      next hq =>
                        split at hin
                        next => cases hin
                        next hqp =>
                          rcases List.mem_singleton.mp hin with rfl
                          refine consume₁ (projE
                            (l := itpEcls p S F (c'' + 1) Γ) hsrc ?_)
                            (imp_mono (G4c.init (.head _))
                              (hEg _ (defect_cons_lt hBS hBΓ)
                                (hScons hBS) _
                                (G4c.identity_mem (.head _))))
                          simp only [itpEcls]
                          refine List.mem_append.mpr (Or.inr
                            (List.mem_flatMap.mpr
                              ⟨(prop q).ifThen B, hF'Γ, ?_⟩))
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
                      refine hEg _ (defect_cons_lt h2 h1)
                        (hScons h2) Δ (projE
                        (l := itpEcls p S F (c'' + 1) Γ) hsrc ?_)
                      simp only [itpEcls]
                      refine List.mem_append.mpr (Or.inr
                        (List.mem_flatMap.mpr
                          ⟨(A₁.and B₁).ifThen B, hF'Γ, ?_⟩))
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
                      have hlt : defect S (A₁.ifThen B :: B₁.ifThen B :: Γ) <
                          defect S Γ := by
                        by_cases hA : A₁.ifThen B ∈ Γ
                        · have hBn : B₁.ifThen B ∉ Γ := fun hB => h1 ⟨hA, hB⟩
                          exact defect_lt_of_mem
                            (Γ' := A₁.ifThen B :: B₁.ifThen B :: Γ)
                            (by intro y hy; simp only [List.toFinset_cons,
                              Finset.mem_insert]; exact Or.inr (Or.inr hy))
                            (h2.2.resolve_left hBn) hBn (.tail _ (.head _))
                        · exact defect_lt_of_mem
                            (Γ' := A₁.ifThen B :: B₁.ifThen B :: Γ)
                            (by intro y hy; simp only [List.toFinset_cons,
                              Finset.mem_insert]; exact Or.inr (Or.inr hy))
                            (h2.1.resolve_left hA) hA (.head _)
                      refine hEg _ hlt (by
                          intro F' hF'
                          rcases List.mem_cons.mp hF' with rfl | hF'
                          · exact hSor h2.1
                          · exact hScons (hSor h2.2) _ hF') Δ (projE
                        (l := itpEcls p S F (c'' + 1) Γ) hsrc ?_)
                      simp only [itpEcls]
                      refine List.mem_append.mpr (Or.inr
                        (List.mem_flatMap.mpr
                          ⟨(A₁.or B₁).ifThen B, hF'Γ, ?_⟩))
                      simp only
                      rw [if_neg h1, if_pos h2]
                      exact .head _
                    next => cases hin
              | ifThen A₁ B₁ =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next hDG =>
                    split at hin
                    next hDS =>
                      split at hin
                      next hBD =>
                        split at hin
                        next hABS =>
                          -- gated present piece: convert the antecedent
                          -- through the A-descent, fire, ascend
                          rcases List.mem_singleton.mp hin with rfl
                          have hd1s : 1 ≤ defect S Γ :=
                            Finset.card_pos.mpr ⟨B, Finset.mem_sdiff.mpr
                              ⟨hDS, fun h => hDG (List.mem_toFinset.mp h)⟩⟩
                          have hmul1 : 1 * ((jumpGoals S).card + 2) ≤
                              defect S Γ * ((jumpGoals S).card + 2) :=
                            Nat.mul_le_mul_right _ hd1s
                          refine G4c.impR ?_
                          have hJs : G4c ((itpE p S F (c'' + 1) Γ).ifThen
                              (itpA p S F (c'' + 1) Γ (A₁.ifThen B₁)) :: Δ)
                              ((itpE p S F c'' Γ).ifThen
                                (itpA p S F c'' Γ (A₁.ifThen B₁))) := by
                            refine G4c.impR ?_
                            refine hAd c'' (A₁.ifThen B₁) _
                              (himp hABS).1 (by omega) (hroomA _)
                              (weaken_sub (fun ψ h => .tail _ (.tail _ h))
                                (hsrcF (c'' + 1) (Nat.le_refl _))) ?_
                            exact fire (G4c.identity_mem (.tail _ (.head _)))
                              (weaken_sub (fun ψ h => .tail _ (.tail _ h))
                                (hsrcF (c'' + 1) (Nat.le_refl _)))
                          refine consume₁ (fire (projE
                            (l := itpEcls p S F (c'' + 1) Γ)
                            (hsrc.weaken _) ?_) hJs)
                            (hEg (B :: Γ) (defect_cons_lt hDS hDG)
                              (hScons hDS) _
                              (G4c.identity_mem (.head _)))
                          simp only [itpEcls]
                          refine List.mem_append.mpr (Or.inr
                            (List.mem_flatMap.mpr
                              ⟨(A₁.ifThen B₁).ifThen B, hF'Γ, ?_⟩))
                          simp only
                          rw [if_neg hDG, if_pos hDS, if_pos hBD, if_pos hABS]
                          exact .head _
                        next => cases hin
                      next hBD =>
                        split at hin
                        next hBDS =>
                          -- fresh piece: ascend the introduced guard,
                          -- fire, descend at the grown context
                          rcases List.mem_singleton.mp hin with rfl
                          refine G4c.impR ?_
                          have hJs : G4c ((itpE p S F (c'' + 2)
                              (B₁.ifThen B :: Γ)).ifThen
                              (itpA p S F (c'' + 2) (B₁.ifThen B :: Γ)
                                (A₁.ifThen B₁)) :: Δ)
                              ((itpE p S F (c'' + 1)
                                (B₁.ifThen B :: Γ)).ifThen
                                (itpA p S F (c'' + 1) (B₁.ifThen B :: Γ)
                                  (A₁.ifThen B₁))) := by
                            refine G4c.impR ?_
                            have hE2 : G4c (itpE p S F (c'' + 1)
                                (B₁.ifThen B :: Γ) ::
                                (itpE p S F (c'' + 2)
                                  (B₁.ifThen B :: Γ)).ifThen
                                (itpA p S F (c'' + 2) (B₁.ifThen B :: Γ)
                                  (A₁.ifThen B₁)) :: Δ)
                                (itpE p S F (c'' + 2)
                                  (B₁.ifThen B :: Γ)) :=
                              hEg _ (defect_cons_lt hBDS hBD)
                                (hScons hBDS) _
                                (G4c.identity_mem (.head _))
                            refine hAg _ (defect_cons_lt hBDS hBD)
                              (c'' + 1) (A₁.ifThen B₁) _
                              (himp (hΓS _ hF'Γ)).1
                              (hScons hBDS) (by omega)
                              (Nat.le_succ _) hE2 ?_
                            exact fire (G4c.identity_mem
                              (.tail _ (.head _))) hE2
                          refine consume₁ (fire (projE
                            (l := itpEcls p S F (c'' + 1) Γ)
                            (hsrc.weaken _) ?_) hJs)
                            (hEg (B :: Γ) (defect_cons_lt hDS hDG)
                              (hScons hDS) _
                              (G4c.identity_mem (.head _)))
                          simp only [itpEcls]
                          refine List.mem_append.mpr (Or.inr
                            (List.mem_flatMap.mpr
                              ⟨(A₁.ifThen B₁).ifThen B, hF'Γ, ?_⟩))
                          simp only
                          rw [if_neg hDG, if_pos hDS, if_neg hBD,
                            if_pos hBDS]
                          exact .head _
                        next => cases hin
                    next => cases hin
              | somehow A₁ =>
                  exact absurd (hΓbf _ hF'Γ) (by simp [boxFree])

/-- Stage-1 entry: the box-free pair descent at the holdout's own
room.  With `S` box-free and subformula-closed and the goal and
context inside `S`, no sealed position exists and the shifted-ledger
machine closes outright. -/
private theorem cascade_low_pos_boxfree (p : String) (S : Finset PLLFormula)
    (hSbf : ∀ F ∈ S, boxFree F)
    (hand : ∀ {A B : PLLFormula}, A.and B ∈ S → A ∈ S ∧ B ∈ S)
    (hor : ∀ {A B : PLLFormula}, A.or B ∈ S → A ∈ S ∧ B ∈ S)
    (himp : ∀ {A B : PLLFormula}, A.ifThen B ∈ S → A ∈ S ∧ B ∈ S)
    (fh : Nat) (Γ : List PLLFormula) (fuel c : Nat) (g : PLLFormula)
    (Δ : List PLLFormula)
    (hgS : g ∈ S) (hΓS : ∀ F ∈ Γ, F ∈ S)
    (hroom : defect S Γ * ((jumpGoals S).card + 2) ≤ c)
    (hc : 1 ≤ c)
    (hamb : G4c Δ (itpE p S fuel (c + 1) Γ))
    (hhead : G4c Δ (itpA p S fh (c + 1) Γ g))
    (hfh : fh ≤ fuel) :
    G4c Δ (itpA p S fuel c Γ g) := by
  refine (cascade_main_bf p S hSbf hand hor himp (defect S Γ) fh).1
    Γ fuel c g {g} Δ _ (Nat.le_refl _) hgS hΓS
    (Finset.mem_singleton_self g) hc ?_ ?_ hamb hhead hfh
  · have hcard := Finset.card_le_card
      (Finset.sdiff_subset (s := jumpGoals S) (t := {g}))
    omega
  · intro g' hg' Δ' _ hval
    rcases Finset.mem_singleton.mp hg' with rfl
    exact hval

/-- HOLDOUT — the one remaining `sorry` of the cascade development,
now restricted to the ◯-involving band: by the dispatcher below it
carries, besides `1 ≤ defect S Γ`, the negation `hbox` — some member
of `S` mentions `◯`, or `S` is not subformula-closed, or the goal or
context escapes `S`.  In the complementary (box-free, closed,
covered) instance the descent is a THEOREM (`cascade_low_pos_boxfree`
via `cascade_main_bf`): there are no ◯-clauses, hence no sealed
positions, and the shifted ledger runs the full pigeonhole machine
from this statement's own room.

Stage-3 note (fuel-indifference, `wip/indiff.lean`): re-leveling
fuels above `mu` is an `Eq` in the FUEL dimension; the seal deficit
is in the BUDGET dimension (the seen-discounted room), which
indifference cannot touch — and removing the fuel descent removes the
only decreasing measure the seal-nesting had, so it does not re-fund
the ◯-band either.

The ambient-relative pair descent at *burned* room: only the defect
tower (`defect·(J+2) ≤ c`, `J = |jumpGoals S|`) survives at the call
sites, not the fresh-chain allotment `J+1+defect·(J+2) ≤ c` that
`cascade_main`'s pigeonhole machinery needs at entry.

Consumed from exactly four *sealed* positions inside `cascade_main`'s
A-half, all of shape "the target disjunct must be introduced before
the inner descent runs", so the sequent's conclusion becomes the inner
*value* rather than the fixed outer `R`, and the seen-set
continuations (which conclude `R`) cannot cross:

* the goal-γ disjunct `◯(E ⇢ A(Γ, D))` (laxL demands a ◯-goal — the
  target box must be committed first);
* the clause-γ-head component `◯(E ⇢ A(Γ, ◯A₁))` (same seal);
* the truncation disjunct (same seal, whole-head rebuild);
* the fresh-antecedent goal implication with the new piece outside
  `S` (the impR seals; the defect does not pay).

What was tried (2026-07-11, this session): (a) inheriting the
seen-set across the seal — semantically impossible: continuations
conclude `R`, the sealed obligation is a value, and no g′-value
derives a differently-goaled value; (b) splicing the sealed repeat
into the inner root's own jump disjunct — fails on the second
component (needs the inner goal at a grown context, unavailable);
(c) charging the ledger more per burn — fails because seal-crossing
resets are fuel-indexed, not S-indexed, so no Γ-computable `kcap`
covers chains-of-seals; (d) box-proof continuation interfaces —
circular.  The residual mathematical content: chains restarted inside
a seal revisit jump goals whose pending slots are outside the box, so
the pigeonhole cannot close them; empirically budgets stabilise at
`b ≈ 2–3` regardless (probe battery, `wip/v3probe*.lean`), so this
statement is believed true — it is exactly the one-step budget
stabilisation at low budget, the open frontier of the development.

Direct semantic adjudication of THIS statement (2026-07-11, session
scratchpad, `v3probe2`'s 7-algebra zoo on the real `itpA`/`itpE`):
zero counterexample points on two adversarial defect-1 configurations
— `S = {◯p⊃r, r}`, `Γ = [◯p⊃r]` (J = 2), and the shared-consequent
pair `S = {◯p⊃r, ◯p₂⊃r, r}` (J = 4, the shape whose live-jump-goal
count exceeds every defect bound, i.e. the worst case for any
defect-indexed ledger) — across goal shapes `p`, `◯p`, `p⊃r`, `◯r`,
`◯(◯p∧r)`, `◯r⊃p` and eliminated atoms absent/live/consequent, at
budgets both in the open band and far below the floor (`c = 1, 2`).
A refutation would have voided the design; none was found.  (The
kernel decider was also pointed at the smallest instance and killed
at a 20-minute cap — its search space is infeasible even there, as
`HANDOFF.md` warns; the zoo is the effective adjudicator.)
The `defect S Γ = 0` band is settled (`cascade_zero` above: every
space-guarded clause is dead and the plain fuel induction closes), so
this statement now carries `1 ≤ defect S Γ` — the open band only.

Two structural leads adjudicated 2026-07-11 (evening):

* **Piece-closure kills the fourth site — but only for closed `S`.**
  If `S` is subformula-closed, a goal-membership invariant `g ∈ S`
  threads through every recursion of `cascade_main` (entry goals are
  antecedent/body pieces of `S`-clauses; decomposition, `C₂`,
  γ-unboxing and carried goals preserve it), and then a fresh goal
  antecedent outside `S` is impossible — the fresh-antecedent seal is
  dead code.  This CANNOT be used here: the three interface lemmas
  quantify over arbitrary `S`, and for non-closed `S` the site is
  reachable at depth 0 (goal `A₁⊃B₁` with `A₁ ∉ Γ ∪ S`).  The
  downstream adequacy instantiation uses the piece-closed space, so a
  closed-`S` variant of this lemma would face only the three ◯-seals;
  recorded for the consumer, not usable for the ∀`S` statements.
* **The ◯-goal specialization is a circular reduction.**  Landing the
  target's truncation disjunct keeps the goal ◯-shaped through every
  box (laxL/`box_fire` need no fresh seen-allotment for the crossing
  itself), and the collapse+re-import moves reduce the γ-family seals
  to: inner descents at strictly smaller goals (weight-paying),
  pointwise `others`-maps (fuel-paying), and the jump-env first
  components at `(c → c−1)` — which are again pair descents at
  arbitrary-shaped jump goals at burned room, i.e. THIS statement one
  budget down.  No measure decreases across that residue (jump goals
  reset weight and ◯-depth; `c` burns without pigeonhole room), so
  the specialization re-derives what the seen-machinery already gives
  above the threshold and cannot close the band below it.

Guarded/consumed reshaping campaign (2026-07-12; zoo file
`wip/refute4.lean` — 34-pair exhaustive-nuclei zoo; engines
`box_remap`/`box_reguard` above).  The task-#13 transfer hypothesis
(guardMP's consumed form admissible where retained fails; Pitts'
guarded `L4→` provable where Iemhoff's unguarded needs cut) was
adjudicated against these seals.  Verdict — the analogy breaks for an
identified structural reason, and the obstruction is now sharper:

* **What crosses a seal is machine-delimited** (`box_remap`): the
  inner obligation receives the opened source body, the target
  guard, and the ENTIRE outer context — every formula-shaped
  resource crosses (laxL retains contexts); only the seen-set
  continuations (meta-level, concluding the outer `R`) do not.
  Guarded-engine candidates therefore repackage the same inner
  sequent.  At same-context seals every reachable guard is
  budget-mono-DOMINATED by the ambient (`E@(c+1) ⊢ E@c ⊢ E@(c−1)`
  pointwise): machine-checked by Z6 ≡ Z1 at the failing point.
  `box_reguard` (Z2b) is the (A)-family survivor — guard plumbing
  with the ambient outside the box; it leaves the value map intact.
* **The floor is a ledger artifact on the A-side** (Z1): the BARE
  descent with only `1 ≤ c` is zoo-true at every probed
  configuration and budget `c ≥ 1` — defect 1 and 2, J ∈ {1,2,4},
  chained (`S={◯p⊃r,r,◯r⊃s,s}`, floor 12) and shared-consequent
  (`S={◯p⊃r,◯p₂⊃r,r}`, floor 6) jump structures, mostly with zero
  slack — and zoo-FALSE at exactly the structural point
  (◯-shaped goal, `c = 0`), where the target table is empty (goal
  clause and truncation both b-gated: `A@0(Γ,◯D) = ⊥` — literally,
  since `orAll [] = ⊥`).
* **But the E-mate genuinely fails low** (Z8): the floorless ascent
  `E@c ⊢ E@(c+1)` is zoo-REFUTED at (chained-d2, `c = 1`) — witness
  chain3, nucleus `[0,2,2]`, `v(r)=v(s)=1` — while true at `c ≥ 2`
  there.  So the mutual-pair decomposition (the only known proof
  scheme) is closed off below `c = 2` by countermodel, independent
  of the seal problem; the A-band's truth at `c = 1` does not
  decompose through the pair.
* **Why the Pitts/guardMP analogy breaks**: her guards are
  ANTECEDENT-side — weakening carries hypotheses across any commit,
  which is exactly why consumed forms close.  The seal deficit is
  SUCCEDENT-side-under-◯: continuations are conclusion-anchored
  (they conclude the outer disjunction `R`, strictly weaker than
  the single ◯-disjunct a seal must produce), and formula-shaped
  stand-ins fail — in-context oracles `(value ⇢ R)` fire to the
  wrong conclusion inside a seal, and budget-family oracles
  `⋀_{β≤c}(A@(β+1) ⇢ A@β)` are the stabilization ladder itself.
  Ledger-raising cannot compensate: entry `… + X` funds seals to
  `defect·(J+2)+X ≤ c−1` while the raised holdout would need
  `J+1+defect·(J+2)+X ≤ c−1` — short by `J+1` for every `X`.
* **The fresh-antecedent seal's law is semantically FREE** (Z5):
  `E@(c+1)(Γ) ⊓ E@c(C₁::Γ) = E@(c+1)(C₁::Γ)` with EQUALITY on the
  zoo at every probed instance (`C₁ ∈ {u, u⊃r, ◯u}`, at and below
  the floor, including the moving-E chained-d2 config where the
  bare E-ascent fails).  A proof of Z5 would kill the fourth seal (the one
  with no decreasing measure) without the whole-head rebuild; its
  γ-conjunct conversions recurse into the A-descent at `c−1`, i.e.
  into this statement — same knot, but now with a zoo-true target.
* **Identified residue** (the sharpest known formulation): a
  low-band A-lemma — this statement's conclusion from `1 ≤ c` alone
  — is TRUE on the zoo; the known decompositions cannot reach it
  (chains hit the (◯-goal, 0) false point; the E-mate fails at 1;
  continuations cannot cross seals).  The mechanism the semantics
  uses at `c = 1` is SYNTACTIC starvation: b-gated tables at
  saturated/grown contexts collapse to literal `⊥` (`orAll [] = ⊥`),
  e.g. `A@1(Γ,p) ⊢ ⊥` at the canonical config, killing every pair
  disjunct whose partner starves.  A future development would prove
  starvation-collapse lemmas (which `(Γ, g, b)` starve) plus a
  `(defect, budget)`-lex landing map for the `c = 1` base, meeting
  the pigeonhole band from below — cascade_main-scale work, not
  attempted here. -/
private theorem cascade_low_pos_box (p : String) (S : Finset PLLFormula)
    (fh : Nat) (Γ : List PLLFormula) (fuel c : Nat) (g : PLLFormula)
    (Δ : List PLLFormula)
    (hbox : ¬ ((∀ F ∈ S, boxFree F) ∧
      (∀ A B : PLLFormula, A.and B ∈ S → A ∈ S ∧ B ∈ S) ∧
      (∀ A B : PLLFormula, A.or B ∈ S → A ∈ S ∧ B ∈ S) ∧
      (∀ A B : PLLFormula, A.ifThen B ∈ S → A ∈ S ∧ B ∈ S) ∧
      g ∈ S ∧ (∀ F ∈ Γ, F ∈ S)))
    (hd1 : 1 ≤ defect S Γ)
    (hroom : defect S Γ * ((jumpGoals S).card + 2) ≤ c)
    (hamb : G4c Δ (itpE p S fuel (c + 1) Γ))
    (hhead : G4c Δ (itpA p S fh (c + 1) Γ g))
    (hfh : fh ≤ fuel) :
    G4c Δ (itpA p S fuel c Γ g) := by
  sorry

/-- The open-band descent, dispatched: the box-free/closed/covered
instance is settled by `cascade_low_pos_boxfree`; the rest is the
◯-involving (or space-uncovered) holdout `cascade_low_pos_box`. -/
private theorem cascade_low_pos (p : String) (S : Finset PLLFormula)
    (fh : Nat) (Γ : List PLLFormula) (fuel c : Nat) (g : PLLFormula)
    (Δ : List PLLFormula)
    (hd1 : 1 ≤ defect S Γ)
    (hroom : defect S Γ * ((jumpGoals S).card + 2) ≤ c)
    (hamb : G4c Δ (itpE p S fuel (c + 1) Γ))
    (hhead : G4c Δ (itpA p S fh (c + 1) Γ g))
    (hfh : fh ≤ fuel) :
    G4c Δ (itpA p S fuel c Γ g) := by
  have hc : 1 ≤ c := by
    have hmul1 : 1 * ((jumpGoals S).card + 2) ≤
        defect S Γ * ((jumpGoals S).card + 2) :=
      Nat.mul_le_mul_right _ hd1
    omega
  by_cases hbf : (∀ F ∈ S, boxFree F) ∧
      (∀ A B : PLLFormula, A.and B ∈ S → A ∈ S ∧ B ∈ S) ∧
      (∀ A B : PLLFormula, A.or B ∈ S → A ∈ S ∧ B ∈ S) ∧
      (∀ A B : PLLFormula, A.ifThen B ∈ S → A ∈ S ∧ B ∈ S) ∧
      g ∈ S ∧ (∀ F ∈ Γ, F ∈ S)
  · exact cascade_low_pos_boxfree p S hbf.1
      (fun {A B} => hbf.2.1 A B) (fun {A B} => hbf.2.2.1 A B)
      (fun {A B} => hbf.2.2.2.1 A B) fh Γ fuel c g Δ
      hbf.2.2.2.2.1 hbf.2.2.2.2.2 hroom hc hamb hhead hfh
  · exact cascade_low_pos_box p S fh Γ fuel c g Δ hbf hd1 hroom
      hamb hhead hfh

/-- The sealed-site descent: saturated contexts settle by the
zero tier, the rest is the holdout. -/
private theorem cascade_low (p : String) (S : Finset PLLFormula)
    (fh : Nat) (Γ : List PLLFormula) (fuel c : Nat) (g : PLLFormula)
    (Δ : List PLLFormula)
    (hc : 1 ≤ c) (hroom : defect S Γ * ((jumpGoals S).card + 2) ≤ c)
    (hamb : G4c Δ (itpE p S fuel (c + 1) Γ))
    (hhead : G4c Δ (itpA p S fh (c + 1) Γ g))
    (hfh : fh ≤ fuel) :
    G4c Δ (itpA p S fuel c Γ g) := by
  by_cases hd0 : defect S Γ = 0
  · exact cascade_zero p S fh Γ (sat_of_defect_zero hd0) fuel c g Δ hc
      hamb hhead hfh
  · exact cascade_low_pos p S fh Γ fuel c g Δ (by omega) hroom hamb
      hhead hfh

private theorem cascade_main (p : String) (S : Finset PLLFormula) :
    ∀ (d fh : Nat),
    (∀ (Γ : List PLLFormula) (fuel c : Nat) (g : PLLFormula)
       (seen : Finset PLLFormula) (Δ : List PLLFormula) (R : PLLFormula),
     defect S Γ ≤ d → g ∈ seen →
     ((jumpGoals S \ seen).card + 1 +
       defect S Γ * ((jumpGoals S).card + 2) ≤ c) →
     (∀ g' ∈ seen, ∀ Δ', (∀ ψ ∈ Δ, ψ ∈ Δ') →
       G4c Δ' (itpA p S fuel c Γ g') → G4c Δ' R) →
     G4c Δ (itpE p S fuel (c + 1) Γ) →
     G4c Δ (itpA p S fh (c + 1) Γ g) →
     fh ≤ fuel →
     G4c Δ R) ∧
    (∀ (Γ : List PLLFormula) (c : Nat) (Δ : List PLLFormula),
     defect S Γ ≤ d →
     ((jumpGoals S).card + 3 +
       defect S Γ * ((jumpGoals S).card + 2) ≤ c) →
     G4c Δ (itpE p S fh c Γ) →
     G4c Δ (itpE p S fh (c + 1) Γ)) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ihd =>
  intro fh
  induction fh with
  | zero =>
      constructor
      · intro Γ fuel c g seen Δ R hd hg hroom hcls hamb hhead hfh
        simp only [itpA] at hhead
        exact G4c.cut hhead (G4c.botL (.head _))
      · intro Γ c Δ hd hroom hsrc
        simp only [itpE]
        exact G4c.truePLL_intro _
  | succ F ihf =>
      obtain ⟨ihfA, ihfE⟩ := ihf
      constructor
      · -- A-half: the descent cascade
        intro Γ fuel c g seen Δ R hd hg hroom hcls hamb hhead hfh
        obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
        obtain ⟨fl, rfl⟩ : ∃ fl, fuel = fl + 1 := ⟨fuel - 1, by omega⟩
        rw [itpA_succ p S F (c' + 2) Γ g] at hhead
        have hF : F ≤ fl := Nat.succ_le_succ_iff.mp hfh
        -- lowered ambient at any weaker fuel/budget
        have hambL : ∀ (f' b' : Nat), f' ≤ fl + 1 → b' ≤ c' + 2 →
            G4c Δ (itpE p S f' b' Γ) := fun f' b' hf hb =>
          consume₁ (consume₁ hamb ((itp_fuel_mono_le p S hf).1 _ Γ))
            ((itp_budget_mono_le p S hb f').1 Γ)
        -- weak rooms for the sealed sites
        have hroomW : defect S Γ * ((jumpGoals S).card + 2) ≤ c' + 1 := by
          omega
        have hroomW0 : defect S Γ * ((jumpGoals S).card + 2) ≤ c' := by
          omega
        -- target-disjunct introduction at the reference-fuel table: a
        -- derivation of any member of the target table closes R
        have hfinT : ∀ (Δ' : List PLLFormula), (∀ ψ ∈ Δ, ψ ∈ Δ') →
            ∀ (ψ : PLLFormula), ψ ∈ itpAfull p S fl (c' + 1) Γ g →
            G4c Δ' ψ → G4c Δ' R := by
          intro Δ' hs ψ hmem dψ
          refine hcls g hg Δ' hs ?_
          rw [itpA_succ]
          exact G4c.orAll_intro hmem dψ
        -- room after a neutral seen-insertion (nested same-pair calls)
        have hroomI : ∀ (x : PLLFormula),
            (jumpGoals S \ insert x seen).card + 1 +
              defect S Γ * ((jumpGoals S).card + 2) ≤ c' + 1 :=
          fun x => le_trans (Nat.add_le_add_right (Nat.add_le_add_right
            (Finset.card_le_card (Finset.sdiff_subset_sdiff
              (Finset.Subset.refl _) (Finset.subset_insert _ _))) 1) _) hroom
        -- room after a paying seen-insertion (jump recursion, c drops)
        have hroomJ : ∀ (x : PLLFormula), x ∈ jumpGoals S → x ∉ seen →
            (jumpGoals S \ insert x seen).card + 1 +
              defect S Γ * ((jumpGoals S).card + 2) ≤ c' := by
          intro x hxJ hxs
          have h1 : (jumpGoals S \ insert x seen).card <
              (jumpGoals S \ seen).card := by
            refine Finset.card_lt_card ⟨Finset.sdiff_subset_sdiff
              (Finset.Subset.refl _) (Finset.subset_insert _ _), ?_⟩
            intro hsub
            have h2 := hsub (Finset.mem_sdiff.mpr ⟨hxJ, hxs⟩)
            rw [Finset.mem_sdiff] at h2
            exact h2.2 (Finset.mem_insert_self _ _)
          omega
        -- restated continuations for same-context nested calls
        have hclsR : ∀ (Δ₀ : List PLLFormula), (∀ ψ ∈ Δ, ψ ∈ Δ₀) →
            ∀ g' ∈ seen, ∀ Δ', (∀ ψ ∈ Δ₀, ψ ∈ Δ') →
            G4c Δ' (itpA p S fl (c' + 1) Γ g') → G4c Δ' R :=
          fun Δ₀ h0 g' hg' Δ' hs val =>
            hcls g' hg' Δ' (fun ψ h => hs ψ (h0 ψ h))
              (val_lift val (Nat.le_succ fl) (Nat.le_refl _))
        -- grown-context full descent: the strong induction on defect
        have hgrown : ∀ (Γ' : List PLLFormula), defect S Γ' < defect S Γ →
            ∀ (fw c₂ : Nat) (h : PLLFormula) (Δ' : List PLLFormula),
            ((jumpGoals S).card + 1 +
              defect S Γ' * ((jumpGoals S).card + 2) ≤ c₂) →
            G4c Δ' (itpE p S fw (c₂ + 1) Γ') →
            G4c Δ' (itpA p S fw (c₂ + 1) Γ' h) →
            G4c Δ' (itpA p S fw c₂ Γ' h) := by
          intro Γ' hlt fw c₂ h Δ' hroom' hamb' hhead'
          refine (ihd (defect S Γ') (lt_of_lt_of_le hlt hd) fw).1 Γ' fw c₂ h
            {h} Δ' _ (Nat.le_refl _) (Finset.mem_singleton_self h) ?_ ?_
            hamb' hhead' (Nat.le_refl _)
          · exact le_trans (Nat.add_le_add_right (Nat.add_le_add_right
              (Finset.card_le_card Finset.sdiff_subset) 1) _) hroom'
          · intro g' hg' Δ'' _ hval
            rcases Finset.mem_singleton.mp hg' with rfl
            exact hval
        -- room arithmetic for a defect-paying descent
        have hroomG : ∀ (Γ' : List PLLFormula), defect S Γ' < defect S Γ →
            (jumpGoals S).card + 1 +
              defect S Γ' * ((jumpGoals S).card + 2) ≤ c' + 1 := by
          intro Γ' hlt
          have hexp : (defect S Γ' + 1) * ((jumpGoals S).card + 2) =
              defect S Γ' * ((jumpGoals S).card + 2) +
              ((jumpGoals S).card + 2) := by ring
          have hmul : (defect S Γ' + 1) * ((jumpGoals S).card + 2) ≤
              defect S Γ * ((jumpGoals S).card + 2) :=
            Nat.mul_le_mul_right _ (by omega)
          omega
        have hroomE : ∀ (Γ' : List PLLFormula), defect S Γ' < defect S Γ →
            (jumpGoals S).card + 3 +
              defect S Γ' * ((jumpGoals S).card + 2) ≤ c' + 1 := by
          intro Γ' hlt
          have hexp : (defect S Γ' + 1) * ((jumpGoals S).card + 2) =
              defect S Γ' * ((jumpGoals S).card + 2) +
              ((jumpGoals S).card + 2) := by ring
          have hmul : (defect S Γ' + 1) * ((jumpGoals S).card + 2) ≤
              defect S Γ * ((jumpGoals S).card + 2) :=
            Nat.mul_le_mul_right _ (by omega)
          omega
        -- guarded-implication component descent at a paying piece: the
        -- introduced target guard ascends by the E-half, fires the
        -- source, and the value descends by the defect induction
        have himpX : ∀ (X h : PLLFormula) (Δ' : List PLLFormula),
            defect S (X :: Γ) < defect S Γ →
            G4c Δ' ((itpE p S F (c' + 2) (X :: Γ)).ifThen
              (itpA p S F (c' + 2) (X :: Γ) h)) →
            G4c Δ' ((itpE p S fl (c' + 1) (X :: Γ)).ifThen
              (itpA p S fl (c' + 1) (X :: Γ) h)) := by
          intro X h Δ' hlt dJ
          refine G4c.impR ?_
          have hE2 : G4c (itpE p S fl (c' + 1) (X :: Γ) :: Δ')
              (itpE p S fl (c' + 2) (X :: Γ)) :=
            (ihd (defect S (X :: Γ)) (lt_of_lt_of_le hlt hd) fl).2 (X :: Γ)
              (c' + 1) _ (Nat.le_refl _) (hroomE (X :: Γ) hlt)
              (G4c.identity_mem (.head _))
          refine hgrown (X :: Γ) hlt fl (c' + 1) h _ (hroomG (X :: Γ) hlt)
            hE2 ?_
          refine val_lift (b := c' + 2) ?_ hF (Nat.le_refl _)
          exact fire (dJ.weaken _) (consume₁ hE2
            ((itp_fuel_mono_le p S hF).1 _ _))
        -- the per-disjunct branch analysis
        have hGOAL : ∀ φ ∈ itpAgoal p S F (c' + 2) Γ g, G4c (φ :: Δ) R := by
          intro φ hφ
          cases g with
          | prop q =>
              simp only [itpAgoal] at hφ
              split at hφ
              next => cases hφ
              next hq =>
                rcases List.mem_singleton.mp hφ with rfl
                refine hfinT _ (fun χ h => .tail _ h) (prop q) ?_
                  (G4c.init (.head _))
                simp only [itpAfull, itpAoth, itpAgoal]
                rw [if_neg hq]
                exact List.mem_append.mpr (Or.inl (.head _))
          | falsePLL => simp only [itpAgoal] at hφ; cases hφ
          | and C₁ C₂ =>
              simp only [itpAgoal] at hφ
              rcases List.mem_singleton.mp hφ with rfl
              refine G4c.andL (List.Perm.refl _) ?_
              -- V₁ :: V₂ :: Δ ⊢ R, CPS-chained through both components
              refine ihfA Γ fl (c' + 1) C₁ (insert C₁ seen) _ R hd
                (Finset.mem_insert_self _ _) (hroomI C₁) ?_
                (((hambL fl (c' + 2) (Nat.le_succ _)
                  (Nat.le_refl _)).weaken _).weaken _)
                (G4c.identity_mem (.head _)) hF
              intro g' hg' Δ' hs' val₁
              rcases Finset.mem_insert.mp hg' with rfl | hg'
              · -- C₁ landed: chain into C₂
                refine ihfA Γ fl (c' + 1) C₂ (insert C₂ seen) Δ' R hd
                  (Finset.mem_insert_self _ _) (hroomI C₂) ?_
                  (weaken_sub (fun ψ h => hs' ψ (.tail _ (.tail _ h)))
                    (hambL fl (c' + 2) (Nat.le_succ _) (Nat.le_refl _)))
                  (G4c.identity_mem (hs' _ (.tail _ (.head _)))) hF
                intro g'' hg'' Δ'' hs'' val₂
                rcases Finset.mem_insert.mp hg'' with rfl | hg''
                · -- both landed: assemble the target conjunction
                  refine hfinT Δ''
                    (fun ψ h => hs'' ψ (hs' ψ (.tail _ (.tail _ h)))) _ ?_
                    (G4c.andR (weaken_sub hs'' val₁) val₂)
                  simp only [itpAfull, itpAoth, itpAgoal]
                  exact List.mem_append.mpr (Or.inl (.head _))
                · exact hclsR Δ' (fun ψ h => hs' ψ (.tail _ (.tail _ h)))
                    g'' hg'' Δ'' hs'' val₂
              · exact hclsR _ (fun ψ h => .tail _ (.tail _ h)) g' hg' Δ' hs'
                  val₁
          | or C₁ C₂ =>
              simp only [itpAgoal] at hφ
              rcases List.mem_cons.mp hφ with rfl | hφ'
              · refine ihfA Γ fl (c' + 1) C₁ (insert C₁ seen) _ R hd
                  (Finset.mem_insert_self _ _) (hroomI C₁) ?_
                  ((hambL fl (c' + 2) (Nat.le_succ _)
                    (Nat.le_refl _)).weaken _)
                  (G4c.identity_mem (.head _)) hF
                intro g' hg' Δ' hs' val
                rcases Finset.mem_insert.mp hg' with rfl | hg'
                · refine hfinT Δ' (fun ψ h => hs' ψ (.tail _ h)) _ ?_ val
                  simp only [itpAfull, itpAoth, itpAgoal]
                  exact List.mem_append.mpr (Or.inl (.head _))
                · exact hclsR _ (fun ψ h => .tail _ h) g' hg' Δ' hs' val
              · rcases List.mem_singleton.mp hφ' with rfl
                refine ihfA Γ fl (c' + 1) C₂ (insert C₂ seen) _ R hd
                  (Finset.mem_insert_self _ _) (hroomI C₂) ?_
                  ((hambL fl (c' + 2) (Nat.le_succ _)
                    (Nat.le_refl _)).weaken _)
                  (G4c.identity_mem (.head _)) hF
                intro g' hg' Δ' hs' val
                rcases Finset.mem_insert.mp hg' with rfl | hg'
                · refine hfinT Δ' (fun ψ h => hs' ψ (.tail _ h)) _ ?_ val
                  simp only [itpAfull, itpAoth, itpAgoal]
                  exact List.mem_append.mpr (Or.inl (.tail _ (.head _)))
                · exact hclsR _ (fun ψ h => .tail _ h) g' hg' Δ' hs' val
          | ifThen C₁ C₂ =>
              simp only [itpAgoal] at hφ
              split at hφ
              next hpres =>
                -- present antecedent: congr-transferred CPS descent
                rcases List.mem_singleton.mp hφ with rfl
                have hset : (C₁ :: Γ).toFinset = Γ.toFinset := by
                  rw [List.toFinset_cons]
                  exact Finset.insert_eq_self.mpr (List.mem_toFinset.mpr hpres)
                have hdef : defect S (C₁ :: Γ) = defect S Γ :=
                  defect_cons_eq hpres
                refine ihfA (C₁ :: Γ) fl (c' + 1) C₂ (insert C₂ seen) _ R
                  (by rw [hdef]; exact hd) (Finset.mem_insert_self _ _)
                  (by rw [hdef]; exact hroomI C₂) ?_
                  ((amb_congr (hambL fl (c' + 2) (Nat.le_succ _)
                    (Nat.le_refl _)) hpres).weaken _)
                  (fire (G4c.identity_mem (.head _))
                    ((amb_congr (hambL F (c' + 1)
                      (le_trans hF (Nat.le_succ _))
                      (Nat.le_succ _)) hpres).weaken _)) hF
                intro g' hg' Δ' hs' val
                rcases Finset.mem_insert.mp hg' with rfl | hg'
                · refine hfinT Δ' (fun ψ h => hs' ψ (.tail _ h)) _ ?_
                    (G4c.impR (val.weaken (itpE p S fl c' (C₁ :: Γ))))
                  simp only [itpAfull, itpAoth, itpAgoal]
                  rw [if_pos hpres]
                  exact List.mem_append.mpr (Or.inl (.head _))
                · exact hclsR _ (fun ψ h => .tail _ h) g' hg' Δ' hs'
                    (consume₁ val ((itp_congr p S fl).2 (c' + 1)
                      (C₁ :: Γ) Γ g' hset))
              next hpres =>
                -- fresh antecedent
                rcases List.mem_singleton.mp hφ with rfl
                by_cases hC₁S : C₁ ∈ S
                · -- the new piece pays: guard ascent by the E-half,
                  -- component descent by the defect induction
                  have hlt : defect S (C₁ :: Γ) < defect S Γ :=
                    defect_cons_lt hC₁S hpres
                  refine hfinT _ (fun χ h => .tail _ h)
                    ((itpE p S fl (c' + 1) (C₁ :: Γ)).ifThen
                      (itpA p S fl (c' + 1) (C₁ :: Γ) C₂)) ?_ (G4c.impR ?_)
                  · simp only [itpAfull, itpAoth, itpAgoal]
                    rw [if_neg hpres]
                    exact List.mem_append.mpr (Or.inl (.head _))
                  · -- W :: φ :: Δ ⊢ the descended component at C₁ :: Γ
                    have hE2 : G4c (itpE p S fl (c' + 1) (C₁ :: Γ) ::
                        (itpE p S F (c' + 2) (C₁ :: Γ)).ifThen
                          (itpA p S F (c' + 2) (C₁ :: Γ) C₂) :: Δ)
                        (itpE p S fl (c' + 2) (C₁ :: Γ)) :=
                      (ihd (defect S (C₁ :: Γ))
                          (lt_of_lt_of_le hlt hd) fl).2 (C₁ :: Γ) (c' + 1) _
                        (Nat.le_refl _) (hroomE _ hlt)
                        (G4c.identity_mem (.head _))
                    have hV : G4c (itpE p S fl (c' + 1) (C₁ :: Γ) ::
                        (itpE p S F (c' + 2) (C₁ :: Γ)).ifThen
                          (itpA p S F (c' + 2) (C₁ :: Γ) C₂) :: Δ)
                        (itpA p S F (c' + 2) (C₁ :: Γ) C₂) :=
                      fire (G4c.identity_mem (.tail _ (.head _)))
                        (consume₁ hE2 ((itp_fuel_mono_le p S hF).1 _ _))
                    exact hgrown (C₁ :: Γ) hlt fl (c' + 1) C₂ _
                      (hroomG _ hlt) hE2 (val_lift hV hF (Nat.le_refl _))
                · -- the new piece does not pay: sealed; rebuild the full
                  -- head from this disjunct and descend whole
                  refine hcls _ hg _ (fun χ h => .tail _ h) ?_
                  refine cascade_low p S (F + 1) Γ (fl + 1) (c' + 1) _ _
                    (by omega) hroomW
                    ((hambL (fl + 1) (c' + 2) (Nat.le_refl _)
                      (Nat.le_refl _)).weaken _) ?_ hfh
                  rw [itpA_succ]
                  refine G4c.orAll_intro
                    (l := itpAfull p S F (c' + 2) Γ (C₁.ifThen C₂)) ?_
                    (G4c.identity_mem (.head _))
                  refine mem_itpAfull_of_oth ?_
                  simp only [itpAoth, itpAgoal]
                  refine List.mem_append.mpr (Or.inl ?_)
                  rw [if_neg hpres]
                  exact .head _
          | somehow D =>
              -- the ◯-goal disjunct: sealed box crossing
              simp only [itpAgoal] at hφ
              rcases List.mem_singleton.mp hφ with rfl
              refine hfinT _ (fun χ h => .tail _ h)
                (((itpE p S fl c' Γ).ifThen
                  (itpA p S fl (c' + 1) Γ D)).somehow) ?_ ?_
              · simp only [itpAfull, itpAoth, itpAgoal]
                exact List.mem_append.mpr (Or.inl (List.mem_append.mpr
                  (Or.inl (.head _))))
              · refine box_fire (W := (itpE p S fl c' Γ).ifThen
                    (itpA p S fl (c' + 1) Γ D))
                  (G4c.identity_mem (.head _))
                  ((hambL F (c' + 1) (le_trans hF (Nat.le_succ _))
                    (Nat.le_succ _)).weaken _) ?_
                refine G4c.laxR (G4c.impR ?_)
                exact cascade_low p S F Γ fl (c' + 1) D _ (by omega) hroomW
                  (weaken_sub (fun ψ h => .tail _ (.tail _ (.tail _ h)))
                    (hambL fl (c' + 2) (Nat.le_succ _) (Nat.le_refl _)))
                  (G4c.identity_mem (.tail _ (.head _))) hF
        have hENV : ∀ φ ∈ itpAenv p S F (c' + 2) Γ g, G4c (φ :: Δ) R := by
          intro φ hφ
          simp only [itpAenv] at hφ
          obtain ⟨F', hF'Γ, hin⟩ := List.mem_flatMap.mp hφ
          have hsub1 : ∀ ψ ∈ Δ, ψ ∈ φ :: Δ := fun ψ h => .tail _ h
          cases F' with
          | prop q =>
              simp only at hin
              split at hin
              next hq =>
                rcases List.mem_singleton.mp hin with rfl
                refine hfinT _ hsub1 truePLL ?_ (G4c.truePLL_intro _)
                refine mem_itpAfull_of_oth ?_
                simp only [itpAoth]
                refine List.mem_append.mpr (Or.inr ?_)
                simp only [itpAenv]
                refine List.mem_flatMap.mpr ⟨prop q, hF'Γ, ?_⟩
                simp only
                rw [if_pos hq]
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
                  have hlt : defect S (A :: B :: Γ) < defect S Γ := by
                    by_cases hA : A ∈ Γ
                    · have hB : B ∉ Γ := fun hB => h1 ⟨hA, hB⟩
                      exact defect_lt_of_mem (Γ' := A :: B :: Γ)
                        (by intro y hy; simp only [List.toFinset_cons,
                          Finset.mem_insert]; exact Or.inr (Or.inr hy))
                        (h2.2.resolve_left hB) hB
                        (.tail _ (.head _))
                    · exact defect_lt_of_mem (Γ' := A :: B :: Γ)
                        (by intro y hy; simp only [List.toFinset_cons,
                          Finset.mem_insert]; exact Or.inr (Or.inr hy))
                        (h2.1.resolve_left hA) hA (.head _)
                  refine hfinT _ hsub1 (itpA p S fl (c' + 1) (A :: B :: Γ) g)
                    ?_ ?_
                  · refine mem_itpAfull_of_oth ?_
                    simp only [itpAoth]
                    refine List.mem_append.mpr (Or.inr ?_)
                    simp only [itpAenv]
                    refine List.mem_flatMap.mpr ⟨A.and B, hF'Γ, ?_⟩
                    simp only
                    rw [if_neg h1, if_pos h2]
                    exact .head _
                  · refine hgrown (A :: B :: Γ) hlt fl (c' + 1) g _
                      (hroomG _ hlt) ?_
                      (val_lift (G4c.identity_mem (.head _)) hF
                        (Nat.le_refl _))
                    refine projE (l := itpEcls p S fl (c' + 2) Γ)
                      (hamb.weaken _) ?_
                    simp only [itpEcls]
                    refine List.mem_append.mpr (Or.inr
                      (List.mem_flatMap.mpr ⟨A.and B, hF'Γ, ?_⟩))
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
                  have hA : A ∉ Γ := fun h => h1 (Or.inl h)
                  have hB : B ∉ Γ := fun h => h1 (Or.inr h)
                  refine hfinT _ hsub1
                    (((itpE p S fl (c' + 1) (A :: Γ)).ifThen
                        (itpA p S fl (c' + 1) (A :: Γ) g)).and
                      ((itpE p S fl (c' + 1) (B :: Γ)).ifThen
                        (itpA p S fl (c' + 1) (B :: Γ) g))) ?_
                    (G4c.andL (List.Perm.refl _) (G4c.andR ?_ ?_))
                  · refine mem_itpAfull_of_oth ?_
                    simp only [itpAoth]
                    refine List.mem_append.mpr (Or.inr ?_)
                    simp only [itpAenv]
                    refine List.mem_flatMap.mpr ⟨A.or B, hF'Γ, ?_⟩
                    simp only
                    rw [if_neg h1, if_pos h2]
                    exact .head _
                  · exact (himpX A g _ (defect_cons_lt h2.1 hA)
                      (G4c.identity_mem (.head _))).perm
                      (List.Perm.refl _)
                  · exact himpX B g _ (defect_cons_lt h2.2 hB)
                      (G4c.identity_mem (.tail _ (.head _)))
                next => cases hin
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
                        -- present prop antecedent: bare growth
                        rcases List.mem_singleton.mp hin with rfl
                        refine hfinT _ hsub1
                          (itpA p S fl (c' + 1) (B :: Γ) g) ?_ ?_
                        · refine mem_itpAfull_of_oth ?_
                          simp only [itpAoth]
                          refine List.mem_append.mpr (Or.inr ?_)
                          simp only [itpAenv]
                          refine List.mem_flatMap.mpr
                            ⟨(prop q).ifThen B, hF'Γ, ?_⟩
                          simp only
                          rw [if_neg hBΓ, if_pos hBS, if_pos hq]
                          exact .head _
                        · refine hgrown (B :: Γ) (defect_cons_lt hBS hBΓ)
                            fl (c' + 1) g _
                            (hroomG _ (defect_cons_lt hBS hBΓ)) ?_
                            (val_lift (G4c.identity_mem (.head _)) hF
                              (Nat.le_refl _))
                          refine projE (l := itpEcls p S fl (c' + 2) Γ)
                            (hamb.weaken _) ?_
                          simp only [itpEcls]
                          refine List.mem_append.mpr (Or.inr
                            (List.mem_flatMap.mpr
                              ⟨(prop q).ifThen B, hF'Γ, ?_⟩))
                          simp only
                          rw [if_neg hBΓ, if_pos hBS, if_pos hq]
                          exact .head _
                      next hq =>
                        split at hin
                        next => cases hin
                        next hqp =>
                          -- fresh prop antecedent: atom-guarded growth
                          rcases List.mem_singleton.mp hin with rfl
                          refine hfinT _ hsub1 ((prop q).and
                            (itpA p S fl (c' + 1) (B :: Γ) g)) ?_ ?_
                          · refine mem_itpAfull_of_oth ?_
                            simp only [itpAoth]
                            refine List.mem_append.mpr (Or.inr ?_)
                            simp only [itpAenv]
                            refine List.mem_flatMap.mpr
                              ⟨(prop q).ifThen B, hF'Γ, ?_⟩
                            simp only
                            rw [if_neg hBΓ, if_pos hBS, if_neg hq, if_neg hqp]
                            exact .head _
                          · refine G4c.andL (List.Perm.refl _)
                              (G4c.andR (G4c.init (.head _)) ?_)
                            refine hgrown (B :: Γ) (defect_cons_lt hBS hBΓ)
                              fl (c' + 1) g _
                              (hroomG _ (defect_cons_lt hBS hBΓ)) ?_
                              (val_lift (G4c.identity_mem
                                (.tail _ (.head _))) hF (Nat.le_refl _))
                            refine fire (projE
                              (l := itpEcls p S fl (c' + 2) Γ)
                              (weaken_sub (fun ψ h =>
                                .tail _ (.tail _ h)) hamb) ?_)
                              (G4c.init (.head _))
                            simp only [itpEcls]
                            refine List.mem_append.mpr (Or.inr
                              (List.mem_flatMap.mpr
                                ⟨(prop q).ifThen B, hF'Γ, ?_⟩))
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
                      refine hfinT _ hsub1 (itpA p S fl (c' + 1)
                        (A₁.ifThen (B₁.ifThen B) :: Γ) g) ?_ ?_
                      · refine mem_itpAfull_of_oth ?_
                        simp only [itpAoth]
                        refine List.mem_append.mpr (Or.inr ?_)
                        simp only [itpAenv]
                        refine List.mem_flatMap.mpr
                          ⟨(A₁.and B₁).ifThen B, hF'Γ, ?_⟩
                        simp only
                        rw [if_neg h1, if_pos h2]
                        exact .head _
                      · refine hgrown _ (defect_cons_lt h2 h1) fl (c' + 1)
                          g _ (hroomG _ (defect_cons_lt h2 h1)) ?_
                          (val_lift (G4c.identity_mem (.head _)) hF
                            (Nat.le_refl _))
                        refine projE (l := itpEcls p S fl (c' + 2) Γ)
                          (hamb.weaken _) ?_
                        simp only [itpEcls]
                        refine List.mem_append.mpr (Or.inr
                          (List.mem_flatMap.mpr
                            ⟨(A₁.and B₁).ifThen B, hF'Γ, ?_⟩))
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
                      have hlt : defect S (A₁.ifThen B :: B₁.ifThen B :: Γ) <
                          defect S Γ := by
                        by_cases hA : A₁.ifThen B ∈ Γ
                        · have hBn : B₁.ifThen B ∉ Γ := fun hB => h1 ⟨hA, hB⟩
                          exact defect_lt_of_mem
                            (Γ' := A₁.ifThen B :: B₁.ifThen B :: Γ)
                            (by intro y hy; simp only [List.toFinset_cons,
                              Finset.mem_insert]; exact Or.inr (Or.inr hy))
                            (h2.2.resolve_left hBn) hBn (.tail _ (.head _))
                        · exact defect_lt_of_mem
                            (Γ' := A₁.ifThen B :: B₁.ifThen B :: Γ)
                            (by intro y hy; simp only [List.toFinset_cons,
                              Finset.mem_insert]; exact Or.inr (Or.inr hy))
                            (h2.1.resolve_left hA) hA (.head _)
                      refine hfinT _ hsub1 (itpA p S fl (c' + 1)
                        (A₁.ifThen B :: B₁.ifThen B :: Γ) g) ?_ ?_
                      · refine mem_itpAfull_of_oth ?_
                        simp only [itpAoth]
                        refine List.mem_append.mpr (Or.inr ?_)
                        simp only [itpAenv]
                        refine List.mem_flatMap.mpr
                          ⟨(A₁.or B₁).ifThen B, hF'Γ, ?_⟩
                        simp only
                        rw [if_neg h1, if_pos h2]
                        exact .head _
                      · refine hgrown _ hlt fl (c' + 1) g _ (hroomG _ hlt) ?_
                          (val_lift (G4c.identity_mem (.head _)) hF
                            (Nat.le_refl _))
                        refine projE (l := itpEcls p S fl (c' + 2) Γ)
                          (hamb.weaken _) ?_
                        simp only [itpEcls]
                        refine List.mem_append.mpr (Or.inr
                          (List.mem_flatMap.mpr
                            ⟨(A₁.or B₁).ifThen B, hF'Γ, ?_⟩))
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
                        next hABS =>
                          -- gated present piece: the impLImp jump chain
                          rcases List.mem_singleton.mp hin with rfl
                          refine G4c.andL (List.Perm.refl _) ?_
                          -- J_s :: W :: Δ ⊢ R
                          have dHead : G4c
                              (((itpE p S F (c' + 1) Γ).ifThen
                                (itpA p S F (c' + 1) Γ (A₁.ifThen B₁))) ::
                               itpA p S F (c' + 2) (B :: Γ) g :: Δ)
                              (itpA p S F (c' + 1) Γ (A₁.ifThen B₁)) :=
                            fire (G4c.identity_mem (.head _))
                              (weaken_sub (fun ψ h => .tail _ (.tail _ h))
                                (hambL F (c' + 1)
                                  (le_trans hF (Nat.le_succ _))
                                  (Nat.le_succ _)))
                          have hgJ : A₁.ifThen B₁ ∈ jumpGoals S :=
                            mem_jumpGoals_imp hABS
                          by_cases hseen : A₁.ifThen B₁ ∈ seen
                          · -- repeat leaf: the mono-splice
                            exact hcls _ hseen _
                              (fun ψ h => .tail _ (.tail _ h))
                              (val_lift dHead
                                (le_trans hF (Nat.le_succ _))
                                (Nat.le_refl _))
                          · -- fresh jump goal: descend
                            refine ihfA Γ fl c' (A₁.ifThen B₁)
                              (insert (A₁.ifThen B₁) seen) _ R hd
                              (Finset.mem_insert_self _ _)
                              (hroomJ _ hgJ hseen) ?_
                              (weaken_sub (fun ψ h => .tail _ (.tail _ h))
                                (hambL fl (c' + 1) (Nat.le_succ _)
                                  (Nat.le_succ _)))
                              dHead hF
                            intro g'' hg'' Δ' hs' val
                            rcases Finset.mem_insert.mp hg'' with rfl | hg''
                            · -- the new continuation: assemble the target
                              -- jump disjunct around the returned value
                              refine hfinT Δ'
                                (fun ψ h => hs' ψ (.tail _ (.tail _ h)))
                                (((itpE p S fl c' Γ).ifThen
                                    (itpA p S fl c' Γ (A₁.ifThen B₁))).and
                                  (itpA p S fl (c' + 1) (B :: Γ) g))
                                ?_ (G4c.andR
                                  (G4c.impR (val.weaken (itpE p S fl c' Γ)))
                                  ?_)
                              · refine mem_itpAfull_of_oth ?_
                                simp only [itpAoth]
                                refine List.mem_append.mpr (Or.inr ?_)
                                simp only [itpAenv]
                                refine List.mem_flatMap.mpr
                                  ⟨(A₁.ifThen B₁).ifThen B, hF'Γ, ?_⟩
                                simp only
                                rw [if_neg hDΓ, if_pos hDS, if_pos hBD,
                                  if_pos hABS]
                                exact .head _
                              · -- second component: grown descent, ambient
                                -- unlocked by firing the packaged jump conjunct
                                refine hgrown (B :: Γ)
                                  (defect_cons_lt hDS hDΓ) fl (c' + 1) g Δ'
                                  (hroomG _ (defect_cons_lt hDS hDΓ)) ?_
                                  (val_lift (G4c.identity_mem
                                    (A := itpA p S F (c' + 2) (B :: Γ) g)
                                    (hs' _ (.tail _ (.head _)))) hF
                                    (Nat.le_refl _))
                                refine fire
                                  (X := (itpE p S fl (c' + 1) Γ).ifThen
                                    (itpA p S fl (c' + 1) Γ (A₁.ifThen B₁)))
                                  (projE
                                  (l := itpEcls p S fl (c' + 2) Γ)
                                  (weaken_sub (fun ψ h =>
                                    hs' ψ (.tail _ (.tail _ h))) hamb) ?_)
                                  (G4c.impR ((val_lift val (Nat.le_refl _)
                                    (Nat.le_succ _)).weaken _))
                                simp only [itpEcls]
                                refine List.mem_append.mpr (Or.inr
                                  (List.mem_flatMap.mpr
                                    ⟨(A₁.ifThen B₁).ifThen B, hF'Γ, ?_⟩))
                                simp only
                                rw [if_neg hDΓ, if_pos hDS, if_pos hBD,
                                  if_pos hABS]
                                exact .head _
                            · exact hcls g'' hg'' Δ'
                                (fun ψ h => hs' ψ (.tail _ (.tail _ h)))
                                (val_lift val (Nat.le_succ _)
                                  (Nat.le_succ _))
                        next => cases hin
                      next hBD =>
                        split at hin
                        next hBDS =>
                          -- fresh piece: guarded growth on both components
                          rcases List.mem_singleton.mp hin with rfl
                          refine G4c.andL (List.Perm.refl _) ?_
                          refine hfinT _
                            (fun ψ h => .tail _ (.tail _ h))
                            (((itpE p S fl (c' + 1) (B₁.ifThen B :: Γ)).ifThen
                                (itpA p S fl (c' + 1) (B₁.ifThen B :: Γ)
                                  (A₁.ifThen B₁))).and
                              (itpA p S fl (c' + 1) (B :: Γ) g)) ?_
                            (G4c.andR ?_ ?_)
                          · refine mem_itpAfull_of_oth ?_
                            simp only [itpAoth]
                            refine List.mem_append.mpr (Or.inr ?_)
                            simp only [itpAenv]
                            refine List.mem_flatMap.mpr
                              ⟨(A₁.ifThen B₁).ifThen B, hF'Γ, ?_⟩
                            simp only
                            rw [if_neg hDΓ, if_pos hDS, if_neg hBD,
                              if_pos hBDS]
                            exact .head _
                          · exact himpX (B₁.ifThen B) (A₁.ifThen B₁) _
                              (defect_cons_lt hBDS hBD)
                              (G4c.identity_mem (.head _))
                          · refine hgrown (B :: Γ)
                              (defect_cons_lt hDS hDΓ) fl (c' + 1) g _
                              (hroomG _ (defect_cons_lt hDS hDΓ)) ?_
                              (val_lift (G4c.identity_mem
                                (.tail _ (.head _))) hF (Nat.le_refl _))
                            refine fire (projE
                              (l := itpEcls p S fl (c' + 2) Γ)
                              (weaken_sub (fun ψ h =>
                                .tail _ (.tail _ h)) hamb) ?_)
                              (G4c.impR (val_lift (fire
                                ((G4c.identity_mem (A := (itpE p S F (c' + 2)
                                    (B₁.ifThen B :: Γ)).ifThen
                                  (itpA p S F (c' + 2) (B₁.ifThen B :: Γ)
                                    (A₁.ifThen B₁)))
                                  (.tail _ (.head _))))
                                (consume₁ (G4c.identity_mem (.head _))
                                  ((itp_fuel_mono_le p S hF).1 _ _)))
                                hF (Nat.le_refl _)))
                            simp only [itpEcls]
                            refine List.mem_append.mpr (Or.inr
                              (List.mem_flatMap.mpr
                                ⟨(A₁.ifThen B₁).ifThen B, hF'Γ, ?_⟩))
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
                          · -- the bare jump disjunct: the impLLax chain
                            refine G4c.andL (List.Perm.refl _) ?_
                            have hgJ : A₁ ∈ jumpGoals S :=
                              mem_jumpGoals_jump hAS
                            by_cases hseen : A₁ ∈ seen
                            · -- repeat leaf: the mono-splice
                              exact hcls _ hseen _
                                (fun ψ h => .tail _ (.tail _ h))
                                (val_lift (G4c.identity_mem (.head _))
                                  (le_trans hF (Nat.le_succ _))
                                  (Nat.le_refl _))
                            · refine ihfA Γ fl c' A₁ (insert A₁ seen) _ R hd
                                (Finset.mem_insert_self _ _)
                                (hroomJ _ hgJ hseen) ?_
                                (weaken_sub (fun ψ h => .tail _ (.tail _ h))
                                  (hambL fl (c' + 1) (Nat.le_succ _)
                                    (Nat.le_succ _)))
                                (G4c.identity_mem (.head _)) hF
                              intro g'' hg'' Δ' hs' val
                              rcases Finset.mem_insert.mp hg'' with rfl | hg''
                              · refine hfinT Δ'
                                  (fun ψ h => hs' ψ (.tail _ (.tail _ h)))
                                  ((itpA p S fl c' Γ g'').and
                                    (itpA p S fl (c' + 1) (B :: Γ) g)) ?_
                                  (G4c.andR val ?_)
                                · refine mem_itpAfull_of_oth ?_
                                  simp only [itpAoth]
                                  refine List.mem_append.mpr (Or.inr ?_)
                                  simp only [itpAenv]
                                  refine List.mem_flatMap.mpr
                                    ⟨g''.somehow.ifThen B, hF'Γ, ?_⟩
                                  simp only
                                  rw [if_neg hBΓ, if_pos hBS, if_pos hAS]
                                  exact List.mem_append.mpr
                                    (Or.inl (.head _))
                                · refine hgrown (B :: Γ)
                                    (defect_cons_lt hBS hBΓ) fl (c' + 1) g Δ'
                                    (hroomG _ (defect_cons_lt hBS hBΓ)) ?_
                                    (val_lift (G4c.identity_mem
                                      (A := itpA p S F (c' + 2) (B :: Γ) g)
                                      (hs' _ (.tail _ (.head _)))) hF
                                      (Nat.le_refl _))
                                  refine fire
                                    (X := itpA p S fl (c' + 1) Γ g'')
                                    (projE
                                      (l := itpEcls p S fl (c' + 2) Γ)
                                      (weaken_sub (fun ψ h =>
                                        hs' ψ (.tail _ (.tail _ h))) hamb)
                                      ?_)
                                    (val_lift val (Nat.le_refl _)
                                      (Nat.le_succ _))
                                  simp only [itpEcls]
                                  refine List.mem_append.mpr (Or.inr
                                    (List.mem_flatMap.mpr
                                      ⟨g''.somehow.ifThen B, hF'Γ, ?_⟩))
                                  simp only
                                  rw [if_neg hBΓ, if_pos hBS, if_pos hAS]
                                  exact List.mem_append.mpr
                                    (Or.inl (.head _))
                              · exact hcls g'' hg'' Δ'
                                  (fun ψ h => hs' ψ (.tail _ (.tail _ h)))
                                  (val_lift val (Nat.le_succ _)
                                    (Nat.le_succ _))
                          · -- the γ-head disjunct: sealed box crossing
                            rcases List.mem_singleton.mp hin' with rfl
                            refine G4c.andL (List.Perm.refl _) ?_
                            refine hfinT _
                              (fun ψ h => .tail _ (.tail _ h))
                              ((((itpE p S fl c' Γ).ifThen
                                  (itpA p S fl c' Γ A₁.somehow)).somehow).and
                                (itpA p S fl (c' + 1) (B :: Γ) g)) ?_
                              (G4c.andR ?_ ?_)
                            · refine mem_itpAfull_of_oth ?_
                              simp only [itpAoth]
                              refine List.mem_append.mpr (Or.inr ?_)
                              simp only [itpAenv]
                              refine List.mem_flatMap.mpr
                                ⟨A₁.somehow.ifThen B, hF'Γ, ?_⟩
                              simp only
                              rw [if_neg hBΓ, if_pos hBS, if_pos hAS]
                              exact List.mem_append.mpr
                                (Or.inl (.tail _ (.head _)))
                            · -- descend inside the box via the holdout
                              refine box_fire
                                (W := (itpE p S fl c' Γ).ifThen
                                  (itpA p S fl c' Γ A₁.somehow))
                                (G4c.identity_mem (.head _))
                                (weaken_sub (fun ψ h =>
                                  .tail _ (.tail _ h))
                                  (hambL F (c' + 1)
                                    (le_trans hF (Nat.le_succ _))
                                    (Nat.le_succ _))) ?_
                              refine G4c.laxR (G4c.impR ?_)
                              exact cascade_low p S F Γ fl c' A₁.somehow _
                                (by
                                  have hd1 : 1 ≤ defect S Γ :=
                                    Finset.card_pos.mpr ⟨B,
                                      Finset.mem_sdiff.mpr ⟨hBS, fun h =>
                                        hBΓ (List.mem_toFinset.mp h)⟩⟩
                                  have h2 : 1 * ((jumpGoals S).card + 2) ≤
                                      defect S Γ *
                                        ((jumpGoals S).card + 2) :=
                                    Nat.mul_le_mul_right _ hd1
                                  omega)
                                hroomW0
                                (weaken_sub (fun ψ h => .tail _ (.tail _
                                  (.tail _ (.tail _ h))))
                                  (hambL fl (c' + 1) (Nat.le_succ _)
                                    (Nat.le_succ _)))
                                (G4c.identity_mem (.tail _ (.head _))) hF
                            · -- second component: fire the γ-head conjunct
                              refine hgrown (B :: Γ)
                                (defect_cons_lt hBS hBΓ) fl (c' + 1) g _
                                (hroomG _ (defect_cons_lt hBS hBΓ)) ?_
                                (val_lift (G4c.identity_mem
                                  (.tail _ (.head _))) hF (Nat.le_refl _))
                              refine fire
                                (X := ((itpE p S fl (c' + 1) Γ).ifThen
                                  (itpA p S fl (c' + 1) Γ
                                    A₁.somehow)).somehow)
                                (projE (l := itpEcls p S fl (c' + 2) Γ)
                                  (weaken_sub (fun ψ h =>
                                    .tail _ (.tail _ h)) hamb) ?_)
                                (consume₁ (G4c.identity_mem (.head _))
                                  (box_mono (imp_mono
                                    ((itp_fuel_mono_le p S hF).1 _ _)
                                    ((itp_fuel_mono_le p S hF).2 _ _ _))))
                              simp only [itpEcls]
                              refine List.mem_append.mpr (Or.inr
                                (List.mem_flatMap.mpr
                                  ⟨A₁.somehow.ifThen B, hF'Γ, ?_⟩))
                              simp only
                              rw [if_neg hBΓ, if_pos hBS, if_pos hAS]
                              exact List.mem_append.mpr
                                (Or.inl (.tail _ (.head _)))
                        next => cases hin
                      · -- the γ-context disjuncts (ungated)
                        obtain ⟨X, hXΓ, heq⟩ := List.mem_filterMap.mp hin
                        cases X with
                        | somehow x =>
                            simp only at heq
                            split at heq
                            next => cases heq
                            next hg2 =>
                              injection heq with heq'
                              subst heq'
                              have hxΓ : x ∉ Γ := fun h => hg2 (Or.inl h)
                              have hxS : x ∈ S := by
                                by_contra h
                                exact hg2 (Or.inr h)
                              refine G4c.andL (List.Perm.refl _) ?_
                              refine hfinT _
                                (fun ψ h => .tail _ (.tail _ h))
                                (((((itpE p S fl (c' + 1) (x :: Γ)).ifThen
                                    (itpA p S fl (c' + 1) (x :: Γ)
                                      A₁.somehow)).somehow)).and
                                  (itpA p S fl (c' + 1) (B :: Γ) g)) ?_
                                (G4c.andR ?_ ?_)
                              · refine mem_itpAfull_of_oth ?_
                                simp only [itpAoth]
                                refine List.mem_append.mpr (Or.inr ?_)
                                simp only [itpAenv]
                                refine List.mem_flatMap.mpr
                                  ⟨A₁.somehow.ifThen B, hF'Γ, ?_⟩
                                simp only
                                rw [if_neg hBΓ, if_pos hBS]
                                refine List.mem_append.mpr (Or.inr
                                  (List.mem_filterMap.mpr
                                    ⟨x.somehow, hXΓ, ?_⟩))
                                simp only
                                rw [if_neg hg2]
                              · -- first: open the ambient's ◯E-growth
                                -- conjunct, cross, land by defect descent
                                refine G4c.cut
                                  (A := (itpE p S fl (c' + 2)
                                    (x :: Γ)).somehow)
                                  (projE (l := itpEcls p S fl (c' + 2) Γ)
                                    (weaken_sub (fun ψ h =>
                                      .tail _ (.tail _ h)) hamb) ?_) ?_
                                · simp only [itpEcls]
                                  refine List.mem_append.mpr (Or.inr
                                    (List.mem_flatMap.mpr
                                      ⟨x.somehow, hXΓ, ?_⟩))
                                  simp only
                                  rw [if_neg hg2]
                                  exact .head _
                                · refine G4c.laxL (.head _) ?_
                                  refine box_fire
                                    (X := itpE p S F (c' + 2) (x :: Γ))
                                    (Y := itpA p S F (c' + 2) (x :: Γ)
                                      A₁.somehow)
                                    (G4c.identity_mem
                                      (.tail _ (.tail _ (.head _))))
                                    (consume₁ (G4c.identity_mem (.head _))
                                      ((itp_fuel_mono_le p S hF).1 _ _)) ?_
                                  refine G4c.laxR (G4c.impR ?_)
                                  refine hgrown (x :: Γ)
                                    (defect_cons_lt hxS hxΓ) fl (c' + 1)
                                    A₁.somehow _
                                    (hroomG _ (defect_cons_lt hxS hxΓ)) ?_
                                    (val_lift (G4c.identity_mem
                                      (.tail _ (.head _))) hF
                                      (Nat.le_refl _))
                                  exact G4c.identity_mem
                                    (.tail _ (.tail _ (.head _)))
                              · -- second: fire the γ-context conjunct
                                refine hgrown (B :: Γ)
                                  (defect_cons_lt hBS hBΓ) fl (c' + 1) g _
                                  (hroomG _ (defect_cons_lt hBS hBΓ)) ?_
                                  (val_lift (G4c.identity_mem
                                    (.tail _ (.head _))) hF (Nat.le_refl _))
                                refine fire
                                  (X := ((itpE p S fl (c' + 2)
                                      (x :: Γ)).ifThen
                                    (itpA p S fl (c' + 2) (x :: Γ)
                                      A₁.somehow)).somehow)
                                  (projE (l := itpEcls p S fl (c' + 2) Γ)
                                    (weaken_sub (fun ψ h =>
                                      .tail _ (.tail _ h)) hamb) ?_)
                                  (consume₁ (G4c.identity_mem (.head _))
                                    (box_mono (imp_mono
                                      ((itp_fuel_mono_le p S hF).1 _ _)
                                      ((itp_fuel_mono_le p S hF).2 _ _ _))))
                                simp only [itpEcls]
                                refine List.mem_append.mpr (Or.inr
                                  (List.mem_flatMap.mpr
                                    ⟨A₁.somehow.ifThen B, hF'Γ, ?_⟩))
                                simp only
                                rw [if_neg hBΓ, if_pos hBS]
                                refine List.mem_append.mpr (Or.inr
                                  (List.mem_filterMap.mpr
                                    ⟨x.somehow, hXΓ, ?_⟩))
                                simp only
                                rw [if_neg hg2]
                        | prop _ => cases heq
                        | falsePLL => cases heq
                        | and _ _ => cases heq
                        | or _ _ => cases heq
                        | ifThen _ _ => cases heq
                    next => cases hin
          | somehow χ =>
              simp only at hin
              cases g with
              | somehow D =>
                  simp only at hin
                  by_cases hg2 : χ ∈ Γ ∨ χ ∉ S
                  · rw [if_pos hg2] at hin
                    cases hin
                  · rw [if_neg hg2] at hin
                    rcases List.mem_singleton.mp hin with rfl
                    have hχΓ : χ ∉ Γ := fun h => hg2 (Or.inl h)
                    have hχS : χ ∈ S := by
                      by_contra h
                      exact hg2 (Or.inr h)
                    refine hfinT _ hsub1
                      (((itpE p S fl (c' + 1) (χ :: Γ)).ifThen
                        (itpA p S fl (c' + 1) (χ :: Γ)
                          (D.somehow))).somehow) ?_ ?_
                    · refine mem_itpAfull_of_oth ?_
                      simp only [itpAoth]
                      refine List.mem_append.mpr (Or.inr ?_)
                      simp only [itpAenv]
                      refine List.mem_flatMap.mpr ⟨χ.somehow, hF'Γ, ?_⟩
                      simp only
                      rw [if_neg hg2]
                      exact .head _
                    · refine G4c.cut
                        (A := (itpE p S fl (c' + 2) (χ :: Γ)).somehow)
                        (projE (l := itpEcls p S fl (c' + 2) Γ)
                          (hamb.weaken _) ?_) ?_
                      · simp only [itpEcls]
                        refine List.mem_append.mpr (Or.inr
                          (List.mem_flatMap.mpr ⟨χ.somehow, hF'Γ, ?_⟩))
                        simp only
                        rw [if_neg hg2]
                        exact .head _
                      · refine G4c.laxL (.head _) ?_
                        refine box_fire
                          (X := itpE p S F (c' + 2) (χ :: Γ))
                          (Y := itpA p S F (c' + 2) (χ :: Γ) (D.somehow))
                          (G4c.identity_mem (.tail _ (.tail _ (.head _))))
                          (consume₁ (G4c.identity_mem (.head _))
                            ((itp_fuel_mono_le p S hF).1 _ _)) ?_
                        refine G4c.laxR (G4c.impR ?_)
                        refine hgrown (χ :: Γ) (defect_cons_lt hχS hχΓ)
                          fl (c' + 1) (D.somehow) _
                          (hroomG _ (defect_cons_lt hχS hχΓ)) ?_
                          (val_lift (G4c.identity_mem (.tail _ (.head _)))
                            hF (Nat.le_refl _))
                        exact G4c.identity_mem
                          (.tail _ (.tail _ (.head _)))
              | prop q => cases hin
              | falsePLL => cases hin
              | and C₁ C₂ => cases hin
              | or C₁ C₂ => cases hin
              | ifThen C₁ C₂ => cases hin
        have hOTH : ∀ φ ∈ itpAoth p S F (c' + 2) Γ g, G4c (φ :: Δ) R := by
          intro φ hφ
          simp only [itpAoth] at hφ
          rcases List.mem_append.mp hφ with hφ | hφ
          · exact hGOAL φ hφ
          · exact hENV φ hφ
        refine G4c.cut hhead (G4c.orAll_elim ?_)
        intro φ hφ
        cases g with
        | somehow D =>
            simp only [itpAfull] at hφ
            rcases List.mem_append.mp hφ with hφ | hφ
            · exact hOTH φ hφ
            · -- the truncation disjunct: sealed box crossing; rebuild
              -- the full head from this disjunct and descend whole
              refine hcls _ hg _ (fun χ h => .tail _ h) ?_
              refine cascade_low p S (F + 1) Γ (fl + 1) (c' + 1) _ _
                (by omega) hroomW
                ((hambL (fl + 1) (c' + 2) (Nat.le_refl _)
                  (Nat.le_refl _)).weaken _) ?_ hfh
              rw [itpA_succ]
              refine G4c.orAll_intro (l := itpAfull p S F (c' + 2) Γ
                (D.somehow)) ?_ (G4c.identity_mem (.head _))
              simp only [itpAfull]
              exact List.mem_append.mpr (Or.inr hφ)
        | prop q => exact hOTH φ hφ
        | falsePLL => exact hOTH φ hφ
        | and C₁ C₂ => exact hOTH φ hφ
        | or C₁ C₂ => exact hOTH φ hφ
        | ifThen C₁ C₂ => exact hOTH φ hφ
      · -- E-half: the one-step ascent
        intro Γ c Δ hd hroom hsrc
        obtain ⟨c'', rfl⟩ : ∃ c'', c = c'' + 1 := ⟨c - 1, by omega⟩
        rw [itpE_succ p S F (c'' + 2) Γ]
        refine G4c.andAll_intro ?_
        intro ψ hψ
        -- fuel-level source at any weaker budget
        have hsrcF : ∀ (b' : Nat), b' ≤ c'' + 1 → G4c Δ (itpE p S F b' Γ) :=
          fun b' hb' => consume₁ (consume₁ hsrc
            ((itp_fuel_mono p S F).1 _ Γ))
            ((itp_budget_mono_le p S hb' F).1 Γ)
        -- entry room for same-context A-descents
        have hroomA : ∀ (x : PLLFormula), (jumpGoals S \ {x}).card + 1 +
            defect S Γ * ((jumpGoals S).card + 2) ≤ c'' := by
          intro x
          have hc := Finset.card_le_card
            (Finset.sdiff_subset (s := jumpGoals S) (t := {x}))
          omega
        -- one-step ascent at a defect-paying grown context
        have hEg : ∀ (Γ' : List PLLFormula), defect S Γ' < defect S Γ →
            ∀ (Δ' : List PLLFormula), G4c Δ' (itpE p S F (c'' + 1) Γ') →
            G4c Δ' (itpE p S F (c'' + 2) Γ') := by
          intro Γ' hlt Δ' hsrc'
          refine ihfE Γ' (c'' + 1) Δ' (le_trans (le_of_lt hlt) hd) ?_ hsrc'
          have hexp : (defect S Γ' + 1) * ((jumpGoals S).card + 2) =
              defect S Γ' * ((jumpGoals S).card + 2) +
              ((jumpGoals S).card + 2) := by ring
          have hmul : (defect S Γ' + 1) * ((jumpGoals S).card + 2) ≤
              defect S Γ * ((jumpGoals S).card + 2) :=
            Nat.mul_le_mul_right _ (by omega)
          omega
        -- entry-shaped same-context A-descent
        have hAd : ∀ (β : Nat) (h : PLLFormula) (Δ' : List PLLFormula),
            (jumpGoals S \ {h}).card + 1 +
              defect S Γ * ((jumpGoals S).card + 2) ≤ β →
            G4c Δ' (itpE p S F (β + 1) Γ) →
            G4c Δ' (itpA p S F (β + 1) Γ h) →
            G4c Δ' (itpA p S F β Γ h) := by
          intro β h Δ' hr hamb' hhead'
          refine ihfA Γ F β h {h} Δ' _ hd (Finset.mem_singleton_self h) hr
            ?_ hamb' hhead' (Nat.le_refl _)
          intro g' hg' Δ'' _ hval
          rcases Finset.mem_singleton.mp hg' with rfl
          exact hval
        -- entry-shaped A-descent at a defect-paying grown context
        have hAg : ∀ (Γ' : List PLLFormula), defect S Γ' < defect S Γ →
            ∀ (β : Nat) (h : PLLFormula) (Δ' : List PLLFormula), c'' ≤ β →
            G4c Δ' (itpE p S F (β + 1) Γ') →
            G4c Δ' (itpA p S F (β + 1) Γ' h) →
            G4c Δ' (itpA p S F β Γ' h) := by
          intro Γ' hlt β h Δ' hβ hamb' hhead'
          refine ihfA Γ' F β h {h} Δ' _ (le_trans (le_of_lt hlt) hd)
            (Finset.mem_singleton_self h) ?_ ?_ hamb' hhead' (Nat.le_refl _)
          · have hc := Finset.card_le_card
              (Finset.sdiff_subset (s := jumpGoals S) (t := {h}))
            have hexp : (defect S Γ' + 1) * ((jumpGoals S).card + 2) =
                defect S Γ' * ((jumpGoals S).card + 2) +
                ((jumpGoals S).card + 2) := by ring
            have hmul : (defect S Γ' + 1) * ((jumpGoals S).card + 2) ≤
                defect S Γ * ((jumpGoals S).card + 2) :=
              Nat.mul_le_mul_right _ (by omega)
            omega
          · intro g' hg' Δ'' _ hval
            rcases Finset.mem_singleton.mp hg' with rfl
            exact hval
        simp only [itpEcls] at hψ
        rcases List.mem_append.mp hψ with hψ | hψ
        · rcases List.mem_append.mp hψ with hψ | hψ
          · -- the ⊥ clause
            split at hψ
            next hbot =>
              rcases List.mem_singleton.mp hψ with rfl
              refine projE (l := itpEcls p S F (c'' + 1) Γ) hsrc ?_
              simp only [itpEcls]
              exact List.mem_append.mpr (Or.inl (List.mem_append.mpr
                (Or.inl (by rw [if_pos hbot]; exact .head _))))
            next => cases hψ
          · -- the atom clauses
            obtain ⟨F', hF'Γ, heq⟩ := List.mem_filterMap.mp hψ
            cases F' with
            | prop q =>
                simp only at heq
                split at heq
                next => cases heq
                next hq =>
                  injection heq with heq'
                  subst heq'
                  refine projE (l := itpEcls p S F (c'' + 1) Γ) hsrc ?_
                  simp only [itpEcls]
                  refine List.mem_append.mpr (Or.inl (List.mem_append.mpr
                    (Or.inr (List.mem_filterMap.mpr ⟨prop q, hF'Γ, ?_⟩))))
                  simp only
                  rw [if_neg hq]
            | falsePLL => cases heq
            | and _ _ => cases heq
            | or _ _ => cases heq
            | ifThen _ _ => cases heq
            | somehow _ => cases heq
        · -- the rule clauses
          obtain ⟨F', hF'Γ, hin⟩ := List.mem_flatMap.mp hψ
          cases F' with
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
                  have hlt : defect S (A :: B :: Γ) < defect S Γ := by
                    by_cases hA : A ∈ Γ
                    · have hB : B ∉ Γ := fun hB => h1 ⟨hA, hB⟩
                      exact defect_lt_of_mem (Γ' := A :: B :: Γ)
                        (by intro y hy; simp only [List.toFinset_cons,
                          Finset.mem_insert]; exact Or.inr (Or.inr hy))
                        (h2.2.resolve_left hB) hB (.tail _ (.head _))
                    · exact defect_lt_of_mem (Γ' := A :: B :: Γ)
                        (by intro y hy; simp only [List.toFinset_cons,
                          Finset.mem_insert]; exact Or.inr (Or.inr hy))
                        (h2.1.resolve_left hA) hA (.head _)
                  refine hEg _ hlt Δ (projE
                    (l := itpEcls p S F (c'' + 1) Γ) hsrc ?_)
                  simp only [itpEcls]
                  refine List.mem_append.mpr (Or.inr
                    (List.mem_flatMap.mpr ⟨A.and B, hF'Γ, ?_⟩))
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
                  have hA : A ∉ Γ := fun h => h1 (Or.inl h)
                  have hB : B ∉ Γ := fun h => h1 (Or.inr h)
                  refine consume₁ (projE
                    (l := itpEcls p S F (c'' + 1) Γ) hsrc ?_)
                    (or_mono
                      (hEg _ (defect_cons_lt h2.1 hA) _
                        (G4c.identity_mem (.head _)))
                      (hEg _ (defect_cons_lt h2.2 hB) _
                        (G4c.identity_mem (.head _))))
                  simp only [itpEcls]
                  refine List.mem_append.mpr (Or.inr
                    (List.mem_flatMap.mpr ⟨A.or B, hF'Γ, ?_⟩))
                  simp only
                  rw [if_neg h1, if_pos h2]
                  exact .head _
                next => cases hin
          | somehow χ =>
              simp only at hin
              split at hin
              next => cases hin
              next hg2 =>
                rcases List.mem_singleton.mp hin with rfl
                have hχΓ : χ ∉ Γ := fun h => hg2 (Or.inl h)
                have hχS : χ ∈ S := by
                  by_contra h
                  exact hg2 (Or.inr h)
                refine consume₁ (projE
                  (l := itpEcls p S F (c'' + 1) Γ) hsrc ?_)
                  (box_mono (hEg _ (defect_cons_lt hχS hχΓ) _
                    (G4c.identity_mem (.head _))))
                simp only [itpEcls]
                refine List.mem_append.mpr (Or.inr
                  (List.mem_flatMap.mpr ⟨χ.somehow, hF'Γ, ?_⟩))
                simp only
                rw [if_neg hg2]
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
                        refine hEg _ (defect_cons_lt hBS hBΓ) Δ (projE
                          (l := itpEcls p S F (c'' + 1) Γ) hsrc ?_)
                        simp only [itpEcls]
                        refine List.mem_append.mpr (Or.inr
                          (List.mem_flatMap.mpr ⟨(prop q).ifThen B, hF'Γ, ?_⟩))
                        simp only
                        rw [if_neg hBΓ, if_pos hBS, if_pos hq]
                        exact .head _
                      next hq =>
                        split at hin
                        next => cases hin
                        next hqp =>
                          rcases List.mem_singleton.mp hin with rfl
                          refine consume₁ (projE
                            (l := itpEcls p S F (c'' + 1) Γ) hsrc ?_)
                            (imp_mono (G4c.init (.head _))
                              (hEg _ (defect_cons_lt hBS hBΓ) _
                                (G4c.identity_mem (.head _))))
                          simp only [itpEcls]
                          refine List.mem_append.mpr (Or.inr
                            (List.mem_flatMap.mpr
                              ⟨(prop q).ifThen B, hF'Γ, ?_⟩))
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
                      refine hEg _ (defect_cons_lt h2 h1) Δ (projE
                        (l := itpEcls p S F (c'' + 1) Γ) hsrc ?_)
                      simp only [itpEcls]
                      refine List.mem_append.mpr (Or.inr
                        (List.mem_flatMap.mpr
                          ⟨(A₁.and B₁).ifThen B, hF'Γ, ?_⟩))
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
                      have hlt : defect S (A₁.ifThen B :: B₁.ifThen B :: Γ) <
                          defect S Γ := by
                        by_cases hA : A₁.ifThen B ∈ Γ
                        · have hBn : B₁.ifThen B ∉ Γ := fun hB => h1 ⟨hA, hB⟩
                          exact defect_lt_of_mem
                            (Γ' := A₁.ifThen B :: B₁.ifThen B :: Γ)
                            (by intro y hy; simp only [List.toFinset_cons,
                              Finset.mem_insert]; exact Or.inr (Or.inr hy))
                            (h2.2.resolve_left hBn) hBn (.tail _ (.head _))
                        · exact defect_lt_of_mem
                            (Γ' := A₁.ifThen B :: B₁.ifThen B :: Γ)
                            (by intro y hy; simp only [List.toFinset_cons,
                              Finset.mem_insert]; exact Or.inr (Or.inr hy))
                            (h2.1.resolve_left hA) hA (.head _)
                      refine hEg _ hlt Δ (projE
                        (l := itpEcls p S F (c'' + 1) Γ) hsrc ?_)
                      simp only [itpEcls]
                      refine List.mem_append.mpr (Or.inr
                        (List.mem_flatMap.mpr
                          ⟨(A₁.or B₁).ifThen B, hF'Γ, ?_⟩))
                      simp only
                      rw [if_neg h1, if_pos h2]
                      exact .head _
                    next => cases hin
              | ifThen A₁ B₁ =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next hDG =>
                    split at hin
                    next hDS =>
                      split at hin
                      next hBD =>
                        split at hin
                        next hABS =>
                          -- gated present piece: convert the antecedent
                          -- through the A-descent, fire, ascend
                          rcases List.mem_singleton.mp hin with rfl
                          refine G4c.impR ?_
                          have hJs : G4c ((itpE p S F (c'' + 1) Γ).ifThen
                              (itpA p S F (c'' + 1) Γ (A₁.ifThen B₁)) :: Δ)
                              ((itpE p S F c'' Γ).ifThen
                                (itpA p S F c'' Γ (A₁.ifThen B₁))) := by
                            refine G4c.impR ?_
                            refine hAd c'' (A₁.ifThen B₁) _ (hroomA _)
                              (weaken_sub (fun ψ h => .tail _ (.tail _ h))
                                (hsrcF (c'' + 1) (Nat.le_refl _))) ?_
                            exact fire (G4c.identity_mem (.tail _ (.head _)))
                              (weaken_sub (fun ψ h => .tail _ (.tail _ h))
                                (hsrcF (c'' + 1) (Nat.le_refl _)))
                          refine consume₁ (fire (projE
                            (l := itpEcls p S F (c'' + 1) Γ)
                            (hsrc.weaken _) ?_) hJs)
                            (hEg (B :: Γ) (defect_cons_lt hDS hDG) _
                              (G4c.identity_mem (.head _)))
                          simp only [itpEcls]
                          refine List.mem_append.mpr (Or.inr
                            (List.mem_flatMap.mpr
                              ⟨(A₁.ifThen B₁).ifThen B, hF'Γ, ?_⟩))
                          simp only
                          rw [if_neg hDG, if_pos hDS, if_pos hBD, if_pos hABS]
                          exact .head _
                        next => cases hin
                      next hBD =>
                        split at hin
                        next hBDS =>
                          -- fresh piece: ascend the introduced guard,
                          -- fire, descend at the grown context
                          rcases List.mem_singleton.mp hin with rfl
                          refine G4c.impR ?_
                          have hJs : G4c ((itpE p S F (c'' + 2)
                              (B₁.ifThen B :: Γ)).ifThen
                              (itpA p S F (c'' + 2) (B₁.ifThen B :: Γ)
                                (A₁.ifThen B₁)) :: Δ)
                              ((itpE p S F (c'' + 1)
                                (B₁.ifThen B :: Γ)).ifThen
                                (itpA p S F (c'' + 1) (B₁.ifThen B :: Γ)
                                  (A₁.ifThen B₁))) := by
                            refine G4c.impR ?_
                            have hE2 : G4c (itpE p S F (c'' + 1)
                                (B₁.ifThen B :: Γ) ::
                                (itpE p S F (c'' + 2)
                                  (B₁.ifThen B :: Γ)).ifThen
                                (itpA p S F (c'' + 2) (B₁.ifThen B :: Γ)
                                  (A₁.ifThen B₁)) :: Δ)
                                (itpE p S F (c'' + 2)
                                  (B₁.ifThen B :: Γ)) :=
                              hEg _ (defect_cons_lt hBDS hBD) _
                                (G4c.identity_mem (.head _))
                            refine hAg _ (defect_cons_lt hBDS hBD)
                              (c'' + 1) (A₁.ifThen B₁) _ (Nat.le_succ _)
                              hE2 ?_
                            exact fire (G4c.identity_mem
                              (.tail _ (.head _))) hE2
                          refine consume₁ (fire (projE
                            (l := itpEcls p S F (c'' + 1) Γ)
                            (hsrc.weaken _) ?_) hJs)
                            (hEg (B :: Γ) (defect_cons_lt hDS hDG) _
                              (G4c.identity_mem (.head _)))
                          simp only [itpEcls]
                          refine List.mem_append.mpr (Or.inr
                            (List.mem_flatMap.mpr
                              ⟨(A₁.ifThen B₁).ifThen B, hF'Γ, ?_⟩))
                          simp only
                          rw [if_neg hDG, if_pos hDS, if_neg hBD,
                            if_pos hBDS]
                          exact .head _
                        next => cases hin
                    next => cases hin
              | somehow A₁ =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next hBG =>
                    split at hin
                    next hBS =>
                      rcases List.mem_append.mp hin with hin | hin
                      · split at hin
                        next hAS =>
                          rcases List.mem_cons.mp hin with rfl | hin'
                          · -- jump conjunct: descend the antecedent
                            refine G4c.impR ?_
                            have hAs : G4c (itpA p S F (c'' + 1) Γ A₁ :: Δ)
                                (itpA p S F c'' Γ A₁) :=
                              hAd c'' A₁ _ (hroomA _)
                                ((hsrcF (c'' + 1) (Nat.le_refl _)).weaken _)
                                (G4c.identity_mem (.head _))
                            refine consume₁ (fire (projE
                              (l := itpEcls p S F (c'' + 1) Γ)
                              (hsrc.weaken _) ?_) hAs)
                              (hEg (B :: Γ) (defect_cons_lt hBS hBG) _
                                (G4c.identity_mem (.head _)))
                            simp only [itpEcls]
                            refine List.mem_append.mpr (Or.inr
                              (List.mem_flatMap.mpr
                                ⟨A₁.somehow.ifThen B, hF'Γ, ?_⟩))
                            simp only
                            rw [if_neg hBG, if_pos hBS, if_pos hAS]
                            exact List.mem_append.mpr (Or.inl (.head _))
                          · -- γ-head conjunct: cross, descend, re-cross
                            rcases List.mem_singleton.mp hin' with rfl
                            refine G4c.impR ?_
                            have hGs : G4c ((((itpE p S F (c'' + 1) Γ).ifThen
                                (itpA p S F (c'' + 1) Γ
                                  A₁.somehow)).somehow) :: Δ)
                                (((itpE p S F c'' Γ).ifThen
                                  (itpA p S F c'' Γ A₁.somehow)).somehow) := by
                              refine box_fire
                                (X := itpE p S F (c'' + 1) Γ)
                                (Y := itpA p S F (c'' + 1) Γ A₁.somehow)
                                (G4c.identity_mem (.head _))
                                ((hsrcF (c'' + 1) (Nat.le_refl _)).weaken _)
                                ?_
                              refine G4c.laxR (G4c.impR ?_)
                              refine hAd c'' A₁.somehow _ (hroomA _)
                                (weaken_sub (fun ψ h =>
                                  .tail _ (.tail _ (.tail _ h)))
                                  (hsrcF (c'' + 1) (Nat.le_refl _)))
                                (G4c.identity_mem (.tail _ (.head _)))
                            refine consume₁ (fire (projE
                              (l := itpEcls p S F (c'' + 1) Γ)
                              (hsrc.weaken _) ?_) hGs)
                              (hEg (B :: Γ) (defect_cons_lt hBS hBG) _
                                (G4c.identity_mem (.head _)))
                            simp only [itpEcls]
                            refine List.mem_append.mpr (Or.inr
                              (List.mem_flatMap.mpr
                                ⟨A₁.somehow.ifThen B, hF'Γ, ?_⟩))
                            simp only
                            rw [if_neg hBG, if_pos hBS, if_pos hAS]
                            exact List.mem_append.mpr
                              (Or.inl (.tail _ (.head _)))
                        next => cases hin
                      · -- γ-context conjuncts (ungated)
                        obtain ⟨X, hXΓ, heq⟩ := List.mem_filterMap.mp hin
                        cases X with
                        | somehow x =>
                            simp only at heq
                            split at heq
                            next => cases heq
                            next hg2 =>
                              injection heq with heq'
                              subst heq'
                              have hxΓ : x ∉ Γ := fun h => hg2 (Or.inl h)
                              have hxS : x ∈ S := by
                                by_contra h
                                exact hg2 (Or.inr h)
                              refine G4c.impR ?_
                              have hGs : G4c ((((itpE p S F (c'' + 2)
                                  (x :: Γ)).ifThen
                                  (itpA p S F (c'' + 2) (x :: Γ)
                                    A₁.somehow)).somehow) :: Δ)
                                  (((itpE p S F (c'' + 1) (x :: Γ)).ifThen
                                    (itpA p S F (c'' + 1) (x :: Γ)
                                      A₁.somehow)).somehow) := by
                                refine G4c.cut
                                  (A := (itpE p S F (c'' + 1)
                                    (x :: Γ)).somehow)
                                  (projE (l := itpEcls p S F (c'' + 1) Γ)
                                    (hsrc.weaken _) ?_) ?_
                                · simp only [itpEcls]
                                  refine List.mem_append.mpr (Or.inr
                                    (List.mem_flatMap.mpr
                                      ⟨x.somehow, hXΓ, ?_⟩))
                                  simp only
                                  rw [if_neg hg2]
                                  exact .head _
                                · refine G4c.laxL (.head _) ?_
                                  have hE2 : G4c (itpE p S F (c'' + 1)
                                      (x :: Γ) ::
                                      (itpE p S F (c'' + 1)
                                        (x :: Γ)).somehow ::
                                      (((itpE p S F (c'' + 2)
                                        (x :: Γ)).ifThen
                                        (itpA p S F (c'' + 2) (x :: Γ)
                                          A₁.somehow)).somehow) :: Δ)
                                      (itpE p S F (c'' + 2) (x :: Γ)) :=
                                    hEg _ (defect_cons_lt hxS hxΓ) _
                                      (G4c.identity_mem (.head _))
                                  refine box_fire
                                    (X := itpE p S F (c'' + 2) (x :: Γ))
                                    (Y := itpA p S F (c'' + 2) (x :: Γ)
                                      A₁.somehow)
                                    (G4c.identity_mem
                                      (.tail _ (.tail _ (.head _))))
                                    hE2 ?_
                                  refine G4c.laxR (G4c.impR ?_)
                                  refine hAg (x :: Γ)
                                    (defect_cons_lt hxS hxΓ) (c'' + 1)
                                    A₁.somehow _ (Nat.le_succ _) ?_
                                    (G4c.identity_mem (.tail _ (.head _)))
                                  exact hEg _ (defect_cons_lt hxS hxΓ) _
                                    (G4c.identity_mem
                                      (.tail _ (.tail _ (.head _))))
                              refine consume₁ (fire (projE
                                (l := itpEcls p S F (c'' + 1) Γ)
                                (hsrc.weaken _) ?_) hGs)
                                (hEg (B :: Γ) (defect_cons_lt hBS hBG) _
                                  (G4c.identity_mem (.head _)))
                              simp only [itpEcls]
                              refine List.mem_append.mpr (Or.inr
                                (List.mem_flatMap.mpr
                                  ⟨A₁.somehow.ifThen B, hF'Γ, ?_⟩))
                              simp only
                              rw [if_neg hBG, if_pos hBS]
                              refine List.mem_append.mpr (Or.inr
                                (List.mem_filterMap.mpr
                                  ⟨x.somehow, hXΓ, ?_⟩))
                              simp only
                              rw [if_neg hg2]
                        | prop _ => cases heq
                        | falsePLL => cases heq
                        | and _ _ => cases heq
                        | or _ _ => cases heq
                        | ifThen _ _ => cases heq
                    next => cases hin

/-- Entry point: the single-goal pair descent for a jump goal of the
space, from the generalized cascade at a singleton seen-set. -/
private theorem cascade_entry (p : String) (S : Finset PLLFormula)
    (fuel c : Nat) (hb : kcap S < c + 2) (Γ : List PLLFormula)
    (g : PLLFormula) (hg : g ∈ jumpGoals S) :
    G4c [itpA p S fuel (c + 1) Γ g, itpE p S (fuel + 1) (c + 1) Γ]
      (itpA p S fuel c Γ g) := by
  have hroom := kcap_room hb Γ
  refine (cascade_main p S (defect S Γ) fuel).1 Γ fuel c g {g} _ _
    (Nat.le_refl _) (Finset.mem_singleton_self g) ?_ ?_
    (consume₁ (G4c.identity_mem (.tail _ (.head _)))
      ((itp_fuel_mono p S fuel).1 (c + 1) Γ))
    (G4c.identity_mem (.head _)) (Nat.le_refl _)
  · exact le_trans (Nat.add_le_add_right (Nat.add_le_add_right
      (Finset.card_le_card Finset.sdiff_subset) 1) _) hroom
  · intro g' hg' Δ' _ hval
    rcases Finset.mem_singleton.mp hg' with rfl
    exact hval

set_option linter.unusedVariables false in
/-- Cascade, `impLImp`-at-present-piece shape: the guarded-implication
first component descends one budget. -/
private theorem cascade_impLImp (p : String) (S : Finset PLLFormula)
    (fuel c : Nat) (hb : kcap S < c + 2) (Γ : List PLLFormula)
    (A₁ B₁ D : PLLFormula)
    (hFΓ : (A₁.ifThen B₁).ifThen D ∈ Γ) (hDΓ : D ∉ Γ) (hDS : D ∈ S)
    (hBD : B₁.ifThen D ∈ Γ) (hABD : (A₁.ifThen B₁).ifThen D ∈ S) :
    G4c [itpA p S fuel (c + 1) Γ (A₁.ifThen B₁),
         itpE p S (fuel + 1) (c + 1) Γ]
      (itpA p S fuel c Γ (A₁.ifThen B₁)) :=
  cascade_entry p S fuel c hb Γ _ (mem_jumpGoals_imp hABD)

set_option linter.unusedVariables false in
/-- Cascade, `impLLax`-jump shape: the bare A-value first component
descends one budget. -/
private theorem cascade_jump (p : String) (S : Finset PLLFormula)
    (fuel c : Nat) (hb : kcap S < c + 2) (Γ : List PLLFormula)
    (A B : PLLFormula)
    (hFΓ : A.somehow.ifThen B ∈ Γ) (hBΓ : B ∉ Γ) (hBS : B ∈ S)
    (hAS : A.somehow.ifThen B ∈ S) :
    G4c [itpA p S fuel (c + 1) Γ A, itpE p S (fuel + 1) (c + 1) Γ]
      (itpA p S fuel c Γ A) :=
  cascade_entry p S fuel c hb Γ _ (mem_jumpGoals_jump hAS)

set_option linter.unusedVariables false in
/-- Cascade, `impLLax`-γ-head shape: the ◯-goal A-value inside the
boxed guard descends one budget (the landing after the laxL/laxR
re-crossing of `cascade_gamma_box`). -/
private theorem cascade_gamma (p : String) (S : Finset PLLFormula)
    (fuel c : Nat) (hb : kcap S < c + 2) (Γ : List PLLFormula)
    (A B : PLLFormula)
    (hFΓ : A.somehow.ifThen B ∈ Γ) (hBΓ : B ∉ Γ) (hBS : B ∈ S)
    (hAS : A.somehow.ifThen B ∈ S) :
    G4c [itpA p S fuel (c + 1) Γ A.somehow, itpE p S (fuel + 1) (c + 1) Γ]
      (itpA p S fuel c Γ A.somehow) :=
  cascade_entry p S fuel c hb Γ _ (mem_jumpGoals_gamma hAS)

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
    ⟨b - 2, by have := kcap_ge (S := S); omega⟩
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

/-! ### The box-free stabilization tier (FACT #1)

`itp_stab` transitively depends on the `◯`-band holdout `sorry`
(via `cascade_main`).  For the `◯`-free fragment the whole descent is
a theorem: with `S` box-free and piece-closed and the context/goal
membership invariants threaded, every `◯`-shaped clause and goal is
dead code, and the two live cascade sites route through the
sorry-free `cascade_main_bf` (via `cascade_low_pos_boxfree`).  The
result, `itp_stab_bf`, is `itp_stab`'s conclusion under the box-free
side conditions. -/

/-- Prepend an `∈ S` fact to a context invariant. -/
private theorem memS_cons_ab {S : Finset PLLFormula} {X : PLLFormula}
    {Γ : List PLLFormula} (hX : X ∈ S) (hΓ : ∀ F ∈ Γ, F ∈ S) :
    ∀ F ∈ X :: Γ, F ∈ S := by
  intro F hF
  rcases List.mem_cons.mp hF with rfl | h
  · exact hX
  · exact hΓ F h

/-- Prepend two `∈ S` facts to a context invariant. -/
private theorem memS_cons₂_ab {S : Finset PLLFormula} {X Y : PLLFormula}
    {Γ : List PLLFormula} (hX : X ∈ S) (hY : Y ∈ S)
    (hΓ : ∀ F ∈ Γ, F ∈ S) : ∀ F ∈ X :: Y :: Γ, F ∈ S :=
  memS_cons_ab hX (memS_cons_ab hY hΓ)

/-- Box-free `impLImp` cascade: the descent for the present guarded
piece, routed through `cascade_low_pos_boxfree` (hence `cascade_main_bf`,
no `sorry`).  `g = A₁ ⊃ B₁ ∈ S` by piece closure of the clause. -/
private theorem cascade_impLImp_bf (p : String) (S : Finset PLLFormula)
    (hSbf : ∀ F ∈ S, boxFree F)
    (hand : ∀ {A B : PLLFormula}, A.and B ∈ S → A ∈ S ∧ B ∈ S)
    (hor : ∀ {A B : PLLFormula}, A.or B ∈ S → A ∈ S ∧ B ∈ S)
    (himp : ∀ {A B : PLLFormula}, A.ifThen B ∈ S → A ∈ S ∧ B ∈ S)
    (fuel c : Nat) (hb : kcap S < c + 2) (Γ : List PLLFormula)
    (A₁ B₁ D : PLLFormula)
    (hΓS : ∀ F ∈ Γ, F ∈ S) (hABD : (A₁.ifThen B₁).ifThen D ∈ S) :
    G4c [itpA p S fuel (c + 1) Γ (A₁.ifThen B₁),
         itpE p S (fuel + 1) (c + 1) Γ]
      (itpA p S fuel c Γ (A₁.ifThen B₁)) := by
  have hroom := kcap_room hb Γ
  have hc : 1 ≤ c := by have := kcap_ge (S := S); omega
  refine cascade_low_pos_boxfree p S hSbf hand hor himp fuel Γ fuel c
    (A₁.ifThen B₁) _ (himp hABD).1 hΓS (by omega) hc
    (consume₁ (G4c.identity_mem (.tail _ (.head _)))
      ((itp_fuel_mono p S fuel).1 (c + 1) Γ))
    (G4c.identity_mem (.head _)) (Nat.le_refl _)

/-- Box-free antecedent conversion for the gated `impLImp` clause,
mirroring `cascade_impLImp_ant` but via `cascade_impLImp_bf`. -/
private theorem cascade_impLImp_ant_bf (p : String) (S : Finset PLLFormula)
    (hSbf : ∀ F ∈ S, boxFree F)
    (hand : ∀ {A B : PLLFormula}, A.and B ∈ S → A ∈ S ∧ B ∈ S)
    (hor : ∀ {A B : PLLFormula}, A.or B ∈ S → A ∈ S ∧ B ∈ S)
    (himp : ∀ {A B : PLLFormula}, A.ifThen B ∈ S → A ∈ S ∧ B ∈ S)
    (fuel c : Nat) (hb : kcap S < c + 2) (Γ : List PLLFormula)
    (A₁ B₁ D : PLLFormula)
    (hΓS : ∀ F ∈ Γ, F ∈ S) (hABD : (A₁.ifThen B₁).ifThen D ∈ S)
    {Δ : List PLLFormula}
    (dJ : G4c Δ ((itpE p S fuel (c + 1) Γ).ifThen
      (itpA p S fuel (c + 1) Γ (A₁.ifThen B₁))))
    (dE : G4c Δ (itpE p S (fuel + 1) (c + 1) Γ)) :
    G4c Δ ((itpE p S fuel c Γ).ifThen
      (itpA p S fuel c Γ (A₁.ifThen B₁))) := by
  refine G4c.impR ?_
  have dE' : G4c (itpE p S fuel c Γ :: Δ) (itpE p S (fuel + 1) (c + 1) Γ) :=
    dE.weaken _
  have dA1 : G4c (itpE p S fuel c Γ :: Δ)
      (itpA p S fuel (c + 1) Γ (A₁.ifThen B₁)) :=
    fire (dJ.weaken _) (consume₁ dE' ((itp_fuel_mono p S fuel).1 (c + 1) Γ))
  exact consume₂ dA1 dE'
    (cascade_impLImp_bf p S hSbf hand hor himp fuel c hb Γ A₁ B₁ D hΓS hABD)

set_option maxHeartbeats 4000000 in
set_option linter.unusedVariables false in
set_option linter.unusedTactic false in
private theorem itp_stab_aux_bf (p : String) (S : Finset PLLFormula)
    (hSbf : ∀ F ∈ S, boxFree F)
    (hand : ∀ {A B : PLLFormula}, A.and B ∈ S → A ∈ S ∧ B ∈ S)
    (hor : ∀ {A B : PLLFormula}, A.or B ∈ S → A ∈ S ∧ B ∈ S)
    (himp : ∀ {A B : PLLFormula}, A.ifThen B ∈ S → A ∈ S ∧ B ∈ S)
    (himpAnd : ∀ {A B D : PLLFormula},
      (A.and B).ifThen D ∈ S → A.ifThen (B.ifThen D) ∈ S)
    (himpOr : ∀ {A B D : PLLFormula},
      (A.or B).ifThen D ∈ S → A.ifThen D ∈ S ∧ B.ifThen D ∈ S)
    (himpImp : ∀ {A B D : PLLFormula},
      (A.ifThen B).ifThen D ∈ S → B.ifThen D ∈ S) :
    ∀ (fuel : Nat), ∀ (c : Nat), kcap S < c + 2 →
    (∀ Γ, (∀ F ∈ Γ, F ∈ S) →
      G4c [itpE p S fuel (c + 1) Γ] (itpE p S fuel (c + 2) Γ)) ∧
    (∀ Γ C, (∀ F ∈ Γ, F ∈ S) → C ∈ S →
      G4c [itpE p S fuel (c + 2) Γ, itpA p S fuel (c + 2) Γ C]
      (itpA p S fuel (c + 1) Γ C)) := by
  intro fuel
  induction fuel with
  | zero =>
      intro c hb
      constructor
      · intro Γ hΓS
        simp only [itpE]
        exact G4c.truePLL_intro _
      · intro Γ C hΓS hCS
        simp only [itpA]
        exact G4c.botL (.tail _ (.head _))
  | succ fuel ih =>
      intro c hb
      have ihE : ∀ Γ', (∀ F ∈ Γ', F ∈ S) → G4c [itpE p S fuel (c + 1) Γ']
          (itpE p S fuel (c + 2) Γ') := fun Γ' hΓ' => (ih c hb).1 Γ' hΓ'
      have ihA : ∀ Γ' C', (∀ F ∈ Γ', F ∈ S) → C' ∈ S →
          G4c [itpE p S fuel (c + 2) Γ',
          itpA p S fuel (c + 2) Γ' C'] (itpA p S fuel (c + 1) Γ' C') :=
        fun Γ' C' hΓ' hC' => (ih c hb).2 Γ' C' hΓ' hC'
      constructor
      · -- E-half: [E@(fuel+1)@(c+1)] ⊢ E@(fuel+1)@(c+2)
        intro Γ hΓS
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
                    (G4c.identity_mem (.head _)) ?_) (ihE (A :: B :: Γ) (memS_cons₂_ab (by first | assumption | exact hCS | exact hΓS _ hFΓ | exact (hand (hΓS _ hFΓ)).1 | exact (hand (hΓS _ hFΓ)).2 | exact (hor (hΓS _ hFΓ)).1 | exact (hor (hΓS _ hFΓ)).2 | exact (himp (hΓS _ hFΓ)).1 | exact (himp (hΓS _ hFΓ)).2 | exact himpAnd (hΓS _ hFΓ) | exact (himpOr (hΓS _ hFΓ)).1 | exact (himpOr (hΓS _ hFΓ)).2 | exact himpImp (hΓS _ hFΓ) | exact (hand hCS).1 | exact (hand hCS).2 | exact (hor hCS).1 | exact (hor hCS).2 | exact (himp hCS).1 | exact (himp hCS).2) (by first | assumption | exact hCS | exact hΓS _ hFΓ | exact (hand (hΓS _ hFΓ)).1 | exact (hand (hΓS _ hFΓ)).2 | exact (hor (hΓS _ hFΓ)).1 | exact (hor (hΓS _ hFΓ)).2 | exact (himp (hΓS _ hFΓ)).1 | exact (himp (hΓS _ hFΓ)).2 | exact himpAnd (hΓS _ hFΓ) | exact (himpOr (hΓS _ hFΓ)).1 | exact (himpOr (hΓS _ hFΓ)).2 | exact himpImp (hΓS _ hFΓ) | exact (hand hCS).1 | exact (hand hCS).2 | exact (hor hCS).1 | exact (hor hCS).2 | exact (himp hCS).1 | exact (himp hCS).2) hΓS))
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
                    (or_mono (ihE (A :: Γ) (memS_cons_ab (by first | assumption | exact hCS | exact hΓS _ hFΓ | exact (hand (hΓS _ hFΓ)).1 | exact (hand (hΓS _ hFΓ)).2 | exact (hor (hΓS _ hFΓ)).1 | exact (hor (hΓS _ hFΓ)).2 | exact (himp (hΓS _ hFΓ)).1 | exact (himp (hΓS _ hFΓ)).2 | exact himpAnd (hΓS _ hFΓ) | exact (himpOr (hΓS _ hFΓ)).1 | exact (himpOr (hΓS _ hFΓ)).2 | exact himpImp (hΓS _ hFΓ) | exact (hand hCS).1 | exact (hand hCS).2 | exact (hor hCS).1 | exact (hor hCS).2 | exact (himp hCS).1 | exact (himp hCS).2) hΓS)) (ihE (B :: Γ) (memS_cons_ab (by first | assumption | exact hCS | exact hΓS _ hFΓ | exact (hand (hΓS _ hFΓ)).1 | exact (hand (hΓS _ hFΓ)).2 | exact (hor (hΓS _ hFΓ)).1 | exact (hor (hΓS _ hFΓ)).2 | exact (himp (hΓS _ hFΓ)).1 | exact (himp (hΓS _ hFΓ)).2 | exact himpAnd (hΓS _ hFΓ) | exact (himpOr (hΓS _ hFΓ)).1 | exact (himpOr (hΓS _ hFΓ)).2 | exact himpImp (hΓS _ hFΓ) | exact (hand hCS).1 | exact (hand hCS).2 | exact (hor hCS).1 | exact (hor hCS).2 | exact (himp hCS).1 | exact (himp hCS).2) hΓS)))
                  simp only [itpEcls]
                  refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                    ⟨A.or B, hFΓ, ?_⟩))
                  simp only
                  rw [if_neg h1, if_pos h2]
                  exact .head _
                next => cases hin
          | somehow χ =>
              exact absurd (hSbf _ (hΓS _ hFΓ)) (by simp [boxFree])
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
                          (G4c.identity_mem (.head _)) ?_) (ihE (B :: Γ) (memS_cons_ab (by first | assumption | exact hCS | exact hΓS _ hFΓ | exact (hand (hΓS _ hFΓ)).1 | exact (hand (hΓS _ hFΓ)).2 | exact (hor (hΓS _ hFΓ)).1 | exact (hor (hΓS _ hFΓ)).2 | exact (himp (hΓS _ hFΓ)).1 | exact (himp (hΓS _ hFΓ)).2 | exact himpAnd (hΓS _ hFΓ) | exact (himpOr (hΓS _ hFΓ)).1 | exact (himpOr (hΓS _ hFΓ)).2 | exact himpImp (hΓS _ hFΓ) | exact (hand hCS).1 | exact (hand hCS).2 | exact (hor hCS).1 | exact (hor hCS).2 | exact (himp hCS).1 | exact (himp hCS).2) hΓS))
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
                            (imp_mono (G4c.init (.head _)) (ihE (B :: Γ) (memS_cons_ab (by first | assumption | exact hCS | exact hΓS _ hFΓ | exact (hand (hΓS _ hFΓ)).1 | exact (hand (hΓS _ hFΓ)).2 | exact (hor (hΓS _ hFΓ)).1 | exact (hor (hΓS _ hFΓ)).2 | exact (himp (hΓS _ hFΓ)).1 | exact (himp (hΓS _ hFΓ)).2 | exact himpAnd (hΓS _ hFΓ) | exact (himpOr (hΓS _ hFΓ)).1 | exact (himpOr (hΓS _ hFΓ)).2 | exact himpImp (hΓS _ hFΓ) | exact (hand hCS).1 | exact (hand hCS).2 | exact (hor hCS).1 | exact (hor hCS).2 | exact (himp hCS).1 | exact (himp hCS).2) hΓS)))
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
                        (ihE (A₁.ifThen (B₁.ifThen B) :: Γ) (memS_cons_ab (by first | assumption | exact hCS | exact hΓS _ hFΓ | exact (hand (hΓS _ hFΓ)).1 | exact (hand (hΓS _ hFΓ)).2 | exact (hor (hΓS _ hFΓ)).1 | exact (hor (hΓS _ hFΓ)).2 | exact (himp (hΓS _ hFΓ)).1 | exact (himp (hΓS _ hFΓ)).2 | exact himpAnd (hΓS _ hFΓ) | exact (himpOr (hΓS _ hFΓ)).1 | exact (himpOr (hΓS _ hFΓ)).2 | exact himpImp (hΓS _ hFΓ) | exact (hand hCS).1 | exact (hand hCS).2 | exact (hor hCS).1 | exact (hor hCS).2 | exact (himp hCS).1 | exact (himp hCS).2) hΓS))
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
                        (ihE (A₁.ifThen B :: B₁.ifThen B :: Γ) (memS_cons₂_ab (by first | assumption | exact hCS | exact hΓS _ hFΓ | exact (hand (hΓS _ hFΓ)).1 | exact (hand (hΓS _ hFΓ)).2 | exact (hor (hΓS _ hFΓ)).1 | exact (hor (hΓS _ hFΓ)).2 | exact (himp (hΓS _ hFΓ)).1 | exact (himp (hΓS _ hFΓ)).2 | exact himpAnd (hΓS _ hFΓ) | exact (himpOr (hΓS _ hFΓ)).1 | exact (himpOr (hΓS _ hFΓ)).2 | exact himpImp (hΓS _ hFΓ) | exact (hand hCS).1 | exact (hand hCS).2 | exact (hor hCS).1 | exact (hor hCS).2 | exact (himp hCS).1 | exact (himp hCS).2) (by first | assumption | exact hCS | exact hΓS _ hFΓ | exact (hand (hΓS _ hFΓ)).1 | exact (hand (hΓS _ hFΓ)).2 | exact (hor (hΓS _ hFΓ)).1 | exact (hor (hΓS _ hFΓ)).2 | exact (himp (hΓS _ hFΓ)).1 | exact (himp (hΓS _ hFΓ)).2 | exact himpAnd (hΓS _ hFΓ) | exact (himpOr (hΓS _ hFΓ)).1 | exact (himpOr (hΓS _ hFΓ)).2 | exact himpImp (hΓS _ hFΓ) | exact (hand hCS).1 | exact (hand hCS).2 | exact (hor hCS).1 | exact (hor hCS).2 | exact (himp hCS).1 | exact (himp hCS).2) hΓS))
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
                              (cascade_impLImp_ant_bf p S hSbf hand hor himp fuel c hb Γ A₁ B₁ B
                                hΓS hABD
                                (G4c.identity_mem (.head _))
                                (G4c.identity_mem (.tail _ (.head _)))))
                            (ihE (B :: Γ) (memS_cons_ab (by first | assumption | exact hCS | exact hΓS _ hFΓ | exact (hand (hΓS _ hFΓ)).1 | exact (hand (hΓS _ hFΓ)).2 | exact (hor (hΓS _ hFΓ)).1 | exact (hor (hΓS _ hFΓ)).2 | exact (himp (hΓS _ hFΓ)).1 | exact (himp (hΓS _ hFΓ)).2 | exact himpAnd (hΓS _ hFΓ) | exact (himpOr (hΓS _ hFΓ)).1 | exact (himpOr (hΓS _ hFΓ)).2 | exact himpImp (hΓS _ hFΓ) | exact (hand hCS).1 | exact (hand hCS).2 | exact (hor hCS).1 | exact (hor hCS).2 | exact (himp hCS).1 | exact (himp hCS).2) hΓS))
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
                            (ihE (B :: Γ) (memS_cons_ab (by first | assumption | exact hCS | exact hΓS _ hFΓ | exact (hand (hΓS _ hFΓ)).1 | exact (hand (hΓS _ hFΓ)).2 | exact (hor (hΓS _ hFΓ)).1 | exact (hor (hΓS _ hFΓ)).2 | exact (himp (hΓS _ hFΓ)).1 | exact (himp (hΓS _ hFΓ)).2 | exact himpAnd (hΓS _ hFΓ) | exact (himpOr (hΓS _ hFΓ)).1 | exact (himpOr (hΓS _ hFΓ)).2 | exact himpImp (hΓS _ hFΓ) | exact (hand hCS).1 | exact (hand hCS).2 | exact (hor hCS).1 | exact (hor hCS).2 | exact (himp hCS).1 | exact (himp hCS).2) hΓS))
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
                                (ihE (B₁.ifThen B :: Γ) (memS_cons_ab (by first | assumption | exact hCS | exact hΓS _ hFΓ | exact (hand (hΓS _ hFΓ)).1 | exact (hand (hΓS _ hFΓ)).2 | exact (hor (hΓS _ hFΓ)).1 | exact (hor (hΓS _ hFΓ)).2 | exact (himp (hΓS _ hFΓ)).1 | exact (himp (hΓS _ hFΓ)).2 | exact himpAnd (hΓS _ hFΓ) | exact (himpOr (hΓS _ hFΓ)).1 | exact (himpOr (hΓS _ hFΓ)).2 | exact himpImp (hΓS _ hFΓ) | exact (hand hCS).1 | exact (hand hCS).2 | exact (hor hCS).1 | exact (hor hCS).2 | exact (himp hCS).1 | exact (himp hCS).2) hΓS))) ?_
                              (ihA (B₁.ifThen B :: Γ) (A₁.ifThen B₁) (memS_cons_ab (by first | assumption | exact hCS | exact hΓS _ hFΓ | exact (hand (hΓS _ hFΓ)).1 | exact (hand (hΓS _ hFΓ)).2 | exact (hor (hΓS _ hFΓ)).1 | exact (hor (hΓS _ hFΓ)).2 | exact (himp (hΓS _ hFΓ)).1 | exact (himp (hΓS _ hFΓ)).2 | exact himpAnd (hΓS _ hFΓ) | exact (himpOr (hΓS _ hFΓ)).1 | exact (himpOr (hΓS _ hFΓ)).2 | exact himpImp (hΓS _ hFΓ) | exact (hand hCS).1 | exact (hand hCS).2 | exact (hor hCS).1 | exact (hor hCS).2 | exact (himp hCS).1 | exact (himp hCS).2) hΓS) (by first | assumption | exact hCS | exact hΓS _ hFΓ | exact (hand (hΓS _ hFΓ)).1 | exact (hand (hΓS _ hFΓ)).2 | exact (hor (hΓS _ hFΓ)).1 | exact (hor (hΓS _ hFΓ)).2 | exact (himp (hΓS _ hFΓ)).1 | exact (himp (hΓS _ hFΓ)).2 | exact himpAnd (hΓS _ hFΓ) | exact (himpOr (hΓS _ hFΓ)).1 | exact (himpOr (hΓS _ hFΓ)).2 | exact himpImp (hΓS _ hFΓ) | exact (hand hCS).1 | exact (hand hCS).2 | exact (hor hCS).1 | exact (hor hCS).2 | exact (himp hCS).1 | exact (himp hCS).2))
                            exact fire (G4c.identity_mem (.tail _ (.head _)))
                              (consume₁ (G4c.identity_mem (.head _))
                                (ihE (B₁.ifThen B :: Γ) (memS_cons_ab (by first | assumption | exact hCS | exact hΓS _ hFΓ | exact (hand (hΓS _ hFΓ)).1 | exact (hand (hΓS _ hFΓ)).2 | exact (hor (hΓS _ hFΓ)).1 | exact (hor (hΓS _ hFΓ)).2 | exact (himp (hΓS _ hFΓ)).1 | exact (himp (hΓS _ hFΓ)).2 | exact himpAnd (hΓS _ hFΓ) | exact (himpOr (hΓS _ hFΓ)).1 | exact (himpOr (hΓS _ hFΓ)).2 | exact himpImp (hΓS _ hFΓ) | exact (hand hCS).1 | exact (hand hCS).2 | exact (hor hCS).1 | exact (hor hCS).2 | exact (himp hCS).1 | exact (himp hCS).2) hΓS)))
                        next => cases hin
                    next => cases hin
              | somehow A₁ =>
                  exact absurd (hSbf _ (hΓS _ hFΓ)) (by simp [boxFree])
      · -- A-half: [E@(fuel+1)@(c+2), A@(fuel+1)@(c+2)] ⊢ A@(fuel+1)@(c+1)
        intro Γ C hΓS hCS
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
                  (Nat.le_refl _)) (G4c.identity_mem (.head _)) (ihA Γ C₁ hΓS (by first | assumption | exact hCS | exact hΓS _ hFΓ | exact (hand (hΓS _ hFΓ)).1 | exact (hand (hΓS _ hFΓ)).2 | exact (hor (hΓS _ hFΓ)).1 | exact (hor (hΓS _ hFΓ)).2 | exact (himp (hΓS _ hFΓ)).1 | exact (himp (hΓS _ hFΓ)).2 | exact himpAnd (hΓS _ hFΓ) | exact (himpOr (hΓS _ hFΓ)).1 | exact (himpOr (hΓS _ hFΓ)).2 | exact himpImp (hΓS _ hFΓ) | exact (hand hCS).1 | exact (hand hCS).2 | exact (hor hCS).1 | exact (hor hCS).2 | exact (himp hCS).1 | exact (himp hCS).2))
              · exact consume₂ (amb_step (.tail _ (.tail _ (.head _)))
                  (Nat.le_refl _)) (G4c.identity_mem (.tail _ (.head _)))
                  (ihA Γ C₂ hΓS (by first | assumption | exact hCS | exact hΓS _ hFΓ | exact (hand (hΓS _ hFΓ)).1 | exact (hand (hΓS _ hFΓ)).2 | exact (hor (hΓS _ hFΓ)).1 | exact (hor (hΓS _ hFΓ)).2 | exact (himp (hΓS _ hFΓ)).1 | exact (himp (hΓS _ hFΓ)).2 | exact himpAnd (hΓS _ hFΓ) | exact (himpOr (hΓS _ hFΓ)).1 | exact (himpOr (hΓS _ hFΓ)).2 | exact himpImp (hΓS _ hFΓ) | exact (hand hCS).1 | exact (hand hCS).2 | exact (hor hCS).1 | exact (hor hCS).2 | exact (himp hCS).1 | exact (himp hCS).2))
          | or C₁ C₂ =>
              simp only [itpAgoal] at hφ ⊢
              rcases List.mem_cons.mp hφ with rfl | hφ'
              · refine ⟨itpA p S fuel (c + 1) Γ C₁, .head _, ?_⟩
                exact consume₂ (amb_step (.tail _ (.head _)) (Nat.le_refl _))
                  (G4c.identity_mem (.head _)) (ihA Γ C₁ hΓS (by first | assumption | exact hCS | exact hΓS _ hFΓ | exact (hand (hΓS _ hFΓ)).1 | exact (hand (hΓS _ hFΓ)).2 | exact (hor (hΓS _ hFΓ)).1 | exact (hor (hΓS _ hFΓ)).2 | exact (himp (hΓS _ hFΓ)).1 | exact (himp (hΓS _ hFΓ)).2 | exact himpAnd (hΓS _ hFΓ) | exact (himpOr (hΓS _ hFΓ)).1 | exact (himpOr (hΓS _ hFΓ)).2 | exact himpImp (hΓS _ hFΓ) | exact (hand hCS).1 | exact (hand hCS).2 | exact (hor hCS).1 | exact (hor hCS).2 | exact (himp hCS).1 | exact (himp hCS).2))
              · rcases List.mem_singleton.mp hφ' with rfl
                refine ⟨itpA p S fuel (c + 1) Γ C₂, .tail _ (.head _), ?_⟩
                exact consume₂ (amb_step (.tail _ (.head _)) (Nat.le_refl _))
                  (G4c.identity_mem (.head _)) (ihA Γ C₂ hΓS (by first | assumption | exact hCS | exact hΓS _ hFΓ | exact (hand (hΓS _ hFΓ)).1 | exact (hand (hΓS _ hFΓ)).2 | exact (hor (hΓS _ hFΓ)).1 | exact (hor (hΓS _ hFΓ)).2 | exact (himp (hΓS _ hFΓ)).1 | exact (himp (hΓS _ hFΓ)).2 | exact himpAnd (hΓS _ hFΓ) | exact (himpOr (hΓS _ hFΓ)).1 | exact (himpOr (hΓS _ hFΓ)).2 | exact himpImp (hΓS _ hFΓ) | exact (hand hCS).1 | exact (hand hCS).2 | exact (hor hCS).1 | exact (hor hCS).2 | exact (himp hCS).1 | exact (himp hCS).2))
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
                    (ihA (C₁ :: Γ) C₂ (memS_cons_ab (by first | assumption | exact hCS | exact hΓS _ hFΓ | exact (hand (hΓS _ hFΓ)).1 | exact (hand (hΓS _ hFΓ)).2 | exact (hor (hΓS _ hFΓ)).1 | exact (hor (hΓS _ hFΓ)).2 | exact (himp (hΓS _ hFΓ)).1 | exact (himp (hΓS _ hFΓ)).2 | exact himpAnd (hΓS _ hFΓ) | exact (himpOr (hΓS _ hFΓ)).1 | exact (himpOr (hΓS _ hFΓ)).2 | exact himpImp (hΓS _ hFΓ) | exact (hand hCS).1 | exact (hand hCS).2 | exact (hor hCS).1 | exact (hor hCS).2 | exact (himp hCS).1 | exact (himp hCS).2) hΓS) (by first | assumption | exact hCS | exact hΓS _ hFΓ | exact (hand (hΓS _ hFΓ)).1 | exact (hand (hΓS _ hFΓ)).2 | exact (hor (hΓS _ hFΓ)).1 | exact (hor (hΓS _ hFΓ)).2 | exact (himp (hΓS _ hFΓ)).1 | exact (himp (hΓS _ hFΓ)).2 | exact himpAnd (hΓS _ hFΓ) | exact (himpOr (hΓS _ hFΓ)).1 | exact (himpOr (hΓS _ hFΓ)).2 | exact himpImp (hΓS _ hFΓ) | exact (hand hCS).1 | exact (hand hCS).2 | exact (hor hCS).1 | exact (hor hCS).2 | exact (himp hCS).1 | exact (himp hCS).2))
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
                      (ihE (C₁ :: Γ) (memS_cons_ab (by first | assumption | exact hCS | exact hΓS _ hFΓ | exact (hand (hΓS _ hFΓ)).1 | exact (hand (hΓS _ hFΓ)).2 | exact (hor (hΓS _ hFΓ)).1 | exact (hor (hΓS _ hFΓ)).2 | exact (himp (hΓS _ hFΓ)).1 | exact (himp (hΓS _ hFΓ)).2 | exact himpAnd (hΓS _ hFΓ) | exact (himpOr (hΓS _ hFΓ)).1 | exact (himpOr (hΓS _ hFΓ)).2 | exact himpImp (hΓS _ hFΓ) | exact (hand hCS).1 | exact (hand hCS).2 | exact (hor hCS).1 | exact (hor hCS).2 | exact (himp hCS).1 | exact (himp hCS).2) hΓS))) ?_ (ihA (C₁ :: Γ) C₂ (memS_cons_ab (by first | assumption | exact hCS | exact hΓS _ hFΓ | exact (hand (hΓS _ hFΓ)).1 | exact (hand (hΓS _ hFΓ)).2 | exact (hor (hΓS _ hFΓ)).1 | exact (hor (hΓS _ hFΓ)).2 | exact (himp (hΓS _ hFΓ)).1 | exact (himp (hΓS _ hFΓ)).2 | exact himpAnd (hΓS _ hFΓ) | exact (himpOr (hΓS _ hFΓ)).1 | exact (himpOr (hΓS _ hFΓ)).2 | exact himpImp (hΓS _ hFΓ) | exact (hand hCS).1 | exact (hand hCS).2 | exact (hor hCS).1 | exact (hor hCS).2 | exact (himp hCS).1 | exact (himp hCS).2) hΓS) (by first | assumption | exact hCS | exact hΓS _ hFΓ | exact (hand (hΓS _ hFΓ)).1 | exact (hand (hΓS _ hFΓ)).2 | exact (hor (hΓS _ hFΓ)).1 | exact (hor (hΓS _ hFΓ)).2 | exact (himp (hΓS _ hFΓ)).1 | exact (himp (hΓS _ hFΓ)).2 | exact himpAnd (hΓS _ hFΓ) | exact (himpOr (hΓS _ hFΓ)).1 | exact (himpOr (hΓS _ hFΓ)).2 | exact himpImp (hΓS _ hFΓ) | exact (hand hCS).1 | exact (hand hCS).2 | exact (hor hCS).1 | exact (hor hCS).2 | exact (himp hCS).1 | exact (himp hCS).2))
                  exact fire (G4c.identity_mem (.tail _ (.head _)))
                    (consume₁ (G4c.identity_mem (.head _)) (ihE (C₁ :: Γ) (memS_cons_ab (by first | assumption | exact hCS | exact hΓS _ hFΓ | exact (hand (hΓS _ hFΓ)).1 | exact (hand (hΓS _ hFΓ)).2 | exact (hor (hΓS _ hFΓ)).1 | exact (hor (hΓS _ hFΓ)).2 | exact (himp (hΓS _ hFΓ)).1 | exact (himp (hΓS _ hFΓ)).2 | exact himpAnd (hΓS _ hFΓ) | exact (himpOr (hΓS _ hFΓ)).1 | exact (himpOr (hΓS _ hFΓ)).2 | exact himpImp (hΓS _ hFΓ) | exact (hand hCS).1 | exact (hand hCS).2 | exact (hor hCS).1 | exact (hor hCS).2 | exact (himp hCS).1 | exact (himp hCS).2) hΓS)))
          | somehow D =>
              exact absurd (hSbf _ hCS) (by simp [boxFree])
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
                      (G4c.identity_mem (.head _)) (ihA (A :: B :: Γ) C (memS_cons₂_ab (by first | assumption | exact hCS | exact hΓS _ hFΓ | exact (hand (hΓS _ hFΓ)).1 | exact (hand (hΓS _ hFΓ)).2 | exact (hor (hΓS _ hFΓ)).1 | exact (hor (hΓS _ hFΓ)).2 | exact (himp (hΓS _ hFΓ)).1 | exact (himp (hΓS _ hFΓ)).2 | exact himpAnd (hΓS _ hFΓ) | exact (himpOr (hΓS _ hFΓ)).1 | exact (himpOr (hΓS _ hFΓ)).2 | exact himpImp (hΓS _ hFΓ) | exact (hand hCS).1 | exact (hand hCS).2 | exact (hor hCS).1 | exact (hor hCS).2 | exact (himp hCS).1 | exact (himp hCS).2) (by first | assumption | exact hCS | exact hΓS _ hFΓ | exact (hand (hΓS _ hFΓ)).1 | exact (hand (hΓS _ hFΓ)).2 | exact (hor (hΓS _ hFΓ)).1 | exact (hor (hΓS _ hFΓ)).2 | exact (himp (hΓS _ hFΓ)).1 | exact (himp (hΓS _ hFΓ)).2 | exact himpAnd (hΓS _ hFΓ) | exact (himpOr (hΓS _ hFΓ)).1 | exact (himpOr (hΓS _ hFΓ)).2 | exact himpImp (hΓS _ hFΓ) | exact (hand hCS).1 | exact (hand hCS).2 | exact (hor hCS).1 | exact (hor hCS).2 | exact (himp hCS).1 | exact (himp hCS).2) hΓS) (by first | assumption | exact hCS | exact hΓS _ hFΓ | exact (hand (hΓS _ hFΓ)).1 | exact (hand (hΓS _ hFΓ)).2 | exact (hor (hΓS _ hFΓ)).1 | exact (hor (hΓS _ hFΓ)).2 | exact (himp (hΓS _ hFΓ)).1 | exact (himp (hΓS _ hFΓ)).2 | exact himpAnd (hΓS _ hFΓ) | exact (himpOr (hΓS _ hFΓ)).1 | exact (himpOr (hΓS _ hFΓ)).2 | exact himpImp (hΓS _ hFΓ) | exact (hand hCS).1 | exact (hand hCS).2 | exact (hor hCS).1 | exact (hor hCS).2 | exact (himp hCS).1 | exact (himp hCS).2))
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
                          (ihE (A :: Γ) (memS_cons_ab (by first | assumption | exact hCS | exact hΓS _ hFΓ | exact (hand (hΓS _ hFΓ)).1 | exact (hand (hΓS _ hFΓ)).2 | exact (hor (hΓS _ hFΓ)).1 | exact (hor (hΓS _ hFΓ)).2 | exact (himp (hΓS _ hFΓ)).1 | exact (himp (hΓS _ hFΓ)).2 | exact himpAnd (hΓS _ hFΓ) | exact (himpOr (hΓS _ hFΓ)).1 | exact (himpOr (hΓS _ hFΓ)).2 | exact himpImp (hΓS _ hFΓ) | exact (hand hCS).1 | exact (hand hCS).2 | exact (hor hCS).1 | exact (hor hCS).2 | exact (himp hCS).1 | exact (himp hCS).2) hΓS))) ?_ (ihA (A :: Γ) C (memS_cons_ab (by first | assumption | exact hCS | exact hΓS _ hFΓ | exact (hand (hΓS _ hFΓ)).1 | exact (hand (hΓS _ hFΓ)).2 | exact (hor (hΓS _ hFΓ)).1 | exact (hor (hΓS _ hFΓ)).2 | exact (himp (hΓS _ hFΓ)).1 | exact (himp (hΓS _ hFΓ)).2 | exact himpAnd (hΓS _ hFΓ) | exact (himpOr (hΓS _ hFΓ)).1 | exact (himpOr (hΓS _ hFΓ)).2 | exact himpImp (hΓS _ hFΓ) | exact (hand hCS).1 | exact (hand hCS).2 | exact (hor hCS).1 | exact (hor hCS).2 | exact (himp hCS).1 | exact (himp hCS).2) hΓS) (by first | assumption | exact hCS | exact hΓS _ hFΓ | exact (hand (hΓS _ hFΓ)).1 | exact (hand (hΓS _ hFΓ)).2 | exact (hor (hΓS _ hFΓ)).1 | exact (hor (hΓS _ hFΓ)).2 | exact (himp (hΓS _ hFΓ)).1 | exact (himp (hΓS _ hFΓ)).2 | exact himpAnd (hΓS _ hFΓ) | exact (himpOr (hΓS _ hFΓ)).1 | exact (himpOr (hΓS _ hFΓ)).2 | exact himpImp (hΓS _ hFΓ) | exact (hand hCS).1 | exact (hand hCS).2 | exact (hor hCS).1 | exact (hor hCS).2 | exact (himp hCS).1 | exact (himp hCS).2))
                      exact fire (G4c.identity_mem (.tail _ (.head _)))
                        (consume₁ (G4c.identity_mem (.head _)) (ihE (A :: Γ) (memS_cons_ab (by first | assumption | exact hCS | exact hΓS _ hFΓ | exact (hand (hΓS _ hFΓ)).1 | exact (hand (hΓS _ hFΓ)).2 | exact (hor (hΓS _ hFΓ)).1 | exact (hor (hΓS _ hFΓ)).2 | exact (himp (hΓS _ hFΓ)).1 | exact (himp (hΓS _ hFΓ)).2 | exact himpAnd (hΓS _ hFΓ) | exact (himpOr (hΓS _ hFΓ)).1 | exact (himpOr (hΓS _ hFΓ)).2 | exact himpImp (hΓS _ hFΓ) | exact (hand hCS).1 | exact (hand hCS).2 | exact (hor hCS).1 | exact (hor hCS).2 | exact (himp hCS).1 | exact (himp hCS).2) hΓS)))
                    · refine G4c.impR ?_
                      -- [E@(c+1)(B::Γ), φ₁, φ₂, Eamb]
                      refine consume₂ (consume₁ (G4c.identity_mem (.head _))
                          (ihE (B :: Γ) (memS_cons_ab (by first | assumption | exact hCS | exact hΓS _ hFΓ | exact (hand (hΓS _ hFΓ)).1 | exact (hand (hΓS _ hFΓ)).2 | exact (hor (hΓS _ hFΓ)).1 | exact (hor (hΓS _ hFΓ)).2 | exact (himp (hΓS _ hFΓ)).1 | exact (himp (hΓS _ hFΓ)).2 | exact himpAnd (hΓS _ hFΓ) | exact (himpOr (hΓS _ hFΓ)).1 | exact (himpOr (hΓS _ hFΓ)).2 | exact himpImp (hΓS _ hFΓ) | exact (hand hCS).1 | exact (hand hCS).2 | exact (hor hCS).1 | exact (hor hCS).2 | exact (himp hCS).1 | exact (himp hCS).2) hΓS))) ?_ (ihA (B :: Γ) C (memS_cons_ab (by first | assumption | exact hCS | exact hΓS _ hFΓ | exact (hand (hΓS _ hFΓ)).1 | exact (hand (hΓS _ hFΓ)).2 | exact (hor (hΓS _ hFΓ)).1 | exact (hor (hΓS _ hFΓ)).2 | exact (himp (hΓS _ hFΓ)).1 | exact (himp (hΓS _ hFΓ)).2 | exact himpAnd (hΓS _ hFΓ) | exact (himpOr (hΓS _ hFΓ)).1 | exact (himpOr (hΓS _ hFΓ)).2 | exact himpImp (hΓS _ hFΓ) | exact (hand hCS).1 | exact (hand hCS).2 | exact (hor hCS).1 | exact (hor hCS).2 | exact (himp hCS).1 | exact (himp hCS).2) hΓS) (by first | assumption | exact hCS | exact hΓS _ hFΓ | exact (hand (hΓS _ hFΓ)).1 | exact (hand (hΓS _ hFΓ)).2 | exact (hor (hΓS _ hFΓ)).1 | exact (hor (hΓS _ hFΓ)).2 | exact (himp (hΓS _ hFΓ)).1 | exact (himp (hΓS _ hFΓ)).2 | exact himpAnd (hΓS _ hFΓ) | exact (himpOr (hΓS _ hFΓ)).1 | exact (himpOr (hΓS _ hFΓ)).2 | exact himpImp (hΓS _ hFΓ) | exact (hand hCS).1 | exact (hand hCS).2 | exact (hor hCS).1 | exact (hor hCS).2 | exact (himp hCS).1 | exact (himp hCS).2))
                      exact fire (G4c.identity_mem
                          (.tail _ (.tail _ (.head _))))
                        (consume₁ (G4c.identity_mem (.head _)) (ihE (B :: Γ) (memS_cons_ab (by first | assumption | exact hCS | exact hΓS _ hFΓ | exact (hand (hΓS _ hFΓ)).1 | exact (hand (hΓS _ hFΓ)).2 | exact (hor (hΓS _ hFΓ)).1 | exact (hor (hΓS _ hFΓ)).2 | exact (himp (hΓS _ hFΓ)).1 | exact (himp (hΓS _ hFΓ)).2 | exact himpAnd (hΓS _ hFΓ) | exact (himpOr (hΓS _ hFΓ)).1 | exact (himpOr (hΓS _ hFΓ)).2 | exact himpImp (hΓS _ hFΓ) | exact (hand hCS).1 | exact (hand hCS).2 | exact (hor hCS).1 | exact (hor hCS).2 | exact (himp hCS).1 | exact (himp hCS).2) hΓS)))
                next => cases hin
          | somehow χ =>
              exact absurd (hSbf _ (hΓS _ hFΓ)) (by simp [boxFree])
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
                            (G4c.identity_mem (.head _)) (ihA (B :: Γ) C (memS_cons_ab (by first | assumption | exact hCS | exact hΓS _ hFΓ | exact (hand (hΓS _ hFΓ)).1 | exact (hand (hΓS _ hFΓ)).2 | exact (hor (hΓS _ hFΓ)).1 | exact (hor (hΓS _ hFΓ)).2 | exact (himp (hΓS _ hFΓ)).1 | exact (himp (hΓS _ hFΓ)).2 | exact himpAnd (hΓS _ hFΓ) | exact (himpOr (hΓS _ hFΓ)).1 | exact (himpOr (hΓS _ hFΓ)).2 | exact himpImp (hΓS _ hFΓ) | exact (hand hCS).1 | exact (hand hCS).2 | exact (hor hCS).1 | exact (hor hCS).2 | exact (himp hCS).1 | exact (himp hCS).2) hΓS) (by first | assumption | exact hCS | exact hΓS _ hFΓ | exact (hand (hΓS _ hFΓ)).1 | exact (hand (hΓS _ hFΓ)).2 | exact (hor (hΓS _ hFΓ)).1 | exact (hor (hΓS _ hFΓ)).2 | exact (himp (hΓS _ hFΓ)).1 | exact (himp (hΓS _ hFΓ)).2 | exact himpAnd (hΓS _ hFΓ) | exact (himpOr (hΓS _ hFΓ)).1 | exact (himpOr (hΓS _ hFΓ)).2 | exact himpImp (hΓS _ hFΓ) | exact (hand hCS).1 | exact (hand hCS).2 | exact (hor hCS).1 | exact (hor hCS).2 | exact (himp hCS).1 | exact (himp hCS).2))
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
                              (ihA (B :: Γ) C (memS_cons_ab (by first | assumption | exact hCS | exact hΓS _ hFΓ | exact (hand (hΓS _ hFΓ)).1 | exact (hand (hΓS _ hFΓ)).2 | exact (hor (hΓS _ hFΓ)).1 | exact (hor (hΓS _ hFΓ)).2 | exact (himp (hΓS _ hFΓ)).1 | exact (himp (hΓS _ hFΓ)).2 | exact himpAnd (hΓS _ hFΓ) | exact (himpOr (hΓS _ hFΓ)).1 | exact (himpOr (hΓS _ hFΓ)).2 | exact himpImp (hΓS _ hFΓ) | exact (hand hCS).1 | exact (hand hCS).2 | exact (hor hCS).1 | exact (hor hCS).2 | exact (himp hCS).1 | exact (himp hCS).2) hΓS) (by first | assumption | exact hCS | exact hΓS _ hFΓ | exact (hand (hΓS _ hFΓ)).1 | exact (hand (hΓS _ hFΓ)).2 | exact (hor (hΓS _ hFΓ)).1 | exact (hor (hΓS _ hFΓ)).2 | exact (himp (hΓS _ hFΓ)).1 | exact (himp (hΓS _ hFΓ)).2 | exact himpAnd (hΓS _ hFΓ) | exact (himpOr (hΓS _ hFΓ)).1 | exact (himpOr (hΓS _ hFΓ)).2 | exact himpImp (hΓS _ hFΓ) | exact (hand hCS).1 | exact (hand hCS).2 | exact (hor hCS).1 | exact (hor hCS).2 | exact (himp hCS).1 | exact (himp hCS).2))
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
                          (ihA (A₁.ifThen (B₁.ifThen B) :: Γ) C (memS_cons_ab (by first | assumption | exact hCS | exact hΓS _ hFΓ | exact (hand (hΓS _ hFΓ)).1 | exact (hand (hΓS _ hFΓ)).2 | exact (hor (hΓS _ hFΓ)).1 | exact (hor (hΓS _ hFΓ)).2 | exact (himp (hΓS _ hFΓ)).1 | exact (himp (hΓS _ hFΓ)).2 | exact himpAnd (hΓS _ hFΓ) | exact (himpOr (hΓS _ hFΓ)).1 | exact (himpOr (hΓS _ hFΓ)).2 | exact himpImp (hΓS _ hFΓ) | exact (hand hCS).1 | exact (hand hCS).2 | exact (hor hCS).1 | exact (hor hCS).2 | exact (himp hCS).1 | exact (himp hCS).2) hΓS) (by first | assumption | exact hCS | exact hΓS _ hFΓ | exact (hand (hΓS _ hFΓ)).1 | exact (hand (hΓS _ hFΓ)).2 | exact (hor (hΓS _ hFΓ)).1 | exact (hor (hΓS _ hFΓ)).2 | exact (himp (hΓS _ hFΓ)).1 | exact (himp (hΓS _ hFΓ)).2 | exact himpAnd (hΓS _ hFΓ) | exact (himpOr (hΓS _ hFΓ)).1 | exact (himpOr (hΓS _ hFΓ)).2 | exact himpImp (hΓS _ hFΓ) | exact (hand hCS).1 | exact (hand hCS).2 | exact (hor hCS).1 | exact (hor hCS).2 | exact (himp hCS).1 | exact (himp hCS).2))
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
                          (ihA (A₁.ifThen B :: B₁.ifThen B :: Γ) C (memS_cons₂_ab (by first | assumption | exact hCS | exact hΓS _ hFΓ | exact (hand (hΓS _ hFΓ)).1 | exact (hand (hΓS _ hFΓ)).2 | exact (hor (hΓS _ hFΓ)).1 | exact (hor (hΓS _ hFΓ)).2 | exact (himp (hΓS _ hFΓ)).1 | exact (himp (hΓS _ hFΓ)).2 | exact himpAnd (hΓS _ hFΓ) | exact (himpOr (hΓS _ hFΓ)).1 | exact (himpOr (hΓS _ hFΓ)).2 | exact himpImp (hΓS _ hFΓ) | exact (hand hCS).1 | exact (hand hCS).2 | exact (hor hCS).1 | exact (hor hCS).2 | exact (himp hCS).1 | exact (himp hCS).2) (by first | assumption | exact hCS | exact hΓS _ hFΓ | exact (hand (hΓS _ hFΓ)).1 | exact (hand (hΓS _ hFΓ)).2 | exact (hor (hΓS _ hFΓ)).1 | exact (hor (hΓS _ hFΓ)).2 | exact (himp (hΓS _ hFΓ)).1 | exact (himp (hΓS _ hFΓ)).2 | exact himpAnd (hΓS _ hFΓ) | exact (himpOr (hΓS _ hFΓ)).1 | exact (himpOr (hΓS _ hFΓ)).2 | exact himpImp (hΓS _ hFΓ) | exact (hand hCS).1 | exact (hand hCS).2 | exact (hor hCS).1 | exact (hor hCS).2 | exact (himp hCS).1 | exact (himp hCS).2) hΓS) (by first | assumption | exact hCS | exact hΓS _ hFΓ | exact (hand (hΓS _ hFΓ)).1 | exact (hand (hΓS _ hFΓ)).2 | exact (hor (hΓS _ hFΓ)).1 | exact (hor (hΓS _ hFΓ)).2 | exact (himp (hΓS _ hFΓ)).1 | exact (himp (hΓS _ hFΓ)).2 | exact himpAnd (hΓS _ hFΓ) | exact (himpOr (hΓS _ hFΓ)).1 | exact (himpOr (hΓS _ hFΓ)).2 | exact himpImp (hΓS _ hFΓ) | exact (hand hCS).1 | exact (hand hCS).2 | exact (hor hCS).1 | exact (hor hCS).2 | exact (himp hCS).1 | exact (himp hCS).2))
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
                              exact cascade_impLImp_ant_bf p S hSbf hand hor himp fuel c hb Γ
                                A₁ B₁ B hΓS hABD
                                (G4c.identity_mem (.head _))
                                (amb_pack_step (.tail _ (.tail _ (.head _)))
                                  (Nat.le_succ _))
                            · -- [J, K, Eamb] ⊢ A@(c+1)(B::Γ)C
                              refine consume₂ ?_
                                (G4c.identity_mem (.tail _ (.head _)))
                                (ihA (B :: Γ) C (memS_cons_ab (by first | assumption | exact hCS | exact hΓS _ hFΓ | exact (hand (hΓS _ hFΓ)).1 | exact (hand (hΓS _ hFΓ)).2 | exact (hor (hΓS _ hFΓ)).1 | exact (hor (hΓS _ hFΓ)).2 | exact (himp (hΓS _ hFΓ)).1 | exact (himp (hΓS _ hFΓ)).2 | exact himpAnd (hΓS _ hFΓ) | exact (himpOr (hΓS _ hFΓ)).1 | exact (himpOr (hΓS _ hFΓ)).2 | exact himpImp (hΓS _ hFΓ) | exact (hand hCS).1 | exact (hand hCS).2 | exact (hor hCS).1 | exact (hor hCS).2 | exact (himp hCS).1 | exact (himp hCS).2) hΓS) (by first | assumption | exact hCS | exact hΓS _ hFΓ | exact (hand (hΓS _ hFΓ)).1 | exact (hand (hΓS _ hFΓ)).2 | exact (hor (hΓS _ hFΓ)).1 | exact (hor (hΓS _ hFΓ)).2 | exact (himp (hΓS _ hFΓ)).1 | exact (himp (hΓS _ hFΓ)).2 | exact himpAnd (hΓS _ hFΓ) | exact (himpOr (hΓS _ hFΓ)).1 | exact (himpOr (hΓS _ hFΓ)).2 | exact himpImp (hΓS _ hFΓ) | exact (hand hCS).1 | exact (hand hCS).2 | exact (hor hCS).1 | exact (hor hCS).2 | exact (himp hCS).1 | exact (himp hCS).2))
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
                                  (ihE (B₁.ifThen B :: Γ) (memS_cons_ab (by first | assumption | exact hCS | exact hΓS _ hFΓ | exact (hand (hΓS _ hFΓ)).1 | exact (hand (hΓS _ hFΓ)).2 | exact (hor (hΓS _ hFΓ)).1 | exact (hor (hΓS _ hFΓ)).2 | exact (himp (hΓS _ hFΓ)).1 | exact (himp (hΓS _ hFΓ)).2 | exact himpAnd (hΓS _ hFΓ) | exact (himpOr (hΓS _ hFΓ)).1 | exact (himpOr (hΓS _ hFΓ)).2 | exact himpImp (hΓS _ hFΓ) | exact (hand hCS).1 | exact (hand hCS).2 | exact (hor hCS).1 | exact (hor hCS).2 | exact (himp hCS).1 | exact (himp hCS).2) hΓS))) ?_
                                (ihA (B₁.ifThen B :: Γ) (A₁.ifThen B₁) (memS_cons_ab (by first | assumption | exact hCS | exact hΓS _ hFΓ | exact (hand (hΓS _ hFΓ)).1 | exact (hand (hΓS _ hFΓ)).2 | exact (hor (hΓS _ hFΓ)).1 | exact (hor (hΓS _ hFΓ)).2 | exact (himp (hΓS _ hFΓ)).1 | exact (himp (hΓS _ hFΓ)).2 | exact himpAnd (hΓS _ hFΓ) | exact (himpOr (hΓS _ hFΓ)).1 | exact (himpOr (hΓS _ hFΓ)).2 | exact himpImp (hΓS _ hFΓ) | exact (hand hCS).1 | exact (hand hCS).2 | exact (hor hCS).1 | exact (hor hCS).2 | exact (himp hCS).1 | exact (himp hCS).2) hΓS) (by first | assumption | exact hCS | exact hΓS _ hFΓ | exact (hand (hΓS _ hFΓ)).1 | exact (hand (hΓS _ hFΓ)).2 | exact (hor (hΓS _ hFΓ)).1 | exact (hor (hΓS _ hFΓ)).2 | exact (himp (hΓS _ hFΓ)).1 | exact (himp (hΓS _ hFΓ)).2 | exact himpAnd (hΓS _ hFΓ) | exact (himpOr (hΓS _ hFΓ)).1 | exact (himpOr (hΓS _ hFΓ)).2 | exact himpImp (hΓS _ hFΓ) | exact (hand hCS).1 | exact (hand hCS).2 | exact (hor hCS).1 | exact (hor hCS).2 | exact (himp hCS).1 | exact (himp hCS).2))
                              exact fire
                                (G4c.identity_mem (.tail _ (.head _)))
                                (consume₁ (G4c.identity_mem (.head _))
                                  (ihE (B₁.ifThen B :: Γ) (memS_cons_ab (by first | assumption | exact hCS | exact hΓS _ hFΓ | exact (hand (hΓS _ hFΓ)).1 | exact (hand (hΓS _ hFΓ)).2 | exact (hor (hΓS _ hFΓ)).1 | exact (hor (hΓS _ hFΓ)).2 | exact (himp (hΓS _ hFΓ)).1 | exact (himp (hΓS _ hFΓ)).2 | exact himpAnd (hΓS _ hFΓ) | exact (himpOr (hΓS _ hFΓ)).1 | exact (himpOr (hΓS _ hFΓ)).2 | exact himpImp (hΓS _ hFΓ) | exact (hand hCS).1 | exact (hand hCS).2 | exact (hor hCS).1 | exact (hor hCS).2 | exact (himp hCS).1 | exact (himp hCS).2) hΓS)))
                            · -- second: identity-fire of the ambient's conjunct
                              refine consume₂ ?_
                                (G4c.identity_mem (.tail _ (.head _)))
                                (ihA (B :: Γ) C (memS_cons_ab (by first | assumption | exact hCS | exact hΓS _ hFΓ | exact (hand (hΓS _ hFΓ)).1 | exact (hand (hΓS _ hFΓ)).2 | exact (hor (hΓS _ hFΓ)).1 | exact (hor (hΓS _ hFΓ)).2 | exact (himp (hΓS _ hFΓ)).1 | exact (himp (hΓS _ hFΓ)).2 | exact himpAnd (hΓS _ hFΓ) | exact (himpOr (hΓS _ hFΓ)).1 | exact (himpOr (hΓS _ hFΓ)).2 | exact himpImp (hΓS _ hFΓ) | exact (hand hCS).1 | exact (hand hCS).2 | exact (hor hCS).1 | exact (hor hCS).2 | exact (himp hCS).1 | exact (himp hCS).2) hΓS) (by first | assumption | exact hCS | exact hΓS _ hFΓ | exact (hand (hΓS _ hFΓ)).1 | exact (hand (hΓS _ hFΓ)).2 | exact (hor (hΓS _ hFΓ)).1 | exact (hor (hΓS _ hFΓ)).2 | exact (himp (hΓS _ hFΓ)).1 | exact (himp (hΓS _ hFΓ)).2 | exact himpAnd (hΓS _ hFΓ) | exact (himpOr (hΓS _ hFΓ)).1 | exact (himpOr (hΓS _ hFΓ)).2 | exact himpImp (hΓS _ hFΓ) | exact (hand hCS).1 | exact (hand hCS).2 | exact (hor hCS).1 | exact (hor hCS).2 | exact (himp hCS).1 | exact (himp hCS).2))
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
                  exact absurd (hSbf _ (hΓS _ hFΓ)) (by simp [boxFree])
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

/-- Box-free ambient-relative budget stabilization: `itp_stab`'s
conclusion under the box-free / piece-closure side conditions and the
threaded context/goal membership invariants.  Sorry-free (routes
through `cascade_main_bf`, not `cascade_main`). -/
theorem itp_stab_bf (p : String) (S : Finset PLLFormula)
    (hSbf : ∀ F ∈ S, boxFree F)
    (hand : ∀ {A B : PLLFormula}, A.and B ∈ S → A ∈ S ∧ B ∈ S)
    (hor : ∀ {A B : PLLFormula}, A.or B ∈ S → A ∈ S ∧ B ∈ S)
    (himp : ∀ {A B : PLLFormula}, A.ifThen B ∈ S → A ∈ S ∧ B ∈ S)
    (himpAnd : ∀ {A B D : PLLFormula},
      (A.and B).ifThen D ∈ S → A.ifThen (B.ifThen D) ∈ S)
    (himpOr : ∀ {A B D : PLLFormula},
      (A.or B).ifThen D ∈ S → A.ifThen D ∈ S ∧ B.ifThen D ∈ S)
    (himpImp : ∀ {A B D : PLLFormula},
      (A.ifThen B).ifThen D ∈ S → B.ifThen D ∈ S) :
    ∀ (fuel : Nat) (b : Nat), kcap S < b →
    (∀ Γ, (∀ F ∈ Γ, F ∈ S) →
      G4c [itpE p S fuel (b - 1) Γ] (itpE p S fuel b Γ)) ∧
    (∀ Γ C, (∀ F ∈ Γ, F ∈ S) → C ∈ S →
      G4c [itpE p S fuel b Γ, itpA p S fuel b Γ C]
      (itpA p S fuel (b - 1) Γ C)) := by
  intro fuel b hb
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 2 :=
    ⟨b - 2, by have := kcap_ge (S := S); omega⟩
  exact itp_stab_aux_bf p S hSbf hand hor himp himpAnd himpOr himpImp fuel c hb

/-- Box-free consumption form (mirror of `itp_stab_le`): the packaged
budget value feeds any lower slot above the threshold, under the
box-free side conditions and the threaded membership invariants. -/
theorem itp_stab_le_bf (p : String) (S : Finset PLLFormula)
    (hSbf : ∀ F ∈ S, boxFree F)
    (hand : ∀ {A B : PLLFormula}, A.and B ∈ S → A ∈ S ∧ B ∈ S)
    (hor : ∀ {A B : PLLFormula}, A.or B ∈ S → A ∈ S ∧ B ∈ S)
    (himp : ∀ {A B : PLLFormula}, A.ifThen B ∈ S → A ∈ S ∧ B ∈ S)
    (himpAnd : ∀ {A B D : PLLFormula},
      (A.and B).ifThen D ∈ S → A.ifThen (B.ifThen D) ∈ S)
    (himpOr : ∀ {A B D : PLLFormula},
      (A.or B).ifThen D ∈ S → A.ifThen D ∈ S ∧ B.ifThen D ∈ S)
    (himpImp : ∀ {A B D : PLLFormula},
      (A.ifThen B).ifThen D ∈ S → B.ifThen D ∈ S)
    {fuel b b' : Nat} (hk : kcap S < b') (hle : b' ≤ b) :
    (∀ Γ, (∀ F ∈ Γ, F ∈ S) →
      G4c [itpE p S fuel b' Γ] (itpE p S fuel b Γ)) ∧
    (∀ Γ C, (∀ F ∈ Γ, F ∈ S) → C ∈ S →
      G4c [itpE p S fuel b Γ, itpA p S fuel b Γ C]
      (itpA p S fuel b' Γ C)) := by
  induction hle with
  | refl =>
      exact ⟨fun Γ _ => G4c.iden (.head _),
        fun Γ C _ _ => G4c.identity_mem (.tail _ (.head _))⟩
  | @step m hm ih =>
      obtain ⟨ihE, ihA⟩ := ih
      have hm' : b' ≤ m := hm
      have hkm : kcap S < m + 1 := by omega
      constructor
      · intro Γ hΓS
        refine consume₁ (ihE Γ hΓS) ?_
        exact (itp_stab_bf p S hSbf hand hor himp himpAnd himpOr himpImp
          fuel (m + 1) hkm).1 Γ hΓS
      · intro Γ C hΓS hCS
        have d1 : G4c [itpE p S fuel (m + 1) Γ, itpA p S fuel (m + 1) Γ C]
            (itpA p S fuel m Γ C) :=
          (itp_stab_bf p S hSbf hand hor himp himpAnd himpOr himpImp
            fuel (m + 1) hkm).2 Γ C hΓS hCS
        have d2 : G4c [itpE p S fuel (m + 1) Γ, itpA p S fuel (m + 1) Γ C]
            (itpE p S fuel m Γ) :=
          consume₁ (G4c.identity_mem (.head _))
            ((itp_budget_mono p S fuel).1 m Γ)
        exact consume₂ d2 d1 (ihA Γ C hΓS hCS)

end PLLND
