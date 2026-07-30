import wip.atomForce
import wip.envDesc

/-!
# The boxed floor branch: the traversal, shape by shape

PROGRESS §102 leaves the boxed row needing one thing: from the source's second
component — a universal table at a grown context with the boxed goal `◯q` — reach the
*goal-clause* disjunct at some grown context, since `AtomForce.boxGoal_remap` then
carries it back to `Γ`.

§103 records why the natural abstraction ("the ambient at any larger context follows
from the ambient") must not be used: it is the existential ascent, and it is refuted.
The grown ambient has to be obtained **shape by shape**, and §103's table says how.

This file does the traversal.  The recursion is on the **defect**; at fuel `0` every
component is `⊤` or `⊥` and the boxed disjunct explodes.

## Scope

A `∨`-free space (inherited from `itpA_atom_forces`) and an **atom** boxed goal `◯q`
with `q ≠ p` — the shape the recursion reaches when the space's γ-heads are atomic.
-/

open PLLFormula

namespace PLLND
namespace BoxSnd

open GoalDesc AtomForce EnvDesc

/-- Project a conjunct out of a derivable `andAll`. -/
theorem projAll {Δ l : List PLLFormula} {φ : PLLFormula}
    (d : G4c Δ (andAll l)) (h : φ ∈ l) : G4c Δ φ :=
  G4c.cut d (G4c.andAll_elim h (G4c.identity_mem (.head _)))

/-- The target of the traversal: the boxed goal clause at `Γ`. -/
abbrev tgtClause (p : String) (S : Finset PLLFormula) (f c : Nat)
    (Γ : List PLLFormula) (q : String) : PLLFormula :=
  ((itpE p S f c Γ).ifThen (itpA p S (f + 1) (c + 1) Γ (prop q))).somehow

/-! ## The ungated projections

For each ungated context shape, the ambient's own clause for that formula is the
grown ambient at the context the `itpA` disjunct grows to.  These are pure
projections out of `itpEcls`; each is stated separately so the induction below reads
as the mathematics rather than as guard bookkeeping. -/

/-- `A ∧ B ∈ Γ'`: the ambient's clause **is** the grown ambient. -/
theorem grown_and (p : String) (S : Finset PLLFormula) {f c : Nat}
    {Γ' Δ : List PLLFormula} {A B : PLLFormula}
    (hF : A.and B ∈ Γ') (h1 : ¬(A ∈ Γ' ∧ B ∈ Γ'))
    (h2 : (A ∈ Γ' ∨ A ∈ S) ∧ (B ∈ Γ' ∨ B ∈ S))
    (hamb : G4c Δ (itpE p S (f + 1) (c + 2) Γ')) :
    G4c Δ (itpE p S f (c + 2) (A :: B :: Γ')) := by
  rw [itpE_succ] at hamb
  refine projAll hamb ?_
  unfold itpEcls
  refine List.mem_append.mpr (Or.inr ?_)
  refine List.mem_flatMap.mpr ⟨A.and B, hF, ?_⟩
  simp only [if_neg h1, if_pos h2]
  exact List.mem_singleton.mpr rfl

/-- `(prop q') ⊃ B ∈ Γ'` with `prop q' ∈ Γ'`: the ambient's clause is the grown
ambient outright. -/
theorem grown_impAtom_pres (p : String) (S : Finset PLLFormula) {f c : Nat}
    {Γ' Δ : List PLLFormula} {q' : String} {B : PLLFormula}
    (hF : (prop q').ifThen B ∈ Γ') (h1 : B ∉ Γ') (h2 : B ∈ S)
    (h3 : (prop q' : PLLFormula) ∈ Γ')
    (hamb : G4c Δ (itpE p S (f + 1) (c + 2) Γ')) :
    G4c Δ (itpE p S f (c + 2) (B :: Γ')) := by
  rw [itpE_succ] at hamb
  refine projAll hamb ?_
  unfold itpEcls
  refine List.mem_append.mpr (Or.inr ?_)
  refine List.mem_flatMap.mpr ⟨(prop q').ifThen B, hF, ?_⟩
  simp only [if_neg h1, if_pos h2, if_pos h3]
  exact List.mem_singleton.mpr rfl

/-- `(A ∧ B) ⊃ D ∈ Γ'`: the ambient's clause is the grown ambient at the curried
context. -/
theorem grown_impAnd (p : String) (S : Finset PLLFormula) {f c : Nat}
    {Γ' Δ : List PLLFormula} {A B D : PLLFormula}
    (hF : (A.and B).ifThen D ∈ Γ') (h1 : A.ifThen (B.ifThen D) ∉ Γ')
    (h2 : A.ifThen (B.ifThen D) ∈ S)
    (hamb : G4c Δ (itpE p S (f + 1) (c + 2) Γ')) :
    G4c Δ (itpE p S f (c + 2) (A.ifThen (B.ifThen D) :: Γ')) := by
  rw [itpE_succ] at hamb
  refine projAll hamb ?_
  unfold itpEcls
  refine List.mem_append.mpr (Or.inr ?_)
  refine List.mem_flatMap.mpr ⟨(A.and B).ifThen D, hF, ?_⟩
  simp only [if_neg h1, if_pos h2]
  exact List.mem_singleton.mpr rfl

/-- `(A ∨ B) ⊃ D ∈ Γ'`: the ambient's clause is the grown ambient at the split
context. -/
theorem grown_impOr (p : String) (S : Finset PLLFormula) {f c : Nat}
    {Γ' Δ : List PLLFormula} {A B D : PLLFormula}
    (hF : (A.or B).ifThen D ∈ Γ')
    (h1 : ¬(A.ifThen D ∈ Γ' ∧ B.ifThen D ∈ Γ'))
    (h2 : (A.ifThen D ∈ Γ' ∨ A.ifThen D ∈ S) ∧
      (B.ifThen D ∈ Γ' ∨ B.ifThen D ∈ S))
    (hamb : G4c Δ (itpE p S (f + 1) (c + 2) Γ')) :
    G4c Δ (itpE p S f (c + 2) (A.ifThen D :: B.ifThen D :: Γ')) := by
  rw [itpE_succ] at hamb
  refine projAll hamb ?_
  unfold itpEcls
  refine List.mem_append.mpr (Or.inr ?_)
  refine List.mem_flatMap.mpr ⟨(A.or B).ifThen D, hF, ?_⟩
  simp only [if_neg h1, if_pos h2]
  exact List.mem_singleton.mpr rfl

/-- `◯χ ∈ Γ'`: the ambient's clause is the grown ambient **under a `◯`** — which is
the form the `itpA` disjunct for `◯χ` can use, since that disjunct is boxed too. -/
theorem grown_box (p : String) (S : Finset PLLFormula) {f c : Nat}
    {Γ' Δ : List PLLFormula} {χ : PLLFormula}
    (hF : χ.somehow ∈ Γ') (h1 : ¬(χ ∈ Γ' ∨ χ ∉ S))
    (hamb : G4c Δ (itpE p S (f + 1) (c + 2) Γ')) :
    G4c Δ ((itpE p S f (c + 2) (χ :: Γ')).somehow) := by
  rw [itpE_succ] at hamb
  refine projAll hamb ?_
  unfold itpEcls
  refine List.mem_append.mpr (Or.inr ?_)
  refine List.mem_flatMap.mpr ⟨χ.somehow, hF, ?_⟩
  simp only [if_neg h1]
  exact List.mem_singleton.mpr rfl

/-! ## The two boxed cases, named

Two disjunct families are boxed on both sides, so closing them means pairing two
`laxL`s and working at the `⊳`-successor.  They are stated here as named
propositions so that the traversal below is sorry-free and the remaining obligations
are explicit and small.

* `BoxCtxCase` — the `◯χ ∈ Γ'` environment family.  Its disjunct is
  `◯( E@(c+1)(χ::Γ') ⇢ A@(c+1)(χ::Γ', ◯q) )` and `grown_box` supplies
  `◯ E@(c+2)(χ::Γ')`: both boxed, to be paired.
* `TruncCase` — the truncation disjunct `◯( E@c(Γ') ⇢ ⋁ others )`, to be opened by
  `laxL` (legitimate, since the conclusion is `◯`-shaped) and then handled by the
  same case analysis one level in. -/

/-- The `◯χ` environment family of the traversal. -/
def BoxCtxCase (p : String) (S : Finset PLLFormula) (q : String) : Prop :=
  ∀ (f c : Nat) (Γ Γ' Δ : List PLLFormula) (χ : PLLFormula),
    χ.somehow ∈ Γ' → χ ∈ S → χ ∉ Γ' → (∀ Y ∈ Γ', Y ∈ S) →
    G4c Δ ((itpE p S f (c + 2) (χ :: Γ')).somehow) →
    G4c Δ (((itpE p S f (c + 1) (χ :: Γ')).ifThen
      (itpA p S f (c + 1) (χ :: Γ') ((prop q).somehow))).somehow) →
    G4c Δ (tgtClause p S f c Γ q)

/-- The truncation disjunct of the traversal. -/
def TruncCase (p : String) (S : Finset PLLFormula) (q : String) : Prop :=
  ∀ (f c : Nat) (Γ Γ' Δ : List PLLFormula),
    (∀ Y ∈ Γ', Y ∈ S) →
    G4c Δ (itpE p S (f + 1) (c + 2) Γ') →
    G4c Δ (((itpE p S f c Γ').ifThen
      (orAll (itpAoth p S f (c + 1) Γ' ((prop q).somehow)))).somehow) →
    G4c Δ (tgtClause p S f c Γ q)

/-- The `⊃`-headed environment families (`(prop q')⊃B`, `(A∧B)⊃D`, `(A∨B)⊃D`,
`(A⊃B)⊃D`, `◯A⊃B`).  Their grown ambients are `grown_impAtom_pres`, `grown_impAnd`,
`grown_impOr` and — for the two gated ones — `EnvDesc.grownAmb_of_plain` and
`grownAmb_of_box`; what remains is the guard bookkeeping. -/
def ImpCase (p : String) (S : Finset PLLFormula) (q : String) : Prop :=
  ∀ (f c : Nat) (Γ Γ' Δ : List PLLFormula) (A D : PLLFormula) (φ : PLLFormula),
    A.ifThen D ∈ Γ' → (∀ Y ∈ Γ', Y ∈ S) →
    φ ∈ itpAenv p S f (c + 1) Γ' ((prop q).somehow) →
    G4c Δ (itpE p S (f + 1) (c + 2) Γ') → G4c Δ φ →
    G4c Δ (tgtClause p S f c Γ q)

/-- The fuel-`0` floor of the traversal: every component of every disjunct is `⊤` or
`⊥`, so each disjunct either explodes or is absurd. -/
def ZeroFuelCase (p : String) (S : Finset PLLFormula) (q : String) : Prop :=
  ∀ (c : Nat) (Γ Γ' Δ : List PLLFormula) (φ : PLLFormula),
    φ ∈ itpAenv p S 0 (c + 1) Γ' ((prop q).somehow) →
    G4c Δ φ → G4c Δ (tgtClause p S 0 c Γ q)

/-- **The target lifts in the fuel**, both conversions free: the guard converts
*down* (`fuelE_le`) and the value converts *up* (`itp_fuel_mono`), which is exactly
the direction each is free in. -/
theorem tgtClause_fuel_lift (p : String) (S : Finset PLLFormula) {f c : Nat}
    {Γ Δ : List PLLFormula} {q : String}
    (d : G4c Δ (tgtClause p S f c Γ q)) :
    G4c Δ (tgtClause p S (f + 1) c Γ q) := by
  refine box_remap_free d ?_ ?_
  · exact consume₁ (G4c.identity_mem (.head _)) (fuelE_le p S (Nat.le_succ f) c Γ)
  · exact consume₁ (G4c.identity_mem (.head _))
      ((itp_fuel_mono p S (f + 1)).2 (c + 1) Γ (prop q))

/-! ## The traversal -/

set_option maxHeartbeats 1000000 in
/-- **The traversal.**  From the ambient and the second component at a grown context
`Γ'`, reach the boxed goal clause at `Γ`.  Recursion on the defect.

Proved outright: the **goal clause** (by `boxGoal_remap`, the mathematically
substantive case), the `∧` environment family (by `grown_and` and the recursion), and
the vacuous families (`prop`, `⊥`, `∨` — the last excluded by `∨`-freeness).  The four
named hypotheses carry the remaining case work. -/
theorem boxSnd_reaches (p : String) (S : Finset PLLFormula)
    (hOr : ∀ A B : PLLFormula, A.or B ∉ S) {q : String} (hq : q ≠ p)
    (hsome : ∀ {A : PLLFormula}, A.somehow ∈ S → A ∈ S)
    (hbc : BoxCtxCase p S q) (htc : TruncCase p S q)
    (hic : ImpCase p S q) (hzc : ZeroFuelCase p S q) :
    ∀ (d : Nat) (f c : Nat) (Γ Γ' Δ : List PLLFormula),
      defect S Γ' ≤ d → (∀ Y ∈ Γ', Y ∈ S) →
      G4c Δ (itpE p S (f + 1) (c + 2) Γ') →
      G4c Δ (itpA p S (f + 1) (c + 1) Γ' ((prop q).somehow)) →
      G4c Δ (tgtClause p S f c Γ q) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ihd =>
  intro f c Γ Γ' Δ hd hΓ'S hamb hsnd
  rw [itpA_succ] at hsnd
  refine G4c.cut hsnd (G4c.orAll_elim ?_)
  intro φ hφ
  have hA : G4c (φ :: Δ) (itpE p S (f + 1) (c + 2) Γ') := hamb.weaken φ
  have hφd : G4c (φ :: Δ) φ := G4c.identity_mem (.head _)
  simp only [itpAfull] at hφ
  rcases List.mem_append.mp hφ with hoth | htr
  · simp only [itpAoth] at hoth
    rcases List.mem_append.mp hoth with hgoal | henv
    · -- THE GOAL CLAUSE — the substantive case
      simp only [itpAgoal] at hgoal
      rcases List.mem_singleton.mp hgoal with rfl
      exact boxGoal_remap p S hOr hq hΓ'S
        (ambE p S (Nat.le_succ _) (Nat.le_refl _) rfl hA) hφd
    · cases f with
      | zero => exact hzc c Γ Γ' _ φ henv hφd
      | succ f' =>
          have step : ∀ (Γ'' : List PLLFormula) (w : PLLFormula),
              (∀ y ∈ Γ', y ∈ Γ'') → (∀ y ∈ Γ'', y ∈ S) →
              w ∈ S → w ∈ Γ'' → w ∉ Γ' →
              G4c (φ :: Δ) (itpE p S (f' + 1) (c + 2) Γ'') →
              G4c (φ :: Δ) (itpA p S (f' + 1) (c + 1) Γ'' ((prop q).somehow)) →
              G4c (φ :: Δ) (tgtClause p S f' c Γ q) := by
            intro Γ'' w hsub hΓ''S hwS hwΓ'' hwΓ' hg'' hs''
            exact ihd (defect S Γ'')
              (by
                have := defect_lt_of_witness hsub hwS hwΓ'' hwΓ'
                omega)
              f' c Γ Γ'' (φ :: Δ) (Nat.le_refl _) hΓ''S hg'' hs''
          simp only [itpAenv] at henv
          obtain ⟨F, hFΓ', hin⟩ := List.mem_flatMap.mp henv
          have hFS : F ∈ S := hΓ'S F hFΓ'
          cases F with
          | prop q' =>
              simp only at hin
              split at hin
              next hc =>
                exfalso
                have h2 : (prop q : PLLFormula).somehow = prop p := hc.2
                exact absurd h2 (by simp)
              next => cases hin
          | falsePLL => cases hin
          | or A B => exact absurd hFS (hOr A B)
          | ifThen A D =>
              exact hic (f' + 1) c Γ Γ' _ A D φ hFΓ' hΓ'S henv hA hφd
          | somehow χ =>
              simp only at hin
              split at hin
              next => cases hin
              next hcond =>
                rcases List.mem_singleton.mp hin with rfl
                exact hbc (f' + 1) c Γ Γ' _ χ hFΓ' (hsome hFS)
                  (fun h => hcond (Or.inl h)) hΓ'S
                  (grown_box p S hFΓ' hcond hA) hφd
          | and A B =>
              simp only at hin
              split at hin
              next => cases hin
              next h1 =>
                split at hin
                next h2 =>
                  rcases List.mem_singleton.mp hin with rfl
                  by_cases hAin : A ∈ Γ'
                  · have hB : B ∉ Γ' := fun hB => h1 ⟨hAin, hB⟩
                    have hBS : B ∈ S := h2.2.resolve_left hB
                    exact step (A :: B :: Γ') B
                      (fun y hy => .tail _ (.tail _ hy))
                      (by
                        intro y hy
                        rcases List.mem_cons.mp hy with rfl | hy
                        · exact hΓ'S _ hAin
                        rcases List.mem_cons.mp hy with rfl | hy
                        · exact hBS
                        · exact hΓ'S y hy)
                      hBS (.tail _ (.head _)) hB
                      (grown_and p S hFΓ' h1 h2 hA) hφd |> tgtClause_fuel_lift p S
                  · have hAS : A ∈ S := h2.1.resolve_left hAin
                    exact step (A :: B :: Γ') A
                      (fun y hy => .tail _ (.tail _ hy))
                      (by
                        intro y hy
                        rcases List.mem_cons.mp hy with rfl | hy
                        · exact hAS
                        rcases List.mem_cons.mp hy with rfl | hy
                        · exact (h2.2.elim (fun h => hΓ'S _ h) id)
                        · exact hΓ'S y hy)
                      hAS (.head _) hAin
                      (grown_and p S hFΓ' h1 h2 hA) hφd |> tgtClause_fuel_lift p S
                next => cases hin
  · by_cases he : (itpAoth p S f (c + 1) Γ' ((prop q).somehow)).isEmpty = true
    · rw [if_pos he] at htr; cases htr
    · rw [if_neg he] at htr
      rcases List.mem_singleton.mp htr with rfl
      exact htc f c Γ Γ' _ hΓ'S hA hφd

/-! ## Discharging the fuel-`0` floor

At fuel `0` every recursive component is `itpE p S 0 … = ⊤` or `itpA p S 0 … = ⊥`, so
each environment disjunct is `⊥`, a conjunction with a `⊥` component, a conjunction
whose first component is `⊤ ⇢ ⊥`, or the boxed `◯(⊤ ⇢ ⊥)` — and the last yields any
`◯`-conclusion by `box_absurd`.

Written shape by shape.  One counting point, which cost two failed attempts (PROGRESS
§105 addendum): the budget here is `c + 1`, a **literal successor**, so `split` does not
branch on the `match b with | 0 | b'+1` of a gated clause — it reduces.  A gated shape
therefore has one fewer `split` than the same shape has when the budget is a variable
(as in `AtomForce.atom_forces_aux`, where `b` is universally quantified). -/

private theorem byBot {Δ : List PLLFormula} {W : PLLFormula}
    (hd : G4c Δ falsePLL) : G4c Δ W :=
  G4c.cut hd (G4c.botL (.head _))

private theorem byBotR {Δ : List PLLFormula} {X W : PLLFormula}
    (hd : G4c Δ (X.and falsePLL)) : G4c Δ W :=
  byBot (projAnd₂ hd)

private theorem byImpBot {Δ : List PLLFormula} {Y W : PLLFormula}
    (hd : G4c Δ ((truePLL.ifThen falsePLL).and Y)) : G4c Δ W :=
  byBot (fire (projAnd₁ hd) (G4c.truePLL_intro _))

theorem zeroFuelCase (p : String) (S : Finset PLLFormula) {q : String}
    (hq : q ≠ p) : ZeroFuelCase p S q := by
  intro c Γ Γ' Δ φ hφ hd
  simp only [itpAenv] at hφ
  obtain ⟨F, hFΓ', hin⟩ := List.mem_flatMap.mp hφ
  cases F with
  | prop q' =>
      simp only at hin
      split at hin
      next hc =>
          exfalso
          have h2 : (prop q : PLLFormula).somehow = prop p := hc.2
          exact absurd h2 (by simp)
      next => cases hin
  | falsePLL => cases hin
  | and A B =>
      simp only at hin
      split at hin
      next => cases hin
      next =>
          split at hin
          next =>
              rcases List.mem_singleton.mp hin with rfl
              simp only [itpA] at hd
              exact byBot hd
          next => cases hin
  | or A B =>
      simp only at hin
      split at hin
      next => cases hin
      next =>
          split at hin
          next =>
              rcases List.mem_singleton.mp hin with rfl
              simp only [itpA, itpE] at hd
              exact byImpBot hd
          next => cases hin
  | somehow χ =>
      simp only at hin
      split at hin
      next => cases hin
      next =>
          rcases List.mem_singleton.mp hin with rfl
          simp only [itpA, itpE] at hd
          exact box_absurd _ hd (G4c.truePLL_intro _)
  | ifThen A D =>
      cases A with
      | falsePLL => cases hin
      | prop q' =>
          simp only at hin
          split at hin
          next => cases hin
          next =>
              split at hin
              next =>
                  split at hin
                  next =>
                      rcases List.mem_singleton.mp hin with rfl
                      simp only [itpA] at hd
                      exact byBot hd
                  next =>
                      split at hin
                      next => cases hin
                      next =>
                          rcases List.mem_singleton.mp hin with rfl
                          simp only [itpA] at hd
                          exact byBotR hd
              next => cases hin
      | and A₁ B₁ =>
          simp only at hin
          split at hin
          next => cases hin
          next =>
              split at hin
              next =>
                  rcases List.mem_singleton.mp hin with rfl
                  simp only [itpA] at hd
                  exact byBot hd
              next => cases hin
      | or A₁ B₁ =>
          simp only at hin
          split at hin
          next => cases hin
          next =>
              split at hin
              next =>
                  rcases List.mem_singleton.mp hin with rfl
                  simp only [itpA] at hd
                  exact byBot hd
              next => cases hin
      | ifThen A₁ B₁ =>
          simp only at hin
          split at hin
          next => cases hin
          next =>
              split at hin
              next =>
                  split at hin
                  next =>
                      split at hin
                      next =>
                          rcases List.mem_singleton.mp hin with rfl
                          simp only [itpA] at hd
                          exact byBotR hd
                      next => cases hin
                  next =>
                      split at hin
                      next =>
                          rcases List.mem_singleton.mp hin with rfl
                          simp only [itpA] at hd
                          exact byBotR hd
                      next => cases hin
              next => cases hin
      | somehow A₁ =>
          simp only at hin
          split at hin
          next => cases hin
          next =>
              split at hin
              next =>
                rcases List.mem_append.mp hin with hL | hR
                · split at hL
                  next =>
                      rcases List.mem_cons.mp hL with rfl | hL'
                      · simp only [itpA] at hd
                        exact byBotR hd
                      · rcases List.mem_singleton.mp hL' with rfl
                        simp only [itpA] at hd
                        exact byBotR hd
                  next => cases hL
                · obtain ⟨X, hX, hXin⟩ := List.mem_filterMap.mp hR
                  cases X with
                  | somehow x =>
                      simp only at hXin
                      split at hXin
                      next => cases hXin
                      next =>
                          injection hXin with hXe
                          subst hXe
                          simp only [itpA] at hd
                          exact byBotR hd
                  | prop _ => cases hXin
                  | falsePLL => cases hXin
                  | and _ _ => cases hXin
                  | or _ _ => cases hXin
                  | ifThen _ _ => cases hXin
              next => cases hin

end BoxSnd
end PLLND

/-! ### Axiom audit -/

/-- info: 'PLLND.BoxSnd.grown_and' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.BoxSnd.grown_and

/-- info: 'PLLND.BoxSnd.grown_box' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.BoxSnd.grown_box

/--
info: 'PLLND.BoxSnd.boxSnd_reaches' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.BoxSnd.boxSnd_reaches

/--
info: 'PLLND.BoxSnd.zeroFuelCase' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.BoxSnd.zeroFuelCase
