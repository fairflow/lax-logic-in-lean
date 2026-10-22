import wip.gapWidth
import Meta.Audit

/-!
# Independence of the odd gaps (PROVED)

With `g k = gap k = ◯t(2k+1) ↠ t(2k+1)` (`wip/gapWidth.lean`, `t n = rnSub n`):

    Indep:  for all finite disjoint S, T ⊆ ℕ,   ⋀_{i∈S} g(2i+1)  ⊬  ⋁_{j∈T} g(2j+1)

(`indep`, with `⋀[] = ⊤` and `⋁[] = ⊥`).  The odd gaps therefore generate a free
distributive lattice on ω generators inside F0; the order embedding of the
dyadic rationals built on this is `wip/f0Dyadic.lean`.

History: the forcing lemma was stated as a blueprint (`sorry`) in
`wip/f0IndepBlueprint.lean` on 2026-10-22 and is proved here the same day; the
blueprint module now only imports this one.

## The model

`cmE m` (`wip/chainOff.lean`) is the abyss-lifted Rieger–Nishimura ladder with
one internal `Rₘ`-edge `(m+3) ⇝ 0`.  The multi-edge lift `cmM ms` has one such
edge for every level `m ∈ ms`: the edge worlds are `E = {m+3 : m ∈ ms}`, each
with `e ⇝ 0` and `e ⇝ ⊤` (the fallible top).  For a finite `T` the levels are
`2j` (`levels T`), so `E = {2j+3 : j ∈ T}`, and the root is the highest edge
world `root T = 2·max T + 3`.

## The forcing lemma (`multi_edge_forcing`)

    ∀ T,  (∀ i ∉ T, ∀ x,  cmM (levels T), x ⊩ g(2i+1))
        ∧ (∀ j ∈ T,       cmM (levels T), root T ⊮ g(2j+1)).

The proof, in four steps, all on `cmM` directly:

1. `cmM_force_oBot`: the edges sit at worlds `≥ 3`, so `◯⊥` holds on the
   skeleton exactly at `0`; hence (`cmM_transfer`, the induction of
   `Skel.transfer`) the substituted rungs keep their ladder truth sets, and
   `T(t(2k+1)) = [0, k]` (`cmM_rung`).
2. `cmM_chainF`: `◯t(2k+1)` holds at `x` iff every `y` in the cone of `x` is
   `0`, an edge world, or `≤ k`.
3. `forced_off`: a counterexample to `g(2i+1)` would be a world `y > 2i+1`
   forcing `◯t(4i+3)`; so `y` is an edge world `2j+3`, and either `j = i`
   (excluded by `i ∉ T`) or `y ≥ 2i+5`, when the even world `2i+2` in its
   cone is neither `0`, nor an edge, nor `≤ 2i+1`.
4. `fails_on`: for `j ∈ T`, the edge world `2j+3` lies in the cone of the
   root, forces `◯t(4j+3)` and refutes `t(4j+3)`.

## Axioms

Every pin is `[propext, Quot.sound]`; `cmM` is used directly and `cmE` not at
all.  The ladder truth sets are re-proved choice-free (`sat_rnP_cf`), a copy
of `sat_rnP` (`wip/rnEmbed.lean`, untouched) with two changes: the `omega`
call that closes an `↔` goal (`_proof_1_5`, which reaches `Classical.choice`
through `Classical.propDecidable`, measured with `#choice_path` on the copy)
is split into two `omega` calls on implications, and the two `by_contra`
steps become `by_cases` on decidable arithmetic.
-/

open PLLFormula

namespace PLLND
namespace F0

open SemUI RNEmbed

/-! ## The conjecture -/

/-- **Indep**: for all finite disjoint `S`, `T`,
`⋀_{i∈S} g(2i+1) ⊬ ⋁_{j∈T} g(2j+1)`. -/
def Indep : Prop :=
  ∀ S T : List Nat, (∀ i ∈ S, i ∉ T) →
    [bigAnd (S.map fun i => gap (2 * i + 1))] ⊬
      PLLND.bigOr (T.map fun j => gap (2 * j + 1))

/-! ## The multi-edge lift -/

/-- `v` is an edge world: `v = m + 3` for a level `m ∈ ms`. -/
def IsEdge (ms : List Nat) (v : Nat) : Prop := ∃ m ∈ ms, v = m + 3

theorem not_isEdge_zero {ms : List Nat} : ¬ IsEdge ms 0 :=
  fun ⟨m, _, h⟩ => Nat.succ_ne_zero (m + 2) h.symm

/-- `Rₘ` with one internal edge `e ⇝ 0` per edge world `e` (and `e ⇝ ⊤`,
for transitivity through `0 ⇝ ⊤`). -/
def RmM (ms : List Nat) : Option Nat → Option Nat → Prop
  | some v, some w => v = w ∨ (IsEdge ms v ∧ w = 0)
  | some v, none   => v = 0 ∨ IsEdge ms v
  | none,   none   => True
  | none,   some _ => False

/-- **The multi-edge lift** of the ladder: the edges of `cmE m` for every
level `m ∈ ms` at once. -/
@[reducible] def cmM (ms : List Nat) : ConstraintModel where
  W := Option Nat
  Ri := riL ladder
  Rm := RmM ms
  F := {x | x = none}
  V _ := {x | x = none}
  refl_i x := by
    cases x with
    | none => exact trivial
    | some a => exact ladder.refl a
  trans_i {x y z} h1 h2 := by
    cases x with
    | none =>
        cases y with
        | some b => exact (h1 : False).elim
        | none =>
            cases z with
            | some c => exact (h2 : False).elim
            | none => exact trivial
    | some a =>
        cases y with
        | none =>
            cases z with
            | some c => exact (h2 : False).elim
            | none => exact trivial
        | some b =>
            cases z with
            | none => exact trivial
            | some c => exact ladder.trans h1 h2
  refl_m x := by
    cases x with
    | none => exact trivial
    | some a => exact Or.inl rfl
  trans_m {x y z} h1 h2 := by
    cases x with
    | none =>
        cases y with
        | some b => exact (h1 : False).elim
        | none =>
            cases z with
            | some c => exact (h2 : False).elim
            | none => exact trivial
    | some a =>
        cases y with
        | none =>
            cases z with
            | some c => exact (h2 : False).elim
            | none => exact h1
        | some b =>
            cases z with
            | none =>
                rcases (h1 : a = b ∨ (IsEdge ms a ∧ b = 0)) with rfl | ⟨ha, _⟩
                · exact h2
                · exact Or.inr ha
            | some c =>
                rcases (h1 : a = b ∨ (IsEdge ms a ∧ b = 0)) with rfl | ⟨ha, rfl⟩
                · exact h2
                · rcases (h2 : (0 : Nat) = c ∨ (IsEdge ms 0 ∧ c = 0)) with rfl | ⟨h0, _⟩
                  · exact Or.inr ⟨ha, rfl⟩
                  · exact (not_isEdge_zero h0).elim
  sub_mi {x y} h := by
    cases x with
    | none =>
        cases y with
        | some b => exact (h : False).elim
        | none => exact trivial
    | some a =>
        cases y with
        | none => exact trivial
        | some b =>
            rcases (h : a = b ∨ (IsEdge ms a ∧ b = 0)) with rfl | ⟨⟨m, _, rfl⟩, rfl⟩
            · exact ladder.refl a
            · exact Or.inr (Nat.le_add_left 2 (m + 1))
  hered_F {x y} h hx := by
    obtain rfl := (hx : x = none)
    cases y with
    | some b => exact (h : False).elim
    | none => exact rfl
  hered_V {a x y} h hx := by
    obtain rfl := (hx : x = none)
    cases y with
    | some b => exact (h : False).elim
    | none => exact rfl
  full_F {a x} hx := hx

/-- The levels for an index set `T`: one edge, at world `2j+3`, per `j ∈ T`. -/
def levels (T : List Nat) : List Nat := T.map (2 * ·)

/-- The root: the highest edge world, `2·max T + 3`. -/
def root (T : List Nat) : Nat := 2 * T.foldr max 0 + 3

/-- **The general forcing lemma**, as a statement: on `cmM (levels T)`, every
odd gap with index outside `T` is forced at every skeleton world, and every
odd gap with index in `T` fails at the root. -/
def MultiEdgeForcing : Prop :=
  ∀ T : List Nat,
    (∀ i : Nat, i ∉ T → ∀ x : Nat, (cmM (levels T)).force (some x) (gap (2 * i + 1))) ∧
    (∀ j ∈ T, ¬ (cmM (levels T)).force (some (root T)) (gap (2 * j + 1)))

/-! ## The ladder truth sets, choice-free

A copy of `sat_rnP` (`wip/rnEmbed.lean`) with its two `by_contra` steps, which
reach `Classical.choice`, replaced by `by_cases` on decidable arithmetic. -/

theorem sat_rnP_cf (k : Nat) :
    (∀ w : Nat, ladder.sat (rnP k).1 w ↔ w ≤ k) ∧
    (∀ w : Nat, ladder.sat (rnP k).2 w ↔ (w + 1 ≤ k ∨ w = k + 1)) := by
  induction k with
  | zero =>
      constructor
      · intro w
        show (pv = pv ∧ w ∈ ladder.U) ↔ w ≤ 0
        rw [ladder_U]
        constructor
        · rintro ⟨-, h⟩; omega
        · intro h; exact ⟨rfl, by omega⟩
      · intro w
        show (∀ v : Nat, ladder.le w v → (pv = pv ∧ v ∈ ladder.U) → False) ↔ _
        constructor
        · intro h
          by_cases hw : w = 0 + 1
          · exact Or.inr hw
          · exfalso
            have h0 : ladder.le w 0 := by rw [ladder_le]; omega
            exact h 0 h0 ⟨rfl, by rw [ladder_U]⟩
        · intro hw v hv hvp
          have hv0 : v = 0 := ladder_U.mp hvp.2
          rw [ladder_le] at hv
          omega
  | succ k ih =>
      obtain ⟨ih1, ih2⟩ := ih
      have hC : ∀ w : Nat,
          ladder.sat ((rnP k).1.or (rnP k).2) w ↔ w ≤ k + 1 := by
        intro w
        show (ladder.sat (rnP k).1 w ∨ ladder.sat (rnP k).2 w) ↔ _
        rw [ih1 w, ih2 w]
        -- two `omega` calls on implications: `omega` on the `↔` goal itself
        -- reaches `Classical.propDecidable`
        constructor
        · intro h; omega
        · intro h; omega
      constructor
      · intro w
        show ladder.sat ((rnP k).1.or (rnP k).2) w ↔ _
        exact hC w
      · intro w
        show (∀ v : Nat, ladder.le w v →
            ladder.sat ((rnP k).1.or (rnP k).2) v →
            ladder.sat (rnP k).1 v) ↔ _
        constructor
        · intro h
          by_cases hw : (w + 1 ≤ k + 1 ∨ w = k + 1 + 1)
          · exact hw
          · exfalso
            have hle : ladder.le w (k + 1) := by rw [ladder_le]; omega
            have hsatC : ladder.sat ((rnP k).1.or (rnP k).2) (k + 1) :=
              (hC (k + 1)).mpr (by omega)
            have := (ih1 (k + 1)).mp (h (k + 1) hle hsatC)
            omega
        · intro hw v hv hvC
          rw [ladder_le] at hv
          have h1 : v ≤ k + 1 := (hC v).mp hvC
          exact (ih1 v).mpr (by omega)

/-- `T(t(2k+1)) = [0, k]` on the ladder, choice-free. -/
theorem sat_rn_odd_cf (k w : Nat) : ladder.sat (rn (2 * k + 1)) w ↔ w ≤ k := by
  rw [rn_odd_eq]; exact (sat_rnP_cf k).1 w

/-! ## Forcing on the multi-edge lift -/

/-- The edges do not enlarge `T(◯⊥)`: on the skeleton it is exactly `{0}`. -/
theorem cmM_force_oBot (ms : List Nat) (x : Nat) :
    (cmM ms).force (some x) oBot ↔ x = 0 := by
  constructor
  · intro h
    rcases Nat.lt_or_ge x 3 with h3 | h3
    · -- x < 3: the witness is x itself
      obtain ⟨u, hm, hu⟩ := h (some x) (Or.inl rfl)
      cases u with
      | some z =>
          rcases (hm : x = z ∨ (IsEdge ms x ∧ z = 0)) with rfl | ⟨⟨m, _, he⟩, _⟩
          · exact absurd (hu : (some x : Option Nat) = none) (Option.some_ne_none x)
          · omega
      | none =>
          rcases (hm : x = 0 ∨ IsEdge ms x) with h0 | ⟨m, _, he⟩
          · exact h0
          · omega
    · -- x ≥ 3: the witness is world 1
      obtain ⟨u, hm, hu⟩ := h (some 1) (Or.inr (by omega))
      cases u with
      | some z =>
          rcases (hm : 1 = z ∨ (IsEdge ms 1 ∧ z = 0)) with rfl | ⟨⟨m, _, he⟩, _⟩
          · exact absurd (hu : (some 1 : Option Nat) = none) (Option.some_ne_none 1)
          · omega
      | none =>
          rcases (hm : (1 : Nat) = 0 ∨ IsEdge ms 1) with h0 | ⟨m, _, he⟩
          · omega
          · omega
  · rintro rfl v hv
    cases v with
    | none => exact ⟨none, trivial, rfl⟩
    | some y =>
        have hy : y = 0 := by
          rcases (hv : y = 0 ∨ y + 2 ≤ 0) with h | h <;> omega
        subst hy
        exact ⟨none, Or.inl rfl, rfl⟩

/-- **The transfer on the multi-edge lift**: for ◯-free `A`, forcing of
`A[p := ◯⊥]` at a skeleton world is IPC forcing on the ladder (the induction
of `Skel.transfer` and `cmE_transfer`; the atom case is `cmM_force_oBot`). -/
theorem cmM_transfer (ms : List Nat) :
    ∀ {A : PLLFormula}, boxFree A = true →
      ∀ w : Nat, ((cmM ms).force (some w) (substP pv oBot A) ↔ ladder.sat A w) := by
  intro A
  induction A with
  | prop a =>
      intro _ w
      by_cases ha : a = pv
      · subst ha
        show (cmM ms).force (some w) oBot ↔ ladder.sat (.prop pv) w
        rw [cmM_force_oBot ms w]
        exact ⟨fun h => ⟨rfl, h⟩, fun h => h.2⟩
      · have he : substP pv oBot (.prop a) = .prop a := by
          show (if a = pv then oBot else .prop a) = .prop a
          exact if_neg ha
        rw [he]
        constructor
        · intro h
          exact absurd (h : (some w : Option Nat) = none) (Option.some_ne_none w)
        · intro h
          exact absurd h.1 ha
  | falsePLL =>
      intro _ w
      show ((some w : Option Nat) = none) ↔ False
      exact iff_false_intro (Option.some_ne_none w)
  | and A B ihA ihB =>
      intro h w
      simp only [boxFree, Bool.and_eq_true] at h
      show ((cmM ms).force (some w) (substP pv oBot A) ∧
            (cmM ms).force (some w) (substP pv oBot B)) ↔
          (ladder.sat A w ∧ ladder.sat B w)
      exact and_congr (ihA h.1 w) (ihB h.2 w)
  | or A B ihA ihB =>
      intro h w
      simp only [boxFree, Bool.and_eq_true] at h
      show ((cmM ms).force (some w) (substP pv oBot A) ∨
            (cmM ms).force (some w) (substP pv oBot B)) ↔
          (ladder.sat A w ∨ ladder.sat B w)
      exact or_congr (ihA h.1 w) (ihB h.2 w)
  | ifThen A B ihA ihB =>
      intro h w
      simp only [boxFree, Bool.and_eq_true] at h
      show (∀ v, (cmM ms).Ri (some w) v →
            (cmM ms).force v (substP pv oBot A) →
            (cmM ms).force v (substP pv oBot B)) ↔
          (∀ y, ladder.le w y → ladder.sat A y → ladder.sat B y)
      constructor
      · intro hf y hle hsy
        exact (ihB h.2 y).mp (hf (some y) hle ((ihA h.1 y).mpr hsy))
      · intro hs v hv hvA
        cases v with
        | none => exact (cmM ms).force_of_fallible rfl
        | some y => exact (ihB h.2 y).mpr (hs y hv ((ihA h.1 y).mp hvA))
  | somehow A _ =>
      intro h w
      simp only [boxFree] at h
      exact Bool.noConfusion h

/-- The odd rungs keep their ladder truth sets: `T(t(2k+1)) = [0, k]`. -/
theorem cmM_rung (ms : List Nat) (k y : Nat) :
    (cmM ms).force (some y) (rnSub (2 * k + 1)) ↔ y ≤ k :=
  (cmM_transfer ms (rn_boxFree _) y).trans (sat_rn_odd_cf k y)

/-- How `◯` evaluates on the multi-edge lift: a cone point is `0`, an edge
world, or forces the body itself. -/
theorem cmM_box_force (ms : List Nat) (N : PLLFormula) (x : Nat) :
    (cmM ms).force (some x) N.somehow ↔
      ∀ y : Nat, ladder.le x y → (y = 0 ∨ IsEdge ms y ∨ (cmM ms).force (some y) N) := by
  constructor
  · intro h y hy
    obtain ⟨u, hu, hf⟩ := h (some y) hy
    cases u with
    | none =>
        rcases (hu : y = 0 ∨ IsEdge ms y) with h0 | he
        · exact Or.inl h0
        · exact Or.inr (Or.inl he)
    | some z =>
        rcases (hu : y = z ∨ (IsEdge ms y ∧ z = 0)) with rfl | ⟨he, -⟩
        · exact Or.inr (Or.inr hf)
        · exact Or.inr (Or.inl he)
  · intro h v hv
    cases v with
    | none => exact ⟨none, trivial, (cmM ms).force_of_fallible rfl⟩
    | some y =>
        rcases h y hv with rfl | he | hf
        · exact ⟨none, Or.inl rfl, (cmM ms).force_of_fallible rfl⟩
        · exact ⟨none, Or.inr he, (cmM ms).force_of_fallible rfl⟩
        · exact ⟨some y, Or.inl rfl, hf⟩

/-- **The truth set of the chain on the multi-edge lift**: `◯t(2k+1)` holds at
`x` iff every cone point is `0`, an edge world, or `≤ k`. -/
theorem cmM_chainF (ms : List Nat) (k x : Nat) :
    (cmM ms).force (some x) (chainF k) ↔
      ∀ y : Nat, ladder.le x y → (y = 0 ∨ IsEdge ms y ∨ y ≤ k) := by
  show (cmM ms).force (some x) ((rnSub (2 * k + 1)).somehow) ↔ _
  rw [cmM_box_force]
  constructor
  · intro h y hy
    rcases h y hy with h0 | he | hf
    · exact Or.inl h0
    · exact Or.inr (Or.inl he)
    · exact Or.inr (Or.inr ((cmM_rung ms k y).mp hf))
  · intro h y hy
    rcases h y hy with h0 | he | hle
    · exact Or.inl h0
    · exact Or.inr (Or.inl he)
    · exact Or.inr (Or.inr ((cmM_rung ms k y).mpr hle))

/-- The edge worlds of `levels T` are the `2j+3`, `j ∈ T`. -/
theorem isEdge_levels {T : List Nat} {v : Nat} :
    IsEdge (levels T) v ↔ ∃ j ∈ T, v = 2 * j + 3 := by
  constructor
  · rintro ⟨m, hm, rfl⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hm
    exact ⟨j, hj, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨2 * j, List.mem_map.mpr ⟨j, hj, rfl⟩, rfl⟩

theorem le_foldr_max {j : Nat} : ∀ {T : List Nat}, j ∈ T → j ≤ T.foldr max 0 := by
  intro T
  induction T with
  | nil => intro h; simp at h
  | cons a T ih =>
      intro h
      show j ≤ max a (T.foldr max 0)
      rcases List.mem_cons.mp h with rfl | h
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

/-! ## The forcing lemma -/

/-- **Off `T`, an odd gap is forced everywhere.** -/
theorem forced_off (T : List Nat) {i : Nat} (hi : i ∉ T) (x : Nat) :
    (cmM (levels T)).force (some x) (gap (2 * i + 1)) := by
  show ∀ v, (cmM (levels T)).Ri (some x) v →
    (cmM (levels T)).force v (chainF (2 * i + 1)) →
    (cmM (levels T)).force v (rnSub (2 * (2 * i + 1) + 1))
  intro v _ hc
  cases v with
  | none => exact (cmM (levels T)).force_of_fallible rfl
  | some y =>
      have hc' := (cmM_chainF (levels T) (2 * i + 1) y).mp hc
      refine (cmM_rung (levels T) (2 * i + 1) y).mpr ?_
      by_cases hy : y ≤ 2 * i + 1
      · exact hy
      · exfalso
        rcases hc' y (Or.inl rfl) with h0 | he | hle
        · omega
        · obtain ⟨j, hj, hyj⟩ := isEdge_levels.mp he
          by_cases hji : j = i
          · subst hji
            exact hi hj
          · -- y = 2j+3 > 2i+1 with j ≠ i, so y ≥ 2i+5: the even world 2i+2
            -- lies in its cone, and is neither 0, an edge, nor ≤ 2i+1
            have hle : ladder.le y (2 * i + 2) := Or.inr (by omega)
            rcases hc' (2 * i + 2) hle with h0 | he' | hle'
            · omega
            · obtain ⟨j', _, hj'⟩ := isEdge_levels.mp he'
              omega
            · omega
        · exact hy hle

/-- **In `T`, an odd gap fails at the root.** -/
theorem fails_on (T : List Nat) {j : Nat} (hj : j ∈ T) :
    ¬ (cmM (levels T)).force (some (root T)) (gap (2 * j + 1)) := by
  intro h
  have hM := le_foldr_max hj
  have hle : ladder.le (root T) (2 * j + 3) := by
    show 2 * j + 3 = 2 * T.foldr max 0 + 3 ∨ 2 * j + 3 + 2 ≤ 2 * T.foldr max 0 + 3
    omega
  have hc : (cmM (levels T)).force (some (2 * j + 3)) (chainF (2 * j + 1)) := by
    refine (cmM_chainF (levels T) (2 * j + 1) (2 * j + 3)).mpr ?_
    intro y hy
    rcases (hy : y = 2 * j + 3 ∨ y + 2 ≤ 2 * j + 3) with rfl | h2
    · exact Or.inr (Or.inl (isEdge_levels.mpr ⟨j, hj, rfl⟩))
    · exact Or.inr (Or.inr (by omega))
  have hr := (cmM_rung (levels T) (2 * j + 1) (2 * j + 3)).mp
    (h (some (2 * j + 3)) hle hc)
  omega

/-- **The forcing lemma.** -/
theorem multi_edge_forcing : MultiEdgeForcing :=
  fun T => ⟨fun _ hi x => forced_off T hi x, fun _ hj => fails_on T hj⟩

/-! ## Independence -/

/-- A finite disjunction is forced at a skeleton world only through one of its
disjuncts (`⋁[] = ⊥` is forced only at the fallible top). -/
theorem cmM_force_bigOr (ms : List Nat) (x : Nat) :
    ∀ L : List PLLFormula, (cmM ms).force (some x) (PLLND.bigOr L) →
      ∃ φ ∈ L, (cmM ms).force (some x) φ
  | [], h => absurd (h : (some x : Option Nat) = none) (Option.some_ne_none x)
  | φ :: L, h => by
      rcases (h : (cmM ms).force (some x) φ ∨ (cmM ms).force (some x) (PLLND.bigOr L))
        with h | h
      · exact ⟨φ, List.mem_cons_self .., h⟩
      · obtain ⟨ψ, hψ, h'⟩ := cmM_force_bigOr ms x L h
        exact ⟨ψ, List.mem_cons_of_mem _ hψ, h'⟩

/-- **The forcing lemma implies independence**: soundness at the root. -/
theorem indep_of_forcing (H : MultiEdgeForcing) : Indep := by
  intro S T hST hd
  have hctx : Deriv (S.map fun i => gap (2 * i + 1))
      (PLLND.bigOr (T.map fun j => gap (2 * j + 1))) :=
    Deriv.cutHead (Deriv.bigAndIntro fun _ hD => Deriv.iden hD) hd
  obtain ⟨d⟩ := hctx
  obtain ⟨hS, hT⟩ := H T
  have hs := soundness d (cmM (levels T)) (some (root T)) (fun ψ hψ => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hψ
    exact hS i (hST i hi) (root T))
  obtain ⟨φ, hφ, hf⟩ := cmM_force_bigOr _ _ _ hs
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hφ
  exact hT j hj hf

/-- **Indep**: for all finite disjoint `S`, `T`,

    ⋀_{i∈S} g(2i+1)  ⊬  ⋁_{j∈T} g(2j+1). -/
theorem indep : Indep := indep_of_forcing multi_edge_forcing

/-- **`|T| = 1`, re-derived from Indep** (choice-free; compare
`odd_gaps_single`, `wip/f0OddGaps.lean`, which carries `Classical.choice`):
for `j ∉ S`,  `⋀_{i∈S} g(2i+1) ⊬ g(2j+1)`. -/
theorem odd_gaps_single_cf (S : List Nat) {j : Nat} (hj : j ∉ S) :
    [bigAnd (S.map fun i => gap (2 * i + 1))] ⊬ gap (2 * j + 1) := fun h =>
  indep S [j] (fun _ hi hij => hj (List.mem_singleton.mp hij ▸ hi))
    (Deriv.cutHead h (Deriv.orIntro1 (Deriv.iden (.head _))))

end F0
end PLLND

#axioms_within PLLND.F0.cmM [propext, Quot.sound]
#axioms_within PLLND.F0.sat_rnP_cf [propext, Quot.sound]
#axioms_within PLLND.F0.sat_rn_odd_cf [propext, Quot.sound]
#axioms_within PLLND.F0.cmM_force_oBot [propext, Quot.sound]
#axioms_within PLLND.F0.cmM_transfer [propext, Quot.sound]
#axioms_within PLLND.F0.cmM_rung [propext, Quot.sound]
#axioms_within PLLND.F0.cmM_box_force [propext, Quot.sound]
#axioms_within PLLND.F0.cmM_chainF [propext, Quot.sound]
#axioms_within PLLND.F0.forced_off [propext, Quot.sound]
#axioms_within PLLND.F0.fails_on [propext, Quot.sound]
#axioms_within PLLND.F0.multi_edge_forcing [propext, Quot.sound]
#axioms_within PLLND.F0.cmM_force_bigOr [propext, Quot.sound]
#axioms_within PLLND.F0.indep_of_forcing [propext, Quot.sound]
#axioms_within PLLND.F0.indep [propext, Quot.sound]
#axioms_within PLLND.F0.odd_gaps_single_cf [propext, Quot.sound]
