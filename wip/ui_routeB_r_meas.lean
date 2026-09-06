/-
Route (B), node **N4**, WP12b, **stage 1, part A**: the measure that founds
the pair-recording recursion `interpR` (`wip/ui_routeB_r_def.lean`).

`docs/n4-bound.md` founds `interpQ` on

    μ s  =  κ s · W s + ν s,
    κ s  =  the number of DISTINCT antecedents of the closure not in `seen`,
    W s  =  3 ^ (mxW (clSt s) + 1),
    ν s  =  2·sum3 todo + sum3 done + goalW goal.

`interpR` records the PAIR `(Qa, done)` and cuts only at a station with the
same MEMBERS, so the first component must count PAIRS:

    κ₂ s = the number of pairs `(Q, T)` with `Q` an antecedent of the closure
           and `T` a subset of the closure, not yet recorded in `seen` up to
           set-equality of the station,

counted as the length of an explicit, deduplicated candidate list.  The
candidate stations are the sublists of the deduplicated closure (`powerL`),
and a station is mapped into that enumeration by `canonSt`, which keeps the
members of the carrier that lie in the station.  Both flattening lemmas of
`wip/ui_routeB_n4q_clos.lean` Part 5 then go through:

* an ORDINARY edge has `clSt` non-increasing and `seen` carried, so `κ₂` is
  non-increasing (`kap2_le`) and `ν` drops;
* a GUARD edge records `(Qa, done)` — a candidate at `s`, since
  `Qa ⊃ N ∈ done ⊆ clSt s` and `done ⊆ clSt s`, and unrecorded at `s`, since
  the check fired — so `κ₂` drops by at least one (`kap2_lt`) and `ν` stays
  below `ν s + W s`.

`κ₂` counts over the CURRENT closure, exactly as `κ` does; a closure that
shrinks along an edge only removes candidates, and records left behind by a
shrinking closure are simply not counted.  That is the reason the first
component is a filtered count and not a difference of two bounds — a
difference whose subtrahend also shrinks is not monotone, and the measure
would not be non-increasing along an ordinary edge.

`κ₂` is not kernel-computable at a designed cell: the candidate enumeration
is exponential in the closure.  Its two lemmas are cell-INDEPENDENT
combinatorics, discharged by proof.  What IS cell-dependent — that the
closure does not grow along an edge, and that `ν` drops (ordinary) or stays
under `ν + W` (guard) — is decided in the kernel on the designed cells in
`wip/ui_routeB_r_gate.lean`, together with the gate watched failing.

`LJF/` is untouched; this module is a leaf.
-/
import wip.ui_routeB_n4q_bound
import wip.ui_routeB_r_def
import Meta.Audit

set_option autoImplicit false

namespace LJFO

/-! # Part 1 · The state space, and literal stabilisation from a measure

`wip/ui_routeB_n4q_thm.lean` Part 1, transcribed to `stepR`. -/

/-- A state of the pair-recording recursion: `(todo, done, goal, seen)`. -/
abbrev RState : Type := List Neg × List Neg × Option Neg × SeenR

/-- An approximant read at a state. -/
def atStR (F : List Neg → List Neg → Option Neg → SeenR → Neg) (s : RState) : Neg :=
  F s.1 s.2.1 s.2.2.1 s.2.2.2

theorem atStR_mk (F : List Neg → List Neg → Option Neg → SeenR → Neg)
    (todo done : List Neg) (g : Option Neg) (seen : SeenR) :
    atStR F (todo, done, g, seen) = F todo done g seen := rfl

/-- **The measure obligation for the pair-recording recursion.**  `μ` FOUNDS
`interpR`: the step at a state consults the level below only at states of
strictly smaller `μ`. -/
def RFounded (rst : SeenR → SeenR) (p : String) (μ : RState → Nat) : Prop :=
  ∀ (prev₁ prev₂ : ApproxR) (s : RState),
    (∀ t : RState, μ t < μ s → atStR prev₁ t = atStR prev₂ t) →
    atStR (stepR rst p prev₁) s = atStR (stepR rst p prev₂) s

/-- **Two levels above the measure agree.** -/
theorem interpGR_founded_eq {rst : SeenR → SeenR} {p : String}
    {μ : RState → Nat} (h : RFounded rst p μ) :
    ∀ (n : Nat) (s : RState), μ s ≤ n → ∀ f g : Nat, n ≤ f → n ≤ g →
      atStR (interpGR rst p (f + 1)) s = atStR (interpGR rst p (g + 1)) s := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hs f g hf hg
    show atStR (stepR rst p (interpGR rst p f)) s
       = atStR (stepR rst p (interpGR rst p g)) s
    refine h _ _ s ?_
    intro t ht
    have hn : 1 ≤ n := by omega
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
    exact ih (n - 1) (by omega) t (by omega) f' g' (by omega) (by omega)

/-- The chain at a state is literally constant from `μ s + 1` on. -/
theorem interpGR_stab_of_founded {rst : SeenR → SeenR} {p : String}
    {μ : RState → Nat} (h : RFounded rst p μ) (s : RState) :
    ∀ f, μ s + 1 ≤ f →
      atStR (interpGR rst p f) s = atStR (interpGR rst p (μ s + 1)) s := by
  intro f hf
  obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
  exact interpGR_founded_eq h (μ s) s (Nat.le_refl _) f' (μ s) (by omega) (Nat.le_refl _)

/-- **A bound for the pair-recording recursion**, as data. -/
def RBound (p : String) : Type :=
  Σ' μ : RState → Nat, RFounded id p μ

/-- Literal stabilisation of the pair-recording `∃p` chain at a station. -/
def RStabLitE (p : String) (done : List Neg) : Type :=
  Σ' f₀ : Nat, ∀ f, f₀ ≤ f →
    interpR p f [] done none [] = interpR p f₀ [] done none []

/-- Literal stabilisation of the pair-recording `∀p` chain at a station. -/
def RStabLitA (p : String) (done : List Neg) (G : Neg) : Type :=
  Σ' f₀ : Nat, ∀ f, f₀ ≤ f →
    interpR p f [] done (some G) [] = interpR p f₀ [] done (some G) []

/-- A bound gives literal stabilisation of the `∃p` chain at EVERY station. -/
def rStabLitE_of_bound {p : String} (bd : RBound p) (done : List Neg) :
    RStabLitE p done :=
  ⟨bd.1 ([], done, none, []) + 1, fun f hf =>
    interpGR_stab_of_founded bd.2 ([], done, none, []) f hf⟩

/-- The same for the `∀p` chain. -/
def rStabLitA_of_bound {p : String} (bd : RBound p) (done : List Neg) (G : Neg) :
    RStabLitA p done G :=
  ⟨bd.1 ([], done, some G, []) + 1, fun f hf =>
    interpGR_stab_of_founded bd.2 ([], done, some G, []) f hf⟩

/-! # Part 2 · The three components of the measure

`clSt`, `bigW` and `nu` (`wip/ui_routeB_n4q_meas.lean`) ignore the fourth
slot of a state, so they are reused through the projection that erases
`seen`. -/

/-- The `QState` underlying an `RState`: the `seen` slot erased. -/
def qOf (s : RState) : QState := (s.1, s.2.1, s.2.2.1, [])

/-- The closure of an `RState`. -/
def clStR (s : RState) : List Neg := clSt (qOf s)

/-- The bound component `W`. -/
def bigWR (s : RState) : Nat := bigW (qOf s)

/-- The weight component `ν`. -/
def nuR (s : RState) : Nat := nu (qOf s)

theorem clStR_mk (todo done : List Neg) (g : Option Neg) (seen : SeenR) :
    clStR (todo, done, g, seen) = subL todo ++ subL done ++ subG g := rfl

theorem nuR_mk (todo done : List Neg) (g : Option Neg) (seen : SeenR) :
    nuR (todo, done, g, seen) = 2 * sum3 todo + sum3 done + goalW g := rfl

theorem mem_clStR {x : Neg} {todo done : List Neg} {g : Option Neg} {seen : SeenR} :
    x ∈ clStR (todo, done, g, seen) ↔
      (x ∈ subL todo ∨ x ∈ subL done ∨ x ∈ subG g) := by
  simp [clStR, qOf, clSt, List.mem_append]

/-! # Part 3 · Set-equality of stations, decided

`negMem`, `subNeg`, `sameSet` and `seenMemR` are `wip/ui_routeB_r_def.lean`'s;
here they are related to membership. -/

theorem negMem_iff (l : List Neg) (X : Neg) : negMem l X = true ↔ X ∈ l := by
  induction l with
  | nil => simp [negMem]
  | cons Y l ih =>
      simp only [negMem, List.mem_cons]
      by_cases h : Y = X
      · subst h; simp
      · rw [if_neg h, ih]
        constructor
        · exact Or.inr
        · rintro (rfl | hx)
          · exact absurd rfl h
          · exact hx

theorem not_negMem_iff (l : List Neg) (X : Neg) : negMem l X = false ↔ X ∉ l := by
  constructor
  · intro hf hx
    have := (negMem_iff l X).mpr hx
    rw [hf] at this
    exact Bool.noConfusion this
  · intro hx
    cases hb : negMem l X with
    | false => rfl
    | true => exact absurd ((negMem_iff l X).mp hb) hx

theorem subNeg_iff (T S : List Neg) : subNeg T S = true ↔ ∀ X ∈ T, X ∈ S := by
  induction T with
  | nil => simp [subNeg]
  | cons X T ih =>
      simp only [subNeg, Bool.and_eq_true, ih, negMem_iff, List.mem_cons]
      constructor
      · rintro ⟨h1, h2⟩ Y hY
        rcases hY with rfl | hY
        · exact h1
        · exact h2 Y hY
      · intro h
        exact ⟨h X (Or.inl rfl), fun Y hY => h Y (Or.inr hY)⟩

theorem sameSet_iff (T S : List Neg) :
    sameSet T S = true ↔ ((∀ X ∈ T, X ∈ S) ∧ ∀ X ∈ S, X ∈ T) := by
  simp only [sameSet, Bool.and_eq_true, subNeg_iff]

theorem sameSet_refl (T : List Neg) : sameSet T T = true :=
  (sameSet_iff T T).mpr ⟨fun _ h => h, fun _ h => h⟩

theorem sameSet_symm {T S : List Neg} (h : sameSet T S = true) :
    sameSet S T = true := by
  rcases (sameSet_iff T S).mp h with ⟨h1, h2⟩
  exact (sameSet_iff S T).mpr ⟨h2, h1⟩

theorem sameSet_trans {T S U : List Neg} (h₁ : sameSet T S = true)
    (h₂ : sameSet S U = true) : sameSet T U = true := by
  rcases (sameSet_iff T S).mp h₁ with ⟨a1, a2⟩
  rcases (sameSet_iff S U).mp h₂ with ⟨b1, b2⟩
  exact (sameSet_iff T U).mpr ⟨fun X hX => b1 X (a1 X hX), fun X hX => a2 X (b2 X hX)⟩

/-- The genuine-loop test, as an existential. -/
theorem seenMemR_iff : ∀ (seen : SeenR) (Q : Pos) (T : List Neg),
    seenMemR seen Q T = true ↔ ∃ T', (Q, T') ∈ seen ∧ sameSet T' T = true := by
  intro seen
  induction seen with
  | nil => intro Q T; simp [seenMemR]
  | cons x seen ih =>
      obtain ⟨R, S⟩ := x
      intro Q T
      simp only [seenMemR, List.mem_cons, Prod.mk.injEq]
      by_cases hR : R = Q
      · rw [if_pos hR]
        by_cases hs : sameSet S T = true
        · rw [if_pos hs]
          constructor
          · intro _; exact ⟨S, Or.inl ⟨hR.symm, rfl⟩, hs⟩
          · intro _; rfl
        · rw [if_neg hs, ih Q T]
          constructor
          · rintro ⟨T', hT', hs'⟩; exact ⟨T', Or.inr hT', hs'⟩
          · rintro ⟨T', (⟨_, rfl⟩ | hT'), hs'⟩
            · exact absurd hs' hs
            · exact ⟨T', hT', hs'⟩
      · rw [if_neg hR, ih Q T]
        constructor
        · rintro ⟨T', hT', hs'⟩; exact ⟨T', Or.inr hT', hs'⟩
        · rintro ⟨T', (⟨heq, _⟩ | hT'), hs'⟩
          · exact absurd heq.symm hR
          · exact ⟨T', hT', hs'⟩

/-- **The test is invariant under set-equality of the station.** -/
theorem seenMemR_congr {seen : SeenR} {Q : Pos} {T S : List Neg}
    (h : sameSet T S = true) : seenMemR seen Q T = seenMemR seen Q S := by
  have key : ∀ (T S : List Neg), sameSet T S = true →
      seenMemR seen Q T = true → seenMemR seen Q S = true := by
    intro T S h ht
    obtain ⟨T', hT', hs⟩ := (seenMemR_iff seen Q T).mp ht
    exact (seenMemR_iff seen Q S).mpr ⟨T', hT', sameSet_trans hs h⟩
  cases hT : seenMemR seen Q T with
  | true => rw [key T S h hT]
  | false =>
      cases hS : seenMemR seen Q S with
      | true =>
          have := key S T (sameSet_symm h) hS
          rw [hT] at this
          exact Bool.noConfusion this
      | false => rfl

/-- Adding a record can only make the test fire. -/
theorem seenMemR_of_cons {seen : SeenR} {Q R : Pos} {T S : List Neg}
    (h : seenMemR ((R, S) :: seen) Q T = false) : seenMemR seen Q T = false := by
  cases hs : seenMemR seen Q T with
  | false => rfl
  | true =>
      obtain ⟨T', hT', hst⟩ := (seenMemR_iff seen Q T).mp hs
      have hc : seenMemR ((R, S) :: seen) Q T = true :=
        (seenMemR_iff _ Q T).mpr ⟨T', List.mem_cons_of_mem _ hT', hst⟩
      rw [h] at hc
      exact Bool.noConfusion hc

/-! # Part 4 · The candidate enumeration -/

/-- Duplicate removal on negatives, by hand (no `DecidableEq` instance search
through `Classical`, as in `ddup`). -/
def ddupN : List Neg → List Neg
  | [] => []
  | X :: l => let r := ddupN l; if negMem r X then r else X :: r

theorem ddupN_cons (X : Neg) (l : List Neg) :
    ddupN (X :: l) = if negMem (ddupN l) X then ddupN l else X :: ddupN l := rfl

theorem mem_ddupN {X : Neg} : ∀ {l : List Neg}, X ∈ ddupN l ↔ X ∈ l := by
  intro l
  induction l with
  | nil => simp [ddupN]
  | cons Y l ih =>
      rw [ddupN_cons]
      by_cases hm : negMem (ddupN l) Y = true
      · rw [if_pos hm, ih, List.mem_cons]
        constructor
        · exact Or.inr
        · rintro (rfl | h)
          · exact ih.mp ((negMem_iff _ _).mp hm)
          · exact h
      · rw [if_neg hm, List.mem_cons, List.mem_cons, ih]

theorem nodup_ddupN : ∀ (l : List Neg), (ddupN l).Nodup := by
  intro l
  induction l with
  | nil => simp [ddupN]
  | cons Y l ih =>
      rw [ddupN_cons]
      by_cases hm : negMem (ddupN l) Y = true
      · rw [if_pos hm]; exact ih
      · rw [if_neg hm]
        refine List.nodup_cons.mpr ⟨?_, ih⟩
        intro h
        exact hm ((negMem_iff _ _).mpr h)

/-- The sublists of a list of negatives: the candidate stations. -/
def powerL : List Neg → List (List Neg)
  | [] => [[]]
  | X :: L => powerL L ++ (powerL L).map (fun T => X :: T)

theorem powerL_cons (X : Neg) (L : List Neg) :
    powerL (X :: L) = powerL L ++ (powerL L).map (fun T => X :: T) := rfl

theorem mem_powerL_sub : ∀ {L T : List Neg}, T ∈ powerL L → ∀ X ∈ T, X ∈ L := by
  intro L
  induction L with
  | nil =>
      intro T hT X hX
      simp only [powerL, List.mem_singleton] at hT
      subst hT
      exact absurd hX List.not_mem_nil
  | cons Y L ih =>
      intro T hT X hX
      rw [powerL_cons, List.mem_append] at hT
      rcases hT with hT | hT
      · exact List.mem_cons_of_mem _ (ih hT X hX)
      · obtain ⟨T₀, hT₀, rfl⟩ := List.mem_map.mp hT
        rcases List.mem_cons.mp hX with rfl | hX
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (ih hT₀ X hX)

/-- The canonical representative of a station inside a carrier. -/
def canonSt : List Neg → List Neg → List Neg
  | [], _ => []
  | X :: L, T => if negMem T X then X :: canonSt L T else canonSt L T

theorem canonSt_cons (X : Neg) (L T : List Neg) :
    canonSt (X :: L) T = if negMem T X then X :: canonSt L T else canonSt L T := rfl

theorem mem_canonSt {X : Neg} : ∀ {L T : List Neg},
    X ∈ canonSt L T ↔ (X ∈ L ∧ X ∈ T) := by
  intro L
  induction L with
  | nil => intro T; simp [canonSt]
  | cons Y L ih =>
      intro T
      rw [canonSt_cons]
      by_cases hm : negMem T Y = true
      · rw [if_pos hm, List.mem_cons, List.mem_cons, ih]
        constructor
        · rintro (rfl | ⟨h1, h2⟩)
          · exact ⟨Or.inl rfl, (negMem_iff _ _).mp hm⟩
          · exact ⟨Or.inr h1, h2⟩
        · rintro ⟨h1 | h1, h2⟩
          · exact Or.inl h1
          · exact Or.inr ⟨h1, h2⟩
      · rw [if_neg hm, ih, List.mem_cons]
        simp only [Bool.not_eq_true] at hm
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨Or.inr h1, h2⟩
        · rintro ⟨h1 | h1, h2⟩
          · subst h1
            have hc := (negMem_iff T X).mpr h2
            rw [hm] at hc
            exact Bool.noConfusion hc
          · exact ⟨h1, h2⟩

theorem canonSt_mem_powerL : ∀ (L T : List Neg), canonSt L T ∈ powerL L := by
  intro L
  induction L with
  | nil => intro T; simp [canonSt, powerL]
  | cons Y L ih =>
      intro T
      rw [canonSt_cons, powerL_cons]
      by_cases hm : negMem T Y = true
      · rw [if_pos hm]
        exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨canonSt L T, ih T, rfl⟩))
      · rw [if_neg hm]
        exact List.mem_append.mpr (Or.inl (ih T))

/-- The canonical map depends only on the station's members INSIDE the
carrier. -/
theorem canonSt_congr_on : ∀ {L T S : List Neg},
    (∀ X ∈ L, (X ∈ T ↔ X ∈ S)) → canonSt L T = canonSt L S := by
  intro L
  induction L with
  | nil => intro T S _; rfl
  | cons Y L ih =>
      intro T S h
      have hY : (Y ∈ T ↔ Y ∈ S) := h Y (List.mem_cons_self ..)
      have hL : ∀ X ∈ L, (X ∈ T ↔ X ∈ S) := fun X hX => h X (List.mem_cons_of_mem _ hX)
      rw [canonSt_cons, canonSt_cons, ih hL]
      by_cases hm : Y ∈ T
      · rw [if_pos ((negMem_iff T Y).mpr hm), if_pos ((negMem_iff S Y).mpr (hY.mp hm))]
      · have hs : Y ∉ S := fun hc => hm (hY.mpr hc)
        rw [if_neg (by simp [(not_negMem_iff T Y).mpr hm]),
            if_neg (by simp [(not_negMem_iff S Y).mpr hs])]

theorem canonSt_congr {T S : List Neg} (h : sameSet T S = true) (L : List Neg) :
    canonSt L T = canonSt L S := by
  rcases (sameSet_iff T S).mp h with ⟨h1, h2⟩
  exact canonSt_congr_on (fun X _ => ⟨fun hx => h1 X hx, fun hx => h2 X hx⟩)

/-- The canonical representative has the same members as the station, as long
as the station lies inside the carrier. -/
theorem canonSt_sameSet {L T : List Neg} (h : ∀ X ∈ T, X ∈ L) :
    sameSet (canonSt L T) T = true := by
  refine (sameSet_iff _ _).mpr ⟨fun X hX => (mem_canonSt.mp hX).2, fun X hX => ?_⟩
  exact mem_canonSt.mpr ⟨h X hX, hX⟩

/-- **The canonical map is the identity on the enumeration.** -/
theorem canonSt_id : ∀ {L : List Neg}, L.Nodup → ∀ {T : List Neg},
    T ∈ powerL L → canonSt L T = T := by
  intro L
  induction L with
  | nil =>
      intro _ T hT
      simp only [powerL, List.mem_singleton] at hT
      subst hT; rfl
  | cons Y L ih =>
      intro hnd T hT
      obtain ⟨hYL, hndL⟩ := List.nodup_cons.mp hnd
      rw [powerL_cons, List.mem_append] at hT
      rcases hT with hT | hT
      · have hY : Y ∉ T := fun hc => hYL (mem_powerL_sub hT Y hc)
        rw [canonSt_cons, if_neg (by simp [(not_negMem_iff T Y).mpr hY])]
        exact ih hndL hT
      · obtain ⟨T₀, hT₀, rfl⟩ := List.mem_map.mp hT
        rw [canonSt_cons, if_pos ((negMem_iff _ Y).mpr (List.mem_cons_self ..))]
        refine congrArg (fun z => Y :: z) ?_
        have hcg : canonSt L (Y :: T₀) = canonSt L T₀ := by
          refine canonSt_congr_on (fun X hX => ⟨fun hx => ?_, fun hx => ?_⟩)
          · rcases List.mem_cons.mp hx with rfl | hx
            · exact absurd hX hYL
            · exact hx
          · exact List.mem_cons_of_mem _ hx
        rw [hcg]
        exact ih hndL hT₀

/-! # Part 5 · The pair count `κ₂` -/

/-- Membership of a candidate pair, by hand. -/
def memPair : List (Pos × List Neg) → (Pos × List Neg) → Bool
  | [], _ => false
  | x :: l, y => if x = y then true else memPair l y

theorem memPair_iff (l : List (Pos × List Neg)) (y : Pos × List Neg) :
    memPair l y = true ↔ y ∈ l := by
  induction l with
  | nil => simp [memPair]
  | cons x l ih =>
      simp only [memPair, List.mem_cons]
      by_cases h : x = y
      · subst h; simp
      · rw [if_neg h, ih]
        constructor
        · exact Or.inr
        · rintro (rfl | hy)
          · exact absurd rfl h
          · exact hy

/-- Duplicate removal on candidate pairs. -/
def ddupPair : List (Pos × List Neg) → List (Pos × List Neg)
  | [] => []
  | x :: l => let r := ddupPair l; if memPair r x then r else x :: r

theorem ddupPair_cons (x : Pos × List Neg) (l : List (Pos × List Neg)) :
    ddupPair (x :: l) = if memPair (ddupPair l) x then ddupPair l else x :: ddupPair l :=
  rfl

theorem mem_ddupPair {y : Pos × List Neg} :
    ∀ {l : List (Pos × List Neg)}, y ∈ ddupPair l ↔ y ∈ l := by
  intro l
  induction l with
  | nil => simp [ddupPair]
  | cons x l ih =>
      rw [ddupPair_cons]
      by_cases hm : memPair (ddupPair l) x = true
      · rw [if_pos hm, ih, List.mem_cons]
        constructor
        · exact Or.inr
        · rintro (rfl | h)
          · exact ih.mp ((memPair_iff _ _).mp hm)
          · exact h
      · rw [if_neg hm, List.mem_cons, List.mem_cons, ih]

theorem nodup_ddupPair : ∀ (l : List (Pos × List Neg)), (ddupPair l).Nodup := by
  intro l
  induction l with
  | nil => simp [ddupPair]
  | cons x l ih =>
      rw [ddupPair_cons]
      by_cases hm : memPair (ddupPair l) x = true
      · rw [if_pos hm]; exact ih
      · rw [if_neg hm]
        refine List.nodup_cons.mpr ⟨?_, ih⟩
        intro h
        exact hm ((memPair_iff _ _).mpr h)

/-- Removal of one occurrence of a pair, by hand. -/
def rmvPair (y : Pos × List Neg) : List (Pos × List Neg) → List (Pos × List Neg)
  | [] => []
  | x :: l => if x = y then l else x :: rmvPair y l

theorem rmvPair_cons (y x : Pos × List Neg) (l : List (Pos × List Neg)) :
    rmvPair y (x :: l) = if x = y then l else x :: rmvPair y l := rfl

theorem length_rmvPair : ∀ {l : List (Pos × List Neg)} {y : Pos × List Neg}, y ∈ l →
    (rmvPair y l).length + 1 = l.length := by
  intro l
  induction l with
  | nil => intro y h; simp at h
  | cons x l ih =>
      intro y h
      rw [rmvPair_cons]
      by_cases hx : x = y
      · rw [if_pos hx]; simp
      · rw [if_neg hx]
        rcases List.mem_cons.mp h with rfl | h
        · exact absurd rfl hx
        · simp only [List.length_cons]
          have := ih h
          omega

theorem mem_rmvPair : ∀ {l : List (Pos × List Neg)} {y z : Pos × List Neg},
    z ∈ l → z ≠ y → z ∈ rmvPair y l := by
  intro l
  induction l with
  | nil => intro y z h _; simp at h
  | cons x l ih =>
      intro y z h hne
      rw [rmvPair_cons]
      by_cases hx : x = y
      · rw [if_pos hx]
        rcases List.mem_cons.mp h with rfl | h
        · exact absurd hx hne
        · exact h
      · rw [if_neg hx]
        rcases List.mem_cons.mp h with rfl | h
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (ih h hne)

/-- Nodup lists of pairs inject into their supersets. -/
theorem nodupPair_length_le : ∀ {l₁ l₂ : List (Pos × List Neg)},
    l₁.Nodup → l₁ ⊆ l₂ → l₁.length ≤ l₂.length := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ _ _; simp
  | cons y l ih =>
      intro l₂ hnd hsub
      have hy : y ∈ l₂ := hsub (List.mem_cons_self ..)
      have hyl : y ∉ l := (List.nodup_cons.mp hnd).1
      have hsub' : l ⊆ rmvPair y l₂ := by
        intro z hz
        exact mem_rmvPair (hsub (List.mem_cons_of_mem _ hz)) (by rintro rfl; exact hyl hz)
      have h1 := ih (List.nodup_cons.mp hnd).2 hsub'
      have h2 := length_rmvPair hy
      simp only [List.length_cons]
      omega

/-- The candidate pairs of a state: an antecedent of the closure together with
a sublist of the deduplicated closure. -/
def candR (s : RState) : List (Pos × List Neg) :=
  (ddup (caOf (clStR s))).flatMap (fun Q =>
    (powerL (ddupN (clStR s))).map (fun T => (Q, T)))

/-- The candidate pairs not yet recorded, up to set-equality of the station. -/
def candFreeR (s : RState) : List (Pos × List Neg) :=
  (candR s).filter (fun pr => !seenMemR s.2.2.2 pr.1 pr.2)

/-- **The pair-deficiency component `κ₂`.** -/
def kap2 (s : RState) : Nat := (ddupPair (candFreeR s)).length

/-- **The candidate measure.** -/
def rMu (s : RState) : Nat := kap2 s * bigWR s + nuR s

theorem mem_candR {s : RState} {Q : Pos} {T : List Neg} :
    (Q, T) ∈ candR s ↔ (Q ∈ caOf (clStR s) ∧ T ∈ powerL (ddupN (clStR s))) := by
  simp only [candR, List.mem_flatMap, List.mem_map, Prod.mk.injEq, mem_ddup]
  constructor
  · rintro ⟨Q', hQ', T', hT', rfl, rfl⟩
    exact ⟨hQ', hT'⟩
  · rintro ⟨hQ, hT⟩
    exact ⟨Q, hQ, T, hT, rfl, rfl⟩

theorem mem_candFreeR {s : RState} {Q : Pos} {T : List Neg} :
    (Q, T) ∈ candFreeR s ↔
      (Q ∈ caOf (clStR s) ∧ T ∈ powerL (ddupN (clStR s)) ∧
        seenMemR s.2.2.2 Q T = false) := by
  simp only [candFreeR, List.mem_filter, mem_candR, Bool.not_eq_true']
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩

/-! ## The two counting lemmas -/

/-- The canonical transfer of a candidate pair into a state's enumeration. -/
def trPair (s : RState) (pr : Pos × List Neg) : Pos × List Neg :=
  (pr.1, canonSt (ddupN (clStR s)) pr.2)

section Count
variable {s t : RState}

theorem trPair_mem (hcl : clStR t ⊆ clStR s)
    (hseen : ∀ (Q : Pos) (T : List Neg),
      seenMemR t.2.2.2 Q T = false → seenMemR s.2.2.2 Q T = false)
    {pr : Pos × List Neg} (h : pr ∈ candFreeR t) : trPair s pr ∈ candFreeR s := by
  obtain ⟨Q, T⟩ := pr
  obtain ⟨hQ, hT, hfree⟩ := mem_candFreeR.mp h
  have hTsub : ∀ X ∈ T, X ∈ ddupN (clStR s) := fun X hX =>
    mem_ddupN.mpr (hcl (mem_ddupN.mp (mem_powerL_sub hT X hX)))
  refine mem_candFreeR.mpr ⟨caOf_mono hcl hQ, canonSt_mem_powerL _ _, ?_⟩
  have hcg := seenMemR_congr (seen := s.2.2.2) (Q := Q)
    (sameSet_symm (canonSt_sameSet hTsub))
  rw [← hcg]
  exact hseen Q T hfree

theorem trPair_inj (hcl : clStR t ⊆ clStR s)
    {pr₁ pr₂ : Pos × List Neg} (h₁ : pr₁ ∈ candFreeR t) (h₂ : pr₂ ∈ candFreeR t)
    (heq : trPair s pr₁ = trPair s pr₂) : pr₁ = pr₂ := by
  obtain ⟨Q₁, T₁⟩ := pr₁
  obtain ⟨Q₂, T₂⟩ := pr₂
  obtain ⟨_, hT₁, _⟩ := mem_candFreeR.mp h₁
  obtain ⟨_, hT₂, _⟩ := mem_candFreeR.mp h₂
  have hQ : Q₁ = Q₂ := congrArg Prod.fst heq
  subst hQ
  have hc : canonSt (ddupN (clStR s)) T₁ = canonSt (ddupN (clStR s)) T₂ :=
    congrArg Prod.snd heq
  have hs₁ : ∀ X ∈ T₁, X ∈ ddupN (clStR s) := fun X hX =>
    mem_ddupN.mpr (hcl (mem_ddupN.mp (mem_powerL_sub hT₁ X hX)))
  have hs₂ : ∀ X ∈ T₂, X ∈ ddupN (clStR s) := fun X hX =>
    mem_ddupN.mpr (hcl (mem_ddupN.mp (mem_powerL_sub hT₂ X hX)))
  have hsame : sameSet T₁ T₂ = true := by
    refine sameSet_trans (sameSet_symm (canonSt_sameSet hs₁)) ?_
    rw [hc]
    exact canonSt_sameSet hs₂
  have h1 : canonSt (ddupN (clStR t)) T₁ = T₁ := canonSt_id (nodup_ddupN _) hT₁
  have h2 : canonSt (ddupN (clStR t)) T₂ = T₂ := canonSt_id (nodup_ddupN _) hT₂
  have hTT : T₁ = T₂ := by
    rw [← h1, ← h2]
    exact canonSt_congr hsame _
  rw [hTT]

/-- **`κ₂` is non-increasing** along an edge that carries `seen` and does not
grow the closure. -/
theorem kap2_le (hcl : clStR t ⊆ clStR s) (hseen : t.2.2.2 = s.2.2.2) :
    kap2 t ≤ kap2 s := by
  have hs : ∀ (Q : Pos) (T : List Neg),
      seenMemR t.2.2.2 Q T = false → seenMemR s.2.2.2 Q T = false := by
    intro Q T h; rw [← hseen]; exact h
  have hmapnd : ((ddupPair (candFreeR t)).map (trPair s)).Nodup := by
    refine List.Nodup.map_on ?_ (nodup_ddupPair _)
    intro x hx y hy hxy
    exact trPair_inj hcl (mem_ddupPair.mp hx) (mem_ddupPair.mp hy) hxy
  have hsub : (ddupPair (candFreeR t)).map (trPair s) ⊆ ddupPair (candFreeR s) := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
    exact mem_ddupPair.mpr (trPair_mem hcl hs (mem_ddupPair.mp hx))
  have h := nodupPair_length_le hmapnd hsub
  rw [List.length_map] at h
  exact h

/-- **`κ₂` strictly drops** along a guard edge: the recorded pair is a
candidate at the source and was not recorded there. -/
theorem kap2_lt {Qa : Pos} {done : List Neg}
    (hcl : clStR t ⊆ clStR s) (hseen : t.2.2.2 = (Qa, done) :: s.2.2.2)
    (hQa : Qa ∈ caOf (clStR s)) (hdone : ∀ X ∈ done, X ∈ clStR s)
    (hnew : seenMemR s.2.2.2 Qa done = false) : kap2 t + 1 ≤ kap2 s := by
  have hs : ∀ (Q : Pos) (T : List Neg),
      seenMemR t.2.2.2 Q T = false → seenMemR s.2.2.2 Q T = false := by
    intro Q T h
    rw [hseen] at h
    exact seenMemR_of_cons h
  have hdoneS : ∀ X ∈ done, X ∈ ddupN (clStR s) := fun X hX => mem_ddupN.mpr (hdone X hX)
  have hcanonSame := canonSt_sameSet hdoneS
  have hnewC : (Qa, canonSt (ddupN (clStR s)) done) ∈ candFreeR s := by
    refine mem_candFreeR.mpr ⟨hQa, canonSt_mem_powerL _ _, ?_⟩
    have hcg := seenMemR_congr (seen := s.2.2.2) (Q := Qa) (sameSet_symm hcanonSame)
    rw [← hcg]
    exact hnew
  have hnotim : (Qa, canonSt (ddupN (clStR s)) done) ∉
      (ddupPair (candFreeR t)).map (trPair s) := by
    intro hc
    obtain ⟨⟨Q, T⟩, hx, heq⟩ := List.mem_map.mp hc
    obtain ⟨_, hT, hfree⟩ := mem_candFreeR.mp (mem_ddupPair.mp hx)
    have hQ : Q = Qa := congrArg Prod.fst heq
    subst hQ
    have hcS : canonSt (ddupN (clStR s)) T = canonSt (ddupN (clStR s)) done :=
      congrArg Prod.snd heq
    have hTsub : ∀ X ∈ T, X ∈ ddupN (clStR s) := fun X hX =>
      mem_ddupN.mpr (hcl (mem_ddupN.mp (mem_powerL_sub hT X hX)))
    have hsame : sameSet done T = true := by
      refine sameSet_symm (sameSet_trans (sameSet_symm (canonSt_sameSet hTsub)) ?_)
      rw [hcS]
      exact hcanonSame
    have hcc : seenMemR t.2.2.2 Q T = true := by
      rw [hseen]
      exact (seenMemR_iff _ Q T).mpr ⟨done, List.mem_cons_self .., hsame⟩
    rw [hfree] at hcc
    exact Bool.noConfusion hcc
  have hmapnd : ((ddupPair (candFreeR t)).map (trPair s)).Nodup := by
    refine List.Nodup.map_on ?_ (nodup_ddupPair _)
    intro x hx y hy hxy
    exact trPair_inj hcl (mem_ddupPair.mp hx) (mem_ddupPair.mp hy) hxy
  have hnd : ((Qa, canonSt (ddupN (clStR s)) done) ::
      (ddupPair (candFreeR t)).map (trPair s)).Nodup :=
    List.nodup_cons.mpr ⟨hnotim, hmapnd⟩
  have hsub : ((Qa, canonSt (ddupN (clStR s)) done) ::
      (ddupPair (candFreeR t)).map (trPair s)) ⊆ ddupPair (candFreeR s) := by
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact mem_ddupPair.mpr hnewC
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
      exact mem_ddupPair.mpr (trPair_mem hcl hs (mem_ddupPair.mp hx))
  have h := nodupPair_length_le hnd hsub
  rw [List.length_cons, List.length_map] at h
  exact h

end Count

/-! # Part 6 · The two flattening lemmas -/

theorem bigWR_mono {s t : RState} (h : clStR t ⊆ clStR s) : bigWR t ≤ bigWR s :=
  bigW_mono h

/-- **An ordinary edge**: the closure does not grow, `seen` is carried, and
`ν` strictly drops. -/
theorem rMu_lt_of_ordinary {s t : RState} (hcl : clStR t ⊆ clStR s)
    (hseen : t.2.2.2 = s.2.2.2) (hnu : nuR t < nuR s) : rMu t < rMu s := by
  have hk : kap2 t ≤ kap2 s := kap2_le hcl hseen
  have hw : bigWR t ≤ bigWR s := bigWR_mono hcl
  have hm : kap2 t * bigWR t ≤ kap2 s * bigWR s :=
    Nat.le_trans (Nat.mul_le_mul_left _ hw) (Nat.mul_le_mul_right _ hk)
  simp only [rMu]; omega

/-- **A guard edge**: the closure does not grow, `seen` gains a candidate pair
that was not recorded, and `ν` stays below `ν s + W s`. -/
theorem rMu_lt_of_guard {s t : RState} {Qa : Pos} {done : List Neg}
    (hcl : clStR t ⊆ clStR s) (hseen : t.2.2.2 = (Qa, done) :: s.2.2.2)
    (hQa : Qa ∈ caOf (clStR s)) (hdone : ∀ X ∈ done, X ∈ clStR s)
    (hnew : seenMemR s.2.2.2 Qa done = false)
    (hnu : nuR t < nuR s + bigWR s) : rMu t < rMu s := by
  have hk : kap2 t + 1 ≤ kap2 s := kap2_lt hcl hseen hQa hdone hnew
  have hw : bigWR t ≤ bigWR s := bigWR_mono hcl
  have h1 : kap2 t * bigWR t ≤ kap2 t * bigWR s := Nat.mul_le_mul_left _ hw
  have h2 : (kap2 t + 1) * bigWR s ≤ kap2 s * bigWR s := Nat.mul_le_mul_right _ hk
  have h3 : (kap2 t + 1) * bigWR s = kap2 t * bigWR s + bigWR s := by ring
  simp only [rMu]
  omega

end LJFO

/-! ## Pins -/

#axioms_within LJFO.interpGR_founded_eq [propext, Quot.sound]
#axioms_within LJFO.interpGR_stab_of_founded [propext, Quot.sound]
#axioms_within LJFO.rStabLitE_of_bound [propext, Quot.sound]
#axioms_within LJFO.rStabLitA_of_bound [propext, Quot.sound]
#axioms_within LJFO.negMem_iff [propext, Quot.sound]
#axioms_within LJFO.sameSet_iff [propext, Quot.sound]
#axioms_within LJFO.seenMemR_iff [propext, Quot.sound]
#axioms_within LJFO.seenMemR_congr [propext, Quot.sound]
#axioms_within LJFO.canonSt_id [propext, Quot.sound]
#axioms_within LJFO.nodupPair_length_le [propext, Quot.sound]
#axioms_within LJFO.kap2_le [propext, Quot.sound]
#axioms_within LJFO.kap2_lt [propext, Quot.sound]
#axioms_within LJFO.rMu_lt_of_ordinary [propext, Quot.sound]
#axioms_within LJFO.rMu_lt_of_guard [propext, Quot.sound]
