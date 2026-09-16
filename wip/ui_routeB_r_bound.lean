/-
Route (B), node **N4**, WP12b, **stage 1, part C**: **the measure descends**,
and `RBound p` is discharged.

`wip/ui_routeB_r_cong.lean` proves that `stepR id p prev` at `s` reads `prev`
only at the states of `edgesR s`.  This module proves

    edges_decreaseR : ∀ t ∈ edgesR s, rMu t < rMu s

edge by edge — `wip/ui_routeB_n4q_bound.lean` Parts 3–5, with `qMu` replaced
by `rMu` and the guard edge restated for the PAIR record — and hence

    rFounded : RFounded id p rMu
    rBound   : RBound p
    rStabLitE_uncond / rStabLitA_uncond : literal stabilisation at EVERY
        station, unconditionally.

The edge table is `docs/n4-bound.md` §3; only the last row (the guard edges)
changes, and it changes only in what is recorded.

`LJF/` is untouched; this module is a leaf.
-/
import wip.ui_routeB_r_cong
import Meta.Audit

set_option autoImplicit false

namespace LJFO

/-! # Part 1 · The guard edge, restated for the pair record

`seen` gains the PAIR `(Qa, done)`, which is a candidate at the source — the
antecedent is one of the closure's and the station lies inside the closure —
and is unrecorded there, since the loop check did not fire.  The closure does
not grow and the new goal weight is strictly below `W`. -/

theorem guard_ltR {done rest : List Neg} {g : Option Neg} {seen : SeenR}
    {Qa : Pos} {N : Neg} (hXr : (Neg.imp Qa N, rest) ∈ splits done)
    (hnew : seenMemR seen Qa done = false) :
    rMu (([] : List Neg), done, some (Neg.up Qa), (Qa, done) :: seen)
      < rMu (([] : List Neg), done, g, seen) := by
  have hmemD : Neg.imp Qa N ∈ done := splits_mem hXr
  have himp : Neg.imp Qa N ∈ clStR (([] : List Neg), done, g, seen) :=
    mem_clStR.mpr (Or.inr (Or.inl (mem_subL_self hmemD)))
  have hant : subN (Neg.up Qa) ⊆ subL done := fun x hx =>
    mem_subL hmemD (subP_sub_subN_imp Qa N (subN_up_sub Qa hx))
  refine rMu_lt_of_guard (Qa := Qa) (done := done) ?_ rfl
    (mem_caOf.mpr ⟨N, himp⟩) ?_ hnew ?_
  · intro x hx
    rcases mem_clStR.mp hx with hx | hx | hx
    · simp [subL_nil] at hx
    · exact mem_clStR.mpr (Or.inr (Or.inl hx))
    · exact mem_clStR.mpr (Or.inr (Or.inl (hant (mem_subG_some.mp hx))))
  · intro X hX
    exact mem_clStR.mpr (Or.inr (Or.inl (mem_subL_self hX)))
  · have hlt := pow_ant_lt_bigW (s := (([] : List Neg), done, g, ([] : List Pos))) himp
    show 2 * sum3 ([] : List Neg) + sum3 done + 3 ^ wPos Qa
       < (2 * sum3 ([] : List Neg) + sum3 done + goalW g)
         + bigWR (([] : List Neg), done, g, seen)
    exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hlt _)
      (Nat.add_le_add_right (Nat.le_add_right _ _) _)

/-! # Part 3 · The edge lemmas -/

/-- **The second component of a parked row**, and the atom fire: the
consequent replaces the whole implication. -/
theorem parkSecondR_lt {done rest : List Neg} {g : Option Neg} {seen : SeenR}
    {Qa : Pos} {N : Neg} (hXr : (Neg.imp Qa N, rest) ∈ splits done) :
    rMu ([N], rest, g, seen) < rMu ([], done, g, seen) := by
  have hmemD : Neg.imp Qa N ∈ done := splits_mem hXr
  refine rMu_lt_of_ordinary ?_ rfl ?_
  · intro x hx
    rcases mem_clStR.mp hx with hx | hx | hx
    · refine mem_clStR.mpr (Or.inr (Or.inl ?_))
      obtain ⟨M, hM, hxM⟩ := mem_subL_iff.mp hx
      rcases List.mem_singleton.mp hM with rfl
      exact mem_subL hmemD (subN_con_sub_imp Qa _ hxM)
    · exact mem_clStR.mpr (Or.inr (Or.inl (subL_mono (splits_rest hXr) hx)))
    · exact mem_clStR.mpr (Or.inr (Or.inr hx))
  · have := dec_parkFire hXr
    simp only [nuR_mk, sum3]
    omega

/-- **The `∃p` residual of a non-Dyckhoff parked row**: the station shrinks. -/
theorem parkResR_lt {done rest : List Neg} {seen : SeenR} {X : Neg}
    (hXr : (X, rest) ∈ splits done) :
    rMu (([] : List Neg), rest, none, seen) < rMu ([], done, none, seen) := by
  refine rMu_lt_of_ordinary ?_ rfl ?_
  · intro x hx
    rcases mem_clStR.mp hx with hx | hx | hx
    · simp [subL_nil] at hx
    · exact mem_clStR.mpr (Or.inr (Or.inl (subL_mono (splits_rest hXr) hx)))
    · exact absurd hx (by simp [subG])
  · have := dec_cimp3 hXr
    simp only [nuR_mk, sum3, goalW]
    omega

/-- **The Dyckhoff residual**: the manufactured implication is in the
closure, and it is lighter. -/
theorem dykResR_lt {done rest : List Neg} {seen : SeenR} {Q' : Pos} {N' N : Neg}
    (hXr : (Neg.imp (.down (.imp Q' N')) N, rest) ∈ splits done) :
    rMu ([Neg.imp (.down N') N], rest, none, seen) < rMu ([], done, none, seen) := by
  have hmemD : Neg.imp (.down (.imp Q' N')) N ∈ done := splits_mem hXr
  refine rMu_lt_of_ordinary ?_ rfl ?_
  · intro x hx
    rcases mem_clStR.mp hx with hx | hx | hx
    · refine mem_clStR.mpr (Or.inr (Or.inl ?_))
      obtain ⟨M, hM, hxM⟩ := mem_subL_iff.mp hx
      rcases List.mem_singleton.mp hM with rfl
      exact mem_subL hmemD (subN_dyk_sub Q' N' N hxM)
    · exact mem_clStR.mpr (Or.inr (Or.inl (subL_mono (splits_rest hXr) hx)))
    · exact absurd hx (by simp [subG])
  · have := dec_dykRes hXr
    simp only [nuR_mk, sum3, goalW]
    omega

/-- **Opening a parked box**: the body enters the todo, paid for by the
box's own `+1`. -/
theorem boxOpenR_lt {done rest : List Neg} {seen : SeenR} {R : Pos}
    {g g' : Option Neg} (hXr : (Neg.circ R, rest) ∈ splits done)
    (hgcl : subG g' ⊆ subG g) (hg : goalW g' ≤ goalW g) :
    rMu ([Neg.up R], rest, g', seen) < rMu ([], done, g, seen) := by
  have hmemD : Neg.circ R ∈ done := splits_mem hXr
  refine rMu_lt_of_ordinary ?_ rfl ?_
  · intro x hx
    rcases mem_clStR.mp hx with hx | hx | hx
    · refine mem_clStR.mpr (Or.inr (Or.inl ?_))
      obtain ⟨M, hM, hxM⟩ := mem_subL_iff.mp hx
      rcases List.mem_singleton.mp hM with rfl
      exact mem_subL hmemD (subP_sub_subN_circ R (subN_up_sub R hxM))
    · exact mem_clStR.mpr (Or.inr (Or.inl (subL_mono (splits_rest hXr) hx)))
    · exact mem_clStR.mpr (Or.inr (Or.inr (hgcl hx)))
  · have := dec_boxE hXr
    simp only [nuR_mk, sum3, wNeg]
    omega

/-- **A goal move at a fixed station**: the lax prefix, the `∨`-goal
disjuncts, the `↑↓`-goal and the `∧`-goal. -/
theorem goalMoveR_lt {done : List Neg} {g g' : Option Neg} {seen : SeenR}
    (hcl : subG g' ⊆ clStR (([] : List Neg), done, g, seen))
    (hlt : goalW g' < goalW g) :
    rMu (([] : List Neg), done, g', seen) < rMu ([], done, g, seen) := by
  refine rMu_lt_of_ordinary ?_ rfl ?_
  · intro x hx
    rcases mem_clStR.mp hx with hx | hx | hx
    · simp [subL_nil] at hx
    · exact mem_clStR.mpr (Or.inr (Or.inl hx))
    · exact hcl hx
  · simp only [nuR_mk, sum3]; omega

/-- **The `∀p` implication goal**: `invertPos Q` moves branches INTO the
station — the growth that refuted the per-station reset policy — and the
closure still does not grow, because the branches are subformulas of the
goal. -/
theorem impGoalR_lt {done b : List Neg} {Q : Pos} {N : Neg} {g' : Option Neg}
    {seen : SeenR} (hb : b ∈ invertPos Q)
    (hgcl : subG g' ⊆ subN (Neg.imp Q N)) (hg : goalW g' ≤ 3 ^ wNeg N) :
    rMu (b, done, g', seen) < rMu ([], done, some (.imp Q N), seen) := by
  refine rMu_lt_of_ordinary ?_ rfl ?_
  · intro x hx
    rcases mem_clStR.mp hx with hx | hx | hx
    · exact mem_clStR.mpr (Or.inr (Or.inr
        (mem_subG_some.mpr (subP_sub_subN_imp Q N (subL_invert hb hx)))))
    · exact mem_clStR.mpr (Or.inr (Or.inl hx))
    · exact mem_clStR.mpr (Or.inr (Or.inr (mem_subG_some.mpr (hgcl hx))))
  · have hd := dec_ainv (Q := Q) (b := b) (N := N) (d := sum3 done) hb
    show 2 * sum3 b + sum3 done + goalW g'
       < 2 * sum3 ([] : List Neg) + sum3 done + 3 ^ wNeg (Neg.imp Q N)
    exact Nat.lt_of_le_of_lt (Nat.add_le_add_left hg _) hd

/-! ## The processing edges -/

/-- **Parking**: a hypothesis moves from the doubled side to the single one. -/
theorem parkR_lt {X : Neg} {todo done : List Neg} {g : Option Neg} {seen : SeenR} :
    rMu (todo, X :: done, g, seen) < rMu (X :: todo, done, g, seen) := by
  refine rMu_lt_of_ordinary ?_ rfl ?_
  · intro x hx
    rcases mem_clStR.mp hx with hx | hx | hx
    · exact mem_clStR.mpr (Or.inl (mem_subL_cons.mpr (Or.inr hx)))
    · rcases mem_subL_cons.mp hx with hx | hx
      · exact mem_clStR.mpr (Or.inl (mem_subL_cons.mpr (Or.inl hx)))
      · exact mem_clStR.mpr (Or.inr (Or.inl hx))
    · exact mem_clStR.mpr (Or.inr (Or.inr hx))
  · have := p3_pos (wNeg X)
    simp only [nuR_mk, sum3]
    omega

/-- **An inert hypothesis** `⊥ ⊃ N` is dropped. -/
theorem dropR_lt {X : Neg} {todo done : List Neg} {g : Option Neg} {seen : SeenR} :
    rMu (todo, done, g, seen) < rMu (X :: todo, done, g, seen) := by
  refine rMu_lt_of_ordinary ?_ rfl ?_
  · intro x hx
    rcases mem_clStR.mp hx with hx | hx | hx
    · exact mem_clStR.mpr (Or.inl (mem_subL_cons.mpr (Or.inr hx)))
    · exact mem_clStR.mpr (Or.inr (Or.inl hx))
    · exact mem_clStR.mpr (Or.inr (Or.inr hx))
  · have := p3_pos (wNeg X)
    simp only [nuR_mk, sum3]
    omega

/-- **A processing replacement**: the head of `todo` becomes strictly
lighter material drawn from its own closure. -/
theorem todoReplR_lt {X : Neg} {r todo done : List Neg} {g g' : Option Neg}
    {seen : SeenR} (hcl : subL r ⊆ subN X) (hgcl : subG g' ⊆ subG g)
    (hg : goalW g' ≤ goalW g) (hlt : sum3 r < 3 ^ wNeg X) :
    rMu (r ++ todo, done, g', seen) < rMu (X :: todo, done, g, seen) := by
  refine rMu_lt_of_ordinary ?_ rfl ?_
  · intro x hx
    rcases mem_clStR.mp hx with hx | hx | hx
    · rw [subL_append] at hx
      rcases List.mem_append.mp hx with hx | hx
      · exact mem_clStR.mpr (Or.inl (mem_subL_cons.mpr (Or.inl (hcl hx))))
      · exact mem_clStR.mpr (Or.inl (mem_subL_cons.mpr (Or.inr hx)))
    · exact mem_clStR.mpr (Or.inr (Or.inl hx))
    · exact mem_clStR.mpr (Or.inr (Or.inr (hgcl hx)))
  · simp only [nuR_mk, sum3_append, sum3]
    omega

/-! # Part 4 · The row maps descend -/

theorem parkEdgesER_decrease {done rest res : List Neg} {Qa : Pos} {N : Neg}
    {seen : SeenR} (hXr : (Neg.imp Qa N, rest) ∈ splits done)
    (hres : rMu (res, rest, none, seen) < rMu ([], done, none, seen)) :
    ∀ t ∈ parkEdgesER done Qa N rest res seen, rMu t < rMu ([], done, none, seen) := by
  intro t ht
  simp only [parkEdgesER, List.mem_append] at ht
  rcases ht with ht | ht
  · by_cases hm : seenMemR seen Qa done = true
    · simp [hm] at ht
    · simp only [Bool.not_eq_true] at hm
      simp only [hm, Bool.false_eq_true, if_false, List.mem_cons,
        List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · exact guard_ltR hXr hm
      · exact parkSecondR_lt hXr
  · rcases List.mem_singleton.mp ht with rfl
    exact hres

theorem parkEdgesAR_decrease {done rest : List Neg} {Qa : Pos} {N goal : Neg}
    {seen : SeenR} (hXr : (Neg.imp Qa N, rest) ∈ splits done) :
    ∀ t ∈ parkEdgesAR done Qa N rest goal seen,
      rMu t < rMu ([], done, some goal, seen) := by
  intro t ht
  by_cases hm : seenMemR seen Qa done = true
  · simp [parkEdgesAR, hm] at ht
  · simp only [Bool.not_eq_true] at hm
    simp only [parkEdgesAR, hm, Bool.false_eq_true, if_false, List.mem_cons,
      List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact guard_ltR hXr hm
    · exact parkSecondR_lt hXr

theorem eRowEdgesR_decrease {done : List Neg} {seen : SeenR} :
    ∀ t ∈ eRowEdgesR done seen, rMu t < rMu (([] : List Neg), done, none, seen) := by
  intro t ht
  obtain ⟨⟨X, rest⟩, hXr, ht⟩ := List.mem_flatMap.mp ht
  simp only at ht
  match X with
  | .up (.atom a) => simp [eRowBodyR] at ht
  | .imp (.atom a) N =>
      rw [show eRowBodyR done seen (Neg.imp (.atom a) N) rest
            = [(([N] : List Neg), rest, (none : Option Neg), seen)] from rfl] at ht
      rcases List.mem_singleton.mp ht with rfl
      exact parkSecondR_lt hXr
  | .imp (.down (.imp Q' N')) N =>
      exact parkEdgesER_decrease hXr (dykResR_lt hXr) t ht
  | .circ Q =>
      rw [show eRowBodyR done seen (Neg.circ Q) rest
            = [(([Neg.up Q] : List Neg), rest, (none : Option Neg), seen)] from rfl] at ht
      rcases List.mem_singleton.mp ht with rfl
      exact boxOpenR_lt hXr (fun _ h => h) (Nat.le_refl _)
  | .imp (.down (.circ Q')) N => exact parkEdgesER_decrease hXr (parkResR_lt hXr) t ht
  | .imp (.or Qa Qb) N => exact parkEdgesER_decrease hXr (parkResR_lt hXr) t ht
  | .imp (.down (.up Pa)) N => exact parkEdgesER_decrease hXr (parkResR_lt hXr) t ht
  | .imp (.down (.and Ma Mb)) N => exact parkEdgesER_decrease hXr (parkResR_lt hXr) t ht
  | .up .fls | .up (.or _ _) | .up (.down _) | .imp .fls _ | .and _ _ =>
      simp [eRowBodyR] at ht

theorem aRowEdgesR_decrease {done : List Neg} {goal : Neg} {box : Bool}
    {seen : SeenR} :
    ∀ t ∈ aRowEdgesR done goal box seen, rMu t < rMu (([] : List Neg), done, some goal, seen) := by
  intro t ht
  obtain ⟨⟨X, rest⟩, hXr, ht⟩ := List.mem_flatMap.mp ht
  simp only at ht
  match X with
  | .imp (.atom a) N =>
      rw [show aRowBodyR done goal box seen (Neg.imp (.atom a) N) rest
            = [(([N] : List Neg), rest, some goal, seen)] from rfl] at ht
      rcases List.mem_singleton.mp ht with rfl
      exact parkSecondR_lt hXr
  | .imp (.down (.imp Q' N')) N => exact parkEdgesAR_decrease hXr t ht
  | .imp (.down (.circ Q')) N => exact parkEdgesAR_decrease hXr t ht
  | .imp (.or Qa Qb) N => exact parkEdgesAR_decrease hXr t ht
  | .imp (.down (.up Pa)) N => exact parkEdgesAR_decrease hXr t ht
  | .imp (.down (.and Ma Mb)) N => exact parkEdgesAR_decrease hXr t ht
  | .circ R =>
      rw [show aRowBodyR done goal box seen (Neg.circ R) rest
            = (if box then [(([Neg.up R] : List Neg), rest, (none : Option Neg), seen),
                            ([Neg.up R], rest, some goal, seen)] else []) from rfl] at ht
      by_cases hb : box = true
      · simp only [hb, if_true, List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl
        · exact boxOpenR_lt hXr (by simp [subG]) (by simp [goalW])
        · exact boxOpenR_lt hXr (fun _ h => h) (Nat.le_refl _)
      · simp only [Bool.not_eq_true] at hb
        simp [hb] at ht
  | .up (.atom _) | .up .fls | .up (.or _ _) | .up (.down _) | .imp .fls _
  | .and _ _ => simp [aRowBodyR] at ht

theorem laxEdgesR_decrease {done : List Neg} {seen : SeenR} {Q : Pos} :
    ∀ t ∈ laxEdgesR done seen Q,
      rMu t < rMu (([] : List Neg), done, some (.circ Q), seen) := by
  intro t ht
  match Q with
  | .atom q =>
      simp only [laxEdgesR, List.mem_singleton] at ht
      rcases ht with rfl
      refine goalMoveR_lt ?_ ?_
      · intro x hx
        exact mem_clStR.mpr (Or.inr (Or.inr
          (mem_subG_some.mpr (subP_sub_subN_circ _ (subN_up_sub _ (mem_subG_some.mp hx))))))
      · simp only [goalW, wNeg, wPos]; exact p3_strict (by omega)
  | .fls =>
      simp only [laxEdgesR, List.mem_singleton] at ht
      rcases ht with rfl
      refine goalMoveR_lt ?_ ?_
      · intro x hx
        exact mem_clStR.mpr (Or.inr (Or.inr
          (mem_subG_some.mpr (subP_sub_subN_circ _ (subN_up_sub _ (mem_subG_some.mp hx))))))
      · simp only [goalW, wNeg, wPos]; exact p3_strict (by omega)
  | .or P₁ P₂ =>
      simp only [laxEdgesR, List.mem_cons, List.not_mem_nil, or_false] at ht
      have hP₁ := wPos_pos P₁
      have hP₂ := wPos_pos P₂
      rcases ht with rfl | rfl | rfl
      · refine goalMoveR_lt ?_ ?_
        · intro x hx
          refine mem_clStR.mpr (Or.inr (Or.inr (mem_subG_some.mpr ?_)))
          exact subP_sub_subN_circ _ (subP_or_left P₁ P₂ (subN_circ_sub P₁ (mem_subG_some.mp hx)))
        · simp only [goalW, wNeg, wPos]; exact p3_strict (by omega)
      · refine goalMoveR_lt ?_ ?_
        · intro x hx
          refine mem_clStR.mpr (Or.inr (Or.inr (mem_subG_some.mpr ?_)))
          exact subP_sub_subN_circ _ (subP_or_right P₁ P₂ (subN_circ_sub P₂ (mem_subG_some.mp hx)))
        · simp only [goalW, wNeg, wPos]; exact p3_strict (by omega)
      · refine goalMoveR_lt ?_ ?_
        · intro x hx
          exact mem_clStR.mpr (Or.inr (Or.inr (mem_subG_some.mpr
            (subP_sub_subN_circ _ (subN_up_sub _ (mem_subG_some.mp hx))))))
        · simp only [goalW, wNeg, wPos]; exact p3_strict (by omega)
  | .down (.up P') =>
      simp only [laxEdgesR, List.mem_singleton] at ht
      rcases ht with rfl
      refine goalMoveR_lt ?_ ?_
      · intro x hx
        refine mem_clStR.mpr (Or.inr (Or.inr (mem_subG_some.mpr ?_)))
        refine subP_sub_subN_circ _ ?_
        refine subN_sub_subP_down _ ?_
        exact subP_sub_subN_up P' (subN_circ_sub P' (mem_subG_some.mp hx))
      · simp only [goalW, wNeg, wPos]; exact p3_strict (by omega)
  | .down (.circ P') =>
      simp only [laxEdgesR, List.mem_singleton] at ht
      rcases ht with rfl
      refine goalMoveR_lt ?_ ?_
      · intro x hx
        refine mem_clStR.mpr (Or.inr (Or.inr (mem_subG_some.mpr ?_)))
        refine subP_sub_subN_circ _ ?_
        exact subN_sub_subP_down _ (mem_subG_some.mp hx)
      · simp only [goalW, wNeg, wPos]; exact p3_strict (by omega)
  | .down (.and M₁ M₂) =>
      simp only [laxEdgesR, List.mem_singleton] at ht
      rcases ht with rfl
      refine goalMoveR_lt ?_ ?_
      · intro x hx
        exact mem_clStR.mpr (Or.inr (Or.inr (mem_subG_some.mpr
          (subP_sub_subN_circ _ (subN_up_sub _ (mem_subG_some.mp hx))))))
      · simp only [goalW, wNeg]; exact p3_strict (by omega)
  | .down (.imp Q₀ N₀) =>
      simp only [laxEdgesR, List.mem_singleton] at ht
      rcases ht with rfl
      refine goalMoveR_lt ?_ ?_
      · intro x hx
        exact mem_clStR.mpr (Or.inr (Or.inr (mem_subG_some.mpr
          (subP_sub_subN_circ _ (subN_up_sub _ (mem_subG_some.mp hx))))))
      · simp only [goalW, wNeg]; exact p3_strict (by omega)

theorem aggEdgesR_decrease {done : List Neg} {g : Option Neg} {seen : SeenR} :
    ∀ t ∈ aggEdgesR done g seen, rMu t < rMu (([] : List Neg), done, g, seen) := by
  intro t ht
  match g with
  | none => exact eRowEdgesR_decrease t ht
  | some (.imp Q N) =>
      simp only [aggEdgesR] at ht
      obtain ⟨b, hb, ht⟩ := List.mem_flatMap.mp ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · exact impGoalR_lt hb (by simp [subG]) (by simp [goalW])
      · exact impGoalR_lt hb (subN_con_sub_imp Q N) (Nat.le_refl _)
  | some (.and M N) =>
      simp only [aggEdgesR, List.mem_cons, List.not_mem_nil, or_false] at ht
      have h1 := wNeg_pos M
      have h2 := wNeg_pos N
      rcases ht with rfl | rfl
      · refine goalMoveR_lt ?_ ?_
        · intro x hx
          refine mem_clStR.mpr (Or.inr (Or.inr (mem_subG_some.mpr ?_)))
          rw [subN_and]
          exact List.mem_cons_of_mem _
            (List.mem_append.mpr (Or.inl (mem_subG_some.mp hx)))
        · simp only [goalW, wNeg]; exact p3_strict (by omega)
      · refine goalMoveR_lt ?_ ?_
        · intro x hx
          refine mem_clStR.mpr (Or.inr (Or.inr (mem_subG_some.mpr ?_)))
          rw [subN_and]
          exact List.mem_cons_of_mem _
            (List.mem_append.mpr (Or.inr (mem_subG_some.mp hx)))
        · simp only [goalW, wNeg]; exact p3_strict (by omega)
  | some (.up (.atom q)) =>
      simp only [aggEdgesR] at ht
      by_cases ha : atomMem q done = true
      · simp [ha] at ht
      · simp only [Bool.not_eq_true] at ha
        simp only [ha, Bool.false_eq_true, if_false] at ht
        exact aRowEdgesR_decrease t ht
  | some (.up .fls) =>
      simp only [aggEdgesR] at ht
      exact aRowEdgesR_decrease t ht
  | some (.up (.or P₁ P₂)) =>
      simp only [aggEdgesR, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false] at ht
      have h1 := wPos_pos P₁
      have h2 := wPos_pos P₂
      rcases ht with (rfl | rfl) | ht
      · refine goalMoveR_lt ?_ ?_
        · intro x hx
          refine mem_clStR.mpr (Or.inr (Or.inr (mem_subG_some.mpr ?_)))
          exact subP_sub_subN_up _ (subP_or_left P₁ P₂ (subN_up_sub P₁ (mem_subG_some.mp hx)))
        · simp only [goalW, wNeg, wPos]; exact p3_strict (by omega)
      · refine goalMoveR_lt ?_ ?_
        · intro x hx
          refine mem_clStR.mpr (Or.inr (Or.inr (mem_subG_some.mpr ?_)))
          exact subP_sub_subN_up _ (subP_or_right P₁ P₂ (subN_up_sub P₂ (mem_subG_some.mp hx)))
        · simp only [goalW, wNeg, wPos]; exact p3_strict (by omega)
      · exact aRowEdgesR_decrease t ht
  | some (.up (.down M)) =>
      simp only [aggEdgesR, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false] at ht
      rcases ht with rfl | ht
      · refine goalMoveR_lt ?_ ?_
        · intro x hx
          refine mem_clStR.mpr (Or.inr (Or.inr (mem_subG_some.mpr ?_)))
          exact subP_sub_subN_up _ (subN_sub_subP_down M (mem_subG_some.mp hx))
        · simp only [goalW, wNeg, wPos]; exact p3_strict (by omega)
      · exact aRowEdgesR_decrease t ht
  | some (.circ Q) =>
      simp only [aggEdgesR, List.mem_append] at ht
      rcases ht with ht | ht
      · exact laxEdgesR_decrease t ht
      · exact aRowEdgesR_decrease t ht

/-! # Part 5 · The descent, the founding, and the bound -/

/-- **Every state the step consults has strictly smaller `rMu`.** -/
theorem edges_decreaseR (s : RState) : ∀ t ∈ edgesR s, rMu t < rMu s := by
  obtain ⟨todo, done, g, seen⟩ := s
  match todo, g with
  | [], g =>
      intro t ht
      simp only [edgesR] at ht
      split at ht
      · rename_i a N rest hf
        rcases List.mem_singleton.mp ht with rfl
        exact parkSecondR_lt (findFire_mem hf)
      · exact aggEdgesR_decrease t ht
  | .up (.atom a) :: todo, g =>
      intro t ht
      simp only [edgesR, List.mem_singleton] at ht
      rcases ht with rfl
      exact parkR_lt
  | .up .fls :: todo, none => intro t ht; simp [edgesR] at ht
  | .up .fls :: todo, some G => intro t ht; simp [edgesR] at ht
  | .up (.or P Q) :: todo, none =>
      intro t ht
      simp only [edgesR, List.mem_map] at ht
      obtain ⟨b, hb, rfl⟩ := ht
      refine todoReplR_lt ?_ (fun _ h => h) (Nat.le_refl _) ?_
      · exact fun x hx => subP_sub_subN_up _ (subL_invert hb hx)
      · have := invertPos_lt (P := Pos.or P Q) (fun a h => Pos.noConfusion h) b hb
        simpa [wNeg] using this
  | .up (.or P Q) :: todo, some G =>
      intro t ht
      simp only [edgesR] at ht
      obtain ⟨b, hb, ht⟩ := List.mem_flatMap.mp ht
      have hcl : subL b ⊆ subN (Neg.up (.or P Q)) :=
        fun x hx => subP_sub_subN_up _ (subL_invert hb hx)
      have hlt : sum3 b < 3 ^ wNeg (Neg.up (Pos.or P Q)) := by
        have := invertPos_lt (P := Pos.or P Q) (fun a h => Pos.noConfusion h) b hb
        simpa [wNeg] using this
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · exact todoReplR_lt hcl (by simp [subG]) (by simp [goalW]) hlt
      · exact todoReplR_lt hcl (fun _ h => h) (Nat.le_refl _) hlt
  | .up (.down M) :: todo, g =>
      intro t ht
      simp only [edgesR, List.mem_singleton] at ht
      rcases ht with rfl
      have : ([M] : List Neg) ++ todo = M :: todo := rfl
      rw [← this]
      refine todoReplR_lt ?_ (fun _ h => h) (Nat.le_refl _) ?_
      · intro x hx
        obtain ⟨M', hM', hxM⟩ := mem_subL_iff.mp hx
        rcases List.mem_singleton.mp hM' with rfl
        exact subP_sub_subN_up _ (subN_sub_subP_down _ hxM)
      · simp only [sum3, wNeg, wPos]
        have := p3_strict (a := wNeg M) (b := wNeg M + 1) (by omega)
        omega
  | .and M N :: todo, g =>
      intro t ht
      simp only [edgesR, List.mem_singleton] at ht
      rcases ht with rfl
      have : ([M, N] : List Neg) ++ todo = M :: N :: todo := rfl
      rw [← this]
      refine todoReplR_lt ?_ (fun _ h => h) (Nat.le_refl _) ?_
      · intro x hx
        obtain ⟨M', hM', hxM⟩ := mem_subL_iff.mp hx
        rw [subN_and]
        refine List.mem_cons_of_mem _ ?_
        rcases List.mem_cons.mp hM' with rfl | hM'
        · exact List.mem_append.mpr (Or.inl hxM)
        · rcases List.mem_singleton.mp hM' with rfl
          exact List.mem_append.mpr (Or.inr hxM)
      · simp only [sum3, wNeg]
        have := p3_add (a := wNeg M) (b := wNeg N) (c := wNeg M + wNeg N + 3)
          (by omega) (by omega)
        omega
  | .imp .fls N :: todo, g =>
      intro t ht
      simp only [edgesR, List.mem_singleton] at ht
      rcases ht with rfl
      exact dropR_lt
  | .imp (.atom a) N :: todo, g =>
      intro t ht
      simp only [edgesR, List.mem_singleton] at ht
      rcases ht with rfl
      exact parkR_lt
  | .imp (.or Q₁ Q₂) N :: todo, g =>
      intro t ht
      simp only [edgesR, List.mem_singleton] at ht
      rcases ht with rfl
      exact parkR_lt
  | .imp (.down (.up P')) N :: todo, g =>
      intro t ht
      simp only [edgesR, List.mem_singleton] at ht
      rcases ht with rfl
      exact parkR_lt
  | .imp (.down (.and M₁ M₂)) N :: todo, g =>
      intro t ht
      simp only [edgesR, List.mem_singleton] at ht
      rcases ht with rfl
      exact parkR_lt
  | .imp (.down (.imp Q' N')) N :: todo, g =>
      intro t ht
      simp only [edgesR, List.mem_singleton] at ht
      rcases ht with rfl
      exact parkR_lt
  | .circ Q :: todo, g =>
      intro t ht
      simp only [edgesR, List.mem_singleton] at ht
      rcases ht with rfl
      exact parkR_lt
  | .imp (.down (.circ Q')) N :: todo, g =>
      intro t ht
      simp only [edgesR, List.mem_singleton] at ht
      rcases ht with rfl
      exact parkR_lt

/-! # Part 5 · The founding, and the bound -/

/-- **`rMu` founds the pair-recording recursion.** -/
theorem rFounded (p : String) : RFounded id p rMu := by
  intro prev₁ prev₂ s h
  exact stepR_congr s (fun t ht => h t (edges_decreaseR s t ht))

/-- **The measure obligation is discharged.** -/
def rBound (p : String) : RBound p := ⟨rMu, rFounded p⟩

/-- Literal stabilisation of the pair-recording `∃p` chain, unconditionally. -/
def rStabLitE_uncond (p : String) (done : List Neg) : RStabLitE p done :=
  rStabLitE_of_bound (rBound p) done

/-- Literal stabilisation of the pair-recording `∀p` chain, unconditionally. -/
def rStabLitA_uncond (p : String) (done : List Neg) (G : Neg) : RStabLitA p done G :=
  rStabLitA_of_bound (rBound p) done G

end LJFO

/-! ## Pins -/

#axioms_within LJFO.guard_ltR [propext, Quot.sound]
#axioms_within LJFO.edges_decreaseR [propext, Quot.sound]
#axioms_within LJFO.rFounded [propext, Quot.sound]
#axioms_within LJFO.rBound [propext, Quot.sound]
#axioms_within LJFO.rStabLitE_uncond [propext, Quot.sound]
#axioms_within LJFO.rStabLitA_uncond [propext, Quot.sound]
