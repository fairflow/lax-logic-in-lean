/-
Route (B), node **N4**, WP9, part C: **the measure descends**, and
`QBound p` is discharged.

`wip/ui_routeB_n4q_cong.lean` proves that `stepQ id p prev` at `s` reads
`prev` only at the states of `edgesQ s`.  This module proves

    edges_decrease : ∀ t ∈ edgesQ s, qMu t < qMu s

edge by edge, and hence

    qFounded : QFounded id p qMu
    qBound   : QBound p

so that `n4_of_interpQ` (`wip/ui_routeB_n4q_thm.lean`) stands over the single
remaining obligation `PQEquiv p`.

The edge table is `docs/n4-bound.md` §2; each row there names the lemma
below that discharges it.
-/
import wip.ui_routeB_n4q_cong
import Meta.Audit

set_option autoImplicit false

namespace LJFO

/-! # Part 1 · Membership in the closure of a state -/

theorem mem_clSt {x : Neg} {todo done : List Neg} {g : Option Neg} {seen : List Pos} :
    x ∈ clSt (todo, done, g, seen) ↔
      (x ∈ subL todo ∨ x ∈ subL done ∨ x ∈ subG g) := by
  simp [clSt, List.mem_append]

theorem mem_subL_cons {x : Neg} {M : Neg} {l : List Neg} :
    x ∈ subL (M :: l) ↔ (x ∈ subN M ∨ x ∈ subL l) := by
  rw [subL_cons]; exact List.mem_append

theorem mem_subL_iff {x : Neg} {l : List Neg} :
    x ∈ subL l ↔ ∃ M ∈ l, x ∈ subN M := List.mem_flatMap

theorem subL_nil : subL ([] : List Neg) = [] := rfl

theorem mem_subG_some {x G : Neg} : x ∈ subG (some G) ↔ x ∈ subN G := Iff.rfl

theorem mem_subG_none {x : Neg} : x ∈ subG (none : Option Neg) ↔ False := by
  simp [subG]

/-- `subP P ⊆ subN (↑P)`. -/
theorem subP_sub_subN_up (P : Pos) : subP P ⊆ subN (.up P) := by
  rw [subN_up]; intro x hx; exact List.mem_cons_of_mem _ hx

/-- `subP P ⊆ subN (◯P)`. -/
theorem subP_sub_subN_circ (P : Pos) : subP P ⊆ subN (.circ P) := by
  rw [subN_circ]; intro x hx; exact List.mem_cons_of_mem _ hx

/-- A branch of an inverted positive lies in the positive's closure. -/
theorem subL_invert {P : Pos} {b : List Neg} (hb : b ∈ invertPos P) :
    subL b ⊆ subP P := by
  intro x hx
  obtain ⟨M, hM, hxM⟩ := mem_subL_iff.mp hx
  exact invert_sub P b hb M hM hxM

/-! # Part 2 · Two station-local weight inequalities

The `dec_*` kit of `LJF/OCore.lean` states the rest; these two shapes are
`interpQ`'s own and are added here. -/

/-- Firing the consequent of ANY parked implication is a descent. -/
theorem dec_parkFire {done rest : List Neg} {Qa : Pos} {N : Neg}
    (h : (Neg.imp Qa N, rest) ∈ splits done) :
    2 * 3 ^ wNeg N + sum3 rest < sum3 done := by
  have hs := splits_sum h
  simp only [wNeg] at hs
  have := p3_2 (a := wNeg N) (c := wPos Qa + wNeg N + 1) (by have := wPos_pos Qa; omega)
  omega

/-- The Dyckhoff residual `↓N′ ⊃ N` is lighter than `↓(Q′ ⊃ N′) ⊃ N`. -/
theorem dec_dykRes {done rest : List Neg} {Q' : Pos} {N' N : Neg}
    (h : (Neg.imp (.down (.imp Q' N')) N, rest) ∈ splits done) :
    2 * 3 ^ wNeg (Neg.imp (.down N') N) + sum3 rest < sum3 done := by
  have hs := splits_sum h
  simp only [wNeg, wPos] at hs ⊢
  have := p3_2 (a := wNeg N' + 1 + wNeg N + 1)
    (c := wPos Q' + wNeg N' + 1 + 1 + wNeg N + 1)
    (by have := wPos_pos Q'; omega)
  omega

/-! # Part 3 · The edge lemmas -/

/-- **The guard edge.**  `seen` gains the antecedent, the closure does not
grow, and the new goal weight is strictly below `W`. -/
theorem guard_lt {done rest : List Neg} {g : Option Neg} {seen : List Pos}
    {Qa : Pos} {N : Neg} (hXr : (Neg.imp Qa N, rest) ∈ splits done)
    (hnew : seenMem seen Qa = false) :
    qMu ([], done, some (.up Qa), Qa :: seen) < qMu ([], done, g, seen) := by
  have hmemD : Neg.imp Qa N ∈ done := splits_mem hXr
  have himp : Neg.imp Qa N ∈ clSt ([], done, g, seen) :=
    mem_clSt.mpr (Or.inr (Or.inl (mem_subL_self hmemD)))
  have hant : subN (Neg.up Qa) ⊆ subL done := fun x hx =>
    mem_subL hmemD (subP_sub_subN_imp Qa N (subN_up_sub Qa hx))
  refine qMu_lt_of_guard (Q' := Qa) ?_ rfl (mem_caOf.mpr ⟨N, himp⟩)
    ((not_seenMem_iff _ _).mp hnew) ?_
  · intro x hx
    rcases mem_clSt.mp hx with hx | hx | hx
    · simp [subL_nil] at hx
    · exact mem_clSt.mpr (Or.inr (Or.inl hx))
    · exact mem_clSt.mpr (Or.inr (Or.inl (hant (mem_subG_some.mp hx))))
  · have hlt := pow_ant_lt_bigW (s := ([], done, g, seen)) himp
    show 2 * sum3 ([] : List Neg) + sum3 done + 3 ^ wPos Qa
       < (2 * sum3 ([] : List Neg) + sum3 done + goalW g) + bigW ([], done, g, seen)
    exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hlt _)
      (Nat.add_le_add_right (Nat.le_add_right _ _) _)

/-- **The second component of a parked row**, and the atom fire: the
consequent replaces the whole implication. -/
theorem parkSecond_lt {done rest : List Neg} {g : Option Neg} {seen : List Pos}
    {Qa : Pos} {N : Neg} (hXr : (Neg.imp Qa N, rest) ∈ splits done) :
    qMu ([N], rest, g, seen) < qMu ([], done, g, seen) := by
  have hmemD : Neg.imp Qa N ∈ done := splits_mem hXr
  refine qMu_lt_of_ordinary ?_ rfl ?_
  · intro x hx
    rcases mem_clSt.mp hx with hx | hx | hx
    · refine mem_clSt.mpr (Or.inr (Or.inl ?_))
      obtain ⟨M, hM, hxM⟩ := mem_subL_iff.mp hx
      rcases List.mem_singleton.mp hM with rfl
      exact mem_subL hmemD (subN_con_sub_imp Qa _ hxM)
    · exact mem_clSt.mpr (Or.inr (Or.inl (subL_mono (splits_rest hXr) hx)))
    · exact mem_clSt.mpr (Or.inr (Or.inr hx))
  · have := dec_parkFire hXr
    simp only [nu, sum3]
    omega

/-- **The `∃p` residual of a non-Dyckhoff parked row**: the station shrinks. -/
theorem parkRes_lt {done rest : List Neg} {seen : List Pos} {X : Neg}
    (hXr : (X, rest) ∈ splits done) :
    qMu (([] : List Neg), rest, none, seen) < qMu ([], done, none, seen) := by
  refine qMu_lt_of_ordinary ?_ rfl ?_
  · intro x hx
    rcases mem_clSt.mp hx with hx | hx | hx
    · simp [subL_nil] at hx
    · exact mem_clSt.mpr (Or.inr (Or.inl (subL_mono (splits_rest hXr) hx)))
    · exact absurd hx (by simp [subG])
  · have := dec_cimp3 hXr
    simp only [nu, sum3, goalW]
    omega

/-- **The Dyckhoff residual**: the manufactured implication is in the
closure, and it is lighter. -/
theorem dykRes_lt {done rest : List Neg} {seen : List Pos} {Q' : Pos} {N' N : Neg}
    (hXr : (Neg.imp (.down (.imp Q' N')) N, rest) ∈ splits done) :
    qMu ([Neg.imp (.down N') N], rest, none, seen) < qMu ([], done, none, seen) := by
  have hmemD : Neg.imp (.down (.imp Q' N')) N ∈ done := splits_mem hXr
  refine qMu_lt_of_ordinary ?_ rfl ?_
  · intro x hx
    rcases mem_clSt.mp hx with hx | hx | hx
    · refine mem_clSt.mpr (Or.inr (Or.inl ?_))
      obtain ⟨M, hM, hxM⟩ := mem_subL_iff.mp hx
      rcases List.mem_singleton.mp hM with rfl
      exact mem_subL hmemD (subN_dyk_sub Q' N' N hxM)
    · exact mem_clSt.mpr (Or.inr (Or.inl (subL_mono (splits_rest hXr) hx)))
    · exact absurd hx (by simp [subG])
  · have := dec_dykRes hXr
    simp only [nu, sum3, goalW]
    omega

/-- **Opening a parked box**: the body enters the todo, paid for by the
box's own `+1`. -/
theorem boxOpen_lt {done rest : List Neg} {seen : List Pos} {R : Pos}
    {g g' : Option Neg} (hXr : (Neg.circ R, rest) ∈ splits done)
    (hgcl : subG g' ⊆ subG g) (hg : goalW g' ≤ goalW g) :
    qMu ([Neg.up R], rest, g', seen) < qMu ([], done, g, seen) := by
  have hmemD : Neg.circ R ∈ done := splits_mem hXr
  refine qMu_lt_of_ordinary ?_ rfl ?_
  · intro x hx
    rcases mem_clSt.mp hx with hx | hx | hx
    · refine mem_clSt.mpr (Or.inr (Or.inl ?_))
      obtain ⟨M, hM, hxM⟩ := mem_subL_iff.mp hx
      rcases List.mem_singleton.mp hM with rfl
      exact mem_subL hmemD (subP_sub_subN_circ R (subN_up_sub R hxM))
    · exact mem_clSt.mpr (Or.inr (Or.inl (subL_mono (splits_rest hXr) hx)))
    · exact mem_clSt.mpr (Or.inr (Or.inr (hgcl hx)))
  · have := dec_boxE hXr
    simp only [nu, sum3, wNeg]
    omega

/-- **A goal move at a fixed station**: the lax prefix, the `∨`-goal
disjuncts, the `↑↓`-goal and the `∧`-goal. -/
theorem goalMove_lt {done : List Neg} {g g' : Option Neg} {seen : List Pos}
    (hcl : subG g' ⊆ clSt (([] : List Neg), done, g, seen))
    (hlt : goalW g' < goalW g) :
    qMu (([] : List Neg), done, g', seen) < qMu ([], done, g, seen) := by
  refine qMu_lt_of_ordinary ?_ rfl ?_
  · intro x hx
    rcases mem_clSt.mp hx with hx | hx | hx
    · simp [subL_nil] at hx
    · exact mem_clSt.mpr (Or.inr (Or.inl hx))
    · exact hcl hx
  · simp only [nu, sum3]; omega

/-- **The `∀p` implication goal**: `invertPos Q` moves branches INTO the
station — the growth that refuted the per-station reset policy — and the
closure still does not grow, because the branches are subformulas of the
goal. -/
theorem impGoal_lt {done b : List Neg} {Q : Pos} {N : Neg} {g' : Option Neg}
    {seen : List Pos} (hb : b ∈ invertPos Q)
    (hgcl : subG g' ⊆ subN (Neg.imp Q N)) (hg : goalW g' ≤ 3 ^ wNeg N) :
    qMu (b, done, g', seen) < qMu ([], done, some (.imp Q N), seen) := by
  refine qMu_lt_of_ordinary ?_ rfl ?_
  · intro x hx
    rcases mem_clSt.mp hx with hx | hx | hx
    · exact mem_clSt.mpr (Or.inr (Or.inr
        (mem_subG_some.mpr (subP_sub_subN_imp Q N (subL_invert hb hx)))))
    · exact mem_clSt.mpr (Or.inr (Or.inl hx))
    · exact mem_clSt.mpr (Or.inr (Or.inr (mem_subG_some.mpr (hgcl hx))))
  · have hd := dec_ainv (Q := Q) (b := b) (N := N) (d := sum3 done) hb
    show 2 * sum3 b + sum3 done + goalW g'
       < 2 * sum3 ([] : List Neg) + sum3 done + 3 ^ wNeg (Neg.imp Q N)
    exact Nat.lt_of_le_of_lt (Nat.add_le_add_left hg _) hd

/-! ## The processing edges -/

/-- **Parking**: a hypothesis moves from the doubled side to the single one. -/
theorem park_lt {X : Neg} {todo done : List Neg} {g : Option Neg} {seen : List Pos} :
    qMu (todo, X :: done, g, seen) < qMu (X :: todo, done, g, seen) := by
  refine qMu_lt_of_ordinary ?_ rfl ?_
  · intro x hx
    rcases mem_clSt.mp hx with hx | hx | hx
    · exact mem_clSt.mpr (Or.inl (mem_subL_cons.mpr (Or.inr hx)))
    · rcases mem_subL_cons.mp hx with hx | hx
      · exact mem_clSt.mpr (Or.inl (mem_subL_cons.mpr (Or.inl hx)))
      · exact mem_clSt.mpr (Or.inr (Or.inl hx))
    · exact mem_clSt.mpr (Or.inr (Or.inr hx))
  · have := p3_pos (wNeg X)
    simp only [nu, sum3]
    omega

/-- **An inert hypothesis** `⊥ ⊃ N` is dropped. -/
theorem drop_lt {X : Neg} {todo done : List Neg} {g : Option Neg} {seen : List Pos} :
    qMu (todo, done, g, seen) < qMu (X :: todo, done, g, seen) := by
  refine qMu_lt_of_ordinary ?_ rfl ?_
  · intro x hx
    rcases mem_clSt.mp hx with hx | hx | hx
    · exact mem_clSt.mpr (Or.inl (mem_subL_cons.mpr (Or.inr hx)))
    · exact mem_clSt.mpr (Or.inr (Or.inl hx))
    · exact mem_clSt.mpr (Or.inr (Or.inr hx))
  · have := p3_pos (wNeg X)
    simp only [nu, sum3]
    omega

/-- **A processing replacement**: the head of `todo` becomes strictly
lighter material drawn from its own closure. -/
theorem todoRepl_lt {X : Neg} {r todo done : List Neg} {g g' : Option Neg}
    {seen : List Pos} (hcl : subL r ⊆ subN X) (hgcl : subG g' ⊆ subG g)
    (hg : goalW g' ≤ goalW g) (hlt : sum3 r < 3 ^ wNeg X) :
    qMu (r ++ todo, done, g', seen) < qMu (X :: todo, done, g, seen) := by
  refine qMu_lt_of_ordinary ?_ rfl ?_
  · intro x hx
    rcases mem_clSt.mp hx with hx | hx | hx
    · rw [subL_append] at hx
      rcases List.mem_append.mp hx with hx | hx
      · exact mem_clSt.mpr (Or.inl (mem_subL_cons.mpr (Or.inl (hcl hx))))
      · exact mem_clSt.mpr (Or.inl (mem_subL_cons.mpr (Or.inr hx)))
    · exact mem_clSt.mpr (Or.inr (Or.inl hx))
    · exact mem_clSt.mpr (Or.inr (Or.inr (hgcl hx)))
  · simp only [nu, sum3_append, sum3]
    omega

/-! # Part 4 · The row maps descend -/

theorem parkEdgesE_decrease {done rest res : List Neg} {Qa : Pos} {N : Neg}
    {seen : List Pos} (hXr : (Neg.imp Qa N, rest) ∈ splits done)
    (hres : qMu (res, rest, none, seen) < qMu ([], done, none, seen)) :
    ∀ t ∈ parkEdgesE done Qa N rest res seen, qMu t < qMu ([], done, none, seen) := by
  intro t ht
  simp only [parkEdgesE, List.mem_append] at ht
  rcases ht with ht | ht
  · by_cases hm : seenMem seen Qa = true
    · simp [hm] at ht
    · simp only [Bool.not_eq_true] at hm
      simp only [hm, Bool.false_eq_true, if_false, List.mem_cons,
        List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · exact guard_lt hXr hm
      · exact parkSecond_lt hXr
  · rcases List.mem_singleton.mp ht with rfl
    exact hres

theorem parkEdgesA_decrease {done rest : List Neg} {Qa : Pos} {N goal : Neg}
    {seen : List Pos} (hXr : (Neg.imp Qa N, rest) ∈ splits done) :
    ∀ t ∈ parkEdgesA done Qa N rest goal seen,
      qMu t < qMu ([], done, some goal, seen) := by
  intro t ht
  by_cases hm : seenMem seen Qa = true
  · simp [parkEdgesA, hm] at ht
  · simp only [Bool.not_eq_true] at hm
    simp only [parkEdgesA, hm, Bool.false_eq_true, if_false, List.mem_cons,
      List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact guard_lt hXr hm
    · exact parkSecond_lt hXr

theorem eRowEdges_decrease {done : List Neg} {seen : List Pos} :
    ∀ t ∈ eRowEdges done seen, qMu t < qMu (([] : List Neg), done, none, seen) := by
  intro t ht
  obtain ⟨⟨X, rest⟩, hXr, ht⟩ := List.mem_flatMap.mp ht
  simp only at ht
  match X with
  | .up (.atom a) => simp [eRowBody] at ht
  | .imp (.atom a) N =>
      rw [show eRowBody done seen (Neg.imp (.atom a) N) rest
            = [(([N] : List Neg), rest, (none : Option Neg), seen)] from rfl] at ht
      rcases List.mem_singleton.mp ht with rfl
      exact parkSecond_lt hXr
  | .imp (.down (.imp Q' N')) N =>
      exact parkEdgesE_decrease hXr (dykRes_lt hXr) t ht
  | .circ Q =>
      rw [show eRowBody done seen (Neg.circ Q) rest
            = [(([Neg.up Q] : List Neg), rest, (none : Option Neg), seen)] from rfl] at ht
      rcases List.mem_singleton.mp ht with rfl
      exact boxOpen_lt hXr (fun _ h => h) (Nat.le_refl _)
  | .imp (.down (.circ Q')) N => exact parkEdgesE_decrease hXr (parkRes_lt hXr) t ht
  | .imp (.or Qa Qb) N => exact parkEdgesE_decrease hXr (parkRes_lt hXr) t ht
  | .imp (.down (.up Pa)) N => exact parkEdgesE_decrease hXr (parkRes_lt hXr) t ht
  | .imp (.down (.and Ma Mb)) N => exact parkEdgesE_decrease hXr (parkRes_lt hXr) t ht
  | .up .fls | .up (.or _ _) | .up (.down _) | .imp .fls _ | .and _ _ =>
      simp [eRowBody] at ht

theorem aRowEdges_decrease {done : List Neg} {goal : Neg} {box : Bool}
    {seen : List Pos} :
    ∀ t ∈ aRowEdges done goal box seen, qMu t < qMu (([] : List Neg), done, some goal, seen) := by
  intro t ht
  obtain ⟨⟨X, rest⟩, hXr, ht⟩ := List.mem_flatMap.mp ht
  simp only at ht
  match X with
  | .imp (.atom a) N =>
      rw [show aRowBody done goal box seen (Neg.imp (.atom a) N) rest
            = [(([N] : List Neg), rest, some goal, seen)] from rfl] at ht
      rcases List.mem_singleton.mp ht with rfl
      exact parkSecond_lt hXr
  | .imp (.down (.imp Q' N')) N => exact parkEdgesA_decrease hXr t ht
  | .imp (.down (.circ Q')) N => exact parkEdgesA_decrease hXr t ht
  | .imp (.or Qa Qb) N => exact parkEdgesA_decrease hXr t ht
  | .imp (.down (.up Pa)) N => exact parkEdgesA_decrease hXr t ht
  | .imp (.down (.and Ma Mb)) N => exact parkEdgesA_decrease hXr t ht
  | .circ R =>
      rw [show aRowBody done goal box seen (Neg.circ R) rest
            = (if box then [(([Neg.up R] : List Neg), rest, (none : Option Neg), seen),
                            ([Neg.up R], rest, some goal, seen)] else []) from rfl] at ht
      by_cases hb : box = true
      · simp only [hb, if_true, List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl
        · exact boxOpen_lt hXr (by simp [subG]) (by simp [goalW])
        · exact boxOpen_lt hXr (fun _ h => h) (Nat.le_refl _)
      · simp only [Bool.not_eq_true] at hb
        simp [hb] at ht
  | .up (.atom _) | .up .fls | .up (.or _ _) | .up (.down _) | .imp .fls _
  | .and _ _ => simp [aRowBody] at ht

theorem laxEdges_decrease {done : List Neg} {seen : List Pos} {Q : Pos} :
    ∀ t ∈ laxEdges done seen Q,
      qMu t < qMu (([] : List Neg), done, some (.circ Q), seen) := by
  intro t ht
  match Q with
  | .atom q =>
      simp only [laxEdges, List.mem_singleton] at ht
      rcases ht with rfl
      refine goalMove_lt ?_ ?_
      · intro x hx
        exact mem_clSt.mpr (Or.inr (Or.inr
          (mem_subG_some.mpr (subP_sub_subN_circ _ (subN_up_sub _ (mem_subG_some.mp hx))))))
      · simp only [goalW, wNeg, wPos]; exact p3_strict (by omega)
  | .fls =>
      simp only [laxEdges, List.mem_singleton] at ht
      rcases ht with rfl
      refine goalMove_lt ?_ ?_
      · intro x hx
        exact mem_clSt.mpr (Or.inr (Or.inr
          (mem_subG_some.mpr (subP_sub_subN_circ _ (subN_up_sub _ (mem_subG_some.mp hx))))))
      · simp only [goalW, wNeg, wPos]; exact p3_strict (by omega)
  | .or P₁ P₂ =>
      simp only [laxEdges, List.mem_cons, List.not_mem_nil, or_false] at ht
      have hP₁ := wPos_pos P₁
      have hP₂ := wPos_pos P₂
      rcases ht with rfl | rfl | rfl
      · refine goalMove_lt ?_ ?_
        · intro x hx
          refine mem_clSt.mpr (Or.inr (Or.inr (mem_subG_some.mpr ?_)))
          exact subP_sub_subN_circ _ (subP_or_left P₁ P₂ (subN_circ_sub P₁ (mem_subG_some.mp hx)))
        · simp only [goalW, wNeg, wPos]; exact p3_strict (by omega)
      · refine goalMove_lt ?_ ?_
        · intro x hx
          refine mem_clSt.mpr (Or.inr (Or.inr (mem_subG_some.mpr ?_)))
          exact subP_sub_subN_circ _ (subP_or_right P₁ P₂ (subN_circ_sub P₂ (mem_subG_some.mp hx)))
        · simp only [goalW, wNeg, wPos]; exact p3_strict (by omega)
      · refine goalMove_lt ?_ ?_
        · intro x hx
          exact mem_clSt.mpr (Or.inr (Or.inr (mem_subG_some.mpr
            (subP_sub_subN_circ _ (subN_up_sub _ (mem_subG_some.mp hx))))))
        · simp only [goalW, wNeg, wPos]; exact p3_strict (by omega)
  | .down (.up P') =>
      simp only [laxEdges, List.mem_singleton] at ht
      rcases ht with rfl
      refine goalMove_lt ?_ ?_
      · intro x hx
        refine mem_clSt.mpr (Or.inr (Or.inr (mem_subG_some.mpr ?_)))
        refine subP_sub_subN_circ _ ?_
        refine subN_sub_subP_down _ ?_
        exact subP_sub_subN_up P' (subN_circ_sub P' (mem_subG_some.mp hx))
      · simp only [goalW, wNeg, wPos]; exact p3_strict (by omega)
  | .down (.circ P') =>
      simp only [laxEdges, List.mem_singleton] at ht
      rcases ht with rfl
      refine goalMove_lt ?_ ?_
      · intro x hx
        refine mem_clSt.mpr (Or.inr (Or.inr (mem_subG_some.mpr ?_)))
        refine subP_sub_subN_circ _ ?_
        exact subN_sub_subP_down _ (mem_subG_some.mp hx)
      · simp only [goalW, wNeg, wPos]; exact p3_strict (by omega)
  | .down (.and M₁ M₂) =>
      simp only [laxEdges, List.mem_singleton] at ht
      rcases ht with rfl
      refine goalMove_lt ?_ ?_
      · intro x hx
        exact mem_clSt.mpr (Or.inr (Or.inr (mem_subG_some.mpr
          (subP_sub_subN_circ _ (subN_up_sub _ (mem_subG_some.mp hx))))))
      · simp only [goalW, wNeg]; exact p3_strict (by omega)
  | .down (.imp Q₀ N₀) =>
      simp only [laxEdges, List.mem_singleton] at ht
      rcases ht with rfl
      refine goalMove_lt ?_ ?_
      · intro x hx
        exact mem_clSt.mpr (Or.inr (Or.inr (mem_subG_some.mpr
          (subP_sub_subN_circ _ (subN_up_sub _ (mem_subG_some.mp hx))))))
      · simp only [goalW, wNeg]; exact p3_strict (by omega)

theorem aggEdges_decrease {done : List Neg} {g : Option Neg} {seen : List Pos} :
    ∀ t ∈ aggEdges done g seen, qMu t < qMu (([] : List Neg), done, g, seen) := by
  intro t ht
  match g with
  | none => exact eRowEdges_decrease t ht
  | some (.imp Q N) =>
      simp only [aggEdges] at ht
      obtain ⟨b, hb, ht⟩ := List.mem_flatMap.mp ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · exact impGoal_lt hb (by simp [subG]) (by simp [goalW])
      · exact impGoal_lt hb (subN_con_sub_imp Q N) (Nat.le_refl _)
  | some (.and M N) =>
      simp only [aggEdges, List.mem_cons, List.not_mem_nil, or_false] at ht
      have h1 := wNeg_pos M
      have h2 := wNeg_pos N
      rcases ht with rfl | rfl
      · refine goalMove_lt ?_ ?_
        · intro x hx
          refine mem_clSt.mpr (Or.inr (Or.inr (mem_subG_some.mpr ?_)))
          rw [subN_and]
          exact List.mem_cons_of_mem _
            (List.mem_append.mpr (Or.inl (mem_subG_some.mp hx)))
        · simp only [goalW, wNeg]; exact p3_strict (by omega)
      · refine goalMove_lt ?_ ?_
        · intro x hx
          refine mem_clSt.mpr (Or.inr (Or.inr (mem_subG_some.mpr ?_)))
          rw [subN_and]
          exact List.mem_cons_of_mem _
            (List.mem_append.mpr (Or.inr (mem_subG_some.mp hx)))
        · simp only [goalW, wNeg]; exact p3_strict (by omega)
  | some (.up (.atom q)) =>
      simp only [aggEdges] at ht
      by_cases ha : atomMem q done = true
      · simp [ha] at ht
      · simp only [Bool.not_eq_true] at ha
        simp only [ha, Bool.false_eq_true, if_false] at ht
        exact aRowEdges_decrease t ht
  | some (.up .fls) =>
      simp only [aggEdges] at ht
      exact aRowEdges_decrease t ht
  | some (.up (.or P₁ P₂)) =>
      simp only [aggEdges, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false] at ht
      have h1 := wPos_pos P₁
      have h2 := wPos_pos P₂
      rcases ht with (rfl | rfl) | ht
      · refine goalMove_lt ?_ ?_
        · intro x hx
          refine mem_clSt.mpr (Or.inr (Or.inr (mem_subG_some.mpr ?_)))
          exact subP_sub_subN_up _ (subP_or_left P₁ P₂ (subN_up_sub P₁ (mem_subG_some.mp hx)))
        · simp only [goalW, wNeg, wPos]; exact p3_strict (by omega)
      · refine goalMove_lt ?_ ?_
        · intro x hx
          refine mem_clSt.mpr (Or.inr (Or.inr (mem_subG_some.mpr ?_)))
          exact subP_sub_subN_up _ (subP_or_right P₁ P₂ (subN_up_sub P₂ (mem_subG_some.mp hx)))
        · simp only [goalW, wNeg, wPos]; exact p3_strict (by omega)
      · exact aRowEdges_decrease t ht
  | some (.up (.down M)) =>
      simp only [aggEdges, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false] at ht
      rcases ht with rfl | ht
      · refine goalMove_lt ?_ ?_
        · intro x hx
          refine mem_clSt.mpr (Or.inr (Or.inr (mem_subG_some.mpr ?_)))
          exact subP_sub_subN_up _ (subN_sub_subP_down M (mem_subG_some.mp hx))
        · simp only [goalW, wNeg, wPos]; exact p3_strict (by omega)
      · exact aRowEdges_decrease t ht
  | some (.circ Q) =>
      simp only [aggEdges, List.mem_append] at ht
      rcases ht with ht | ht
      · exact laxEdges_decrease t ht
      · exact aRowEdges_decrease t ht

/-! # Part 5 · The descent, the founding, and the bound -/

/-- **Every state the step consults has strictly smaller `qMu`.** -/
theorem edges_decrease (s : QState) : ∀ t ∈ edgesQ s, qMu t < qMu s := by
  obtain ⟨todo, done, g, seen⟩ := s
  match todo, g with
  | [], g =>
      intro t ht
      simp only [edgesQ] at ht
      split at ht
      · rename_i a N rest hf
        rcases List.mem_singleton.mp ht with rfl
        exact parkSecond_lt (findFire_mem hf)
      · exact aggEdges_decrease t ht
  | .up (.atom a) :: todo, g =>
      intro t ht
      simp only [edgesQ, List.mem_singleton] at ht
      rcases ht with rfl
      exact park_lt
  | .up .fls :: todo, none => intro t ht; simp [edgesQ] at ht
  | .up .fls :: todo, some G => intro t ht; simp [edgesQ] at ht
  | .up (.or P Q) :: todo, none =>
      intro t ht
      simp only [edgesQ, List.mem_map] at ht
      obtain ⟨b, hb, rfl⟩ := ht
      refine todoRepl_lt ?_ (fun _ h => h) (Nat.le_refl _) ?_
      · exact fun x hx => subP_sub_subN_up _ (subL_invert hb hx)
      · have := invertPos_lt (P := Pos.or P Q) (fun a h => Pos.noConfusion h) b hb
        simpa [wNeg] using this
  | .up (.or P Q) :: todo, some G =>
      intro t ht
      simp only [edgesQ] at ht
      obtain ⟨b, hb, ht⟩ := List.mem_flatMap.mp ht
      have hcl : subL b ⊆ subN (Neg.up (.or P Q)) :=
        fun x hx => subP_sub_subN_up _ (subL_invert hb hx)
      have hlt : sum3 b < 3 ^ wNeg (Neg.up (Pos.or P Q)) := by
        have := invertPos_lt (P := Pos.or P Q) (fun a h => Pos.noConfusion h) b hb
        simpa [wNeg] using this
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · exact todoRepl_lt hcl (by simp [subG]) (by simp [goalW]) hlt
      · exact todoRepl_lt hcl (fun _ h => h) (Nat.le_refl _) hlt
  | .up (.down M) :: todo, g =>
      intro t ht
      simp only [edgesQ, List.mem_singleton] at ht
      rcases ht with rfl
      have : ([M] : List Neg) ++ todo = M :: todo := rfl
      rw [← this]
      refine todoRepl_lt ?_ (fun _ h => h) (Nat.le_refl _) ?_
      · intro x hx
        obtain ⟨M', hM', hxM⟩ := mem_subL_iff.mp hx
        rcases List.mem_singleton.mp hM' with rfl
        exact subP_sub_subN_up _ (subN_sub_subP_down _ hxM)
      · simp only [sum3, wNeg, wPos]
        have := p3_strict (a := wNeg M) (b := wNeg M + 1) (by omega)
        omega
  | .and M N :: todo, g =>
      intro t ht
      simp only [edgesQ, List.mem_singleton] at ht
      rcases ht with rfl
      have : ([M, N] : List Neg) ++ todo = M :: N :: todo := rfl
      rw [← this]
      refine todoRepl_lt ?_ (fun _ h => h) (Nat.le_refl _) ?_
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
      simp only [edgesQ, List.mem_singleton] at ht
      rcases ht with rfl
      exact drop_lt
  | .imp (.atom a) N :: todo, g =>
      intro t ht
      simp only [edgesQ, List.mem_singleton] at ht
      rcases ht with rfl
      exact park_lt
  | .imp (.or Q₁ Q₂) N :: todo, g =>
      intro t ht
      simp only [edgesQ, List.mem_singleton] at ht
      rcases ht with rfl
      exact park_lt
  | .imp (.down (.up P')) N :: todo, g =>
      intro t ht
      simp only [edgesQ, List.mem_singleton] at ht
      rcases ht with rfl
      exact park_lt
  | .imp (.down (.and M₁ M₂)) N :: todo, g =>
      intro t ht
      simp only [edgesQ, List.mem_singleton] at ht
      rcases ht with rfl
      exact park_lt
  | .imp (.down (.imp Q' N')) N :: todo, g =>
      intro t ht
      simp only [edgesQ, List.mem_singleton] at ht
      rcases ht with rfl
      exact park_lt
  | .circ Q :: todo, g =>
      intro t ht
      simp only [edgesQ, List.mem_singleton] at ht
      rcases ht with rfl
      exact park_lt
  | .imp (.down (.circ Q')) N :: todo, g =>
      intro t ht
      simp only [edgesQ, List.mem_singleton] at ht
      rcases ht with rfl
      exact park_lt

/-- **`qMu` founds the loop-checked recursion.** -/
theorem qFounded (p : String) : QFounded id p qMu := by
  intro prev₁ prev₂ s h
  exact stepQ_congr s (fun t ht => h t (edges_decrease s t ht))

/-- **The measure obligation is discharged.** -/
def qBound (p : String) : QBound p := ⟨qMu, qFounded p⟩

/-! # Part 6 · N4 over the single remaining obligation -/

/-- Literal stabilisation of the loop-checked `∃p` chain, unconditionally. -/
def qStabLitE_uncond (p : String) (done : List Neg) : QStabLitE p done :=
  qStabLitE_of_bound (qBound p) done

/-- Literal stabilisation of the loop-checked `∀p` chain, unconditionally. -/
def qStabLitA_uncond (p : String) (done : List Neg) (G : Neg) : QStabLitA p done G :=
  qStabLitA_of_bound (qBound p) done G

/-- **N4 for PLL over `PQEquiv` alone.**  The measure obligation of
`docs/n4-loopcheck.md` §7 is gone. -/
noncomputable def n4_of_pqequiv {p : String} (eq : PQEquiv p)
    (done : List Neg) (G : Neg) : EStabilises p done × AStabilises p done G :=
  n4_of_interpQ eq (qBound p) done G

/-- **The uniform-interpolant pair over `PQEquiv` alone**, at a saturated
parked station, over the cofinality statements as variables. -/
noncomputable def hasUI_of_pqequiv {p : String} (s2 : SatE2P p) (a2 : SatA2P p)
    (eq : PQEquiv p) {done : List Neg} {G : Neg}
    (hsat : Saturated done) (hpk : ParkedCtxP done) : HasUI p done G :=
  hasUI_of_interpQ s2 a2 eq (qBound p) hsat hpk

end LJFO

/-! ## Pins -/

#axioms_within LJFO.edges_decrease [propext, Quot.sound]
#axioms_within LJFO.qFounded [propext, Quot.sound]
#axioms_within LJFO.qBound [propext, Quot.sound]
#axioms_within LJFO.qStabLitE_uncond [propext, Quot.sound]
#axioms_within LJFO.qStabLitA_uncond [propext, Quot.sound]
#axioms_within LJFO.n4_of_pqequiv [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.hasUI_of_pqequiv [propext, Classical.choice, Quot.sound]
