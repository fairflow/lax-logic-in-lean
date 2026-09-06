/-
Route (B), node **N4**, WP9, part B: **the mirror is complete.**

`edgesQ s` (`wip/ui_routeB_n4q_meas.lean`) lists the states `stepQ id p prev`
reads `prev` at.  This module proves that it lists ENOUGH of them:

    stepQ_congr : (∀ t ∈ edgesQ s, atSt prev₁ t = atSt prev₂ t) →
                  atSt (stepQ id p prev₁) s = atSt (stepQ id p prev₂) s

— one congruence lemma per row function, then one match over the clauses of
`stepQ`, exactly the shape of `pfree_stepQ`.  Nothing here mentions the
measure; the descent is `wip/ui_routeB_n4q_bound.lean`.
-/
import wip.ui_routeB_n4q_clos
import Meta.Audit

set_option autoImplicit false

namespace LJFO

/-- Reading an approximant at a written-out state. -/
theorem atSt_mk (F : List Neg → List Neg → Option Neg → List Pos → Neg)
    (todo done : List Neg) (g : Option Neg) (seen : List Pos) :
    atSt F (todo, done, g, seen) = F todo done g seen := rfl

section
variable {p : String} {prev₁ prev₂ : ApproxQ}

/-! # Part 1 · The parked-implication rows -/

theorem parkRowE_congr {done : List Neg} {Qa : Pos} {N : Neg} {rest res : List Neg}
    {seen : List Pos}
    (h : ∀ t ∈ parkEdgesE done Qa N rest res seen, atSt prev₁ t = atSt prev₂ t) :
    parkRowE id prev₁ done Qa N rest res seen
      = parkRowE id prev₂ done Qa N rest res seen := by
  have hres : prev₁ res rest none (id seen) = prev₂ res rest none (id seen) :=
    h (res, rest, none, seen) (by simp [parkEdgesE])
  by_cases hm : seenMem seen Qa = true
  · simp only [parkRowE, hm, if_true]
    rw [hres]
  · simp only [Bool.not_eq_true] at hm
    have h1 : prev₁ [] done (some (.up Qa)) (Qa :: seen)
            = prev₂ [] done (some (.up Qa)) (Qa :: seen) :=
      h ([], done, some (.up Qa), Qa :: seen) (by simp [parkEdgesE, hm])
    have h2 : prev₁ [N] rest none (id seen) = prev₂ [N] rest none (id seen) :=
      h ([N], rest, none, seen) (by simp [parkEdgesE, hm])
    simp only [parkRowE, hm, Bool.false_eq_true, if_false]
    rw [h1, h2, hres]

theorem parkRowA_congr {done : List Neg} {Qa : Pos} {N : Neg} {rest : List Neg}
    {goal : Neg} {seen : List Pos}
    (h : ∀ t ∈ parkEdgesA done Qa N rest goal seen, atSt prev₁ t = atSt prev₂ t) :
    parkRowA id prev₁ done Qa N rest goal seen
      = parkRowA id prev₂ done Qa N rest goal seen := by
  by_cases hm : seenMem seen Qa = true
  · simp only [parkRowA, hm, if_true]
  · simp only [Bool.not_eq_true] at hm
    have h1 : prev₁ [] done (some (.up Qa)) (Qa :: seen)
            = prev₂ [] done (some (.up Qa)) (Qa :: seen) :=
      h ([], done, some (.up Qa), Qa :: seen) (by simp [parkEdgesA, hm])
    have h2 : prev₁ [N] rest (some goal) (id seen)
            = prev₂ [N] rest (some goal) (id seen) :=
      h ([N], rest, some goal, seen) (by simp [parkEdgesA, hm])
    simp only [parkRowA, hm, Bool.false_eq_true, if_false]
    rw [h1, h2]

/-! # Part 2 · The row maps -/

theorem eRowsQ_congr {done : List Neg} {seen : List Pos}
    (h : ∀ t ∈ eRowEdges done seen, atSt prev₁ t = atSt prev₂ t) :
    eRowsQ id p prev₁ done seen = eRowsQ id p prev₂ done seen := by
  simp only [eRowsQ]
  refine List.map_congr_left ?_
  rintro ⟨X, rest⟩ hXr
  have hb : ∀ t ∈ eRowBody done seen X rest, atSt prev₁ t = atSt prev₂ t :=
    fun t ht => h t (List.mem_flatMap.mpr ⟨(X, rest), hXr, ht⟩)
  match X with
  | .up (.atom a) => rfl
  | .imp (.atom a) N =>
      have hx : prev₁ [N] rest none (id seen) = prev₂ [N] rest none (id seen) :=
        hb ([N], rest, none, seen) (by simp [eRowBody])
      show pGuard p a nTop (.imp (.atom a) (prev₁ [N] rest none (id seen)))
         = pGuard p a nTop (.imp (.atom a) (prev₂ [N] rest none (id seen)))
      rw [hx]
  | .imp (.down (.imp Q' N')) N =>
      exact parkRowE_congr (fun t ht => hb t (by simpa [eRowBody] using ht))
  | .circ Q =>
      have hx : prev₁ [Neg.up Q] rest none (id seen)
              = prev₂ [Neg.up Q] rest none (id seen) :=
        hb ([Neg.up Q], rest, none, seen) (by simp [eRowBody])
      show Neg.circ (.down (prev₁ [Neg.up Q] rest none (id seen)))
         = Neg.circ (.down (prev₂ [Neg.up Q] rest none (id seen)))
      rw [hx]
  | .imp (.down (.circ Q')) N =>
      exact parkRowE_congr (fun t ht => hb t (by simpa [eRowBody] using ht))
  | .imp (.or Qa Qb) N =>
      exact parkRowE_congr (fun t ht => hb t (by simpa [eRowBody] using ht))
  | .imp (.down (.up Pa)) N =>
      exact parkRowE_congr (fun t ht => hb t (by simpa [eRowBody] using ht))
  | .imp (.down (.and Ma Mb)) N =>
      exact parkRowE_congr (fun t ht => hb t (by simpa [eRowBody] using ht))
  | .up .fls | .up (.or _ _) | .up (.down _) | .imp .fls _ | .and _ _ => rfl

theorem aRowsQ_congr {done : List Neg} {goal : Neg} {box : Bool} {seen : List Pos}
    (h : ∀ t ∈ aRowEdges done goal box seen, atSt prev₁ t = atSt prev₂ t) :
    aRowsQ id p prev₁ done goal box seen = aRowsQ id p prev₂ done goal box seen := by
  simp only [aRowsQ]
  refine List.map_congr_left ?_
  rintro ⟨X, rest⟩ hXr
  have hb : ∀ t ∈ aRowBody done goal box seen X rest, atSt prev₁ t = atSt prev₂ t :=
    fun t ht => h t (List.mem_flatMap.mpr ⟨(X, rest), hXr, ht⟩)
  match X with
  | .imp (.atom a) N =>
      have hx : prev₁ [N] rest (some goal) (id seen)
              = prev₂ [N] rest (some goal) (id seen) :=
        hb ([N], rest, some goal, seen) (by simp [aRowBody])
      show pGuard p a nBot (nAnd (.up (.atom a)) (prev₁ [N] rest (some goal) (id seen)))
         = pGuard p a nBot (nAnd (.up (.atom a)) (prev₂ [N] rest (some goal) (id seen)))
      rw [hx]
  | .imp (.down (.imp Q' N')) N =>
      exact parkRowA_congr (fun t ht => hb t (by simpa [aRowBody] using ht))
  | .imp (.down (.circ Q')) N =>
      exact parkRowA_congr (fun t ht => hb t (by simpa [aRowBody] using ht))
  | .imp (.or Qa Qb) N =>
      exact parkRowA_congr (fun t ht => hb t (by simpa [aRowBody] using ht))
  | .imp (.down (.up Pa)) N =>
      exact parkRowA_congr (fun t ht => hb t (by simpa [aRowBody] using ht))
  | .imp (.down (.and Ma Mb)) N =>
      exact parkRowA_congr (fun t ht => hb t (by simpa [aRowBody] using ht))
  | .circ R =>
      by_cases hbx : box = true
      · have h1 : prev₁ [Neg.up R] rest none (id seen)
                = prev₂ [Neg.up R] rest none (id seen) :=
          hb ([Neg.up R], rest, none, seen) (by simp [aRowBody, hbx])
        have h2 : prev₁ [Neg.up R] rest (some goal) (id seen)
                = prev₂ [Neg.up R] rest (some goal) (id seen) :=
          hb ([Neg.up R], rest, some goal, seen) (by simp [aRowBody, hbx])
        show (if box then Neg.imp (.down (prev₁ [Neg.up R] rest none (id seen)))
                (prev₁ [Neg.up R] rest (some goal) (id seen)) else nBot)
           = (if box then Neg.imp (.down (prev₂ [Neg.up R] rest none (id seen)))
                (prev₂ [Neg.up R] rest (some goal) (id seen)) else nBot)
        rw [h1, h2]
      · simp only [Bool.not_eq_true] at hbx
        show (if box then Neg.imp (.down (prev₁ [Neg.up R] rest none (id seen)))
                (prev₁ [Neg.up R] rest (some goal) (id seen)) else nBot)
           = (if box then Neg.imp (.down (prev₂ [Neg.up R] rest none (id seen)))
                (prev₂ [Neg.up R] rest (some goal) (id seen)) else nBot)
        simp only [hbx, Bool.false_eq_true, if_false]
  | .up (.atom _) | .up .fls | .up (.or _ _) | .up (.down _) | .imp .fls _
  | .and _ _ => rfl

theorem laxPrefixQ_congr {done : List Neg} {seen : List Pos} {Q : Pos}
    (h : ∀ t ∈ laxEdges done seen Q, atSt prev₁ t = atSt prev₂ t) :
    laxPrefixQ prev₁ done seen Q = laxPrefixQ prev₂ done seen Q := by
  match Q with
  | .atom q =>
      have h1 : prev₁ [] done (some (.up (.atom q))) seen
              = prev₂ [] done (some (.up (.atom q))) seen :=
        h ([], done, some (.up (.atom q)), seen) (by simp [laxEdges])
      show [prev₁ [] done (some (.up (.atom q))) seen]
         = [prev₂ [] done (some (.up (.atom q))) seen]
      rw [h1]
  | .fls =>
      have h1 : prev₁ [] done (some (.up .fls)) seen
              = prev₂ [] done (some (.up .fls)) seen :=
        h ([], done, some (.up .fls), seen) (by simp [laxEdges])
      show [prev₁ [] done (some (.up .fls)) seen] = [prev₂ [] done (some (.up .fls)) seen]
      rw [h1]
  | .or P₁ P₂ =>
      have h1 : prev₁ [] done (some (.circ P₁)) seen
              = prev₂ [] done (some (.circ P₁)) seen :=
        h ([], done, some (.circ P₁), seen) (by simp [laxEdges])
      have h2 : prev₁ [] done (some (.circ P₂)) seen
              = prev₂ [] done (some (.circ P₂)) seen :=
        h ([], done, some (.circ P₂), seen) (by simp [laxEdges])
      have h3 : prev₁ [] done (some (.up (.or P₁ P₂))) seen
              = prev₂ [] done (some (.up (.or P₁ P₂))) seen :=
        h ([], done, some (.up (.or P₁ P₂)), seen) (by simp [laxEdges])
      show [prev₁ [] done (some (.circ P₁)) seen, prev₁ [] done (some (.circ P₂)) seen,
            prev₁ [] done (some (.up (.or P₁ P₂))) seen]
         = [prev₂ [] done (some (.circ P₁)) seen, prev₂ [] done (some (.circ P₂)) seen,
            prev₂ [] done (some (.up (.or P₁ P₂))) seen]
      rw [h1, h2, h3]
  | .down (.up P') =>
      have h1 : prev₁ [] done (some (.circ P')) seen
              = prev₂ [] done (some (.circ P')) seen :=
        h ([], done, some (.circ P'), seen) (by simp [laxEdges])
      show [prev₁ [] done (some (.circ P')) seen] = [prev₂ [] done (some (.circ P')) seen]
      rw [h1]
  | .down (.circ P') =>
      have h1 : prev₁ [] done (some (.circ P')) seen
              = prev₂ [] done (some (.circ P')) seen :=
        h ([], done, some (.circ P'), seen) (by simp [laxEdges])
      show [prev₁ [] done (some (.circ P')) seen] = [prev₂ [] done (some (.circ P')) seen]
      rw [h1]
  | .down (.and M₁ M₂) =>
      have h1 : prev₁ [] done (some (.up (.down (.and M₁ M₂)))) seen
              = prev₂ [] done (some (.up (.down (.and M₁ M₂)))) seen :=
        h ([], done, some (.up (.down (.and M₁ M₂))), seen) (by simp [laxEdges])
      show [prev₁ [] done (some (.up (.down (.and M₁ M₂)))) seen]
         = [prev₂ [] done (some (.up (.down (.and M₁ M₂)))) seen]
      rw [h1]
  | .down (.imp Q₀ N₀) =>
      have h1 : prev₁ [] done (some (.up (.down (.imp Q₀ N₀)))) seen
              = prev₂ [] done (some (.up (.down (.imp Q₀ N₀)))) seen :=
        h ([], done, some (.up (.down (.imp Q₀ N₀))), seen) (by simp [laxEdges])
      show [prev₁ [] done (some (.up (.down (.imp Q₀ N₀)))) seen]
         = [prev₂ [] done (some (.up (.down (.imp Q₀ N₀)))) seen]
      rw [h1]

/-! # Part 3 · The aggregate and the step -/

theorem aggQ_congr {done : List Neg} {g : Option Neg} {seen : List Pos}
    (h : ∀ t ∈ aggEdges done g seen, atSt prev₁ t = atSt prev₂ t) :
    aggQ id p prev₁ done g seen = aggQ id p prev₂ done g seen := by
  match g with
  | none =>
      show nAndAll (eRowsQ id p prev₁ done seen) = nAndAll (eRowsQ id p prev₂ done seen)
      rw [eRowsQ_congr (fun t ht => h t (by simpa [aggEdges] using ht))]
  | some (.imp Q N) =>
      show nAndAll ((invertPos Q).map (fun b =>
             Neg.imp (.down (prev₁ b done none seen)) (prev₁ b done (some N) seen)))
         = nAndAll ((invertPos Q).map (fun b =>
             Neg.imp (.down (prev₂ b done none seen)) (prev₂ b done (some N) seen)))
      refine congrArg nAndAll (List.map_congr_left ?_)
      intro b hb
      have h1 : prev₁ b done none seen = prev₂ b done none seen :=
        h (b, done, none, seen)
          (by simp only [aggEdges]; exact List.mem_flatMap.mpr ⟨b, hb, by simp⟩)
      have h2 : prev₁ b done (some N) seen = prev₂ b done (some N) seen :=
        h (b, done, some N, seen)
          (by simp only [aggEdges]; exact List.mem_flatMap.mpr ⟨b, hb, by simp⟩)
      rw [h1, h2]
  | some (.and M N) =>
      have h1 : prev₁ [] done (some M) seen = prev₂ [] done (some M) seen :=
        h ([], done, some M, seen) (by simp [aggEdges])
      have h2 : prev₁ [] done (some N) seen = prev₂ [] done (some N) seen :=
        h ([], done, some N, seen) (by simp [aggEdges])
      show nAnd (prev₁ [] done (some M) seen) (prev₁ [] done (some N) seen)
         = nAnd (prev₂ [] done (some M) seen) (prev₂ [] done (some N) seen)
      rw [h1, h2]
  | some (.up (.atom q)) =>
      show (if atomMem q done then nTop
            else nOrAll (atomHead p q ++ aRowsQ id p prev₁ done (.up (.atom q)) false seen))
         = (if atomMem q done then nTop
            else nOrAll (atomHead p q ++ aRowsQ id p prev₂ done (.up (.atom q)) false seen))
      by_cases ha : atomMem q done = true
      · simp only [ha, if_true]
      · simp only [Bool.not_eq_true] at ha
        simp only [ha, Bool.false_eq_true, if_false]
        rw [aRowsQ_congr (box := false)
          (fun t ht => h t (by simp only [aggEdges, ha, Bool.false_eq_true, if_false]; exact ht))]
  | some (.up .fls) =>
      show nOrAll (aRowsQ id p prev₁ done (.up .fls) false seen)
         = nOrAll (aRowsQ id p prev₂ done (.up .fls) false seen)
      rw [aRowsQ_congr (box := false) (fun t ht => h t (by simpa [aggEdges] using ht))]
  | some (.up (.or P₁ P₂)) =>
      have h1 : prev₁ [] done (some (.up P₁)) seen = prev₂ [] done (some (.up P₁)) seen :=
        h ([], done, some (.up P₁), seen) (by simp [aggEdges])
      have h2 : prev₁ [] done (some (.up P₂)) seen = prev₂ [] done (some (.up P₂)) seen :=
        h ([], done, some (.up P₂), seen) (by simp [aggEdges])
      show nOrAll ([prev₁ [] done (some (.up P₁)) seen, prev₁ [] done (some (.up P₂)) seen] ++
              aRowsQ id p prev₁ done (.up (.or P₁ P₂)) false seen)
         = nOrAll ([prev₂ [] done (some (.up P₁)) seen, prev₂ [] done (some (.up P₂)) seen] ++
              aRowsQ id p prev₂ done (.up (.or P₁ P₂)) false seen)
      rw [h1, h2, aRowsQ_congr (box := false)
        (fun t ht => h t (by simp only [aggEdges]; exact List.mem_append.mpr (Or.inr ht)))]
  | some (.up (.down M)) =>
      have h1 : prev₁ [] done (some M) seen = prev₂ [] done (some M) seen :=
        h ([], done, some M, seen) (by simp [aggEdges])
      show nOrAll ([prev₁ [] done (some M) seen] ++
              aRowsQ id p prev₁ done (.up (.down M)) false seen)
         = nOrAll ([prev₂ [] done (some M) seen] ++
              aRowsQ id p prev₂ done (.up (.down M)) false seen)
      rw [h1, aRowsQ_congr (box := false)
        (fun t ht => h t (by simp only [aggEdges]; exact List.mem_append.mpr (Or.inr ht)))]
  | some (.circ Q) =>
      show Neg.circ (.down (nOrAll (laxPrefixQ prev₁ done seen Q ++
              aRowsQ id p prev₁ done (.circ Q) true seen)))
         = Neg.circ (.down (nOrAll (laxPrefixQ prev₂ done seen Q ++
              aRowsQ id p prev₂ done (.circ Q) true seen)))
      rw [laxPrefixQ_congr
            (fun t ht => h t (by simp only [aggEdges]; exact List.mem_append.mpr (Or.inl ht))),
          aRowsQ_congr (box := true)
            (fun t ht => h t (by simp only [aggEdges]; exact List.mem_append.mpr (Or.inr ht)))]

/-- **The mirror is complete**: `stepQ` at `s` reads the level below only at
states listed by `edgesQ s`. -/
theorem stepQ_congr (s : QState)
    (h : ∀ t ∈ edgesQ s, atSt prev₁ t = atSt prev₂ t) :
    atSt (stepQ id p prev₁) s = atSt (stepQ id p prev₂) s := by
  obtain ⟨todo, done, g, seen⟩ := s
  match todo, g with
  | [], g =>
      show (match findFire done (splits done) with
        | some (_, N, rest) => prev₁ [N] rest g (id seen)
        | none => aggQ id p prev₁ done g seen)
        = (match findFire done (splits done) with
        | some (_, N, rest) => prev₂ [N] rest g (id seen)
        | none => aggQ id p prev₂ done g seen)
      split
      · rename_i a N rest hf
        exact h ([N], rest, g, seen) (by simp only [edgesQ, hf]; simp)
      · rename_i hf
        exact aggQ_congr (fun t ht => h t (by simp only [edgesQ, hf]; exact ht))
  | .up (.atom a) :: todo, g =>
      exact h (todo, .up (.atom a) :: done, g, seen) (by simp [edgesQ])
  | .up .fls :: todo, none => rfl
  | .up .fls :: todo, some G => rfl
  | .up (.or P Q) :: todo, none =>
      show nOrAll ((invertPos (.or P Q)).map (fun b => prev₁ (b ++ todo) done none (id seen)))
         = nOrAll ((invertPos (.or P Q)).map (fun b => prev₂ (b ++ todo) done none (id seen)))
      refine congrArg nOrAll (List.map_congr_left ?_)
      intro b hb
      exact h (b ++ todo, done, none, seen)
        (by simp only [edgesQ]; exact List.mem_map.mpr ⟨b, hb, rfl⟩)
  | .up (.or P Q) :: todo, some G =>
      show nAndAll ((invertPos (.or P Q)).map (fun b =>
             Neg.imp (.down (prev₁ (b ++ todo) done none (id seen)))
               (prev₁ (b ++ todo) done (some G) (id seen))))
         = nAndAll ((invertPos (.or P Q)).map (fun b =>
             Neg.imp (.down (prev₂ (b ++ todo) done none (id seen)))
               (prev₂ (b ++ todo) done (some G) (id seen))))
      refine congrArg nAndAll (List.map_congr_left ?_)
      intro b hb
      have h1 : prev₁ (b ++ todo) done none (id seen)
              = prev₂ (b ++ todo) done none (id seen) :=
        h (b ++ todo, done, none, seen)
          (by simp only [edgesQ]; exact List.mem_flatMap.mpr ⟨b, hb, by simp⟩)
      have h2 : prev₁ (b ++ todo) done (some G) (id seen)
              = prev₂ (b ++ todo) done (some G) (id seen) :=
        h (b ++ todo, done, some G, seen)
          (by simp only [edgesQ]; exact List.mem_flatMap.mpr ⟨b, hb, by simp⟩)
      rw [h1, h2]
  | .up (.down M) :: todo, g =>
      exact h (M :: todo, done, g, seen) (by simp [edgesQ])
  | .and M N :: todo, g =>
      exact h (M :: N :: todo, done, g, seen) (by simp [edgesQ])
  | .imp .fls N :: todo, g =>
      exact h (todo, done, g, seen) (by simp [edgesQ])
  | .imp (.atom a) N :: todo, g =>
      exact h (todo, .imp (.atom a) N :: done, g, seen) (by simp [edgesQ])
  | .imp (.or Q₁ Q₂) N :: todo, g =>
      exact h (todo, .imp (.or Q₁ Q₂) N :: done, g, seen) (by simp [edgesQ])
  | .imp (.down (.up P')) N :: todo, g =>
      exact h (todo, .imp (.down (.up P')) N :: done, g, seen) (by simp [edgesQ])
  | .imp (.down (.and M₁ M₂)) N :: todo, g =>
      exact h (todo, .imp (.down (.and M₁ M₂)) N :: done, g, seen) (by simp [edgesQ])
  | .imp (.down (.imp Q' N')) N :: todo, g =>
      exact h (todo, .imp (.down (.imp Q' N')) N :: done, g, seen) (by simp [edgesQ])
  | .circ Q :: todo, g =>
      exact h (todo, .circ Q :: done, g, seen) (by simp [edgesQ])
  | .imp (.down (.circ Q')) N :: todo, g =>
      exact h (todo, .imp (.down (.circ Q')) N :: done, g, seen) (by simp [edgesQ])

end

end LJFO

/-! ## Pins -/

#axioms_within LJFO.stepQ_congr [propext, Quot.sound]
