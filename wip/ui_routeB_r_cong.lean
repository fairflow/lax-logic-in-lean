/-
Route (B), node **N4**, WP12b, **stage 1, part B**: the edge mirror of the
pair-recording recursion, and the proof that it is COMPLETE.

`edgesR s` lists the states `stepR id p prev` reads `prev` at, and

    stepR_congr : (∀ t ∈ edgesR s, atStR prev₁ t = atStR prev₂ t) →
                  atStR (stepR id p prev₁) s = atStR (stepR id p prev₂) s

says that it lists ENOUGH of them.  `wip/ui_routeB_n4q_meas.lean` Part 3 and
`wip/ui_routeB_n4q_cong.lean`, transcribed: the guard target records the PAIR
`(Qa, done)` and the recording test is `seenMemR seen Qa done`; nothing else
changes, and nothing here mentions the measure.

`LJF/` is untouched; this module is a leaf.
-/
import wip.ui_routeB_r_meas
import Meta.Audit

set_option autoImplicit false

namespace LJFO

/-! # Part 1 · The consulted states, mirrored -/

/-- The `∃p` rows of one parked compound implication. -/
def parkEdgesER (done : List Neg) (Qa : Pos) (N : Neg) (rest res : List Neg)
    (seen : SeenR) : List RState :=
  (if seenMemR seen Qa done then []
   else [([], done, some (.up Qa), (Qa, done) :: seen), ([N], rest, none, seen)])
  ++ [(res, rest, none, seen)]

/-- The `∀p` rows of one parked compound implication. -/
def parkEdgesAR (done : List Neg) (Qa : Pos) (N : Neg) (rest : List Neg)
    (goal : Neg) (seen : SeenR) : List RState :=
  if seenMemR seen Qa done then []
  else [([], done, some (.up Qa), (Qa, done) :: seen), ([N], rest, some goal, seen)]

/-- One row of `eRowsR`, as states. -/
def eRowBodyR (done : List Neg) (seen : SeenR) : Neg → List Neg → List RState
  | .imp (.atom _) N, rest => [([N], rest, none, seen)]
  | .imp (.down (.imp Q' N')) N, rest =>
      parkEdgesER done (.down (.imp Q' N')) N rest [.imp (.down N') N] seen
  | .circ Q, rest => [([.up Q], rest, none, seen)]
  | .imp (.down (.circ Q')) N, rest => parkEdgesER done (.down (.circ Q')) N rest [] seen
  | .imp (.or Qa Qb) N, rest => parkEdgesER done (.or Qa Qb) N rest [] seen
  | .imp (.down (.up Pa)) N, rest => parkEdgesER done (.down (.up Pa)) N rest [] seen
  | .imp (.down (.and Ma Mb)) N, rest => parkEdgesER done (.down (.and Ma Mb)) N rest [] seen
  | _, _ => []

/-- `eRowsR`, as states. -/
def eRowEdgesR (done : List Neg) (seen : SeenR) : List RState :=
  (splits done).flatMap (fun Xr => eRowBodyR done seen Xr.1 Xr.2)

/-- One row of `aRowsR`, as states. -/
def aRowBodyR (done : List Neg) (goal : Neg) (box : Bool) (seen : SeenR) :
    Neg → List Neg → List RState
  | .imp (.atom _) N, rest => [([N], rest, some goal, seen)]
  | .imp (.down (.imp Q' N')) N, rest =>
      parkEdgesAR done (.down (.imp Q' N')) N rest goal seen
  | .imp (.down (.circ Q')) N, rest => parkEdgesAR done (.down (.circ Q')) N rest goal seen
  | .imp (.or Qa Qb) N, rest => parkEdgesAR done (.or Qa Qb) N rest goal seen
  | .imp (.down (.up Pa)) N, rest => parkEdgesAR done (.down (.up Pa)) N rest goal seen
  | .imp (.down (.and Ma Mb)) N, rest => parkEdgesAR done (.down (.and Ma Mb)) N rest goal seen
  | .circ R, rest =>
      if box then [([.up R], rest, none, seen), ([.up R], rest, some goal, seen)] else []
  | _, _ => []

/-- `aRowsR`, as states. -/
def aRowEdgesR (done : List Neg) (goal : Neg) (box : Bool) (seen : SeenR) :
    List RState :=
  (splits done).flatMap (fun Xr => aRowBodyR done goal box seen Xr.1 Xr.2)

/-- `laxPrefixR`, as states. -/
def laxEdgesR (done : List Neg) (seen : SeenR) : Pos → List RState
  | .atom q => [([], done, some (.up (.atom q)), seen)]
  | .fls => [([], done, some (.up .fls), seen)]
  | .or P₁ P₂ => [([], done, some (.circ P₁), seen),
                  ([], done, some (.circ P₂), seen),
                  ([], done, some (.up (.or P₁ P₂)), seen)]
  | .down (.up P') => [([], done, some (.circ P'), seen)]
  | .down (.circ P') => [([], done, some (.circ P'), seen)]
  | .down (.and M₁ M₂) => [([], done, some (.up (.down (.and M₁ M₂))), seen)]
  | .down (.imp Q₀ N₀) => [([], done, some (.up (.down (.imp Q₀ N₀))), seen)]

/-- `aggR`, as states. -/
def aggEdgesR (done : List Neg) (g : Option Neg) (seen : SeenR) : List RState :=
  match g with
  | none => eRowEdgesR done seen
  | some (.imp Q N) =>
      (invertPos Q).flatMap (fun b => [(b, done, none, seen), (b, done, some N, seen)])
  | some (.and M N) => [([], done, some M, seen), ([], done, some N, seen)]
  | some (.up (.atom q)) =>
      if atomMem q done then [] else aRowEdgesR done (.up (.atom q)) false seen
  | some (.up .fls) => aRowEdgesR done (.up .fls) false seen
  | some (.up (.or P₁ P₂)) =>
      [([], done, some (.up P₁), seen), ([], done, some (.up P₂), seen)] ++
        aRowEdgesR done (.up (.or P₁ P₂)) false seen
  | some (.up (.down M)) =>
      [([], done, some M, seen)] ++ aRowEdgesR done (.up (.down M)) false seen
  | some (.circ Q) => laxEdgesR done seen Q ++ aRowEdgesR done (.circ Q) true seen

/-- **The consulted states of one `stepR` unfolding**, at `rst = id`. -/
def edgesR : RState → List RState
  | (.up (.atom a) :: todo, done, g, s) => [(todo, .up (.atom a) :: done, g, s)]
  | (.up .fls :: _, _, _, _) => []
  | (.up (.or P Q) :: todo, done, none, s) =>
      (invertPos (.or P Q)).map (fun b => (b ++ todo, done, none, s))
  | (.up (.or P Q) :: todo, done, some G, s) =>
      (invertPos (.or P Q)).flatMap (fun b =>
        [(b ++ todo, done, none, s), (b ++ todo, done, some G, s)])
  | (.up (.down M) :: todo, done, g, s) => [(M :: todo, done, g, s)]
  | (.and M N :: todo, done, g, s) => [(M :: N :: todo, done, g, s)]
  | (.imp .fls _ :: todo, done, g, s) => [(todo, done, g, s)]
  | (.imp (.atom a) N :: todo, done, g, s) => [(todo, .imp (.atom a) N :: done, g, s)]
  | (.imp (.or Q₁ Q₂) N :: todo, done, g, s) =>
      [(todo, .imp (.or Q₁ Q₂) N :: done, g, s)]
  | (.imp (.down (.up P')) N :: todo, done, g, s) =>
      [(todo, .imp (.down (.up P')) N :: done, g, s)]
  | (.imp (.down (.and M₁ M₂)) N :: todo, done, g, s) =>
      [(todo, .imp (.down (.and M₁ M₂)) N :: done, g, s)]
  | (.imp (.down (.imp Q' N')) N :: todo, done, g, s) =>
      [(todo, .imp (.down (.imp Q' N')) N :: done, g, s)]
  | (.circ Q :: todo, done, g, s) => [(todo, .circ Q :: done, g, s)]
  | (.imp (.down (.circ Q')) N :: todo, done, g, s) =>
      [(todo, .imp (.down (.circ Q')) N :: done, g, s)]
  | ([], done, g, seen) =>
      match findFire done (splits done) with
      | some (_, N, rest) => [([N], rest, g, seen)]
      | none => aggEdgesR done g seen

/-! # Part 2 · The mirror is complete -/

section
variable {p : String} {prev₁ prev₂ : ApproxR}

/-! # Part 1 · The parked-implication rows -/

theorem parkRowER_congr {done : List Neg} {Qa : Pos} {N : Neg} {rest res : List Neg}
    {seen : SeenR}
    (h : ∀ t ∈ parkEdgesER done Qa N rest res seen, atStR prev₁ t = atStR prev₂ t) :
    parkRowER id prev₁ done Qa N rest res seen
      = parkRowER id prev₂ done Qa N rest res seen := by
  have hres : prev₁ res rest none (id seen) = prev₂ res rest none (id seen) :=
    h (res, rest, none, seen) (by simp [parkEdgesER])
  by_cases hm : seenMemR seen Qa done = true
  · simp only [parkRowER, hm, if_true]
    rw [hres]
  · simp only [Bool.not_eq_true] at hm
    have h1 : prev₁ [] done (some (.up Qa)) ((Qa, done) :: seen)
            = prev₂ [] done (some (.up Qa)) ((Qa, done) :: seen) :=
      h ([], done, some (.up Qa), (Qa, done) :: seen) (by simp [parkEdgesER, hm])
    have h2 : prev₁ [N] rest none (id seen) = prev₂ [N] rest none (id seen) :=
      h ([N], rest, none, seen) (by simp [parkEdgesER, hm])
    simp only [parkRowER, hm, Bool.false_eq_true, if_false]
    rw [h1, h2, hres]

theorem parkRowAR_congr {done : List Neg} {Qa : Pos} {N : Neg} {rest : List Neg}
    {goal : Neg} {seen : SeenR}
    (h : ∀ t ∈ parkEdgesAR done Qa N rest goal seen, atStR prev₁ t = atStR prev₂ t) :
    parkRowAR id prev₁ done Qa N rest goal seen
      = parkRowAR id prev₂ done Qa N rest goal seen := by
  by_cases hm : seenMemR seen Qa done = true
  · simp only [parkRowAR, hm, if_true]
  · simp only [Bool.not_eq_true] at hm
    have h1 : prev₁ [] done (some (.up Qa)) ((Qa, done) :: seen)
            = prev₂ [] done (some (.up Qa)) ((Qa, done) :: seen) :=
      h ([], done, some (.up Qa), (Qa, done) :: seen) (by simp [parkEdgesAR, hm])
    have h2 : prev₁ [N] rest (some goal) (id seen)
            = prev₂ [N] rest (some goal) (id seen) :=
      h ([N], rest, some goal, seen) (by simp [parkEdgesAR, hm])
    simp only [parkRowAR, hm, Bool.false_eq_true, if_false]
    rw [h1, h2]

/-! # Part 2 · The row maps -/

theorem eRowsR_congr {done : List Neg} {seen : SeenR}
    (h : ∀ t ∈ eRowEdgesR done seen, atStR prev₁ t = atStR prev₂ t) :
    eRowsR id p prev₁ done seen = eRowsR id p prev₂ done seen := by
  simp only [eRowsR]
  refine List.map_congr_left ?_
  rintro ⟨X, rest⟩ hXr
  have hb : ∀ t ∈ eRowBodyR done seen X rest, atStR prev₁ t = atStR prev₂ t :=
    fun t ht => h t (List.mem_flatMap.mpr ⟨(X, rest), hXr, ht⟩)
  match X with
  | .up (.atom a) => rfl
  | .imp (.atom a) N =>
      have hx : prev₁ [N] rest none (id seen) = prev₂ [N] rest none (id seen) :=
        hb ([N], rest, none, seen) (by simp [eRowBodyR])
      show pGuard p a nTop (.imp (.atom a) (prev₁ [N] rest none (id seen)))
         = pGuard p a nTop (.imp (.atom a) (prev₂ [N] rest none (id seen)))
      rw [hx]
  | .imp (.down (.imp Q' N')) N =>
      exact parkRowER_congr (fun t ht => hb t (by simpa [eRowBodyR] using ht))
  | .circ Q =>
      have hx : prev₁ [Neg.up Q] rest none (id seen)
              = prev₂ [Neg.up Q] rest none (id seen) :=
        hb ([Neg.up Q], rest, none, seen) (by simp [eRowBodyR])
      show Neg.circ (.down (prev₁ [Neg.up Q] rest none (id seen)))
         = Neg.circ (.down (prev₂ [Neg.up Q] rest none (id seen)))
      rw [hx]
  | .imp (.down (.circ Q')) N =>
      exact parkRowER_congr (fun t ht => hb t (by simpa [eRowBodyR] using ht))
  | .imp (.or Qa Qb) N =>
      exact parkRowER_congr (fun t ht => hb t (by simpa [eRowBodyR] using ht))
  | .imp (.down (.up Pa)) N =>
      exact parkRowER_congr (fun t ht => hb t (by simpa [eRowBodyR] using ht))
  | .imp (.down (.and Ma Mb)) N =>
      exact parkRowER_congr (fun t ht => hb t (by simpa [eRowBodyR] using ht))
  | .up .fls | .up (.or _ _) | .up (.down _) | .imp .fls _ | .and _ _ => rfl

theorem aRowsR_congr {done : List Neg} {goal : Neg} {box : Bool} {seen : SeenR}
    (h : ∀ t ∈ aRowEdgesR done goal box seen, atStR prev₁ t = atStR prev₂ t) :
    aRowsR id p prev₁ done goal box seen = aRowsR id p prev₂ done goal box seen := by
  simp only [aRowsR]
  refine List.map_congr_left ?_
  rintro ⟨X, rest⟩ hXr
  have hb : ∀ t ∈ aRowBodyR done goal box seen X rest, atStR prev₁ t = atStR prev₂ t :=
    fun t ht => h t (List.mem_flatMap.mpr ⟨(X, rest), hXr, ht⟩)
  match X with
  | .imp (.atom a) N =>
      have hx : prev₁ [N] rest (some goal) (id seen)
              = prev₂ [N] rest (some goal) (id seen) :=
        hb ([N], rest, some goal, seen) (by simp [aRowBodyR])
      show pGuard p a nBot (nAnd (.up (.atom a)) (prev₁ [N] rest (some goal) (id seen)))
         = pGuard p a nBot (nAnd (.up (.atom a)) (prev₂ [N] rest (some goal) (id seen)))
      rw [hx]
  | .imp (.down (.imp Q' N')) N =>
      exact parkRowAR_congr (fun t ht => hb t (by simpa [aRowBodyR] using ht))
  | .imp (.down (.circ Q')) N =>
      exact parkRowAR_congr (fun t ht => hb t (by simpa [aRowBodyR] using ht))
  | .imp (.or Qa Qb) N =>
      exact parkRowAR_congr (fun t ht => hb t (by simpa [aRowBodyR] using ht))
  | .imp (.down (.up Pa)) N =>
      exact parkRowAR_congr (fun t ht => hb t (by simpa [aRowBodyR] using ht))
  | .imp (.down (.and Ma Mb)) N =>
      exact parkRowAR_congr (fun t ht => hb t (by simpa [aRowBodyR] using ht))
  | .circ R =>
      by_cases hbx : box = true
      · have h1 : prev₁ [Neg.up R] rest none (id seen)
                = prev₂ [Neg.up R] rest none (id seen) :=
          hb ([Neg.up R], rest, none, seen) (by simp [aRowBodyR, hbx])
        have h2 : prev₁ [Neg.up R] rest (some goal) (id seen)
                = prev₂ [Neg.up R] rest (some goal) (id seen) :=
          hb ([Neg.up R], rest, some goal, seen) (by simp [aRowBodyR, hbx])
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

theorem laxPrefixR_congr {done : List Neg} {seen : SeenR} {Q : Pos}
    (h : ∀ t ∈ laxEdgesR done seen Q, atStR prev₁ t = atStR prev₂ t) :
    laxPrefixR prev₁ done seen Q = laxPrefixR prev₂ done seen Q := by
  match Q with
  | .atom q =>
      have h1 : prev₁ [] done (some (.up (.atom q))) seen
              = prev₂ [] done (some (.up (.atom q))) seen :=
        h ([], done, some (.up (.atom q)), seen) (by simp [laxEdgesR])
      show [prev₁ [] done (some (.up (.atom q))) seen]
         = [prev₂ [] done (some (.up (.atom q))) seen]
      rw [h1]
  | .fls =>
      have h1 : prev₁ [] done (some (.up .fls)) seen
              = prev₂ [] done (some (.up .fls)) seen :=
        h ([], done, some (.up .fls), seen) (by simp [laxEdgesR])
      show [prev₁ [] done (some (.up .fls)) seen] = [prev₂ [] done (some (.up .fls)) seen]
      rw [h1]
  | .or P₁ P₂ =>
      have h1 : prev₁ [] done (some (.circ P₁)) seen
              = prev₂ [] done (some (.circ P₁)) seen :=
        h ([], done, some (.circ P₁), seen) (by simp [laxEdgesR])
      have h2 : prev₁ [] done (some (.circ P₂)) seen
              = prev₂ [] done (some (.circ P₂)) seen :=
        h ([], done, some (.circ P₂), seen) (by simp [laxEdgesR])
      have h3 : prev₁ [] done (some (.up (.or P₁ P₂))) seen
              = prev₂ [] done (some (.up (.or P₁ P₂))) seen :=
        h ([], done, some (.up (.or P₁ P₂)), seen) (by simp [laxEdgesR])
      show [prev₁ [] done (some (.circ P₁)) seen, prev₁ [] done (some (.circ P₂)) seen,
            prev₁ [] done (some (.up (.or P₁ P₂))) seen]
         = [prev₂ [] done (some (.circ P₁)) seen, prev₂ [] done (some (.circ P₂)) seen,
            prev₂ [] done (some (.up (.or P₁ P₂))) seen]
      rw [h1, h2, h3]
  | .down (.up P') =>
      have h1 : prev₁ [] done (some (.circ P')) seen
              = prev₂ [] done (some (.circ P')) seen :=
        h ([], done, some (.circ P'), seen) (by simp [laxEdgesR])
      show [prev₁ [] done (some (.circ P')) seen] = [prev₂ [] done (some (.circ P')) seen]
      rw [h1]
  | .down (.circ P') =>
      have h1 : prev₁ [] done (some (.circ P')) seen
              = prev₂ [] done (some (.circ P')) seen :=
        h ([], done, some (.circ P'), seen) (by simp [laxEdgesR])
      show [prev₁ [] done (some (.circ P')) seen] = [prev₂ [] done (some (.circ P')) seen]
      rw [h1]
  | .down (.and M₁ M₂) =>
      have h1 : prev₁ [] done (some (.up (.down (.and M₁ M₂)))) seen
              = prev₂ [] done (some (.up (.down (.and M₁ M₂)))) seen :=
        h ([], done, some (.up (.down (.and M₁ M₂))), seen) (by simp [laxEdgesR])
      show [prev₁ [] done (some (.up (.down (.and M₁ M₂)))) seen]
         = [prev₂ [] done (some (.up (.down (.and M₁ M₂)))) seen]
      rw [h1]
  | .down (.imp Q₀ N₀) =>
      have h1 : prev₁ [] done (some (.up (.down (.imp Q₀ N₀)))) seen
              = prev₂ [] done (some (.up (.down (.imp Q₀ N₀)))) seen :=
        h ([], done, some (.up (.down (.imp Q₀ N₀))), seen) (by simp [laxEdgesR])
      show [prev₁ [] done (some (.up (.down (.imp Q₀ N₀)))) seen]
         = [prev₂ [] done (some (.up (.down (.imp Q₀ N₀)))) seen]
      rw [h1]

/-! # Part 3 · The aggregate and the step -/

theorem aggR_congr {done : List Neg} {g : Option Neg} {seen : SeenR}
    (h : ∀ t ∈ aggEdgesR done g seen, atStR prev₁ t = atStR prev₂ t) :
    aggR id p prev₁ done g seen = aggR id p prev₂ done g seen := by
  match g with
  | none =>
      show nAndAll (eRowsR id p prev₁ done seen) = nAndAll (eRowsR id p prev₂ done seen)
      rw [eRowsR_congr (fun t ht => h t (by simpa [aggEdgesR] using ht))]
  | some (.imp Q N) =>
      show nAndAll ((invertPos Q).map (fun b =>
             Neg.imp (.down (prev₁ b done none seen)) (prev₁ b done (some N) seen)))
         = nAndAll ((invertPos Q).map (fun b =>
             Neg.imp (.down (prev₂ b done none seen)) (prev₂ b done (some N) seen)))
      refine congrArg nAndAll (List.map_congr_left ?_)
      intro b hb
      have h1 : prev₁ b done none seen = prev₂ b done none seen :=
        h (b, done, none, seen)
          (by simp only [aggEdgesR]; exact List.mem_flatMap.mpr ⟨b, hb, by simp⟩)
      have h2 : prev₁ b done (some N) seen = prev₂ b done (some N) seen :=
        h (b, done, some N, seen)
          (by simp only [aggEdgesR]; exact List.mem_flatMap.mpr ⟨b, hb, by simp⟩)
      rw [h1, h2]
  | some (.and M N) =>
      have h1 : prev₁ [] done (some M) seen = prev₂ [] done (some M) seen :=
        h ([], done, some M, seen) (by simp [aggEdgesR])
      have h2 : prev₁ [] done (some N) seen = prev₂ [] done (some N) seen :=
        h ([], done, some N, seen) (by simp [aggEdgesR])
      show nAnd (prev₁ [] done (some M) seen) (prev₁ [] done (some N) seen)
         = nAnd (prev₂ [] done (some M) seen) (prev₂ [] done (some N) seen)
      rw [h1, h2]
  | some (.up (.atom q)) =>
      show (if atomMem q done then nTop
            else nOrAll (atomHead p q ++ aRowsR id p prev₁ done (.up (.atom q)) false seen))
         = (if atomMem q done then nTop
            else nOrAll (atomHead p q ++ aRowsR id p prev₂ done (.up (.atom q)) false seen))
      by_cases ha : atomMem q done = true
      · simp only [ha, if_true]
      · simp only [Bool.not_eq_true] at ha
        simp only [ha, Bool.false_eq_true, if_false]
        rw [aRowsR_congr (box := false)
          (fun t ht => h t (by simp only [aggEdgesR, ha, Bool.false_eq_true, if_false]; exact ht))]
  | some (.up .fls) =>
      show nOrAll (aRowsR id p prev₁ done (.up .fls) false seen)
         = nOrAll (aRowsR id p prev₂ done (.up .fls) false seen)
      rw [aRowsR_congr (box := false) (fun t ht => h t (by simpa [aggEdgesR] using ht))]
  | some (.up (.or P₁ P₂)) =>
      have h1 : prev₁ [] done (some (.up P₁)) seen = prev₂ [] done (some (.up P₁)) seen :=
        h ([], done, some (.up P₁), seen) (by simp [aggEdgesR])
      have h2 : prev₁ [] done (some (.up P₂)) seen = prev₂ [] done (some (.up P₂)) seen :=
        h ([], done, some (.up P₂), seen) (by simp [aggEdgesR])
      show nOrAll ([prev₁ [] done (some (.up P₁)) seen, prev₁ [] done (some (.up P₂)) seen] ++
              aRowsR id p prev₁ done (.up (.or P₁ P₂)) false seen)
         = nOrAll ([prev₂ [] done (some (.up P₁)) seen, prev₂ [] done (some (.up P₂)) seen] ++
              aRowsR id p prev₂ done (.up (.or P₁ P₂)) false seen)
      rw [h1, h2, aRowsR_congr (box := false)
        (fun t ht => h t (by simp only [aggEdgesR]; exact List.mem_append.mpr (Or.inr ht)))]
  | some (.up (.down M)) =>
      have h1 : prev₁ [] done (some M) seen = prev₂ [] done (some M) seen :=
        h ([], done, some M, seen) (by simp [aggEdgesR])
      show nOrAll ([prev₁ [] done (some M) seen] ++
              aRowsR id p prev₁ done (.up (.down M)) false seen)
         = nOrAll ([prev₂ [] done (some M) seen] ++
              aRowsR id p prev₂ done (.up (.down M)) false seen)
      rw [h1, aRowsR_congr (box := false)
        (fun t ht => h t (by simp only [aggEdgesR]; exact List.mem_append.mpr (Or.inr ht)))]
  | some (.circ Q) =>
      show Neg.circ (.down (nOrAll (laxPrefixR prev₁ done seen Q ++
              aRowsR id p prev₁ done (.circ Q) true seen)))
         = Neg.circ (.down (nOrAll (laxPrefixR prev₂ done seen Q ++
              aRowsR id p prev₂ done (.circ Q) true seen)))
      rw [laxPrefixR_congr
            (fun t ht => h t (by simp only [aggEdgesR]; exact List.mem_append.mpr (Or.inl ht))),
          aRowsR_congr (box := true)
            (fun t ht => h t (by simp only [aggEdgesR]; exact List.mem_append.mpr (Or.inr ht)))]

/-- **The mirror is complete**: `stepR` at `s` reads the level below only at
states listed by `edgesR s`. -/
theorem stepR_congr (s : RState)
    (h : ∀ t ∈ edgesR s, atStR prev₁ t = atStR prev₂ t) :
    atStR (stepR id p prev₁) s = atStR (stepR id p prev₂) s := by
  obtain ⟨todo, done, g, seen⟩ := s
  match todo, g with
  | [], g =>
      show (match findFire done (splits done) with
        | some (_, N, rest) => prev₁ [N] rest g (id seen)
        | none => aggR id p prev₁ done g seen)
        = (match findFire done (splits done) with
        | some (_, N, rest) => prev₂ [N] rest g (id seen)
        | none => aggR id p prev₂ done g seen)
      split
      · rename_i a N rest hf
        exact h ([N], rest, g, seen) (by simp only [edgesR, hf]; simp)
      · rename_i hf
        exact aggR_congr (fun t ht => h t (by simp only [edgesR, hf]; exact ht))
  | .up (.atom a) :: todo, g =>
      exact h (todo, .up (.atom a) :: done, g, seen) (by simp [edgesR])
  | .up .fls :: todo, none => rfl
  | .up .fls :: todo, some G => rfl
  | .up (.or P Q) :: todo, none =>
      show nOrAll ((invertPos (.or P Q)).map (fun b => prev₁ (b ++ todo) done none (id seen)))
         = nOrAll ((invertPos (.or P Q)).map (fun b => prev₂ (b ++ todo) done none (id seen)))
      refine congrArg nOrAll (List.map_congr_left ?_)
      intro b hb
      exact h (b ++ todo, done, none, seen)
        (by simp only [edgesR]; exact List.mem_map.mpr ⟨b, hb, rfl⟩)
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
          (by simp only [edgesR]; exact List.mem_flatMap.mpr ⟨b, hb, by simp⟩)
      have h2 : prev₁ (b ++ todo) done (some G) (id seen)
              = prev₂ (b ++ todo) done (some G) (id seen) :=
        h (b ++ todo, done, some G, seen)
          (by simp only [edgesR]; exact List.mem_flatMap.mpr ⟨b, hb, by simp⟩)
      rw [h1, h2]
  | .up (.down M) :: todo, g =>
      exact h (M :: todo, done, g, seen) (by simp [edgesR])
  | .and M N :: todo, g =>
      exact h (M :: N :: todo, done, g, seen) (by simp [edgesR])
  | .imp .fls N :: todo, g =>
      exact h (todo, done, g, seen) (by simp [edgesR])
  | .imp (.atom a) N :: todo, g =>
      exact h (todo, .imp (.atom a) N :: done, g, seen) (by simp [edgesR])
  | .imp (.or Q₁ Q₂) N :: todo, g =>
      exact h (todo, .imp (.or Q₁ Q₂) N :: done, g, seen) (by simp [edgesR])
  | .imp (.down (.up P')) N :: todo, g =>
      exact h (todo, .imp (.down (.up P')) N :: done, g, seen) (by simp [edgesR])
  | .imp (.down (.and M₁ M₂)) N :: todo, g =>
      exact h (todo, .imp (.down (.and M₁ M₂)) N :: done, g, seen) (by simp [edgesR])
  | .imp (.down (.imp Q' N')) N :: todo, g =>
      exact h (todo, .imp (.down (.imp Q' N')) N :: done, g, seen) (by simp [edgesR])
  | .circ Q :: todo, g =>
      exact h (todo, .circ Q :: done, g, seen) (by simp [edgesR])
  | .imp (.down (.circ Q')) N :: todo, g =>
      exact h (todo, .imp (.down (.circ Q')) N :: done, g, seen) (by simp [edgesR])

end

end LJFO

/-! ## Pins -/

#axioms_within LJFO.parkRowER_congr [propext, Quot.sound]
#axioms_within LJFO.parkRowAR_congr [propext, Quot.sound]
#axioms_within LJFO.eRowsR_congr [propext, Quot.sound]
#axioms_within LJFO.aRowsR_congr [propext, Quot.sound]
#axioms_within LJFO.laxPrefixR_congr [propext, Quot.sound]
#axioms_within LJFO.aggR_congr [propext, Quot.sound]
#axioms_within LJFO.stepR_congr [propext, Quot.sound]
