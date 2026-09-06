/-
Route (B), node **N4**, WP12c, **prerequisite 1**: **RECORD MONOTONICITY of
the pair-recording recursion `interpR`**.

`wip/ui_routeB_r_mono.lean` reads the polarity table along the FUEL.  This
module reads it along the RECORD: a larger record cuts more rows, and the
cut is `⊤` in the `∃p` aggregate and `⊥` in the `∀p` aggregate, so

    E_f(s | seen)   ⊢  E_f(s | seen')        (`∃p` is monotone in the record)
    A_f(s | seen')  ⊢  A_f(s | seen)         (`∀p` is antitone in the record)

whenever `SeenLe seen seen'`, i.e. whenever every genuine-loop test that
fires against `seen` fires against `seen'`.  At every state, every fuel and
every pair of records so related.

The proof is `wip/ui_routeB_r_mono.lean`'s: an induction on the fuel through
ONE operator lemma, `stepR` preserving the mixed-variance relation
`SeenMonoR`, the sixteen processing clauses discharged against an abstract
`prev`.  The only new case is the one that carries the whole content: at a
parked implication the test may fire on the right and not on the left, and
then the `∃p` row is `⊤` (weaker, so entailed) and the `∀p` row is `⊥`
(stronger, so entailing).

**Why WP12c needs it.**  The record grows at exactly one place, the guard
call of `parkRowER`/`parkRowAR`, which is emitted at `(Qa, done) :: seen`.
An induction that carries escapes must move its hypotheses and conclusions
between `seen` and `(Qa, done) :: seen` at that site; `SeenLe` is the
relation, `seenLe_tail` and `seenLe_cons` the two instances used.

`LJF/` is untouched; this module is a leaf.
-/
import wip.ui_routeB_r_mono
import Meta.Audit

set_option autoImplicit false

namespace LJFO

/-! # Part 1 · The order on records -/

/-- `seen'` records at least what `seen` records: every genuine-loop test
that fires against `seen` fires against `seen'`. -/
def SeenLe (s s' : SeenR) : Prop :=
  ∀ (Q : Pos) (done : List Neg), seenMemR s Q done = true → seenMemR s' Q done = true

theorem seenLe_refl (s : SeenR) : SeenLe s s := fun _ _ h => h

theorem seenLe_trans {s₁ s₂ s₃ : SeenR} (h₁ : SeenLe s₁ s₂) (h₂ : SeenLe s₂ s₃) :
    SeenLe s₁ s₃ := fun Q d h => h₂ Q d (h₁ Q d h)

/-- Recording one more pair on both sides preserves the order. -/
theorem seenLe_cons (e : Pos × List Neg) {s s' : SeenR} (h : SeenLe s s') :
    SeenLe (e :: s) (e :: s') := by
  rintro Q done hQ
  obtain ⟨Q₀, T₀⟩ := e
  by_cases hEq : Q₀ = Q
  · by_cases hs : sameSet T₀ done = true
    · simp only [seenMemR, if_pos hEq, if_pos hs]
    · simp only [seenMemR, if_pos hEq, if_neg hs] at hQ ⊢
      exact h Q done hQ
  · simp only [seenMemR, if_neg hEq] at hQ ⊢
    exact h Q done hQ

/-- A record is below any extension of itself. -/
theorem seenLe_tail (e : Pos × List Neg) (s : SeenR) : SeenLe s (e :: s) := by
  rintro Q done hQ
  obtain ⟨Q₀, T₀⟩ := e
  by_cases hEq : Q₀ = Q
  · by_cases hs : sameSet T₀ done = true
    · simp only [seenMemR, if_pos hEq, if_pos hs]
    · simp only [seenMemR, if_pos hEq, if_neg hs]
      exact hQ
  · simp only [seenMemR, if_neg hEq]
    exact hQ

/-! # Part 2 · The operator statement -/

/-- `prev` is monotone in the record: `∃p`-monotone, `∀p`-antitone. -/
structure SeenMonoR (p : String) (prev : ApproxR) : Type where
  /-- `∃p`: the smaller record's approximant entails the larger one's. -/
  E : ∀ (todo done : List Neg) (seen seen' : SeenR), SeenLe seen seen' →
        Inv [prev todo done none seen] [] .tru (prev todo done none seen')
  /-- `∀p`: the larger record's approximant entails the smaller one's. -/
  A : ∀ (todo done : List Neg) (G : Neg) (seen seen' : SeenR), SeenLe seen seen' →
        Inv [prev todo done (some G) seen'] [] .tru (prev todo done (some G) seen)

section OpR
variable {p : String} {prev : ApproxR}

/-! # Part 3 · The rows -/

/-- The `∃p` row of a parked compound implication is record-monotone.  The
new case: the test fires against `seen'` and not against `seen`, and the row
on the right is `⊤`. -/
noncomputable def smParkRowER (ih : SeenMonoR p prev)
    (done : List Neg) (Qa : Pos) (N : Neg) (rest res : List Neg)
    {seen seen' : SeenR} (hle : SeenLe seen seen') :
    Inv [parkRowER id prev done Qa N rest res seen] [] .tru
        (parkRowER id prev done Qa N rest res seen') := by
  unfold parkRowER
  refine andMono ?_ (ih.E res rest seen seen' hle)
  by_cases hc' : seenMemR seen' Qa done = true
  · rw [if_pos hc']; exact nTopIntro
  · have hc : ¬ seenMemR seen Qa done = true := fun hh => hc' (hle _ _ hh)
    rw [if_neg hc, if_neg hc']
    exact impMono
      (ih.A [] done (.up Qa) ((Qa, done) :: seen) ((Qa, done) :: seen')
        (seenLe_cons _ hle))
      (ih.E [N] rest seen seen' hle)

/-- The `∀p` attack row of a parked compound implication is record-antitone.
The new case: the test fires against `seen'` and not against `seen`, and the
row on the left is `⊥`. -/
noncomputable def smParkRowAR (ih : SeenMonoR p prev)
    (done : List Neg) (Qa : Pos) (N : Neg) (rest : List Neg) (goal : Neg)
    {seen seen' : SeenR} (hle : SeenLe seen seen') :
    Inv [parkRowAR id prev done Qa N rest goal seen'] [] .tru
        (parkRowAR id prev done Qa N rest goal seen) := by
  unfold parkRowAR
  by_cases hc' : seenMemR seen' Qa done = true
  · rw [if_pos hc']; exact nBotElim _ (List.mem_cons_self ..)
  · have hc : ¬ seenMemR seen Qa done = true := fun hh => hc' (hle _ _ hh)
    rw [if_neg hc, if_neg hc']
    exact andMono
      (ih.A [] done (.up Qa) ((Qa, done) :: seen) ((Qa, done) :: seen')
        (seenLe_cons _ hle))
      (ih.A [N] rest goal seen seen' hle)

/-- The `∃p` station rows, row by row. -/
noncomputable def smERowsR (ih : SeenMonoR p prev) (done : List Neg)
    {seen seen' : SeenR} (hle : SeenLe seen seen') :
    PW (eRowsR id p prev done seen) (eRowsR id p prev done seen') := by
  unfold eRowsR
  refine PW.mapBoth ?_
  rintro ⟨X, rest⟩ -
  match X with
  | .up (.atom a) => exact idNeg _ _ (List.mem_cons_self ..)
  | .imp (.atom a) N =>
      by_cases hap : a = p
      · simp only [pGuard, if_pos hap]; exact nTopIntro
      · simp only [pGuard, if_neg hap]
        exact impMonoAtom (ih.E [N] rest seen seen' hle)
  | .imp (.down (.imp Q' N')) N =>
      exact smParkRowER ih done (.down (.imp Q' N')) N rest [.imp (.down N') N] hle
  | .circ Q => exact circMono (ih.E [.up Q] rest seen seen' hle)
  | .imp (.down (.circ Q')) N =>
      exact smParkRowER ih done (.down (.circ Q')) N rest [] hle
  | .imp (.or Qa Qb) N => exact smParkRowER ih done (.or Qa Qb) N rest [] hle
  | .imp (.down (.up Pa)) N =>
      exact smParkRowER ih done (.down (.up Pa)) N rest [] hle
  | .imp (.down (.and Ma Mb)) N =>
      exact smParkRowER ih done (.down (.and Ma Mb)) N rest [] hle
  | .up .fls => exact nTopIntro
  | .up (.or _ _) => exact nTopIntro
  | .up (.down _) => exact nTopIntro
  | .imp .fls _ => exact nTopIntro
  | .and _ _ => exact nTopIntro

/-- The `∀p` station rows, row by row, at every goal and with or without the
box row. -/
noncomputable def smARowsR (ih : SeenMonoR p prev) (done : List Neg)
    (goal : Neg) (box : Bool) {seen seen' : SeenR} (hle : SeenLe seen seen') :
    PW (aRowsR id p prev done goal box seen')
       (aRowsR id p prev done goal box seen) := by
  unfold aRowsR
  refine PW.mapBoth ?_
  rintro ⟨X, rest⟩ -
  match X with
  | .imp (.atom a) N =>
      by_cases hap : a = p
      · simp only [pGuard, if_pos hap]
        exact nBotElim _ (List.mem_cons_self ..)
      · simp only [pGuard, if_neg hap]
        exact andMono (idNeg _ _ (List.mem_cons_self ..))
                      (ih.A [N] rest goal seen seen' hle)
  | .imp (.down (.imp Q' N')) N =>
      exact smParkRowAR ih done (.down (.imp Q' N')) N rest goal hle
  | .imp (.down (.circ Q')) N =>
      exact smParkRowAR ih done (.down (.circ Q')) N rest goal hle
  | .imp (.or Qa Qb) N => exact smParkRowAR ih done (.or Qa Qb) N rest goal hle
  | .imp (.down (.up Pa)) N =>
      exact smParkRowAR ih done (.down (.up Pa)) N rest goal hle
  | .imp (.down (.and Ma Mb)) N =>
      exact smParkRowAR ih done (.down (.and Ma Mb)) N rest goal hle
  | .circ R =>
      cases box with
      | true =>
          exact impMono (ih.E [.up R] rest seen seen' hle)
                        (ih.A [.up R] rest goal seen seen' hle)
      | false => exact nBotElim _ (List.mem_cons_self ..)
  | .up (.atom _) => exact nBotElim _ (List.mem_cons_self ..)
  | .up .fls => exact nBotElim _ (List.mem_cons_self ..)
  | .up (.or _ _) => exact nBotElim _ (List.mem_cons_self ..)
  | .up (.down _) => exact nBotElim _ (List.mem_cons_self ..)
  | .imp .fls _ => exact nBotElim _ (List.mem_cons_self ..)
  | .and _ _ => exact nBotElim _ (List.mem_cons_self ..)

/-- The lax goal-inversion prefix. -/
noncomputable def smLaxPrefixR (ih : SeenMonoR p prev)
    (done : List Neg) (Q : Pos) {seen seen' : SeenR} (hle : SeenLe seen seen') :
    PW (laxPrefixR prev done seen' Q) (laxPrefixR prev done seen Q) := by
  match Q with
  | .atom q => exact .cons (ih.A [] done (.up (.atom q)) seen seen' hle) .nil
  | .fls => exact .cons (ih.A [] done (.up .fls) seen seen' hle) .nil
  | .or P₁ P₂ =>
      exact .cons (ih.A [] done (.circ P₁) seen seen' hle)
        (.cons (ih.A [] done (.circ P₂) seen seen' hle)
          (.cons (ih.A [] done (.up (.or P₁ P₂)) seen seen' hle) .nil))
  | .down (.up P') => exact .cons (ih.A [] done (.circ P') seen seen' hle) .nil
  | .down (.circ P') => exact .cons (ih.A [] done (.circ P') seen seen' hle) .nil
  | .down (.and M₁ M₂) =>
      exact .cons (ih.A [] done (.up (.down (.and M₁ M₂))) seen seen' hle) .nil
  | .down (.imp Q₀ N₀) =>
      exact .cons (ih.A [] done (.up (.down (.imp Q₀ N₀))) seen seen' hle) .nil

/-! # Part 4 · The operator lemma -/

/-- **`stepR id` preserves record monotonicity, `∃p` half.** -/
noncomputable def smStepER (ih : SeenMonoR p prev) :
    ∀ (todo done : List Neg) (seen seen' : SeenR), SeenLe seen seen' →
      Inv [stepR id p prev todo done none seen] [] .tru
          (stepR id p prev todo done none seen') := by
  intro todo done seen seen' hle
  match todo with
  | .up (.atom a) :: todo =>
      exact ih.E todo (.up (.atom a) :: done) seen seen' hle
  | .up .fls :: todo => exact idNeg _ _ (List.mem_cons_self ..)
  | .up (.or P₁ P₂) :: todo =>
      exact nOrAllPW (PW.mapBoth (fun b _ => ih.E (b ++ todo) done seen seen' hle))
  | .up (.down M) :: todo => exact ih.E (M :: todo) done seen seen' hle
  | .and M N :: todo => exact ih.E (M :: N :: todo) done seen seen' hle
  | .imp .fls N :: todo => exact ih.E todo done seen seen' hle
  | .imp (.atom a) N :: todo =>
      exact ih.E todo (.imp (.atom a) N :: done) seen seen' hle
  | .imp (.or Q₁ Q₂) N :: todo =>
      exact ih.E todo (.imp (.or Q₁ Q₂) N :: done) seen seen' hle
  | .imp (.down (.up P')) N :: todo =>
      exact ih.E todo (.imp (.down (.up P')) N :: done) seen seen' hle
  | .imp (.down (.and M₁ M₂)) N :: todo =>
      exact ih.E todo (.imp (.down (.and M₁ M₂)) N :: done) seen seen' hle
  | .imp (.down (.imp Q' N')) N :: todo =>
      exact ih.E todo (.imp (.down (.imp Q' N')) N :: done) seen seen' hle
  | .circ Q :: todo => exact ih.E todo (.circ Q :: done) seen seen' hle
  | .imp (.down (.circ Q')) N :: todo =>
      exact ih.E todo (.imp (.down (.circ Q')) N :: done) seen seen' hle
  | [] =>
      match hfr : findFire done (splits done) with
      | some (a, N, rest) =>
          rw [srFire (rst := id) (p := p) (prev := prev) hfr none seen,
              srFire (rst := id) (p := p) (prev := prev) hfr none seen']
          exact ih.E [N] rest seen seen' hle
      | none =>
          rw [srAgg (rst := id) (p := p) (prev := prev) hfr none seen,
              srAgg (rst := id) (p := p) (prev := prev) hfr none seen',
              aggR_none, aggR_none]
          exact nAndAllPW (smERowsR ih done hle)

/-- **`stepR id` preserves record monotonicity, `∀p` half.** -/
noncomputable def smStepAR (ih : SeenMonoR p prev) :
    ∀ (todo done : List Neg) (G : Neg) (seen seen' : SeenR), SeenLe seen seen' →
      Inv [stepR id p prev todo done (some G) seen'] [] .tru
          (stepR id p prev todo done (some G) seen) := by
  intro todo done G seen seen' hle
  match todo with
  | .up (.atom a) :: todo =>
      exact ih.A todo (.up (.atom a) :: done) G seen seen' hle
  | .up .fls :: todo => exact nTopIntro
  | .up (.or P₁ P₂) :: todo =>
      exact nAndAllPW (PW.mapBoth (fun b _ =>
        impMono (ih.E (b ++ todo) done seen seen' hle)
                (ih.A (b ++ todo) done G seen seen' hle)))
  | .up (.down M) :: todo => exact ih.A (M :: todo) done G seen seen' hle
  | .and M N :: todo => exact ih.A (M :: N :: todo) done G seen seen' hle
  | .imp .fls N :: todo => exact ih.A todo done G seen seen' hle
  | .imp (.atom a) N :: todo =>
      exact ih.A todo (.imp (.atom a) N :: done) G seen seen' hle
  | .imp (.or Q₁ Q₂) N :: todo =>
      exact ih.A todo (.imp (.or Q₁ Q₂) N :: done) G seen seen' hle
  | .imp (.down (.up P')) N :: todo =>
      exact ih.A todo (.imp (.down (.up P')) N :: done) G seen seen' hle
  | .imp (.down (.and M₁ M₂)) N :: todo =>
      exact ih.A todo (.imp (.down (.and M₁ M₂)) N :: done) G seen seen' hle
  | .imp (.down (.imp Q' N')) N :: todo =>
      exact ih.A todo (.imp (.down (.imp Q' N')) N :: done) G seen seen' hle
  | .circ Q :: todo => exact ih.A todo (.circ Q :: done) G seen seen' hle
  | .imp (.down (.circ Q')) N :: todo =>
      exact ih.A todo (.imp (.down (.circ Q')) N :: done) G seen seen' hle
  | [] =>
      match hfr : findFire done (splits done) with
      | some (a, N, rest) =>
          rw [srFire (rst := id) (p := p) (prev := prev) hfr (some G) seen,
              srFire (rst := id) (p := p) (prev := prev) hfr (some G) seen']
          exact ih.A [N] rest G seen seen' hle
      | none =>
          rw [srAgg (rst := id) (p := p) (prev := prev) hfr (some G) seen,
              srAgg (rst := id) (p := p) (prev := prev) hfr (some G) seen']
          match G with
          | .imp Q N =>
              rw [aggR_imp, aggR_imp]
              exact nAndAllPW (PW.mapBoth (fun b _ =>
                impMono (ih.E b done seen seen' hle) (ih.A b done N seen seen' hle)))
          | .and M N =>
              rw [aggR_and, aggR_and]
              exact andMono (ih.A [] done M seen seen' hle)
                            (ih.A [] done N seen seen' hle)
          | .up (.atom q) =>
              by_cases hq : atomMem q done = true
              · rw [aggR_atomT _ hq, aggR_atomT _ hq]; exact nTopIntro
              · rw [aggR_atomF _ hq, aggR_atomF _ hq]
                exact nOrAllPW ((PW.refl (atomHead p q)).append
                  (smARowsR ih done (.up (.atom q)) false hle))
          | .up .fls =>
              rw [aggR_fls, aggR_fls]
              exact nOrAllPW (smARowsR ih done (.up .fls) false hle)
          | .up (.or P₁ P₂) =>
              rw [aggR_or, aggR_or]
              exact nOrAllPW ((PW.cons (ih.A [] done (.up P₁) seen seen' hle)
                (PW.cons (ih.A [] done (.up P₂) seen seen' hle) PW.nil)).append
                  (smARowsR ih done (.up (.or P₁ P₂)) false hle))
          | .up (.down M) =>
              rw [aggR_down, aggR_down]
              exact nOrAllPW ((PW.cons (ih.A [] done M seen seen' hle) PW.nil).append
                (smARowsR ih done (.up (.down M)) false hle))
          | .circ Q =>
              rw [aggR_circ, aggR_circ]
              exact circMono (nOrAllPW ((smLaxPrefixR ih done Q hle).append
                (smARowsR ih done (.circ Q) true hle)))

/-- **The operator lemma**: one fuel level of the pair recursion preserves
record monotonicity. -/
noncomputable def smStepR (ih : SeenMonoR p prev) :
    SeenMonoR p (stepR id p prev) where
  E := smStepER ih
  A := smStepAR ih

end OpR

/-! # Part 5 · Record monotonicity -/

/-- Every fuel level of `interpR` is record-monotone. -/
noncomputable def interpR_seenMonoLvl (p : String) :
    ∀ f, SeenMonoR p (interpR p f)
  | 0 =>
      { E := fun _ _ _ _ _ => nTopIntro
        A := fun _ _ _ _ _ _ => nBotElim _ (List.mem_cons_self ..) }
  | f + 1 => smStepR (interpR_seenMonoLvl p f)

/-- **`∃p` is monotone in the record**: a larger record cuts more conjuncts,
so its `∃p` approximant is weaker. -/
noncomputable def interpR_seenMonoE (p : String) (f : Nat) (todo done : List Neg)
    {seen seen' : SeenR} (hle : SeenLe seen seen') :
    Inv [interpR p f todo done none seen] [] .tru
        (interpR p f todo done none seen') :=
  (interpR_seenMonoLvl p f).E todo done seen seen' hle

/-- **`∀p` is antitone in the record**: a larger record cuts more disjuncts,
so its `∀p` approximant is stronger. -/
noncomputable def interpR_seenMonoA (p : String) (f : Nat) (todo done : List Neg)
    (G : Neg) {seen seen' : SeenR} (hle : SeenLe seen seen') :
    Inv [interpR p f todo done (some G) seen'] [] .tru
        (interpR p f todo done (some G) seen) :=
  (interpR_seenMonoLvl p f).A todo done G seen seen' hle

/-! # Part 6 · The two instances the escape induction uses

The record grows at one place only, the guard call, from `seen` to
`(Qa, done) :: seen`. -/

/-- The `∃p` approximant survives recording one more pair. -/
noncomputable def interpR_seenStepE (p : String) (f : Nat) (todo done : List Neg)
    (e : Pos × List Neg) (seen : SeenR) :
    Inv [interpR p f todo done none seen] [] .tru
        (interpR p f todo done none (e :: seen)) :=
  interpR_seenMonoE p f todo done (seenLe_tail e seen)

/-- The `∀p` approximant at the extended record entails the one below it. -/
noncomputable def interpR_seenStepA (p : String) (f : Nat) (todo done : List Neg)
    (G : Neg) (e : Pos × List Neg) (seen : SeenR) :
    Inv [interpR p f todo done (some G) (e :: seen)] [] .tru
        (interpR p f todo done (some G) seen) :=
  interpR_seenMonoA p f todo done G (seenLe_tail e seen)

end LJFO

/-! ## Pins -/

#axioms_within LJFO.seenLe_cons [propext, Quot.sound]
#axioms_within LJFO.seenLe_tail [propext, Quot.sound]
#axioms_within LJFO.smStepR [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.interpR_seenMonoLvl [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.interpR_seenMonoE [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.interpR_seenMonoA [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.interpR_seenStepE [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.interpR_seenStepA [propext, Classical.choice, Quot.sound]
