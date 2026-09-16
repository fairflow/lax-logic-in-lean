/-
Route (B), node **N4**, WP12b, **stage 3, prerequisite**: **FUEL MONOTONICITY
of the pair-recording recursion `interpR`**.

`wip/ui_routeB_pqmono.lean` (WP11) transcribed.  The statement is the
polarity table read along the FUEL: one more fuel level adds conjuncts to the
`∃p` aggregate and disjuncts to the `∀p` aggregate, so

    E_{f+1}(s | seen)  ⊢  E_f(s | seen)          (`∃p` is antitone in the fuel)
    A_f(s | seen)      ⊢  A_{f+1}(s | seen)      (`∀p` is monotone in the fuel)

at EVERY state, every `seen`, and every reset policy.  The proof is an
induction on the fuel through ONE operator lemma: `stepR` preserves the mixed
-variance relation `StepMonoR`, because each aggregate's rows carry the other
mode in negative position.  Both fuel levels run through the SAME `stepR`, so
the recording test is split on identically on the two sides and the cut rows
match; the sixteen processing clauses are discharged against an abstract
`prev`.

This is what merges the thresholds of independent sub-results inside a
cofinality induction for `interpR` (`docs/ui-ljfo-clause-table.md` §4.28).

`LJF/` is untouched; this module is a leaf.
-/
import wip.ui_routeB_r_sound
import Meta.Audit

set_option autoImplicit false

namespace LJFO

/-! # Part 1 · The operator statement

`StepMonoR rst p prev₁ prev₂` says: `prev₁` is `∃p`-STRONGER and `∀p`-WEAKER
than `prev₂`.  It is the relation the fuel step must preserve. -/

/-- `prev₁` dominates `prev₂`: stronger in `∃p` mode, weaker in `∀p` mode. -/
structure StepMonoR (rst : SeenR → SeenR) (p : String)
    (prev₁ prev₂ : ApproxR) : Type where
  /-- `∃p`: the stronger approximant entails the weaker. -/
  E : ∀ (todo done : List Neg) (seen : SeenR),
        Inv [prev₁ todo done none seen] [] .tru (prev₂ todo done none seen)
  /-- `∀p`: the weaker approximant entails the stronger. -/
  A : ∀ (todo done : List Neg) (G : Neg) (seen : SeenR),
        Inv [prev₂ todo done (some G) seen] [] .tru (prev₁ todo done (some G) seen)

section OpR
variable {rst : SeenR → SeenR} {p : String} {prev₁ prev₂ : ApproxR}

/-! # Part 2 · `stepR`'s own equations, against an abstract approximant

The processing clauses are definitional; only the two aggregate-phase
clauses need their scrutinee named. -/

/-- The fire equation. -/
theorem srFire {prev : ApproxR} {done : List Neg} {a : String} {N : Neg}
    {rest : List Neg} (hf : findFire done (splits done) = some (a, N, rest))
    (g : Option Neg) (seen : SeenR) :
    stepR rst p prev [] done g seen = prev [N] rest g (rst seen) := by
  rw [stepR, hf]

/-- The aggregate equation. -/
theorem srAgg {prev : ApproxR} {done : List Neg} (hsat : Saturated done)
    (g : Option Neg) (seen : SeenR) :
    stepR rst p prev [] done g seen = aggR rst p prev done g seen := by
  rw [stepR, hsat]

/-! # Part 3 · The rows -/

/-- The `∃p` row of a parked compound implication is monotone. -/
noncomputable def monoParkRowER (ih : StepMonoR rst p prev₁ prev₂)
    (done : List Neg) (Qa : Pos) (N : Neg) (rest res : List Neg)
    (seen : SeenR) :
    Inv [parkRowER rst prev₁ done Qa N rest res seen] [] .tru
        (parkRowER rst prev₂ done Qa N rest res seen) := by
  unfold parkRowER
  refine andMono ?_ (ih.E res rest (rst seen))
  by_cases hc : seenMemR seen Qa done = true
  · rw [if_pos hc, if_pos hc]; exact nTopIntro
  · rw [if_neg hc, if_neg hc]
    exact impMono (ih.A [] done (.up Qa) ((Qa, done) :: seen)) (ih.E [N] rest (rst seen))

/-- The `∀p` attack row of a parked compound implication is monotone. -/
noncomputable def monoParkRowAR (ih : StepMonoR rst p prev₁ prev₂)
    (done : List Neg) (Qa : Pos) (N : Neg) (rest : List Neg) (goal : Neg)
    (seen : SeenR) :
    Inv [parkRowAR rst prev₂ done Qa N rest goal seen] [] .tru
        (parkRowAR rst prev₁ done Qa N rest goal seen) := by
  unfold parkRowAR
  by_cases hc : seenMemR seen Qa done = true
  · rw [if_pos hc, if_pos hc]; exact nBotElim _ (List.mem_cons_self ..)
  · rw [if_neg hc, if_neg hc]
    exact andMono (ih.A [] done (.up Qa) ((Qa, done) :: seen))
                  (ih.A [N] rest goal (rst seen))

/-- The `∃p` station rows are monotone, row by row. -/
noncomputable def monoERowsR (ih : StepMonoR rst p prev₁ prev₂) (done : List Neg)
    (seen : SeenR) :
    PW (eRowsR rst p prev₁ done seen) (eRowsR rst p prev₂ done seen) := by
  unfold eRowsR
  refine PW.mapBoth ?_
  rintro ⟨X, rest⟩ -
  match X with
  | .up (.atom a) => exact idNeg _ _ (List.mem_cons_self ..)
  | .imp (.atom a) N =>
      by_cases hap : a = p
      · simp only [pGuard, if_pos hap]; exact nTopIntro
      · simp only [pGuard, if_neg hap]
        exact impMonoAtom (ih.E [N] rest (rst seen))
  | .imp (.down (.imp Q' N')) N =>
      exact monoParkRowER ih done (.down (.imp Q' N')) N rest [.imp (.down N') N] seen
  | .circ Q => exact circMono (ih.E [.up Q] rest (rst seen))
  | .imp (.down (.circ Q')) N =>
      exact monoParkRowER ih done (.down (.circ Q')) N rest [] seen
  | .imp (.or Qa Qb) N => exact monoParkRowER ih done (.or Qa Qb) N rest [] seen
  | .imp (.down (.up Pa)) N =>
      exact monoParkRowER ih done (.down (.up Pa)) N rest [] seen
  | .imp (.down (.and Ma Mb)) N =>
      exact monoParkRowER ih done (.down (.and Ma Mb)) N rest [] seen
  | .up .fls => exact nTopIntro
  | .up (.or _ _) => exact nTopIntro
  | .up (.down _) => exact nTopIntro
  | .imp .fls _ => exact nTopIntro
  | .and _ _ => exact nTopIntro

/-- The `∀p` station rows are monotone, row by row, at every goal and with or
without the box row. -/
noncomputable def monoARowsR (ih : StepMonoR rst p prev₁ prev₂) (done : List Neg)
    (goal : Neg) (box : Bool) (seen : SeenR) :
    PW (aRowsR rst p prev₂ done goal box seen)
       (aRowsR rst p prev₁ done goal box seen) := by
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
                      (ih.A [N] rest goal (rst seen))
  | .imp (.down (.imp Q' N')) N =>
      exact monoParkRowAR ih done (.down (.imp Q' N')) N rest goal seen
  | .imp (.down (.circ Q')) N =>
      exact monoParkRowAR ih done (.down (.circ Q')) N rest goal seen
  | .imp (.or Qa Qb) N => exact monoParkRowAR ih done (.or Qa Qb) N rest goal seen
  | .imp (.down (.up Pa)) N =>
      exact monoParkRowAR ih done (.down (.up Pa)) N rest goal seen
  | .imp (.down (.and Ma Mb)) N =>
      exact monoParkRowAR ih done (.down (.and Ma Mb)) N rest goal seen
  | .circ R =>
      cases box with
      | true =>
          exact impMono (ih.E [.up R] rest (rst seen))
                        (ih.A [.up R] rest goal (rst seen))
      | false => exact nBotElim _ (List.mem_cons_self ..)
  | .up (.atom _) => exact nBotElim _ (List.mem_cons_self ..)
  | .up .fls => exact nBotElim _ (List.mem_cons_self ..)
  | .up (.or _ _) => exact nBotElim _ (List.mem_cons_self ..)
  | .up (.down _) => exact nBotElim _ (List.mem_cons_self ..)
  | .imp .fls _ => exact nBotElim _ (List.mem_cons_self ..)
  | .and _ _ => exact nBotElim _ (List.mem_cons_self ..)

/-- The lax goal-inversion prefix is monotone. -/
noncomputable def monoLaxPrefixR (ih : StepMonoR rst p prev₁ prev₂)
    (done : List Neg) (Q : Pos) (seen : SeenR) :
    PW (laxPrefixR prev₂ done seen Q) (laxPrefixR prev₁ done seen Q) := by
  match Q with
  | .atom q => exact .cons (ih.A [] done (.up (.atom q)) seen) .nil
  | .fls => exact .cons (ih.A [] done (.up .fls) seen) .nil
  | .or P₁ P₂ =>
      exact .cons (ih.A [] done (.circ P₁) seen)
        (.cons (ih.A [] done (.circ P₂) seen)
          (.cons (ih.A [] done (.up (.or P₁ P₂)) seen) .nil))
  | .down (.up P') => exact .cons (ih.A [] done (.circ P') seen) .nil
  | .down (.circ P') => exact .cons (ih.A [] done (.circ P') seen) .nil
  | .down (.and M₁ M₂) =>
      exact .cons (ih.A [] done (.up (.down (.and M₁ M₂))) seen) .nil
  | .down (.imp Q₀ N₀) =>
      exact .cons (ih.A [] done (.up (.down (.imp Q₀ N₀))) seen) .nil

/-! # Part 4 · The operator lemma -/

/-- **`stepR` preserves domination, `∃p` half.** -/
noncomputable def monoStepER (ih : StepMonoR rst p prev₁ prev₂) :
    ∀ (todo done : List Neg) (seen : SeenR),
      Inv [stepR rst p prev₁ todo done none seen] [] .tru
          (stepR rst p prev₂ todo done none seen) := by
  intro todo done seen
  match todo with
  | .up (.atom a) :: todo => exact ih.E todo (.up (.atom a) :: done) (rst seen)
  | .up .fls :: todo => exact idNeg _ _ (List.mem_cons_self ..)
  | .up (.or P₁ P₂) :: todo =>
      exact nOrAllPW (PW.mapBoth (fun b _ => ih.E (b ++ todo) done (rst seen)))
  | .up (.down M) :: todo => exact ih.E (M :: todo) done (rst seen)
  | .and M N :: todo => exact ih.E (M :: N :: todo) done (rst seen)
  | .imp .fls N :: todo => exact ih.E todo done (rst seen)
  | .imp (.atom a) N :: todo =>
      exact ih.E todo (.imp (.atom a) N :: done) (rst seen)
  | .imp (.or Q₁ Q₂) N :: todo =>
      exact ih.E todo (.imp (.or Q₁ Q₂) N :: done) (rst seen)
  | .imp (.down (.up P')) N :: todo =>
      exact ih.E todo (.imp (.down (.up P')) N :: done) (rst seen)
  | .imp (.down (.and M₁ M₂)) N :: todo =>
      exact ih.E todo (.imp (.down (.and M₁ M₂)) N :: done) (rst seen)
  | .imp (.down (.imp Q' N')) N :: todo =>
      exact ih.E todo (.imp (.down (.imp Q' N')) N :: done) (rst seen)
  | .circ Q :: todo => exact ih.E todo (.circ Q :: done) (rst seen)
  | .imp (.down (.circ Q')) N :: todo =>
      exact ih.E todo (.imp (.down (.circ Q')) N :: done) (rst seen)
  | [] =>
      match hfr : findFire done (splits done) with
      | some (a, N, rest) =>
          rw [srFire (rst := rst) (p := p) (prev := prev₁) hfr none seen,
              srFire (rst := rst) (p := p) (prev := prev₂) hfr none seen]
          exact ih.E [N] rest (rst seen)
      | none =>
          rw [srAgg (rst := rst) (p := p) (prev := prev₁) hfr none seen,
              srAgg (rst := rst) (p := p) (prev := prev₂) hfr none seen,
              aggR_none, aggR_none]
          exact nAndAllPW (monoERowsR ih done seen)

/-- **`stepR` preserves domination, `∀p` half.** -/
noncomputable def monoStepAR (ih : StepMonoR rst p prev₁ prev₂) :
    ∀ (todo done : List Neg) (G : Neg) (seen : SeenR),
      Inv [stepR rst p prev₂ todo done (some G) seen] [] .tru
          (stepR rst p prev₁ todo done (some G) seen) := by
  intro todo done G seen
  match todo with
  | .up (.atom a) :: todo => exact ih.A todo (.up (.atom a) :: done) G (rst seen)
  | .up .fls :: todo => exact nTopIntro
  | .up (.or P₁ P₂) :: todo =>
      exact nAndAllPW (PW.mapBoth (fun b _ =>
        impMono (ih.E (b ++ todo) done (rst seen))
                (ih.A (b ++ todo) done G (rst seen))))
  | .up (.down M) :: todo => exact ih.A (M :: todo) done G (rst seen)
  | .and M N :: todo => exact ih.A (M :: N :: todo) done G (rst seen)
  | .imp .fls N :: todo => exact ih.A todo done G (rst seen)
  | .imp (.atom a) N :: todo =>
      exact ih.A todo (.imp (.atom a) N :: done) G (rst seen)
  | .imp (.or Q₁ Q₂) N :: todo =>
      exact ih.A todo (.imp (.or Q₁ Q₂) N :: done) G (rst seen)
  | .imp (.down (.up P')) N :: todo =>
      exact ih.A todo (.imp (.down (.up P')) N :: done) G (rst seen)
  | .imp (.down (.and M₁ M₂)) N :: todo =>
      exact ih.A todo (.imp (.down (.and M₁ M₂)) N :: done) G (rst seen)
  | .imp (.down (.imp Q' N')) N :: todo =>
      exact ih.A todo (.imp (.down (.imp Q' N')) N :: done) G (rst seen)
  | .circ Q :: todo => exact ih.A todo (.circ Q :: done) G (rst seen)
  | .imp (.down (.circ Q')) N :: todo =>
      exact ih.A todo (.imp (.down (.circ Q')) N :: done) G (rst seen)
  | [] =>
      match hfr : findFire done (splits done) with
      | some (a, N, rest) =>
          rw [srFire (rst := rst) (p := p) (prev := prev₁) hfr (some G) seen,
              srFire (rst := rst) (p := p) (prev := prev₂) hfr (some G) seen]
          exact ih.A [N] rest G (rst seen)
      | none =>
          rw [srAgg (rst := rst) (p := p) (prev := prev₁) hfr (some G) seen,
              srAgg (rst := rst) (p := p) (prev := prev₂) hfr (some G) seen]
          match G with
          | .imp Q N =>
              rw [aggR_imp, aggR_imp]
              exact nAndAllPW (PW.mapBoth (fun b _ =>
                impMono (ih.E b done seen) (ih.A b done N seen)))
          | .and M N =>
              rw [aggR_and, aggR_and]
              exact andMono (ih.A [] done M seen) (ih.A [] done N seen)
          | .up (.atom q) =>
              by_cases hq : atomMem q done = true
              · rw [aggR_atomT _ hq, aggR_atomT _ hq]; exact nTopIntro
              · rw [aggR_atomF _ hq, aggR_atomF _ hq]
                exact nOrAllPW ((PW.refl (atomHead p q)).append
                  (monoARowsR ih done (.up (.atom q)) false seen))
          | .up .fls =>
              rw [aggR_fls, aggR_fls]
              exact nOrAllPW (monoARowsR ih done (.up .fls) false seen)
          | .up (.or P₁ P₂) =>
              rw [aggR_or, aggR_or]
              exact nOrAllPW ((PW.cons (ih.A [] done (.up P₁) seen)
                (PW.cons (ih.A [] done (.up P₂) seen) PW.nil)).append
                  (monoARowsR ih done (.up (.or P₁ P₂)) false seen))
          | .up (.down M) =>
              rw [aggR_down, aggR_down]
              exact nOrAllPW ((PW.cons (ih.A [] done M seen) PW.nil).append
                (monoARowsR ih done (.up (.down M)) false seen))
          | .circ Q =>
              rw [aggR_circ, aggR_circ]
              exact circMono (nOrAllPW ((monoLaxPrefixR ih done Q seen).append
                (monoARowsR ih done (.circ Q) true seen)))

/-- **The operator lemma**: one fuel level of the loop-checked recursion
preserves domination. -/
noncomputable def monoStepR (ih : StepMonoR rst p prev₁ prev₂) :
    StepMonoR rst p (stepR rst p prev₁) (stepR rst p prev₂) where
  E := monoStepER ih
  A := monoStepAR ih

end OpR

/-! # Part 5 · Fuel monotonicity -/

/-- **Each fuel level dominates the one below.** -/
noncomputable def interpGR_monoLvl (rst : SeenR → SeenR) (p : String) :
    ∀ f, StepMonoR rst p (interpGR rst p (f + 1)) (interpGR rst p f)
  | 0 =>
      { E := fun _ _ _ => nTopIntro
        A := fun _ _ _ _ => nBotElim _ (List.mem_cons_self ..) }
  | f + 1 => monoStepR (interpGR_monoLvl rst p f)

/-- **`∃p` is antitone in the fuel**, at every state, every `seen` and every
reset policy. -/
noncomputable def interpGR_monoE (rst : SeenR → SeenR) (p : String)
    (f : Nat) (todo done : List Neg) (seen : SeenR) :
    Inv [interpGR rst p (f + 1) todo done none seen] [] .tru
        (interpGR rst p f todo done none seen) :=
  (interpGR_monoLvl rst p f).E todo done seen

/-- **`∀p` is monotone in the fuel**, at every state, every `seen` and every
reset policy. -/
noncomputable def interpGR_monoA (rst : SeenR → SeenR) (p : String)
    (f : Nat) (todo done : List Neg) (G : Neg) (seen : SeenR) :
    Inv [interpGR rst p f todo done (some G) seen] [] .tru
        (interpGR rst p (f + 1) todo done (some G) seen) :=
  (interpGR_monoLvl rst p f).A todo done G seen

/-- `∃p`, any number of fuel levels. -/
noncomputable def interpGR_monoE_add (rst : SeenR → SeenR) (p : String)
    (f : Nat) : ∀ (k : Nat) (todo done : List Neg) (seen : SeenR),
      Inv [interpGR rst p (f + k) todo done none seen] [] .tru
          (interpGR rst p f todo done none seen)
  | 0, _, _, _ => idNeg _ _ (List.mem_cons_self ..)
  | k + 1, todo, done, seen =>
      cut1N (interpGR_monoE rst p (f + k) todo done seen)
            (interpGR_monoE_add rst p f k todo done seen)

/-- `∀p`, any number of fuel levels. -/
noncomputable def interpGR_monoA_add (rst : SeenR → SeenR) (p : String)
    (f : Nat) : ∀ (k : Nat) (todo done : List Neg) (G : Neg) (seen : SeenR),
      Inv [interpGR rst p f todo done (some G) seen] [] .tru
          (interpGR rst p (f + k) todo done (some G) seen)
  | 0, _, _, _, _ => idNeg _ _ (List.mem_cons_self ..)
  | k + 1, todo, done, G, seen =>
      cut1N (interpGR_monoA_add rst p f k todo done G seen)
            (interpGR_monoA rst p (f + k) todo done G seen)

/-! # Part 6 · The instances the route uses -/

/-- `E^Q` is antitone in the fuel. -/
noncomputable def interpR_monoE (p : String) (f : Nat) (todo done : List Neg)
    (seen : SeenR) :
    Inv [interpR p (f + 1) todo done none seen] [] .tru
        (interpR p f todo done none seen) :=
  interpGR_monoE id p f todo done seen

/-- `A^Q` is monotone in the fuel — the lemma the `∀p` hard half needs at the
guard state, where the self-attack row of `interpP` is the same state ONE
FUEL DOWN. -/
noncomputable def interpR_monoA (p : String) (f : Nat) (todo done : List Neg)
    (G : Neg) (seen : SeenR) :
    Inv [interpR p f todo done (some G) seen] [] .tru
        (interpR p (f + 1) todo done (some G) seen) :=
  interpGR_monoA id p f todo done G seen

end LJFO

/-! ## Pins -/

#axioms_within LJFO.monoStepR [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.interpGR_monoLvl [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.interpGR_monoE [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.interpGR_monoA [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.interpGR_monoE_add [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.interpGR_monoA_add [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.interpR_monoE [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.interpR_monoA [propext, Classical.choice, Quot.sound]
