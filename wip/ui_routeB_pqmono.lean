/-
Route (B), node **N4**, WP11, Stage 1: **FUEL MONOTONICITY of the
loop-checked recursion `interpG`** (`wip/ui_routeB_n4q.lean`).

No lemma of this kind existed in the development.  The statement is the
polarity table of `docs/n4-loopcheck.md` §3 read along the FUEL rather than
along the loop check: one more fuel level adds conjuncts to the `∃p`
aggregate and disjuncts to the `∀p` aggregate, so

    E_{f+1}(s | seen)  ⊢  E_f(s | seen)          (`∃p` is antitone in the fuel)
    A_f(s | seen)      ⊢  A_{f+1}(s | seen)      (`∀p` is monotone in the fuel)

at EVERY state `s = (todo, done, g)`, every `seen`, and every reset policy
`rst` — hence for `interpQ = interpG id` and for `interpQ0`.

The proof is an induction on the fuel through ONE operator lemma: `stepQ` is
monotone in its approximant argument, in the mixed-variance sense that the
two halves are ONE simultaneous statement (`StepMono`), because each
aggregate's rows carry the other mode in NEGATIVE position.  Both fuel levels
run through the SAME `stepQ`, so — unlike the easy halves of
`wip/ui_routeB_pqequiv.lean`, which compare two different recursions — every
row transfers pointwise and the sixteen processing clauses are discharged
against an abstract `prev`.

`LJF/` is untouched; this module is a leaf.
-/
import wip.ui_routeB_pqequiv
import Meta.Audit

set_option autoImplicit false

namespace LJFO

/-! # Part 1 · The operator statement

`StepMono rst p prev₁ prev₂` says: `prev₁` is `∃p`-STRONGER and `∀p`-WEAKER
than `prev₂`.  It is the relation the fuel step must preserve. -/

/-- `prev₁` dominates `prev₂`: stronger in `∃p` mode, weaker in `∀p` mode. -/
structure StepMono (rst : List Pos → List Pos) (p : String)
    (prev₁ prev₂ : ApproxQ) : Type where
  /-- `∃p`: the stronger approximant entails the weaker. -/
  E : ∀ (todo done : List Neg) (seen : List Pos),
        Inv [prev₁ todo done none seen] [] .tru (prev₂ todo done none seen)
  /-- `∀p`: the weaker approximant entails the stronger. -/
  A : ∀ (todo done : List Neg) (G : Neg) (seen : List Pos),
        Inv [prev₂ todo done (some G) seen] [] .tru (prev₁ todo done (some G) seen)

section Op
variable {rst : List Pos → List Pos} {p : String} {prev₁ prev₂ : ApproxQ}

/-! # Part 2 · `stepQ`'s own equations, against an abstract approximant

The processing clauses are definitional; only the two aggregate-phase
clauses need their scrutinee named. -/

/-- The fire equation. -/
theorem sqFire {prev : ApproxQ} {done : List Neg} {a : String} {N : Neg}
    {rest : List Neg} (hf : findFire done (splits done) = some (a, N, rest))
    (g : Option Neg) (seen : List Pos) :
    stepQ rst p prev [] done g seen = prev [N] rest g (rst seen) := by
  rw [stepQ, hf]

/-- The aggregate equation. -/
theorem sqAgg {prev : ApproxQ} {done : List Neg} (hsat : Saturated done)
    (g : Option Neg) (seen : List Pos) :
    stepQ rst p prev [] done g seen = aggQ rst p prev done g seen := by
  rw [stepQ, hsat]

/-! # Part 3 · The rows -/

/-- The `∃p` row of a parked compound implication is monotone. -/
noncomputable def monoParkRowE (ih : StepMono rst p prev₁ prev₂)
    (done : List Neg) (Qa : Pos) (N : Neg) (rest res : List Neg)
    (seen : List Pos) :
    Inv [parkRowE rst prev₁ done Qa N rest res seen] [] .tru
        (parkRowE rst prev₂ done Qa N rest res seen) := by
  unfold parkRowE
  refine andMono ?_ (ih.E res rest (rst seen))
  by_cases hc : seenMem seen Qa = true
  · rw [if_pos hc, if_pos hc]; exact nTopIntro
  · rw [if_neg hc, if_neg hc]
    exact impMono (ih.A [] done (.up Qa) (Qa :: seen)) (ih.E [N] rest (rst seen))

/-- The `∀p` attack row of a parked compound implication is monotone. -/
noncomputable def monoParkRowA (ih : StepMono rst p prev₁ prev₂)
    (done : List Neg) (Qa : Pos) (N : Neg) (rest : List Neg) (goal : Neg)
    (seen : List Pos) :
    Inv [parkRowA rst prev₂ done Qa N rest goal seen] [] .tru
        (parkRowA rst prev₁ done Qa N rest goal seen) := by
  unfold parkRowA
  by_cases hc : seenMem seen Qa = true
  · rw [if_pos hc, if_pos hc]; exact nBotElim _ (List.mem_cons_self ..)
  · rw [if_neg hc, if_neg hc]
    exact andMono (ih.A [] done (.up Qa) (Qa :: seen))
                  (ih.A [N] rest goal (rst seen))

/-- The `∃p` station rows are monotone, row by row. -/
noncomputable def monoERows (ih : StepMono rst p prev₁ prev₂) (done : List Neg)
    (seen : List Pos) :
    PW (eRowsQ rst p prev₁ done seen) (eRowsQ rst p prev₂ done seen) := by
  unfold eRowsQ
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
      exact monoParkRowE ih done (.down (.imp Q' N')) N rest [.imp (.down N') N] seen
  | .circ Q => exact circMono (ih.E [.up Q] rest (rst seen))
  | .imp (.down (.circ Q')) N =>
      exact monoParkRowE ih done (.down (.circ Q')) N rest [] seen
  | .imp (.or Qa Qb) N => exact monoParkRowE ih done (.or Qa Qb) N rest [] seen
  | .imp (.down (.up Pa)) N =>
      exact monoParkRowE ih done (.down (.up Pa)) N rest [] seen
  | .imp (.down (.and Ma Mb)) N =>
      exact monoParkRowE ih done (.down (.and Ma Mb)) N rest [] seen
  | .up .fls => exact nTopIntro
  | .up (.or _ _) => exact nTopIntro
  | .up (.down _) => exact nTopIntro
  | .imp .fls _ => exact nTopIntro
  | .and _ _ => exact nTopIntro

/-- The `∀p` station rows are monotone, row by row, at every goal and with or
without the box row. -/
noncomputable def monoARows (ih : StepMono rst p prev₁ prev₂) (done : List Neg)
    (goal : Neg) (box : Bool) (seen : List Pos) :
    PW (aRowsQ rst p prev₂ done goal box seen)
       (aRowsQ rst p prev₁ done goal box seen) := by
  unfold aRowsQ
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
      exact monoParkRowA ih done (.down (.imp Q' N')) N rest goal seen
  | .imp (.down (.circ Q')) N =>
      exact monoParkRowA ih done (.down (.circ Q')) N rest goal seen
  | .imp (.or Qa Qb) N => exact monoParkRowA ih done (.or Qa Qb) N rest goal seen
  | .imp (.down (.up Pa)) N =>
      exact monoParkRowA ih done (.down (.up Pa)) N rest goal seen
  | .imp (.down (.and Ma Mb)) N =>
      exact monoParkRowA ih done (.down (.and Ma Mb)) N rest goal seen
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
noncomputable def monoLaxPrefix (ih : StepMono rst p prev₁ prev₂)
    (done : List Neg) (Q : Pos) (seen : List Pos) :
    PW (laxPrefixQ prev₂ done seen Q) (laxPrefixQ prev₁ done seen Q) := by
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

/-- **`stepQ` preserves domination, `∃p` half.** -/
noncomputable def monoStepE (ih : StepMono rst p prev₁ prev₂) :
    ∀ (todo done : List Neg) (seen : List Pos),
      Inv [stepQ rst p prev₁ todo done none seen] [] .tru
          (stepQ rst p prev₂ todo done none seen) := by
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
          rw [sqFire (rst := rst) (p := p) (prev := prev₁) hfr none seen,
              sqFire (rst := rst) (p := p) (prev := prev₂) hfr none seen]
          exact ih.E [N] rest (rst seen)
      | none =>
          rw [sqAgg (rst := rst) (p := p) (prev := prev₁) hfr none seen,
              sqAgg (rst := rst) (p := p) (prev := prev₂) hfr none seen,
              aggQ_none, aggQ_none]
          exact nAndAllPW (monoERows ih done seen)

/-- **`stepQ` preserves domination, `∀p` half.** -/
noncomputable def monoStepA (ih : StepMono rst p prev₁ prev₂) :
    ∀ (todo done : List Neg) (G : Neg) (seen : List Pos),
      Inv [stepQ rst p prev₂ todo done (some G) seen] [] .tru
          (stepQ rst p prev₁ todo done (some G) seen) := by
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
          rw [sqFire (rst := rst) (p := p) (prev := prev₁) hfr (some G) seen,
              sqFire (rst := rst) (p := p) (prev := prev₂) hfr (some G) seen]
          exact ih.A [N] rest G (rst seen)
      | none =>
          rw [sqAgg (rst := rst) (p := p) (prev := prev₁) hfr (some G) seen,
              sqAgg (rst := rst) (p := p) (prev := prev₂) hfr (some G) seen]
          match G with
          | .imp Q N =>
              rw [aggQ_imp, aggQ_imp]
              exact nAndAllPW (PW.mapBoth (fun b _ =>
                impMono (ih.E b done seen) (ih.A b done N seen)))
          | .and M N =>
              rw [aggQ_and, aggQ_and]
              exact andMono (ih.A [] done M seen) (ih.A [] done N seen)
          | .up (.atom q) =>
              by_cases hq : atomMem q done = true
              · rw [aggQ_atomT _ hq, aggQ_atomT _ hq]; exact nTopIntro
              · rw [aggQ_atomF _ hq, aggQ_atomF _ hq]
                exact nOrAllPW ((PW.refl (atomHead p q)).append
                  (monoARows ih done (.up (.atom q)) false seen))
          | .up .fls =>
              rw [aggQ_fls, aggQ_fls]
              exact nOrAllPW (monoARows ih done (.up .fls) false seen)
          | .up (.or P₁ P₂) =>
              rw [aggQ_or, aggQ_or]
              exact nOrAllPW ((PW.cons (ih.A [] done (.up P₁) seen)
                (PW.cons (ih.A [] done (.up P₂) seen) PW.nil)).append
                  (monoARows ih done (.up (.or P₁ P₂)) false seen))
          | .up (.down M) =>
              rw [aggQ_down, aggQ_down]
              exact nOrAllPW ((PW.cons (ih.A [] done M seen) PW.nil).append
                (monoARows ih done (.up (.down M)) false seen))
          | .circ Q =>
              rw [aggQ_circ, aggQ_circ]
              exact circMono (nOrAllPW ((monoLaxPrefix ih done Q seen).append
                (monoARows ih done (.circ Q) true seen)))

/-- **The operator lemma**: one fuel level of the loop-checked recursion
preserves domination. -/
noncomputable def monoStep (ih : StepMono rst p prev₁ prev₂) :
    StepMono rst p (stepQ rst p prev₁) (stepQ rst p prev₂) where
  E := monoStepE ih
  A := monoStepA ih

end Op

/-! # Part 5 · Fuel monotonicity -/

/-- **Each fuel level dominates the one below.** -/
noncomputable def interpG_monoLvl (rst : List Pos → List Pos) (p : String) :
    ∀ f, StepMono rst p (interpG rst p (f + 1)) (interpG rst p f)
  | 0 =>
      { E := fun _ _ _ => nTopIntro
        A := fun _ _ _ _ => nBotElim _ (List.mem_cons_self ..) }
  | f + 1 => monoStep (interpG_monoLvl rst p f)

/-- **`∃p` is antitone in the fuel**, at every state, every `seen` and every
reset policy. -/
noncomputable def interpG_monoE (rst : List Pos → List Pos) (p : String)
    (f : Nat) (todo done : List Neg) (seen : List Pos) :
    Inv [interpG rst p (f + 1) todo done none seen] [] .tru
        (interpG rst p f todo done none seen) :=
  (interpG_monoLvl rst p f).E todo done seen

/-- **`∀p` is monotone in the fuel**, at every state, every `seen` and every
reset policy. -/
noncomputable def interpG_monoA (rst : List Pos → List Pos) (p : String)
    (f : Nat) (todo done : List Neg) (G : Neg) (seen : List Pos) :
    Inv [interpG rst p f todo done (some G) seen] [] .tru
        (interpG rst p (f + 1) todo done (some G) seen) :=
  (interpG_monoLvl rst p f).A todo done G seen

/-- `∃p`, any number of fuel levels. -/
noncomputable def interpG_monoE_add (rst : List Pos → List Pos) (p : String)
    (f : Nat) : ∀ (k : Nat) (todo done : List Neg) (seen : List Pos),
      Inv [interpG rst p (f + k) todo done none seen] [] .tru
          (interpG rst p f todo done none seen)
  | 0, _, _, _ => idNeg _ _ (List.mem_cons_self ..)
  | k + 1, todo, done, seen =>
      cut1N (interpG_monoE rst p (f + k) todo done seen)
            (interpG_monoE_add rst p f k todo done seen)

/-- `∀p`, any number of fuel levels. -/
noncomputable def interpG_monoA_add (rst : List Pos → List Pos) (p : String)
    (f : Nat) : ∀ (k : Nat) (todo done : List Neg) (G : Neg) (seen : List Pos),
      Inv [interpG rst p f todo done (some G) seen] [] .tru
          (interpG rst p (f + k) todo done (some G) seen)
  | 0, _, _, _, _ => idNeg _ _ (List.mem_cons_self ..)
  | k + 1, todo, done, G, seen =>
      cut1N (interpG_monoA_add rst p f k todo done G seen)
            (interpG_monoA rst p (f + k) todo done G seen)

/-! # Part 6 · The instances the route uses -/

/-- `E^Q` is antitone in the fuel. -/
noncomputable def interpQ_monoE (p : String) (f : Nat) (todo done : List Neg)
    (seen : List Pos) :
    Inv [interpQ p (f + 1) todo done none seen] [] .tru
        (interpQ p f todo done none seen) :=
  interpG_monoE id p f todo done seen

/-- `A^Q` is monotone in the fuel — the lemma the `∀p` hard half needs at the
guard state, where the self-attack row of `interpP` is the same state ONE
FUEL DOWN. -/
noncomputable def interpQ_monoA (p : String) (f : Nat) (todo done : List Neg)
    (G : Neg) (seen : List Pos) :
    Inv [interpQ p f todo done (some G) seen] [] .tru
        (interpQ p (f + 1) todo done (some G) seen) :=
  interpG_monoA id p f todo done G seen

/-! # Part 7 · Fuel monotonicity for `interpP`

The same statement for the UNCHECKED recursion.  The route needs it wherever
a hypothesis built at one fuel is consumed at another — in particular the
dropped conjunct `↓A^P(done ⇒ ↑Q′) ⊃ E^P(N :: rest)` of
`docs/pqequiv-cases.md` §3 is ANTITONE in the fuel, by exactly these two
halves, so recording it once at the fuel of its recording site serves every
lower fuel.  `interpP` has no `step` function, so the sixteen processing
clauses are unfolded on both sides through `LJF/OFuelPMin.lean`'s named
equations. -/

/-- One fuel level of `interpP` dominates the one below. -/
structure MonoP (p : String) (f : Nat) : Type where
  /-- `∃p` is antitone in the fuel. -/
  E : ∀ (todo done : List Neg),
        Inv [interpP p (f + 1) todo done none] [] .tru (interpP p f todo done none)
  /-- `∀p` is monotone in the fuel. -/
  A : ∀ (todo done : List Neg) (G : Neg),
        Inv [interpP p f todo done (some G)] [] .tru
            (interpP p (f + 1) todo done (some G))

/-- Fuel 0: the defaults. -/
def monoP_zero (p : String) : MonoP p 0 where
  E := fun _ _ => nTopIntro
  A := fun _ _ _ => nBotElim _ (List.mem_cons_self ..)

section StepP
variable {p : String} {f : Nat}

/-- The `∃p` station rows are antitone in the fuel. -/
noncomputable def monoPERows (ih : MonoP p f) (done : List Neg) :
    PW (eConjRowsP p (f + 1) done) (eConjRowsP p f done) := by
  unfold eConjRowsP
  refine PW.mapBoth ?_
  rintro ⟨⟨X, rest⟩, hXr⟩ -
  match X with
  | .up (.atom a) => exact idNeg _ _ (List.mem_cons_self ..)
  | .imp (.atom a) N =>
      by_cases hap : a = p
      · simp only [pGuard, if_pos hap]; exact nTopIntro
      · simp only [pGuard, if_neg hap]
        exact impMonoAtom (ih.E [N] rest)
  | .imp (.down (.imp Q' N')) N =>
      exact andMono
        (impMono (ih.A [] done (.up (.down (.imp Q' N')))) (ih.E [N] rest))
        (ih.E [.imp (.down N') N] rest)
  | .circ Q => exact circMono (ih.E [.up Q] rest)
  | .imp (.down (.circ Q')) N =>
      exact andMono
        (impMono (ih.A [] done (.up (.down (.circ Q')))) (ih.E [N] rest))
        (ih.E [] rest)
  | .imp (.or Qa Qb) N =>
      exact andMono
        (impMono (ih.A [] done (.up (.or Qa Qb))) (ih.E [N] rest))
        (ih.E [] rest)
  | .imp (.down (.up Pa)) N =>
      exact andMono
        (impMono (ih.A [] done (.up (.down (.up Pa)))) (ih.E [N] rest))
        (ih.E [] rest)
  | .imp (.down (.and Ma Mb)) N =>
      exact andMono
        (impMono (ih.A [] done (.up (.down (.and Ma Mb)))) (ih.E [N] rest))
        (ih.E [] rest)
  | .up .fls => exact nTopIntro
  | .up (.or _ _) => exact nTopIntro
  | .up (.down _) => exact nTopIntro
  | .imp .fls _ => exact nTopIntro
  | .and _ _ => exact nTopIntro

/-- The `∀p` station rows at a shifted goal are monotone in the fuel. -/
noncomputable def monoPTruRows (ih : MonoP p f) (done : List Neg) (G : Pos) :
    PW (truStationRowsP p f done G) (truStationRowsP p (f + 1) done G) := by
  unfold truStationRowsP
  refine PW.mapBoth ?_
  rintro ⟨⟨X, rest⟩, hXr⟩ -
  match X with
  | .imp (.atom a) N =>
      by_cases hap : a = p
      · simp only [pGuard, if_pos hap]
        exact nBotElim _ (List.mem_cons_self ..)
      · simp only [pGuard, if_neg hap]
        exact andMono (idNeg _ _ (List.mem_cons_self ..))
                      (ih.A [N] rest (.up G))
  | .imp (.down (.imp Q' N')) N =>
      exact andMono (ih.A [] done (.up (.down (.imp Q' N'))))
                    (ih.A [N] rest (.up G))
  | .imp (.down (.circ Q')) N =>
      exact andMono (ih.A [] done (.up (.down (.circ Q'))))
                    (ih.A [N] rest (.up G))
  | .imp (.or Qa Qb) N =>
      exact andMono (ih.A [] done (.up (.or Qa Qb))) (ih.A [N] rest (.up G))
  | .imp (.down (.up Pa)) N =>
      exact andMono (ih.A [] done (.up (.down (.up Pa))))
                    (ih.A [N] rest (.up G))
  | .imp (.down (.and Ma Mb)) N =>
      exact andMono (ih.A [] done (.up (.down (.and Ma Mb))))
                    (ih.A [N] rest (.up G))
  | .circ R => exact nBotElim _ (List.mem_cons_self ..)
  | .up (.atom _) => exact nBotElim _ (List.mem_cons_self ..)
  | .up .fls => exact nBotElim _ (List.mem_cons_self ..)
  | .up (.or _ _) => exact nBotElim _ (List.mem_cons_self ..)
  | .up (.down _) => exact nBotElim _ (List.mem_cons_self ..)
  | .imp .fls _ => exact nBotElim _ (List.mem_cons_self ..)
  | .and _ _ => exact nBotElim _ (List.mem_cons_self ..)

/-- The `∀p` station rows at a ◯-goal are monotone in the fuel. -/
noncomputable def monoPCircRows (ih : MonoP p f) (done : List Neg) (G : Pos) :
    PW (circStationRowsP p f done G) (circStationRowsP p (f + 1) done G) := by
  unfold circStationRowsP
  refine PW.mapBoth ?_
  rintro ⟨⟨X, rest⟩, hXr⟩ -
  match X with
  | .imp (.atom a) N =>
      by_cases hap : a = p
      · simp only [pGuard, if_pos hap]
        exact nBotElim _ (List.mem_cons_self ..)
      · simp only [pGuard, if_neg hap]
        exact andMono (idNeg _ _ (List.mem_cons_self ..))
                      (ih.A [N] rest (.circ G))
  | .imp (.down (.imp Q' N')) N =>
      exact andMono (ih.A [] done (.up (.down (.imp Q' N'))))
                    (ih.A [N] rest (.circ G))
  | .imp (.down (.circ Q')) N =>
      exact andMono (ih.A [] done (.up (.down (.circ Q'))))
                    (ih.A [N] rest (.circ G))
  | .imp (.or Qa Qb) N =>
      exact andMono (ih.A [] done (.up (.or Qa Qb))) (ih.A [N] rest (.circ G))
  | .imp (.down (.up Pa)) N =>
      exact andMono (ih.A [] done (.up (.down (.up Pa))))
                    (ih.A [N] rest (.circ G))
  | .imp (.down (.and Ma Mb)) N =>
      exact andMono (ih.A [] done (.up (.down (.and Ma Mb))))
                    (ih.A [N] rest (.circ G))
  | .circ R =>
      exact impMono (ih.E [.up R] rest) (ih.A [.up R] rest (.circ G))
  | .up (.atom _) => exact nBotElim _ (List.mem_cons_self ..)
  | .up .fls => exact nBotElim _ (List.mem_cons_self ..)
  | .up (.or _ _) => exact nBotElim _ (List.mem_cons_self ..)
  | .up (.down _) => exact nBotElim _ (List.mem_cons_self ..)
  | .imp .fls _ => exact nBotElim _ (List.mem_cons_self ..)
  | .and _ _ => exact nBotElim _ (List.mem_cons_self ..)

/-- The lax goal-inversion prefix is monotone in the fuel. -/
noncomputable def monoPLaxPrefix (ih : MonoP p f) (done : List Neg) (Q : Pos) :
    PW (laxPrefixP p f done Q) (laxPrefixP p (f + 1) done Q) := by
  match Q with
  | .atom q => exact .cons (ih.A [] done (.up (.atom q))) .nil
  | .fls => exact .cons (ih.A [] done (.up .fls)) .nil
  | .or P₁ P₂ =>
      exact .cons (ih.A [] done (.circ P₁))
        (.cons (ih.A [] done (.circ P₂))
          (.cons (ih.A [] done (.up (.or P₁ P₂))) .nil))
  | .down (.up P') => exact .cons (ih.A [] done (.circ P')) .nil
  | .down (.circ P') => exact .cons (ih.A [] done (.circ P')) .nil
  | .down (.and M₁ M₂) =>
      exact .cons (ih.A [] done (.up (.down (.and M₁ M₂)))) .nil
  | .down (.imp Q₀ N₀) =>
      exact .cons (ih.A [] done (.up (.down (.imp Q₀ N₀)))) .nil

/-- **`∃p` antitone, one fuel up.** -/
noncomputable def monoPE_succ (ih : MonoP p f) (todo done : List Neg) :
    Inv [interpP p (f + 1 + 1) todo done none] [] .tru
        (interpP p (f + 1) todo done none) := by
  match todo with
  | .up (.atom a) :: todo =>
      rw [show interpP p (f + 1 + 1) (.up (.atom a) :: todo) done none
            = interpP p (f + 1) todo (.up (.atom a) :: done) none from by rw [interpP],
          show interpP p (f + 1) (.up (.atom a) :: todo) done none
            = interpP p f todo (.up (.atom a) :: done) none from by rw [interpP]]
      exact ih.E _ _
  | .up .fls :: todo =>
      rw [show interpP p (f + 1 + 1) (.up .fls :: todo) done none = nBot from by rw [interpP],
          show interpP p (f + 1) (.up .fls :: todo) done none = nBot from by rw [interpP]]
      exact idNeg _ _ (List.mem_cons_self ..)
  | .up (.or P₁ P₂) :: todo =>
      rw [show interpP p (f + 1 + 1) (.up (.or P₁ P₂) :: todo) done none
            = nOrAll ((invertPos (Pos.or P₁ P₂)).attach.map
                (fun b => interpP p (f + 1) (b.1 ++ todo) done none)) from by rw [interpP],
          show interpP p (f + 1) (.up (.or P₁ P₂) :: todo) done none
            = nOrAll ((invertPos (Pos.or P₁ P₂)).attach.map
                (fun b => interpP p f (b.1 ++ todo) done none)) from by rw [interpP]]
      exact nOrAllPW (PW.mapBoth (fun b _ => ih.E (b.1 ++ todo) done))
  | .up (.down M) :: todo =>
      rw [show interpP p (f + 1 + 1) (.up (.down M) :: todo) done none
            = interpP p (f + 1) (M :: todo) done none from by rw [interpP],
          show interpP p (f + 1) (.up (.down M) :: todo) done none
            = interpP p f (M :: todo) done none from by rw [interpP]]
      exact ih.E _ _
  | .and M N :: todo =>
      rw [show interpP p (f + 1 + 1) (.and M N :: todo) done none
            = interpP p (f + 1) (M :: N :: todo) done none from by rw [interpP],
          show interpP p (f + 1) (.and M N :: todo) done none
            = interpP p f (M :: N :: todo) done none from by rw [interpP]]
      exact ih.E _ _
  | .imp .fls N :: todo =>
      rw [show interpP p (f + 1 + 1) (.imp .fls N :: todo) done none
            = interpP p (f + 1) todo done none from by rw [interpP],
          show interpP p (f + 1) (.imp .fls N :: todo) done none
            = interpP p f todo done none from by rw [interpP]]
      exact ih.E _ _
  | .imp (.atom a) N :: todo =>
      rw [show interpP p (f + 1 + 1) (.imp (.atom a) N :: todo) done none
            = interpP p (f + 1) todo (.imp (.atom a) N :: done) none from by rw [interpP],
          show interpP p (f + 1) (.imp (.atom a) N :: todo) done none
            = interpP p f todo (.imp (.atom a) N :: done) none from by rw [interpP]]
      exact ih.E _ _
  | .imp (.or Q₁ Q₂) N :: todo =>
      rw [show interpP p (f + 1 + 1) (.imp (.or Q₁ Q₂) N :: todo) done none
            = interpP p (f + 1) todo (.imp (.or Q₁ Q₂) N :: done) none from by rw [interpP],
          show interpP p (f + 1) (.imp (.or Q₁ Q₂) N :: todo) done none
            = interpP p f todo (.imp (.or Q₁ Q₂) N :: done) none from by rw [interpP]]
      exact ih.E _ _
  | .imp (.down (.up P')) N :: todo =>
      rw [show interpP p (f + 1 + 1) (.imp (.down (.up P')) N :: todo) done none
            = interpP p (f + 1) todo (.imp (.down (.up P')) N :: done) none from by rw [interpP],
          show interpP p (f + 1) (.imp (.down (.up P')) N :: todo) done none
            = interpP p f todo (.imp (.down (.up P')) N :: done) none from by rw [interpP]]
      exact ih.E _ _
  | .imp (.down (.and M₁ M₂)) N :: todo =>
      rw [show interpP p (f + 1 + 1) (.imp (.down (.and M₁ M₂)) N :: todo) done none
            = interpP p (f + 1) todo (.imp (.down (.and M₁ M₂)) N :: done) none from by
              rw [interpP],
          show interpP p (f + 1) (.imp (.down (.and M₁ M₂)) N :: todo) done none
            = interpP p f todo (.imp (.down (.and M₁ M₂)) N :: done) none from by rw [interpP]]
      exact ih.E _ _
  | .imp (.down (.imp Q' N')) N :: todo =>
      rw [show interpP p (f + 1 + 1) (.imp (.down (.imp Q' N')) N :: todo) done none
            = interpP p (f + 1) todo (.imp (.down (.imp Q' N')) N :: done) none from by
              rw [interpP],
          show interpP p (f + 1) (.imp (.down (.imp Q' N')) N :: todo) done none
            = interpP p f todo (.imp (.down (.imp Q' N')) N :: done) none from by rw [interpP]]
      exact ih.E _ _
  | .circ Q :: todo =>
      rw [show interpP p (f + 1 + 1) (.circ Q :: todo) done none
            = interpP p (f + 1) todo (.circ Q :: done) none from by rw [interpP],
          show interpP p (f + 1) (.circ Q :: todo) done none
            = interpP p f todo (.circ Q :: done) none from by rw [interpP]]
      exact ih.E _ _
  | .imp (.down (.circ Q')) N :: todo =>
      rw [show interpP p (f + 1 + 1) (.imp (.down (.circ Q')) N :: todo) done none
            = interpP p (f + 1) todo (.imp (.down (.circ Q')) N :: done) none from by
              rw [interpP],
          show interpP p (f + 1) (.imp (.down (.circ Q')) N :: todo) done none
            = interpP p f todo (.imp (.down (.circ Q')) N :: done) none from by rw [interpP]]
      exact ih.E _ _
  | [] =>
      match hfr : findFire done (splits done) with
      | some (a, N, rest) =>
          rw [interpPFire_eq (f := f + 1) hfr none, interpPFire_eq (f := f) hfr none]
          exact ih.E _ _
      | none =>
          rw [interpPE_eq (f := f + 1) hfr, interpPE_eq (f := f) hfr]
          exact nAndAllPW (monoPERows ih done)

/-- **`∀p` monotone, one fuel up.** -/
noncomputable def monoPA_succ (ih : MonoP p f) (todo done : List Neg) (G : Neg) :
    Inv [interpP p (f + 1) todo done (some G)] [] .tru
        (interpP p (f + 1 + 1) todo done (some G)) := by
  match todo with
  | .up (.atom a) :: todo =>
      rw [show interpP p (f + 1 + 1) (.up (.atom a) :: todo) done (some G)
            = interpP p (f + 1) todo (.up (.atom a) :: done) (some G) from by rw [interpP],
          show interpP p (f + 1) (.up (.atom a) :: todo) done (some G)
            = interpP p f todo (.up (.atom a) :: done) (some G) from by rw [interpP]]
      exact ih.A _ _ _
  | .up .fls :: todo =>
      rw [show interpP p (f + 1 + 1) (.up .fls :: todo) done (some G) = nTop from by rw [interpP]]
      exact nTopIntro
  | .up (.or P₁ P₂) :: todo =>
      rw [show interpP p (f + 1 + 1) (.up (.or P₁ P₂) :: todo) done (some G)
            = nAndAll ((invertPos (Pos.or P₁ P₂)).attach.map
                (fun b => .imp (.down (interpP p (f + 1) (b.1 ++ todo) done none))
                               (interpP p (f + 1) (b.1 ++ todo) done (some G)))) from by
              rw [interpP],
          show interpP p (f + 1) (.up (.or P₁ P₂) :: todo) done (some G)
            = nAndAll ((invertPos (Pos.or P₁ P₂)).attach.map
                (fun b => .imp (.down (interpP p f (b.1 ++ todo) done none))
                               (interpP p f (b.1 ++ todo) done (some G)))) from by
              rw [interpP]]
      exact nAndAllPW (PW.mapBoth (fun b _ =>
        impMono (ih.E (b.1 ++ todo) done) (ih.A (b.1 ++ todo) done G)))
  | .up (.down M) :: todo =>
      rw [show interpP p (f + 1 + 1) (.up (.down M) :: todo) done (some G)
            = interpP p (f + 1) (M :: todo) done (some G) from by rw [interpP],
          show interpP p (f + 1) (.up (.down M) :: todo) done (some G)
            = interpP p f (M :: todo) done (some G) from by rw [interpP]]
      exact ih.A _ _ _
  | .and M N :: todo =>
      rw [show interpP p (f + 1 + 1) (.and M N :: todo) done (some G)
            = interpP p (f + 1) (M :: N :: todo) done (some G) from by rw [interpP],
          show interpP p (f + 1) (.and M N :: todo) done (some G)
            = interpP p f (M :: N :: todo) done (some G) from by rw [interpP]]
      exact ih.A _ _ _
  | .imp .fls N :: todo =>
      rw [show interpP p (f + 1 + 1) (.imp .fls N :: todo) done (some G)
            = interpP p (f + 1) todo done (some G) from by rw [interpP],
          show interpP p (f + 1) (.imp .fls N :: todo) done (some G)
            = interpP p f todo done (some G) from by rw [interpP]]
      exact ih.A _ _ _
  | .imp (.atom a) N :: todo =>
      rw [show interpP p (f + 1 + 1) (.imp (.atom a) N :: todo) done (some G)
            = interpP p (f + 1) todo (.imp (.atom a) N :: done) (some G) from by rw [interpP],
          show interpP p (f + 1) (.imp (.atom a) N :: todo) done (some G)
            = interpP p f todo (.imp (.atom a) N :: done) (some G) from by rw [interpP]]
      exact ih.A _ _ _
  | .imp (.or Q₁ Q₂) N :: todo =>
      rw [show interpP p (f + 1 + 1) (.imp (.or Q₁ Q₂) N :: todo) done (some G)
            = interpP p (f + 1) todo (.imp (.or Q₁ Q₂) N :: done) (some G) from by rw [interpP],
          show interpP p (f + 1) (.imp (.or Q₁ Q₂) N :: todo) done (some G)
            = interpP p f todo (.imp (.or Q₁ Q₂) N :: done) (some G) from by rw [interpP]]
      exact ih.A _ _ _
  | .imp (.down (.up P')) N :: todo =>
      rw [show interpP p (f + 1 + 1) (.imp (.down (.up P')) N :: todo) done (some G)
            = interpP p (f + 1) todo (.imp (.down (.up P')) N :: done) (some G) from by
              rw [interpP],
          show interpP p (f + 1) (.imp (.down (.up P')) N :: todo) done (some G)
            = interpP p f todo (.imp (.down (.up P')) N :: done) (some G) from by rw [interpP]]
      exact ih.A _ _ _
  | .imp (.down (.and M₁ M₂)) N :: todo =>
      rw [show interpP p (f + 1 + 1) (.imp (.down (.and M₁ M₂)) N :: todo) done (some G)
            = interpP p (f + 1) todo (.imp (.down (.and M₁ M₂)) N :: done) (some G) from by
              rw [interpP],
          show interpP p (f + 1) (.imp (.down (.and M₁ M₂)) N :: todo) done (some G)
            = interpP p f todo (.imp (.down (.and M₁ M₂)) N :: done) (some G) from by
              rw [interpP]]
      exact ih.A _ _ _
  | .imp (.down (.imp Q' N')) N :: todo =>
      rw [show interpP p (f + 1 + 1) (.imp (.down (.imp Q' N')) N :: todo) done (some G)
            = interpP p (f + 1) todo (.imp (.down (.imp Q' N')) N :: done) (some G) from by
              rw [interpP],
          show interpP p (f + 1) (.imp (.down (.imp Q' N')) N :: todo) done (some G)
            = interpP p f todo (.imp (.down (.imp Q' N')) N :: done) (some G) from by
              rw [interpP]]
      exact ih.A _ _ _
  | .circ Q :: todo =>
      rw [show interpP p (f + 1 + 1) (.circ Q :: todo) done (some G)
            = interpP p (f + 1) todo (.circ Q :: done) (some G) from by rw [interpP],
          show interpP p (f + 1) (.circ Q :: todo) done (some G)
            = interpP p f todo (.circ Q :: done) (some G) from by rw [interpP]]
      exact ih.A _ _ _
  | .imp (.down (.circ Q')) N :: todo =>
      rw [show interpP p (f + 1 + 1) (.imp (.down (.circ Q')) N :: todo) done (some G)
            = interpP p (f + 1) todo (.imp (.down (.circ Q')) N :: done) (some G) from by
              rw [interpP],
          show interpP p (f + 1) (.imp (.down (.circ Q')) N :: todo) done (some G)
            = interpP p f todo (.imp (.down (.circ Q')) N :: done) (some G) from by
              rw [interpP]]
      exact ih.A _ _ _
  | [] =>
      match hfr : findFire done (splits done) with
      | some (a, N, rest) =>
          rw [interpPFire_eq (f := f + 1) hfr (some G), interpPFire_eq (f := f) hfr (some G)]
          exact ih.A _ _ _
      | none =>
          match G with
          | .imp Q N =>
              rw [interpPA_imp_eq (f := f + 1) hfr Q N, interpPA_imp_eq (f := f) hfr Q N]
              exact nAndAllPW (PW.mapBoth (fun b _ =>
                impMono (ih.E b.1 done) (ih.A b.1 done N)))
          | .and M N =>
              rw [interpPA_and_eq (f := f + 1) hfr M N, interpPA_and_eq (f := f) hfr M N]
              exact andMono (ih.A [] done M) (ih.A [] done N)
          | .up (.atom q) =>
              by_cases hq : atomMem q done = true
              · rw [interpPA_atomT_eq (f := f + 1) hfr hq]
                exact nTopIntro
              · rw [interpPA_atom_eq (f := f + 1) hfr hq,
                    interpPA_atom_eq (f := f) hfr hq]
                exact nOrAllPW ((PW.refl (atomHead p q)).append
                  (monoPTruRows ih done (.atom q)))
          | .up .fls =>
              rw [interpPA_fls_eq (f := f + 1) hfr, interpPA_fls_eq (f := f) hfr]
              exact nOrAllPW (monoPTruRows ih done .fls)
          | .up (.or P₁ P₂) =>
              rw [interpPA_or_eq (f := f + 1) hfr P₁ P₂,
                  interpPA_or_eq (f := f) hfr P₁ P₂]
              exact nOrAllPW ((PW.cons (ih.A [] done (.up P₁))
                (PW.cons (ih.A [] done (.up P₂)) PW.nil)).append
                  (monoPTruRows ih done (.or P₁ P₂)))
          | .up (.down M) =>
              rw [interpPA_down_eq (f := f + 1) hfr M, interpPA_down_eq (f := f) hfr M]
              exact nOrAllPW ((PW.cons (ih.A [] done M) PW.nil).append
                (monoPTruRows ih done (.down M)))
          | .circ Q =>
              rw [interpP_circ_laxRows (f := f + 1) hfr Q,
                  interpP_circ_laxRows (f := f) hfr Q]
              unfold laxRowsP
              exact circMono (nOrAllPW ((monoPLaxPrefix ih done Q).append
                (monoPCircRows ih done Q)))

end StepP

/-- **Fuel monotonicity for `interpP`, at every fuel.** -/
noncomputable def monoP (p : String) : ∀ f, MonoP p f
  | 0 => monoP_zero p
  | f + 1 => { E := monoPE_succ (monoP p f), A := monoPA_succ (monoP p f) }

/-- `E^P` is antitone in the fuel. -/
noncomputable def interpP_monoE (p : String) (f : Nat) (todo done : List Neg) :
    Inv [interpP p (f + 1) todo done none] [] .tru (interpP p f todo done none) :=
  (monoP p f).E todo done

/-- `A^P` is monotone in the fuel. -/
noncomputable def interpP_monoA (p : String) (f : Nat) (todo done : List Neg)
    (G : Neg) :
    Inv [interpP p f todo done (some G)] [] .tru
        (interpP p (f + 1) todo done (some G)) :=
  (monoP p f).A todo done G

/-- `E^P`, any number of fuel levels. -/
noncomputable def interpP_monoE_add (p : String) (f : Nat) :
    ∀ (k : Nat) (todo done : List Neg),
      Inv [interpP p (f + k) todo done none] [] .tru (interpP p f todo done none)
  | 0, _, _ => idNeg _ _ (List.mem_cons_self ..)
  | k + 1, todo, done =>
      cut1N (interpP_monoE p (f + k) todo done) (interpP_monoE_add p f k todo done)

/-- `A^P`, any number of fuel levels. -/
noncomputable def interpP_monoA_add (p : String) (f : Nat) :
    ∀ (k : Nat) (todo done : List Neg) (G : Neg),
      Inv [interpP p f todo done (some G)] [] .tru
          (interpP p (f + k) todo done (some G))
  | 0, _, _, _ => idNeg _ _ (List.mem_cons_self ..)
  | k + 1, todo, done, G =>
      cut1N (interpP_monoA_add p f k todo done G) (interpP_monoA p (f + k) todo done G)

end LJFO

/-! ## Pins -/

#axioms_within LJFO.sqFire [propext, Quot.sound]
#axioms_within LJFO.sqAgg [propext, Quot.sound]
#axioms_within LJFO.monoParkRowE [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.monoParkRowA [propext, Quot.sound]
#axioms_within LJFO.monoERows [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.monoARows [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.monoLaxPrefix [propext, Quot.sound]
#axioms_within LJFO.monoStepE [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.monoStepA [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.monoStep [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.interpG_monoLvl [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.interpG_monoE [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.interpG_monoA [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.interpG_monoE_add [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.interpG_monoA_add [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.interpQ_monoE [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.interpQ_monoA [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.monoP_zero [propext, Quot.sound]
#axioms_within LJFO.monoPERows [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.monoPTruRows [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.monoPCircRows [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.monoPLaxPrefix [propext, Quot.sound]
#axioms_within LJFO.monoPE_succ [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.monoPA_succ [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.monoP [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.interpP_monoE [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.interpP_monoA [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.interpP_monoE_add [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.interpP_monoA_add [propext, Classical.choice, Quot.sound]
