/-
Route (B), node **N4**, WP12b, **stage 2**: `interpR` is SOUND.

`docs/ui-ljfo-clause-table.md` §4.28(2) asks for a transcription of
`LJF/OFuelPSound.lean`, observing that the cut rows are `⊥` in a `∀p`
aggregate and `⊤` in an `∃p` aggregate and so trivially sound.  That
observation is already a THEOREM in the shape needed: it is exactly the two
EASY halves of `PQEquiv` (`wip/ui_routeB_pqequiv.lean`, WP10),

    E^P ⊢ E^R      (∃p: dropping a conjunct of an `nAndAll` weakens)
    A^R ⊢ A^P      (∀p: dropping a disjunct of an `nOrAll` strengthens)

whose proof never inspects the recording test — it only splits on it — and
holds at EVERY `seen` and under EVERY reset policy.  So the transfer is
transcribed here for `interpR` (Parts 1–3), and soundness follows from
`eSoundP` / `aSoundP` by ONE cut on each side (Part 4):

    eSoundR : Inv (todo ++ done) [] .tru (interpR p f todo done none seen)
    aSoundR : Inv (interpR p f todo done (some G) seen :: (todo ++ done)) [] .tru G

at every state and every `seen`.  `Classical.choice` enters at `cutInv` and
nowhere else, as everywhere in this development.

`LJF/` is untouched; this module is a leaf.
-/
import wip.ui_routeB_pqequiv
import wip.ui_routeB_r_cells
import Meta.Audit

set_option autoImplicit false

namespace LJFO

/-! # Part 3 · The loop-checked recursion's own equations

`interpP`'s are already named (`LJF/OFuelPMin.lean`).  The step form makes
`interpGR`'s processing clauses definitional; only the aggregate needs the
saturation hypothesis. -/

section REq
variable {rst : SeenR → SeenR} {p : String} {f : Nat}

theorem rAtom (a : String) (todo done : List Neg) (g : Option Neg) (seen : SeenR) :
    interpGR rst p (f + 1) (.up (.atom a) :: todo) done g seen
      = interpGR rst p f todo (.up (.atom a) :: done) g (rst seen) := rfl

theorem rFlsE (todo done : List Neg) (seen : SeenR) :
    interpGR rst p (f + 1) (.up .fls :: todo) done none seen = nBot := rfl

theorem rFlsA (todo done : List Neg) (G : Neg) (seen : SeenR) :
    interpGR rst p (f + 1) (.up .fls :: todo) done (some G) seen = nTop := rfl

theorem rOrE (P₁ P₂ : Pos) (todo done : List Neg) (seen : SeenR) :
    interpGR rst p (f + 1) (.up (.or P₁ P₂) :: todo) done none seen
      = nOrAll ((invertPos (Pos.or P₁ P₂)).map
          (fun b => interpGR rst p f (b ++ todo) done none (rst seen))) := rfl

theorem rOrA (P₁ P₂ : Pos) (todo done : List Neg) (G : Neg) (seen : SeenR) :
    interpGR rst p (f + 1) (.up (.or P₁ P₂) :: todo) done (some G) seen
      = nAndAll ((invertPos (Pos.or P₁ P₂)).map
          (fun b => .imp (.down (interpGR rst p f (b ++ todo) done none (rst seen)))
                         (interpGR rst p f (b ++ todo) done (some G) (rst seen)))) := rfl

theorem rDown (M : Neg) (todo done : List Neg) (g : Option Neg) (seen : SeenR) :
    interpGR rst p (f + 1) (.up (.down M) :: todo) done g seen
      = interpGR rst p f (M :: todo) done g (rst seen) := rfl

theorem rAnd (M N : Neg) (todo done : List Neg) (g : Option Neg) (seen : SeenR) :
    interpGR rst p (f + 1) (.and M N :: todo) done g seen
      = interpGR rst p f (M :: N :: todo) done g (rst seen) := rfl

theorem rImpFls (N : Neg) (todo done : List Neg) (g : Option Neg) (seen : SeenR) :
    interpGR rst p (f + 1) (.imp .fls N :: todo) done g seen
      = interpGR rst p f todo done g (rst seen) := rfl

theorem rParkAtom (a : String) (N : Neg) (todo done : List Neg) (g : Option Neg)
    (seen : SeenR) :
    interpGR rst p (f + 1) (.imp (.atom a) N :: todo) done g seen
      = interpGR rst p f todo (.imp (.atom a) N :: done) g (rst seen) := rfl

theorem rParkOr (Q₁ Q₂ : Pos) (N : Neg) (todo done : List Neg) (g : Option Neg)
    (seen : SeenR) :
    interpGR rst p (f + 1) (.imp (.or Q₁ Q₂) N :: todo) done g seen
      = interpGR rst p f todo (.imp (.or Q₁ Q₂) N :: done) g (rst seen) := rfl

theorem rParkShift (P' : Pos) (N : Neg) (todo done : List Neg) (g : Option Neg)
    (seen : SeenR) :
    interpGR rst p (f + 1) (.imp (.down (.up P')) N :: todo) done g seen
      = interpGR rst p f todo (.imp (.down (.up P')) N :: done) g (rst seen) := rfl

theorem rParkAnd (M₁ M₂ N : Neg) (todo done : List Neg) (g : Option Neg)
    (seen : SeenR) :
    interpGR rst p (f + 1) (.imp (.down (.and M₁ M₂)) N :: todo) done g seen
      = interpGR rst p f todo (.imp (.down (.and M₁ M₂)) N :: done) g (rst seen) := rfl

theorem rParkDyk (Q' : Pos) (N' N : Neg) (todo done : List Neg) (g : Option Neg)
    (seen : SeenR) :
    interpGR rst p (f + 1) (.imp (.down (.imp Q' N')) N :: todo) done g seen
      = interpGR rst p f todo (.imp (.down (.imp Q' N')) N :: done) g (rst seen) := rfl

theorem rParkBox (Q : Pos) (todo done : List Neg) (g : Option Neg) (seen : SeenR) :
    interpGR rst p (f + 1) (.circ Q :: todo) done g seen
      = interpGR rst p f todo (.circ Q :: done) g (rst seen) := rfl

theorem rParkCimp (Q' : Pos) (N : Neg) (todo done : List Neg) (g : Option Neg)
    (seen : SeenR) :
    interpGR rst p (f + 1) (.imp (.down (.circ Q')) N :: todo) done g seen
      = interpGR rst p f todo (.imp (.down (.circ Q')) N :: done) g (rst seen) := rfl

/-- The fire equation for the loop-checked recursion. -/
theorem rFire {done : List Neg} {a : String} {N : Neg} {rest : List Neg}
    (hf : findFire done (splits done) = some (a, N, rest))
    (g : Option Neg) (seen : SeenR) :
    interpGR rst p (f + 1) [] done g seen = interpGR rst p f [N] rest g (rst seen) := by
  show stepR rst p (interpGR rst p f) [] done g seen = _
  rw [stepR, hf]

/-- The aggregate equation for the loop-checked recursion. -/
theorem rAgg {done : List Neg} (hsat : Saturated done) (g : Option Neg)
    (seen : SeenR) :
    interpGR rst p (f + 1) [] done g seen
      = aggR rst p (interpGR rst p f) done g seen := by
  show stepR rst p (interpGR rst p f) [] done g seen = _
  rw [stepR, hsat]

/-! The aggregate, clause by clause. -/

theorem aggR_none (prev : ApproxR) (done : List Neg) (seen : SeenR) :
    aggR rst p prev done none seen = nAndAll (eRowsR rst p prev done seen) := rfl

theorem aggR_imp (prev : ApproxR) (done : List Neg) (Q : Pos) (N : Neg)
    (seen : SeenR) :
    aggR rst p prev done (some (.imp Q N)) seen
      = nAndAll ((invertPos Q).map (fun b =>
          .imp (.down (prev b done none seen)) (prev b done (some N) seen))) := rfl

theorem aggR_and (prev : ApproxR) (done : List Neg) (M N : Neg) (seen : SeenR) :
    aggR rst p prev done (some (.and M N)) seen
      = nAnd (prev [] done (some M) seen) (prev [] done (some N) seen) := rfl

theorem aggR_atomIf (prev : ApproxR) (done : List Neg) (q : String)
    (seen : SeenR) :
    aggR rst p prev done (some (.up (.atom q))) seen
      = if atomMem q done then nTop
        else nOrAll (atomHead p q ++
              aRowsR rst p prev done (.up (.atom q)) false seen) := rfl

theorem aggR_atomT (prev : ApproxR) {done : List Neg} {q : String}
    (hq : atomMem q done = true) (seen : SeenR) :
    aggR rst p prev done (some (.up (.atom q))) seen = nTop := by
  rw [aggR_atomIf, if_pos hq]

theorem aggR_atomF (prev : ApproxR) {done : List Neg} {q : String}
    (hq : ¬ atomMem q done = true) (seen : SeenR) :
    aggR rst p prev done (some (.up (.atom q))) seen
      = nOrAll (atomHead p q ++ aRowsR rst p prev done (.up (.atom q)) false seen) := by
  rw [aggR_atomIf, if_neg hq]

theorem aggR_fls (prev : ApproxR) (done : List Neg) (seen : SeenR) :
    aggR rst p prev done (some (.up .fls)) seen
      = nOrAll (aRowsR rst p prev done (.up .fls) false seen) := rfl

theorem aggR_or (prev : ApproxR) (done : List Neg) (P₁ P₂ : Pos) (seen : SeenR) :
    aggR rst p prev done (some (.up (.or P₁ P₂))) seen
      = nOrAll ([prev [] done (some (.up P₁)) seen,
                 prev [] done (some (.up P₂)) seen] ++
          aRowsR rst p prev done (.up (.or P₁ P₂)) false seen) := rfl

theorem aggR_down (prev : ApproxR) (done : List Neg) (M : Neg) (seen : SeenR) :
    aggR rst p prev done (some (.up (.down M))) seen
      = nOrAll ([prev [] done (some M) seen] ++
          aRowsR rst p prev done (.up (.down M)) false seen) := rfl

theorem aggR_circ (prev : ApproxR) (done : List Neg) (Q : Pos) (seen : SeenR) :
    aggR rst p prev done (some (.circ Q)) seen
      = .circ (.down (nOrAll (laxPrefixR prev done seen Q ++
          aRowsR rst p prev done (.circ Q) true seen))) := rfl

end REq

/-! # Part 4 · The two easy halves -/

/-- The two easy halves at one fuel level, at EVERY station, goal and
`seen`. -/
structure EasyLvlR (rst : SeenR → SeenR) (p : String) (f : Nat) : Type where
  /-- `∃p`: `interpP` entails the loop-checked interpolant. -/
  E : ∀ (todo done : List Neg) (seen : SeenR),
        Inv [interpP p f todo done none] [] .tru (interpGR rst p f todo done none seen)
  /-- `∀p`: the loop-checked interpolant entails `interpP`. -/
  A : ∀ (todo done : List Neg) (G : Neg) (seen : SeenR),
        Inv [interpGR rst p f todo done (some G) seen] [] .tru
            (interpP p f todo done (some G))

/-- Fuel 0: both sides are the same default. -/
def easyLvlR_zero (rst : SeenR → SeenR) (p : String) : EasyLvlR rst p 0 where
  E := fun _ _ _ => nTopIntro
  A := fun _ _ _ _ => nBotElim _ (List.mem_cons_self ..)

section Step
variable {rst : SeenR → SeenR} {p : String} {f : Nat}

/-- The `∀p` row of a parked compound implication transfers: the cut row is
`⊥`, and the retained row is conjunct-wise. -/
noncomputable def aParkRowR (ih : EasyLvlR rst p f) (done : List Neg) (Qa : Pos)
    (N : Neg) (rest : List Neg) (goal : Neg) (seen : SeenR) :
    Inv [parkRowAR rst (interpGR rst p f) done Qa N rest goal seen] [] .tru
        (nAnd (interpP p f [] done (some (.up Qa)))
              (interpP p f [N] rest (some goal))) := by
  unfold parkRowAR
  split
  · exact nBotElim _ (List.mem_cons_self ..)
  · exact andMono (ih.A [] done (.up Qa) ((Qa, done) :: seen))
                  (ih.A [N] rest goal (rst seen))

/-- The `∃p` row of a parked compound implication transfers: the cut conjunct
is `⊤`, and the retained conjunct is the guarded implication, contravariant
in its guard. -/
noncomputable def eParkRowR (ih : EasyLvlR rst p f) (done : List Neg) (Qa : Pos)
    (N : Neg) (rest res : List Neg) (seen : SeenR) :
    Inv [nAnd (.imp (.down (interpP p f [] done (some (.up Qa))))
                    (interpP p f [N] rest none))
              (interpP p f res rest none)] [] .tru
        (parkRowER rst (interpGR rst p f) done Qa N rest res seen) := by
  unfold parkRowER
  refine andMono ?_ (ih.E res rest (rst seen))
  split
  · exact nTopIntro
  · exact impMono (ih.A [] done (.up Qa) ((Qa, done) :: seen)) (ih.E [N] rest (rst seen))

/-- The `∃p` station rows transfer. -/
noncomputable def eRowsRPW (ih : EasyLvlR rst p f) (done : List Neg)
    (seen : SeenR) :
    PW (eConjRowsP p f done) (eRowsR rst p (interpGR rst p f) done seen) := by
  unfold eConjRowsP eRowsR
  refine PW.attachMap (splits done) _ _ ?_
  rintro ⟨⟨X, rest⟩, hXr⟩
  match X with
  | .up (.atom a) => exact idNeg _ _ (List.mem_cons_self ..)
  | .imp (.atom a) N =>
      by_cases hap : a = p
      · simp only [pGuard, if_pos hap]; exact nTopIntro
      · simp only [pGuard, if_neg hap]
        exact impMonoAtom (ih.E [N] rest (rst seen))
  | .imp (.down (.imp Q' N')) N =>
      exact eParkRowR ih done (.down (.imp Q' N')) N rest [.imp (.down N') N] seen
  | .circ Q => exact circMono (ih.E [.up Q] rest (rst seen))
  | .imp (.down (.circ Q')) N =>
      exact eParkRowR ih done (.down (.circ Q')) N rest [] seen
  | .imp (.or Qa Qb) N => exact eParkRowR ih done (.or Qa Qb) N rest [] seen
  | .imp (.down (.up Pa)) N => exact eParkRowR ih done (.down (.up Pa)) N rest [] seen
  | .imp (.down (.and Ma Mb)) N =>
      exact eParkRowR ih done (.down (.and Ma Mb)) N rest [] seen
  | .up .fls => exact nTopIntro
  | .up (.or _ _) => exact nTopIntro
  | .up (.down _) => exact nTopIntro
  | .imp .fls _ => exact nTopIntro
  | .and _ _ => exact nTopIntro

/-- The `∀p` station rows transfer at a shifted goal (no box row). -/
noncomputable def aRowsTruRPW (ih : EasyLvlR rst p f) (done : List Neg) (G : Pos)
    (seen : SeenR) :
    PW (aRowsR rst p (interpGR rst p f) done (.up G) false seen)
       (truStationRowsP p f done G) := by
  unfold aRowsR truStationRowsP
  refine PW.mapAttach (splits done) _ _ ?_
  rintro ⟨⟨X, rest⟩, hXr⟩
  match X with
  | .imp (.atom a) N =>
      by_cases hap : a = p
      · simp only [pGuard, if_pos hap]; exact nBotElim _ (List.mem_cons_self ..)
      · simp only [pGuard, if_neg hap]
        exact andMono (idNeg _ _ (List.mem_cons_self ..))
                      (ih.A [N] rest (.up G) (rst seen))
  | .imp (.down (.imp Q' N')) N =>
      exact aParkRowR ih done (.down (.imp Q' N')) N rest (.up G) seen
  | .imp (.down (.circ Q')) N =>
      exact aParkRowR ih done (.down (.circ Q')) N rest (.up G) seen
  | .imp (.or Qa Qb) N => exact aParkRowR ih done (.or Qa Qb) N rest (.up G) seen
  | .imp (.down (.up Pa)) N =>
      exact aParkRowR ih done (.down (.up Pa)) N rest (.up G) seen
  | .imp (.down (.and Ma Mb)) N =>
      exact aParkRowR ih done (.down (.and Ma Mb)) N rest (.up G) seen
  | .circ R => exact nBotElim _ (List.mem_cons_self ..)
  | .up (.atom _) => exact nBotElim _ (List.mem_cons_self ..)
  | .up .fls => exact nBotElim _ (List.mem_cons_self ..)
  | .up (.or _ _) => exact nBotElim _ (List.mem_cons_self ..)
  | .up (.down _) => exact nBotElim _ (List.mem_cons_self ..)
  | .imp .fls _ => exact nBotElim _ (List.mem_cons_self ..)
  | .and _ _ => exact nBotElim _ (List.mem_cons_self ..)

/-- The `∀p` station rows transfer at a ◯-goal (the box row is present). -/
noncomputable def aRowsCircRPW (ih : EasyLvlR rst p f) (done : List Neg) (G : Pos)
    (seen : SeenR) :
    PW (aRowsR rst p (interpGR rst p f) done (.circ G) true seen)
       (circStationRowsP p f done G) := by
  unfold aRowsR circStationRowsP
  refine PW.mapAttach (splits done) _ _ ?_
  rintro ⟨⟨X, rest⟩, hXr⟩
  match X with
  | .imp (.atom a) N =>
      by_cases hap : a = p
      · simp only [pGuard, if_pos hap]; exact nBotElim _ (List.mem_cons_self ..)
      · simp only [pGuard, if_neg hap]
        exact andMono (idNeg _ _ (List.mem_cons_self ..))
                      (ih.A [N] rest (.circ G) (rst seen))
  | .imp (.down (.imp Q' N')) N =>
      exact aParkRowR ih done (.down (.imp Q' N')) N rest (.circ G) seen
  | .imp (.down (.circ Q')) N =>
      exact aParkRowR ih done (.down (.circ Q')) N rest (.circ G) seen
  | .imp (.or Qa Qb) N => exact aParkRowR ih done (.or Qa Qb) N rest (.circ G) seen
  | .imp (.down (.up Pa)) N =>
      exact aParkRowR ih done (.down (.up Pa)) N rest (.circ G) seen
  | .imp (.down (.and Ma Mb)) N =>
      exact aParkRowR ih done (.down (.and Ma Mb)) N rest (.circ G) seen
  | .circ R =>
      exact impMono (ih.E [.up R] rest (rst seen))
                    (ih.A [.up R] rest (.circ G) (rst seen))
  | .up (.atom _) => exact nBotElim _ (List.mem_cons_self ..)
  | .up .fls => exact nBotElim _ (List.mem_cons_self ..)
  | .up (.or _ _) => exact nBotElim _ (List.mem_cons_self ..)
  | .up (.down _) => exact nBotElim _ (List.mem_cons_self ..)
  | .imp .fls _ => exact nBotElim _ (List.mem_cons_self ..)
  | .and _ _ => exact nBotElim _ (List.mem_cons_self ..)

/-- The lax goal-inversion prefix transfers. -/
noncomputable def laxPrefixRPW (ih : EasyLvlR rst p f) (done : List Neg) (Q : Pos)
    (seen : SeenR) :
    PW (laxPrefixR (interpGR rst p f) done seen Q) (laxPrefixP p f done Q) := by
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

/-- **The `∃p` half, one fuel up.** -/
noncomputable def easyER_succ (ih : EasyLvlR rst p f) (todo done : List Neg)
    (seen : SeenR) :
    Inv [interpP p (f + 1) todo done none] [] .tru
        (interpGR rst p (f + 1) todo done none seen) := by
  match todo with
  | .up (.atom a) :: todo =>
      rw [show interpP p (f + 1) (.up (.atom a) :: todo) done none
            = interpP p f todo (.up (.atom a) :: done) none from by rw [interpP],
          rAtom (rst := rst) a todo done none seen]
      exact ih.E _ _ _
  | .up .fls :: todo =>
      rw [show interpP p (f + 1) (.up .fls :: todo) done none = nBot from by rw [interpP],
          rFlsE (rst := rst) (p := p) (f := f) todo done seen]
      exact idNeg _ _ (List.mem_cons_self ..)
  | .up (.or P₁ P₂) :: todo =>
      rw [rOrE (rst := rst) (p := p) (f := f) P₁ P₂ todo done seen, interpP]
      exact nOrAllPW (PW.attachMap _ _ _ (fun x => ih.E (x.1 ++ todo) done (rst seen)))
  | .up (.down M) :: todo =>
      rw [show interpP p (f + 1) (.up (.down M) :: todo) done none
            = interpP p f (M :: todo) done none from by rw [interpP],
          rDown (rst := rst) M todo done none seen]
      exact ih.E _ _ _
  | .and M N :: todo =>
      rw [show interpP p (f + 1) (.and M N :: todo) done none
            = interpP p f (M :: N :: todo) done none from by rw [interpP],
          rAnd (rst := rst) M N todo done none seen]
      exact ih.E _ _ _
  | .imp .fls N :: todo =>
      rw [show interpP p (f + 1) (.imp .fls N :: todo) done none
            = interpP p f todo done none from by rw [interpP],
          rImpFls (rst := rst) N todo done none seen]
      exact ih.E _ _ _
  | .imp (.atom a) N :: todo =>
      rw [show interpP p (f + 1) (.imp (.atom a) N :: todo) done none
            = interpP p f todo (.imp (.atom a) N :: done) none from by rw [interpP],
          rParkAtom (rst := rst) a N todo done none seen]
      exact ih.E _ _ _
  | .imp (.or Q₁ Q₂) N :: todo =>
      rw [show interpP p (f + 1) (.imp (.or Q₁ Q₂) N :: todo) done none
            = interpP p f todo (.imp (.or Q₁ Q₂) N :: done) none from by rw [interpP],
          rParkOr (rst := rst) Q₁ Q₂ N todo done none seen]
      exact ih.E _ _ _
  | .imp (.down (.up P')) N :: todo =>
      rw [show interpP p (f + 1) (.imp (.down (.up P')) N :: todo) done none
            = interpP p f todo (.imp (.down (.up P')) N :: done) none from by rw [interpP],
          rParkShift (rst := rst) P' N todo done none seen]
      exact ih.E _ _ _
  | .imp (.down (.and M₁ M₂)) N :: todo =>
      rw [show interpP p (f + 1) (.imp (.down (.and M₁ M₂)) N :: todo) done none
            = interpP p f todo (.imp (.down (.and M₁ M₂)) N :: done) none from by
              rw [interpP],
          rParkAnd (rst := rst) M₁ M₂ N todo done none seen]
      exact ih.E _ _ _
  | .imp (.down (.imp Q' N')) N :: todo =>
      rw [show interpP p (f + 1) (.imp (.down (.imp Q' N')) N :: todo) done none
            = interpP p f todo (.imp (.down (.imp Q' N')) N :: done) none from by
              rw [interpP],
          rParkDyk (rst := rst) Q' N' N todo done none seen]
      exact ih.E _ _ _
  | .circ Q :: todo =>
      rw [show interpP p (f + 1) (.circ Q :: todo) done none
            = interpP p f todo (.circ Q :: done) none from by rw [interpP],
          rParkBox (rst := rst) Q todo done none seen]
      exact ih.E _ _ _
  | .imp (.down (.circ Q')) N :: todo =>
      rw [show interpP p (f + 1) (.imp (.down (.circ Q')) N :: todo) done none
            = interpP p f todo (.imp (.down (.circ Q')) N :: done) none from by
              rw [interpP],
          rParkCimp (rst := rst) Q' N todo done none seen]
      exact ih.E _ _ _
  | [] =>
      match hfr : findFire done (splits done) with
      | some (a, N, rest) =>
          rw [interpPFire_eq hfr none, rFire (rst := rst) hfr none seen]
          exact ih.E _ _ _
      | none =>
          rw [interpPE_eq hfr, rAgg (rst := rst) hfr none seen, aggR_none]
          exact nAndAllPW (eRowsRPW ih done seen)

/-- **The `∀p` half, one fuel up.** -/
noncomputable def easyAR_succ (ih : EasyLvlR rst p f) (todo done : List Neg) (G : Neg)
    (seen : SeenR) :
    Inv [interpGR rst p (f + 1) todo done (some G) seen] [] .tru
        (interpP p (f + 1) todo done (some G)) := by
  match todo with
  | .up (.atom a) :: todo =>
      rw [show interpP p (f + 1) (.up (.atom a) :: todo) done (some G)
            = interpP p f todo (.up (.atom a) :: done) (some G) from by rw [interpP],
          rAtom (rst := rst) a todo done (some G) seen]
      exact ih.A _ _ _ _
  | .up .fls :: todo =>
      rw [show interpP p (f + 1) (.up .fls :: todo) done (some G) = nTop from by
            rw [interpP],
          rFlsA (rst := rst) (p := p) (f := f) todo done G seen]
      exact nTopIntro
  | .up (.or P₁ P₂) :: todo =>
      rw [rOrA (rst := rst) (p := p) (f := f) P₁ P₂ todo done G seen, interpP]
      exact nAndAllPW (PW.mapAttach _ _ _ (fun x =>
        impMono (ih.E (x.1 ++ todo) done (rst seen))
                (ih.A (x.1 ++ todo) done G (rst seen))))
  | .up (.down M) :: todo =>
      rw [show interpP p (f + 1) (.up (.down M) :: todo) done (some G)
            = interpP p f (M :: todo) done (some G) from by rw [interpP],
          rDown (rst := rst) M todo done (some G) seen]
      exact ih.A _ _ _ _
  | .and M N :: todo =>
      rw [show interpP p (f + 1) (.and M N :: todo) done (some G)
            = interpP p f (M :: N :: todo) done (some G) from by rw [interpP],
          rAnd (rst := rst) M N todo done (some G) seen]
      exact ih.A _ _ _ _
  | .imp .fls N :: todo =>
      rw [show interpP p (f + 1) (.imp .fls N :: todo) done (some G)
            = interpP p f todo done (some G) from by rw [interpP],
          rImpFls (rst := rst) N todo done (some G) seen]
      exact ih.A _ _ _ _
  | .imp (.atom a) N :: todo =>
      rw [show interpP p (f + 1) (.imp (.atom a) N :: todo) done (some G)
            = interpP p f todo (.imp (.atom a) N :: done) (some G) from by rw [interpP],
          rParkAtom (rst := rst) a N todo done (some G) seen]
      exact ih.A _ _ _ _
  | .imp (.or Q₁ Q₂) N :: todo =>
      rw [show interpP p (f + 1) (.imp (.or Q₁ Q₂) N :: todo) done (some G)
            = interpP p f todo (.imp (.or Q₁ Q₂) N :: done) (some G) from by rw [interpP],
          rParkOr (rst := rst) Q₁ Q₂ N todo done (some G) seen]
      exact ih.A _ _ _ _
  | .imp (.down (.up P')) N :: todo =>
      rw [show interpP p (f + 1) (.imp (.down (.up P')) N :: todo) done (some G)
            = interpP p f todo (.imp (.down (.up P')) N :: done) (some G) from by
              rw [interpP],
          rParkShift (rst := rst) P' N todo done (some G) seen]
      exact ih.A _ _ _ _
  | .imp (.down (.and M₁ M₂)) N :: todo =>
      rw [show interpP p (f + 1) (.imp (.down (.and M₁ M₂)) N :: todo) done (some G)
            = interpP p f todo (.imp (.down (.and M₁ M₂)) N :: done) (some G) from by
              rw [interpP],
          rParkAnd (rst := rst) M₁ M₂ N todo done (some G) seen]
      exact ih.A _ _ _ _
  | .imp (.down (.imp Q' N')) N :: todo =>
      rw [show interpP p (f + 1) (.imp (.down (.imp Q' N')) N :: todo) done (some G)
            = interpP p f todo (.imp (.down (.imp Q' N')) N :: done) (some G) from by
              rw [interpP],
          rParkDyk (rst := rst) Q' N' N todo done (some G) seen]
      exact ih.A _ _ _ _
  | .circ Q :: todo =>
      rw [show interpP p (f + 1) (.circ Q :: todo) done (some G)
            = interpP p f todo (.circ Q :: done) (some G) from by rw [interpP],
          rParkBox (rst := rst) Q todo done (some G) seen]
      exact ih.A _ _ _ _
  | .imp (.down (.circ Q')) N :: todo =>
      rw [show interpP p (f + 1) (.imp (.down (.circ Q')) N :: todo) done (some G)
            = interpP p f todo (.imp (.down (.circ Q')) N :: done) (some G) from by
              rw [interpP],
          rParkCimp (rst := rst) Q' N todo done (some G) seen]
      exact ih.A _ _ _ _
  | [] =>
      match hfr : findFire done (splits done) with
      | some (a, N, rest) =>
          rw [interpPFire_eq hfr (some G), rFire (rst := rst) hfr (some G) seen]
          exact ih.A _ _ _ _
      | none =>
          rw [rAgg (rst := rst) hfr (some G) seen]
          match G with
          | .imp Q N =>
              rw [interpPA_imp_eq hfr Q N, aggR_imp]
              exact nAndAllPW (PW.mapAttach _ _ _ (fun x =>
                impMono (ih.E x.1 done seen) (ih.A x.1 done N seen)))
          | .and M N =>
              rw [interpPA_and_eq hfr M N, aggR_and]
              exact andMono (ih.A [] done M seen) (ih.A [] done N seen)
          | .up (.atom q) =>
              by_cases hq : atomMem q done = true
              · rw [interpPA_atomT_eq hfr hq, aggR_atomT _ hq]
                exact nTopIntro
              · rw [interpPA_atom_eq hfr hq, aggR_atomF _ hq]
                exact nOrAllPW ((PW.refl (atomHead p q)).append
                  (aRowsTruRPW ih done (.atom q) seen))
          | .up .fls =>
              rw [interpPA_fls_eq hfr, aggR_fls]
              exact nOrAllPW (aRowsTruRPW ih done .fls seen)
          | .up (.or P₁ P₂) =>
              rw [interpPA_or_eq hfr P₁ P₂, aggR_or]
              exact nOrAllPW ((PW.cons (ih.A [] done (.up P₁) seen)
                (PW.cons (ih.A [] done (.up P₂) seen) PW.nil)).append
                  (aRowsTruRPW ih done (.or P₁ P₂) seen))
          | .up (.down M) =>
              rw [interpPA_down_eq hfr M, aggR_down]
              exact nOrAllPW ((PW.cons (ih.A [] done M seen) PW.nil).append
                (aRowsTruRPW ih done (.down M) seen))
          | .circ Q =>
              rw [interpP_circ_laxRows hfr Q, aggR_circ]
              exact circMono (nOrAllPW ((laxPrefixRPW ih done Q seen).append
                (aRowsCircRPW ih done Q seen)))

end Step

/-- **The two easy halves, at every fuel.** -/
noncomputable def easyLvlR (rst : SeenR → SeenR) (p : String) :
    ∀ f, EasyLvlR rst p f
  | 0 => easyLvlR_zero rst p
  | f + 1 =>
      { E := easyER_succ (easyLvlR rst p f)
        A := easyAR_succ (easyLvlR rst p f) }

/-! # Part 5 · The easy halves at the cells `PQEquiv` names -/

/-- **`interpP ⊢ interpR` on the `∃p` side**, at every fuel and every
station: the dropped conjunct is `⊤`. -/
noncomputable def prEasyE (p : String) (f : Nat) (done : List Neg) :
    Inv [interpP p f [] done none] [] .tru (interpR p f [] done none []) :=
  (easyLvlR id p f).E [] done []

/-- **`interpR ⊢ interpP` on the `∀p` side**, at every fuel, station and
goal: the dropped disjunct is `⊥`. -/
noncomputable def prEasyA (p : String) (f : Nat) (done : List Neg) (G : Neg) :
    Inv [interpR p f [] done (some G) []] [] .tru (interpP p f [] done (some G)) :=
  (easyLvlR id p f).A [] done G []

/-! # Part 4 · Soundness, by one cut on each side -/

/-- **`interpR` is sound on the `∃p` side**, at every state and every `seen`:
the station entails the interpolant. -/
noncomputable def eSoundR (p : String) (f : Nat) (todo done : List Neg)
    (seen : SeenR) :
    Inv (todo ++ done) [] .tru (interpR p f todo done none seen) := by
  have h := cutInv (todo ++ done) [] .tru
    (interpP p f todo done none) (interpR p f todo done none seen)
    (eSoundP p f todo done) ((easyLvlR id p f).E todo done seen)
  simpa using h

/-- **`interpR` is sound on the `∀p` side**, at every state and every `seen`:
the interpolant is sufficient for the goal over the station. -/
noncomputable def aSoundR (p : String) (f : Nat) (todo done : List Neg) (G : Neg)
    (seen : SeenR) :
    Inv (interpR p f todo done (some G) seen :: (todo ++ done)) [] .tru G := by
  have h := cutInv [interpR p f todo done (some G) seen] (todo ++ done) .tru
    (interpP p f todo done (some G)) G
    ((easyLvlR id p f).A todo done G seen) (aSoundP p f todo done G)
  simpa using h

/-- E1 at every fuel and every `seen`, for `interpR`, as a type. -/
def ESoundR' (p : String) : Type :=
  ∀ (f : Nat) (todo done : List Neg) (seen : SeenR),
    Inv (todo ++ done) [] .tru (interpR p f todo done none seen)

/-- A1 at every fuel and every `seen`, for `interpR`, as a type. -/
def ASoundR' (p : String) : Type :=
  ∀ (f : Nat) (todo done : List Neg) (G : Neg) (seen : SeenR),
    Inv (interpR p f todo done (some G) seen :: (todo ++ done)) [] .tru G

/-- `ESoundR'` is inhabited. -/
noncomputable def eSoundRWitness (p : String) : ESoundR' p := eSoundR p

/-- `ASoundR'` is inhabited. -/
noncomputable def aSoundRWitness (p : String) : ASoundR' p := aSoundR p

/-! # Part 5 · The gate: the transfer is not vacuous

If `interpR` were literally `interpP` the two halves above would carry no
content and soundness would be a restatement.  It is not: at the ◯-free cell
(i) the loop check fires from fuel 2 on, in BOTH modes, and the two
interpolants are literally different formulas — kernel-checked `= false`.
The control at fuels 0 and 1, where the check cannot yet have fired, is
`= true`, so the gate is measuring the loop check and not a transcription
difference. -/

/-- **GATE, watched failing**: `interpR = interpP` is FALSE at cell (i) from
fuel 2 on, in both modes. -/
theorem gate_r_sound_nonvacuous :
    decide (interpR "p" 2 [] cell1 (some goal1) [] = interpP "p" 2 [] cell1 (some goal1))
      = false ∧
    decide (interpR "p" 3 [] cell1 (some goal1) [] = interpP "p" 3 [] cell1 (some goal1))
      = false ∧
    decide (interpR "p" 2 [] cell1 none [] = interpP "p" 2 [] cell1 none) = false ∧
    decide (interpR "p" 3 [] cell1 none [] = interpP "p" 3 [] cell1 none) = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- **CONTROL**: below the fuel at which the check can fire the two agree, so
the gate above measures the loop check. -/
theorem gate_r_sound_control :
    decide (interpR "p" 1 [] cell1 (some goal1) [] = interpP "p" 1 [] cell1 (some goal1))
      = true ∧
    decide (interpR "p" 1 [] cell1 none [] = interpP "p" 1 [] cell1 none) = true := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

end LJFO

/-! ## Pins -/

#axioms_within LJFO.easyLvlR_zero [propext, Quot.sound]
#axioms_within LJFO.aParkRowR [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.eParkRowR [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.easyER_succ [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.easyAR_succ [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.easyLvlR [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.prEasyE [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.prEasyA [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.eSoundR [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.aSoundR [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.eSoundRWitness [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.aSoundRWitness [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.gate_r_sound_nonvacuous [propext]
#axioms_within LJFO.gate_r_sound_control [propext]
