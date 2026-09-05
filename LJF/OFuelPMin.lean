/-
LJF◯ — the minimality layer over the PARKING retention interpolant
(route (B), node N0e).

`LJF/OFuelMin.lean` Parts 2-5 and 7, transposed from `interpF` to
`interpP` (`LJF/OFuelP.lean`).  Part 1 — the upward-closed witness types
`UpFrom`/`UpFrom2` — is imported unchanged.

What changes, and nothing else:

* the `∃p` station map `eConjRowsP` and the two `∀p` station maps
  `truStationRowsP`/`circStationRowsP` gain THREE rows each, for the
  shapes `interpP` newly parks, and their Dyckhoff row takes its guard at
  the FULL station and at the ANTECEDENT'S OWN GOAL `↑↓(Q′ ⊃ N′)`, so
  that all five parked implication rows have literally one shape
  (`LJF/OFuelP.lean` (c), 2026-09-05);
* the aggregate equations and row memberships follow verbatim (they are
  `rfl`/`rowMem` against the new maps);
* `SatE2P`/`SatA2P` are `SatE2F`/`SatA2F` with `interpP` and the extended
  parked-shape invariant `ParkedCtxP`;
* the processing phase `eMinPP`/`aMinPP` loses its three RESHAPING
  clauses: `(Q₁∨Q₂) ⊃ N`, `↓↑P′ ⊃ N` and `↓(M₁∧M₂) ⊃ N` now PARK, so
  their clauses are `subParkOut` weakenings and the transformers
  `invImpOr`, `invStrip`, `invCurry` are never called.  That is the whole
  point of the definition change (`LJF/OFuelHeight.lean` §7.2): after it,
  every processing edge is either a parking weakening (height EXACT by
  Part 1 of that module) or one of the six non-increasing transformers.

`LJF/OCore.lean`, `LJF/O.lean`, `LJF/OFuel.lean`, `LJF/OFuelSound.lean`,
`LJF/OFuelMin.lean` and `LJF/OFuelP.lean` are untouched; this module is
purely additive.
-/
import LJF.OFuelMin
import LJF.OFuelPSound
import Meta.Audit

namespace LJFO

/-! # Part 2: the `∃p` station map at fuel `f+1`

`LJF/ORows.lean`'s `eConjRows`, transposed to `interpP`.  One difference,
and it is the point of route (B): the `◯`-implication row takes its
`∀p` guard at the FULL station `done`, where `interp` takes it at the
residual `rest`. -/

set_option linter.unusedVariables false in
/-- The conjunct rows of the `∃p` aggregate of `interpP` at fuel `f+1`
over a saturated station: one row per split, the residuals interpolated
at fuel `f`, the `◯`-implication guard RETAINED at `done`. -/
def eConjRowsP (p : String) (f : Nat) (done : List Neg) : List Neg :=
  (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
    match X with
    | .up (.atom a) => pGuard p a nTop (.up (.atom a))
    | .imp (.atom a) N =>
        pGuard p a nTop (.imp (.atom a) (interpP p f [N] rest none))
    | .imp (.down (.imp Q' N')) N =>
        nAnd
          (.imp (.down (interpP p f [] done (some (.up (.down (.imp Q' N'))))))
               (interpP p f [N] rest none))
          (interpP p f [.imp (.down N') N] rest none)
    | .circ Q =>
        .circ (.down (interpP p f [.up Q] rest none))
    | .imp (.down (.circ Q')) N =>
        nAnd
          (.imp (.down (interpP p f [] done (some (.up (.down (.circ Q'))))))
               (interpP p f [N] rest none))
          (interpP p f [] rest none)
    | .imp (.or Qa Qb) N =>
        nAnd
          (.imp (.down (interpP p f [] done (some (.up (.or Qa Qb)))))
               (interpP p f [N] rest none))
          (interpP p f [] rest none)
    | .imp (.down (.up Pa)) N =>
        nAnd
          (.imp (.down (interpP p f [] done (some (.up (.down (.up Pa))))))
               (interpP p f [N] rest none))
          (interpP p f [] rest none)
    | .imp (.down (.and Ma Mb)) N =>
        nAnd
          (.imp (.down (interpP p f [] done (some (.up (.down (.and Ma Mb))))))
               (interpP p f [N] rest none))
          (interpP p f [] rest none)
    | _ => nTop)

/-- The saturated `∃p` aggregate of `interpP`, as an equation. -/
theorem interpPE_eq {p : String} {f : Nat} {done : List Neg}
    (hsat : Saturated done) :
    interpP p (f + 1) [] done none = nAndAll (eConjRowsP p f done) := by
  rw [interpP]; split
  all_goals rename_i heq
  · rw [hsat] at heq; cases heq
  · rfl

/-- The `∃p` conjunct of a `q`-implication member. -/
theorem qimpConjMemP {p : String} {f : Nat} {done : List Neg} {a : String}
    {N : Neg} {rest : List Neg}
    (hXr : (Neg.imp (.atom a) N, rest) ∈ splits done) :
    pGuard p a nTop (.imp (.atom a) (interpP p f [N] rest none)) ∈
      eConjRowsP p f done :=
  rowMem hXr

/-- Likewise for a surviving atom. -/
theorem atomConjMemP {p : String} {f : Nat} {done : List Neg} {a : String}
    {rest : List Neg} (hXr : (Neg.up (.atom a), rest) ∈ splits done) :
    pGuard p a nTop (.up (.atom a)) ∈ eConjRowsP p f done :=
  rowMem hXr

/-- And for a Dyckhoff member. -/
theorem dykConjMemP {p : String} {f : Nat} {done : List Neg} {Q' : Pos}
    {N' N : Neg} {rest : List Neg}
    (hXr : (Neg.imp (.down (.imp Q' N')) N, rest) ∈ splits done) :
    nAnd
      (.imp (.down (interpP p f [] done (some (.up (.down (.imp Q' N'))))))
           (interpP p f [N] rest none))
      (interpP p f [.imp (.down N') N] rest none) ∈ eConjRowsP p f done :=
  rowMem hXr

/-- And for a parked box. -/
theorem boxConjMemP {p : String} {f : Nat} {done : List Neg} {Q : Pos}
    {rest : List Neg} (hXr : (Neg.circ Q, rest) ∈ splits done) :
    Neg.circ (.down (interpP p f [.up Q] rest none)) ∈ eConjRowsP p f done :=
  rowMem hXr

/-- And for a `◯`-implication member — the retention row: the guard is the
`∀p` of `↑↓◯Q′` at `done`, not at `rest`. -/
theorem cimpConjMemP {p : String} {f : Nat} {done : List Neg} {Q' : Pos}
    {N : Neg} {rest : List Neg}
    (hXr : (Neg.imp (.down (.circ Q')) N, rest) ∈ splits done) :
    nAnd
      (.imp (.down (interpP p f [] done (some (.up (.down (.circ Q'))))))
           (interpP p f [N] rest none))
      (interpP p f [] rest none) ∈ eConjRowsP p f done :=
  rowMem hXr

/-- And for a newly parked `(Qa∨Qb) ⊃ N` member. -/
theorem orimpConjMemP {p : String} {f : Nat} {done : List Neg} {Qa Qb : Pos}
    {N : Neg} {rest : List Neg}
    (hXr : (Neg.imp (.or Qa Qb) N, rest) ∈ splits done) :
    nAnd
      (.imp (.down (interpP p f [] done (some (.up (.or Qa Qb)))))
           (interpP p f [N] rest none))
      (interpP p f [] rest none) ∈ eConjRowsP p f done :=
  rowMem hXr

/-- And for a newly parked `↓↑Pa ⊃ N` member. -/
theorem shimpConjMemP {p : String} {f : Nat} {done : List Neg} {Pa : Pos}
    {N : Neg} {rest : List Neg}
    (hXr : (Neg.imp (.down (.up Pa)) N, rest) ∈ splits done) :
    nAnd
      (.imp (.down (interpP p f [] done (some (.up (.down (.up Pa))))))
           (interpP p f [N] rest none))
      (interpP p f [] rest none) ∈ eConjRowsP p f done :=
  rowMem hXr

/-- And for a newly parked `↓(Ma∧Mb) ⊃ N` member. -/
theorem andimpConjMemP {p : String} {f : Nat} {done : List Neg} {Ma Mb N : Neg}
    {rest : List Neg}
    (hXr : (Neg.imp (.down (.and Ma Mb)) N, rest) ∈ splits done) :
    nAnd
      (.imp (.down (interpP p f [] done (some (.up (.down (.and Ma Mb))))))
           (interpP p f [N] rest none))
      (interpP p f [] rest none) ∈ eConjRowsP p f done :=
  rowMem hXr

/-! # Part 3: the `tru`-goal station map at fuel `f+1` -/

set_option linter.unusedVariables false in
/-- The station rows of every `↑`-goal aggregate of `interpP` at fuel
`f+1`; identical across all four shifted goal shapes. -/
def truStationRowsP (p : String) (f : Nat) (done : List Neg) (G : Pos) :
    List Neg :=
  (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
    match X, hXr with
    | .imp (.atom a) N, hXr =>
        pGuard p a nBot
          (nAnd (.up (.atom a)) (interpP p f [N] rest (some (.up G))))
    | .imp (.down (.imp Q' N')) N, hXr =>
        nAnd (interpP p f [] done (some (.up (.down (.imp Q' N')))))
             (interpP p f [N] rest (some (.up G)))
    | .imp (.down (.circ Q')) N, hXr =>
        nAnd (interpP p f [] done (some (.up (.down (.circ Q')))))
             (interpP p f [N] rest (some (.up G)))
    | .imp (.or Qa Qb) N, hXr =>
        nAnd (interpP p f [] done (some (.up (.or Qa Qb))))
             (interpP p f [N] rest (some (.up G)))
    | .imp (.down (.up Pa)) N, hXr =>
        nAnd (interpP p f [] done (some (.up (.down (.up Pa)))))
             (interpP p f [N] rest (some (.up G)))
    | .imp (.down (.and Ma Mb)) N, hXr =>
        nAnd (interpP p f [] done (some (.up (.down (.and Ma Mb)))))
             (interpP p f [N] rest (some (.up G)))
    | _, _ => nBot)

theorem interpPA_atom_eq {p : String} {f : Nat} {done : List Neg}
    (hsat : Saturated done) {q : String} (hq : ¬ atomMem q done = true) :
    interpP p (f + 1) [] done (some (.up (.atom q))) =
      nOrAll (atomHead p q ++ truStationRowsP p f done (.atom q)) := by
  rw [interpP]; split
  all_goals rename_i heq
  · rw [hsat] at heq; cases heq
  · simp only [hq, if_false, Bool.false_eq_true]; rfl

theorem interpPA_atomT_eq {p : String} {f : Nat} {done : List Neg}
    (hsat : Saturated done) {q : String} (hq : atomMem q done = true) :
    interpP p (f + 1) [] done (some (.up (.atom q))) = nTop := by
  rw [interpP]; split
  all_goals rename_i heq
  · rw [hsat] at heq; cases heq
  · simp [hq]

theorem interpPA_fls_eq {p : String} {f : Nat} {done : List Neg}
    (hsat : Saturated done) :
    interpP p (f + 1) [] done (some (.up .fls)) =
      nOrAll (truStationRowsP p f done .fls) := by
  rw [interpP]; split
  all_goals rename_i heq
  · rw [hsat] at heq; cases heq
  · rfl

theorem interpPA_or_eq {p : String} {f : Nat} {done : List Neg}
    (hsat : Saturated done) (P₁ P₂ : Pos) :
    interpP p (f + 1) [] done (some (.up (.or P₁ P₂))) =
      nOrAll ([interpP p f [] done (some (.up P₁)),
               interpP p f [] done (some (.up P₂))] ++
              truStationRowsP p f done (.or P₁ P₂)) := by
  rw [interpP]; split
  all_goals rename_i heq
  · rw [hsat] at heq; cases heq
  · rfl

theorem interpPA_down_eq {p : String} {f : Nat} {done : List Neg}
    (hsat : Saturated done) (M : Neg) :
    interpP p (f + 1) [] done (some (.up (.down M))) =
      nOrAll ([interpP p f [] done (some M)] ++
              truStationRowsP p f done (.down M)) := by
  rw [interpP]; split
  all_goals rename_i heq
  · rw [hsat] at heq; cases heq
  · rfl

theorem interpPA_imp_eq {p : String} {f : Nat} {done : List Neg}
    (hsat : Saturated done) (Q : Pos) (N : Neg) :
    interpP p (f + 1) [] done (some (.imp Q N)) =
      nAndAll ((invertPos Q).attach.map
        (fun ⟨b, hb⟩ =>
          .imp (.down (interpP p f b done none))
            (interpP p f b done (some N)))) := by
  rw [interpP]; split
  all_goals rename_i heq
  · rw [hsat] at heq; cases heq
  · rfl

theorem interpPA_and_eq {p : String} {f : Nat} {done : List Neg}
    (hsat : Saturated done) (M N : Neg) :
    interpP p (f + 1) [] done (some (.and M N)) =
      nAnd (interpP p f [] done (some M)) (interpP p f [] done (some N)) := by
  rw [interpP]; split
  all_goals rename_i heq
  · rw [hsat] at heq; cases heq
  · rfl

/-! # Part 4: the ◯-goal row family at fuel `f+1` -/

set_option linter.unusedVariables false in
/-- The station rows of every ◯-goal aggregate of `interpP` at fuel `f+1`;
identical across all seven goal shapes. -/
def circStationRowsP (p : String) (f : Nat) (done : List Neg) (G : Pos) :
    List Neg :=
  (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
    match X, hXr with
    | .imp (.atom a) N, hXr =>
        pGuard p a nBot
          (nAnd (.up (.atom a)) (interpP p f [N] rest (some (.circ G))))
    | .imp (.down (.imp Q' N')) N, hXr =>
        nAnd (interpP p f [] done (some (.up (.down (.imp Q' N')))))
             (interpP p f [N] rest (some (.circ G)))
    | .imp (.down (.circ Q')) N, hXr =>
        nAnd (interpP p f [] done (some (.up (.down (.circ Q')))))
             (interpP p f [N] rest (some (.circ G)))
    | .imp (.or Qa Qb) N, hXr =>
        nAnd (interpP p f [] done (some (.up (.or Qa Qb))))
             (interpP p f [N] rest (some (.circ G)))
    | .imp (.down (.up Pa)) N, hXr =>
        nAnd (interpP p f [] done (some (.up (.down (.up Pa)))))
             (interpP p f [N] rest (some (.circ G)))
    | .imp (.down (.and Ma Mb)) N, hXr =>
        nAnd (interpP p f [] done (some (.up (.down (.and Ma Mb)))))
             (interpP p f [N] rest (some (.circ G)))
    | .circ R, hXr =>
        .imp (.down (interpP p f [.up R] rest none))
             (interpP p f [.up R] rest (some (.circ G)))
    | _, _ => nBot)

/-- The lax goal-inversion prefix at fuel `f+1`, by goal shape. -/
def laxPrefixP (p : String) (f : Nat) (done : List Neg) : Pos → List Neg
  | .atom q => [interpP p f [] done (some (.up (.atom q)))]
  | .fls => [interpP p f [] done (some (.up .fls))]
  | .or P₁ P₂ => [interpP p f [] done (some (.circ P₁)),
                  interpP p f [] done (some (.circ P₂)),
                  interpP p f [] done (some (.up (.or P₁ P₂)))]
  | .down (.up P') => [interpP p f [] done (some (.circ P'))]
  | .down (.circ P') => [interpP p f [] done (some (.circ P'))]
  | .down (.and M₁ M₂) =>
      [interpP p f [] done (some (.up (.down (.and M₁ M₂))))]
  | .down (.imp Q₀ N₀) =>
      [interpP p f [] done (some (.up (.down (.imp Q₀ N₀))))]

/-- The ◯-goal row family at fuel `f+1`. -/
def laxRowsP (p : String) (f : Nat) (done : List Neg) (Q : Pos) : List Neg :=
  laxPrefixP p f done Q ++ circStationRowsP p f done Q

/-- **The unified ◯-goal equation** for `interpP` at fuel `f+1`. -/
theorem interpP_circ_laxRows {p : String} {f : Nat} {done : List Neg}
    (hsat : Saturated done) (Q : Pos) :
    interpP p (f + 1) [] done (some (.circ Q)) =
      .circ (.down (nOrAll (laxRowsP p f done Q))) := by
  match Q with
  | .atom _ | .fls | .or _ _ | .down (.up _) | .down (.circ _)
  | .down (.and _ _) | .down (.imp _ _) =>
    conv => lhs; rw [interpP]
    split
    all_goals rename_i heq
    · rw [hsat] at heq; cases heq
    · rfl

/-- The row list of a ◯-goal aggregate at fuel `f+1` is `laxRowsP`. -/
theorem laxRowsP_of_eq {p : String} {f : Nat} {done : List Neg} {L : List Neg}
    (hsat : Saturated done) (Q : Pos)
    (hV : interpP p (f + 1) [] done (some (.circ Q)) =
      .circ (.down (nOrAll L))) :
    L = laxRowsP p f done Q :=
  nOrAll_inj (Pos.down.inj (Neg.circ.inj
    (hV.symm.trans (interpP_circ_laxRows hsat Q))))

/-- The fired-`q`-implication row. -/
theorem laxRowsP_qimpMem {p : String} {f : Nat} {done : List Neg} {Q : Pos}
    {c : String} {Nc : Neg} {rest : List Neg}
    (hsp : (Neg.imp (.atom c) Nc, rest) ∈ splits done) :
    pGuard p c nBot (nAnd (.up (.atom c))
      (interpP p f [Nc] rest (some (.circ Q)))) ∈ laxRowsP p f done Q :=
  rowMemR hsp

/-- The Dyckhoff row. -/
theorem laxRowsP_dykMem {p : String} {f : Nat} {done : List Neg} {Q : Pos}
    {Q' : Pos} {N' N : Neg} {rest : List Neg}
    (hsp : (Neg.imp (.down (.imp Q' N')) N, rest) ∈ splits done) :
    nAnd (interpP p f [] done (some (.up (.down (.imp Q' N')))))
         (interpP p f [N] rest (some (.circ Q))) ∈ laxRowsP p f done Q :=
  rowMemR hsp

/-- The newly parked `(Qa∨Qb) ⊃ N` row. -/
theorem laxRowsP_orimpMem {p : String} {f : Nat} {done : List Neg} {Q : Pos}
    {Qa Qb : Pos} {N : Neg} {rest : List Neg}
    (hsp : (Neg.imp (.or Qa Qb) N, rest) ∈ splits done) :
    nAnd (interpP p f [] done (some (.up (.or Qa Qb))))
         (interpP p f [N] rest (some (.circ Q))) ∈ laxRowsP p f done Q :=
  rowMemR hsp

/-- The newly parked `↓↑Pa ⊃ N` row. -/
theorem laxRowsP_shimpMem {p : String} {f : Nat} {done : List Neg} {Q : Pos}
    {Pa : Pos} {N : Neg} {rest : List Neg}
    (hsp : (Neg.imp (.down (.up Pa)) N, rest) ∈ splits done) :
    nAnd (interpP p f [] done (some (.up (.down (.up Pa)))))
         (interpP p f [N] rest (some (.circ Q))) ∈ laxRowsP p f done Q :=
  rowMemR hsp

/-- The newly parked `↓(Ma∧Mb) ⊃ N` row. -/
theorem laxRowsP_andimpMem {p : String} {f : Nat} {done : List Neg} {Q : Pos}
    {Ma Mb N : Neg} {rest : List Neg}
    (hsp : (Neg.imp (.down (.and Ma Mb)) N, rest) ∈ splits done) :
    nAnd (interpP p f [] done (some (.up (.down (.and Ma Mb)))))
         (interpP p f [N] rest (some (.circ Q))) ∈ laxRowsP p f done Q :=
  rowMemR hsp

/-- The `◯`-implication row — retained at `done`. -/
theorem laxRowsP_cimpMem {p : String} {f : Nat} {done : List Neg} {Q : Pos}
    {Q' : Pos} {N : Neg} {rest : List Neg}
    (hsp : (Neg.imp (.down (.circ Q')) N, rest) ∈ splits done) :
    nAnd (interpP p f [] done (some (.up (.down (.circ Q')))))
         (interpP p f [N] rest (some (.circ Q))) ∈ laxRowsP p f done Q :=
  rowMemR hsp

/-- The opened-box row — the lax-only one (`circL`). -/
theorem laxRowsP_boxMem {p : String} {f : Nat} {done : List Neg} {Q : Pos}
    {R : Pos} {rest : List Neg}
    (hsp : (Neg.circ R, rest) ∈ splits done) :
    Neg.imp (.down (interpP p f [.up R] rest none))
      (interpP p f [.up R] rest (some (.circ Q))) ∈ laxRowsP p f done Q :=
  rowMemR hsp

/-! # Part 5: the cofinality statements at a saturated station -/

/-- Minimality of `∃p` at a saturated station, fuel form: the ∃p
approximant is cofinal for the `p`-free consequences of the station. -/
def SatE2P (p : String) : Type :=
  ∀ (done Δ : List Neg) (ψ : Neg), Saturated done → ParkedCtxP done →
    PFreeCtx p Δ → PFreeN p ψ →
    ∀ {j : JD}, Inv (done ++ Δ) [] j ψ →
      UpFrom (fun e => Inv (interpP p e [] done none :: Δ) [] j ψ)

/-- Minimality of `∀p` at a saturated station, fuel form (E-relativised, as
`SatA2`).  The `∃p` fuel `e` and the `∀p` fuel `f` are independent. -/
def SatA2P (p : String) : Type :=
  ∀ (done Δ : List Neg) (G : Neg), Saturated done → ParkedCtxP done →
    PFreeCtx p Δ →
    ∀ {j : JD}, Inv (done ++ Δ) [] j G →
      UpFrom2 (fun e f => Inv (interpP p e [] done none :: Δ) [] .tru
        (interpP p f [] done (some (jGoal j G))))


/-- **The fire equation at fuel.**  When a parked implication fires, the
interpolant at the station equals the interpolant at the residual station
one fuel down, whatever the goal.  Stated by cases for the same reason as
`interpPire_eq`: the equation lemmas are specialised per fused matcher
alternative. -/
theorem interpPFire_eq {p : String} {f : Nat} {done : List Neg} {a : String}
    {N' : Neg} {rest : List Neg}
    (hf : findFire done (splits done) = some (a, N', rest)) :
    ∀ g, interpP p (f + 1) [] done g = interpP p f [N'] rest g := by
  intro g
  match g with
  | none | some (.up (.atom _)) | some (.up .fls) | some (.up (.or _ _))
  | some (.up (.down _)) | some (.imp _ _) | some (.and _ _)
  | some (.circ (.atom _)) | some (.circ .fls) | some (.circ (.or _ _))
  | some (.circ (.down (.up _))) | some (.circ (.down (.circ _)))
  | some (.circ (.down (.and _ _))) | some (.circ (.down (.imp _ _))) =>
      rw [interpP]; split
      all_goals rename_i heq
      · rw [hf] at heq; cases heq; rfl
      · rw [hf] at heq; cases heq

variable {p : String}

/-- **Minimality of `∃p`, processing phase, at fuel.**  Every station
reduces to a saturated one. -/
def eMinPP (sat : SatE2P p) :
    ∀ (todo done Δ : List Neg) (ψ : Neg), ParkedCtxP done →
      PFreeCtx p Δ → PFreeN p ψ → ∀ {j : JD},
      Inv ((todo ++ done) ++ Δ) [] j ψ →
      UpFrom (fun e => Inv (interpP p e todo done none :: Δ) [] j ψ)
  | .up (.atom a) :: todo, done, Δ, ψ, hP, hΔ, hψ, _, d =>
      let w := eMinPP sat todo (.up (.atom a) :: done) Δ ψ
        (ParkedCtxP.cons (ParkedNP.atom a) hP) hΔ hψ (d.wk subParkOut)
      UpFrom.mk1 w.1 (fun e' he' => by rw [interpP]; exact w.2 e' he')
  | .up .fls :: todo, done, Δ, ψ, _, _, _, _, d =>
      UpFrom.mk1 0 (fun e' _ => by
        rw [interpP]; exact nBotElimJ _ (List.mem_cons_self ..) d)
  | .up (.or P Q) :: todo, done, Δ, ψ, hP, hΔ, hψ, _, d =>
      UpFrom.mk1
        (maxOver (fun (bh : {b // b ∈ invertPos (Pos.or P Q)}) =>
          match bh with
          | ⟨b', hb'⟩ =>
            (eMinPP sat (b' ++ todo) done Δ ψ hP hΔ hψ
              ((invUp (d.wk subHeadOut) b' hb').wk subChainIn)).1)
          (invertPos (Pos.or P Q)).attach)
        (fun e' he' => by
        rw [interpP]
        refine nOrAllElimJ _ (List.mem_cons_self ..) d ?_
        intro x hx Γ' hsub
        obtain ⟨⟨b, hb⟩, hmem, hEq⟩ := memMapWitness _ _ x hx
        subst hEq
        have hle := Nat.le_trans (le_maxOver hmem) he'
        refine (((eMinPP sat (b ++ todo) done Δ ψ hP hΔ hψ
          ((invUp (d.wk subHeadOut) b hb).wk subChainIn)).2 e' hle).wk ?_)
        intro Z hZ
        rcases List.mem_cons.mp hZ with rfl | hZ
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (hsub _ (List.mem_cons_of_mem _ hZ)))
  | .up (.down M) :: todo, done, Δ, ψ, hP, hΔ, hψ, _, d =>
      let w := eMinPP sat (M :: todo) done Δ ψ hP hΔ hψ
        (((invUp (d.wk subHeadOut) [M] (by simp [invertPos]))).wk subChainIn)
      UpFrom.mk1 w.1 (fun e' he' => by rw [interpP]; exact w.2 e' he')
  | .and M N :: todo, done, Δ, ψ, hP, hΔ, hψ, _, d =>
      let w := eMinPP sat (M :: N :: todo) done Δ ψ hP hΔ hψ
        ((invAndHyp (d.wk subHeadOut)).wk (subChainIn (b := [M, N])))
      UpFrom.mk1 w.1 (fun e' he' => by rw [interpP]; exact w.2 e' he')
  | .imp .fls N :: todo, done, Δ, ψ, hP, hΔ, hψ, _, d =>
      let w := eMinPP sat todo done Δ ψ hP hΔ hψ (invImpFls (d.wk subHeadOut))
      UpFrom.mk1 w.1 (fun e' he' => by rw [interpP]; exact w.2 e' he')
  | .imp (.atom a) N :: todo, done, Δ, ψ, hP, hΔ, hψ, _, d =>
      let w := eMinPP sat todo (.imp (.atom a) N :: done) Δ ψ
        (ParkedCtxP.cons (ParkedNP.qimp a N) hP) hΔ hψ (d.wk subParkOut)
      UpFrom.mk1 w.1 (fun e' he' => by rw [interpP]; exact w.2 e' he')
  | .imp (.or Q₁ Q₂) N :: todo, done, Δ, ψ, hP, hΔ, hψ, _, d =>
      let w := eMinPP sat todo (.imp (.or Q₁ Q₂) N :: done) Δ ψ
        (ParkedCtxP.cons (ParkedNP.oimp Q₁ Q₂ N) hP) hΔ hψ (d.wk subParkOut)
      UpFrom.mk1 w.1 (fun e' he' => by rw [interpP]; exact w.2 e' he')
  | .imp (.down (.up P')) N :: todo, done, Δ, ψ, hP, hΔ, hψ, _, d =>
      let w := eMinPP sat todo (.imp (.down (.up P')) N :: done) Δ ψ
        (ParkedCtxP.cons (ParkedNP.simp P' N) hP) hΔ hψ (d.wk subParkOut)
      UpFrom.mk1 w.1 (fun e' he' => by rw [interpP]; exact w.2 e' he')
  | .imp (.down (.and M₁ M₂)) N :: todo, done, Δ, ψ, hP, hΔ, hψ, _, d =>
      let w := eMinPP sat todo (.imp (.down (.and M₁ M₂)) N :: done) Δ ψ
        (ParkedCtxP.cons (ParkedNP.aimp M₁ M₂ N) hP) hΔ hψ (d.wk subParkOut)
      UpFrom.mk1 w.1 (fun e' he' => by rw [interpP]; exact w.2 e' he')
  | .imp (.down (.imp Q' N')) N :: todo, done, Δ, ψ, hP, hΔ, hψ, _, d =>
      let w := eMinPP sat todo (.imp (.down (.imp Q' N')) N :: done) Δ ψ
        (ParkedCtxP.cons (ParkedNP.dyk Q' N' N) hP) hΔ hψ (d.wk subParkOut)
      UpFrom.mk1 w.1 (fun e' he' => by rw [interpP]; exact w.2 e' he')
  | .circ Q :: todo, done, Δ, ψ, hP, hΔ, hψ, _, d =>
      let w := eMinPP sat todo (.circ Q :: done) Δ ψ
        (ParkedCtxP.cons (ParkedNP.box Q) hP) hΔ hψ (d.wk subParkOut)
      UpFrom.mk1 w.1 (fun e' he' => by rw [interpP]; exact w.2 e' he')
  | .imp (.down (.circ Q')) N :: todo, done, Δ, ψ, hP, hΔ, hψ, _, d =>
      let w := eMinPP sat todo (.imp (.down (.circ Q')) N :: done) Δ ψ
        (ParkedCtxP.cons (ParkedNP.cimp Q' N) hP) hΔ hψ (d.wk subParkOut)
      UpFrom.mk1 w.1 (fun e' he' => by rw [interpP]; exact w.2 e' he')
  | [], done, Δ, ψ, hP, hΔ, hψ, _, d =>
      match hf : findFire done (splits done) with
      | some (a, N, rest) =>
          let w := eMinPP sat [N] rest Δ ψ
            (ParkedCtxP.sub (splits_sub (findFire_mem hf)) hP) hΔ hψ
            (invFireHyp (findFire_mem hf) d)
          UpFrom.mk1 w.1 (fun e' he' => by
            rw [interpPFire_eq hf none]; exact w.2 e' he')
      | none => sat done Δ ψ hf hP hΔ hψ d
  termination_by todo done Δ ψ hP hΔ hψ j d => 2 * sum3 todo + sum3 done
  decreasing_by ljf_dec_e

/-- **Minimality of `∀p`, processing phase, at fuel.** -/
def aMinPP (sat : SatA2P p) :
    ∀ (todo done Δ : List Neg) (G : Neg), ParkedCtxP done →
      PFreeCtx p Δ → ∀ {j : JD},
      Inv ((todo ++ done) ++ Δ) [] j G →
      UpFrom2 (fun e f => Inv (interpP p e todo done none :: Δ) [] .tru
        (interpP p f todo done (some (jGoal j G))))
  | .up (.atom a) :: todo, done, Δ, G, hP, hΔ, _, d =>
      let w := aMinPP sat todo (.up (.atom a) :: done) Δ G
        (ParkedCtxP.cons (ParkedNP.atom a) hP) hΔ (d.wk subParkOut)
      UpFrom2.mk1 w.1 (fun e' f' he' hf' => by
        rw [interpP, interpP]; exact w.2 e' f' he' hf')
  | .up .fls :: todo, done, Δ, G, _, _, _, _ =>
      UpFrom2.mk1 0 (fun e' f' _ _ => by
        rw [interpP, interpP]; exact nBotElim _ (List.mem_cons_self ..))
  | .up (.or P Q) :: todo, done, Δ, G, hP, hΔ, _, d =>
      UpFrom2.mk1
        (maxOver (fun (bh : {b // b ∈ invertPos (Pos.or P Q)}) =>
          match bh with
          | ⟨b', hb'⟩ =>
            (aMinPP sat (b' ++ todo) done Δ G hP hΔ
              ((invUp (d.wk subHeadOut) b' hb').wk subChainIn)).1)
          (invertPos (Pos.or P Q)).attach)
        (fun e' f' he' hf' => by
        rw [interpP, interpP]
        refine nAndAllIntro ?_
        intro x hx
        obtain ⟨⟨b, hb⟩, hmem, hEq⟩ := memMapWitness _ _ x hx
        subst hEq
        refine .impR (.downL ?_)
        -- the `∀p` row guards itself with the `∃p` approximant at the
        -- SAME fuel, so the sub-witness is read on the diagonal at `f'`
        have hlf := Nat.le_trans (le_maxOver hmem) hf'
        refine (((aMinPP sat (b ++ todo) done Δ G hP hΔ
          ((invUp (d.wk subHeadOut) b hb).wk subChainIn)).2 f' f' hlf hlf).wk ?_)
        intro Z hZ
        rcases List.mem_cons.mp hZ with rfl | hZ
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ))
  | .up (.down M) :: todo, done, Δ, G, hP, hΔ, _, d =>
      let w := aMinPP sat (M :: todo) done Δ G hP hΔ
        (((invUp (d.wk subHeadOut) [M] (by simp [invertPos]))).wk subChainIn)
      UpFrom2.mk1 w.1 (fun e' f' he' hf' => by
        rw [interpP, interpP]; exact w.2 e' f' he' hf')
  | .and M N :: todo, done, Δ, G, hP, hΔ, _, d =>
      let w := aMinPP sat (M :: N :: todo) done Δ G hP hΔ
        ((invAndHyp (d.wk subHeadOut)).wk (subChainIn (b := [M, N])))
      UpFrom2.mk1 w.1 (fun e' f' he' hf' => by
        rw [interpP, interpP]; exact w.2 e' f' he' hf')
  | .imp .fls N :: todo, done, Δ, G, hP, hΔ, _, d =>
      let w := aMinPP sat todo done Δ G hP hΔ (invImpFls (d.wk subHeadOut))
      UpFrom2.mk1 w.1 (fun e' f' he' hf' => by
        rw [interpP, interpP]; exact w.2 e' f' he' hf')
  | .imp (.atom a) N :: todo, done, Δ, G, hP, hΔ, _, d =>
      let w := aMinPP sat todo (.imp (.atom a) N :: done) Δ G
        (ParkedCtxP.cons (ParkedNP.qimp a N) hP) hΔ (d.wk subParkOut)
      UpFrom2.mk1 w.1 (fun e' f' he' hf' => by
        rw [interpP, interpP]; exact w.2 e' f' he' hf')
  | .imp (.or Q₁ Q₂) N :: todo, done, Δ, G, hP, hΔ, _, d =>
      let w := aMinPP sat todo (.imp (.or Q₁ Q₂) N :: done) Δ G
        (ParkedCtxP.cons (ParkedNP.oimp Q₁ Q₂ N) hP) hΔ (d.wk subParkOut)
      UpFrom2.mk1 w.1 (fun e' f' he' hf' => by
        rw [interpP, interpP]; exact w.2 e' f' he' hf')
  | .imp (.down (.up P')) N :: todo, done, Δ, G, hP, hΔ, _, d =>
      let w := aMinPP sat todo (.imp (.down (.up P')) N :: done) Δ G
        (ParkedCtxP.cons (ParkedNP.simp P' N) hP) hΔ (d.wk subParkOut)
      UpFrom2.mk1 w.1 (fun e' f' he' hf' => by
        rw [interpP, interpP]; exact w.2 e' f' he' hf')
  | .imp (.down (.and M₁ M₂)) N :: todo, done, Δ, G, hP, hΔ, _, d =>
      let w := aMinPP sat todo (.imp (.down (.and M₁ M₂)) N :: done) Δ G
        (ParkedCtxP.cons (ParkedNP.aimp M₁ M₂ N) hP) hΔ (d.wk subParkOut)
      UpFrom2.mk1 w.1 (fun e' f' he' hf' => by
        rw [interpP, interpP]; exact w.2 e' f' he' hf')
  | .imp (.down (.imp Q' N')) N :: todo, done, Δ, G, hP, hΔ, _, d =>
      let w := aMinPP sat todo (.imp (.down (.imp Q' N')) N :: done) Δ G
        (ParkedCtxP.cons (ParkedNP.dyk Q' N' N) hP) hΔ (d.wk subParkOut)
      UpFrom2.mk1 w.1 (fun e' f' he' hf' => by
        rw [interpP, interpP]; exact w.2 e' f' he' hf')
  | .circ Q :: todo, done, Δ, G, hP, hΔ, _, d =>
      let w := aMinPP sat todo (.circ Q :: done) Δ G
        (ParkedCtxP.cons (ParkedNP.box Q) hP) hΔ (d.wk subParkOut)
      UpFrom2.mk1 w.1 (fun e' f' he' hf' => by
        rw [interpP, interpP]; exact w.2 e' f' he' hf')
  | .imp (.down (.circ Q')) N :: todo, done, Δ, G, hP, hΔ, _, d =>
      let w := aMinPP sat todo (.imp (.down (.circ Q')) N :: done) Δ G
        (ParkedCtxP.cons (ParkedNP.cimp Q' N) hP) hΔ (d.wk subParkOut)
      UpFrom2.mk1 w.1 (fun e' f' he' hf' => by
        rw [interpP, interpP]; exact w.2 e' f' he' hf')
  | [], done, Δ, G, hP, hΔ, j, d =>
      match hf : findFire done (splits done) with
      | some (a, N', rest) =>
          let w := aMinPP sat [N'] rest Δ G
            (ParkedCtxP.sub (splits_sub (findFire_mem hf)) hP) hΔ
            (invFireHyp (findFire_mem hf) d)
          UpFrom2.mk1 w.1 (fun e' f' he' hf' => by
            rw [interpPFire_eq hf none, interpPFire_eq hf (some (jGoal j G))]
            exact w.2 e' f' he' hf')
      | none => sat done Δ G hf hP hΔ d
  termination_by todo done Δ G hP hΔ j d =>
    2 * sum3 todo + sum3 done + 3 ^ wNeg G
  decreasing_by ljf_dec_a

end LJFO

/-! ### Axiom audit -/

#axioms_within LJFO.interpPE_eq [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.interpP_circ_laxRows [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.laxRowsP_of_eq [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.eMinPP [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.aMinPP [propext, Classical.choice, Quot.sound]

/-! The measured set for the row layer is smaller. -/

#axioms_within LJFO.interpPE_eq [propext]
#axioms_within LJFO.interpPFire_eq [propext]
#axioms_within LJFO.interpPA_atom_eq [propext]
#axioms_within LJFO.interpPA_atomT_eq [propext]
#axioms_within LJFO.interpPA_fls_eq [propext]
#axioms_within LJFO.interpPA_or_eq [propext]
#axioms_within LJFO.interpPA_down_eq [propext]
#axioms_within LJFO.interpPA_imp_eq [propext]
#axioms_within LJFO.interpPA_and_eq [propext]
#axioms_within LJFO.interpP_circ_laxRows [propext]
#axioms_within LJFO.laxRowsP_of_eq [propext]
