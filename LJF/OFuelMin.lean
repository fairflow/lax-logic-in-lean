/-
LJF◯ — the minimality layer over the fuel-founded retention interpolant
(route (B), layer 4c).

`LJF/OFuel.lean` defines `interpF`, the retention interpolant founded on
structural fuel; `LJF/OFuelSound.lean` proves both soundness halves at
every fuel.  This module is the minimality (cofinality) side: the row
layer of `LJF/ORows.lean` transposed to `interpF` at fuel `f+1`, the
upward-closed witness type the recursion needs, and the isolated modal
obligation of the retention rows.

Nothing in `LJF/OCore.lean`, `LJF/ORows.lean`, `LJF/O.lean`,
`LJF/OFuel.lean` or `LJF/OFuelSound.lean` is touched; this module is
purely additive.
-/
import LJF.O
import LJF.OFuel
import Meta.Audit

namespace LJFO

/-! # Part 1: upward-closed fuel witnesses

`interpF` has no chain-monotonicity lemma (`E_{f+1} ⊢ E_f` and
`A_f ⊢ A_{f+1}` are observed, not proved), so a bare `Σ f` witness cannot
be combined across several sub-results: two witnesses at fuels `f₁ ≠ f₂`
have no common instance.  Every statement below therefore carries an
upward-closed witness — a threshold, plus the family at every fuel above
it — which combines by `max`.

`UpFrom` is the ∃p side (one fuel, the `∃p`-approximant's).  `UpFrom2` is
the ∀p side: the `∃p`-approximant standing as a hypothesis and the
`∀p`-approximant standing as the goal decrement at different sites (the
∃p aggregate is opened by the row projections, the ∀p aggregate by the
goal dispatch), so their fuels are independent and one shared threshold
bounds both. -/

/-- "From some fuel on": the threshold is data, the closure is proved. -/
def UpFrom (P : Nat → Type) : Type := Σ f : Nat, ∀ f', f ≤ f' → P f'

/-- The two-fuel form: the `∃p` fuel and the `∀p` fuel above one
threshold. -/
def UpFrom2 (P : Nat → Nat → Type) : Type :=
  Σ n : Nat, ∀ e f, n ≤ e → n ≤ f → P e f

/-- Read an `UpFrom` witness at its own threshold. -/
def UpFrom.here {P : Nat → Type} (w : UpFrom P) : P w.1 := w.2 w.1 (Nat.le_refl _)

/-- Read an `UpFrom2` witness on the diagonal at its own threshold. -/
def UpFrom2.here {P : Nat → Nat → Type} (w : UpFrom2 P) : P w.1 w.1 :=
  w.2 w.1 w.1 (Nat.le_refl _) (Nat.le_refl _)

/-- Postcompose an `UpFrom` witness fuelwise. -/
def UpFrom.map {P Q : Nat → Type} (k : ∀ f, P f → Q f) (w : UpFrom P) :
    UpFrom Q :=
  ⟨w.1, fun f' hf' => k f' (w.2 f' hf')⟩

/-- Postcompose an `UpFrom2` witness fuelwise. -/
def UpFrom2.map {P Q : Nat → Nat → Type} (k : ∀ e f, P e f → Q e f)
    (w : UpFrom2 P) : UpFrom2 Q :=
  ⟨w.1, fun e f he hf => k e f (w.2 e f he hf)⟩

/-- Raise a threshold. -/
def UpFrom.raise {P : Nat → Type} (n : Nat) (w : UpFrom P) : UpFrom P :=
  ⟨max n w.1, fun f' hf' => w.2 f' (Nat.le_trans (Nat.le_max_right n w.1) hf')⟩

/-- Raise a threshold, two-fuel form. -/
def UpFrom2.raise {P : Nat → Nat → Type} (n : Nat) (w : UpFrom2 P) : UpFrom2 P :=
  ⟨max n w.1, fun e f he hf =>
    w.2 e f (Nat.le_trans (Nat.le_max_right n w.1) he)
            (Nat.le_trans (Nat.le_max_right n w.1) hf)⟩

/-- An `UpFrom` witness of a two-fuel family, on the diagonal. -/
def UpFrom2.diag {P : Nat → Nat → Type} (w : UpFrom2 P) :
    UpFrom (fun f => P f f) :=
  ⟨w.1, fun f' hf' => w.2 f' f' hf' hf'⟩

/-! # Part 2: the `∃p` station map at fuel `f+1`

`LJF/ORows.lean`'s `eConjRows`, transposed to `interpF`.  One difference,
and it is the point of route (B): the `◯`-implication row takes its
`∀p` guard at the FULL station `done`, where `interp` takes it at the
residual `rest`. -/

set_option linter.unusedVariables false in
/-- The conjunct rows of the `∃p` aggregate of `interpF` at fuel `f+1`
over a saturated station: one row per split, the residuals interpolated
at fuel `f`, the `◯`-implication guard RETAINED at `done`. -/
def eConjRowsF (p : String) (f : Nat) (done : List Neg) : List Neg :=
  (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
    match X with
    | .up (.atom a) => pGuard p a nTop (.up (.atom a))
    | .imp (.atom a) N =>
        pGuard p a nTop (.imp (.atom a) (interpF p f [N] rest none))
    | .imp (.down (.imp Q' N')) N =>
        nAnd
          (.imp (.down (interpF p f [.imp (.down N') N] rest
                         (some (.imp Q' N'))))
               (interpF p f [N] rest none))
          (interpF p f [.imp (.down N') N] rest none)
    | .circ Q =>
        .circ (.down (interpF p f [.up Q] rest none))
    | .imp (.down (.circ Q')) N =>
        nAnd
          (.imp (.down (interpF p f [] done (some (.up (.down (.circ Q'))))))
               (interpF p f [N] rest none))
          (interpF p f [] rest none)
    | _ => nTop)

/-- The saturated `∃p` aggregate of `interpF`, as an equation. -/
theorem interpFE_eq {p : String} {f : Nat} {done : List Neg}
    (hsat : Saturated done) :
    interpF p (f + 1) [] done none = nAndAll (eConjRowsF p f done) := by
  rw [interpF]; split
  all_goals rename_i heq
  · rw [hsat] at heq; cases heq
  · rfl

/-- The `∃p` conjunct of a `q`-implication member. -/
theorem qimpConjMemF {p : String} {f : Nat} {done : List Neg} {a : String}
    {N : Neg} {rest : List Neg}
    (hXr : (Neg.imp (.atom a) N, rest) ∈ splits done) :
    pGuard p a nTop (.imp (.atom a) (interpF p f [N] rest none)) ∈
      eConjRowsF p f done :=
  rowMem hXr

/-- Likewise for a surviving atom. -/
theorem atomConjMemF {p : String} {f : Nat} {done : List Neg} {a : String}
    {rest : List Neg} (hXr : (Neg.up (.atom a), rest) ∈ splits done) :
    pGuard p a nTop (.up (.atom a)) ∈ eConjRowsF p f done :=
  rowMem hXr

/-- And for a Dyckhoff member. -/
theorem dykConjMemF {p : String} {f : Nat} {done : List Neg} {Q' : Pos}
    {N' N : Neg} {rest : List Neg}
    (hXr : (Neg.imp (.down (.imp Q' N')) N, rest) ∈ splits done) :
    nAnd
      (.imp (.down (interpF p f [.imp (.down N') N] rest (some (.imp Q' N'))))
           (interpF p f [N] rest none))
      (interpF p f [.imp (.down N') N] rest none) ∈ eConjRowsF p f done :=
  rowMem hXr

/-- And for a parked box. -/
theorem boxConjMemF {p : String} {f : Nat} {done : List Neg} {Q : Pos}
    {rest : List Neg} (hXr : (Neg.circ Q, rest) ∈ splits done) :
    Neg.circ (.down (interpF p f [.up Q] rest none)) ∈ eConjRowsF p f done :=
  rowMem hXr

/-- And for a `◯`-implication member — the retention row: the guard is the
`∀p` of `↑↓◯Q′` at `done`, not at `rest`. -/
theorem cimpConjMemF {p : String} {f : Nat} {done : List Neg} {Q' : Pos}
    {N : Neg} {rest : List Neg}
    (hXr : (Neg.imp (.down (.circ Q')) N, rest) ∈ splits done) :
    nAnd
      (.imp (.down (interpF p f [] done (some (.up (.down (.circ Q'))))))
           (interpF p f [N] rest none))
      (interpF p f [] rest none) ∈ eConjRowsF p f done :=
  rowMem hXr

/-! # Part 3: the `tru`-goal station map at fuel `f+1` -/

set_option linter.unusedVariables false in
/-- The station rows of every `↑`-goal aggregate of `interpF` at fuel
`f+1`; identical across all four shifted goal shapes. -/
def truStationRowsF (p : String) (f : Nat) (done : List Neg) (G : Pos) :
    List Neg :=
  (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
    match X, hXr with
    | .imp (.atom a) N, hXr =>
        pGuard p a nBot
          (nAnd (.up (.atom a)) (interpF p f [N] rest (some (.up G))))
    | .imp (.down (.imp Q' N')) N, hXr =>
        nAnd (interpF p f [.imp (.down N') N] rest (some (.imp Q' N')))
             (interpF p f [N] rest (some (.up G)))
    | .imp (.down (.circ Q')) N, hXr =>
        nAnd (interpF p f [] done (some (.up (.down (.circ Q')))))
             (interpF p f [N] rest (some (.up G)))
    | _, _ => nBot)

theorem interpFA_atom_eq {p : String} {f : Nat} {done : List Neg}
    (hsat : Saturated done) {q : String} (hq : ¬ atomMem q done = true) :
    interpF p (f + 1) [] done (some (.up (.atom q))) =
      nOrAll (atomHead p q ++ truStationRowsF p f done (.atom q)) := by
  rw [interpF]; split
  all_goals rename_i heq
  · rw [hsat] at heq; cases heq
  · simp only [hq, if_false, Bool.false_eq_true]; rfl

theorem interpFA_atomT_eq {p : String} {f : Nat} {done : List Neg}
    (hsat : Saturated done) {q : String} (hq : atomMem q done = true) :
    interpF p (f + 1) [] done (some (.up (.atom q))) = nTop := by
  rw [interpF]; split
  all_goals rename_i heq
  · rw [hsat] at heq; cases heq
  · simp [hq]

theorem interpFA_fls_eq {p : String} {f : Nat} {done : List Neg}
    (hsat : Saturated done) :
    interpF p (f + 1) [] done (some (.up .fls)) =
      nOrAll (truStationRowsF p f done .fls) := by
  rw [interpF]; split
  all_goals rename_i heq
  · rw [hsat] at heq; cases heq
  · rfl

theorem interpFA_or_eq {p : String} {f : Nat} {done : List Neg}
    (hsat : Saturated done) (P₁ P₂ : Pos) :
    interpF p (f + 1) [] done (some (.up (.or P₁ P₂))) =
      nOrAll ([interpF p f [] done (some (.up P₁)),
               interpF p f [] done (some (.up P₂))] ++
              truStationRowsF p f done (.or P₁ P₂)) := by
  rw [interpF]; split
  all_goals rename_i heq
  · rw [hsat] at heq; cases heq
  · rfl

theorem interpFA_down_eq {p : String} {f : Nat} {done : List Neg}
    (hsat : Saturated done) (M : Neg) :
    interpF p (f + 1) [] done (some (.up (.down M))) =
      nOrAll ([interpF p f [] done (some M)] ++
              truStationRowsF p f done (.down M)) := by
  rw [interpF]; split
  all_goals rename_i heq
  · rw [hsat] at heq; cases heq
  · rfl

theorem interpFA_imp_eq {p : String} {f : Nat} {done : List Neg}
    (hsat : Saturated done) (Q : Pos) (N : Neg) :
    interpF p (f + 1) [] done (some (.imp Q N)) =
      nAndAll ((invertPos Q).attach.map
        (fun ⟨b, hb⟩ =>
          .imp (.down (interpF p f b done none))
            (interpF p f b done (some N)))) := by
  rw [interpF]; split
  all_goals rename_i heq
  · rw [hsat] at heq; cases heq
  · rfl

theorem interpFA_and_eq {p : String} {f : Nat} {done : List Neg}
    (hsat : Saturated done) (M N : Neg) :
    interpF p (f + 1) [] done (some (.and M N)) =
      nAnd (interpF p f [] done (some M)) (interpF p f [] done (some N)) := by
  rw [interpF]; split
  all_goals rename_i heq
  · rw [hsat] at heq; cases heq
  · rfl

/-! # Part 4: the ◯-goal row family at fuel `f+1` -/

set_option linter.unusedVariables false in
/-- The station rows of every ◯-goal aggregate of `interpF` at fuel `f+1`;
identical across all seven goal shapes. -/
def circStationRowsF (p : String) (f : Nat) (done : List Neg) (G : Pos) :
    List Neg :=
  (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
    match X, hXr with
    | .imp (.atom a) N, hXr =>
        pGuard p a nBot
          (nAnd (.up (.atom a)) (interpF p f [N] rest (some (.circ G))))
    | .imp (.down (.imp Q' N')) N, hXr =>
        nAnd (interpF p f [.imp (.down N') N] rest (some (.imp Q' N')))
             (interpF p f [N] rest (some (.circ G)))
    | .imp (.down (.circ Q')) N, hXr =>
        nAnd (interpF p f [] done (some (.up (.down (.circ Q')))))
             (interpF p f [N] rest (some (.circ G)))
    | .circ R, hXr =>
        .imp (.down (interpF p f [.up R] rest none))
             (interpF p f [.up R] rest (some (.circ G)))
    | _, _ => nBot)

/-- The lax goal-inversion prefix at fuel `f+1`, by goal shape. -/
def laxPrefixF (p : String) (f : Nat) (done : List Neg) : Pos → List Neg
  | .atom q => [interpF p f [] done (some (.up (.atom q)))]
  | .fls => [interpF p f [] done (some (.up .fls))]
  | .or P₁ P₂ => [interpF p f [] done (some (.circ P₁)),
                  interpF p f [] done (some (.circ P₂)),
                  interpF p f [] done (some (.up (.or P₁ P₂)))]
  | .down (.up P') => [interpF p f [] done (some (.circ P'))]
  | .down (.circ P') => [interpF p f [] done (some (.circ P'))]
  | .down (.and M₁ M₂) =>
      [interpF p f [] done (some (.up (.down (.and M₁ M₂))))]
  | .down (.imp Q₀ N₀) =>
      [interpF p f [] done (some (.up (.down (.imp Q₀ N₀))))]

/-- The ◯-goal row family at fuel `f+1`. -/
def laxRowsF (p : String) (f : Nat) (done : List Neg) (Q : Pos) : List Neg :=
  laxPrefixF p f done Q ++ circStationRowsF p f done Q

/-- **The unified ◯-goal equation** for `interpF` at fuel `f+1`. -/
theorem interpF_circ_laxRows {p : String} {f : Nat} {done : List Neg}
    (hsat : Saturated done) (Q : Pos) :
    interpF p (f + 1) [] done (some (.circ Q)) =
      .circ (.down (nOrAll (laxRowsF p f done Q))) := by
  match Q with
  | .atom _ | .fls | .or _ _ | .down (.up _) | .down (.circ _)
  | .down (.and _ _) | .down (.imp _ _) =>
    conv => lhs; rw [interpF]
    split
    all_goals rename_i heq
    · rw [hsat] at heq; cases heq
    · rfl

/-- The row list of a ◯-goal aggregate at fuel `f+1` is `laxRowsF`. -/
theorem laxRowsF_of_eq {p : String} {f : Nat} {done : List Neg} {L : List Neg}
    (hsat : Saturated done) (Q : Pos)
    (hV : interpF p (f + 1) [] done (some (.circ Q)) =
      .circ (.down (nOrAll L))) :
    L = laxRowsF p f done Q :=
  nOrAll_inj (Pos.down.inj (Neg.circ.inj
    (hV.symm.trans (interpF_circ_laxRows hsat Q))))

/-- The fired-`q`-implication row. -/
theorem laxRowsF_qimpMem {p : String} {f : Nat} {done : List Neg} {Q : Pos}
    {c : String} {Nc : Neg} {rest : List Neg}
    (hsp : (Neg.imp (.atom c) Nc, rest) ∈ splits done) :
    pGuard p c nBot (nAnd (.up (.atom c))
      (interpF p f [Nc] rest (some (.circ Q)))) ∈ laxRowsF p f done Q :=
  rowMemR hsp

/-- The Dyckhoff row. -/
theorem laxRowsF_dykMem {p : String} {f : Nat} {done : List Neg} {Q : Pos}
    {Q' : Pos} {N' N : Neg} {rest : List Neg}
    (hsp : (Neg.imp (.down (.imp Q' N')) N, rest) ∈ splits done) :
    nAnd (interpF p f [.imp (.down N') N] rest (some (.imp Q' N')))
         (interpF p f [N] rest (some (.circ Q))) ∈ laxRowsF p f done Q :=
  rowMemR hsp

/-- The `◯`-implication row — retained at `done`. -/
theorem laxRowsF_cimpMem {p : String} {f : Nat} {done : List Neg} {Q : Pos}
    {Q' : Pos} {N : Neg} {rest : List Neg}
    (hsp : (Neg.imp (.down (.circ Q')) N, rest) ∈ splits done) :
    nAnd (interpF p f [] done (some (.up (.down (.circ Q')))))
         (interpF p f [N] rest (some (.circ Q))) ∈ laxRowsF p f done Q :=
  rowMemR hsp

/-- The opened-box row — the lax-only one (`circL`). -/
theorem laxRowsF_boxMem {p : String} {f : Nat} {done : List Neg} {Q : Pos}
    {R : Pos} {rest : List Neg}
    (hsp : (Neg.circ R, rest) ∈ splits done) :
    Neg.imp (.down (interpF p f [.up R] rest none))
      (interpF p f [.up R] rest (some (.circ Q))) ∈ laxRowsF p f done Q :=
  rowMemR hsp

/-! # Part 5: the cofinality statements at a saturated station -/

/-- Minimality of `∃p` at a saturated station, fuel form: the ∃p
approximant is cofinal for the `p`-free consequences of the station. -/
def SatE2F (p : String) : Type :=
  ∀ (done Δ : List Neg) (ψ : Neg), Saturated done → ParkedCtx done →
    PFreeCtx p Δ → PFreeN p ψ →
    ∀ {j : JD}, Inv (done ++ Δ) [] j ψ →
      UpFrom (fun e => Inv (interpF p e [] done none :: Δ) [] j ψ)

/-- Minimality of `∀p` at a saturated station, fuel form (E-relativised, as
`SatA2`).  The `∃p` fuel `e` and the `∀p` fuel `f` are independent. -/
def SatA2F (p : String) : Type :=
  ∀ (done Δ : List Neg) (G : Neg), Saturated done → ParkedCtx done →
    PFreeCtx p Δ →
    ∀ {j : JD}, Inv (done ++ Δ) [] j G →
      UpFrom2 (fun e f => Inv (interpF p e [] done none :: Δ) [] .tru
        (interpF p f [] done (some (jGoal j G))))

/-! # Part 6: the isolated modal obligation of the retention rows

Twelve rows of `interpF` carry `A_f(done ⇒ ↑↓◯Q′)` — the `∀p` guard of a
parked `↓◯Q′ ⊃ N` at the FULL station.  Using such a row (projecting the
fire out of the `∃p` aggregate, or emitting the attack disjunct of a `∀p`
aggregate) requires deriving that guard from a main-line stable proof of
the antecedent.  This is the fuel analogue of `LJF/O.lean`'s `CimpAnt`,
with `rest` replaced by `done` throughout — the change route (B) was
built for. -/

/-- **The isolated modal obligation, retention form.**  From a main-line
stable proof of `↓◯Q′` over a mixed context `Γ′ ⊆ done ∪ K`, derive the
`∀p` interpolant of `↑↓◯Q′` at the FULL station `done`, on the interpolant
side, from some fuel on. -/
def CimpAntF (p : String) : Type :=
  ∀ (done rest K Γ' : List Neg) (Q' : Pos) (N : Neg),
    Saturated done → ParkedCtx done →
    (Neg.imp (.down (.circ Q')) N, rest) ∈ splits done →
    (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
    Stab Γ' .tru (.down (.circ Q')) →
    UpFrom2 (fun e f => Inv (interpF p e [] done none :: K) [] .tru
      (interpF p f [] done (some (.up (.down (.circ Q'))))))

/-- **The retention obligation is an instance of `∀p`-cofinality itself**,
at the SAME station and applied to the antecedent's own subderivation.

This is the content of the retention design: where `LJF/O.lean`'s
`CimpAnt` asks for the `∀p` interpolant at the RESIDUAL station `rest` —
unreachable from a proof over a context containing the full station, which
is why it stands isolated there — the retention rows ask for it at `done`,
and `done ∪ K` is exactly the context the antecedent proof lives over.  So
no descent machinery is needed to state the discharge: it is `SatA2F`
applied to `Inv.stable s`.

What this does NOT give is a discharge inside the minimality recursion:
`SatA2F` is the statement being proved, at the same station, so the appeal
is a recursive call at an unchanged station weight, and it is founded only
if the recursion is founded on the derivation — see the module note. -/
def cimpAntF_of_satA2F {p : String} (a2 : SatA2F p) : CimpAntF p :=
  fun done rest K Γ' Q' N hsat hP _hXr hm _hm2 hK s =>
    ((a2 done K (.up (.down (.circ Q'))) hsat hP hK (j := .tru)
      ((Inv.stable s).wk (fun Z hZ => by
        rcases hm Z hZ with hd | hk
        · exact List.mem_append_left _ hd
        · exact List.mem_append_right _ hk))).map
      (fun _e _f d => by rw [jGoal_tru] at d; exact d))

end LJFO

/-! ### Axiom audit

The standard bound first, then the measured set, which is smaller: every
declaration of this module is `[propext]`.  `sorryAx` appears nowhere. -/

#axioms_within LJFO.interpFE_eq [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.interpF_circ_laxRows [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.laxRowsF_of_eq [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.cimpAntF_of_satA2F [propext, Classical.choice, Quot.sound]

#axioms_within LJFO.interpFE_eq [propext]
#axioms_within LJFO.interpFA_atom_eq [propext]
#axioms_within LJFO.interpFA_atomT_eq [propext]
#axioms_within LJFO.interpFA_fls_eq [propext]
#axioms_within LJFO.interpFA_or_eq [propext]
#axioms_within LJFO.interpFA_down_eq [propext]
#axioms_within LJFO.interpFA_imp_eq [propext]
#axioms_within LJFO.interpFA_and_eq [propext]
#axioms_within LJFO.interpF_circ_laxRows [propext]
#axioms_within LJFO.laxRowsF_of_eq [propext]
#axioms_within LJFO.cimpAntF_of_satA2F [propext]
