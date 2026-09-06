/-
Route (B), node **N4**, WP12c: the escape-carrying cofinality statements for
`interpR`, **restated so that the escapes do not mention the current
station**, with the specialisation to `SatE2R`/`SatA2R` and the four
structural steps at which the record changes.

## What changed against `wip/ui_routeB_r_esc.lean` (§4.32), and why

§4.32's escapes are indexed by the CURRENT station:

    escRowsR p f done seen = [ A^R(done ⇒ ↑Q | seen) | (Q,T) ∈ seen, sameSet T done ]
    escConjR p e done seen = [ ↓A^R(done ⇒ ↑Qa | (Qa,done)::seen) ⊃ E^R([N],rest | seen)
                             | (Qa ⊃ N, rest) ∈ splits done, seenMemR seen Qa done ]

Both lists therefore CHANGE along every station-changing edge of the
recursion, and the induction has no clause that can move them:

* `∀p`.  The station-attack clause reads its continuation at the residue
  state `([N], rest)`, whose escapes are those of the pairs set-equal to the
  RESIDUE station.  A pair `(Q,T)` with `sameSet T done''` and not
  `sameSet T done` yields a disjunct at the residue that is not a permitted
  disjunct of the conclusion at `done`, and there is nothing to convert it
  with (the two `interpR` values sit at different, unrelated stations).
* `∃p`.  Dually, the conjuncts are HYPOTHESES: to apply the induction
  hypothesis at the residue state one must SUPPLY the residue's cut
  conjuncts, and `E^R(done | seen)` together with the conjuncts at `done`
  does not supply them.

This is a statement fault, not a proof fault, and it is repaired by indexing
the escapes by the RECORD alone — each recorded pair carries its escape at
its OWN station, with the record it had.  Since the record is carried
unchanged along every edge but the guard call (`interpR = interpGR id`), both
lists are then LITERALLY CONSTANT along every ordinary edge, and the only
site at which they move is the site the loop check was designed for:

    escConjS p e []             = []
    escConjS p e (QT :: s)      = E^R(T | s)                :: escConjS p e s
    escRowsS p f []             = []
    escRowsS p f (QT :: s)      = A^R(T ⇒ ↑Q | QT :: s)     :: escRowsS p f s

The `∃p` conjunct of a recorded pair is the `∃p` approximant at its station
with the record it had BEFORE the pair was recorded — the record under which
the row that the loop check later cuts is still present.  The `∀p` escape is
the `∀p` approximant of the guard sequent at that station, with the record as
EXTENDED by the pair — exactly the guard conjunct of `parkRowAR`.

Part 3 proves the four steps this indexing exists for:

* `escHyp_record`   — at the guard call the `∃p` hypothesis at the extended
  record is supplied by the one in hand (its new head is the head we hold);
* `escGoal_absorb`  — at the guard call the escape-carrying `∀p` conclusion
  collapses to "the guard conjunct, or one of the escapes already permitted
  here" (the new escape IS the guard conjunct);
* `escHyp_recorded` — at a CUT site the `∃p` hypothesis of the statement at
  the recorded station and record is among the conjuncts in hand;
* `escGoal_escape`  — at a CUT site the escape-carrying `∀p` conclusion at
  the recorded station and record is a disjunction of escapes permitted here.

`escRowsR`/`escConjR` of §4.32 are left in place, untouched, in
`wip/ui_routeB_r_esc.lean`; nothing imports them from here except the two
singleton lemmas.  `LJF/` is untouched; this module is a leaf.
-/
import wip.ui_routeB_r_esc
import wip.ui_routeB_r_seenmono
import Meta.Audit

set_option autoImplicit false

namespace LJFO

/-! # Part 0 · Two list-shaped entailments -/

/-- Project a conjunct out of a list conjunction. -/
def nAndAllProj {l : List Neg} {x : Neg} (hx : x ∈ l) :
    Inv [nAndAll l] [] .tru x :=
  simHyp (H := x) (Γ := []) (Δ₀ := [nAndAll l])
    (fun hs lf => .lfoc (hs _ (List.mem_cons_self ..)) (lfocAndAll hx lf))
    (fun _ hc => absurd hc List.not_mem_nil)
    (idNeg x [x] (List.mem_cons_self ..))

/-- The head conjunct of a non-empty list conjunction. -/
def nAndAllHead {x : Neg} {l : List Neg} : Inv [nAndAll (x :: l)] [] .tru x :=
  simHyp (H := x) (Γ := []) (Δ₀ := [nAndAll (x :: l)])
    (fun hs lf => .lfoc (hs _ (List.mem_cons_self ..)) (.and1 lf))
    (fun _ hc => absurd hc List.not_mem_nil)
    (idNeg x [x] (List.mem_cons_self ..))

/-- The tail conjunction of a non-empty list conjunction. -/
def nAndAllTail {x : Neg} {l : List Neg} :
    Inv [nAndAll (x :: l)] [] .tru (nAndAll l) :=
  simHyp (H := nAndAll l) (Γ := []) (Δ₀ := [nAndAll (x :: l)])
    (fun hs lf => .lfoc (hs _ (List.mem_cons_self ..)) (.and2 lf))
    (fun _ hc => absurd hc List.not_mem_nil)
    (idNeg (nAndAll l) [nAndAll l] (List.mem_cons_self ..))

/-- `nAndAll` is antitone under member inclusion. -/
def nAndAllSub {l m : List Neg} (h : ∀ X ∈ m, X ∈ l) :
    Inv [nAndAll l] [] .tru (nAndAll m) :=
  nAndAllIntro (fun x hx => nAndAllProj (h x hx))

/-- `nOrAll` is monotone under member inclusion. -/
def nOrAllSub {l m : List Neg} (h : ∀ X ∈ l, X ∈ m) :
    Inv [nOrAll l] [] .tru (nOrAll m) :=
  nOrAllElim (nOrAll m) (List.mem_cons_self ..)
    (fun x hx _Γ' _hs => nOrAllIntro (h x hx) (idNeg x _ (List.mem_cons_self ..)))

/-! # Part 1 · The escapes, indexed by the record alone -/

/-- The `∃p` escape conjuncts: one per recorded pair, the `∃p` approximant at
its own station under the record it had before being recorded. -/
def escConjS (p : String) (e : Nat) : SeenR → List Neg
  | [] => []
  | QT :: s => interpR p e [] QT.2 none s :: escConjS p e s

/-- The `∀p` escape disjuncts: one per recorded pair, the `∀p` approximant of
its guard sequent at its own station, under the record as extended by it —
literally the guard conjunct of `parkRowAR` at the recording site. -/
def escRowsS (p : String) (f : Nat) : SeenR → List Neg
  | [] => []
  | QT :: s => interpR p f [] QT.2 (some (.up QT.1)) (QT :: s) :: escRowsS p f s

/-- The `∃p` hypothesis of the escape-carrying statements. -/
def escHyp (p : String) (e : Nat) (done : List Neg) (seen : SeenR) : Neg :=
  nAndAll (interpR p e [] done none seen :: escConjS p e seen)

/-- The `∀p` conclusion of the escape-carrying statement. -/
def escGoal (p : String) (f : Nat) (done : List Neg) (g : Neg) (seen : SeenR) : Neg :=
  nOrAll (interpR p f [] done (some g) seen :: escRowsS p f seen)

theorem escConjS_nil (p : String) (e : Nat) : escConjS p e [] = [] := rfl

theorem escRowsS_nil (p : String) (f : Nat) : escRowsS p f [] = [] := rfl

theorem escHyp_nil (p : String) (e : Nat) (done : List Neg) :
    escHyp p e done [] = nAndAll [interpR p e [] done none []] := rfl

theorem escGoal_nil (p : String) (f : Nat) (done : List Neg) (g : Neg) :
    escGoal p f done g [] = nOrAll [interpR p f [] done (some g) []] := rfl

-- Both lists are blind to the station: `escConjS` and `escRowsS` take no
-- station argument at all, so they are LITERALLY unchanged along every edge
-- of `interpR` that does not touch the record — which is every edge but the
-- guard call.  That is the whole point of the restatement, and it is a fact
-- about the two signatures above, not a theorem.

/-! ## Suffix inclusion

The record grows by consing, so the record of any ancestor state is a SUFFIX
of the current one, and both escape lists are suffix-monotone. -/

theorem escConjS_suffix (p : String) (e : Nat) :
    ∀ (t u : SeenR) (X : Neg), X ∈ escConjS p e u → X ∈ escConjS p e (t ++ u)
  | [], _, _, h => h
  | _ :: t, u, X, h =>
      List.mem_cons_of_mem _ (escConjS_suffix p e t u X h)

theorem escRowsS_suffix (p : String) (f : Nat) :
    ∀ (t u : SeenR) (X : Neg), X ∈ escRowsS p f u → X ∈ escRowsS p f (t ++ u)
  | [], _, _, h => h
  | _ :: t, u, X, h =>
      List.mem_cons_of_mem _ (escRowsS_suffix p f t u X h)

/-! # Part 2 · The escape-carrying statements (typed obligations, OPEN) -/

/-- **Cofinality with escapes, `∃p` side** (OPEN).  At every station and every
record, the `∃p` approximant computed with that record, strengthened by one
conjunct per recorded pair, is cofinal for the `p`-free consequences of the
station. -/
def SatE2RS (p : String) : Type :=
  ∀ (done Δ : List Neg) (ψ : Neg) (seen : SeenR), Saturated done →
    ParkedCtxP done → PFreeCtx p Δ → PFreeN p ψ →
    ∀ {j : JD}, Inv (done ++ Δ) [] j ψ →
      UpFrom (fun e => Inv (escHyp p e done seen :: Δ) [] j ψ)

/-- **Cofinality with escapes, `∀p` side** (OPEN), E-relativised as `SatA2P`
is.  The conclusion is weakened by one disjunct per recorded pair. -/
def SatA2RS (p : String) : Type :=
  ∀ (done Δ : List Neg) (G : Neg) (seen : SeenR), Saturated done →
    ParkedCtxP done → PFreeCtx p Δ →
    ∀ {j : JD}, Inv (done ++ Δ) [] j G →
      UpFrom2 (fun e f => Inv (escHyp p e done seen :: Δ) [] .tru
        (escGoal p f done (jGoal j G) seen))

/-! # Part 3 · The four structural steps

Each is a theorem about the STATEMENTS, provable without the induction; they
are what the record indexing exists for. -/

/-- **The guard call, `∃p` side.**  At the site where the record grows the
hypothesis of the statement at the extended record is supplied by the
hypothesis in hand: its new head is `E^R(done | seen)`, which is the head we
hold, and its old head weakens by record monotonicity. -/
noncomputable def escHyp_record (p : String) (e : Nat) (done : List Neg)
    (Qa : Pos) (seen : SeenR) :
    Inv [escHyp p e done seen] [] .tru (escHyp p e done ((Qa, done) :: seen)) :=
  .andR (cut1N nAndAllHead (interpR_seenStepE p e [] done (Qa, done) seen))
    (idNeg _ _ (List.mem_cons_self ..))

/-- **The guard call, `∀p` side — absorption.**  The escape-carrying
conclusion at the extended record, read at the guard's own goal, is exactly
"the guard conjunct of `parkRowAR`, or one of the escapes already permitted
at the recording state": the escape the extension adds IS the guard
conjunct. -/
noncomputable def escGoal_absorb (p : String) (f : Nat) (done : List Neg)
    (Qa : Pos) (seen : SeenR) :
    Inv [escGoal p f done (.up Qa) ((Qa, done) :: seen)] [] .tru
        (nOrAll (interpR p f [] done (some (.up Qa)) ((Qa, done) :: seen)
                  :: escRowsS p f seen)) := by
  refine nOrAllSub ?_
  intro X hX
  rcases List.mem_cons.mp hX with rfl | hX
  · exact List.mem_cons_self ..
  · rcases List.mem_cons.mp hX with rfl | hX
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ hX

/-- **A cut site, `∃p` side.**  When the loop check fires for a recorded pair
`(Q, T)` — necessarily `t ++ (Q,T) :: s` for the current record — the
hypothesis of the statement AT the recorded station and record is among the
conjuncts in hand. -/
noncomputable def escHyp_recorded (p : String) (e : Nat) (done : List Neg)
    (t : SeenR) (Q : Pos) (T : List Neg) (s : SeenR) :
    Inv [escHyp p e done (t ++ (Q, T) :: s)] [] .tru (escHyp p e T s) := by
  refine nAndAllSub ?_
  intro X hX
  rcases List.mem_cons.mp hX with rfl | hX
  · exact List.mem_cons_of_mem _
      (escConjS_suffix p e t ((Q, T) :: s) _ (List.mem_cons_self ..))
  · exact List.mem_cons_of_mem _
      (escConjS_suffix p e t ((Q, T) :: s) X (List.mem_cons_of_mem _ hX))

/-- **A cut site, `∀p` side — production.**  The escape-carrying conclusion of
the statement at the recorded station and record, read at the recorded pair's
own goal, is a disjunction of escapes permitted at the current state. -/
noncomputable def escGoal_escape (p : String) (f : Nat)
    (t : SeenR) (Q : Pos) (T : List Neg) (s : SeenR) :
    Inv [escGoal p f T (.up Q) ((Q, T) :: s)] [] .tru
        (nOrAll (escRowsS p f (t ++ (Q, T) :: s))) := by
  refine nOrAllSub ?_
  intro X hX
  rcases List.mem_cons.mp hX with rfl | hX
  · exact escRowsS_suffix p f t ((Q, T) :: s) _ (List.mem_cons_self ..)
  · exact escRowsS_suffix p f t ((Q, T) :: s) X hX

/-! # Part 4 · The specialisation at the empty record -/

/-- **The `∃p` generalisation specialises to the residual.** -/
noncomputable def satE2R_of_escapesS {p : String} (w : SatE2RS p) : SatE2R p :=
  fun done Δ ψ hsat hP hΔ hψ {_j} d =>
    (w done Δ ψ [] hsat hP hΔ hψ d).map (fun e dd => by
      rw [escHyp_nil] at dd
      have h := cutInv [interpR p e [] done none []] Δ _j
        (nAndAll [interpR p e [] done none []]) ψ
        (nAndAll_singleton_intro _) dd
      simpa using h)

/-- **The `∀p` generalisation specialises to the residual.** -/
noncomputable def satA2R_of_escapesS {p : String} (w : SatA2RS p) : SatA2R p :=
  fun done Δ G hsat hP hΔ {_j} d =>
    (w done Δ G [] hsat hP hΔ d).map (fun e f dd => by
      rw [escHyp_nil, escGoal_nil] at dd
      have h1 := cutInv [interpR p e [] done none []] Δ .tru
        (nAndAll [interpR p e [] done none []])
        (nOrAll [interpR p f [] done (some (jGoal _j G)) []])
        (nAndAll_singleton_intro _) dd
      have h2 : Inv (interpR p e [] done none [] :: Δ) [] .tru
          (nOrAll [interpR p f [] done (some (jGoal _j G)) []]) := by simpa using h1
      have h3 := cutInv (interpR p e [] done none [] :: Δ) [] .tru
        (nOrAll [interpR p f [] done (some (jGoal _j G)) []])
        (interpR p f [] done (some (jGoal _j G)) [])
        h2 (nOrAll_singleton_elim _)
      simpa using h3)

/-- **`PLL_UI` over the restated escape-carrying statements alone**, with
`SatE2P`/`SatA2P` (inhabited by `satE2P`/`satA2P`, `LJF/OFuelPCofinal.lean`)
kept as variables because this leaf must not import the family. -/
noncomputable def pll_ui_R_escS (s2 : ∀ p, SatE2P p) (a2 : ∀ p, SatA2P p)
    (we : ∀ p, SatE2RS p) (wa : ∀ p, SatA2RS p) : PLL_UI :=
  pll_ui_R s2 a2 (fun p => satE2R_of_escapesS (we p))
    (fun p => satA2R_of_escapesS (wa p))

end LJFO

/-! ## Pins -/

#axioms_within LJFO.nAndAllProj [propext, Quot.sound]
#axioms_within LJFO.nAndAllHead [propext, Quot.sound]
#axioms_within LJFO.nAndAllTail [propext, Quot.sound]
#axioms_within LJFO.nAndAllSub [propext, Quot.sound]
#axioms_within LJFO.nOrAllSub [propext, Quot.sound]
#axioms_within LJFO.escConjS_nil [propext]
#axioms_within LJFO.escRowsS_nil [propext]
#axioms_within LJFO.escHyp_nil [propext]
#axioms_within LJFO.escGoal_nil [propext]
#axioms_within LJFO.escConjS_suffix [propext]
#axioms_within LJFO.escRowsS_suffix [propext]
#axioms_within LJFO.escHyp_record [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.escGoal_absorb [propext, Quot.sound]
#axioms_within LJFO.escHyp_recorded [propext, Quot.sound]
#axioms_within LJFO.escGoal_escape [propext, Quot.sound]
#axioms_within LJFO.satE2R_of_escapesS [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.satA2R_of_escapesS [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.pll_ui_R_escS [propext, Classical.choice, Quot.sound]
