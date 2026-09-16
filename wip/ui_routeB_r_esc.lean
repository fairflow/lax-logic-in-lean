/-
Route (B), node **N4**, WP12b, **stage 3**: the escape-carrying
generalisation of cofinality for `interpR`, as a typed obligation, and the
proof that it SPECIALISES to the residual `SatE2R` / `SatA2R` at the empty
record.

**Status.**  `SatE2RE` and `SatA2RE` are DESIGN — typed obligations, no term
of either type is built here (rule 1: an open case is a parameter, never a
`sorry`).  The two THEOREMS of this module are the specialisations

    satE2R_of_escapes : SatE2RE p → SatE2R p
    satA2R_of_escapes : SatA2RE p → SatA2R p

which are the check that the generalisation is the right one: at `seen = []`
the escape lists are literally empty, so the escape-carrying statement
collapses to the residual up to the unit of `nAndAll` / `nOrAll`.

**Why a generalisation is needed at all** (`docs/ui-ljfo-clause-table.md`
§4.28).  Cofinality for `interpR` cannot be had from cofinality for
`interpP`: the two easy halves run `E^P ⊢ E^R` and `A^R ⊢ A^P`, so `interpR`
is WEAKER in `∃p` and STRONGER in `∀p`, and cofinality transfers along
neither.  The argument has to be run again, by induction on the DERIVATION
height, and there the loop check costs nothing: a derivation that re-attacks
`Qa ⊃ N` at a station with the same members contains a derivation of the
guard sequent `done ⊢ Qa` as a PROPER sub-derivation, so the induction
hypothesis applies to it at the guard state, and the consequence re-appears
as an ESCAPE — a disjunct on the `∀p` side, a conjunct on the `∃p` side —
absorbed at the guard state, where it is the goal itself.

The escapes are exactly the rows the loop check cut:

* `∀p` (`escRowsR`): the cut row of `parkRowAR` is `⊥`; the escape is the
  `∀p` approximant of the guard sequent `done ⇒ ↑Q`, one for each recorded
  pair `(Q, T)` whose station `T` has the same members as the current one.
* `∃p` (`escConjR`): the cut conjunct of `parkRowER` is `⊤`; the escape is
  the guarded implication that conjunct would have been, one for each split
  of the station at an implication whose antecedent is recorded at this
  station — written verbatim as the row writes it, guard at
  `(Qa, done) :: seen`.

At `seen = []` no record exists, so both lists are empty and the escapes
vanish — `escRowsR_nil`, `escConjR_nil`.

**What is tested and what is not.**  The escape SHAPE is the one WP12's
Stage 0 leg R2 decided on designed cell (ix) (`docs/n4-pair-design.md` §3):
the sufficient datum `b` is not reached by `A^R` at the same-station residue,
IS reached by `A^R(r) ∨ A^R(g)`, and lands at the guard `g`.  The statements
below have NOT themselves been through a refutation stage; that is the first
task of the work package that attempts the induction (rules 7 and 9).

`LJF/` is untouched; this module is a leaf.
-/
import wip.ui_routeB_r_ui
import Meta.Audit

set_option autoImplicit false

namespace LJFO

/-! # Part 1 · The escape lists -/

/-- The `∀p` escapes at a station: for each recorded pair whose station has
the same members as the current one, the `∀p` approximant of the guard
sequent `done ⇒ ↑Q`. -/
def escRowsR (p : String) (f : Nat) (done : List Neg) (seen : SeenR) : List Neg :=
  (seen.filter (fun QT => sameSet QT.2 done)).map
    (fun QT => interpR p f [] done (some (.up QT.1)) seen)

/-- The `∃p` escapes at a station: for each split of the station at an
implication whose antecedent is recorded AT THIS STATION, the guarded
implication that `parkRowER`'s cut conjunct would have been. -/
def escConjR (p : String) (f : Nat) (done : List Neg) (seen : SeenR) : List Neg :=
  (splits done).flatMap (fun Xr =>
    match Xr with
    | (.imp Qa N, rest) =>
        if seenMemR seen Qa done then
          [Neg.imp (.down (interpR p f [] done (some (.up Qa)) ((Qa, done) :: seen)))
                   (interpR p f [N] rest none seen)]
        else []
    | _ => [])

theorem flatMap_nil_of {α β : Type} (g : α → List β) :
    ∀ (l : List α), (∀ x ∈ l, g x = []) → l.flatMap g = []
  | [], _ => rfl
  | x :: l, h => by
      rw [List.flatMap_cons, h x (List.mem_cons_self ..),
        flatMap_nil_of g l (fun y hy => h y (List.mem_cons_of_mem _ hy))]
      rfl

/-- **At the empty record there are no `∀p` escapes.** -/
theorem escRowsR_nil (p : String) (f : Nat) (done : List Neg) :
    escRowsR p f done [] = [] := rfl

/-- **At the empty record there are no `∃p` escapes.** -/
theorem escConjR_nil (p : String) (f : Nat) (done : List Neg) :
    escConjR p f done [] = [] := by
  refine flatMap_nil_of _ (splits done) ?_
  rintro ⟨X, rest⟩ _
  match X with
  | .imp Qa N => rfl
  | .up _ | .circ _ | .and _ _ => rfl

/-! # Part 2 · The escape-carrying statements (DESIGN, OPEN) -/

/-- **Cofinality with escapes, `∃p` side** (OPEN).  At every station and
every record, the `∃p` approximant computed with that record, STRENGTHENED by
the escape conjuncts the loop check cut, is cofinal for the `p`-free
consequences of the station. -/
def SatE2RE (p : String) : Type :=
  ∀ (done Δ : List Neg) (ψ : Neg) (seen : SeenR), Saturated done →
    ParkedCtxP done → PFreeCtx p Δ → PFreeN p ψ →
    ∀ {j : JD}, Inv (done ++ Δ) [] j ψ →
      UpFrom (fun e =>
        Inv (nAndAll (interpR p e [] done none seen :: escConjR p e done seen) :: Δ)
          [] j ψ)

/-- **Cofinality with escapes, `∀p` side** (OPEN), E-relativised as `SatA2P`
is.  The conclusion is WEAKENED by the escape disjuncts the loop check cut. -/
def SatA2RE (p : String) : Type :=
  ∀ (done Δ : List Neg) (G : Neg) (seen : SeenR), Saturated done →
    ParkedCtxP done → PFreeCtx p Δ →
    ∀ {j : JD}, Inv (done ++ Δ) [] j G →
      UpFrom2 (fun e f =>
        Inv (nAndAll (interpR p e [] done none seen :: escConjR p e done seen) :: Δ)
          [] .tru
          (nOrAll (interpR p f [] done (some (jGoal j G)) seen ::
                   escRowsR p f done seen)))

/-! # Part 3 · The specialisation at the empty record -/

/-- `nAndAll [X]` is entailed by `X`. -/
def nAndAll_singleton_intro (X : Neg) : Inv [X] [] .tru (nAndAll [X]) :=
  nAndAllIntro (fun y hy => by
    rcases List.mem_singleton.mp hy with rfl
    exact idNeg _ _ (List.mem_cons_self ..))

/-- `nOrAll [X]` entails `X`. -/
def nOrAll_singleton_elim (X : Neg) : Inv [nOrAll [X]] [] .tru X :=
  nOrAllElim X (List.mem_cons_self ..) (fun y hy _Γ' _s => by
    rcases List.mem_singleton.mp hy with rfl
    exact idNeg _ _ (List.mem_cons_self ..))

/-- **The `∃p` generalisation specialises to the residual.** -/
noncomputable def satE2R_of_escapes {p : String} (w : SatE2RE p) : SatE2R p :=
  fun done Δ ψ hsat hP hΔ hψ {_j} d =>
    (w done Δ ψ [] hsat hP hΔ hψ d).map (fun e dd => by
      rw [escConjR_nil] at dd
      have h := cutInv [interpR p e [] done none []] Δ _j
        (nAndAll [interpR p e [] done none []]) ψ
        (nAndAll_singleton_intro _) dd
      simpa using h)

/-- **The `∀p` generalisation specialises to the residual.** -/
noncomputable def satA2R_of_escapes {p : String} (w : SatA2RE p) : SatA2R p :=
  fun done Δ G hsat hP hΔ {_j} d =>
    (w done Δ G [] hsat hP hΔ d).map (fun e f dd => by
      rw [escConjR_nil, escRowsR_nil] at dd
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

/-- **`PLL_UI` over the escape-carrying statements alone**, with `SatE2P` /
`SatA2P` (inhabited by `satE2P` / `satA2P`, `LJF/OFuelPCofinal.lean`) kept as
variables because this leaf must not import the family. -/
noncomputable def pll_ui_R_esc (s2 : ∀ p, SatE2P p) (a2 : ∀ p, SatA2P p)
    (we : ∀ p, SatE2RE p) (wa : ∀ p, SatA2RE p) : PLL_UI :=
  pll_ui_R s2 a2 (fun p => satE2R_of_escapes (we p)) (fun p => satA2R_of_escapes (wa p))

end LJFO

/-! ## Pins -/

#axioms_within LJFO.escRowsR_nil [propext]
#axioms_within LJFO.escConjR_nil [propext, Quot.sound]
#axioms_within LJFO.nAndAll_singleton_intro [propext, Quot.sound]
#axioms_within LJFO.nOrAll_singleton_elim [propext, Quot.sound]
#axioms_within LJFO.satE2R_of_escapes [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.satA2R_of_escapes [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.pll_ui_R_esc [propext, Classical.choice, Quot.sound]
