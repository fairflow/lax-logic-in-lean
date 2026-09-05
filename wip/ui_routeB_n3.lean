/-
Route (B), node **N3** over the PARKING interpolant `interpP`: *the chains
stabilise at a cell ⟺ the cell has a uniform interpolant* (work package
WP2 of `docs/ui-routeB-blueprint.md`).

The two cofinality statements are taken as VARIABLES (`SatE2P`, `SatA2P`
of `LJF/OFuelPMin.lean`, passed as arguments), so that nothing here
depends on the family module `LJF/OFuelPFam.lean` while that is being
re-founded (WP1c).  They are PROVED unconditional elsewhere
(`LJFO.satE2P`, `LJFO.satA2P` in `LJF/OFuelPCofinal.lean`); instantiating
this file's results at them is a one-line job that belongs with that
module, not here.

Nothing in this file is a `sorry`: every case that is not proved is a
TYPED OBLIGATION, a `def … : Type` passed as an argument (the `CimpAnt`
idiom).

Contents:

* N1  `EStabEq`/`AStabEq` — the chains are LITERALLY eventually constant —
      and the interderivable forms `EStabilises`/`AStabilises`, with
      `estabilises_of_stabEq`/`astabilises_of_stabEq`.
* the fuel-irrelevance side: `interpP_pfree` (the interpolants are
  `p`-free at every fuel) and `FuelIrrelevance`, the typed obligation
  that a recursion which bottoms out below its fuel is fuel-invariant.
* N2  `IsUIPair`/`HasUI` for `interpP`.
* N3  forward: `hasUI_of_stabEq` — PROVED from the two variables.
      backward: `stabilises_of_hasUI` — PROVED relative to `CutInv`.
* N6  `IsUIPairPLL`/`PLL_UI`, the polarisation fact `pfree_roundTripN`,
      and the transport `isUIPairPLL_of_isUIPair` / `pll_ui_of_ljfo`.
-/
import LJF.OFuelP
import LJF.OFuelPSound
import LJF.OFuelPMin
import LJF.OBridge
import Meta.Audit

namespace LJFO

open PLLND

/-! # N1 · Stabilisation of the fuel chains, literal and interderivable

`E_f := interpP p f [] done none` descends from `⊤`; `A_f := interpP p f
[] done (some G)` ascends from `⊥`.  `interpP`'s fuel is a BOUND and
nothing else: every clause but the fuel-0 defaults passes `f` to the
recursive calls of `f+1`, so a station whose recursion bottoms out before
the fuel runs out gives literally the same formula at every larger fuel.
That is what "the chains stabilise" means for a fuel-bounded definition,
and it is stated first. -/

/-- **The `∃p`-chain is literally eventually constant.** -/
def EStabEq (p : String) (done : List Neg) : Type :=
  Σ' f₀ : Nat, ∀ f, f₀ ≤ f →
    interpP p f [] done none = interpP p f₀ [] done none

/-- **The `∀p`-chain is literally eventually constant.** -/
def AStabEq (p : String) (done : List Neg) (G : Neg) : Type :=
  Σ' f₀ : Nat, ∀ f, f₀ ≤ f →
    interpP p f [] done (some G) = interpP p f₀ [] done (some G)

/-- The `∃p`-chain is eventually constant up to interderivability
(`wip/ui_routeB_blueprint.lean`'s `EStabilises`, over `interpP`). -/
def EStabilises (p : String) (done : List Neg) : Type :=
  Σ f₀ : Nat, ∀ f, f₀ ≤ f →
    Inv [interpP p f₀ [] done none] [] .tru (interpP p f [] done none) ×
    Inv [interpP p f [] done none] [] .tru (interpP p f₀ [] done none)

/-- The `∀p`-chain is eventually constant modulo `E_f`
(`wip/ui_routeB_blueprint.lean`'s `AStabilises`, over `interpP`). -/
def AStabilises (p : String) (done : List Neg) (G : Neg) : Type :=
  Σ f₀ : Nat, ∀ f, f₀ ≤ f →
    Inv [interpP p f [] done none, interpP p f₀ [] done (some G)] [] .tru
      (interpP p f [] done (some G)) ×
    Inv [interpP p f [] done none, interpP p f [] done (some G)] [] .tru
      (interpP p f₀ [] done (some G))

/-- Literal stabilisation implies interderivable stabilisation: after the
rewrite both sequents are an identity `X ⊢ X`, discharged by `idNeg`.  No
composition of derivations is involved — this is the reason the literal
form is stated first. -/
def estabilises_of_stabEq {p : String} {done : List Neg}
    (h : EStabEq p done) : EStabilises p done :=
  ⟨h.1, fun f hf => by
    rw [h.2 f hf]
    exact ⟨idNeg _ _ (List.mem_cons_self ..), idNeg _ _ (List.mem_cons_self ..)⟩⟩

/-- Literal stabilisation of the `∀p`-chain implies its interderivable,
`E`-relativised form.  The `∃p` hypothesis is carried but unused: after
the rewrite the goal is the identity on `A_{f₀}`, which the second
hypothesis supplies. -/
def astabilises_of_stabEq {p : String} {done : List Neg} {G : Neg}
    (h : AStabEq p done G) : AStabilises p done G :=
  ⟨h.1, fun f hf => by
    rw [h.2 f hf]
    exact ⟨idNeg _ _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)),
           idNeg _ _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))⟩⟩

/-! # The interpolants are `p`-free at every fuel

`LJF/OCore.lean`'s `interp_pfree` is the same fact for the weight-founded
`interp`; neither `LJF/OFuelSound.lean` nor `LJF/OFuelPMin.lean` states it
for a fuel-carrying interpolant, so it is proved here.  Farm style, as
`interp_pfree`: no positional case names, every case falls through the
alternatives until one matches, so the proof survives clause insertion and
reordering — which matters, `interpP` having three parked shapes and their
rows more than `interp`. -/

set_option maxHeartbeats 4000000 in
/-- **The interpolant never mentions `p`, at any fuel.**  `LJF/OCore.lean`'s
`interp_pfree` for the weight-founded `interp`, re-proved for `interpP`:
every clause either keeps `p` out by construction, or is guarded by the
`a == p` test that replaces the would-be conjunct or disjunct by its unit.

The processing clauses, the fire step, the fuel-0 defaults and the inert
hypotheses fall to the three-way `first`; the sixteen aggregate clauses are
taken one by one in `fun_induction`'s own case numbering, since the
alternatives of a farm-style `first` are not cheap to refute on an
aggregate goal (unifying `nOrAll ?l` with an `nAndAll` over
`(splits done).attach` sends `whnf` past its budget). -/
theorem interpP_pfree (p : String) :
    ∀ (f : Nat) (todo done : List Neg) (g : Option Neg),
      PFreeN p (interpP p f todo done g) := by
  intro f todo done g
  fun_induction interpP p f todo done g
  all_goals try (first | exact pfree_nTop | exact pfree_nBot | assumption)
  -- ∃p at a disjunctive hypothesis: the disjunction of the branch results
  case case6 =>
    rename_i ihB
    apply pfree_nOrAll
    intro x hx
    simp only [List.mem_map, List.mem_attach, true_and] at hx
    obtain ⟨⟨b, hb⟩, rfl⟩ := hx
    exact ihB b
  -- ∀p at a disjunctive hypothesis: each branch conjunct guarded by the
  -- branch's ∃p
  case case7 =>
    rename_i ihE ihA
    apply pfree_nAndAll
    intro x hx
    simp only [List.mem_map, List.mem_attach, true_and] at hx
    obtain ⟨⟨b, hb⟩, rfl⟩ := hx
    exact ⟨ihE b, ihA b⟩
  -- the ∃p aggregate at a saturated station: the eight parked shapes
  case case19 =>
    rename_i ihFire ihDykG ihDykRes ihBox ihCimpG ihRes ihOrG ihStripG ihAndG
    apply pfree_nAndAll
    intro x hx
    simp only [List.mem_map, List.mem_attach, true_and] at hx
    obtain ⟨⟨⟨X, rest⟩, hXr⟩, rfl⟩ := hx
    cases X with
    | up P =>
        cases P with
        | atom a =>
            exact pfree_pGuard pfree_nTop
              (fun h => by simpa only [PFreeN, PFreeP] using h)
        | fls => exact pfree_nTop
        | or _ _ => exact pfree_nTop
        | down _ => exact pfree_nTop
    | imp Q N =>
        cases Q with
        | atom a => exact pfree_pGuard pfree_nTop (fun h => ⟨h, ihFire rest N⟩)
        | fls => exact pfree_nTop
        | or Qa Qb => exact ⟨⟨ihOrG Qa Qb, ihFire rest N⟩, ihRes rest⟩
        | down M =>
            cases M with
            | up Pa => exact ⟨⟨ihStripG Pa, ihFire rest N⟩, ihRes rest⟩
            | and Ma Mb => exact ⟨⟨ihAndG Ma Mb, ihFire rest N⟩, ihRes rest⟩
            | imp Q' N' => exact ⟨⟨ihDykG Q' N', ihFire rest N⟩, ihDykRes rest N' N⟩
            | circ Q' => exact ⟨⟨ihCimpG Q', ihFire rest N⟩, ihRes rest⟩
    | and _ _ => exact pfree_nTop
    | circ Q => exact ihBox rest Q
  -- ∀p at an implication goal: each branch conjunct guarded by the branch's ∃p
  case case20 =>
    rename_i ihE ihA
    apply pfree_nAndAll
    intro x hx
    simp only [List.mem_map, List.mem_attach, true_and] at hx
    obtain ⟨⟨b, hb⟩, rfl⟩ := hx
    exact ⟨ihE b, ihA b⟩
  -- ∀p at a conjunctive goal
  case case21 => exact ⟨by assumption, by assumption⟩
  -- ∀p at an atomic goal not in the station: the atom head and the rows
  case case23 =>
    rename_i ihFire ihDyk ihCimp ihOr ihStrip ihAnd
    apply pfree_nOrAll
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact pfree_atomHead x hx
    · simp only [List.mem_map, List.mem_attach, true_and] at hx
      obtain ⟨⟨⟨X, rest⟩, hXr⟩, rfl⟩ := hx
      cases X with
      | up P => cases P <;> exact pfree_nBot
      | imp Q N =>
          cases Q with
          | atom a => exact pfree_pGuard pfree_nBot (fun h => ⟨h, ihFire rest N⟩)
          | fls => exact pfree_nBot
          | or Qa Qb => exact ⟨ihOr Qa Qb, ihFire rest N⟩
          | down M =>
              cases M with
              | up Pa => exact ⟨ihStrip Pa, ihFire rest N⟩
              | and Ma Mb => exact ⟨ihAnd Ma Mb, ihFire rest N⟩
              | imp Q' N' => exact ⟨ihDyk Q' N', ihFire rest N⟩
              | circ Q' => exact ⟨ihCimp Q', ihFire rest N⟩
      | and _ _ => exact pfree_nBot
      | circ _ => exact pfree_nBot
  -- ∀p at `↑⊥`: the rows alone
  case case24 =>
    rename_i ihFire ihDyk ihCimp ihOr ihStrip ihAnd
    apply pfree_nOrAll
    intro x hx
    simp only [List.mem_map, List.mem_attach, true_and] at hx
    obtain ⟨⟨⟨X, rest⟩, hXr⟩, rfl⟩ := hx
    cases X with
    | up P => cases P <;> exact pfree_nBot
    | imp Q N =>
        cases Q with
        | atom a => exact pfree_pGuard pfree_nBot (fun h => ⟨h, ihFire rest N⟩)
        | fls => exact pfree_nBot
        | or Qa Qb => exact ⟨ihOr Qa Qb, ihFire rest N⟩
        | down M =>
            cases M with
            | up Pa => exact ⟨ihStrip Pa, ihFire rest N⟩
            | and Ma Mb => exact ⟨ihAnd Ma Mb, ihFire rest N⟩
            | imp Q' N' => exact ⟨ihDyk Q' N', ihFire rest N⟩
            | circ Q' => exact ⟨ihCimp Q', ihFire rest N⟩
    | and _ _ => exact pfree_nBot
    | circ _ => exact pfree_nBot
  -- ∀p at `↑(P₁∨P₂)` and at `↑↓M`: the goal-inversion heads and the rows
  case case25 =>
    rename_i ihFire ihDyk ihCimp ihOr ihStrip ihAnd
    apply pfree_nOrAll
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · repeat' (rcases List.mem_cons.mp hx with rfl | hx)
      all_goals first
        | assumption
        | exact absurd hx List.not_mem_nil
    · simp only [List.mem_map, List.mem_attach, true_and] at hx
      obtain ⟨⟨⟨X, rest⟩, hXr⟩, rfl⟩ := hx
      cases X with
      | up P => cases P <;> exact pfree_nBot
      | imp Q N =>
          cases Q with
          | atom a => exact pfree_pGuard pfree_nBot (fun h => ⟨h, ihFire rest N⟩)
          | fls => exact pfree_nBot
          | or Qa Qb => exact ⟨ihOr Qa Qb, ihFire rest N⟩
          | down M =>
              cases M with
              | up Pa => exact ⟨ihStrip Pa, ihFire rest N⟩
              | and Ma Mb => exact ⟨ihAnd Ma Mb, ihFire rest N⟩
              | imp Q' N' => exact ⟨ihDyk Q' N', ihFire rest N⟩
              | circ Q' => exact ⟨ihCimp Q', ihFire rest N⟩
      | and _ _ => exact pfree_nBot
      | circ _ => exact pfree_nBot
  case case26 =>
    rename_i ihFire ihDyk ihCimp ihOr ihStrip ihAnd
    apply pfree_nOrAll
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · repeat' (rcases List.mem_cons.mp hx with rfl | hx)
      all_goals first
        | assumption
        | exact absurd hx List.not_mem_nil
    · simp only [List.mem_map, List.mem_attach, true_and] at hx
      obtain ⟨⟨⟨X, rest⟩, hXr⟩, rfl⟩ := hx
      cases X with
      | up P => cases P <;> exact pfree_nBot
      | imp Q N =>
          cases Q with
          | atom a => exact pfree_pGuard pfree_nBot (fun h => ⟨h, ihFire rest N⟩)
          | fls => exact pfree_nBot
          | or Qa Qb => exact ⟨ihOr Qa Qb, ihFire rest N⟩
          | down M =>
              cases M with
              | up Pa => exact ⟨ihStrip Pa, ihFire rest N⟩
              | and Ma Mb => exact ⟨ihAnd Ma Mb, ihFire rest N⟩
              | imp Q' N' => exact ⟨ihDyk Q' N', ihFire rest N⟩
              | circ Q' => exact ⟨ihCimp Q', ihFire rest N⟩
      | and _ _ => exact pfree_nBot
      | circ _ => exact pfree_nBot
  -- the seven `◯`-goals: heads, the six implication rows, and the box row, all under `◯↓`
  case case27 =>
    rename_i ihFire ihDyk ihCimp ihOr ihStrip ihAnd ihBoxE ihBoxA
    apply pfree_nOrAll
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · repeat' (rcases List.mem_cons.mp hx with rfl | hx)
      all_goals first
        | assumption
        | exact absurd hx List.not_mem_nil
    · simp only [List.mem_map, List.mem_attach, true_and] at hx
      obtain ⟨⟨⟨X, rest⟩, hXr⟩, rfl⟩ := hx
      cases X with
      | up P => cases P <;> exact pfree_nBot
      | imp Q N =>
          cases Q with
          | atom a => exact pfree_pGuard pfree_nBot (fun h => ⟨h, ihFire rest N⟩)
          | fls => exact pfree_nBot
          | or Qa Qb => exact ⟨ihOr Qa Qb, ihFire rest N⟩
          | down M =>
              cases M with
              | up Pa => exact ⟨ihStrip Pa, ihFire rest N⟩
              | and Ma Mb => exact ⟨ihAnd Ma Mb, ihFire rest N⟩
              | imp Q' N' => exact ⟨ihDyk Q' N', ihFire rest N⟩
              | circ Q' => exact ⟨ihCimp Q', ihFire rest N⟩
      | and _ _ => exact pfree_nBot
      | circ R => exact ⟨ihBoxE rest R, ihBoxA rest R⟩
  case case28 =>
    rename_i ihFire ihDyk ihCimp ihOr ihStrip ihAnd ihBoxE ihBoxA
    apply pfree_nOrAll
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · repeat' (rcases List.mem_cons.mp hx with rfl | hx)
      all_goals first
        | assumption
        | exact absurd hx List.not_mem_nil
    · simp only [List.mem_map, List.mem_attach, true_and] at hx
      obtain ⟨⟨⟨X, rest⟩, hXr⟩, rfl⟩ := hx
      cases X with
      | up P => cases P <;> exact pfree_nBot
      | imp Q N =>
          cases Q with
          | atom a => exact pfree_pGuard pfree_nBot (fun h => ⟨h, ihFire rest N⟩)
          | fls => exact pfree_nBot
          | or Qa Qb => exact ⟨ihOr Qa Qb, ihFire rest N⟩
          | down M =>
              cases M with
              | up Pa => exact ⟨ihStrip Pa, ihFire rest N⟩
              | and Ma Mb => exact ⟨ihAnd Ma Mb, ihFire rest N⟩
              | imp Q' N' => exact ⟨ihDyk Q' N', ihFire rest N⟩
              | circ Q' => exact ⟨ihCimp Q', ihFire rest N⟩
      | and _ _ => exact pfree_nBot
      | circ R => exact ⟨ihBoxE rest R, ihBoxA rest R⟩
  case case29 =>
    rename_i ihFire ihDyk ihCimp ihOr ihStrip ihAnd ihBoxE ihBoxA
    apply pfree_nOrAll
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · repeat' (rcases List.mem_cons.mp hx with rfl | hx)
      all_goals first
        | assumption
        | exact absurd hx List.not_mem_nil
    · simp only [List.mem_map, List.mem_attach, true_and] at hx
      obtain ⟨⟨⟨X, rest⟩, hXr⟩, rfl⟩ := hx
      cases X with
      | up P => cases P <;> exact pfree_nBot
      | imp Q N =>
          cases Q with
          | atom a => exact pfree_pGuard pfree_nBot (fun h => ⟨h, ihFire rest N⟩)
          | fls => exact pfree_nBot
          | or Qa Qb => exact ⟨ihOr Qa Qb, ihFire rest N⟩
          | down M =>
              cases M with
              | up Pa => exact ⟨ihStrip Pa, ihFire rest N⟩
              | and Ma Mb => exact ⟨ihAnd Ma Mb, ihFire rest N⟩
              | imp Q' N' => exact ⟨ihDyk Q' N', ihFire rest N⟩
              | circ Q' => exact ⟨ihCimp Q', ihFire rest N⟩
      | and _ _ => exact pfree_nBot
      | circ R => exact ⟨ihBoxE rest R, ihBoxA rest R⟩
  case case30 =>
    rename_i ihFire ihDyk ihCimp ihOr ihStrip ihAnd ihBoxE ihBoxA
    apply pfree_nOrAll
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · repeat' (rcases List.mem_cons.mp hx with rfl | hx)
      all_goals first
        | assumption
        | exact absurd hx List.not_mem_nil
    · simp only [List.mem_map, List.mem_attach, true_and] at hx
      obtain ⟨⟨⟨X, rest⟩, hXr⟩, rfl⟩ := hx
      cases X with
      | up P => cases P <;> exact pfree_nBot
      | imp Q N =>
          cases Q with
          | atom a => exact pfree_pGuard pfree_nBot (fun h => ⟨h, ihFire rest N⟩)
          | fls => exact pfree_nBot
          | or Qa Qb => exact ⟨ihOr Qa Qb, ihFire rest N⟩
          | down M =>
              cases M with
              | up Pa => exact ⟨ihStrip Pa, ihFire rest N⟩
              | and Ma Mb => exact ⟨ihAnd Ma Mb, ihFire rest N⟩
              | imp Q' N' => exact ⟨ihDyk Q' N', ihFire rest N⟩
              | circ Q' => exact ⟨ihCimp Q', ihFire rest N⟩
      | and _ _ => exact pfree_nBot
      | circ R => exact ⟨ihBoxE rest R, ihBoxA rest R⟩
  case case31 =>
    rename_i ihFire ihDyk ihCimp ihOr ihStrip ihAnd ihBoxE ihBoxA
    apply pfree_nOrAll
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · repeat' (rcases List.mem_cons.mp hx with rfl | hx)
      all_goals first
        | assumption
        | exact absurd hx List.not_mem_nil
    · simp only [List.mem_map, List.mem_attach, true_and] at hx
      obtain ⟨⟨⟨X, rest⟩, hXr⟩, rfl⟩ := hx
      cases X with
      | up P => cases P <;> exact pfree_nBot
      | imp Q N =>
          cases Q with
          | atom a => exact pfree_pGuard pfree_nBot (fun h => ⟨h, ihFire rest N⟩)
          | fls => exact pfree_nBot
          | or Qa Qb => exact ⟨ihOr Qa Qb, ihFire rest N⟩
          | down M =>
              cases M with
              | up Pa => exact ⟨ihStrip Pa, ihFire rest N⟩
              | and Ma Mb => exact ⟨ihAnd Ma Mb, ihFire rest N⟩
              | imp Q' N' => exact ⟨ihDyk Q' N', ihFire rest N⟩
              | circ Q' => exact ⟨ihCimp Q', ihFire rest N⟩
      | and _ _ => exact pfree_nBot
      | circ R => exact ⟨ihBoxE rest R, ihBoxA rest R⟩
  case case32 =>
    rename_i ihFire ihDyk ihCimp ihOr ihStrip ihAnd ihBoxE ihBoxA
    apply pfree_nOrAll
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · repeat' (rcases List.mem_cons.mp hx with rfl | hx)
      all_goals first
        | assumption
        | exact absurd hx List.not_mem_nil
    · simp only [List.mem_map, List.mem_attach, true_and] at hx
      obtain ⟨⟨⟨X, rest⟩, hXr⟩, rfl⟩ := hx
      cases X with
      | up P => cases P <;> exact pfree_nBot
      | imp Q N =>
          cases Q with
          | atom a => exact pfree_pGuard pfree_nBot (fun h => ⟨h, ihFire rest N⟩)
          | fls => exact pfree_nBot
          | or Qa Qb => exact ⟨ihOr Qa Qb, ihFire rest N⟩
          | down M =>
              cases M with
              | up Pa => exact ⟨ihStrip Pa, ihFire rest N⟩
              | and Ma Mb => exact ⟨ihAnd Ma Mb, ihFire rest N⟩
              | imp Q' N' => exact ⟨ihDyk Q' N', ihFire rest N⟩
              | circ Q' => exact ⟨ihCimp Q', ihFire rest N⟩
      | and _ _ => exact pfree_nBot
      | circ R => exact ⟨ihBoxE rest R, ihBoxA rest R⟩
  case case33 =>
    rename_i ihFire ihDyk ihCimp ihOr ihStrip ihAnd ihBoxE ihBoxA
    apply pfree_nOrAll
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · repeat' (rcases List.mem_cons.mp hx with rfl | hx)
      all_goals first
        | assumption
        | exact absurd hx List.not_mem_nil
    · simp only [List.mem_map, List.mem_attach, true_and] at hx
      obtain ⟨⟨⟨X, rest⟩, hXr⟩, rfl⟩ := hx
      cases X with
      | up P => cases P <;> exact pfree_nBot
      | imp Q N =>
          cases Q with
          | atom a => exact pfree_pGuard pfree_nBot (fun h => ⟨h, ihFire rest N⟩)
          | fls => exact pfree_nBot
          | or Qa Qb => exact ⟨ihOr Qa Qb, ihFire rest N⟩
          | down M =>
              cases M with
              | up Pa => exact ⟨ihStrip Pa, ihFire rest N⟩
              | and Ma Mb => exact ⟨ihAnd Ma Mb, ihFire rest N⟩
              | imp Q' N' => exact ⟨ihDyk Q' N', ihFire rest N⟩
              | circ Q' => exact ⟨ihCimp Q', ihFire rest N⟩
      | and _ _ => exact pfree_nBot
      | circ R => exact ⟨ihBoxE rest R, ihBoxA rest R⟩

/-! # Fuel irrelevance, as a typed obligation

The literal form `EStabEq`/`AStabEq` is natural because `interpP`'s fuel is
a bound and nothing else: below the fuel-0 clauses every clause passes `f`
to the recursive calls of `f+1`.  So a station at which one step of the
chain is already constant should have a constant chain from there on.
That statement is NOT proved here — proving it needs a `Defined` predicate
mirroring all thirty clauses of `interpP`, which is a definition the size
of `interpP` itself and an induction to match; it is stated as a typed
obligation and passed as an argument where it is wanted.  **Nothing in N3
below uses it**: `EStabEq`/`AStabEq` are hypotheses of N3, not conclusions.
It is what N4 would consume. -/

/-- One step of the chain is constant at `(todo, done, g)`. -/
def FuelStep (p : String) (todo done : List Neg) (g : Option Neg) (f : Nat) : Prop :=
  interpP p (f + 1) todo done g = interpP p f todo done g

/-- **Fuel irrelevance** (OBLIGATION, not proved here): one constant step
propagates upward.  Equivalently, the recursion that bottoms out below its
fuel gives the same formula at every larger fuel. -/
def FuelIrrelevance (p : String) : Prop :=
  ∀ (f : Nat) (todo done : List Neg) (g : Option Neg), FuelStep p todo done g f →
    ∀ f', f ≤ f' → interpP p f' todo done g = interpP p f todo done g

/-- What fuel irrelevance buys: ONE equality check at a station is literal
stabilisation of its `∃p`-chain. -/
def eStabEq_of_fuelStep {p : String} {done : List Neg} {f : Nat}
    (fi : FuelIrrelevance p) (h : FuelStep p [] done none f) : EStabEq p done :=
  ⟨f, fun f' hf' => fi f [] done none h f' hf'⟩

/-- The same for the `∀p`-chain. -/
def aStabEq_of_fuelStep {p : String} {done : List Neg} {G : Neg} {f : Nat}
    (fi : FuelIrrelevance p) (h : FuelStep p [] done (some G) f) : AStabEq p done G :=
  ⟨f, fun f' hf' => fi f [] done (some G) h f' hf'⟩

/-! # N2 · The uniform-interpolant pair of a cell, intrinsic

Pitts's pair for the sequent `done ⇒ G` and the variable `p`: `E` is the
strongest `p`-free consequence of the station, `A` the weakest `p`-free
formula sufficient for the goal, its minimality RELATIVE to `E` (exactly as
`SatA2P` is stated).  Nothing here mentions a chain.

Two adjustments to the drafted statement of `wip/ui_routeB_blueprint.lean`,
both forced by what the inputs deliver:

* `minE` is stated for EVERY judgment `j`, not just `.tru`.  `SatE2P` is
  stated with `∀ {j : JD}`, so the general form is free, and it is strictly
  stronger.
* `minA` stays at `.tru`.  `SatA2P` sends a derivation at judgment `j` to
  the `∀p` approximant of `jGoal j G` — a DIFFERENT goal when `j = .lax`
  and `G = ↑P` (namely `◯P`).  A pair for the cell `done ⇒ G` can therefore
  only be read off the `.tru` instance, where `jGoal .tru G = G`; the lax
  cell is the cell `done ⇒ ◯P`, which this same statement covers. -/

/-- `(E, A)` is a uniform-interpolant pair for the cell `done ⇒ G`. -/
structure IsUIPair (p : String) (done : List Neg) (G : Neg) (E A : Neg) : Type where
  pfreeE : PFreeN p E
  pfreeA : PFreeN p A
  /-- `Γ ⊢ E` -/
  soundE : Inv done [] .tru E
  /-- `Δ, Γ ⊢ⱼ ψ  →  Δ, E ⊢ⱼ ψ` for `p`-free `Δ`, `ψ`, at every judgment -/
  minE : ∀ (Δ : List Neg) (ψ : Neg), PFreeCtx p Δ → PFreeN p ψ →
    ∀ {j : JD}, Inv (done ++ Δ) [] j ψ → Inv (E :: Δ) [] j ψ
  /-- `A, Γ ⊢ G` -/
  soundA : Inv (A :: done) [] .tru G
  /-- `Δ, Γ ⊢ G  →  Δ, E ⊢ A` for `p`-free `Δ` -/
  minA : ∀ (Δ : List Neg), PFreeCtx p Δ →
    Inv (done ++ Δ) [] .tru G → Inv (E :: Δ) [] .tru A

/-- The cell has a uniform-interpolant pair. -/
def HasUI (p : String) (done : List Neg) (G : Neg) : Type :=
  Σ (E A : Neg), IsUIPair p done G E A

/-! ### Two `p`-freeness facts used below -/

theorem pfreeCtx_nil {p : String} : PFreeCtx p ([] : List Neg) :=
  fun _ h => absurd h List.not_mem_nil

theorem pfreeCtx_singleton {p : String} {N : Neg} (h : PFreeN p N) :
    PFreeCtx p [N] := by
  intro Z hZ
  rcases List.mem_singleton.mp hZ with rfl
  exact h

/-! # N3 forward · stabilisation gives a uniform-interpolant pair

The point of the LITERAL form: no composition of derivations is needed.
Soundness is `eSoundP`/`aSoundP` read at the stabilisation fuel.  For
minimality, the cofinality variable delivers the fact at every fuel above a
threshold; take the fuel above both the threshold and the stabilisation
fuel and REWRITE with the stabilisation equation — the derivation the
variable supplies is then literally at `E_{f₀}`, `A_{f₀'}`. -/

/-- **N3, forward.**  If both chains are literally eventually constant at a
saturated parked station, their stabilised values are a uniform-interpolant
pair for the cell. -/
def hasUI_of_stabEq {p : String} {done : List Neg} {G : Neg}
    (s2 : SatE2P p) (a2 : SatA2P p)
    (hsat : Saturated done) (hP : ParkedCtxP done)
    (he : EStabEq p done) (ha : AStabEq p done G) : HasUI p done G := by
  obtain ⟨f₀, hE⟩ := he
  obtain ⟨f₁, hA⟩ := ha
  refine ⟨interpP p f₀ [] done none, interpP p f₁ [] done (some G),
    { pfreeE := interpP_pfree p _ _ _ _
      pfreeA := interpP_pfree p _ _ _ _
      soundE := eSoundP p f₀ [] done
      soundA := aSoundP p f₁ [] done G
      minE := ?_
      minA := ?_ }⟩
  · -- minimality of `E_{f₀}`: cofinality above `max (threshold, f₀)`, then the
    -- stabilisation equation carries the derivation down to `f₀` itself
    intro Δ ψ hΔ hψ j d
    obtain ⟨n, hw⟩ := s2 done Δ ψ hsat hP hΔ hψ d
    have hd : Inv (interpP p (n + f₀) [] done none :: Δ) [] j ψ :=
      hw (n + f₀) (Nat.le_add_right _ _)
    rw [hE (n + f₀) (Nat.le_add_left _ _)] at hd
    exact hd
  · -- minimality of `A_{f₁}`, `E`-relativised; `jGoal .tru G = G`
    intro Δ hΔ d
    obtain ⟨n, hw⟩ := a2 done Δ G hsat hP hΔ d
    have hd : Inv (interpP p (n + f₀ + f₁) [] done none :: Δ) [] .tru
        (interpP p (n + f₀ + f₁) [] done (some (jGoal .tru G))) :=
      hw (n + f₀ + f₁) (n + f₀ + f₁) (by omega) (by omega)
    rw [jGoal_tru] at hd
    rw [hE (n + f₀ + f₁) (by omega), hA (n + f₀ + f₁) (by omega)] at hd
    exact hd

/-! # N3 backward · a uniform-interpolant pair makes the chains stabilise

Here the LITERAL form is false in general — nothing makes the syntactic
formula `E_f` equal to `E_{f₀}` once a pair exists — so the conclusion is
the interderivable form, and the proof must COMPOSE derivations:
`E_f ⊢ E` from cofinality at `ψ := E`, `E ⊢ E_{f₀}` from the pair's
minimality applied to the soundness of `E_{f₀}`, hence `E_f ⊢ E_{f₀}`.
LJF◯ has no cut lemma (`docs/calculus-map.md`), and the bridge's
completeness `FocalizationPLL` is stated only for `negOfO`-polarised
contexts, so the composition is stated as a typed obligation and the
backward direction is proved RELATIVE to it.  Contraction and permutation
are not part of the obligation: `Sub` is membership-inclusion, so `Inv.wk`
supplies both. -/

/-- **The composition principle** (OBLIGATION).  Cut at a negative
formula, in the inversion phase with an empty pending zone.  The backward
direction below instantiates it only at `j = .tru`; it is stated at every
`j` because that is the form a cut-admissibility proof for LJF◯ would
deliver. -/
def CutInv : Type :=
  ∀ (Γ Δ : List Neg) (j : JD) (N ψ : Neg),
    Inv Γ [] .tru N → Inv (N :: Δ) [] j ψ → Inv (Γ ++ Δ) [] j ψ

/-- **N3, backward.**  From a uniform-interpolant pair, both chains
stabilise up to interderivability — relative to `CutInv`. -/
def stabilises_of_hasUI {p : String} {done : List Neg} {G : Neg}
    (cut : CutInv) (s2 : SatE2P p) (a2 : SatA2P p)
    (hsat : Saturated done) (hP : ParkedCtxP done)
    (h : HasUI p done G) : EStabilises p done × AStabilises p done G := by
  obtain ⟨E, A, u⟩ := h
  -- cofinality of the ∃p-chain at `ψ := E`: `E_e ⊢ E` from the fuel `n` on
  have hEdone : Inv (done ++ []) [] .tru E :=
    u.soundE.wk (fun Z hZ => List.mem_append.mpr (Or.inl hZ))
  obtain ⟨n, hv⟩ := s2 done [] E hsat hP pfreeCtx_nil u.pfreeE hEdone
  -- cofinality of the ∀p-chain at `Δ := [A]`: `E_e, A ⊢ A_f` from the fuel `m` on
  have hAdone : Inv (done ++ [A]) [] .tru G :=
    u.soundA.wk (fun Z hZ => by
      rcases List.mem_cons.mp hZ with rfl | hZ
      · exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
      · exact List.mem_append.mpr (Or.inl hZ))
  obtain ⟨m, hw⟩ := a2 done [A] G hsat hP (pfreeCtx_singleton u.pfreeA) hAdone
  -- `E ⊢ E_k` at every fuel `k`, from minimality applied to `eSoundP`
  have hEmin : ∀ k : Nat, Inv (E :: []) [] .tru (interpP p k [] done none) :=
    fun k => u.minE [] _ pfreeCtx_nil (interpP_pfree p _ _ _ _)
      ((eSoundP p k [] done).wk (fun Z hZ => List.mem_append.mpr (Or.inl hZ)))
  -- `E, A_k ⊢ A` at every fuel `k`, from minimality applied to `aSoundP`
  have hAmin : ∀ k : Nat, Inv (E :: [interpP p k [] done (some G)]) [] .tru A :=
    fun k => u.minA _ (pfreeCtx_singleton (interpP_pfree p _ _ _ _))
      ((aSoundP p k [] done G).wk (fun Z hZ => by
        rcases List.mem_cons.mp hZ with rfl | hZ
        · exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
        · exact List.mem_append.mpr (Or.inl hZ)))
  refine ⟨⟨n + m, fun f hf => ⟨?_, ?_⟩⟩, ⟨n + m, fun f hf => ⟨?_, ?_⟩⟩⟩
  · -- `E_{f₀} ⊢ E_f`, by cut at `E`
    have h1 : Inv (interpP p (n + m) [] done none :: []) [] .tru E :=
      hv (n + m) (by omega)
    exact cut _ _ _ _ _ h1 (hEmin f)
  · -- `E_f ⊢ E_{f₀}`, by cut at `E`
    have h1 : Inv (interpP p f [] done none :: []) [] .tru E := hv f (by omega)
    exact cut _ _ _ _ _ h1 (hEmin (n + m))
  · -- `E_f, A_{f₀} ⊢ A_f`: cut `E` into minimality, then cut `A` into cofinality
    have hEf : Inv (interpP p f [] done none :: []) [] .tru E := hv f (by omega)
    have hA : Inv ([interpP p f [] done none] ++
        [interpP p (n + m) [] done (some G)]) [] .tru A :=
      cut _ _ _ _ _ hEf (hAmin (n + m))
    have hcof : Inv (interpP p f [] done none :: [A]) [] .tru
        (interpP p f [] done (some (jGoal .tru G))) :=
      hw f f (by omega) (by omega)
    rw [jGoal_tru] at hcof
    have hcof' : Inv (A :: [interpP p f [] done none]) [] .tru
        (interpP p f [] done (some G)) :=
      hcof.wk (fun Z hZ => by
        rcases List.mem_cons.mp hZ with rfl | hZ
        · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
        · rcases List.mem_cons.mp hZ with rfl | hZ
          · exact List.mem_cons_self ..
          · exact absurd hZ List.not_mem_nil)
    exact (cut _ _ _ _ _ hA hcof').wk (fun Z hZ => by
      rcases List.mem_append.mp hZ with hZ | hZ
      · exact hZ
      · rcases List.mem_cons.mp hZ with rfl | hZ
        · exact List.mem_cons_self ..
        · exact absurd hZ List.not_mem_nil)
  · -- `E_f, A_f ⊢ A_{f₀}`: the same, with the ∃p fuel `f` and the ∀p fuel `f₀`
    have hEf : Inv (interpP p f [] done none :: []) [] .tru E := hv f (by omega)
    have hA : Inv ([interpP p f [] done none] ++ [interpP p f [] done (some G)])
        [] .tru A := cut _ _ _ _ _ hEf (hAmin f)
    have hcof : Inv (interpP p f [] done none :: [A]) [] .tru
        (interpP p (n + m) [] done (some (jGoal .tru G))) :=
      hw f (n + m) (by omega) (by omega)
    rw [jGoal_tru] at hcof
    have hcof' : Inv (A :: [interpP p f [] done none]) [] .tru
        (interpP p (n + m) [] done (some G)) :=
      hcof.wk (fun Z hZ => by
        rcases List.mem_cons.mp hZ with rfl | hZ
        · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
        · rcases List.mem_cons.mp hZ with rfl | hZ
          · exact List.mem_cons_self ..
          · exact absurd hZ List.not_mem_nil)
    exact (cut _ _ _ _ _ hA hcof').wk (fun Z hZ => by
      rcases List.mem_append.mp hZ with hZ | hZ
      · exact hZ
      · rcases List.mem_cons.mp hZ with rfl | hZ
        · exact List.mem_cons_self ..
        · exact absurd hZ List.not_mem_nil)

/-! # N6 · Transport to PLL through the focalization bridge

`bridge_iff` (`LJF/OBridge.lean`) is a biconditional at every context, so
both directions of a uniform-interpolant pair cross it.  Two cells are
involved and they are different: the `∃p` side lives at the station
`[negOfO φ]`, the `∀p` side at the cell `[] ⇒ negOfO φ` with the candidate
hypothesis supplied as `Δ`.

The one polarisation fact the transport needs turns out to be PROVABLE
rather than an obligation: `p`-freeness survives the round trip
`negOfO ∘ eraseNeg`, which is not the identity on `Neg` but does preserve
the atoms. -/

/-- `p`-freeness of a PLL formula, read through the polarisation. -/
def PFreeF (p : String) (φ : PLLFormula) : Prop := PFreeN p (negOfO φ)

/-- The two polarisations of a PLL formula have the same atoms, so
`p`-freeness passes between them. -/
theorem pfree_posOfO_of_negOfO {p : String} :
    ∀ (χ : PLLFormula), PFreeN p (negOfO χ) → PFreeP p (posOfO χ)
  | .prop _, h => h
  | .falsePLL, h => h
  | .or _ _, h => h
  | .and _ _, h => h
  | .ifThen _ _, h => h
  | .somehow _, h => h

mutual

/-- **`p`-freeness survives the round trip** (negatives).  `eraseNeg`
followed by `negOfO` is not the identity on `Neg` — polarity is
reconstructed, not remembered — but it preserves the atoms. -/
theorem pfree_roundTripN {p : String} :
    ∀ {N : Neg}, PFreeN p N → PFreeN p (negOfO (eraseNeg N))
  | .up _, h => pfree_roundTripP h
  | .imp _ _, h =>
      ⟨pfree_posOfO_of_negOfO _ (pfree_roundTripP h.1), pfree_roundTripN h.2⟩
  | .and _ _, h => ⟨pfree_roundTripN h.1, pfree_roundTripN h.2⟩
  | .circ _, h => pfree_posOfO_of_negOfO _ (pfree_roundTripP h)

/-- The same for positives. -/
theorem pfree_roundTripP {p : String} :
    ∀ {P : Pos}, PFreeP p P → PFreeN p (negOfO (erasePos P))
  | .atom _, h => h
  | .fls, _ => trivial
  | .or _ _, h =>
      ⟨pfree_posOfO_of_negOfO _ (pfree_roundTripP h.1),
       pfree_posOfO_of_negOfO _ (pfree_roundTripP h.2)⟩
  | .down _, h => pfree_roundTripN h

end

/-- Pitts's pair for a PLL formula and a variable, in `LaxND`. -/
structure IsUIPairPLL (p : String) (φ : PLLFormula) (E A : PLLFormula) : Type where
  pfreeE : PFreeF p E
  pfreeA : PFreeF p A
  soundE : Nonempty (LaxND [φ] E)
  minE : ∀ ψ, PFreeF p ψ → Nonempty (LaxND [φ] ψ) → Nonempty (LaxND [E] ψ)
  soundA : Nonempty (LaxND [A] φ)
  minA : ∀ ψ, PFreeF p ψ → Nonempty (LaxND [ψ] φ) → Nonempty (LaxND [ψ] A)

/-- **Uniform interpolation for PLL.** -/
def PLL_UI : Type :=
  ∀ (p : String) (φ : PLLFormula), Σ (E A : PLLFormula), IsUIPairPLL p φ E A

/-- **The transport.**  A uniform-interpolant pair at the station
`[negOfO φ]` supplies `∃p.φ`, one at the cell `[] ⇒ negOfO φ` supplies
`∀p.φ`, and erasure carries both back to PLL.  `CutInv` enters once, on
the `∀p` side, to discharge the `E₀` that the cell's own minimality
places beside the candidate hypothesis; `E₀` is derivable outright
(`soundE` at the empty station), so this use of cut is a weakening in
disguise and would go if `IsUIPair` were stated with the `E`-relativised
`minA` made optional at the empty station. -/
def isUIPairPLL_of_isUIPair (cut : CutInv) {p : String} {φ : PLLFormula}
    {E A₁ E₀ A : Neg}
    (uE : IsUIPair p [negOfO φ] (negOfO φ) E A₁)
    (uA : IsUIPair p [] (negOfO φ) E₀ A) :
    IsUIPairPLL p φ (eraseNeg E) (eraseNeg A) where
  pfreeE := pfree_roundTripN uE.pfreeE
  pfreeA := pfree_roundTripN uA.pfreeA
  soundE := by
    have h := Inv.sound uE.soundE
    simp only [eraseCtx, List.map_cons, List.map_nil, List.nil_append,
      (erase_polarise φ).2, goal] at h
    exact ⟨h⟩
  minE := by
    intro ψ hψ hd
    obtain ⟨d⟩ := (bridge_iff [φ] ψ).mp hd
    have h0 : Inv ([negOfO φ] ++ []) [] .tru (negOfO ψ) :=
      d.wk (fun Z hZ => List.mem_append.mpr (Or.inl hZ))
    have h1 := uE.minE [] (negOfO ψ) pfreeCtx_nil hψ h0
    have h := Inv.sound h1
    simp only [eraseCtx, List.map_cons, List.map_nil, List.nil_append,
      (erase_polarise ψ).2, goal] at h
    exact ⟨h⟩
  soundA := by
    have h := Inv.sound uA.soundA
    simp only [eraseCtx, List.map_cons, List.map_nil, List.nil_append,
      (erase_polarise φ).2, goal] at h
    exact ⟨h⟩
  minA := by
    intro ψ hψ hd
    obtain ⟨d⟩ := (bridge_iff [ψ] φ).mp hd
    have h0 : Inv ([] ++ [negOfO ψ]) [] .tru (negOfO φ) := d
    have h1 := uA.minA [negOfO ψ] (pfreeCtx_singleton hψ) h0
    have h2 : Inv ([] ++ [negOfO ψ]) [] .tru A := cut _ _ _ _ _ uA.soundE h1
    have h := Inv.sound h2
    simp only [eraseCtx, List.map_cons, List.map_nil, List.nil_append,
      (erase_polarise ψ).2, goal] at h
    exact ⟨h⟩

/-- What the transport still needs, per formula: a uniform-interpolant
pair at the polarised station and one at the polarised goal cell.  The
second is an instance of N3 forward at the empty station (`Saturated []`,
`ParkedCtxP []`); the first is N3 forward at the SATURATION of
`[negOfO φ]`, so it also needs the processing phase `eMinPP`/`aMinPP`
(`LJF/OFuelPMin.lean`) to move the pair from the saturated station back to
`[negOfO φ]`.  That last step is WP4's, and is the only thing between this
file and `PLL_UI`. -/
def CellsFor (p : String) : Type :=
  ∀ φ : PLLFormula, HasUI p [negOfO φ] (negOfO φ) × HasUI p [] (negOfO φ)

/-- **Uniform interpolation for PLL, from the cells.** -/
def pll_ui_of_ljfo (cut : CutInv) (cells : ∀ p, CellsFor p) : PLL_UI := by
  intro p φ
  obtain ⟨⟨E, A₁, uE⟩, ⟨E₀, A, uA⟩⟩ := cells p φ
  exact ⟨eraseNeg E, eraseNeg A, isUIPairPLL_of_isUIPair cut uE uA⟩


end LJFO

/-! ## Pins

Measured with `#axioms_within_pin`, not retyped.  Nothing here reaches
`Classical.choice`: the fuel recursion spends none, and neither does the
`fun_induction` of `interpP_pfree`. -/

#axioms_within LJFO.EStabEq [propext]
#axioms_within LJFO.AStabEq [propext]
#axioms_within LJFO.EStabilises [propext]
#axioms_within LJFO.AStabilises [propext]
#axioms_within LJFO.estabilises_of_stabEq [propext, Quot.sound]
#axioms_within LJFO.astabilises_of_stabEq [propext, Quot.sound]
#axioms_within LJFO.interpP_pfree [propext, Quot.sound]
#axioms_within LJFO.FuelStep [propext]
#axioms_within LJFO.FuelIrrelevance [propext]
#axioms_within LJFO.eStabEq_of_fuelStep [propext]
#axioms_within LJFO.aStabEq_of_fuelStep [propext]
#axioms_within LJFO.IsUIPair []
#axioms_within LJFO.HasUI []
#axioms_within LJFO.pfreeCtx_nil []
#axioms_within LJFO.pfreeCtx_singleton [propext]
#axioms_within LJFO.hasUI_of_stabEq [propext, Quot.sound]
#axioms_within LJFO.CutInv []
#axioms_within LJFO.stabilises_of_hasUI [propext, Quot.sound]

#axioms_within LJFO.PFreeF []
#axioms_within LJFO.pfree_posOfO_of_negOfO []
#axioms_within LJFO.pfree_roundTripN []
#axioms_within LJFO.pfree_roundTripP []
#axioms_within LJFO.IsUIPairPLL []
#axioms_within LJFO.PLL_UI []
#axioms_within LJFO.isUIPairPLL_of_isUIPair [propext, Quot.sound]
#axioms_within LJFO.CellsFor []
#axioms_within LJFO.pll_ui_of_ljfo [propext, Quot.sound]
