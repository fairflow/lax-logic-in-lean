/-
LJF◯ — the cofinality family for the parking interpolant `interpP`
(route (B), node N0c over node N0e).

This module carries the two ENTRY POINTS of the cofinality family as
typed statements, the reduction of `SatE2P`/`SatA2P` to them, and the
antecedent-dispatch obligation with its discharge.  Nothing here is a
`sorry`: an open case is a typed obligation (`def … : Type := ∀ …`), the
`CimpAnt` idiom of `LJF/O.lean`, so that nothing is asserted.

## The measure

`LJF/O.lean`'s weight-founded family is ordered by

    (station-and-goal weight, sizeOf d)

and `LJF/OFuelMin.lean`'s termination note shows that no order of that
form survives the RETENTION edge — the guard `A(done ⇒ …)` at the FULL
station makes the antecedent dispatch a call of the `∀p` family at an
UNCHANGED station, on a strict subderivation, and §4.11's cycle then
forces the weight to be constant round a cycle at a fixed station, which
a goal-blind weight cannot pay for.  The order that does survive puts the
derivation first:

    μ := (normalised derivation height, station weight with the
          `LJF/O.lean` offsets, derivation size)     lexicographic

with the normalised height of `LJF/OFuelHeight.lean` Part 10 —
`hgtI d = szI d`, `hgtS s = szS s + 1`, `hgtL lf = szL lf + 2`,
`hgtR r = szR r + 2` — under which the phase constructors are neutral.

`LJF/OFuelHeight.lean` §7.2 refuted that order for `interpF`: its three
PROCESSING clauses that reshape a parked implication's antecedent have
derivation transformers (`invImpOr`, `invStrip`, `invCurry`) that RAISE
the height while the station weight drops.  `interpP` parks those three
shapes instead, which is why the order is available here.  Part 10 is the
height side of the edge table:

    edge class                        height          discharged by
    ------------------------------------------------------------------
    structural descent                strictly <      10.3
    antecedent dispatch (5 shapes)    strictly <      10.4 hgt_antDispatch
    fire continuation                 strictly <      10.5 hgt_fireCont
    box row                           = (station ↓)   10.5 hgt_boxRow
    the two release sites             strictly <      10.6 hgt_release*
    goal inversion                    strictly <      10.7 hgt_goalInv
    parking (all EIGHT shapes)        EXACT (st. ↓)   10.1 hgt_wk
    ↑(P∨Q), ↑↓M, M∧N, ⊥⊃N, fire scan  ≤    (st. ↓)   10.7
    phase change                      = (size ↓)      10.1

The station side is the `LJF/O.lean` measure unchanged (`ljf_dec_e` /
`ljf_dec_a`, with `dec_park` where the reshaping clauses used
`dec_impor` / `dec_stripshift` / `dec_curry`), and the third component is
`sizeOf`, as there.

## What is OPEN

The family itself, in fuel-carrying (`UpFrom`/`UpFrom2`) form: `interpP`
has no chain-monotonicity lemma, so every traversal must return an
upward-closed witness rather than a derivation at one fuel, and each
clause must combine its sub-witnesses by `max` and re-read them at the
common threshold (`LJF/OFuelMin.lean` Part 1; `eMinPP`/`aMinPP` are the
worked precedent for the processing phase).  That is witness
bookkeeping, not termination, and it is not done here.

The two entry points below are therefore typed OBLIGATIONS.  Everything
downstream of them is proved: `SatE2P`/`SatA2P` reduce to them, and
`ECofinalP`/`ACofinalP` reduce to those
(`wip/ui_routeB_statements.lean`).
-/
import LJF.OFuelPMin
import LJF.OFuelHeight
import Meta.Audit

namespace LJFO

/-! ## The two entry points, as typed obligations

`TInvP` is `LJF/O.lean`'s `TInv` and `UEntryP` is its `UEntry`, with
`interp` replaced by `interpP`, `ParkedCtx` by `ParkedCtxP`, and the
value replaced by an upward-closed fuel witness.  They are the exact
statements the family's mutual block would inhabit. -/

/-- **The `∃p` traversal at a saturated station**, fuel form: from a
derivation over a mixed context `Γ′ ⊆ done ∪ K` with a `p`-free `K`,
`Ω` and goal, a derivation from the `∃p` approximant beside `K`, from
some fuel on. -/
def TInvP (p : String) : Type :=
  ∀ (done : List Neg), Saturated done → ParkedCtxP done →
    ∀ {Γ' K : List Neg} {Ω : List Pos} {C : Neg} {j : JD},
      (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
      PFreeΩ p Ω → PFreeN p C →
      Inv Γ' Ω j C →
      UpFrom (fun e => Inv (interpP p e [] done none :: K) Ω j C)

/-- **The `∀p` entry at a saturated station**, fuel form: from a
derivation of any goal over a mixed context, the `∀p` approximant of that
goal beside `K`, relativised to the `∃p` approximant, from some fuel on.
The two fuels are independent, over one shared threshold. -/
def UEntryP (p : String) : Type :=
  ∀ (done : List Neg), Saturated done → ParkedCtxP done →
    ∀ {Γ' K : List Neg},
      (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
      ∀ (G : Neg) {j : JD}, Inv Γ' [] j G →
      UpFrom2 (fun e f => Inv (interpP p e [] done none :: K) [] .tru
        (interpP p f [] done (some (jGoal j G))))

/-! ## The reductions, proved

Both are the projections `LJF/O.lean`'s `satE2`/`satA2` take: the
saturated station `done` sits at the head of `done ++ Δ`, and the
`p`-free part `K` is `Δ`. -/

/-- `SatE2P` reduces to the `∃p` traversal. -/
def satE2P_of_tinvP {p : String} (t : TInvP p) : SatE2P p :=
  fun done Δ ψ hsat hP hΔ hψ {_j} d =>
    t done hsat hP (fun Z hZ => List.mem_append.mp hZ)
      (fun Z hZ => List.mem_append_left _ hZ) hΔ PFreeΩ.nil hψ d

/-- `SatA2P` reduces to the `∀p` entry. -/
def satA2P_of_uentryP {p : String} (u : UEntryP p) : SatA2P p :=
  fun done Δ G hsat hP hΔ {_j} d =>
    u done hsat hP (fun Z hZ => List.mem_append.mp hZ)
      (fun Z hZ => List.mem_append_left _ hZ) hΔ G d

/-! ## The antecedent dispatch

`interpP`'s rows for the FIVE parked implication shapes — the
◯-implication and the Dyckhoff shape of `interpF`, and the three shapes
`interpP` newly parks — all guard the fire by the `∀p` of the
ANTECEDENT at the FULL station.  Using such a row asks for that `∀p`
from a main-line stable proof of the antecedent.  One statement covers
all five, generic in the antecedent positive `Q`.

Where `LJF/O.lean`'s `CimpAnt` asks for the `∀p` at the RESIDUAL station
— unreachable from a proof over a context containing the full station,
which is why it stands isolated there — this asks for it at `done`, and
`done ∪ K` is exactly the context the antecedent proof lives over.  So
it is an instance of `∀p`-cofinality itself, applied to the antecedent's
own subderivation, and `parkAntP_of_satA2P` below proves that.

What makes it a legitimate RECURSIVE call, which is what `CimpAntF`
lacked, is `LJF/OFuelHeight.lean` §10.4: the argument
`(Inv.stable s_d).wk H` is strictly below the focus
`Stab.lfoc h (.impL s_d lf′)` in normalised height, so the first
component of `μ` drops even though the station does not move. -/

/-- **The antecedent dispatch obligation**, generic in the antecedent
positive. -/
def ParkAntP (p : String) : Type :=
  ∀ (done K Γ' : List Neg) (Q : Pos) (N : Neg),
    Saturated done → ParkedCtxP done →
    Neg.imp Q N ∈ done →
    (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
    Stab Γ' .tru Q →
    UpFrom2 (fun e f => Inv (interpP p e [] done none :: K) [] .tru
      (interpP p f [] done (some (.up Q))))

/-- **The dispatch is an instance of `∀p`-cofinality itself**, at the SAME
station and applied to the antecedent's own subderivation.  This is the
content of the retention design, generalised from the ◯-implication to
every parked implication shape. -/
def parkAntP_of_satA2P {p : String} (a2 : SatA2P p) : ParkAntP p :=
  fun done K Γ' Q N hsat hP _hX hm _hm2 hK s =>
    ((a2 done K (.up Q) hsat hP hK (j := .tru)
      ((Inv.stable s).wk (fun Z hZ => by
        rcases hm Z hZ with hd | hk
        · exact List.mem_append_left _ hd
        · exact List.mem_append_right _ hk))).map
      (fun _e _f d => by rw [jGoal_tru] at d; exact d))

/-- And the height fact that makes the dispatch a legitimate recursive
call rather than an isolated obligation: the argument is strictly below
the focus in normalised height, so `μ`'s first component drops with the
station unchanged. -/
theorem parkAnt_edge {Γ Γ₂ : List Neg} {j : JD} {Q : Pos} {N : Neg}
    {P : Pos} (H : Sub Γ Γ₂) (h : Neg.imp Q N ∈ Γ)
    (s_d : Stab Γ .tru Q) (lf' : LFoc Γ N j P) :
    hgtI ((Inv.stable s_d).wk H) < hgtS (Stab.lfoc h (.impL s_d lf')) :=
  hgt_antDispatch H h s_d lf'

end LJFO

/-! ### Axiom audit -/

#axioms_within LJFO.satE2P_of_tinvP [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.satA2P_of_uentryP [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.parkAntP_of_satA2P [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.parkAnt_edge [propext, Classical.choice, Quot.sound]

#axioms_within LJFO.satE2P_of_tinvP [propext]
#axioms_within LJFO.satA2P_of_uentryP [propext]
#axioms_within LJFO.parkAntP_of_satA2P [propext]
