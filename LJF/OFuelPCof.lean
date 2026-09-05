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
ANTECEDENT'S OWN GOAL `↑Q` at the FULL station (the Dyckhoff row since
2026-09-05, `docs/ui-ljfo-clause-table.md` §4.15).  Using such a row
asks for that `∀p` from a main-line stable proof of the antecedent.
One statement covers all five, generic in the antecedent positive `Q`.

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

/-! ## The upward-closed witness kit

`interpP` has no chain-monotonicity lemma, so every value the family
produces is an `UpFrom`/`UpFrom2` witness (`LJF/OFuelMin.lean` Part 1)
and every clause with more than one sub-result must combine thresholds
by `max`.  Part 1 has the unary combinators; these are the binary and
ternary ones the traversals need. -/

/-- Combine two `UpFrom` witnesses at a common threshold. -/
def UpFrom.map₂ {P Q R : Nat → Type} (k : ∀ f, P f → Q f → R f)
    (w : UpFrom P) (v : UpFrom Q) : UpFrom R :=
  ⟨max w.1 v.1, fun f hf =>
    k f (w.2 f (Nat.le_trans (Nat.le_max_left _ _) hf))
        (v.2 f (Nat.le_trans (Nat.le_max_right _ _) hf))⟩

/-- Combine three. -/
def UpFrom.map₃ {P Q R S : Nat → Type} (k : ∀ f, P f → Q f → R f → S f)
    (w : UpFrom P) (v : UpFrom Q) (u : UpFrom R) : UpFrom S :=
  UpFrom.map₂ (fun f x y => y x) w (UpFrom.map₂ (fun f y z x => k f x y z) v u)

/-- Combine two `UpFrom2` witnesses. -/
def UpFrom2.map₂ {P Q R : Nat → Nat → Type} (k : ∀ e f, P e f → Q e f → R e f)
    (w : UpFrom2 P) (v : UpFrom2 Q) : UpFrom2 R :=
  ⟨max w.1 v.1, fun e f he hf =>
    k e f (w.2 e f (Nat.le_trans (Nat.le_max_left _ _) he)
                   (Nat.le_trans (Nat.le_max_left _ _) hf))
          (v.2 e f (Nat.le_trans (Nat.le_max_right _ _) he)
                   (Nat.le_trans (Nat.le_max_right _ _) hf))⟩

/-- An `UpFrom` witness read at the `∃p` fuel of an `UpFrom2` family. -/
def UpFrom.toUpFrom2 {P : Nat → Type} (w : UpFrom P) :
    UpFrom2 (fun e _ => P e) :=
  ⟨w.1, fun e _ he _ => w.2 e he⟩

/-! ## The ∃p row of a parked implication, assembled and fired

`LJF/OCore.lean`'s `cimpAssembleN`, generalised in the antecedent's goal
and moved to `interpP`.  One statement covers all FIVE parked implication
shapes, because `interpP` gives them all the SAME row form: the fire
guarded by the `∀p` of the antecedent at the full station, paired with a
residual component `R` the assembler never inspects. -/

/-- Fire a parked implication's `∃p` row: the guard supplies the
antecedent, the recursively interpolated body is consumed through `δ`. -/
def parkAssembleP {p : String} {f : Nat} {done rest K : List Neg}
    {G' N C R : Neg} {L : List Neg}
    (hE : interpP p (f + 1) [] done none = nAndAll L)
    (hmem : nAnd (.imp (.down (interpP p f [] done (some G')))
                       (interpP p f [N] rest none)) R ∈ L)
    (sant : Inv (interpP p (f + 1) [] done none :: K) [] .tru
      (interpP p f [] done (some G')))
    {j : JD} (δ : Inv (interpP p f [N] rest none :: K) [] j C) :
    Inv (interpP p (f + 1) [] done none :: K) [] j C :=
  simHyp
    (fl := fun hs lf =>
      .lfoc (hs _ (List.mem_cons_self ..))
        (hE.symm ▸ lfocAndAll hmem
          (.and1 (.impL (.rfoc (.rel (sant.wk hs))) lf))))
    (Sub.grow _) δ

/-- **The retention row, used** — the clause of the `∃p` traversal that
the retention design exists for, in isolation and in fuel-carrying form.
Given the antecedent's `∀p` at the FULL station (an `UpFrom2` witness, of
the shape `ParkAntP` delivers) and the continuation's `∃p` at the
residual station, the fire of the row is available from some fuel on:
take the aggregate at `f+1`, its guard at `f`, and the continuation at
`f`, over the two thresholds' maximum.

This is what `LJF/OFuelMin.lean`'s `CimpAntF` could only state: there the
guard sits at the RESIDUAL station, so the two fuels cannot be lined up
with a proof over the full station.  Here they line up, and the `UpFrom2`
two-fuel form is exactly what makes them. -/
def parkFireE {p : String} {done rest K : List Neg} {G' N C : Neg}
    {R : Nat → Neg} {j : JD}
    (hsat : Saturated done)
    (hmem : ∀ f, nAnd (.imp (.down (interpP p f [] done (some G')))
                            (interpP p f [N] rest none)) (R f)
              ∈ eConjRowsP p f done)
    (want : UpFrom2 (fun e f => Inv (interpP p e [] done none :: K) [] .tru
              (interpP p f [] done (some G'))))
    (cont : UpFrom (fun e => Inv (interpP p e [N] rest none :: K) [] j C)) :
    UpFrom (fun e => Inv (interpP p e [] done none :: K) [] j C) :=
  UpFrom.mk1 (max want.1 cont.1) (fun f' hf' =>
    parkAssembleP (interpPE_eq hsat) (hmem f')
      (want.2 (f' + 1) f'
        (Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) hf') (Nat.le_succ _))
        (Nat.le_trans (Nat.le_max_left _ _) hf'))
      (cont.2 f' (Nat.le_trans (Nat.le_max_right _ _) hf')))

/-! The five instances, one per parked implication shape.  Each is
`parkFireE` at its own row membership, and since 2026-09-05 all five
take the antecedent goal `↑Q` at the antecedent positive `Q` — the
Dyckhoff shape at `Q := ↓(Q′ ⊃ N′)` like the rest
(`docs/ui-ljfo-clause-table.md` §4.15). -/

/-- `↓◯Q′ ⊃ N` — the ◯-implication row of `interpF`, retained. -/
def cimpFireE {p : String} {done rest K : List Neg} {Q' : Pos} {N C : Neg}
    {j : JD} (hsat : Saturated done)
    (hXr : (Neg.imp (.down (.circ Q')) N, rest) ∈ splits done)
    (want : UpFrom2 (fun e f => Inv (interpP p e [] done none :: K) [] .tru
              (interpP p f [] done (some (.up (.down (.circ Q')))))))
    (cont : UpFrom (fun e => Inv (interpP p e [N] rest none :: K) [] j C)) :
    UpFrom (fun e => Inv (interpP p e [] done none :: K) [] j C) :=
  parkFireE hsat (fun _ => cimpConjMemP hXr) want cont

/-- `↓(Q′ ⊃ N′) ⊃ N` — the Dyckhoff row, guard retained at the full
station and at the antecedent's own goal `↑↓(Q′ ⊃ N′)`, so this is
`parkFireE` at `Q := ↓(Q′ ⊃ N′)` exactly as the other four are. -/
def dykFireE {p : String} {done rest K : List Neg} {Q' : Pos} {N' N C : Neg}
    {j : JD} (hsat : Saturated done)
    (hXr : (Neg.imp (.down (.imp Q' N')) N, rest) ∈ splits done)
    (want : UpFrom2 (fun e f => Inv (interpP p e [] done none :: K) [] .tru
              (interpP p f [] done (some (.up (.down (.imp Q' N')))))))
    (cont : UpFrom (fun e => Inv (interpP p e [N] rest none :: K) [] j C)) :
    UpFrom (fun e => Inv (interpP p e [] done none :: K) [] j C) :=
  parkFireE hsat (fun _ => dykConjMemP hXr) want cont

/-- `(Qa ∨ Qb) ⊃ N` — newly parked. -/
def orimpFireE {p : String} {done rest K : List Neg} {Qa Qb : Pos} {N C : Neg}
    {j : JD} (hsat : Saturated done)
    (hXr : (Neg.imp (.or Qa Qb) N, rest) ∈ splits done)
    (want : UpFrom2 (fun e f => Inv (interpP p e [] done none :: K) [] .tru
              (interpP p f [] done (some (.up (.or Qa Qb))))))
    (cont : UpFrom (fun e => Inv (interpP p e [N] rest none :: K) [] j C)) :
    UpFrom (fun e => Inv (interpP p e [] done none :: K) [] j C) :=
  parkFireE hsat (fun _ => orimpConjMemP hXr) want cont

/-- `↓↑Pa ⊃ N` — newly parked. -/
def shimpFireE {p : String} {done rest K : List Neg} {Pa : Pos} {N C : Neg}
    {j : JD} (hsat : Saturated done)
    (hXr : (Neg.imp (.down (.up Pa)) N, rest) ∈ splits done)
    (want : UpFrom2 (fun e f => Inv (interpP p e [] done none :: K) [] .tru
              (interpP p f [] done (some (.up (.down (.up Pa)))))))
    (cont : UpFrom (fun e => Inv (interpP p e [N] rest none :: K) [] j C)) :
    UpFrom (fun e => Inv (interpP p e [] done none :: K) [] j C) :=
  parkFireE hsat (fun _ => shimpConjMemP hXr) want cont

/-- `↓(Ma ∧ Mb) ⊃ N` — newly parked. -/
def andimpFireE {p : String} {done rest K : List Neg} {Ma Mb N C : Neg}
    {j : JD} (hsat : Saturated done)
    (hXr : (Neg.imp (.down (.and Ma Mb)) N, rest) ∈ splits done)
    (want : UpFrom2 (fun e f => Inv (interpP p e [] done none :: K) [] .tru
              (interpP p f [] done (some (.up (.down (.and Ma Mb)))))))
    (cont : UpFrom (fun e => Inv (interpP p e [N] rest none :: K) [] j C)) :
    UpFrom (fun e => Inv (interpP p e [] done none :: K) [] j C) :=
  parkFireE hsat (fun _ => andimpConjMemP hXr) want cont

/-- And the guard ALL FIVE need is exactly what `ParkAntP` delivers:
`ParkAntP` is stated for every positive antecedent `Q`, and since the
Dyckhoff row's guard moved to `↑↓(Q′ ⊃ N′)` its antecedent
`↓(Q′ ⊃ N′)` is covered with no change to the obligation. -/
def parkAntGuard {p : String} (pant : ParkAntP p)
    {done K Γ' : List Neg} {Q : Pos} {N : Neg}
    (hsat : Saturated done) (hP : ParkedCtxP done)
    (hX : Neg.imp Q N ∈ done)
    (hm : ∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) (hm2 : Sub done Γ')
    (hK : PFreeCtx p K) (s : Stab Γ' .tru Q) :
    UpFrom2 (fun e f => Inv (interpP p e [] done none :: K) [] .tru
      (interpP p f [] done (some (.up Q)))) :=
  pant done K Γ' Q N hsat hP hX hm hm2 hK s

/-- **The fold is exact.**  At `Q := ↓(Q′ ⊃ N′)` the guard `ParkAntP`
delivers is precisely `dykFireE`'s `want`, so the Dyckhoff arms of the
family are parked arms and no separate obligation is needed.  Before the
guard moved to `↑↓(Q′ ⊃ N′)` this did not typecheck — the row wanted
`interpP p f [] done (some (Q′ ⊃ N′))`, which `ParkAntP` cannot supply
(`docs/ui-ljfo-clause-table.md` §4.15). -/
example {p : String} (pant : ParkAntP p)
    {done K Γ' : List Neg} {Q' : Pos} {N' N : Neg}
    (hsat : Saturated done) (hP : ParkedCtxP done)
    (hX : Neg.imp (.down (.imp Q' N')) N ∈ done)
    (hm : ∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) (hm2 : Sub done Γ')
    (hK : PFreeCtx p K) (s : Stab Γ' .tru (.down (.imp Q' N'))) :
    UpFrom2 (fun e f => Inv (interpP p e [] done none :: K) [] .tru
      (interpP p f [] done (some (.up (.down (.imp Q' N')))))) :=
  parkAntGuard pant hsat hP hX hm hm2 hK s

end LJFO

/-! ### Axiom audit -/

#axioms_within LJFO.satE2P_of_tinvP [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.satA2P_of_uentryP [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.parkAntP_of_satA2P [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.parkAnt_edge [propext, Classical.choice, Quot.sound]

#axioms_within LJFO.satE2P_of_tinvP [propext]
#axioms_within LJFO.satA2P_of_uentryP [propext]
#axioms_within LJFO.parkAntP_of_satA2P [propext]

#axioms_within LJFO.UpFrom.map₂ [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.UpFrom.map₃ [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.UpFrom2.map₂ [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.parkAssembleP [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.parkFireE [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.cimpFireE [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.dykFireE [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.orimpFireE [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.shimpFireE [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.andimpFireE [propext, Classical.choice, Quot.sound]

#axioms_within LJFO.parkAssembleP [propext, Quot.sound]
#axioms_within LJFO.parkFireE [propext, Quot.sound]
#axioms_within LJFO.cimpFireE [propext, Quot.sound]
#axioms_within LJFO.dykFireE [propext, Quot.sound]
#axioms_within LJFO.orimpFireE [propext, Quot.sound]
#axioms_within LJFO.shimpFireE [propext, Quot.sound]
#axioms_within LJFO.andimpFireE [propext, Quot.sound]
