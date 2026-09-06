/-
Route (B), node **N4**, WP12c: the **derivation-level** escape design for the
pair recursion, and the reduction of `SatE2R` / `SatA2R` to it.

## Why the escapes must be derivations and not formulas

`wip/ui_routeB_r_esc2.lean` restates §4.32's escapes so that they no longer
mention the current station, and Part 3 there proves the four steps at which
the record changes.  What that restatement does NOT repair is a step INSIDE
the `∃p` traversal, and it is the step that decides the design.

At a station attack on a parked `Qa ⊃ N ∈ done` whose row is not cut, the
`∃p` traversal must discharge the row's guard `A^R(done ⇒ ↑Qa | (Qa,done)::seen)`,
which only the `∀p` statement at the extended record supplies.  Carrying
formula-level escapes, that statement returns

    A^R(done ⇒ ↑Qa | (Qa,done)::seen)  ∨  ⋁_k A^R(T_k ⇒ ↑Q_k | u_k)

and in an escape branch the `∃p` traversal holds a `∀p` formula about an
ANCESTOR station `T_k` and must still prove its own goal `ψ`.  Every way of
using it needs a derivation of `ψ` at the ancestor's fire state
`([N_k], rest_k)`, which is available only by transporting the current
derivation there — and a transport is a cut, so its height is not controlled
and the family's measure cannot pay for the step.  Putting the escapes into
the `∃p` CONCLUSION instead is no better: the `∃p` traversal replays the
goal's own introductions (`impR`, `andR`, `circR`), which a disjunctive goal
blocks; and putting them into the `∃p` HYPOTHESIS needs a conjunct
implying the goal, which is not fixed along the traversal.

The repair is to make the escape a DERIVATION rather than a formula.  Two
facts about `interpR` make it work.

**(1) The record extension is confined to the guard call.**  In both rows the
extension `(Qa, done) :: seen` occurs in the guard sub-call ALONE; the fire
continuation and the residual are read at `seen` (`parkRowER_record`,
`parkRowAR_record` below, and every other clause of `stepR` passes its record
through unchanged).  So a state whose record contains `(Qa, done)` is a state
inside that guard's sub-traversal, and the derivation it carries is a proper
sub-derivation of the guard derivation `s_d` used there.

**(2) So an escape can carry a strictly smaller guard derivation.**  When the
loop check fires for a recorded pair, the traversal holds the antecedent
sub-derivation of the current derivation — a derivation of the SAME guard
sequent (up to the set-equality of the stations, which `Inv.wk` absorbs) of
height strictly below the one in use at the recording site.  Returned as an
escape, it is caught at that site, which RESTARTS its guard call with it.
The restart is well-founded on the guard derivation's height
(`escapeLoop`), and an escape for an older pair is passed further up.

This is `docs/ui-ljfo-clause-table.md` §4.28's "the sub-derivation is
smaller, the induction hypothesis at the guard state applies to it" taken
literally, with the consequence returned as a derivation instead of being
re-expressed as a formula.

## What is in this module

The confinement equations, the abstract loop, the escape type, the two
traversal obligations stated verbatim (OPEN — no term of either type is
built), and the reduction: at the empty record the escape branch is
UNINHABITED, so the obligations give `SatE2R` and `SatA2R` outright.

`LJF/` is untouched; this module is a leaf.  `LJF.OFuelHeight` is imported
for `hgtI` only; the family modules `LJF.OFuelPFam`, `LJF.OFuelPFamKit`,
`LJF.OFuelPCofinal` are NOT imported.
-/
import wip.ui_routeB_r_esc2
import LJF.OFuelHeight
import Meta.Audit

set_option autoImplicit false

namespace LJFO

/-! # Part 1 · The record extension is confined to the guard call -/

/-- **The `∃p` row.**  `(Qa, done) :: seen` occurs in the guard sub-call
alone: the fire continuation `prev [N] rest none` and the residual
`prev res rest none` are read at `seen`. -/
theorem parkRowER_record (prev : ApproxR) (done : List Neg) (Qa : Pos) (N : Neg)
    (rest res : List Neg) (seen : SeenR) :
    parkRowER id prev done Qa N rest res seen =
      nAnd (if seenMemR seen Qa done then nTop
            else .imp (.down (prev [] done (some (.up Qa)) ((Qa, done) :: seen)))
                      (prev [N] rest none seen))
           (prev res rest none seen) := rfl

/-- **The `∀p` attack row.**  The same: only the guard conjunct sees the
extension. -/
theorem parkRowAR_record (prev : ApproxR) (done : List Neg) (Qa : Pos) (N : Neg)
    (rest : List Neg) (goal : Neg) (seen : SeenR) :
    parkRowAR id prev done Qa N rest goal seen =
      (if seenMemR seen Qa done then nBot
       else nAnd (prev [] done (some (.up Qa)) ((Qa, done) :: seen))
                 (prev [N] rest (some goal) seen)) := rfl

/-! ## The set-equality at a cut site is absorbed by weakening

The loop check fires when a pair `(Q, T)` is recorded whose station `T` is
SET-EQUAL to the current one, not equal to it.  The escape must therefore
carry a derivation at `T` where the traversal holds one at `done`; the two
sequents differ only by the multiplicity and order of hypotheses, which
`Inv.wk` absorbs.  Proved here so that §5 of `docs/n4-pair-cofinality.md`
rests on a theorem and not on a picture. -/

/-- **Set-equal stations weaken into one another.** -/
theorem sameSet_subs {T S : List Neg} (h : sameSet T S = true) :
    Sub T S ∧ Sub S T :=
  ⟨fun X hX => ((sameSet_iff T S).mp h).1 X hX,
   fun X hX => ((sameSet_iff T S).mp h).2 X hX⟩

/-- **A derivation moves between set-equal stations.**  This is the step the
escape takes at a cut site: the traversal holds a derivation at the current
station `done`, the escape must carry one at the recorded station `T`, and
`sameSet T done` is exactly what the loop check tested. -/
def wkSameSet {T S Γ : List Neg} {Ω : List Pos} {j : JD} {C : Neg}
    (h : sameSet T S = true) (d : Inv (T ++ Γ) Ω j C) : Inv (S ++ Γ) Ω j C :=
  d.wk (fun Z hZ => by
    rcases List.mem_append.mp hZ with hZ | hZ
    · exact List.mem_append_left _ ((sameSet_subs h).1 Z hZ)
    · exact List.mem_append_right _ hZ)

/-! # Part 2 · The recording-site loop, abstractly

The site that records a pair calls the guard sub-traversal; if that returns
an escape for the pair just recorded, the site restarts with the strictly
smaller derivation the escape carries.  Stripped of everything else, that is
recursion on a natural number. -/

/-- **The restart is well-founded.**  Given an attempt that either succeeds
or returns a strictly smaller input, iterating it succeeds. -/
def escapeLoop {R D : Type} (h : D → Nat)
    (g : (d : D) → Sum R {d' : D // h d' < h d}) (d : D) : R :=
  match g d with
  | .inl r => r
  | .inr w => escapeLoop h g w.1
  termination_by h d
  decreasing_by exact w.2

/-! # Part 3 · The escape type -/

/-- The heights in use at the sites that recorded the pairs of a record: one
natural number per recorded pair. -/
def HeightBook : SeenR → Type
  | [] => PUnit
  | _ :: s => Nat × HeightBook s

/-- **A derivation-level escape** at a state whose record is `seen`: a
recorded pair, located by the suffix of the record at which it sits, together
with a derivation of THAT pair's own guard sequent whose height is strictly
below the height booked for its recording site. -/
inductive EscD (K : List Neg) : (seen : SeenR) → HeightBook seen → Type where
  /-- an escape for the head pair of the record. -/
  | here {Q : Pos} {T : List Neg} {s : SeenR} {n : Nat} {bs : HeightBook s}
      (gd : Inv (T ++ K) [] .tru (.up Q)) (hlt : hgtI gd < n) :
      EscD K ((Q, T) :: s) (n, bs)
  /-- an escape for an older pair, passed through. -/
  | there {e : Pos × List Neg} {s : SeenR} {n : Nat} {bs : HeightBook s} :
      EscD K s bs → EscD K (e :: s) (n, bs)

/-- **At the empty record there is no escape.** -/
theorem escD_nil_empty {K : List Neg} (e : EscD K [] PUnit.unit) : False := nomatch e

/-! # Part 4 · The two obligations, verbatim (OPEN) -/

/-- **The `∃p` traversal at a saturated station, with derivation-level
escapes** (OPEN).  `SatE2R` generalised to an arbitrary record, the
conclusion admitting an escape. -/
def SatE2RD (p : String) : Type :=
  ∀ (done Δ : List Neg) (ψ : Neg) (seen : SeenR) (b : HeightBook seen),
    Saturated done → ParkedCtxP done → PFreeCtx p Δ → PFreeN p ψ →
    ∀ {j : JD}, Inv (done ++ Δ) [] j ψ →
      Sum (UpFrom (fun e => Inv (interpR p e [] done none seen :: Δ) [] j ψ))
          (EscD Δ seen b)

/-- **The `∀p` entry at a saturated station, with derivation-level escapes**
(OPEN).  `SatA2R` generalised the same way. -/
def SatA2RD (p : String) : Type :=
  ∀ (done Δ : List Neg) (G : Neg) (seen : SeenR) (b : HeightBook seen),
    Saturated done → ParkedCtxP done → PFreeCtx p Δ →
    ∀ {j : JD}, Inv (done ++ Δ) [] j G →
      Sum (UpFrom2 (fun e f => Inv (interpR p e [] done none seen :: Δ) [] .tru
             (interpR p f [] done (some (jGoal j G)) seen)))
          (EscD Δ seen b)

/-! # Part 5 · The reduction

At `seen = []` the escape branch is uninhabited, so both obligations give the
residuals of §4.31 outright, with no escape formulas anywhere. -/

/-- **`SatE2R` from the escape-carrying `∃p` traversal.** -/
noncomputable def satE2R_of_escD {p : String} (t : SatE2RD p) : SatE2R p :=
  fun done Δ ψ hsat hP hΔ hψ {_j} d =>
    match t done Δ ψ [] PUnit.unit hsat hP hΔ hψ d with
    | .inl w => w
    | .inr e => (escD_nil_empty e).elim

/-- **`SatA2R` from the escape-carrying `∀p` entry.** -/
noncomputable def satA2R_of_escD {p : String} (a : SatA2RD p) : SatA2R p :=
  fun done Δ G hsat hP hΔ {_j} d =>
    match a done Δ G [] PUnit.unit hsat hP hΔ d with
    | .inl w => w
    | .inr e => (escD_nil_empty e).elim

/-- **`PLL_UI` over the two derivation-level obligations alone**, with
`SatE2P` / `SatA2P` (inhabited by `satE2P` / `satA2P`,
`LJF/OFuelPCofinal.lean`) kept as variables because this leaf must not import
the family. -/
noncomputable def pll_ui_R_escD (s2 : ∀ p, SatE2P p) (a2 : ∀ p, SatA2P p)
    (te : ∀ p, SatE2RD p) (ta : ∀ p, SatA2RD p) : PLL_UI :=
  pll_ui_R s2 a2 (fun p => satE2R_of_escD (te p)) (fun p => satA2R_of_escD (ta p))

end LJFO

/-! ## Pins -/

#axioms_within LJFO.sameSet_subs [propext, Quot.sound]
#axioms_within LJFO.wkSameSet [propext, Quot.sound]
#axioms_within LJFO.parkRowER_record []
#axioms_within LJFO.parkRowAR_record []
#axioms_within LJFO.escapeLoop []
#axioms_within LJFO.escD_nil_empty []
#axioms_within LJFO.satE2R_of_escD [propext]
#axioms_within LJFO.satA2R_of_escD [propext]
#axioms_within LJFO.pll_ui_R_escD [propext, Classical.choice, Quot.sound]
