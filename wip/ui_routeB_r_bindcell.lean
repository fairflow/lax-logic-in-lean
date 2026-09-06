/-
Route (B), node **N4**, WP12d: **the designed cell** for the binder question
of `wip/ui_routeB_r_bind.lean`.

The analysis there says that a cut site can sit BELOW a `p`-free binder that
a recording site sits ABOVE, so that the escape has to cross the binder.
This module exhibits the configuration as a single kernel-checked
derivation, so the claim rests on a term and not on a trace of the
traversal.  One cell, designed (CLAUDE.md rule 9), not a sweep.

## The cell

    p     := "p"
    Qa    := ↓↑a                          the antecedent of a parked `simp`
    M₀    := ↑a                           so Qa = ↓M₀
    X     := Qa ⊃ ↑n                      the parked implication, compound
    done  := [X, ↑p]                      saturated, `p`-carrying
    HK    := ↓(Qa ⊃ ↑n) ⊃ ↑Qa             a kept implication
    K     := [HK]                         `p`-free
    seen  := [(Qa, done)]                 the pair recorded at the site below

`Qa` is provable at `done ++ K` only through `HK`, and `HK`'s antecedent is
the implication `Qa ⊃ ↑n`, whose proof BINDS `M₀ = ↑a` (`Inv.impR` then
`Inv.downL`) and then attacks `X` again — at the same station, so the loop
test fires (`cellCut`).  The derivation is `cellDeriv`.

The goal is `↑n` throughout, and `X` is the only source of `n` in the whole
sequent, so the cut site cannot avoid firing `X`: `cellRows` computes the
∃p row list of `E^R(done | seen)` and it is
`[⊤ ∧ E^R([], [↑p] | seen), ⊤]` — the fire of `X` has been replaced by `⊤`
and nothing else mentions `n`.  So the traversal there has no row to use and
must escape.

## What the cell settles

* `cellDeriv` type-checks: the configuration is realisable.
* `cellCut : seenMemR seen Qa done = true` — at the second attack the record
  already holds the pair, so `interpR`'s ∃p row there is `⊤`
  (`parkRowER_cut`) and its ∀p row is `⊥` (`parkRowAR_cut`): the traversal
  has no row and must escape.
* `cellRows` computes the whole ∃p row list at that record: the fire of `X`
  is gone.  Since `X` is the only source of the goal atom `n`, the escape is
  not a convenience there — it is the only outcome the traversal has.
* `cellEscapePayload` is that escape's payload, `Inv.stable sInner`, and it
  lives at `M₀ :: (done ++ K)` — under the binder.
* `cellHeight` : its height is strictly below the height booked at the
  recording site, so the escape's own premise holds; the escape is
  well-formed where it is created.
* `cellCrossFails : ↑↓M₀ ∉ K` — `escC_crossDown`'s premise, the only step
  that takes an escape above a `downL` binder, is FALSE here.
* `cellGoalSpan` : the binder's span grants 2 units of height where a
  crossing costs 4 (`hgt_goalSpan`).

Nothing here claims that no derivation of `done ++ K ⊢ ↑Qa` of the required
height exists — no countermodel is built.  What the cell settles is that
the step the family needs is REACHED, and that the step it has does not
apply.

`LJF/` is untouched; this module is a leaf.
-/
import wip.ui_routeB_r_bind
import wip.ui_routeB_r_rows
import Meta.Audit

set_option autoImplicit false

namespace LJFO

namespace BindCell

/-! # Part 1 · The formulas -/

/-- The antecedent of the parked implication: compound, so its row is
loop-checked. -/
def Qa : Pos := .down (.up (.atom "a"))

/-- The hypothesis the goal's antecedent binds.  `Qa = ↓M₀`. -/
def M0 : Neg := .up (.atom "a")

/-- The parked implication, of `interpP`'s `simp` shape `↓↑Pa ⊃ N`. -/
def X : Neg := .imp Qa (.up (.atom "n"))

/-- The station: saturated, and `p`-carrying. -/
def done : List Neg := [X, .up (.atom "p")]

/-- The kept implication whose antecedent is an IMPLICATION, so that proving
it binds `M₀`. -/
def HK : Neg := .imp (.down (.imp Qa (.up (.atom "n")))) (.up Qa)

/-- The `p`-free ambient context. -/
def K : List Neg := [HK]

/-- The sequent's context. -/
def Γ : List Neg := done ++ K

/-- The record in force inside the guard sub-traversal: the pair the
recording site of Part 3 has just booked. -/
def seen : SeenR := [(Qa, done)]

/-! # Part 2 · The side conditions -/

theorem cellSaturated : Saturated done := rfl

theorem cellParked : ParkedCtxP done := by
  intro Z hZ
  rcases List.mem_cons.mp hZ with rfl | hZ
  · exact ParkedNP.simp (.atom "a") (.up (.atom "n"))
  · rcases List.mem_cons.mp hZ with rfl | hZ
    · exact ParkedNP.atom "p"
    · exact absurd hZ List.not_mem_nil

theorem cellPFreeK : PFreeCtx "p" K := by
  intro Z hZ
  rcases List.mem_cons.mp hZ with rfl | hZ
  · show PFreeN "p" HK
    simp only [HK, Qa, PFreeN, PFreeP]
    exact ⟨⟨by decide, by decide⟩, by decide⟩
  · exact absurd hZ List.not_mem_nil

/-! # Part 3 · The derivation

Read it bottom-up: `cellDeriv` attacks `X`, its antecedent sub-derivation
`sGuard` is the RECORDING SITE's guard derivation, `dGoal` is the
GOAL-ANTECEDENT BINDER inside it, and `xCut` is the CUT SITE below the
binder. -/

/-- The right-focus proof of `Qa` from the bound `M₀` alone.  This is the
antecedent sub-derivation the cut site holds, and hence the escape's
payload — and it lives under the binder. -/
def sInner : Stab (M0 :: Γ) .tru Qa :=
  .rfoc (.rel (.stable (.rfoc (.init (by decide)))))

/-- The consequent chain of `X`: the goal atom `n` arrives exactly here. -/
def lfN (Δ : List Neg) :
    LFoc Δ (.up (.atom "n")) .tru (.atom "n") :=
  .rel (.atomL (.stable (.rfoc (.init (List.mem_cons_self ..)))))

/-- **The cut site.**  `X` is attacked a SECOND time, at the same station
`done`, below the binder; its antecedent sub-derivation is `sInner`, which
uses the bound `M₀`. -/
def xCut : Inv (M0 :: Γ) [] .tru (.up (.atom "n")) :=
  .stable (.lfoc (by decide) (.impL sInner (lfN (M0 :: Γ))))

/-- **The goal-antecedent binder.**  `Inv.impR` puts `Qa = ↓M₀` into `Ω`;
`Inv.downL` binds `M₀`. -/
def dGoal : Inv Γ [] .tru (.imp Qa (.up (.atom "n"))) :=
  .impR (.downL xCut)

/-- `HK`'s antecedent, proved by the binder subtree. -/
def sQH : Stab Γ .tru (.down (.imp Qa (.up (.atom "n")))) :=
  .rfoc (.rel dGoal)

/-- `HK`'s consequent `↑Qa`, released. -/
def lfH : LFoc Γ (.up Qa) .tru Qa :=
  .rel (.downL (.stable (.rfoc (.rel (.stable (.rfoc (.init (by decide))))))))

/-- **The recording site's guard derivation.**  `Qa` at the station `done`,
which is what the dispatch on `X` in `cellDeriv` hands to the guard call —
and the height booked for the pair `(Qa, done)`. -/
def sGuard : Stab Γ .tru Qa := .lfoc (by decide) (.impL sQH lfH)

/-- **The cell.**  `X` attacked at the station `done`: the RECORDING SITE. -/
def cellDeriv : Inv Γ [] .tru (.up (.atom "n")) :=
  .stable (.lfoc (by decide) (.impL sGuard (lfN Γ)))

/-! # Part 4 · What the cell settles -/

/-- **The loop test fires at the cut site.**  So `interpR`'s ∃p row there is
`⊤` and its ∀p row is `⊥`: the traversal has no row and must escape. -/
theorem cellCut : seenMemR seen Qa done = true := by decide

/-- The ∃p row at the cut site, by `parkRowER_cut`. -/
theorem cellRowE (prev : ApproxR) (N : Neg) (rest res : List Neg) :
    parkRowER id prev done Qa N rest res seen
      = nAnd nTop (prev res rest none seen) :=
  by rw [parkRowER_record, if_pos cellCut]

/-- **The whole ∃p row list at the cut site's record.**  The fire of `X` has
become `⊤`; the row of `↑p` is `⊤` because its atom IS `p`.  Nothing that
remains mentions `n`, and `X` is the only source of `n` in the sequent, so
the traversal has no route to the goal and must escape. -/
theorem cellRows (prev : ApproxR) :
    eRowsR id "p" prev done seen
      = [nAnd nTop (prev [] [Neg.up (.atom "p")] none seen), nTop] := rfl

/-- The ∀p row at the cut site, by `parkRowAR_cut`. -/
theorem cellRowA (prev : ApproxR) (N : Neg) (rest : List Neg) (goal : Neg) :
    parkRowAR id prev done Qa N rest goal seen = nBot :=
  by rw [parkRowAR_record, if_pos cellCut]

/-- **The escape's payload**, as the cut site holds it: a derivation of the
guard sequent's goal, at the station `done` — and at the context `M₀ :: Γ`,
BELOW the binder. -/
def cellEscapePayload : Inv (M0 :: Γ) [] .tru (.up Qa) := .stable sInner

/-- **Its own premise holds**: it is strictly below the height booked at the
recording site, so `EscC.here` is well-formed where it is created. -/
theorem cellHeight :
    hgtI cellEscapePayload + 4 < hgtI (Inv.stable sGuard) := by decide

/-- **The step that would take it above the binder does not apply.**
`escC_crossDown` needs `↑↓M₀ ∈ K`, and `↑↓M₀ = ↑Qa` is not a member of `K`:
it is the CONSEQUENT of `HK`, reached through `LFoc.impL`, not a hypothesis.
`escC_crossMem` needs `M₀ ∈ K`, and `M₀ = ↑a` is not there either. -/
theorem cellCrossFails : Neg.up (.down M0) ∉ K ∧ M0 ∉ K := by decide

/-- **And the room would not pay for it anyway.**  The binder's span grants
2 units of normalised height; `bindBackI` costs 4. -/
theorem cellGoalSpan : hgtI dGoal = hgtI xCut + 2 := hgt_goalSpan xCut

end BindCell

end LJFO

/-! ## Pins -/

#axioms_within LJFO.BindCell.cellSaturated [propext]
#axioms_within LJFO.BindCell.cellParked [propext]
#axioms_within LJFO.BindCell.cellPFreeK [propext]
#axioms_within LJFO.BindCell.cellDeriv [propext]
#axioms_within LJFO.BindCell.cellCut []
#axioms_within LJFO.BindCell.cellRows [propext]
#axioms_within LJFO.BindCell.cellRowE []
#axioms_within LJFO.BindCell.cellRowA []
#axioms_within LJFO.BindCell.cellHeight [propext]
#axioms_within LJFO.BindCell.cellCrossFails [propext]
#axioms_within LJFO.BindCell.cellGoalSpan [propext]
