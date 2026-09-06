/-
Route (B), node **N4**, WP12d: **the escape and the `p`-free binders of the
inversion phase**.

`wip/ui_routeB_r_escd.lean` gives the derivation-level escape

    EscD (K : List Neg) : (seen : SeenR) → HeightBook seen → Type
      | here (gd : Inv (T ++ K) [] .tru (↑Q)) (hlt : hgtI gd < n)
      | there : EscD K s bs → EscD K (e :: s) (n, bs)

with `K` the `p`-free context the traversal runs at, and
`wip/ui_routeB_r_guard.lean` closes both ends of the mechanism: what a cut
site produces (`escOfCut`) and what a recording site does with it
(`guardLoop`).  Between the two ends sits the traversal, and this module
settles the one thing the traversal does to `K` that neither end sees.

## The step the family needs and neither end supplies

`K` is NOT constant along the saturated phase.  Four clauses of the
`interpP` family extend it — `TInvQ`/`TpInvQ` and `UInvGQ`/`UpInvGQ` at
`Inv.downL` and `Inv.atomL` (`LJF/OFuelPFam.lean` Parts 5 and 6) — because
the derivation binds a new `p`-free hypothesis there:

    | .down M₀ :: _, …, .downL d =>  … (recursive call at `PFreeCtx.cons hM hK`) …

A recording site sits ABOVE such a clause and a cut site can sit BELOW it:
from the guard call `UEntryQ done … (↑Qa) (Inv.stable s_d)` the traversal
reaches `UStabQ`, left-focuses on a KEPT hypothesis (`ULFQ`), inverts its
premise (`UInvGQ`) — binding `M₀` — and then dispatches again on the same
parked `Qa ⊃ N ∈ done`, whose loop test now fires.  The escape that cut
site creates lives at `M₀ :: K`; the recording site's loop needs one at
`K`.  So the family needs

    EscD (M₀ :: K) seen b → EscD K seen b

and `EscD`'s payload is a DERIVATION, so this is a strengthening of a
context, not a weakening: it is not available for nothing.

## What this module proves

It is available exactly when the bound hypothesis is one the context above
can re-supply, and then at a cost the traversal has already paid.

* **Part 1.**  `bindBackI`: if `↑↓M₀ ∈ Γ` then `M₀` can be discharged from
  a derivation of a shift goal, by the four constructors
  `stable · lfoc · rel · downL` — a rule of `LJF◯`, not a cut — and the
  normalised height rises by EXACTLY 4 (`hgt_bindBackI`).
* **Part 2.**  `EscC`, the escape carrying a COST: `hgtI gd + c < n`
  instead of `hgtI gd < n`.  At `c = 0` it is `EscD`
  (`escC_zero`, `escD_of_escC0`).
* **Part 3.**  The crossing lemmas.  `escC_crossDown` crosses a `downL`
  binder at cost `+4` when `↑↓M₀ ∈ K`; `escC_crossAtom` and
  `escC_crossMem` cross at cost `0` when the bound hypothesis is already
  in `K`.
* **Part 4.**  The cost is exactly what the traversal's own descent pays:
  crossing a kept-hypothesis binder consumes the same four constructors
  (`hgt_keptSpan`), so the invariant `BookBound seen b (hgtI d + c)` is
  PRESERVED across the span (`bb_keptSpan`).  No book slack is needed;
  the accounting closes.
* **Part 5.**  The residual, verbatim.  The GOAL-antecedent binder — the
  `∃p` inversion traversal at `Inv.impR` followed by `downL`/`atomL`, where
  the bound hypothesis is the antecedent of the goal being PROVED and is
  therefore not available above — has no such step, and is stated as a
  typed obligation (OPEN; no term is built).

`LJF/` is untouched; this module is a leaf.  The family modules
`LJF.OFuelPFam`, `LJF.OFuelPFamKit`, `LJF.OFuelPCofinal` are NOT imported.
-/
import wip.ui_routeB_r_guard
import Meta.Audit

set_option autoImplicit false

namespace LJFO

/-! # Part 1 · Discharging a bound hypothesis that the context re-supplies

The `downL` binder of the inversion phase puts `M₀` into the context
because the derivation inverted `↓M₀` out of `Ω`.  When that `↓M₀` came
from a KEPT hypothesis — `ULFQ`/`TLFQ` at `LFoc.rel`, where the hypothesis
is `↑↓M₀ ∈ K` — the same hypothesis discharges it again. -/

/-- **The bound hypothesis goes back.**  `↑↓M₀ ∈ Γ` re-supplies `M₀` by
left focus, so a derivation of a shift goal that uses `M₀` becomes one
that does not.  This is `Stab.lfoc · LFoc.rel · Inv.downL` under
`Inv.stable`: four rules of `LJF◯`, no cut. -/
def bindBackI {Γ : List Neg} {M₀ : Neg} {j : JD} {P : Pos}
    (h : Neg.up (.down M₀) ∈ Γ) (x : Inv (M₀ :: Γ) [] j (.up P)) :
    Inv Γ [] j (.up P) :=
  .stable (.lfoc h (.rel (.downL x)))

/-- **Its cost is exactly 4.**  The four constructors it rebuilds are the
four the traversal consumed to reach `x` (Part 4). -/
theorem hgt_bindBackI {Γ : List Neg} {M₀ : Neg} {j : JD} {P : Pos}
    (h : Neg.up (.down M₀) ∈ Γ) (x : Inv (M₀ :: Γ) [] j (.up P)) :
    hgtI (bindBackI h x) = hgtI x + 4 := by
  simp only [bindBackI, hgtI, szI, szS, szL]

/-- The context move the crossing needs on the escape's own payload: the
escape is stated at `T ++ (M₀ :: K)` and `bindBackI` wants `M₀` at the
head. -/
theorem subBindHead (T K : List Neg) (M₀ : Neg) :
    Sub (T ++ M₀ :: K) (M₀ :: (T ++ K)) := by
  intro Z hZ
  rcases List.mem_append.mp hZ with hZ | hZ
  · exact List.mem_cons_of_mem _ (List.mem_append_left _ hZ)
  · rcases List.mem_cons.mp hZ with rfl | hZ
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ hZ)

/-- The context move for a hypothesis ALREADY present: then the extension
is absorbed by weakening alone. -/
theorem subDropMem {K : List Neg} {M₀ : Neg} (hK : M₀ ∈ K) (T : List Neg) :
    Sub (T ++ M₀ :: K) (T ++ K) := by
  intro Z hZ
  rcases List.mem_append.mp hZ with hZ | hZ
  · exact List.mem_append_left _ hZ
  · rcases List.mem_cons.mp hZ with rfl | hZ
    · exact List.mem_append_right _ hK
    · exact List.mem_append_right _ hZ

/-! # Part 2 · The escape carrying a cost

`EscD` demands `hgtI gd < n`.  A crossing raises the payload's height, so
the traversal must carry the room for the crossings still to come.  `EscC`
is `EscD` with that room as an index; at cost `0` the two agree. -/

/-- **A derivation-level escape with `c` units of height still to spend.**
`EscC K 0` is `EscD K`. -/
inductive EscC (K : List Neg) (c : Nat) :
    (seen : SeenR) → HeightBook seen → Type where
  /-- an escape for the head pair of the record. -/
  | here {Q : Pos} {T : List Neg} {s : SeenR} {n : Nat} {bs : HeightBook s}
      (gd : Inv (T ++ K) [] .tru (.up Q)) (hlt : hgtI gd + c < n) :
      EscC K c ((Q, T) :: s) (n, bs)
  /-- an escape for an older pair, passed through. -/
  | there {e : Pos × List Neg} {s : SeenR} {n : Nat} {bs : HeightBook s} :
      EscC K c s bs → EscC K c (e :: s) (n, bs)

/-- At the empty record there is no escape, at any cost. -/
theorem escC_nil_empty {K : List Neg} {c : Nat}
    (e : EscC K c [] PUnit.unit) : False := nomatch e

/-- **`EscD` is `EscC` at cost 0.** -/
def escC_zero {K : List Neg} :
    ∀ (seen : SeenR) (b : HeightBook seen), EscD K seen b → EscC K 0 seen b
  | (_, _) :: _, (_, _), .here gd hlt => .here gd (by omega)
  | _ :: _, (_, _), .there e => .there (escC_zero _ _ e)

/-- and back. -/
def escD_of_escC0 {K : List Neg} :
    ∀ (seen : SeenR) (b : HeightBook seen), EscC K 0 seen b → EscD K seen b
  | (_, _) :: _, (_, _), .here gd hlt => .here gd (by omega)
  | _ :: _, (_, _), .there e => .there (escD_of_escC0 _ _ e)

/-- Room may always be given up. -/
def escC_mono {K : List Neg} {c c' : Nat} (hc : c' ≤ c) :
    ∀ (seen : SeenR) (b : HeightBook seen), EscC K c seen b → EscC K c' seen b
  | (_, _) :: _, (_, _), .here gd hlt => .here gd (by omega)
  | _ :: _, (_, _), .there e => .there (escC_mono hc _ _ e)

/-! # Part 3 · The crossing lemmas

The three shapes of `p`-free binder the inversion phase creates, and the
cost each one charges the escape. -/

/-- **Crossing a `downL` binder whose hypothesis the context re-supplies.**
`↑↓M₀ ∈ K` is what a kept-hypothesis binder has: the clause reached
`M₀` by left-focusing on `↑↓M₀ ∈ K` and inverting, so the same member is
still there.  Cost: 4. -/
def escC_crossDown {K : List Neg} {M₀ : Neg} {c : Nat}
    (hK : Neg.up (.down M₀) ∈ K) :
    ∀ (seen : SeenR) (b : HeightBook seen),
      EscC (M₀ :: K) (c + 4) seen b → EscC K c seen b
  | (_, T) :: _, (_, _), .here gd hlt =>
      .here (bindBackI (List.mem_append_right T hK)
              (gd.wk (subBindHead T K M₀)))
        (by
          rw [hgt_bindBackI, hgt_wk]
          omega)
  | _ :: _, (_, _), .there e => .there (escC_crossDown hK _ _ e)

/-- **Crossing an `atomL` binder whose atom the context already holds.**
The atom binder adds `↑a`, and `ULFQ`/`TLFQ` reached it by left-focusing
on `↑a ∈ K` itself, so the extension is absorbed by weakening.  Cost: 0. -/
def escC_crossAtom {K : List Neg} {a : String} {c : Nat}
    (hK : Neg.up (.atom a) ∈ K) :
    ∀ (seen : SeenR) (b : HeightBook seen),
      EscC (.up (.atom a) :: K) c seen b → EscC K c seen b
  | (_, T) :: _, (_, _), .here gd hlt =>
      .here (gd.wk (subDropMem hK T)) (by rw [hgt_wk]; omega)
  | _ :: _, (_, _), .there e => .there (escC_crossAtom hK _ _ e)

/-- **Crossing any binder whose hypothesis is already kept.**  The general
form of the previous one. -/
def escC_crossMem {K : List Neg} {M₀ : Neg} {c : Nat} (hK : M₀ ∈ K) :
    ∀ (seen : SeenR) (b : HeightBook seen),
      EscC (M₀ :: K) c seen b → EscC K c seen b
  | (_, T) :: _, (_, _), .here gd hlt =>
      .here (gd.wk (subDropMem hK T)) (by rw [hgt_wk]; omega)
  | _ :: _, (_, _), .there e => .there (escC_crossMem hK _ _ e)

/-! # Part 4 · The cost is what the traversal has already paid

The four constructors `bindBackI` rebuilds are the four the traversal
consumed to reach the binder: `Stab.lfoc` on the kept hypothesis,
`LFoc.rel`, `Inv.downL`, `Inv.stable`.  In normalised height that span is
exactly 4, so an escape created below the binder with `c + 4` units of
room is created under a book bound that already grants them: the invariant
`BookBound seen b (hgtI d + c)` needs no slack. -/

/-- **The kept-hypothesis span is exactly 4.**  `LJF/OFuelHeight.lean`
Part 10's normalisation makes the two phase constructors free, so the span
is `lfoc` + `rel` + `downL` + `stable`, and each costs one. -/
theorem hgt_keptSpan {Γ : List Neg} {M₀ : Neg} {j : JD} {P₀ : Pos}
    (h : Neg.up (.down M₀) ∈ Γ) (x : Inv (M₀ :: Γ) [] j (.up P₀)) :
    hgtS (Stab.lfoc h (.rel (.downL x))) = hgtI x + 4 := by
  simp only [hgtS, szS, szL, szI, hgtI]

/-- **So the book invariant crosses the span with the room the crossing
needs.**  At the top of the span the traversal holds the `Stab`; at the
bottom it holds `x`; and what the escape below must beat is exactly what
the book granted above. -/
theorem bb_keptSpan {Γ : List Neg} {M₀ : Neg} {j : JD} {P₀ : Pos}
    {seen : SeenR} {b : HeightBook seen} {c : Nat}
    (h : Neg.up (.down M₀) ∈ Γ) (x : Inv (M₀ :: Γ) [] j (.up P₀))
    (hb : BookBound seen b (hgtS (Stab.lfoc h (.rel (.downL x))) + c)) :
    BookBound seen b (hgtI x + (c + 4)) := by
  rw [hgt_keptSpan] at hb
  exact bookBound_mono seen b (by omega) hb

/-- **The escape a cut site creates, in cost form.**  `escOfCut`
(`wip/ui_routeB_r_guard.lean`) with the room the crossings above will
spend: the derivation in hand is `c + 1` below every booked height, so the
escape it creates has `c` units to give away. -/
def escOfCutC {K : List Neg} {c : Nat} :
    ∀ (seen : SeenR) (b : HeightBook seen) (Qa : Pos) (done : List Neg)
      (h : Nat), seenMemR seen Qa done = true → BookBound seen b h →
      ∀ (gd0 : Inv (done ++ K) [] .tru (.up Qa)), hgtI gd0 + c < h →
      EscC K c seen b
  | [], _, _, _, _, hmem, _, _, _ => absurd hmem (by simp [seenMemR])
  | (Q, T) :: s, ⟨n, bs⟩, Qa, done, h, hmem, hb, gd0, hlt =>
      if hQ : Q = Qa then
        if hT : sameSet T done = true then
          (by
            subst hQ
            refine .here (wkSameSet (sameSet_symm hT) gd0) ?_
            have he : hgtI (wkSameSet (sameSet_symm hT) gd0) = hgtI gd0 :=
              hgt_wk _ _
            have h1 : h ≤ n := hb.1
            omega)
        else
          .there (escOfCutC s bs Qa done h
            (by
              simp only [seenMemR, if_pos hQ, if_neg hT] at hmem
              exact hmem) hb.2 gd0 hlt)
      else
        .there (escOfCutC s bs Qa done h
          (by
            simp only [seenMemR, if_neg hQ] at hmem
            exact hmem) hb.2 gd0 hlt)

/-! # Part 5 · The residual, verbatim (OPEN)

Part 3 crosses every binder whose hypothesis the context above re-supplies.
It does NOT cross the one binder whose hypothesis it does not: the
antecedent of a goal.

`LJF/OFuelPFam.lean`'s `TInvQ` proves a `p`-free implication goal by
`Inv.impR`, which puts the antecedent into `Ω`; the following `downL` /
`atomL` binds it into `K`.  That hypothesis is the antecedent of the goal
being PROVED, so nothing above holds it, and `bindBackI`'s premise
`↑↓M₀ ∈ K` is unavailable.  A cut site below such a binder — the same
parked `Qa ⊃ N ∈ done` re-attacked at a set-equal station, `interpR`'s ∃p
row then `⊤` (`parkRowER_cut`) and the ∀p row `⊥` (`parkRowAR_cut`) —
creates an escape whose derivation genuinely uses the bound hypothesis, and
there is no step that takes it above the binder.

This is stated, not proved: no term of the type below is built, and no
countermodel is claimed either.  It is the shape of §2 of
`docs/n4-pair-cofinality.md` — a step at which the escape must move and
has no clause. -/

/-- **The goal-antecedent binder crossing** (OPEN).  What the `∃p`
inversion traversal would need at `Inv.impR` followed by `Inv.downL`, where
the bound hypothesis is the goal's own antecedent and `escC_crossDown`'s
premise `↑↓M₀ ∈ K` is not available. -/
def EscBindGoalR (p : String) : Type :=
  ∀ (K : List Neg) (M₀ : Neg) (c : Nat) (seen : SeenR) (b : HeightBook seen),
    PFreeN p M₀ → PFreeCtx p K →
      EscC (M₀ :: K) (c + 4) seen b → EscC K c seen b

end LJFO

/-! ## Pins -/

#axioms_within LJFO.bindBackI []
#axioms_within LJFO.hgt_bindBackI [propext]
#axioms_within LJFO.subBindHead [propext]
#axioms_within LJFO.subDropMem [propext]
#axioms_within LJFO.escC_nil_empty []
#axioms_within LJFO.escC_zero []
#axioms_within LJFO.escD_of_escC0 []
#axioms_within LJFO.escC_mono [propext, Quot.sound]
#axioms_within LJFO.escC_crossDown [propext, Quot.sound]
#axioms_within LJFO.escC_crossAtom [propext]
#axioms_within LJFO.escC_crossMem [propext]
#axioms_within LJFO.hgt_keptSpan [propext]
#axioms_within LJFO.bb_keptSpan [propext, Quot.sound]
#axioms_within LJFO.escOfCutC [propext, Quot.sound]
