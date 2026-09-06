/-
Route (B), node **N4**, WP12d: **the repaired residual**.

`wip/ui_routeB_r_refute.lean` REFUTES `SatE2RD` (`wip/ui_routeB_r_escd.lean`)
by taking `Δ := []` with a record whose pair could only have been created at
a larger `Δ`.  The fault is that `SatE2RD` quantifies the record `seen` and
the `p`-free context `Δ` INDEPENDENTLY, and books a bare NUMBER per pair:
nothing in the statement says the recorded pair was ever recordable.

The repair is to book what a recording site actually holds — its guard
DERIVATION — instead of that derivation's height:

    GuardBook Δ []            = PUnit
    GuardBook Δ ((Q,T) :: s)  = Inv (T ++ Δ) [] .tru (↑Q) × GuardBook Δ s

An escape then beats the booked derivation rather than a booked number, and
the book's mere existence says the pair was recordable at this `Δ`.  The
counter-instance is excluded outright (`refute_blocked`): at `Δ = []` there
is no derivation of `done ⊢ ↑Qa`, so `GuardBook [] seen` is uninhabited and
the statement has nothing to say there.

The rest of the mechanism is unchanged and is re-proved here over the new
book: the empty record has no escape, the reduction to `SatE2R` / `SatA2R`
at `seen = []`, `PLL_UI` over the two repaired obligations, what a cut site
produces (`escWOfCut`), and the recording-site loop (`guardLoopW`), whose
restart is now literally "book the smaller derivation".

**What is still OPEN, and what is still in the way.**  `SatE2RW` and
`SatA2RW` are OPEN: no term of either type is built.  Repairing the
statement does NOT repair the induction — `wip/ui_routeB_r_bind.lean` and
`wip/ui_routeB_r_bindcell.lean` localise a separate difficulty, that the
escape has no step across the `p`-free binders of the inversion phase, and
that difficulty is untouched by anything here.

`LJF/` is untouched; this module is a leaf.
-/
import wip.ui_routeB_r_refute
import Meta.Audit

set_option autoImplicit false

namespace LJFO

variable {p : String}

/-! # Part 1 · The record with its guard derivations -/

/-- **What a recording site books**: for each recorded pair, the derivation
of its guard sequent that the site had in hand.  Its existence is the
statement that the pair was recordable at this `Δ`. -/
def GuardBook (Δ : List Neg) : SeenR → Type
  | [] => PUnit
  | (Q, T) :: s => Inv (T ++ Δ) [] .tru (.up Q) × GuardBook Δ s

/-- **A derivation-level escape against the booked derivations.** -/
inductive EscW (Δ : List Neg) : (seen : SeenR) → GuardBook Δ seen → Type where
  /-- an escape for the head pair: a strictly smaller derivation of its own
  guard sequent. -/
  | here {Q : Pos} {T : List Neg} {s : SeenR}
      {g : Inv (T ++ Δ) [] .tru (.up Q)} {bs : GuardBook Δ s}
      (gd : Inv (T ++ Δ) [] .tru (.up Q)) (hlt : hgtI gd < hgtI g) :
      EscW Δ ((Q, T) :: s) (g, bs)
  /-- an escape for an older pair, passed through. -/
  | there {Q : Pos} {T : List Neg} {s : SeenR}
      {g : Inv (T ++ Δ) [] .tru (.up Q)} {bs : GuardBook Δ s} :
      EscW Δ s bs → EscW Δ ((Q, T) :: s) (g, bs)

/-- **At the empty record there is no escape.** -/
theorem escW_nil_empty {Δ : List Neg} (e : EscW Δ [] PUnit.unit) : False :=
  nomatch e

/-- **The book invariant**, over the booked derivations. -/
def GuardBound (Δ : List Neg) :
    ∀ (seen : SeenR), GuardBook Δ seen → Nat → Prop
  | [], _, _ => True
  | (_, _) :: s, bk, h => h ≤ hgtI bk.1 ∧ GuardBound Δ s bk.2 h

theorem guardBound_nil {Δ : List Neg} {bk : GuardBook Δ []} {h : Nat} :
    GuardBound Δ [] bk h := trivial

theorem guardBound_mono {Δ : List Neg} :
    ∀ (seen : SeenR) (bk : GuardBook Δ seen) {h h' : Nat},
      h ≤ h' → GuardBound Δ seen bk h' → GuardBound Δ seen bk h
  | [], _, _, _, _, _ => trivial
  | (_, _) :: s, bk, _, _, hle, hb =>
      ⟨Nat.le_trans hle hb.1, guardBound_mono s bk.2 hle hb.2⟩

/-! # Part 2 · The counter-instance of `wip/ui_routeB_r_refute.lean` is
excluded

At `Δ = []` the record `[(Qa, done)]` has no book at all: booking it would
be a derivation of `done ⊢ ↑Qa`, and `escapeFails` refutes that sequent in a
one-world model.  So the repaired statement says nothing at the instance
that refutes `SatE2RD`. -/

/-- **The refutation is blocked.** -/
theorem refute_blocked (bk : GuardBook [] BindCell.seen) : False :=
  Refute.escapeFails bk.1

/-! # Part 3 · The two obligations, verbatim (OPEN) -/

/-- **The `∃p` traversal at a saturated station, with the record booked by
its guard derivations** (OPEN). -/
def SatE2RW (p : String) : Type :=
  ∀ (done Δ : List Neg) (ψ : Neg) (seen : SeenR) (bk : GuardBook Δ seen),
    Saturated done → ParkedCtxP done → PFreeCtx p Δ → PFreeN p ψ →
    ∀ {j : JD} (d : Inv (done ++ Δ) [] j ψ), GuardBound Δ seen bk (hgtI d) →
      Sum (UpFrom (fun e => Inv (interpR p e [] done none seen :: Δ) [] j ψ))
          (EscW Δ seen bk)

/-- **The `∀p` entry at a saturated station, the same way** (OPEN). -/
def SatA2RW (p : String) : Type :=
  ∀ (done Δ : List Neg) (G : Neg) (seen : SeenR) (bk : GuardBook Δ seen),
    Saturated done → ParkedCtxP done → PFreeCtx p Δ →
    ∀ {j : JD} (d : Inv (done ++ Δ) [] j G), GuardBound Δ seen bk (hgtI d) →
      Sum (UpFrom2 (fun e f => Inv (interpR p e [] done none seen :: Δ) [] .tru
             (interpR p f [] done (some (jGoal j G)) seen)))
          (EscW Δ seen bk)

/-! # Part 4 · The reduction

At `seen = []` the book is trivial and the escape branch is uninhabited, so
the two obligations give the residuals of §4.31 outright. -/

/-- **`SatE2R` from the repaired `∃p` traversal.** -/
noncomputable def satE2R_of_escW (t : SatE2RW p) : SatE2R p :=
  fun done Δ ψ hsat hP hΔ hψ {_j} d =>
    match t done Δ ψ [] PUnit.unit hsat hP hΔ hψ d guardBound_nil with
    | .inl w => w
    | .inr e => (escW_nil_empty e).elim

/-- **`SatA2R` from the repaired `∀p` entry.** -/
noncomputable def satA2R_of_escW (a : SatA2RW p) : SatA2R p :=
  fun done Δ G hsat hP hΔ {_j} d =>
    match a done Δ G [] PUnit.unit hsat hP hΔ d guardBound_nil with
    | .inl w => w
    | .inr e => (escW_nil_empty e).elim

/-- **`PLL_UI` over the two repaired obligations alone.** -/
noncomputable def pll_ui_R_escW (s2 : ∀ p, SatE2P p) (a2 : ∀ p, SatA2P p)
    (te : ∀ p, SatE2RW p) (ta : ∀ p, SatA2RW p) : PLL_UI :=
  pll_ui_R s2 a2 (fun p => satE2R_of_escW (te p)) (fun p => satA2R_of_escW (ta p))

/-! # Part 5 · Both ends of the mechanism, over the repaired book

`wip/ui_routeB_r_guard.lean`'s `escOfCut` and `guardLoop`, re-proved.  The
loop's restart is now literally "book the smaller derivation". -/

/-- **The escape a cut site creates.**  Unchanged in content: walk the record
to the pair the loop test fired on, move the derivation to the recorded
station by `wkSameSet`, and discharge the strict bound from the book
invariant. -/
def escWOfCut {Δ : List Neg} :
    ∀ (seen : SeenR) (bk : GuardBook Δ seen) (Qa : Pos) (done : List Neg)
      (h : Nat), seenMemR seen Qa done = true → GuardBound Δ seen bk h →
      ∀ (gd0 : Inv (done ++ Δ) [] .tru (.up Qa)), hgtI gd0 < h →
      EscW Δ seen bk
  | [], _, _, _, _, hmem, _, _, _ => absurd hmem (by simp [seenMemR])
  | (Q, T) :: s, (g, bs), Qa, done, h, hmem, hb, gd0, hlt =>
      if hQ : Q = Qa then
        if hT : sameSet T done = true then
          (by
            subst hQ
            refine .here (wkSameSet (sameSet_symm hT) gd0) ?_
            have he : hgtI (wkSameSet (sameSet_symm hT) gd0) = hgtI gd0 :=
              hgt_wk _ _
            have h1 : h ≤ hgtI g := hb.1
            omega)
        else
          .there (escWOfCut s bs Qa done h
            (by
              simp only [seenMemR, if_pos hQ, if_neg hT] at hmem
              exact hmem) hb.2 gd0 hlt)
      else
        .there (escWOfCut s bs Qa done h
          (by
            simp only [seenMemR, if_neg hQ] at hmem
            exact hmem) hb.2 gd0 hlt)

/-- **The `∀p` entry with the repaired escapes** (OPEN, no term built). -/
def UEntryRW (p : String) : Type :=
  ∀ (done : List Neg), Saturated done → ParkedCtxP done →
    ∀ {Γ' K : List Neg},
      (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
      ∀ (G : Neg) (seen : SeenR) (bk : GuardBook K seen) {j : JD}
      (d : Inv Γ' [] j G), GuardBound K seen bk (hgtI d) →
      Sum (UpFrom2 (fun e f => Inv (interpR p e [] done none seen :: K) [] .tru
             (interpR p f [] done (some (jGoal j G)) seen)))
          (EscW K seen bk)

/-- The entry reduces to the saturated-station statement. -/
def satA2RW_of_uentryRW (u : UEntryRW p) : SatA2RW p :=
  fun done Δ G seen bk hsat hP hΔ _ d hb =>
    u done hsat hP (fun Z hZ => List.mem_append.mp hZ)
      (fun Z hZ => List.mem_append_left _ hZ) hΔ G seen bk d hb

/-- **The recording-site loop, over the repaired book.**  The site books the
guard derivation it holds; an escape for the pair just recorded is a
strictly smaller derivation of the same sequent, and the site restarts with
it — booking THAT.  The recursion is well-founded on the booked
derivation's height, exactly as before. -/
def guardLoopW (u : UEntryRW p) (done : List Neg)
    (hsat : Saturated done) (hP : ParkedCtxP done) {K : List Neg}
    (hK : PFreeCtx p K) (Qa : Pos) (seen : SeenR) (bk : GuardBook K seen) :
    ∀ (s : Inv (done ++ K) [] .tru (.up Qa)), GuardBound K seen bk (hgtI s) →
      Sum (UpFrom2 (fun e f =>
             Inv (interpR p e [] done none ((Qa, done) :: seen) :: K) [] .tru
                 (interpR p f [] done (some (.up Qa)) ((Qa, done) :: seen))))
          (EscW K seen bk) := fun s hb =>
  match hu : u done hsat hP (fun Z hZ => List.mem_append.mp hZ)
              (fun Z hZ => List.mem_append_left _ hZ) hK (.up Qa)
              ((Qa, done) :: seen) (s, bk) (j := .tru) s
              ⟨Nat.le_refl _, hb⟩ with
  | .inl w => .inl (by rw [jGoal_tru] at w; exact w)
  | .inr (.here gd hlt) =>
      guardLoopW u done hsat hP hK Qa seen bk gd
        (guardBound_mono seen bk (Nat.le_of_lt hlt) hb)
  | .inr (.there e) => .inr e
  termination_by s _ => hgtI s
  decreasing_by exact hlt

/-! # Part 6 · Why the repair is not refutable the way `SatE2RD` was

The counter-instance of `wip/ui_routeB_r_refute.lean` worked because the
value branch failed while the escape branch was empty.  Under the repaired
book the two cannot both fail, and the reason is arithmetic.

For the value branch to fail, the derivation `d` must use a row the record
has cut — i.e. must left-focus a parked implication whose antecedent is
recorded — because the cut rows are the ONLY thing the record removes from
the interpolant.  Such a `d` contains a derivation of that pair's own guard
sequent, and it costs at least three units MORE than that derivation
(`hgt_fireCost`, `hgtL_ge`).  For the escape branch to be empty, the booked
derivation `g` must be minimal for the guard sequent.  Then

    hgtI d  ≥  (a guard derivation) + 3  ≥  hgtI g + 3  >  hgtI g

so `GuardBound Δ seen bk (hgtI d)` fails and the instance is not an instance.
Conversely, if `g` is far enough from minimal for `GuardBound` to hold, a
shorter derivation of the guard sequent exists and IS an escape.

This is an argument about instances, not a proof of `SatE2RW`.  What is
proved here is the arithmetic it turns on. -/

/-- **The cost of firing a parked implication**, exactly: the dispatch is its
antecedent's guard derivation plus its consequent chain. -/
theorem hgt_fireCost {Γ : List Neg} {j : JD} {Q : Pos} {N : Neg} {P : Pos}
    (h : Neg.imp Q N ∈ Γ) (s : Stab Γ .tru Q) (lf : LFoc Γ N j P) :
    hgtS (Stab.lfoc h (.impL s lf)) = hgtS s + hgtL lf := by
  simp only [hgtS, hgtL, szS, szL]; omega

/-- A consequent chain costs at least three. -/
theorem hgtL_ge {Γ : List Neg} {N : Neg} {j : JD} {P : Pos}
    (lf : LFoc Γ N j P) : 3 ≤ hgtL lf := by
  have := szL_pos lf; simp only [hgtL]; omega

/-- Every stable derivation spends a phase change and then a rule. -/
theorem szS_ge_two {Γ : List Neg} {j : JD} {P : Pos} :
    ∀ (s : Stab Γ j P), 2 ≤ szS s
  | .rfoc r => by have := szR_pos r; simp only [szS]; omega
  | .lfoc _ lf => by have := szL_pos lf; simp only [szS]; omega
  | .laxOf s => by have := szS_pos s; simp only [szS]; omega

theorem hgtS_ge {Γ : List Neg} {j : JD} {P : Pos} (s : Stab Γ j P) :
    3 ≤ hgtS s := by
  have := szS_ge_two s; simp only [hgtS]; omega

/-- **No derivation of a shift goal is shorter than three.**  So a booked
guard derivation of minimal height cannot be beaten by an escape that does
not exist. -/
theorem hgtI_up_ge {Γ : List Neg} {j : JD} {P : Pos}
    (d : Inv Γ [] j (.up P)) : 3 ≤ hgtI d := by
  cases d with
  | stable s =>
      have := szS_ge_two s
      simp only [hgtI, szI]
      omega

/-- **So a fire is at least three above its own guard derivation.**  This is
the inequality Part 6's argument turns on. -/
theorem hgt_fire_above_guard {Γ : List Neg} {j : JD} {Q : Pos} {N : Neg}
    {P : Pos} (h : Neg.imp Q N ∈ Γ) (s : Stab Γ .tru Q) (lf : LFoc Γ N j P) :
    hgtI (Inv.stable s) + 3 ≤ hgtI (Inv.stable (Stab.lfoc h (.impL s lf))) := by
  have h1 := hgt_fireCost h s lf
  have h2 := hgtL_ge lf
  simp only [hgtI, hgtS, szI] at *
  omega

end LJFO

/-! ## Pins -/

#axioms_within LJFO.escW_nil_empty []
#axioms_within LJFO.guardBound_nil []
#axioms_within LJFO.guardBound_mono []
#axioms_within LJFO.refute_blocked [propext, Quot.sound]
#axioms_within LJFO.satE2R_of_escW [propext]
#axioms_within LJFO.satA2R_of_escW [propext]
#axioms_within LJFO.pll_ui_R_escW [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.escWOfCut [propext, Quot.sound]
#axioms_within LJFO.satA2RW_of_uentryRW [propext]
#axioms_within LJFO.guardLoopW [propext]
#axioms_within LJFO.hgt_fireCost [propext, Quot.sound]
#axioms_within LJFO.hgtL_ge [propext, Quot.sound]
#axioms_within LJFO.szS_ge_two [propext, Quot.sound]
#axioms_within LJFO.hgtS_ge [propext, Quot.sound]
#axioms_within LJFO.hgtI_up_ge [propext, Quot.sound]
#axioms_within LJFO.hgt_fire_above_guard [propext, Quot.sound]
