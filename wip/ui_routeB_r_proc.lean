/-
Route (B), node **N4**, WP12c: **the processing phase of the cofinality
family, for the pair recursion, at EVERY record**.

`LJF/OFuelPMin.lean` Part 5's `eMinPP` / `aMinPP` transposed from `interpP`
to `interpR`, with the record carried.  Everything in the processing phase is
record-blind: `stepR` passes its record through unchanged at all sixteen
processing clauses and at the fire clause (`interpR = interpGR id`, so the
reset is the identity), and the record is touched at ONE place only, the
guard call of `parkRowER` / `parkRowAR` — which lives in the saturated phase.
So the transfer of cofinality from a station to its saturated reduct holds at
every record, with the record a spectator:

    eMinPRg : SatE2Rg p → ∀ todo done Δ ψ seen, ParkedCtxP done → … →
              Inv ((todo ++ done) ++ Δ) [] j ψ →
              UpFrom (fun e => Inv (interpR p e todo done none seen :: Δ) [] j ψ)
    aMinPRg : SatA2Rg p → … the two-fuel form

`SatE2Rg` / `SatA2Rg` are `SatE2R` / `SatA2R` (`wip/ui_routeB_r_ui.lean`) at
an arbitrary record; at `seen = []` they ARE those statements, so the
residuals of §4.31 follow from them by `satE2R_of_g` / `satA2R_of_g`.

This is the first block of the family for `interpR` and is neutral between
the two escape designs: with derivation-level escapes
(`wip/ui_routeB_r_escd.lean`) every clause below wraps in `Sum … (EscD Δ seen b)`
and passes escapes through unchanged, since no clause here touches the
record; `seqSum` (Part 1) is the one piece of plumbing that wrapping needs,
for the clause that inverts a disjunction into several branches.

`LJF/` is untouched; this module is a leaf.  `LJF.OFuelPMin` is imported, as
the existing leaves import it; the family modules are not.
-/
import wip.ui_routeB_r_escd
import Meta.Audit

set_option autoImplicit false

namespace LJFO

variable {p : String}

/-! # Part 1 · Sequencing escapes over the branches of an inversion

The one clause of the processing phase with several sub-results is the
inversion of a disjunctive hypothesis, which recurses once per branch of
`invertPos`.  Under a `Sum`-valued statement the branches must be sequenced:
all succeed, or one escapes.  Stated here for the branch type `List Neg`,
whose decidable equality lets the rebuilt function be defined without
eliminating a membership proof into `Type`. -/

/-- Sequence a family of escape-or-result values over a list of branches. -/
def seqSum {K : List Neg} {seen : SeenR} {b : HeightBook seen}
    {P : List Neg → Nat → Type} :
    ∀ (l : List (List Neg)),
      (∀ a ∈ l, Sum (UpFrom (P a)) (EscD K seen b)) →
      Sum (∀ a ∈ l, UpFrom (P a)) (EscD K seen b)
  | [], _ => .inl (fun _ ha => absurd ha List.not_mem_nil)
  | x :: l, h =>
      match h x (List.mem_cons_self ..) with
      | .inr e => .inr e
      | .inl w =>
          match seqSum l (fun a ha => h a (List.mem_cons_of_mem _ ha)) with
          | .inr e => .inr e
          | .inl g =>
              .inl (fun a ha =>
                if hax : a = x then hax ▸ w
                else g a ((List.mem_cons.mp ha).resolve_left hax))

/-! # Part 2 · The fire equation for `interpR` -/

/-- **The fire step, as one equation for every mode and every record.**  When
a parked `a ⊃ N'` fires, the interpolant at the station equals the
interpolant at the residual station one fuel down, at the same record. -/
theorem interpRFire_eq {f : Nat} {done : List Neg} {a : String}
    {N' : Neg} {rest : List Neg} {seen : SeenR}
    (hf : findFire done (splits done) = some (a, N', rest)) (g : Option Neg) :
    interpR p (f + 1) [] done g seen = interpR p f [N'] rest g seen :=
  srFire (rst := id) (p := p) (prev := interpR p f) hf g seen

/-- The `∃p` clause that inverts a disjunctive hypothesis, as an equation. -/
theorem interpR_orTodo_none {f : Nat} {P Q : Pos} {todo done : List Neg}
    {seen : SeenR} :
    interpR p (f + 1) (.up (.or P Q) :: todo) done none seen =
      nOrAll ((invertPos (.or P Q)).map
        (fun b => interpR p f (b ++ todo) done none seen)) := rfl

/-- The `∀p` clause that inverts a disjunctive hypothesis, as an equation. -/
theorem interpR_orTodo_some {f : Nat} {P Q : Pos} {todo done : List Neg}
    {G : Neg} {seen : SeenR} :
    interpR p (f + 1) (.up (.or P Q) :: todo) done (some G) seen =
      nAndAll ((invertPos (.or P Q)).map (fun b =>
        Neg.imp (.down (interpR p f (b ++ todo) done none seen))
                (interpR p f (b ++ todo) done (some G) seen))) := rfl

/-! # Part 3 · The saturated statements at an arbitrary record -/

/-- Cofinality at a saturated station, `∃p` side, at an ARBITRARY record. -/
def SatE2Rg (p : String) : Type :=
  ∀ (done Δ : List Neg) (ψ : Neg) (seen : SeenR), Saturated done →
    ParkedCtxP done → PFreeCtx p Δ → PFreeN p ψ →
    ∀ {j : JD}, Inv (done ++ Δ) [] j ψ →
      UpFrom (fun e => Inv (interpR p e [] done none seen :: Δ) [] j ψ)

/-- Cofinality at a saturated station, `∀p` side, at an ARBITRARY record. -/
def SatA2Rg (p : String) : Type :=
  ∀ (done Δ : List Neg) (G : Neg) (seen : SeenR), Saturated done →
    ParkedCtxP done → PFreeCtx p Δ →
    ∀ {j : JD}, Inv (done ++ Δ) [] j G →
      UpFrom2 (fun e f => Inv (interpR p e [] done none seen :: Δ) [] .tru
        (interpR p f [] done (some (jGoal j G)) seen))

/-- At the empty record `SatE2Rg` is the residual `SatE2R`. -/
def satE2R_of_g (s : SatE2Rg p) : SatE2R p :=
  fun done Δ ψ hsat hP hΔ hψ _ d => s done Δ ψ [] hsat hP hΔ hψ d

/-- At the empty record `SatA2Rg` is the residual `SatA2R`. -/
def satA2R_of_g (s : SatA2Rg p) : SatA2R p :=
  fun done Δ G hsat hP hΔ _ d => s done Δ G [] hsat hP hΔ d

/-! # Part 4 · The processing phase -/

/-- **Cofinality of `∃p` through the processing phase, at every record.**
Every station reduces to a saturated one; the record is a spectator. -/
def eMinPRg (sat : SatE2Rg p) :
    ∀ (todo done Δ : List Neg) (ψ : Neg) (seen : SeenR), ParkedCtxP done →
      PFreeCtx p Δ → PFreeN p ψ → ∀ {j : JD},
      Inv ((todo ++ done) ++ Δ) [] j ψ →
      UpFrom (fun e => Inv (interpR p e todo done none seen :: Δ) [] j ψ)
  | .up (.atom a) :: todo, done, Δ, ψ, seen, hP, hΔ, hψ, _, d =>
      let w := eMinPRg sat todo (.up (.atom a) :: done) Δ ψ seen
        (ParkedCtxP.cons (ParkedNP.atom a) hP) hΔ hψ (d.wk subParkOut)
      UpFrom.mk1 w.1 (fun e' he' => w.2 e' he')
  | .up .fls :: _, _, _, _, _, _, _, _, _, d =>
      UpFrom.mk1 0 (fun _ _ => nBotElimJ _ (List.mem_cons_self ..) d)
  | .up (.or P Q) :: todo, done, Δ, ψ, seen, hP, hΔ, hψ, _, d =>
      UpFrom.mk1
        (maxOver (fun (bh : {b // b ∈ invertPos (Pos.or P Q)}) =>
          match bh with
          | ⟨b', hb'⟩ =>
            (eMinPRg sat (b' ++ todo) done Δ ψ seen hP hΔ hψ
              ((invUp (d.wk subHeadOut) b' hb').wk subChainIn)).1)
          (invertPos (Pos.or P Q)).attach)
        (fun e' he' => by
        rw [interpR_orTodo_none]
        refine nOrAllElimJ _ (List.mem_cons_self ..) d ?_
        intro x hx Γ' hsub
        obtain ⟨b, hb, hEq⟩ := memMapWitness _ _ x hx
        subst hEq
        have hle := Nat.le_trans (le_maxOver (List.mem_attach _ ⟨b, hb⟩)) he'
        refine (((eMinPRg sat (b ++ todo) done Δ ψ seen hP hΔ hψ
          ((invUp (d.wk subHeadOut) b hb).wk subChainIn)).2 e' hle).wk ?_)
        intro Z hZ
        rcases List.mem_cons.mp hZ with rfl | hZ
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (hsub _ (List.mem_cons_of_mem _ hZ)))
  | .up (.down M) :: todo, done, Δ, ψ, seen, hP, hΔ, hψ, _, d =>
      let w := eMinPRg sat (M :: todo) done Δ ψ seen hP hΔ hψ
        (((invUp (d.wk subHeadOut) [M] (by simp [invertPos]))).wk subChainIn)
      UpFrom.mk1 w.1 (fun e' he' => w.2 e' he')
  | .and M N :: todo, done, Δ, ψ, seen, hP, hΔ, hψ, _, d =>
      let w := eMinPRg sat (M :: N :: todo) done Δ ψ seen hP hΔ hψ
        ((invAndHyp (d.wk subHeadOut)).wk (subChainIn (b := [M, N])))
      UpFrom.mk1 w.1 (fun e' he' => w.2 e' he')
  | .imp .fls _ :: todo, done, Δ, ψ, seen, hP, hΔ, hψ, _, d =>
      let w := eMinPRg sat todo done Δ ψ seen hP hΔ hψ (invImpFls (d.wk subHeadOut))
      UpFrom.mk1 w.1 (fun e' he' => w.2 e' he')
  | .imp (.atom a) N :: todo, done, Δ, ψ, seen, hP, hΔ, hψ, _, d =>
      let w := eMinPRg sat todo (.imp (.atom a) N :: done) Δ ψ seen
        (ParkedCtxP.cons (ParkedNP.qimp a N) hP) hΔ hψ (d.wk subParkOut)
      UpFrom.mk1 w.1 (fun e' he' => w.2 e' he')
  | .imp (.or Q₁ Q₂) N :: todo, done, Δ, ψ, seen, hP, hΔ, hψ, _, d =>
      let w := eMinPRg sat todo (.imp (.or Q₁ Q₂) N :: done) Δ ψ seen
        (ParkedCtxP.cons (ParkedNP.oimp Q₁ Q₂ N) hP) hΔ hψ (d.wk subParkOut)
      UpFrom.mk1 w.1 (fun e' he' => w.2 e' he')
  | .imp (.down (.up P')) N :: todo, done, Δ, ψ, seen, hP, hΔ, hψ, _, d =>
      let w := eMinPRg sat todo (.imp (.down (.up P')) N :: done) Δ ψ seen
        (ParkedCtxP.cons (ParkedNP.simp P' N) hP) hΔ hψ (d.wk subParkOut)
      UpFrom.mk1 w.1 (fun e' he' => w.2 e' he')
  | .imp (.down (.and M₁ M₂)) N :: todo, done, Δ, ψ, seen, hP, hΔ, hψ, _, d =>
      let w := eMinPRg sat todo (.imp (.down (.and M₁ M₂)) N :: done) Δ ψ seen
        (ParkedCtxP.cons (ParkedNP.aimp M₁ M₂ N) hP) hΔ hψ (d.wk subParkOut)
      UpFrom.mk1 w.1 (fun e' he' => w.2 e' he')
  | .imp (.down (.imp Q' N')) N :: todo, done, Δ, ψ, seen, hP, hΔ, hψ, _, d =>
      let w := eMinPRg sat todo (.imp (.down (.imp Q' N')) N :: done) Δ ψ seen
        (ParkedCtxP.cons (ParkedNP.dyk Q' N' N) hP) hΔ hψ (d.wk subParkOut)
      UpFrom.mk1 w.1 (fun e' he' => w.2 e' he')
  | .circ Q :: todo, done, Δ, ψ, seen, hP, hΔ, hψ, _, d =>
      let w := eMinPRg sat todo (.circ Q :: done) Δ ψ seen
        (ParkedCtxP.cons (ParkedNP.box Q) hP) hΔ hψ (d.wk subParkOut)
      UpFrom.mk1 w.1 (fun e' he' => w.2 e' he')
  | .imp (.down (.circ Q')) N :: todo, done, Δ, ψ, seen, hP, hΔ, hψ, _, d =>
      let w := eMinPRg sat todo (.imp (.down (.circ Q')) N :: done) Δ ψ seen
        (ParkedCtxP.cons (ParkedNP.cimp Q' N) hP) hΔ hψ (d.wk subParkOut)
      UpFrom.mk1 w.1 (fun e' he' => w.2 e' he')
  | [], done, Δ, ψ, seen, hP, hΔ, hψ, _, d =>
      match hf : findFire done (splits done) with
      | some (_, N, rest) =>
          let w := eMinPRg sat [N] rest Δ ψ seen
            (ParkedCtxP.sub (splits_sub (findFire_mem hf)) hP) hΔ hψ
            (invFireHyp (findFire_mem hf) d)
          UpFrom.mk1 w.1 (fun e' he' => by
            rw [interpRFire_eq hf none]; exact w.2 e' he')
      | none => sat done Δ ψ seen hf hP hΔ hψ d
  termination_by todo done Δ ψ seen hP hΔ hψ j d => 2 * sum3 todo + sum3 done
  -- NOT `ljf_dec_e`: this module sees BOTH `LJF/OCore.lean`'s macro and
  -- `LJF/Base.lean`'s, and the token is ambiguous (`wip/ui_routeB_wp4.lean`,
  -- `stabP`).  The alternatives actually needed, spelled out.
  decreasing_by
    all_goals simp_wf
    all_goals try simp only [sum3, sum3_append, wNeg, wPos]
    all_goals
      first
        | exact dec_park
        | exact dec_drop
        | exact dec_shift1
        | exact dec_and
        | (have h1 := invertPos_lt (P := Pos.or _ _)
             (by intro a h; nomatch h) _ (by assumption)
           simp only [wPos] at h1; omega)
        | exact Nat.lt_of_lt_of_le (dec_fire (by assumption)) (by omega)
        | omega

/-- **Cofinality of `∀p` through the processing phase, at every record.** -/
def aMinPRg (sat : SatA2Rg p) :
    ∀ (todo done Δ : List Neg) (G : Neg) (seen : SeenR), ParkedCtxP done →
      PFreeCtx p Δ → ∀ {j : JD},
      Inv ((todo ++ done) ++ Δ) [] j G →
      UpFrom2 (fun e f => Inv (interpR p e todo done none seen :: Δ) [] .tru
        (interpR p f todo done (some (jGoal j G)) seen))
  | .up (.atom a) :: todo, done, Δ, G, seen, hP, hΔ, _, d =>
      let w := aMinPRg sat todo (.up (.atom a) :: done) Δ G seen
        (ParkedCtxP.cons (ParkedNP.atom a) hP) hΔ (d.wk subParkOut)
      UpFrom2.mk1 w.1 (fun e' f' he' hf' => w.2 e' f' he' hf')
  | .up .fls :: _, _, _, _, _, _, _, _, _ =>
      UpFrom2.mk1 0 (fun _ _ _ _ => nBotElim _ (List.mem_cons_self ..))
  | .up (.or P Q) :: todo, done, Δ, G, seen, hP, hΔ, _, d =>
      UpFrom2.mk1
        (maxOver (fun (bh : {b // b ∈ invertPos (Pos.or P Q)}) =>
          match bh with
          | ⟨b', hb'⟩ =>
            (aMinPRg sat (b' ++ todo) done Δ G seen hP hΔ
              ((invUp (d.wk subHeadOut) b' hb').wk subChainIn)).1)
          (invertPos (Pos.or P Q)).attach)
        (fun e' f' he' hf' => by
        rw [interpR_orTodo_some]
        refine nAndAllIntro ?_
        intro x hx
        obtain ⟨b, hb, hEq⟩ := memMapWitness _ _ x hx
        subst hEq
        refine .impR (.downL ?_)
        have hlf := Nat.le_trans (le_maxOver (List.mem_attach _ ⟨b, hb⟩)) hf'
        refine (((aMinPRg sat (b ++ todo) done Δ G seen hP hΔ
          ((invUp (d.wk subHeadOut) b hb).wk subChainIn)).2 f' f' hlf hlf).wk ?_)
        intro Z hZ
        rcases List.mem_cons.mp hZ with rfl | hZ
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ))
  | .up (.down M) :: todo, done, Δ, G, seen, hP, hΔ, _, d =>
      let w := aMinPRg sat (M :: todo) done Δ G seen hP hΔ
        (((invUp (d.wk subHeadOut) [M] (by simp [invertPos]))).wk subChainIn)
      UpFrom2.mk1 w.1 (fun e' f' he' hf' => w.2 e' f' he' hf')
  | .and M N :: todo, done, Δ, G, seen, hP, hΔ, _, d =>
      let w := aMinPRg sat (M :: N :: todo) done Δ G seen hP hΔ
        ((invAndHyp (d.wk subHeadOut)).wk (subChainIn (b := [M, N])))
      UpFrom2.mk1 w.1 (fun e' f' he' hf' => w.2 e' f' he' hf')
  | .imp .fls _ :: todo, done, Δ, G, seen, hP, hΔ, _, d =>
      let w := aMinPRg sat todo done Δ G seen hP hΔ (invImpFls (d.wk subHeadOut))
      UpFrom2.mk1 w.1 (fun e' f' he' hf' => w.2 e' f' he' hf')
  | .imp (.atom a) N :: todo, done, Δ, G, seen, hP, hΔ, _, d =>
      let w := aMinPRg sat todo (.imp (.atom a) N :: done) Δ G seen
        (ParkedCtxP.cons (ParkedNP.qimp a N) hP) hΔ (d.wk subParkOut)
      UpFrom2.mk1 w.1 (fun e' f' he' hf' => w.2 e' f' he' hf')
  | .imp (.or Q₁ Q₂) N :: todo, done, Δ, G, seen, hP, hΔ, _, d =>
      let w := aMinPRg sat todo (.imp (.or Q₁ Q₂) N :: done) Δ G seen
        (ParkedCtxP.cons (ParkedNP.oimp Q₁ Q₂ N) hP) hΔ (d.wk subParkOut)
      UpFrom2.mk1 w.1 (fun e' f' he' hf' => w.2 e' f' he' hf')
  | .imp (.down (.up P')) N :: todo, done, Δ, G, seen, hP, hΔ, _, d =>
      let w := aMinPRg sat todo (.imp (.down (.up P')) N :: done) Δ G seen
        (ParkedCtxP.cons (ParkedNP.simp P' N) hP) hΔ (d.wk subParkOut)
      UpFrom2.mk1 w.1 (fun e' f' he' hf' => w.2 e' f' he' hf')
  | .imp (.down (.and M₁ M₂)) N :: todo, done, Δ, G, seen, hP, hΔ, _, d =>
      let w := aMinPRg sat todo (.imp (.down (.and M₁ M₂)) N :: done) Δ G seen
        (ParkedCtxP.cons (ParkedNP.aimp M₁ M₂ N) hP) hΔ (d.wk subParkOut)
      UpFrom2.mk1 w.1 (fun e' f' he' hf' => w.2 e' f' he' hf')
  | .imp (.down (.imp Q' N')) N :: todo, done, Δ, G, seen, hP, hΔ, _, d =>
      let w := aMinPRg sat todo (.imp (.down (.imp Q' N')) N :: done) Δ G seen
        (ParkedCtxP.cons (ParkedNP.dyk Q' N' N) hP) hΔ (d.wk subParkOut)
      UpFrom2.mk1 w.1 (fun e' f' he' hf' => w.2 e' f' he' hf')
  | .circ Q :: todo, done, Δ, G, seen, hP, hΔ, _, d =>
      let w := aMinPRg sat todo (.circ Q :: done) Δ G seen
        (ParkedCtxP.cons (ParkedNP.box Q) hP) hΔ (d.wk subParkOut)
      UpFrom2.mk1 w.1 (fun e' f' he' hf' => w.2 e' f' he' hf')
  | .imp (.down (.circ Q')) N :: todo, done, Δ, G, seen, hP, hΔ, _, d =>
      let w := aMinPRg sat todo (.imp (.down (.circ Q')) N :: done) Δ G seen
        (ParkedCtxP.cons (ParkedNP.cimp Q' N) hP) hΔ (d.wk subParkOut)
      UpFrom2.mk1 w.1 (fun e' f' he' hf' => w.2 e' f' he' hf')
  | [], done, Δ, G, seen, hP, hΔ, j, d =>
      match hf : findFire done (splits done) with
      | some (_, N', rest) =>
          let w := aMinPRg sat [N'] rest Δ G seen
            (ParkedCtxP.sub (splits_sub (findFire_mem hf)) hP) hΔ
            (invFireHyp (findFire_mem hf) d)
          UpFrom2.mk1 w.1 (fun e' f' he' hf' => by
            rw [interpRFire_eq hf none, interpRFire_eq hf (some (jGoal j G))]
            exact w.2 e' f' he' hf')
      | none => sat done Δ G seen hf hP hΔ d
  termination_by todo done Δ G seen hP hΔ j d => 2 * sum3 todo + sum3 done
  decreasing_by
    all_goals simp_wf
    all_goals try simp only [sum3, sum3_append, wNeg, wPos]
    all_goals
      first
        | exact dec_park
        | exact dec_drop
        | exact dec_shift1
        | exact dec_and
        | (have h1 := invertPos_lt (P := Pos.or _ _)
             (by intro a h; nomatch h) _ (by assumption)
           simp only [wPos] at h1; omega)
        | exact Nat.lt_of_lt_of_le (dec_fire (by assumption)) (by omega)
        | omega

end LJFO

/-! ## Pins -/

#axioms_within LJFO.seqSum [propext]
#axioms_within LJFO.interpRFire_eq [propext]
#axioms_within LJFO.interpR_orTodo_none [propext]
#axioms_within LJFO.interpR_orTodo_some [propext]
#axioms_within LJFO.satE2R_of_g [propext]
#axioms_within LJFO.satA2R_of_g [propext]
#axioms_within LJFO.eMinPRg [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.aMinPRg [propext, Classical.choice, Quot.sound]
