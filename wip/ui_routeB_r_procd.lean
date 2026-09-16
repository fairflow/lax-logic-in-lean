/-
Route (B), node **N4**, WP12c: **the processing phase of the family for
`interpR`, carrying DERIVATION-LEVEL escapes**.

`wip/ui_routeB_r_proc.lean` proves the processing phase over the escape-free
statements at an arbitrary record.  This is the same block over the
`Sum`-valued statements of `wip/ui_routeB_r_escd.lean`, i.e. the block as the
final family will contain it:

    eMinPRD : SatE2RD p → ∀ todo done Δ ψ seen b, … →
              Inv ((todo ++ done) ++ Δ) [] j ψ →
              Sum (UpFrom (fun e => Inv (interpR p e todo done none seen :: Δ) [] j ψ))
                  (EscD Δ seen b)
    aMinPRD : SatA2RD p → … the two-fuel form

Every clause is `wip/ui_routeB_r_proc.lean`'s with the escape passed straight
through: the processing phase never touches the record, so an escape arising
below is an escape here, with the same record, the same height book and the
same `p`-free context.  The only clause needing plumbing is the inversion of
a disjunctive hypothesis, which has one sub-result per branch of `invertPos`
and must therefore SEQUENCE them: all succeed, or one escapes (`seqSumG`).

`LJF/` is untouched; this module is a leaf.
-/
import wip.ui_routeB_r_proc
import Meta.Audit

set_option autoImplicit false

namespace LJFO

variable {p : String}

/-! # Part 1 · Sequencing over the branches of an inversion

`seqSum` (`wip/ui_routeB_r_proc.lean`) at an arbitrary family. -/

/-- Sequence a family of escape-or-result values over a list of branches: all
succeed, or one escapes. -/
def seqSumG {K : List Neg} {seen : SeenR} {b : HeightBook seen}
    {F : List Neg → Type} :
    ∀ (l : List (List Neg)),
      (∀ a ∈ l, Sum (F a) (EscD K seen b)) →
      Sum (∀ a ∈ l, F a) (EscD K seen b)
  | [], _ => .inl (fun _ ha => absurd ha List.not_mem_nil)
  | x :: l, h =>
      match h x (List.mem_cons_self ..) with
      | .inr e => .inr e
      | .inl w =>
          match seqSumG l (fun a ha => h a (List.mem_cons_of_mem _ ha)) with
          | .inr e => .inr e
          | .inl g =>
              .inl (fun a ha =>
                if hax : a = x then hax ▸ w
                else g a ((List.mem_cons.mp ha).resolve_left hax))

/-! ## The book invariant along a processing edge

Every processing edge is a parking weakening (height EXACT) or one of the
transformers (height NON-INCREASING), `LJF/OFuelHeight.lean` Part 10, so the
book invariant descends with the derivation. -/

/-- A parking weakening keeps the height exactly. -/
theorem bb_park {seen : SeenR} {b : HeightBook seen} {Γ Γ' : List Neg}
    {Ω : List Pos} {j : JD} {C : Neg} (H : Sub Γ Γ') (d : Inv Γ Ω j C)
    (hb : BookBound seen b (hgtI d)) : BookBound seen b (hgtI (Inv.wk H d)) := by
  rw [hgt_wk]; exact hb

/-- Inverting a non-atomic positive hypothesis does not raise the height. -/
theorem bb_orBranch {seen : SeenR} {b : HeightBook seen} {R : Pos}
    {Γ Γ₁ Γ₂ : List Neg} {j : JD} {C : Neg}
    {H₀ : Sub Γ (Neg.up R :: Γ₁)} {bl : List Neg} {hbl : bl ∈ invertPos R}
    {H₁ : Sub (bl ++ Γ₁) Γ₂}
    (d : Inv Γ [] j C) (hb : BookBound seen b (hgtI d))
    (hR : ∀ a : String, R ≠ .atom a := by intro a h; nomatch h) :
    BookBound seen b (hgtI (Inv.wk H₁ (invUp (Inv.wk H₀ d) bl hbl))) := by
  refine bookBound_mono _ _ ?_ hb
  rw [hgt_wk]
  exact Nat.le_trans (hgt_invUp hR _ _ _) (Nat.le_of_eq (hgt_wk _ _))

/-- Inverting a conjunctive hypothesis does not raise the height. -/
theorem bb_andHyp {seen : SeenR} {b : HeightBook seen} {M N : Neg}
    {Γ Γ₁ Γ₂ : List Neg} {j : JD} {C : Neg}
    {H₀ : Sub Γ (Neg.and M N :: Γ₁)} {H₁ : Sub (M :: N :: Γ₁) Γ₂}
    (d : Inv Γ [] j C) (hb : BookBound seen b (hgtI d)) :
    BookBound seen b (hgtI (Inv.wk H₁ (invAndHyp (Inv.wk H₀ d)))) := by
  refine bookBound_mono _ _ ?_ hb
  rw [hgt_wk]
  exact Nat.le_trans (hgt_invAndHyp _) (Nat.le_of_eq (hgt_wk _ _))

/-- Dropping a `⊥ ⊃ N` hypothesis does not raise the height. -/
theorem bb_impFls {seen : SeenR} {b : HeightBook seen} {N : Neg}
    {Γ Γ₁ : List Neg} {j : JD} {C : Neg}
    {H₀ : Sub Γ (Neg.imp .fls N :: Γ₁)}
    (d : Inv Γ [] j C) (hb : BookBound seen b (hgtI d)) :
    BookBound seen b (hgtI (invImpFls (Inv.wk H₀ d))) := by
  refine bookBound_mono _ _ ?_ hb
  exact Nat.le_trans (hgt_invImpFls _) (Nat.le_of_eq (hgt_wk _ _))

/-- Firing a parked `a ⊃ N` does not raise the height. -/
theorem bb_fire {seen : SeenR} {b : HeightBook seen} {a : String} {N : Neg}
    {done rest Δext : List Neg} {j : JD} {C : Neg}
    (h : (Neg.imp (.atom a) N, rest) ∈ splits done)
    (d : Inv (done ++ Δext) [] j C) (hb : BookBound seen b (hgtI d)) :
    BookBound seen b (hgtI (invFireHyp h d)) :=
  bookBound_mono _ _ (hgt_invFireHyp h d) hb

/-! # Part 2 · The processing phase with escapes -/

/-- **Cofinality of `∃p` through the processing phase, with escapes.**  Every
station reduces to a saturated one; the record, the height book and any
escape are spectators. -/
def eMinPRD (sat : SatE2RD p) :
    ∀ (todo done Δ : List Neg) (ψ : Neg) (seen : SeenR) (b : HeightBook seen),
      ParkedCtxP done → PFreeCtx p Δ → PFreeN p ψ → ∀ {j : JD}
      (d : Inv ((todo ++ done) ++ Δ) [] j ψ), BookBound seen b (hgtI d) →
      Sum (UpFrom (fun e => Inv (interpR p e todo done none seen :: Δ) [] j ψ))
          (EscD Δ seen b)
  | .up (.atom a) :: todo, done, Δ, ψ, seen, b, hP, hΔ, hψ, _, d, hb =>
      match eMinPRD sat todo (.up (.atom a) :: done) Δ ψ seen b
        (ParkedCtxP.cons (ParkedNP.atom a) hP) hΔ hψ (d.wk subParkOut) (bb_park subParkOut d hb) with
      | .inr esc => .inr esc
      | .inl w => .inl (UpFrom.mk1 w.1 (fun e' he' => w.2 e' he'))
  | .up .fls :: _, _, _, _, _, _, _, _, _, _, d, _ =>
      .inl (UpFrom.mk1 0 (fun _ _ => nBotElimJ _ (List.mem_cons_self ..) d))
  | .up (.or P Q) :: todo, done, Δ, ψ, seen, b, hP, hΔ, hψ, j, d, hb =>
      match seqSumG (K := Δ) (seen := seen) (b := b)
              (F := fun b' => UpFrom (fun e =>
                 Inv (interpR p e (b' ++ todo) done none seen :: Δ) [] j ψ))
              (invertPos (Pos.or P Q))
              (fun b' hb' => eMinPRD sat (b' ++ todo) done Δ ψ seen b hP hΔ hψ
                 ((invUp (d.wk subHeadOut) b' hb').wk subChainIn) (bb_orBranch d hb)) with
      | .inr esc => .inr esc
      | .inl g =>
          .inl (UpFrom.mk1
            (maxOver (fun (bh : {b' // b' ∈ invertPos (Pos.or P Q)}) => (g bh.1 bh.2).1)
              (invertPos (Pos.or P Q)).attach)
            (fun e' he' => by
              rw [interpR_orTodo_none]
              refine nOrAllElimJ _ (List.mem_cons_self ..) d ?_
              intro x hx Γ' hsub
              obtain ⟨b', hb', hEq⟩ := memMapWitness _ _ x hx
              subst hEq
              have hle := Nat.le_trans (le_maxOver (List.mem_attach _ ⟨b', hb'⟩)) he'
              refine (((g b' hb').2 e' hle).wk ?_)
              intro Z hZ
              rcases List.mem_cons.mp hZ with rfl | hZ
              · exact List.mem_cons_self ..
              · exact List.mem_cons_of_mem _ (hsub _ (List.mem_cons_of_mem _ hZ))))
  | .up (.down M) :: todo, done, Δ, ψ, seen, b, hP, hΔ, hψ, _, d, hb =>
      match eMinPRD sat (M :: todo) done Δ ψ seen b hP hΔ hψ
        (((invUp (d.wk subHeadOut) [M] (by simp [invertPos]))).wk subChainIn) (bb_orBranch d hb) with
      | .inr esc => .inr esc
      | .inl w => .inl (UpFrom.mk1 w.1 (fun e' he' => w.2 e' he'))
  | .and M N :: todo, done, Δ, ψ, seen, b, hP, hΔ, hψ, _, d, hb =>
      match eMinPRD sat (M :: N :: todo) done Δ ψ seen b hP hΔ hψ
        ((invAndHyp (d.wk subHeadOut)).wk (subChainIn (b := [M, N]))) (bb_andHyp d hb) with
      | .inr esc => .inr esc
      | .inl w => .inl (UpFrom.mk1 w.1 (fun e' he' => w.2 e' he'))
  | .imp .fls _ :: todo, done, Δ, ψ, seen, b, hP, hΔ, hψ, _, d, hb =>
      match eMinPRD sat todo done Δ ψ seen b hP hΔ hψ
        (invImpFls (d.wk subHeadOut)) (bb_impFls d hb) with
      | .inr esc => .inr esc
      | .inl w => .inl (UpFrom.mk1 w.1 (fun e' he' => w.2 e' he'))
  | .imp (.atom a) N :: todo, done, Δ, ψ, seen, b, hP, hΔ, hψ, _, d, hb =>
      match eMinPRD sat todo (.imp (.atom a) N :: done) Δ ψ seen b
        (ParkedCtxP.cons (ParkedNP.qimp a N) hP) hΔ hψ (d.wk subParkOut) (bb_park subParkOut d hb) with
      | .inr esc => .inr esc
      | .inl w => .inl (UpFrom.mk1 w.1 (fun e' he' => w.2 e' he'))
  | .imp (.or Q₁ Q₂) N :: todo, done, Δ, ψ, seen, b, hP, hΔ, hψ, _, d, hb =>
      match eMinPRD sat todo (.imp (.or Q₁ Q₂) N :: done) Δ ψ seen b
        (ParkedCtxP.cons (ParkedNP.oimp Q₁ Q₂ N) hP) hΔ hψ (d.wk subParkOut) (bb_park subParkOut d hb) with
      | .inr esc => .inr esc
      | .inl w => .inl (UpFrom.mk1 w.1 (fun e' he' => w.2 e' he'))
  | .imp (.down (.up P')) N :: todo, done, Δ, ψ, seen, b, hP, hΔ, hψ, _, d, hb =>
      match eMinPRD sat todo (.imp (.down (.up P')) N :: done) Δ ψ seen b
        (ParkedCtxP.cons (ParkedNP.simp P' N) hP) hΔ hψ (d.wk subParkOut) (bb_park subParkOut d hb) with
      | .inr esc => .inr esc
      | .inl w => .inl (UpFrom.mk1 w.1 (fun e' he' => w.2 e' he'))
  | .imp (.down (.and M₁ M₂)) N :: todo, done, Δ, ψ, seen, b, hP, hΔ, hψ, _, d, hb =>
      match eMinPRD sat todo (.imp (.down (.and M₁ M₂)) N :: done) Δ ψ seen b
        (ParkedCtxP.cons (ParkedNP.aimp M₁ M₂ N) hP) hΔ hψ (d.wk subParkOut) (bb_park subParkOut d hb) with
      | .inr esc => .inr esc
      | .inl w => .inl (UpFrom.mk1 w.1 (fun e' he' => w.2 e' he'))
  | .imp (.down (.imp Q' N')) N :: todo, done, Δ, ψ, seen, b, hP, hΔ, hψ, _, d, hb =>
      match eMinPRD sat todo (.imp (.down (.imp Q' N')) N :: done) Δ ψ seen b
        (ParkedCtxP.cons (ParkedNP.dyk Q' N' N) hP) hΔ hψ (d.wk subParkOut) (bb_park subParkOut d hb) with
      | .inr esc => .inr esc
      | .inl w => .inl (UpFrom.mk1 w.1 (fun e' he' => w.2 e' he'))
  | .circ Q :: todo, done, Δ, ψ, seen, b, hP, hΔ, hψ, _, d, hb =>
      match eMinPRD sat todo (.circ Q :: done) Δ ψ seen b
        (ParkedCtxP.cons (ParkedNP.box Q) hP) hΔ hψ (d.wk subParkOut) (bb_park subParkOut d hb) with
      | .inr esc => .inr esc
      | .inl w => .inl (UpFrom.mk1 w.1 (fun e' he' => w.2 e' he'))
  | .imp (.down (.circ Q')) N :: todo, done, Δ, ψ, seen, b, hP, hΔ, hψ, _, d, hb =>
      match eMinPRD sat todo (.imp (.down (.circ Q')) N :: done) Δ ψ seen b
        (ParkedCtxP.cons (ParkedNP.cimp Q' N) hP) hΔ hψ (d.wk subParkOut) (bb_park subParkOut d hb) with
      | .inr esc => .inr esc
      | .inl w => .inl (UpFrom.mk1 w.1 (fun e' he' => w.2 e' he'))
  | [], done, Δ, ψ, seen, b, hP, hΔ, hψ, _, d, hb =>
      match hf : findFire done (splits done) with
      | some (_, N, rest) =>
          match eMinPRD sat [N] rest Δ ψ seen b
            (ParkedCtxP.sub (splits_sub (findFire_mem hf)) hP) hΔ hψ
            (invFireHyp (findFire_mem hf) d) (bb_fire (findFire_mem hf) d hb) with
          | .inr esc => .inr esc
          | .inl w =>
              .inl (UpFrom.mk1 w.1 (fun e' he' => by
                rw [interpRFire_eq hf none]; exact w.2 e' he'))
      | none => sat done Δ ψ seen b hf hP hΔ hψ d hb
  termination_by todo done Δ ψ seen b hP hΔ hψ j d => 2 * sum3 todo + sum3 done
  -- NOT `ljf_dec_e`: the token is ambiguous in a leaf that sees both
  -- `LJF/OCore.lean`'s macro and `LJF/Base.lean`'s (`stabP`,
  -- `wip/ui_routeB_wp4.lean`).
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

/-- **Cofinality of `∀p` through the processing phase, with escapes.** -/
def aMinPRD (sat : SatA2RD p) :
    ∀ (todo done Δ : List Neg) (G : Neg) (seen : SeenR) (b : HeightBook seen),
      ParkedCtxP done → PFreeCtx p Δ → ∀ {j : JD}
      (d : Inv ((todo ++ done) ++ Δ) [] j G), BookBound seen b (hgtI d) →
      Sum (UpFrom2 (fun e f => Inv (interpR p e todo done none seen :: Δ) [] .tru
             (interpR p f todo done (some (jGoal j G)) seen)))
          (EscD Δ seen b)
  | .up (.atom a) :: todo, done, Δ, G, seen, b, hP, hΔ, _, d, hb =>
      match aMinPRD sat todo (.up (.atom a) :: done) Δ G seen b
        (ParkedCtxP.cons (ParkedNP.atom a) hP) hΔ (d.wk subParkOut) (bb_park subParkOut d hb) with
      | .inr esc => .inr esc
      | .inl w => .inl (UpFrom2.mk1 w.1 (fun e' f' he' hf' => w.2 e' f' he' hf'))
  | .up .fls :: _, _, _, _, _, _, _, _, _, _, _ =>
      .inl (UpFrom2.mk1 0 (fun _ _ _ _ => nBotElim _ (List.mem_cons_self ..)))
  | .up (.or P Q) :: todo, done, Δ, G, seen, b, hP, hΔ, j, d, hb =>
      match seqSumG (K := Δ) (seen := seen) (b := b)
              (F := fun b' => UpFrom2 (fun e f =>
                 Inv (interpR p e (b' ++ todo) done none seen :: Δ) [] .tru
                     (interpR p f (b' ++ todo) done (some (jGoal j G)) seen)))
              (invertPos (Pos.or P Q))
              (fun b' hb' => aMinPRD sat (b' ++ todo) done Δ G seen b hP hΔ
                 ((invUp (d.wk subHeadOut) b' hb').wk subChainIn) (bb_orBranch d hb)) with
      | .inr esc => .inr esc
      | .inl g =>
          .inl (UpFrom2.mk1
            (maxOver (fun (bh : {b' // b' ∈ invertPos (Pos.or P Q)}) => (g bh.1 bh.2).1)
              (invertPos (Pos.or P Q)).attach)
            (fun e' f' he' hf' => by
              rw [interpR_orTodo_some]
              refine nAndAllIntro ?_
              intro x hx
              obtain ⟨b', hb', hEq⟩ := memMapWitness _ _ x hx
              subst hEq
              refine .impR (.downL ?_)
              have hlf := Nat.le_trans (le_maxOver (List.mem_attach _ ⟨b', hb'⟩)) hf'
              refine (((g b' hb').2 f' f' hlf hlf).wk ?_)
              intro Z hZ
              rcases List.mem_cons.mp hZ with rfl | hZ
              · exact List.mem_cons_self ..
              · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ)))
  | .up (.down M) :: todo, done, Δ, G, seen, b, hP, hΔ, _, d, hb =>
      match aMinPRD sat (M :: todo) done Δ G seen b hP hΔ
        (((invUp (d.wk subHeadOut) [M] (by simp [invertPos]))).wk subChainIn) (bb_orBranch d hb) with
      | .inr esc => .inr esc
      | .inl w => .inl (UpFrom2.mk1 w.1 (fun e' f' he' hf' => w.2 e' f' he' hf'))
  | .and M N :: todo, done, Δ, G, seen, b, hP, hΔ, _, d, hb =>
      match aMinPRD sat (M :: N :: todo) done Δ G seen b hP hΔ
        ((invAndHyp (d.wk subHeadOut)).wk (subChainIn (b := [M, N]))) (bb_andHyp d hb) with
      | .inr esc => .inr esc
      | .inl w => .inl (UpFrom2.mk1 w.1 (fun e' f' he' hf' => w.2 e' f' he' hf'))
  | .imp .fls _ :: todo, done, Δ, G, seen, b, hP, hΔ, _, d, hb =>
      match aMinPRD sat todo done Δ G seen b hP hΔ (invImpFls (d.wk subHeadOut)) (bb_impFls d hb) with
      | .inr esc => .inr esc
      | .inl w => .inl (UpFrom2.mk1 w.1 (fun e' f' he' hf' => w.2 e' f' he' hf'))
  | .imp (.atom a) N :: todo, done, Δ, G, seen, b, hP, hΔ, _, d, hb =>
      match aMinPRD sat todo (.imp (.atom a) N :: done) Δ G seen b
        (ParkedCtxP.cons (ParkedNP.qimp a N) hP) hΔ (d.wk subParkOut) (bb_park subParkOut d hb) with
      | .inr esc => .inr esc
      | .inl w => .inl (UpFrom2.mk1 w.1 (fun e' f' he' hf' => w.2 e' f' he' hf'))
  | .imp (.or Q₁ Q₂) N :: todo, done, Δ, G, seen, b, hP, hΔ, _, d, hb =>
      match aMinPRD sat todo (.imp (.or Q₁ Q₂) N :: done) Δ G seen b
        (ParkedCtxP.cons (ParkedNP.oimp Q₁ Q₂ N) hP) hΔ (d.wk subParkOut) (bb_park subParkOut d hb) with
      | .inr esc => .inr esc
      | .inl w => .inl (UpFrom2.mk1 w.1 (fun e' f' he' hf' => w.2 e' f' he' hf'))
  | .imp (.down (.up P')) N :: todo, done, Δ, G, seen, b, hP, hΔ, _, d, hb =>
      match aMinPRD sat todo (.imp (.down (.up P')) N :: done) Δ G seen b
        (ParkedCtxP.cons (ParkedNP.simp P' N) hP) hΔ (d.wk subParkOut) (bb_park subParkOut d hb) with
      | .inr esc => .inr esc
      | .inl w => .inl (UpFrom2.mk1 w.1 (fun e' f' he' hf' => w.2 e' f' he' hf'))
  | .imp (.down (.and M₁ M₂)) N :: todo, done, Δ, G, seen, b, hP, hΔ, _, d, hb =>
      match aMinPRD sat todo (.imp (.down (.and M₁ M₂)) N :: done) Δ G seen b
        (ParkedCtxP.cons (ParkedNP.aimp M₁ M₂ N) hP) hΔ (d.wk subParkOut) (bb_park subParkOut d hb) with
      | .inr esc => .inr esc
      | .inl w => .inl (UpFrom2.mk1 w.1 (fun e' f' he' hf' => w.2 e' f' he' hf'))
  | .imp (.down (.imp Q' N')) N :: todo, done, Δ, G, seen, b, hP, hΔ, _, d, hb =>
      match aMinPRD sat todo (.imp (.down (.imp Q' N')) N :: done) Δ G seen b
        (ParkedCtxP.cons (ParkedNP.dyk Q' N' N) hP) hΔ (d.wk subParkOut) (bb_park subParkOut d hb) with
      | .inr esc => .inr esc
      | .inl w => .inl (UpFrom2.mk1 w.1 (fun e' f' he' hf' => w.2 e' f' he' hf'))
  | .circ Q :: todo, done, Δ, G, seen, b, hP, hΔ, _, d, hb =>
      match aMinPRD sat todo (.circ Q :: done) Δ G seen b
        (ParkedCtxP.cons (ParkedNP.box Q) hP) hΔ (d.wk subParkOut) (bb_park subParkOut d hb) with
      | .inr esc => .inr esc
      | .inl w => .inl (UpFrom2.mk1 w.1 (fun e' f' he' hf' => w.2 e' f' he' hf'))
  | .imp (.down (.circ Q')) N :: todo, done, Δ, G, seen, b, hP, hΔ, _, d, hb =>
      match aMinPRD sat todo (.imp (.down (.circ Q')) N :: done) Δ G seen b
        (ParkedCtxP.cons (ParkedNP.cimp Q' N) hP) hΔ (d.wk subParkOut) (bb_park subParkOut d hb) with
      | .inr esc => .inr esc
      | .inl w => .inl (UpFrom2.mk1 w.1 (fun e' f' he' hf' => w.2 e' f' he' hf'))
  | [], done, Δ, G, seen, b, hP, hΔ, j, d, hb =>
      match hf : findFire done (splits done) with
      | some (_, N', rest) =>
          match aMinPRD sat [N'] rest Δ G seen b
            (ParkedCtxP.sub (splits_sub (findFire_mem hf)) hP) hΔ
            (invFireHyp (findFire_mem hf) d) (bb_fire (findFire_mem hf) d hb) with
          | .inr esc => .inr esc
          | .inl w =>
              .inl (UpFrom2.mk1 w.1 (fun e' f' he' hf' => by
                rw [interpRFire_eq hf none, interpRFire_eq hf (some (jGoal j G))]
                exact w.2 e' f' he' hf'))
      | none => sat done Δ G seen b hf hP hΔ d hb
  termination_by todo done Δ G seen b hP hΔ j d => 2 * sum3 todo + sum3 done
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

#axioms_within LJFO.seqSumG [propext]
#axioms_within LJFO.bb_park [propext]
#axioms_within LJFO.bb_orBranch [propext, Quot.sound]
#axioms_within LJFO.bb_andHyp [propext, Quot.sound]
#axioms_within LJFO.bb_impFls [propext, Quot.sound]
#axioms_within LJFO.bb_fire [propext, Quot.sound]
#axioms_within LJFO.eMinPRD [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.aMinPRD [propext, Classical.choice, Quot.sound]
