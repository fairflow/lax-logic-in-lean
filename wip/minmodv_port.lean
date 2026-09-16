/-
# The hloc-lift, stage 1: the free grade — fallible joins at ANY world

The lifted recursion's regular demands split into two grades.  The
FREE grade (this file) serves every consumer that accepts any tag —
`⊃∈`/`⊃∉` premises, `∧`-wraps, the root — and closes at ARBITRARY
worlds with NO `hloc`: at a circ-carrying world the fallible joins
`⋈^At_F`/`⋈^∨_F` take the SAME `Λ*`-thick premise family as the
template's barren joins (round 1, `wip/minmodv.lean`) and their
contexts keep the whole modal zone unconditionally (`joinCtxCircF`),
so the `Λ*`-circs ride through: a stable `◯Y` lands in `Σ^◯`, an
all-Θ one in `Θ^◯∩`.  The price is the `.blocked` tag, which cannot
feed `◯∈`/`◯∉` — those consumers are the TAGGED grade (stage 3).

`FreeWitV` is `RegWitV` minus the tag obligation; `RegWitV.toFree`
embeds, so barren/tagged wits serve free demands (used by the
dichotomy: circ-free worlds keep the round-1 barren joins with their
better tags).
-/
import wip.minmodv

namespace FRJ

open Form

/-- The free-grade regular witness: any tag, no `tOK`. -/
structure FreeWitV (K : Kripke) (G : Form) (a : K.W) (C : Form) : Type where
  ctx : List Form
  t : Tag
  der : FRJVr G t ctx C
  wld : K.W
  wle : K.le a wld
  cov : lamStar K wld G ⊆ ctx

/-- Tagged wits serve free demands. -/
def RegWitV.toFree {K : Kripke} {G : Form} {a : K.W} {C : Form}
    (w : RegWitV K G a C) : FreeWitV K G a C :=
  { ctx := w.ctx, t := w.t, der := w.der, wld := w.wld, wle := w.wle,
    cov := w.cov }

/-- Proper `Rm`-successors, as a list. -/
def properSucc (K : Kripke) (w : K.W) : List K.W :=
  K.elems.filter (fun c => decide (K.Rm w c ∧ c ≠ w))

theorem mem_properSucc {K : Kripke} {w c : K.W} :
    c ∈ properSucc K w ↔ (K.Rm w c ∧ c ≠ w) := by
  simp [properSucc, List.mem_filter, K.complete c]

/-- The fat irregular cell `Ax^I` as an `IrrWitV` — available for EVERY
refuted prime, and its Θ-zone holds the whole of `Ĝ`'s three zones, so
`Λ*`-coverage is free.  (This removes the `upsPrime ≠ []`/`Ax^R`
dichotomy of the template: the family `C :: upsPrime` is never empty.) -/
def axIWitV (K : Kripke) (G : Form) (w : K.W) (C : Form)
    (hCp : C.isPrime) (hC : C ∈ sfR G) (hnf : ¬ K.force w C) :
    IrrWitV K G w C :=
  { stab := []
    th := rm (gAt G) C ++ gImp G ++ gCirc G
    der := .axI C hCp hC (CtxEq.refl _)
    sub := List.nil_subset _
    cov := fun _ hx => lamStar_subset_axI hnf hx }

section FreeJoins

variable {K : Kripke} {G : Form}

/-- The fallible `⋈^At` case: `regPrimeV_join`'s premise family, the
paper context plus the UNCONDITIONAL modal zone; no `hloc`, tag
`.blocked`. -/
def regPrimeF_join (K : Kripke) (G : Form) (a : K.W) (C : Form)
    (hCp : C.isPrime) (hC : C ∈ sfR G) (hnf : ¬ K.force a C)
    (ih : ∀ (A : Form), A ∈ sfR G → ¬ K.force a A → IrrWitV K G a A) :
    FreeWitV K G a C :=
  let E := enumOf (C :: upsPrime K a G) (by simp)
  let f := E.f
  let hfmem : ∀ j, f j ∈ C :: upsPrime K a G := fun j =>
    (E.spec (f j)).mp (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)
  let wit : ∀ j, IrrWitV K G a (f j) := fun j =>
    if h1 : f j = C then by rw [h1]; exact axIWitV K G a C hCp hC hnf
    else
      have hm : f j ∈ upsPrime K a G :=
        (List.mem_cons.mp (hfmem j)).resolve_left h1
      ih (f j) (upsPrime_spec hm).1 (upsPrime_spec hm).2
  let stab := fun j => (wit j).stab
  let th := fun j => (wit j).th
  { ctx := joinCtxAtF stab th f C
    t := .blocked
    wld := a
    wle := K.le_refl a
    der := by
      refine .joinAtF (fun j => (wit j).der)
        (fun i j _ X hX => (wit j).cov ((wit i).sub hX))
        (fun A B hmem => ?_)
        hCp (fun hmem => ?_) hC (CtxEq.refl _)
      · obtain ⟨i, hi⟩ := mem_unionAll.mp hmem
        exact (E.spec A).mpr (List.mem_cons_of_mem _ (mem_upsPrime ((wit i).sub (List.mem_filter.mp hi).1)))
      · obtain ⟨i, hi⟩ := mem_unionAll.mp hmem
        exact not_mem_lamStar_of_not_force hnf ((wit i).sub (List.mem_filter.mp hi).1)
    cov := by
      intro X hX
      have hXG := lamStar_subset_gHat hX
      simp only [gHat, List.mem_append] at hXG
      simp only [joinCtxAtF, joinCtxAt, joinCtxCircF, List.mem_append]
      by_cases hin : ∃ j, X ∈ stab j
      · obtain ⟨j, hj⟩ := hin
        rcases hXG with (h | h) | h
        · exact Or.inl (Or.inl (Or.inl (Or.inl (mem_unionAll.mpr
            ⟨j, List.mem_filter.mpr ⟨hj, (List.mem_filter.mp h).2⟩⟩))))
        · exact Or.inl (Or.inl (Or.inr (mem_unionAll.mpr
            ⟨j, List.mem_filter.mpr ⟨hj, (List.mem_filter.mp h).2⟩⟩)))
        · exact Or.inr (Or.inl (mem_unionAll.mpr
            ⟨j, List.mem_filter.mpr ⟨hj, (List.mem_filter.mp h).2⟩⟩))
      · have hin' : ∀ j, X ∉ stab j := fun j hj => hin ⟨j, hj⟩
        have hallTh : ∀ j, X ∈ th j :=
          fun j => (List.mem_append.mp ((wit j).cov hX)).resolve_left (hin' j)
        rcases hXG with (h | h) | h
        · refine Or.inl (Or.inl (Or.inl (Or.inr (mem_rm.mpr
            ⟨fun hc => not_mem_lamStar_of_not_force hnf (hc ▸ hX), ?_⟩))))
          exact mem_interAll.mpr (fun j =>
            List.mem_filter.mpr ⟨hallTh j, (List.mem_filter.mp h).2⟩)
        · refine Or.inl (Or.inr ?_)
          have himp : X.isImp := (List.mem_filter.mp h).2
          match X, himp with
          | .imp A B, _ =>
              refine mem_restrict.mpr ⟨?_, (E.spec A).mpr (List.mem_cons_of_mem _ (mem_upsPrime hX))⟩
              exact mem_interAll.mpr (fun j => List.mem_filter.mpr ⟨hallTh j, rfl⟩)
        · exact Or.inr (Or.inr (mem_interAll.mpr (fun j =>
            List.mem_filter.mpr ⟨hallTh j, (List.mem_filter.mp h).2⟩))) }

/-- The fallible `⋈^∨` case, same pattern; the disjunct conditions are
the paper-strict `∈ Υ` (both disjuncts head the family). -/
def regOrF_join (K : Kripke) (G : Form) (a : K.W) (C₁ C₂ : Form)
    (hC : Form.or C₁ C₂ ∈ sfR G) (hnf : ¬ K.force a (.or C₁ C₂))
    (ih : ∀ (A : Form), A ∈ sfR G → ¬ K.force a A → IrrWitV K G a A) :
    FreeWitV K G a (.or C₁ C₂) :=
  let hn1 : ¬ K.force a C₁ := fun hc => hnf (Or.inl hc)
  let hn2 : ¬ K.force a C₂ := fun hc => hnf (Or.inr hc)
  let U := C₁ :: C₂ :: upsPrime K a G
  let E := enumOf U (by simp [U])
  let f := E.f
  let hfmem : ∀ j, f j ∈ U := fun j =>
    (E.spec (f j)).mp (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)
  let wit : ∀ j, IrrWitV K G a (f j) := fun j =>
    if h1 : f j = C₁ then by rw [h1]; exact ih C₁ (sfR_or hC).1 hn1
    else if h2 : f j = C₂ then by rw [h2]; exact ih C₂ (sfR_or hC).2 hn2
    else
      have hm : f j ∈ upsPrime K a G := by
        rcases List.mem_cons.mp (hfmem j) with h | h
        · exact absurd h h1
        · rcases List.mem_cons.mp h with h' | h'
          · exact absurd h' h2
          · exact h'
      ih (f j) (upsPrime_spec hm).1 (upsPrime_spec hm).2
  let stab := fun j => (wit j).stab
  let th := fun j => (wit j).th
  { ctx := joinCtxOrF stab th f
    t := .blocked
    wld := a
    wle := K.le_refl a
    der := by
      refine .joinOrF (fun j => (wit j).der)
        (fun i j _ X hX => (wit j).cov ((wit i).sub hX))
        (fun A B hmem => ?_)
        ⟨(E.spec C₁).mpr List.mem_cons_self,
         (E.spec C₂).mpr (List.mem_cons_of_mem _ List.mem_cons_self)⟩
        hC (CtxEq.refl _)
      · obtain ⟨i, hi⟩ := mem_unionAll.mp hmem
        exact (E.spec A).mpr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (mem_upsPrime ((wit i).sub (List.mem_filter.mp hi).1))))
    cov := by
      intro X hX
      have hXG := lamStar_subset_gHat hX
      simp only [gHat, List.mem_append] at hXG
      simp only [joinCtxOrF, joinCtxOr, joinCtxCircF, List.mem_append]
      by_cases hin : ∃ j, X ∈ stab j
      · obtain ⟨j, hj⟩ := hin
        rcases hXG with (h | h) | h
        · exact Or.inl (Or.inl (Or.inl (Or.inl (mem_unionAll.mpr
            ⟨j, List.mem_filter.mpr ⟨hj, (List.mem_filter.mp h).2⟩⟩))))
        · exact Or.inl (Or.inl (Or.inr (mem_unionAll.mpr
            ⟨j, List.mem_filter.mpr ⟨hj, (List.mem_filter.mp h).2⟩⟩)))
        · exact Or.inr (Or.inl (mem_unionAll.mpr
            ⟨j, List.mem_filter.mpr ⟨hj, (List.mem_filter.mp h).2⟩⟩))
      · have hin' : ∀ j, X ∉ stab j := fun j hj => hin ⟨j, hj⟩
        have hallTh : ∀ j, X ∈ th j :=
          fun j => (List.mem_append.mp ((wit j).cov hX)).resolve_left (hin' j)
        rcases hXG with (h | h) | h
        · exact Or.inl (Or.inl (Or.inl (Or.inr (mem_interAll.mpr (fun j =>
            List.mem_filter.mpr ⟨hallTh j, (List.mem_filter.mp h).2⟩)))))
        · refine Or.inl (Or.inr ?_)
          have himp : X.isImp := (List.mem_filter.mp h).2
          match X, himp with
          | .imp A B, _ =>
              refine mem_restrict.mpr ⟨?_, (E.spec A).mpr
                (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (mem_upsPrime hX)))⟩
              exact mem_interAll.mpr (fun j => List.mem_filter.mpr ⟨hallTh j, rfl⟩)
        · exact Or.inr (Or.inr (mem_interAll.mpr (fun j =>
            List.mem_filter.mpr ⟨hallTh j, (List.mem_filter.mp h).2⟩))) }

end FreeJoins

/-- info: 'FRJ.regPrimeF_join' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms regPrimeF_join

/-- info: 'FRJ.regOrF_join' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms regOrF_join


/-! ## Stage 2: the pledged joins — chain-tagged rows for CONE-REFUTED
prime/or goals at worlds with proper `Rm`-successors

The promise joins pledge the goal itself: the family is one tagged row
per proper `Rm`-successor (all of which refute the goal — that is what
cone-refutation transports), each pledging `C` with its own `tOK` as
the per-row condition, and the conclusion carries `.chain C` whose
`tOK` is `Covers.refl`.  Pledge-existence is SAFE here (the peer's
`not_pledgeFam_of_circ_mem` needs `◯C ∈ Λ*`, impossible for a
cone-refuted `C`), and the `Λ*`-circs are retained by `joinCtxCircP`:
a stable `◯Y` is grounded through (J5) by the `Rm`-witness of its own
forcing — which is a proper successor, hence IN the family — and an
all-Θ one survives `restrictC` the same way.  The `restrictP` filter
keeps every `Λ*`-member because `Λ*`-members are forced, hence
`Clo`-derivable in every family context (`mem_clo_lamStar`). -/

section Pledged

variable {K : Kripke} {G : Form}

/-- **The pledged `⋈^At_P`.**  `C` prime, refuted on the whole
`Rm`-cone of `w`, with at least one proper successor: the promise
family pledges `C` at every proper successor and the conclusion is
`.chain C`-tagged. -/
def tagPrimeP_join (K : Kripke) (G : Form) (hinf : K.Infallible)
    (w : K.W) (C : Form)
    (hCp : C.isPrime) (hC : C ∈ sfR G)
    (hcone : ∀ v, K.Rm w v → ¬ K.force v C)
    (hs : properSucc K w ≠ [])
    (ih : ∀ (A : Form), A ∈ sfR G → ¬ K.force w A → IrrWitV K G w A)
    (fam : ∀ c, K.Rm w c → c ≠ w → RegWitV K G c C) :
    RegWitV K G w C :=
  have hnf : ¬ K.force w C := hcone w (K.rm_refl w)
  -- the irregular family: the fat axiom cell heads `C :: upsPrime`
  let E := enumOf (C :: upsPrime K w G) (by simp)
  let f := E.f
  let hfmem : ∀ j, f j ∈ C :: upsPrime K w G := fun j =>
    (E.spec (f j)).mp (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)
  let wit : ∀ j, IrrWitV K G w (f j) := fun j =>
    if h1 : f j = C then by rw [h1]; exact axIWitV K G w C hCp hC hnf
    else
      have hm : f j ∈ upsPrime K w G :=
        (List.mem_cons.mp (hfmem j)).resolve_left h1
      ih (f j) (upsPrime_spec hm).1 (upsPrime_spec hm).2
  let stab := fun j => (wit j).stab
  let th := fun j => (wit j).th
  -- the promise family: one tagged row per proper successor
  match hsl : properSucc K w with
  | [] => absurd hsl hs
  | c0 :: cs =>
      let sw : Fin (cs.length + 1) → K.W := fun i => (c0 :: cs)[i.val]'i.isLt
      have hsw : ∀ i, K.Rm w (sw i) ∧ sw i ≠ w := fun i =>
        mem_properSucc.mp (hsl ▸ List.getElem_mem i.isLt)
      have hswm : ∀ c, K.Rm w c → c ≠ w → ∃ i, sw i = c := fun c hrm hne => by
        have : c ∈ c0 :: cs := hsl ▸ mem_properSucc.mpr ⟨hrm, hne⟩
        obtain ⟨i, hi⟩ := List.mem_iff_get.mp this
        exact ⟨i, hi⟩
      let pw : ∀ i, RegWitV K G (sw i) C := fun i =>
        fam (sw i) (hsw i).1 (hsw i).2
      let Δs : Fin (cs.length + 1) → List Form := fun i => (pw i).ctx
      -- forced sfL-members are Clo-derivable in EVERY family context
      have hcloAll : ∀ (X : Form), X ∈ sfL G → K.force w X →
          ∀ i, Clo (Δs i) X := fun X hsf hf i =>
        clo_mono (pw i).cov (mem_clo_lamStar (hinf (pw i).wld) hsf
          (K.force_mono (K.le_trans (K.sub_mi (hsw i).1) (pw i).wle) hf))
      -- the (J5)-style grounding: a Λ*-circ's body has an Rm-witness,
      -- which is a proper successor, hence a family index
      have hground : ∀ (Y : Form), Form.circ Y ∈ lamStar K w G →
          ∃ i, Clo (Δs i) Y := by
        intro Y hY
        obtain ⟨hsfY, hstar⟩ := mem_lamStar.mp hY
        obtain ⟨c, hrc, hcY⟩ := hstar.1 w (K.le_refl w)
        have hcne : c ≠ w := fun h => hstar.2 (h ▸ hcY)
        obtain ⟨i, hi⟩ := hswm c hrc hcne
        refine ⟨i, clo_mono (pw i).cov (mem_clo_lamStar (hinf (pw i).wld)
          (sfL_circ hsfY) (K.force_mono (pw i).wle (hi ▸ hcY)))⟩
      { ctx := joinCtxAtP stab th f C Δs
        t := .chain C
        wld := w
        wle := K.le_refl w
        tOK := Or.inr ⟨C, rfl, Covers.refl⟩
        der := by
          refine .joinAtP (fun j => (wit j).der) (fun i => (pw i).der)
            (fun i j _ X hX => (wit j).cov ((wit i).sub hX))
            (fun A B hmem => ?_)
            (fun Y hmem => ?_)
            (fun i j X hX => ?_)
            (Or.inr ⟨rfl, fun i => ⟨rfl, (pw i).tOK⟩⟩)
            hCp (fun hmem => ?_) hC (CtxEq.refl _)
          · obtain ⟨i, hi⟩ := mem_unionAll.mp hmem
            exact (E.spec A).mpr (List.mem_cons_of_mem _
              (mem_upsPrime ((wit i).sub (List.mem_filter.mp hi).1)))
          · obtain ⟨i, hi⟩ := mem_unionAll.mp hmem
            exact hground Y ((wit i).sub (List.mem_filter.mp hi).1)
          · exact clo_mono (pw i).cov (mem_clo_lamStar (hinf (pw i).wld)
              (mem_lamStar.mp ((wit j).sub hX)).1
              (K.force_mono (K.le_trans (K.sub_mi (hsw i).1) (pw i).wle)
                (K.forceStar_force (mem_lamStar.mp ((wit j).sub hX)).2)))
          · obtain ⟨i, hi⟩ := mem_unionAll.mp hmem
            exact not_mem_lamStar_of_not_force hnf
              ((wit i).sub (List.mem_filter.mp hi).1)
        cov := by
          intro X hX
          have hXsf := (mem_lamStar.mp hX).1
          have hXf := K.forceStar_force (mem_lamStar.mp hX).2
          have hXG := lamStar_subset_gHat hX
          simp only [gHat, List.mem_append] at hXG
          refine mem_restrictP.mpr ⟨?_, fun i => hcloAll X hXsf hXf i⟩
          simp only [joinCtxAt, joinCtxCircP, List.mem_append]
          by_cases hin : ∃ j, X ∈ stab j
          · obtain ⟨j, hj⟩ := hin
            rcases hXG with (h | h) | h
            · exact Or.inl (Or.inl (Or.inl (Or.inl (mem_unionAll.mpr
                ⟨j, List.mem_filter.mpr ⟨hj, (List.mem_filter.mp h).2⟩⟩))))
            · exact Or.inl (Or.inl (Or.inr (mem_unionAll.mpr
                ⟨j, List.mem_filter.mpr ⟨hj, (List.mem_filter.mp h).2⟩⟩)))
            · exact Or.inr (Or.inl (mem_unionAll.mpr
                ⟨j, List.mem_filter.mpr ⟨hj, (List.mem_filter.mp h).2⟩⟩))
          · have hin' : ∀ j, X ∉ stab j := fun j hj => hin ⟨j, hj⟩
            have hallTh : ∀ j, X ∈ th j :=
              fun j => (List.mem_append.mp ((wit j).cov hX)).resolve_left (hin' j)
            rcases hXG with (h | h) | h
            · refine Or.inl (Or.inl (Or.inl (Or.inr (mem_rm.mpr
                ⟨fun hc => not_mem_lamStar_of_not_force hnf (hc ▸ hX), ?_⟩))))
              exact mem_interAll.mpr (fun j =>
                List.mem_filter.mpr ⟨hallTh j, (List.mem_filter.mp h).2⟩)
            · refine Or.inl (Or.inr ?_)
              have himp : X.isImp := (List.mem_filter.mp h).2
              match X, himp with
              | .imp A B, _ =>
                  refine mem_restrict.mpr ⟨?_, (E.spec A).mpr
                    (List.mem_cons_of_mem _ (mem_upsPrime hX))⟩
                  exact mem_interAll.mpr (fun j =>
                    List.mem_filter.mpr ⟨hallTh j, rfl⟩)
            · refine Or.inr (Or.inr ?_)
              have hcircX : X.isCirc := (List.mem_filter.mp h).2
              match X, hcircX with
              | .circ Y, _ =>
                  refine mem_restrictC.mpr ⟨?_, hground Y hX⟩
                  exact mem_interAll.mpr (fun j =>
                    List.mem_filter.mpr ⟨hallTh j, rfl⟩) }

end Pledged

/-- info: 'FRJ.tagPrimeP_join' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms tagPrimeP_join

/-- **The pledged `⋈^∨_P`.**  Same design at an `∨`-goal: disjunct
conditions are paper-strict (both head the irregular family), the
promise family pledges the disjunction itself. -/
def tagOrP_join (K : Kripke) (G : Form) (hinf : K.Infallible)
    (w : K.W) (C₁ C₂ : Form)
    (hC : Form.or C₁ C₂ ∈ sfR G)
    (hcone : ∀ v, K.Rm w v → ¬ K.force v (.or C₁ C₂))
    (hs : properSucc K w ≠ [])
    (ih : ∀ (A : Form), A ∈ sfR G → ¬ K.force w A → IrrWitV K G w A)
    (fam : ∀ c, K.Rm w c → c ≠ w → RegWitV K G c (.or C₁ C₂)) :
    RegWitV K G w (.or C₁ C₂) :=
  have hnf : ¬ K.force w (.or C₁ C₂) := hcone w (K.rm_refl w)
  let hn1 : ¬ K.force w C₁ := fun hc => hnf (Or.inl hc)
  let hn2 : ¬ K.force w C₂ := fun hc => hnf (Or.inr hc)
  let U := C₁ :: C₂ :: upsPrime K w G
  let E := enumOf U (by simp [U])
  let f := E.f
  let hfmem : ∀ j, f j ∈ U := fun j =>
    (E.spec (f j)).mp (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)
  let wit : ∀ j, IrrWitV K G w (f j) := fun j =>
    if h1 : f j = C₁ then by rw [h1]; exact ih C₁ (sfR_or hC).1 hn1
    else if h2 : f j = C₂ then by rw [h2]; exact ih C₂ (sfR_or hC).2 hn2
    else
      have hm : f j ∈ upsPrime K w G := by
        rcases List.mem_cons.mp (hfmem j) with h | h
        · exact absurd h h1
        · rcases List.mem_cons.mp h with h' | h'
          · exact absurd h' h2
          · exact h'
      ih (f j) (upsPrime_spec hm).1 (upsPrime_spec hm).2
  let stab := fun j => (wit j).stab
  let th := fun j => (wit j).th
  match hsl : properSucc K w with
  | [] => absurd hsl hs
  | c0 :: cs =>
      let sw : Fin (cs.length + 1) → K.W := fun i => (c0 :: cs)[i.val]'i.isLt
      have hsw : ∀ i, K.Rm w (sw i) ∧ sw i ≠ w := fun i =>
        mem_properSucc.mp (hsl ▸ List.getElem_mem i.isLt)
      have hswm : ∀ c, K.Rm w c → c ≠ w → ∃ i, sw i = c := fun c hrm hne => by
        have : c ∈ c0 :: cs := hsl ▸ mem_properSucc.mpr ⟨hrm, hne⟩
        obtain ⟨i, hi⟩ := List.mem_iff_get.mp this
        exact ⟨i, hi⟩
      let pw : ∀ i, RegWitV K G (sw i) (.or C₁ C₂) := fun i =>
        fam (sw i) (hsw i).1 (hsw i).2
      let Δs : Fin (cs.length + 1) → List Form := fun i => (pw i).ctx
      have hcloAll : ∀ (X : Form), X ∈ sfL G → K.force w X →
          ∀ i, Clo (Δs i) X := fun X hsf hf i =>
        clo_mono (pw i).cov (mem_clo_lamStar (hinf (pw i).wld) hsf
          (K.force_mono (K.le_trans (K.sub_mi (hsw i).1) (pw i).wle) hf))
      have hground : ∀ (Y : Form), Form.circ Y ∈ lamStar K w G →
          ∃ i, Clo (Δs i) Y := by
        intro Y hY
        obtain ⟨hsfY, hstar⟩ := mem_lamStar.mp hY
        obtain ⟨c, hrc, hcY⟩ := hstar.1 w (K.le_refl w)
        have hcne : c ≠ w := fun h => hstar.2 (h ▸ hcY)
        obtain ⟨i, hi⟩ := hswm c hrc hcne
        refine ⟨i, clo_mono (pw i).cov (mem_clo_lamStar (hinf (pw i).wld)
          (sfL_circ hsfY) (K.force_mono (pw i).wle (hi ▸ hcY)))⟩
      { ctx := joinCtxOrP stab th f Δs
        t := .chain (.or C₁ C₂)
        wld := w
        wle := K.le_refl w
        tOK := Or.inr ⟨.or C₁ C₂, rfl, Covers.refl⟩
        der := by
          refine .joinOrP (fun j => (wit j).der) (fun i => (pw i).der)
            (fun i j _ X hX => (wit j).cov ((wit i).sub hX))
            (fun A B hmem => ?_)
            (fun Y hmem => ?_)
            (fun i j X hX => ?_)
            (Or.inr ⟨rfl, fun i => ⟨rfl, (pw i).tOK⟩⟩)
            ⟨(E.spec C₁).mpr List.mem_cons_self,
             (E.spec C₂).mpr (List.mem_cons_of_mem _ List.mem_cons_self)⟩
            hC (CtxEq.refl _)
          · obtain ⟨i, hi⟩ := mem_unionAll.mp hmem
            exact (E.spec A).mpr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (mem_upsPrime ((wit i).sub (List.mem_filter.mp hi).1))))
          · obtain ⟨i, hi⟩ := mem_unionAll.mp hmem
            exact hground Y ((wit i).sub (List.mem_filter.mp hi).1)
          · exact clo_mono (pw i).cov (mem_clo_lamStar (hinf (pw i).wld)
              (mem_lamStar.mp ((wit j).sub hX)).1
              (K.force_mono (K.le_trans (K.sub_mi (hsw i).1) (pw i).wle)
                (K.forceStar_force (mem_lamStar.mp ((wit j).sub hX)).2)))
        cov := by
          intro X hX
          have hXsf := (mem_lamStar.mp hX).1
          have hXf := K.forceStar_force (mem_lamStar.mp hX).2
          have hXG := lamStar_subset_gHat hX
          simp only [gHat, List.mem_append] at hXG
          refine mem_restrictP.mpr ⟨?_, fun i => hcloAll X hXsf hXf i⟩
          simp only [joinCtxOr, joinCtxCircP, List.mem_append]
          by_cases hin : ∃ j, X ∈ stab j
          · obtain ⟨j, hj⟩ := hin
            rcases hXG with (h | h) | h
            · exact Or.inl (Or.inl (Or.inl (Or.inl (mem_unionAll.mpr
                ⟨j, List.mem_filter.mpr ⟨hj, (List.mem_filter.mp h).2⟩⟩))))
            · exact Or.inl (Or.inl (Or.inr (mem_unionAll.mpr
                ⟨j, List.mem_filter.mpr ⟨hj, (List.mem_filter.mp h).2⟩⟩)))
            · exact Or.inr (Or.inl (mem_unionAll.mpr
                ⟨j, List.mem_filter.mpr ⟨hj, (List.mem_filter.mp h).2⟩⟩))
          · have hin' : ∀ j, X ∉ stab j := fun j hj => hin ⟨j, hj⟩
            have hallTh : ∀ j, X ∈ th j :=
              fun j => (List.mem_append.mp ((wit j).cov hX)).resolve_left (hin' j)
            rcases hXG with (h | h) | h
            · exact Or.inl (Or.inl (Or.inl (Or.inr (mem_interAll.mpr (fun j =>
                List.mem_filter.mpr ⟨hallTh j, (List.mem_filter.mp h).2⟩)))))
            · refine Or.inl (Or.inr ?_)
              have himp : X.isImp := (List.mem_filter.mp h).2
              match X, himp with
              | .imp A B, _ =>
                  refine mem_restrict.mpr ⟨?_, (E.spec A).mpr
                    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (mem_upsPrime hX)))⟩
                  exact mem_interAll.mpr (fun j =>
                    List.mem_filter.mpr ⟨hallTh j, rfl⟩)
            · refine Or.inr (Or.inr ?_)
              have hcircX : X.isCirc := (List.mem_filter.mp h).2
              match X, hcircX with
              | .circ Y, _ =>
                  refine mem_restrictC.mpr ⟨?_, hground Y hX⟩
                  exact mem_interAll.mpr (fun j =>
                    List.mem_filter.mpr ⟨hallTh j, rfl⟩) }

/-- info: 'FRJ.tagOrP_join' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms tagOrP_join


end FRJ
