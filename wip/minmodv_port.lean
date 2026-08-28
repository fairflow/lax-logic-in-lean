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

section FreeJoins

variable {K : Kripke} {G : Form}

/-- The fallible `⋈^At` case: `regPrimeV_join`'s premise family, the
paper context plus the UNCONDITIONAL modal zone; no `hloc`, tag
`.blocked`. -/
def regPrimeF_join (K : Kripke) (G : Form) (a : K.W) (C : Form)
    (hCp : C.isPrime) (hC : C ∈ sfR G) (hnf : ¬ K.force a C)
    (hne : upsPrime K a G ≠ [])
    (ih : ∀ (A : Form), A ∈ sfR G → ¬ K.force a A → IrrWitV K G a A) :
    FreeWitV K G a C :=
  let E := enumOf (upsPrime K a G) hne
  let f := E.f
  let hfmem : ∀ j, f j ∈ upsPrime K a G := fun j =>
    (E.spec (f j)).mp (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)
  let wit : ∀ j, IrrWitV K G a (f j) := fun j =>
    ih (f j) (upsPrime_spec (hfmem j)).1 (upsPrime_spec (hfmem j)).2
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
        exact (E.spec A).mpr (mem_upsPrime ((wit i).sub (List.mem_filter.mp hi).1))
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
              refine mem_restrict.mpr ⟨?_, (E.spec A).mpr (mem_upsPrime hX)⟩
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

end FRJ
