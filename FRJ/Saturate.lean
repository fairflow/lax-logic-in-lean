/-
# FRJ◯ completeness: the saturation-closure organisation

W4 §10 (docs/frj-w4.md): the completeness construction for the modal
calculus cannot be founded on a lexicographic measure over
(height, phase, size) — the Υ-edge and the ◯-body edge pull the phase
priority in opposite directions, and the order that resolves a given
instance depends on the model (§10 addendum).  This file sets up the
replacement organisation: a demand-closure predicate `AllMet`, from
which completeness follows in one step, and which the landed ◯-free
construction already establishes in the circ-free case (validation
below).  The open content of FRJ◯ completeness is exactly:
`AllMet K G` for every `K` — the progress lemma of the per-instance
fixpoint.
-/
import FRJ.Minimal

namespace FRJ

/-- The modal regular wit: a tag-carrying derivation anchored at a world
`wld ≥ a` whose `Λ*` the context covers, with the tag consumable by the
modal rules (`circIn`/`circNotIn`/the ⋈^◯ family all gate on exactly
this disjunction). -/
structure MRWit (K : Kripke) (G : Form) (a : K.W) (C : Form) : Type where
  t : Tag
  ctx : List Form
  der : FRJr G t ctx C
  tOK : t = .barren ∨ ∃ W, t = .chain W ∧ Covers ctx W C
  wld : K.W
  wle : K.le a wld
  wfal : ¬ K.Fal wld
  cov : lamStar K wld G ⊆ ctx

/-- **The demand closure.**  Every refuted right-signature formula at
every world of `K` has both an irregular and a (tag-admissible) regular
wit.  `¬ force a C` already yields `¬ Fal a` (a fallible world forces
everything), so no separate infallibility hypothesis is needed. -/
def AllMet (K : Kripke) (G : Form) : Prop :=
  ∀ a : K.W, ∀ C ∈ sfR G, ¬ K.force a C →
    Nonempty (IrrWit K G a C) ∧ Nonempty (MRWit K G a C)

/-- **Completeness, given the closure**: statement (A) of the W4 targets
follows from `AllMet` in one step, at the root demand for `G` itself. -/
theorem completeness_of_allMet {K : Kripke} {G : Form}
    (h : AllMet K G) (hK : ¬ K.valid G) : Provable G := by
  obtain ⟨w⟩ := (h K.root G (sfR_self G) hK).2
  exact ⟨w.t, w.ctx, ⟨w.der⟩⟩

/-- **The full biconditional, given the closure** — W4 statement (B):
`FRJ(G)` proves `G` iff `G` has a root-infallible countermodel.  The
soundness half is unconditional (`provable_root_countermodel`); the
closure carries the completeness half. -/
theorem frj_iff_root_countermodel_of_allMet {G : Form}
    (hmet : ∀ K : Kripke, AllMet K G) :
    Provable G ↔ ∃ K : Kripke, ¬ K.Fal K.root ∧ ¬ K.valid G := by
  constructor
  · exact provable_root_countermodel
  · rintro ⟨K, -, hv⟩
    exact completeness_of_allMet (hmet K) hv

/-- **Validation: the landed ◯-free construction establishes the
closure.**  For a circ-free goal over an infallible model, `minMod`
supplies both wits, barren-tagged; so the new organisation subsumes the
proved ◯-free completeness. -/
theorem allMet_of_circFree {K : Kripke} {G : Form}
    (hcf : ∀ X ∈ sfR G ++ sfL G, X.isCirc = false)
    (hinf : K.Infallible) : AllMet K G := by
  intro a C hC hf
  refine ⟨⟨minMod K G hcf hinf a 0 C hC hf⟩, ?_⟩
  have w : RegWit K G a C := minMod K G hcf hinf a 1 C hC hf
  exact ⟨⟨.barren, w.ctx, w.der, Or.inl rfl, w.wld, w.wle, hinf _, w.cov⟩⟩

/-- The ◯-free completeness re-derived through the closure — the two
organisations agree on their common domain. -/
theorem completeness_via_closure {G : Form}
    (hcf : ∀ X ∈ sfR G ++ sfL G, X.isCirc = false)
    (K : Kripke) (hinf : K.Infallible) (hK : ¬ K.valid G) : Provable G :=
  completeness_of_allMet (allMet_of_circFree hcf hinf) hK

/-! ## Case builders (slice 2)

Each of the visit's cases, refactored to take its supplier wits as
INPUTS: the un-orderable recursion of §9/§10 becomes a family of
independently checkable constructions, and the open content of `AllMet`
contracts to the per-instance supply order alone.  Everything is
Type-valued data — `Nonempty` appears only at the `AllMet` interface —
so the layer stays `Classical.choice`-free like the landed `minMod`. -/

/-- **The irregular ◯-demand** (`◯∉`), from a regular `Z`-wit anywhere
above `a`.  The §9 bad edge — its supplier is now an input. -/
def metI_circ {K : Kripke} {G : Form} {a : K.W} {Z : Form}
    (hgoal : Form.circ Z ∈ sfR G)
    (w : MRWit K G a Z) : IrrWit K G a (.circ Z) where
  stab := []
  th := nf G (lamStar K a G)
  der := .circNotIn w.der w.tOK
    (fun X hX =>
      ⟨clo_mono w.cov (lamStar_mono w.wfal w.wle X (mem_nf.mp hX).2),
        (mem_nf.mp hX).1⟩) hgoal
  sub := List.nil_subset _
  cov := fun X hX =>
    List.mem_append_right _ (mem_nf.mpr ⟨lamStar_subset_gHat hX, hX⟩)
  thNf := nf_idem.symm

/-- The irregular atomic demand — supplier-free (`Ax^I` with the full
complement zone), ported from `minMod` unchanged: it never used `hcf`. -/
def metI_atom {K : Kripke} {G : Form} {a : K.W} {p : String}
    (hC : Form.atom p ∈ sfR G) (hnf : ¬ K.force a (.atom p)) :
    IrrWit K G a (.atom p) where
  stab := []
  th := nf G ((rm (gAt G) (.atom p)) ++ gImp G ++ gCirc G)
  der := .axI (.atom p) rfl hC
  sub := fun _ h => absurd h List.not_mem_nil
  cov := fun _ hx => lamStar_subset_axI hnf hx
  thNf := nf_idem.symm

/-- The irregular `⊥`-demand — supplier-free. -/
def metI_bot {K : Kripke} {G : Form} {a : K.W}
    (hC : Form.bot ∈ sfR G) (hnf : ¬ K.force a .bot) :
    IrrWit K G a .bot where
  stab := []
  th := nf G ((rm (gAt G) .bot) ++ gImp G ++ gCirc G)
  der := .axI .bot rfl hC
  sub := fun _ h => absurd h List.not_mem_nil
  cov := fun _ hx => lamStar_subset_axI hnf hx
  thNf := nf_idem.symm

/-- The irregular `∧`-demand, from a wit for whichever conjunct fails. -/
def metI_and {K : Kripke} {G : Form} {a : K.W} {C₁ C₂ : Form}
    (hC : Form.and C₁ C₂ ∈ sfR G) (hnf : ¬ K.force a (.and C₁ C₂))
    (sup₁ : ¬ K.force a C₁ → IrrWit K G a C₁)
    (sup₂ : K.force a C₁ → ¬ K.force a C₂ → IrrWit K G a C₂) :
    IrrWit K G a (.and C₁ C₂) :=
  if h1 : K.force a C₁ then
    let w := sup₂ h1 (fun hc => hnf ⟨h1, hc⟩)
    { stab := w.stab, th := w.th, der := .andI2 w.der hC
      sub := w.sub, cov := w.cov, thNf := w.thNf }
  else
    let w := sup₁ h1
    { stab := w.stab, th := w.th, der := .andI1 w.der hC
      sub := w.sub, cov := w.cov, thNf := w.thNf }

/-- The irregular `∨`-demand, from wits for both disjuncts. -/
def metI_or {K : Kripke} {G : Form} {a : K.W} {C₁ C₂ : Form}
    (hC : Form.or C₁ C₂ ∈ sfR G) (hnf : ¬ K.force a (.or C₁ C₂))
    (sup₁ : ¬ K.force a C₁ → IrrWit K G a C₁)
    (sup₂ : ¬ K.force a C₂ → IrrWit K G a C₂) :
    IrrWit K G a (.or C₁ C₂) := by
  let w₁ := sup₁ (fun hc => hnf (Or.inl hc))
  let w₂ := sup₂ (fun hc => hnf (Or.inr hc))
  refine { stab := w₁.stab ++ w₂.stab, th := nf G (cap w₁.th w₂.th)
           der := .orI w₁.der w₂.der (fun X hX => w₂.cov (w₁.sub hX))
                    (fun X hX => w₁.cov (w₂.sub hX)) hC
           sub := ?_, cov := ?_, thNf := nf_idem.symm }
  · intro X hX
    rcases List.mem_append.mp hX with hX' | hX'
    · exact w₁.sub hX'
    · exact w₂.sub hX'
  · intro X hX
    by_cases hx1 : X ∈ w₁.stab
    · exact List.mem_append_left _ (List.mem_append_left _ hx1)
    · by_cases hx2 : X ∈ w₂.stab
      · exact List.mem_append_left _ (List.mem_append_right _ hx2)
      · refine List.mem_append_right _ (mem_nf.mpr ⟨lamStar_subset_gHat hX, ?_⟩)
        exact mem_cap.mpr ⟨(List.mem_append.mp (w₁.cov hX)).resolve_left hx1,
          (List.mem_append.mp (w₂.cov hX)).resolve_left hx2⟩

/-- The irregular `⊃`-demand.  Two suppliers: the `⊃∈` route (an
irregular `B`-wit at `a` itself, used when `a` forces `A`) and the
`⊃∉` float (a regular `B`-wit at the minEta world, which is then
strictly above `a`). -/
def metI_imp {K : Kripke} {G : Form} {a : K.W} {A B : Form}
    (hC : Form.imp A B ∈ sfR G) (hnf : ¬ K.force a (.imp A B))
    (supI : K.force a A → ¬ K.force a B → IrrWit K G a B)
    (supR : ∀ e : K.W, K.le a e → e ≠ a → K.force e A → ¬ K.force e B →
      MRWit K G e B) :
    IrrWit K G a (.imp A B) := by
  obtain ⟨hA, hB⟩ := sfR_imp hC
  have hfa : ¬ K.Fal a := fun hf => hnf (K.fal_force _ hf)
  let m := minEta hnf
  by_cases hea : m.e = a
  · have heA : K.force a A := hea ▸ m.fA
    have heB : ¬ K.force a B := hea ▸ m.nfB
    let w := supI heA heB
    have hLamTh : sdiff (lamStar K a G) w.stab ⊆ w.th := by
      intro x hx
      obtain ⟨hx1, hx2⟩ := mem_sdiff.mp hx
      exact (List.mem_append.mp (w.cov hx1)).resolve_left hx2
    have hStLam : lamStar K a G ⊆ w.stab ++ sdiff (lamStar K a G) w.stab := by
      intro x hx
      by_cases hs : x ∈ w.stab
      · exact List.mem_append_left _ hs
      · exact List.mem_append_right _ (mem_sdiff.mpr ⟨hx, hs⟩)
    have hzone : nf G (sdiff w.th (sdiff (lamStar K a G) w.stab) ++
        sdiff (lamStar K a G) w.stab) = w.th := by
      conv_rhs => rw [w.thNf]
      refine nf_ext (fun x _ => ?_)
      constructor
      · intro hx
        rcases List.mem_append.mp hx with hx' | hx'
        · exact (mem_sdiff.mp hx').1
        · exact hLamTh hx'
      · intro hx
        by_cases hL : x ∈ sdiff (lamStar K a G) w.stab
        · exact List.mem_append_right _ hL
        · exact List.mem_append_left _ (mem_sdiff.mpr ⟨hx, hL⟩)
    have hAclo : Clo (nf G (w.stab ++ sdiff (lamStar K a G) w.stab)) A := by
      refine clo_mono ?_ (mem_clo_lamStar hfa hA heA)
      intro x hx
      exact mem_nf.mpr ⟨lamStar_subset_gHat hx, hStLam hx⟩
    refine { stab := nf G (w.stab ++ sdiff (lamStar K a G) w.stab)
             th := nf G (sdiff w.th (sdiff (lamStar K a G) w.stab))
             der := .impInI (by rw [hzone]; exact w.der) cap_sdiff_eq_nil hAclo hC
             sub := ?_, cov := ?_, thNf := nf_idem.symm }
    · intro X hX
      rcases List.mem_append.mp (mem_nf.mp hX).2 with hX' | hX'
      · exact w.sub hX'
      · exact (mem_sdiff.mp hX').1
    · intro X hX
      exact List.mem_append_left _
        (mem_nf.mpr ⟨lamStar_subset_gHat hX, hStLam hX⟩)
  · have hnaA : ¬ K.force a A :=
      m.min a (K.le_refl a) m.le (fun hc => hea hc.symm)
    let w := supR m.e m.le hea m.fA m.nfB
    have hab : K.le a w.wld := K.le_trans m.le w.wle
    exact { stab := [], th := nf G (lamStar K a G)
            der := .impNotIn w.der
              (fun X hX => ⟨clo_mono w.cov (lamStar_mono w.wfal hab X (mem_nf.mp hX).2),
                (mem_nf.mp hX).1⟩)
              (clo_mono w.cov (mem_clo_lamStar w.wfal hA (K.force_mono w.wle m.fA)))
              (fun hc => hnaA (forces_clo_lamStar (clo_mono nf_subset_self hc))) hC
            sub := fun _ h => absurd h List.not_mem_nil
            cov := fun x hx => mem_nf.mpr ⟨lamStar_subset_gHat hx, hx⟩
            thNf := nf_idem.symm }

/-- Tag admissibility threads through `∧`-introduction via `Covers.andL/R`. -/
def metR_and {K : Kripke} {G : Form} {a : K.W} {C₁ C₂ : Form}
    (hC : Form.and C₁ C₂ ∈ sfR G) (hnf : ¬ K.force a (.and C₁ C₂))
    (sup₁ : ¬ K.force a C₁ → MRWit K G a C₁)
    (sup₂ : K.force a C₁ → ¬ K.force a C₂ → MRWit K G a C₂) :
    MRWit K G a (.and C₁ C₂) :=
  if h1 : K.force a C₁ then
    let w := sup₂ h1 (fun hc => hnf ⟨h1, hc⟩)
    ⟨w.t, w.ctx, .andR2 w.der hC,
      w.tOK.elim Or.inl (fun ⟨W, htg, hcov⟩ => Or.inr ⟨W, htg, .andR hcov⟩),
      w.wld, w.wle, w.wfal, w.cov⟩
  else
    let w := sup₁ h1
    ⟨w.t, w.ctx, .andR1 w.der hC,
      w.tOK.elim Or.inl (fun ⟨W, htg, hcov⟩ => Or.inr ⟨W, htg, .andL hcov⟩),
      w.wld, w.wle, w.wfal, w.cov⟩

/-- Tag admissibility threads through `⊃`-introduction via `Covers.imp`,
whose `Clo` side condition is the same one `impIn` itself consumes.  The
minEta float and the stay-at-`a` case share one body. -/
def metR_imp {K : Kripke} {G : Form} {a : K.W} {A B : Form}
    (hC : Form.imp A B ∈ sfR G) (hnf : ¬ K.force a (.imp A B))
    (sup : ∀ e : K.W, K.le a e → K.force e A → ¬ K.force e B →
      MRWit K G e B) :
    MRWit K G a (.imp A B) :=
  let m := minEta hnf
  let w := sup m.e m.le m.fA m.nfB
  let hAclo : Clo w.ctx A :=
    clo_mono w.cov (mem_clo_lamStar w.wfal (sfR_imp hC).1 (K.force_mono w.wle m.fA))
  ⟨w.t, w.ctx, .impIn w.der hAclo hC,
    w.tOK.elim Or.inl (fun ⟨W, htg, hcov⟩ => Or.inr ⟨W, htg, .imp hcov hAclo⟩),
    w.wld, K.le_trans m.le w.wle, w.wfal, w.cov⟩

/-- The regular `◯`-demand, by `◯∈` over a `Z`-wit at the minZeta world.
No modal join is needed: `circIn` preserves any admissible tag, and the
measure cycle that forced the ⋈^◯ route in the recursive organisation
does not exist here — the supplier is an input. -/
def metR_circ {K : Kripke} {G : Form} {a : K.W} {Z : Form}
    (hC : Form.circ Z ∈ sfR G) (hnf : ¬ K.force a (.circ Z))
    (sup : ∀ e : K.W, K.le a e → ¬ K.force e Z → MRWit K G e Z) :
    MRWit K G a (.circ Z) :=
  let mz := minZeta hnf
  let w := sup mz.e mz.le (mz.cone _ (K.rm_refl _))
  ⟨w.t, w.ctx, .circIn w.der w.tOK hC,
    w.tOK.elim Or.inl (fun ⟨W, htg, hcov⟩ => Or.inr ⟨W, htg, .circ hcov⟩),
    w.wld, K.le_trans mz.le w.wle, w.wfal, w.cov⟩

/-! ### The prime and `∨` joins at locally circ-free worlds

`hcf` (the global syntactic circ-freeness) enters the landed helpers in
exactly two roles, both derivable from the runtime per-world condition
`circPart (Λ*_a) = []`: the `hcirc` discharge of the barren joins, and
the `Ĝ_◯`-branch of cov.  The residual — the same demands at worlds
whose `Λ*` carries `◯`-formulas, where the joins must run in promise
mode — is the §8 corner in its final localisation. -/

theorem lamStar_not_circ_loc {K : Kripke} {a : K.W} {G : Form} {X : Form}
    (hloc : circPart (lamStar K a G) = [])
    (hX : X ∈ lamStar K a G) (hc : X.isCirc = true) : False := by
  have : X ∈ circPart (lamStar K a G) := List.mem_filter.mpr ⟨hX, hc⟩
  rw [hloc] at this
  exact List.not_mem_nil this

theorem unionAll_circPart_nil_loc {K : Kripke} {a : K.W} {G : Form} {n : Nat}
    (hloc : circPart (lamStar K a G) = [])
    {stab : Fin (n + 1) → List Form} (hsub : ∀ j, stab j ⊆ lamStar K a G) :
    unionAll (fun j => circPart (stab j)) = [] := by
  refine eq_nil_of_forall_not_mem (fun X hX => ?_)
  obtain ⟨j, hj⟩ := mem_unionAll.mp hX
  obtain ⟨hXs, hXc⟩ := List.mem_filter.mp hj
  exact lamStar_not_circ_loc hloc (hsub j hXs) hXc

/-- The prime regular demand at a locally circ-free world: `Ax^R` when
`Λ*_a` is purely atomic, the barren `⋈` otherwise.  Suppliers: the full
irregular layer at `a`. -/
def metR_prime {K : Kripke} {G : Form} {a : K.W} {C : Form}
    (hloc : circPart (lamStar K a G) = [])
    (hCp : C.isPrime) (hC : C ∈ sfR G) (hnf : ¬ K.force a C)
    (ih : ∀ A : Form, A ∈ sfR G → ¬ K.force a A → IrrWit K G a A) :
    MRWit K G a C := by
  by_cases hempty : impPart (lamStar K a G) = []
  · refine ⟨.barren, rm (gAt G) C, .axR C hCp hC, Or.inl rfl, a, K.le_refl a,
      fun hf => hnf (K.fal_force _ hf), fun X hX => ?_⟩
    have hXG := lamStar_subset_gHat hX
    simp only [gHat, List.mem_append] at hXG
    rcases hXG with (h | h) | h
    · exact mem_rm.mpr ⟨fun hc => not_mem_lamStar_of_not_force hnf (hc ▸ hX), h⟩
    · exfalso
      have hmem : X ∈ impPart (lamStar K a G) :=
        List.mem_filter.mpr ⟨hX, (List.mem_filter.mp h).2⟩
      rw [hempty] at hmem
      exact List.not_mem_nil hmem
    · exact absurd ((List.mem_filter.mp h).2)
        (fun hc => lamStar_not_circ_loc hloc hX hc)
  · have hne : upsPrime K a G ≠ [] := by
      intro hc
      refine hempty (eq_nil_of_forall_not_mem (fun X hX => ?_))
      obtain ⟨hXl, hXi⟩ := List.mem_filter.mp hX
      match X, hXi with
      | .imp A B, _ =>
          exact absurd (mem_upsPrime hXl) (by rw [hc]; exact List.not_mem_nil)
    let E := enumOf (upsPrime K a G) hne
    let f := E.f
    have hfmem : ∀ j, f j ∈ upsPrime K a G := fun j =>
      (E.spec (f j)).mp (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)
    let wit : ∀ j, IrrWit K G a (f j) := fun j =>
      ih (f j) (upsPrime_spec (hfmem j)).1 (upsPrime_spec (hfmem j)).2
    let stab := fun j => (wit j).stab
    let th := fun j => (wit j).th
    refine ⟨.barren, joinCtxAt stab th f C, ?_, Or.inl rfl, a, K.le_refl a,
      fun hf => hnf (K.fal_force _ hf), ?_⟩
    · refine .joinAt (fun j => (wit j).der) (fun i j _ X hX => (wit j).cov ((wit i).sub hX))
        (fun A B hmem => ?_) (unionAll_circPart_nil_loc hloc (fun j => (wit j).sub))
        hCp (fun hmem => ?_) hC
      · obtain ⟨i, hi⟩ := mem_unionAll.mp hmem
        exact (E.spec A).mpr (mem_upsPrime ((wit i).sub (List.mem_filter.mp hi).1))
      · obtain ⟨i, hi⟩ := mem_unionAll.mp hmem
        exact not_mem_lamStar_of_not_force hnf ((wit i).sub (List.mem_filter.mp hi).1)
    · intro X hX
      have hXG := lamStar_subset_gHat hX
      simp only [gHat, List.mem_append] at hXG
      by_cases hin : ∃ j, X ∈ stab j
      · obtain ⟨j, hj⟩ := hin
        simp only [joinCtxAt, List.mem_append]
        rcases hXG with (h | h) | h
        · exact Or.inl (Or.inl (Or.inl (mem_unionAll.mpr
            ⟨j, List.mem_filter.mpr ⟨hj, (List.mem_filter.mp h).2⟩⟩)))
        · exact Or.inl (Or.inr (mem_unionAll.mpr
            ⟨j, List.mem_filter.mpr ⟨hj, (List.mem_filter.mp h).2⟩⟩))
        · exact absurd ((List.mem_filter.mp h).2)
            (fun hc => lamStar_not_circ_loc hloc hX hc)
      · have hin' : ∀ j, X ∉ stab j := fun j hj => hin ⟨j, hj⟩
        have hallTh : ∀ j, X ∈ th j :=
          fun j => (List.mem_append.mp ((wit j).cov hX)).resolve_left (hin' j)
        simp only [joinCtxAt, List.mem_append]
        rcases hXG with (h | h) | h
        · refine Or.inl (Or.inl (Or.inr (mem_rm.mpr
            ⟨fun hc => not_mem_lamStar_of_not_force hnf (hc ▸ hX), ?_⟩)))
          exact mem_interAll.mpr (fun j =>
            List.mem_filter.mpr ⟨hallTh j, (List.mem_filter.mp h).2⟩)
        · refine Or.inr ?_
          have himp : X.isImp := (List.mem_filter.mp h).2
          match X, himp with
          | .imp A B, _ =>
              refine mem_restrict.mpr ⟨mem_interAll.mpr (fun j =>
                List.mem_filter.mpr ⟨hallTh j, rfl⟩), ?_⟩
              exact (E.spec A).mpr (mem_upsPrime hX)
        · exact absurd ((List.mem_filter.mp h).2)
            (fun hc => lamStar_not_circ_loc hloc hX hc)

/-- **The syntactic irregular ◯-cell.**  `circNotIn` over ANY tagged
`Z`-row, with the maximal `Clo`-zone of that row's context as `Θ`.
This is a full `IrrWit` for the demand at `a` whenever every
`Λ*_a`-member is `Clo`-derivable from the row's context — the
cycle-breaking route the engine's derivations of the §9 corner cells
use (an `Ax^R` row's atomic context grounds implication members through
`Clo`'s weakening clause).  No world-anchoring, no minZeta. -/
def metI_circ_syn {K : Kripke} {G : Form} {a : K.W} {Z : Form} {t : Tag}
    {Γ : List Form}
    (hgoal : Form.circ Z ∈ sfR G)
    (d : FRJr G t Γ Z)
    (htag : t = .barren ∨ ∃ W, t = .chain W ∧ Covers Γ W Z)
    (hcov : ∀ X ∈ lamStar K a G, Clo Γ X) :
    IrrWit K G a (.circ Z) where
  stab := []
  th := (gHat G).filter (fun X => cloB Γ X)
  der := .circNotIn d htag
    (fun X hX => by
      obtain ⟨hXG, hXc⟩ := List.mem_filter.mp hX
      exact ⟨cloB_iff.mp hXc, hXG⟩) hgoal
  sub := List.nil_subset _
  cov := fun X hX => List.mem_append_right _
    (List.mem_filter.mpr ⟨lamStar_subset_gHat hX, cloB_iff.mpr (hcov X hX)⟩)
  thNf := by
    simp only [nf]
    refine (List.filter_congr (fun x hx => ?_)).symm
    by_cases h : cloB Γ x = true
    · simp [List.mem_filter, hx, h]
    · simp [List.mem_filter, h]

end FRJ
