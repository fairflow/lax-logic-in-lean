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

/-- The FREE-grade regular wit: as `MRWit` but with no tag certificate.
Consumed where any tag serves (`impNotIn` premises, the root).  The
fallible joins produce these unconditionally at circ-carrying worlds. -/
structure FRWit (K : Kripke) (G : Form) (a : K.W) (C : Form) : Type where
  t : Tag
  ctx : List Form
  der : FRJr G t ctx C
  wld : K.W
  wle : K.le a wld
  wfal : ¬ K.Fal wld
  cov : lamStar K wld G ⊆ ctx

/-- Certified wits weaken to free ones. -/
def MRWit.toFree {K : Kripke} {G : Form} {a : K.W} {C : Form}
    (w : MRWit K G a C) : FRWit K G a C :=
  ⟨w.t, w.ctx, w.der, w.wld, w.wle, w.wfal, w.cov⟩

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
      FRWit K G e B) :
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

/-! ### The origin-indexed certified interface (build β2, target type)

What `circNotIn`/`circIn` consumers actually need from a certified row
is weaker than `MRWit`: the derivation, the tag certificate, and the
DEMANDING world's `Λ*` grounded through the row's context.  Requiring
the anchor's own full `Λ*`-coverage is over-specification and contains
the one provably-unsatisfiable pledge instance (docs §13). -/

/-- The origin-indexed certified wit: a tagged row grounding the
origin's `Λ*`.  No anchor fields — the anchor is dissolved into
`ground`. -/
structure OWit (K : Kripke) (G : Form) (b : K.W) (C : Form) : Type where
  t : Tag
  ctx : List Form
  der : FRJr G t ctx C
  tOK : t = .barren ∨ ∃ W, t = .chain W ∧ Covers ctx W C
  ground : ∀ X ∈ lamStar K b G, Clo ctx X

/-- Every anchored certified wit above `b` yields an origin-indexed one:
the transport `lamStar_mono` ∘ `clo_mono` is packaged once and for all.
The converse fails — `OWit` is strictly weaker, which is the point. -/
def MRWit.toOWit {K : Kripke} {G : Form} {b : K.W} {C : Form}
    (w : MRWit K G b C) : OWit K G b C :=
  ⟨w.t, w.ctx, w.der, w.tOK,
    fun X hX => clo_mono w.cov (lamStar_mono w.wfal w.wle X hX)⟩

/-- `metI_circ` against the corrected interface: the irregular ◯-demand
from an origin-indexed `Z`-wit.  Subsumes `metI_circ` (via `toOWit`)
and `metI_circ_syn` (an `OWit` with syntactic ground). -/
def metI_circO {K : Kripke} {G : Form} {b : K.W} {Z : Form}
    (hgoal : Form.circ Z ∈ sfR G)
    (w : OWit K G b Z) : IrrWit K G b (.circ Z) where
  stab := []
  th := nf G (lamStar K b G)
  der := .circNotIn w.der w.tOK
    (fun X hX => ⟨w.ground X (mem_nf.mp hX).2, (mem_nf.mp hX).1⟩) hgoal
  sub := List.nil_subset _
  cov := fun X hX =>
    List.mem_append_right _ (mem_nf.mpr ⟨lamStar_subset_gHat hX, hX⟩)
  thNf := nf_idem.symm

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

/-- The `∨`-regular demand at a locally circ-free world: the barren
`⋈^∨` over the two disjunct cells and the prime Υ-family. -/
def metR_or {K : Kripke} {G : Form} {a : K.W} {C₁ C₂ : Form}
    (hloc : circPart (lamStar K a G) = [])
    (hC : Form.or C₁ C₂ ∈ sfR G) (hnf : ¬ K.force a (.or C₁ C₂))
    (ih : ∀ A : Form, A ∈ sfR G → ¬ K.force a A → IrrWit K G a A) :
    MRWit K G a (.or C₁ C₂) := by
  have hn1 : ¬ K.force a C₁ := fun hc => hnf (Or.inl hc)
  have hn2 : ¬ K.force a C₂ := fun hc => hnf (Or.inr hc)
  let U := C₁ :: C₂ :: upsPrime K a G
  let E := enumOf U (by simp [U])
  let f := E.f
  have hfmem : ∀ j, f j ∈ U := fun j =>
    (E.spec (f j)).mp (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)
  let wit : ∀ j, IrrWit K G a (f j) := fun j =>
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
  refine ⟨.barren, joinCtxOr stab th f, ?_, Or.inl rfl, a, K.le_refl a,
    fun hf => hnf (K.fal_force _ hf), ?_⟩
  · refine .joinOr (fun j => (wit j).der) (fun i j _ X hX => (wit j).cov ((wit i).sub hX))
      (fun A B hmem => ?_) (unionAll_circPart_nil_loc hloc (fun j => (wit j).sub))
      ⟨?_, ?_⟩ hC
    · obtain ⟨i, hi⟩ := mem_unionAll.mp hmem
      exact (E.spec A).mpr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (mem_upsPrime ((wit i).sub (List.mem_filter.mp hi).1))))
    · exact (E.spec C₁).mpr List.mem_cons_self
    · exact (E.spec C₂).mpr (List.mem_cons_of_mem _ List.mem_cons_self)
  · intro X hX
    have hXG := lamStar_subset_gHat hX
    simp only [gHat, List.mem_append] at hXG
    by_cases hin : ∃ j, X ∈ stab j
    · obtain ⟨j, hj⟩ := hin
      simp only [joinCtxOr, List.mem_append]
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
      simp only [joinCtxOr, List.mem_append]
      rcases hXG with (h | h) | h
      · exact Or.inl (Or.inl (Or.inr (mem_interAll.mpr (fun j =>
          List.mem_filter.mpr ⟨hallTh j, (List.mem_filter.mp h).2⟩))))
      · refine Or.inr ?_
        have himp : X.isImp := (List.mem_filter.mp h).2
        match X, himp with
        | .imp A B, _ =>
            refine mem_restrict.mpr ⟨mem_interAll.mpr (fun j =>
              List.mem_filter.mpr ⟨hallTh j, rfl⟩), ?_⟩
            exact (E.spec A).mpr (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ (mem_upsPrime hX)))
      · exact absurd ((List.mem_filter.mp h).2)
          (fun hc => lamStar_not_circ_loc hloc hX hc)

/-! ### The promise-mode joins (build γ): circ-carrying worlds

`Λ*`-circs must be retained (their bodies are unforced, so no `Clo`
route exists) and the barren joins have no θ-circ zone, so circ-carrying
worlds need `joinAtP`/`joinOrP`.  A tOK-consumable promise row must
pledge the goal itself (`Covers` at a prime or `∨`-goal admits only
`refl`), which fixes the supply: a component family for the goal over
the demanding world's modal cone. -/

/-- A pledge family for goal `F` at world `a`: components deriving `F`
with admissible tags, whose contexts `Clo`-contain `Λ*_a` (hence hJ7s
and the stable zones) and some member of which grounds each
`Λ*`-circ-body (hence hJ5 and the θ-circ restriction). -/
structure PledgeFam (K : Kripke) (G : Form) (a : K.W) (F : Form) : Type where
  k : Nat
  tps : Fin (k + 1) → Tag
  Δs : Fin (k + 1) → List Form
  dps : ∀ i, FRJr G (tps i) (Δs i) F
  htps : ∀ i, tps i = .barren ∨ ∃ W, tps i = .chain W ∧ Covers (Δs i) W F
  hlam : ∀ i, ∀ X ∈ lamStar K a G, Clo (Δs i) X
  hbody : ∀ Y : Form, Form.circ Y ∈ lamStar K a G → ∃ i, Clo (Δs i) Y

/-- **The second named supply**: pledge families at circ-carrying
worlds, for prime and disjunctive demands. -/
def PledgeSupply (K : Kripke) (G : Form) : Type :=
  ∀ a : K.W, ∀ F : Form, F ∈ sfR G → ¬ K.force a F →
    circPart (lamStar K a G) ≠ [] → PledgeFam K G a F

/-- The prime regular demand at a circ-carrying world: the promise
`⋈^At,p`, pledging the goal. -/
def metR_primeP {K : Kripke} {G : Form} {a : K.W} {C : Form}
    (pf : PledgeFam K G a C)
    (hCp : C.isPrime) (hC : C ∈ sfR G) (hnf : ¬ K.force a C)
    (ih : ∀ A : Form, A ∈ sfR G → ¬ K.force a A → IrrWit K G a A) :
    MRWit K G a C := by
  let U := C :: upsPrime K a G
  let E := enumOf U (by simp [U])
  let f := E.f
  have hfmem : ∀ j, f j ∈ U := fun j =>
    (E.spec (f j)).mp (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)
  let wit : ∀ j, IrrWit K G a (f j) := fun j =>
    if h1 : f j = C then by rw [h1]; exact ih C hC hnf
    else
      have hm : f j ∈ upsPrime K a G := by
        rcases List.mem_cons.mp (hfmem j) with h | h
        · exact absurd h h1
        · exact h
      ih (f j) (upsPrime_spec hm).1 (upsPrime_spec hm).2
  let stab := fun j => (wit j).stab
  let th := fun j => (wit j).th
  refine ⟨.chain C, joinCtxAtP stab th f C pf.Δs, ?_,
    Or.inr ⟨C, rfl, .refl⟩, a, K.le_refl a,
    fun hf => hnf (K.fal_force _ hf), ?_⟩
  · refine .joinAtP (Ds := fun _ => C) (fun j => (wit j).der) pf.dps
      (fun i j _ X hX => (wit j).cov ((wit i).sub hX))
      (fun A B hmem => ?_)
      (fun Y hmem => ?_)
      (fun i j X hX => pf.hlam i X ((wit j).sub hX))
      (Or.inr ⟨rfl, fun i => ⟨rfl, pf.htps i⟩⟩)
      hCp (fun hmem => ?_) hC
    · obtain ⟨i, hi⟩ := mem_unionAll.mp hmem
      exact (E.spec A).mpr (List.mem_cons_of_mem _
        (mem_upsPrime ((wit i).sub (List.mem_filter.mp hi).1)))
    · obtain ⟨i, hi⟩ := mem_unionAll.mp hmem
      exact pf.hbody Y ((wit i).sub (List.mem_filter.mp hi).1)
    · obtain ⟨i, hi⟩ := mem_unionAll.mp hmem
      exact not_mem_lamStar_of_not_force hnf ((wit i).sub (List.mem_filter.mp hi).1)
  · intro X hX
    refine mem_restrictP.mpr ⟨?_, fun i => pf.hlam i X hX⟩
    have hXG := lamStar_subset_gHat hX
    simp only [gHat, List.mem_append] at hXG
    by_cases hin : ∃ j, X ∈ stab j
    · obtain ⟨j, hj⟩ := hin
      rcases hXG with (h | h) | h
      · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_left _ (mem_unionAll.mpr
            ⟨j, List.mem_filter.mpr ⟨hj, (List.mem_filter.mp h).2⟩⟩))))
      · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
          (mem_unionAll.mpr ⟨j, List.mem_filter.mpr ⟨hj, (List.mem_filter.mp h).2⟩⟩)))
      · exact List.mem_append_right _ (List.mem_append_left _ (mem_unionAll.mpr
          ⟨j, List.mem_filter.mpr ⟨hj, (List.mem_filter.mp h).2⟩⟩))
    · have hin' : ∀ j, X ∉ stab j := fun j hj => hin ⟨j, hj⟩
      have hallTh : ∀ j, X ∈ th j :=
        fun j => (List.mem_append.mp ((wit j).cov hX)).resolve_left (hin' j)
      rcases hXG with (h | h) | h
      · refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_right _ (mem_rm.mpr
            ⟨fun hc => not_mem_lamStar_of_not_force hnf (hc ▸ hX), ?_⟩))))
        exact mem_interAll.mpr (fun j =>
          List.mem_filter.mpr ⟨hallTh j, (List.mem_filter.mp h).2⟩)
      · refine List.mem_append_left _ (List.mem_append_right _ ?_)
        have himp : X.isImp := (List.mem_filter.mp h).2
        match X, himp with
        | .imp A B, _ =>
            refine mem_restrict.mpr ⟨mem_interAll.mpr (fun j =>
              List.mem_filter.mpr ⟨hallTh j, rfl⟩), ?_⟩
            exact (E.spec A).mpr (List.mem_cons_of_mem _ (mem_upsPrime hX))
      · refine List.mem_append_right _ (List.mem_append_right _ ?_)
        have hcirc : X.isCirc := (List.mem_filter.mp h).2
        match X, hcirc with
        | .circ Y, _ =>
            refine mem_restrictC.mpr ⟨mem_interAll.mpr (fun j =>
              List.mem_filter.mpr ⟨hallTh j, rfl⟩), pf.hbody Y hX⟩

/-- The `∨`-regular demand at a circ-carrying world: the promise
`⋈^∨,p`, pledging the disjunction itself. -/
def metR_orP {K : Kripke} {G : Form} {a : K.W} {C₁ C₂ : Form}
    (pf : PledgeFam K G a (.or C₁ C₂))
    (hC : Form.or C₁ C₂ ∈ sfR G) (hnf : ¬ K.force a (.or C₁ C₂))
    (ih : ∀ A : Form, A ∈ sfR G → ¬ K.force a A → IrrWit K G a A) :
    MRWit K G a (.or C₁ C₂) := by
  have hn1 : ¬ K.force a C₁ := fun hc => hnf (Or.inl hc)
  have hn2 : ¬ K.force a C₂ := fun hc => hnf (Or.inr hc)
  let U := C₁ :: C₂ :: upsPrime K a G
  let E := enumOf U (by simp [U])
  let f := E.f
  have hfmem : ∀ j, f j ∈ U := fun j =>
    (E.spec (f j)).mp (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)
  let wit : ∀ j, IrrWit K G a (f j) := fun j =>
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
  refine ⟨.chain (.or C₁ C₂), joinCtxOrP stab th f pf.Δs, ?_,
    Or.inr ⟨.or C₁ C₂, rfl, .refl⟩, a, K.le_refl a,
    fun hf => hnf (K.fal_force _ hf), ?_⟩
  · refine .joinOrP (Ds := fun _ => .or C₁ C₂) (fun j => (wit j).der) pf.dps
      (fun i j _ X hX => (wit j).cov ((wit i).sub hX))
      (fun A B hmem => ?_)
      (fun Y hmem => ?_)
      (fun i j X hX => pf.hlam i X ((wit j).sub hX))
      (Or.inr ⟨rfl, fun i => ⟨rfl, pf.htps i⟩⟩)
      ⟨?_, ?_⟩ hC
    · obtain ⟨i, hi⟩ := mem_unionAll.mp hmem
      exact (E.spec A).mpr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (mem_upsPrime ((wit i).sub (List.mem_filter.mp hi).1))))
    · obtain ⟨i, hi⟩ := mem_unionAll.mp hmem
      exact pf.hbody Y ((wit i).sub (List.mem_filter.mp hi).1)
    · exact (E.spec C₁).mpr List.mem_cons_self
    · exact (E.spec C₂).mpr (List.mem_cons_of_mem _ List.mem_cons_self)
  · intro X hX
    refine mem_restrictP.mpr ⟨?_, fun i => pf.hlam i X hX⟩
    have hXG := lamStar_subset_gHat hX
    simp only [gHat, List.mem_append] at hXG
    by_cases hin : ∃ j, X ∈ stab j
    · obtain ⟨j, hj⟩ := hin
      rcases hXG with (h | h) | h
      · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_left _ (mem_unionAll.mpr
            ⟨j, List.mem_filter.mpr ⟨hj, (List.mem_filter.mp h).2⟩⟩))))
      · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
          (mem_unionAll.mpr ⟨j, List.mem_filter.mpr ⟨hj, (List.mem_filter.mp h).2⟩⟩)))
      · exact List.mem_append_right _ (List.mem_append_left _ (mem_unionAll.mpr
          ⟨j, List.mem_filter.mpr ⟨hj, (List.mem_filter.mp h).2⟩⟩))
    · have hin' : ∀ j, X ∉ stab j := fun j hj => hin ⟨j, hj⟩
      have hallTh : ∀ j, X ∈ th j :=
        fun j => (List.mem_append.mp ((wit j).cov hX)).resolve_left (hin' j)
      rcases hXG with (h | h) | h
      · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_right _ (mem_interAll.mpr (fun j =>
            List.mem_filter.mpr ⟨hallTh j, (List.mem_filter.mp h).2⟩)))))
      · refine List.mem_append_left _ (List.mem_append_right _ ?_)
        have himp : X.isImp := (List.mem_filter.mp h).2
        match X, himp with
        | .imp A B, _ =>
            refine mem_restrict.mpr ⟨mem_interAll.mpr (fun j =>
              List.mem_filter.mpr ⟨hallTh j, rfl⟩), ?_⟩
            exact (E.spec A).mpr (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ (mem_upsPrime hX)))
      · refine List.mem_append_right _ (List.mem_append_right _ ?_)
        have hcirc : X.isCirc := (List.mem_filter.mp h).2
        match X, hcirc with
        | .circ Y, _ =>
            refine mem_restrictC.mpr ⟨mem_interAll.mpr (fun j =>
              List.mem_filter.mpr ⟨hallTh j, rfl⟩), pf.hbody Y hX⟩


/-- Free-grade `∧`-threading (no tag lift needed). -/
def metR_andF {K : Kripke} {G : Form} {a : K.W} {C₁ C₂ : Form}
    (hC : Form.and C₁ C₂ ∈ sfR G) (hnf : ¬ K.force a (.and C₁ C₂))
    (sup₁ : ¬ K.force a C₁ → FRWit K G a C₁)
    (sup₂ : K.force a C₁ → ¬ K.force a C₂ → FRWit K G a C₂) :
    FRWit K G a (.and C₁ C₂) :=
  if h1 : K.force a C₁ then
    let w := sup₂ h1 (fun hc => hnf ⟨h1, hc⟩)
    ⟨w.t, w.ctx, .andR2 w.der hC, w.wld, w.wle, w.wfal, w.cov⟩
  else
    let w := sup₁ h1
    ⟨w.t, w.ctx, .andR1 w.der hC, w.wld, w.wle, w.wfal, w.cov⟩

/-- Free-grade `⊃`-threading. -/
def metR_impF {K : Kripke} {G : Form} {a : K.W} {A B : Form}
    (hC : Form.imp A B ∈ sfR G) (hnf : ¬ K.force a (.imp A B))
    (sup : ∀ e : K.W, K.le a e → K.force e A → ¬ K.force e B →
      FRWit K G e B) :
    FRWit K G a (.imp A B) :=
  let m := minEta hnf
  let w := sup m.e m.le m.fA m.nfB
  let hAclo : Clo w.ctx A :=
    clo_mono w.cov (mem_clo_lamStar w.wfal (sfR_imp hC).1 (K.force_mono w.wle m.fA))
  ⟨w.t, w.ctx, .impIn w.der hAclo hC, w.wld, K.le_trans m.le w.wle, w.wfal, w.cov⟩

/-- The prime regular demand at a circ-carrying world, FREE grade: the
FALLIBLE `⋈^At,⊥`, whose conclusion keeps the whole modal zone with no
side condition — no pledge needed. -/
def metR_primeF {K : Kripke} {G : Form} {a : K.W} {C : Form}
    (hCp : C.isPrime) (hC : C ∈ sfR G) (hnf : ¬ K.force a C)
    (ih : ∀ A : Form, A ∈ sfR G → ¬ K.force a A → IrrWit K G a A) :
    FRWit K G a C := by
  let U := C :: upsPrime K a G
  let E := enumOf U (by simp [U])
  let f := E.f
  have hfmem : ∀ j, f j ∈ U := fun j =>
    (E.spec (f j)).mp (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)
  let wit : ∀ j, IrrWit K G a (f j) := fun j =>
    if h1 : f j = C then by rw [h1]; exact ih C hC hnf
    else
      have hm : f j ∈ upsPrime K a G := by
        rcases List.mem_cons.mp (hfmem j) with h | h
        · exact absurd h h1
        · exact h
      ih (f j) (upsPrime_spec hm).1 (upsPrime_spec hm).2
  let stab := fun j => (wit j).stab
  let th := fun j => (wit j).th
  refine ⟨.blocked, joinCtxAtF stab th f C, ?_, a, K.le_refl a,
    fun hf => hnf (K.fal_force _ hf), ?_⟩
  · refine .joinAtF (fun j => (wit j).der)
      (fun i j _ X hX => (wit j).cov ((wit i).sub hX))
      (fun A B hmem => ?_) hCp (fun hmem => ?_) hC
    · obtain ⟨i, hi⟩ := mem_unionAll.mp hmem
      exact (E.spec A).mpr (List.mem_cons_of_mem _
        (mem_upsPrime ((wit i).sub (List.mem_filter.mp hi).1)))
    · obtain ⟨i, hi⟩ := mem_unionAll.mp hmem
      exact not_mem_lamStar_of_not_force hnf ((wit i).sub (List.mem_filter.mp hi).1)
  · intro X hX
    have hXG := lamStar_subset_gHat hX
    simp only [gHat, List.mem_append] at hXG
    by_cases hin : ∃ j, X ∈ stab j
    · obtain ⟨j, hj⟩ := hin
      rcases hXG with (h | h) | h
      · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_left _ (mem_unionAll.mpr
            ⟨j, List.mem_filter.mpr ⟨hj, (List.mem_filter.mp h).2⟩⟩))))
      · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
          (mem_unionAll.mpr ⟨j, List.mem_filter.mpr ⟨hj, (List.mem_filter.mp h).2⟩⟩)))
      · exact List.mem_append_right _ (List.mem_append_left _ (mem_unionAll.mpr
          ⟨j, List.mem_filter.mpr ⟨hj, (List.mem_filter.mp h).2⟩⟩))
    · have hin' : ∀ j, X ∉ stab j := fun j hj => hin ⟨j, hj⟩
      have hallTh : ∀ j, X ∈ th j :=
        fun j => (List.mem_append.mp ((wit j).cov hX)).resolve_left (hin' j)
      rcases hXG with (h | h) | h
      · refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_right _ (mem_rm.mpr
            ⟨fun hc => not_mem_lamStar_of_not_force hnf (hc ▸ hX), ?_⟩))))
        exact mem_interAll.mpr (fun j =>
          List.mem_filter.mpr ⟨hallTh j, (List.mem_filter.mp h).2⟩)
      · refine List.mem_append_left _ (List.mem_append_right _ ?_)
        have himp : X.isImp := (List.mem_filter.mp h).2
        match X, himp with
        | .imp A B, _ =>
            refine mem_restrict.mpr ⟨mem_interAll.mpr (fun j =>
              List.mem_filter.mpr ⟨hallTh j, rfl⟩), ?_⟩
            exact (E.spec A).mpr (List.mem_cons_of_mem _ (mem_upsPrime hX))
      · exact List.mem_append_right _ (List.mem_append_right _
          (mem_interAll.mpr (fun j =>
            List.mem_filter.mpr ⟨hallTh j, (List.mem_filter.mp h).2⟩)))

/-- The `∨`-regular demand at a circ-carrying world, FREE grade: the
fallible `⋈^∨,⊥`. -/
def metR_orF {K : Kripke} {G : Form} {a : K.W} {C₁ C₂ : Form}
    (hC : Form.or C₁ C₂ ∈ sfR G) (hnf : ¬ K.force a (.or C₁ C₂))
    (ih : ∀ A : Form, A ∈ sfR G → ¬ K.force a A → IrrWit K G a A) :
    FRWit K G a (.or C₁ C₂) := by
  have hn1 : ¬ K.force a C₁ := fun hc => hnf (Or.inl hc)
  have hn2 : ¬ K.force a C₂ := fun hc => hnf (Or.inr hc)
  let U := C₁ :: C₂ :: upsPrime K a G
  let E := enumOf U (by simp [U])
  let f := E.f
  have hfmem : ∀ j, f j ∈ U := fun j =>
    (E.spec (f j)).mp (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)
  let wit : ∀ j, IrrWit K G a (f j) := fun j =>
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
  refine ⟨.blocked, joinCtxOrF stab th f, ?_, a, K.le_refl a,
    fun hf => hnf (K.fal_force _ hf), ?_⟩
  · refine .joinOrF (fun j => (wit j).der)
      (fun i j _ X hX => (wit j).cov ((wit i).sub hX))
      (fun A B hmem => ?_) ⟨?_, ?_⟩ hC
    · obtain ⟨i, hi⟩ := mem_unionAll.mp hmem
      exact (E.spec A).mpr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (mem_upsPrime ((wit i).sub (List.mem_filter.mp hi).1))))
    · exact (E.spec C₁).mpr List.mem_cons_self
    · exact (E.spec C₂).mpr (List.mem_cons_of_mem _ List.mem_cons_self)
  · intro X hX
    have hXG := lamStar_subset_gHat hX
    simp only [gHat, List.mem_append] at hXG
    by_cases hin : ∃ j, X ∈ stab j
    · obtain ⟨j, hj⟩ := hin
      rcases hXG with (h | h) | h
      · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_left _ (mem_unionAll.mpr
            ⟨j, List.mem_filter.mpr ⟨hj, (List.mem_filter.mp h).2⟩⟩))))
      · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
          (mem_unionAll.mpr ⟨j, List.mem_filter.mpr ⟨hj, (List.mem_filter.mp h).2⟩⟩)))
      · exact List.mem_append_right _ (List.mem_append_left _ (mem_unionAll.mpr
          ⟨j, List.mem_filter.mpr ⟨hj, (List.mem_filter.mp h).2⟩⟩))
    · have hin' : ∀ j, X ∉ stab j := fun j hj => hin ⟨j, hj⟩
      have hallTh : ∀ j, X ∈ th j :=
        fun j => (List.mem_append.mp ((wit j).cov hX)).resolve_left (hin' j)
      rcases hXG with (h | h) | h
      · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_right _ (mem_interAll.mpr (fun j =>
            List.mem_filter.mpr ⟨hallTh j, (List.mem_filter.mp h).2⟩)))))
      · refine List.mem_append_left _ (List.mem_append_right _ ?_)
        have himp : X.isImp := (List.mem_filter.mp h).2
        match X, himp with
        | .imp A B, _ =>
            refine mem_restrict.mpr ⟨mem_interAll.mpr (fun j =>
              List.mem_filter.mpr ⟨hallTh j, rfl⟩), ?_⟩
            exact (E.spec A).mpr (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ (mem_upsPrime hX)))
      · exact List.mem_append_right _ (List.mem_append_right _
          (mem_interAll.mpr (fun j =>
            List.mem_filter.mpr ⟨hallTh j, (List.mem_filter.mp h).2⟩)))

/-! ## The gluing (slice 3)

The visit that assembles the builders.  Measure `(ht, t, size)` — the
paper's own, irregular-before-regular.  Every builder edge is legal:
the Υ-edges drop phase, the floats drop height (`metI_imp` records
`e ≠ a`; `minZetaNS` prefers a non-self candidate), the in-layer edges
drop size.  The single un-orderable edge — the irregular ◯-demand at a
world that is its own sole minZeta candidate — is discharged by an
explicit supply (`CircSupply`), which is thereby THE open kernel of
FRJ◯ completeness. -/

/-- Anchor weakening: a wit for a demand at `b` serves any `a ≤ b`. -/
def MRWit.weaken {K : Kripke} {G : Form} {a b : K.W} {C : Form}
    (hab : K.le a b) (w : MRWit K G b C) : MRWit K G a C :=
  ⟨w.t, w.ctx, w.der, w.tOK, w.wld, K.le_trans hab w.wle, w.wfal, w.cov⟩

/-- minZeta with the opposite preference: a NON-self candidate whenever
one exists, and a soleness certificate when the pick is `a` itself. -/
structure MinZetaNS (K : Kripke) (a : K.W) (Z : Form) : Type where
  e : K.W
  le : K.le a e
  cone : ∀ v, K.Rm e v → ¬ K.force v Z
  sole : e = a → ∀ u, K.le a u → (∀ v, K.Rm u v → ¬ K.force v Z) → u = a

def minZetaNS {K : Kripke} {a : K.W} {Z : Form}
    (h : ¬ K.force a (.circ Z)) : MinZetaNS K a Z :=
  match hc : (zetaCand K a Z).filter (fun u => decide (¬(u = a))) with
  | u :: _ =>
      have hu : u ∈ (zetaCand K a Z).filter (fun u => decide (¬(u = a))) := by
        rw [hc]; exact List.mem_cons_self
      have hz := mem_zetaCand.mp (List.mem_filter.mp hu).1
      { e := u, le := hz.1, cone := hz.2
        sole := fun hea => by
          exfalso
          have : ¬ (u = a) := by
            have := (List.mem_filter.mp hu).2
            simpa using this
          exact this hea }
  | [] =>
      let mz := minZeta h
      { e := mz.e, le := mz.le, cone := mz.cone
        sole := fun _ u hu hcone => by
          by_contra hne
          have hmem : u ∈ (zetaCand K a Z).filter (fun u => decide (¬(u = a))) :=
            List.mem_filter.mpr ⟨mem_zetaCand.mpr ⟨hu, hcone⟩, by simpa using hne⟩
          rw [hc] at hmem
          exact List.not_mem_nil hmem }

/-- A `Z`-refuting anchor above `a`, preferring a PROPER one; when the
pick is `a` itself, a certificate that every proper extension forces
`Z`.  (`a ⊮ ◯Z` gives `a ⊮ Z`, so `a` is always available.) -/
structure MinRef (K : Kripke) (a : K.W) (Z : Form) : Type where
  e : K.W
  le : K.le a e
  nfZ : ¬ K.force e Z
  sole : e = a → ∀ u, K.le a u → u ≠ a → K.force u Z

def minRef {K : Kripke} {a : K.W} {Z : Form}
    (h : ¬ K.force a Z) : MinRef K a Z :=
  match hc : K.elems.filter
      (fun u => decide (K.le a u ∧ ¬(u = a) ∧ ¬ K.force u Z)) with
  | u :: _ =>
      have hu : u ∈ K.elems.filter
          (fun u => decide (K.le a u ∧ ¬(u = a) ∧ ¬ K.force u Z)) := by
        rw [hc]; exact List.mem_cons_self
      have hz : K.le a u ∧ ¬(u = a) ∧ ¬ K.force u Z := by
        have := (List.mem_filter.mp hu).2
        simpa using this
      { e := u, le := hz.1, nfZ := hz.2.2
        sole := fun hea => absurd hea hz.2.1 }
  | [] =>
      { e := a, le := K.le_refl a, nfZ := h
        sole := fun _ u hu hne => by
          by_contra hnf
          have hmem : u ∈ K.elems.filter
              (fun u => decide (K.le a u ∧ ¬(u = a) ∧ ¬ K.force u Z)) :=
            List.mem_filter.mpr ⟨K.complete u, by simp [hu, hne, hnf]⟩
          rw [hc] at hmem
          exact List.not_mem_nil hmem }

/-- **The open kernel of FRJ◯ completeness**: supply for the irregular
◯-demand at a world every proper extension of which forces the body.
(This entails `cone(a) = {a}` and that `a` is the sole minZeta
candidate; it is the weakest corner the visit cannot route around.)
The `IrrWit` may be produced by any route — `metI_circ_syn` over a
tagged grounding row, or the generalised `Ax^I◯` at maximal worlds
(`circWit_of_maximal` below). -/
def CircSupply (K : Kripke) (G : Form) : Type :=
  ∀ a : K.W, ∀ Z : Form, Form.circ Z ∈ sfR G → ¬ K.force a (.circ Z) →
    (∀ u, K.le a u → u ≠ a → K.force u Z) →
    IrrWit K G a (.circ Z)

/-- The statement family: `t = 0` the irregular wit, else the regular. -/
def SatStmt (K : Kripke) (G : Form) (a : K.W) (t : Nat) (C : Form) : Type :=
  match t with
  | 0 => IrrWit K G a C
  | 1 => MRWit K G a C
  | _ + 2 => FRWit K G a C

/-- **The visit.**  Well-founded on `(ht, t, size)`; total given the two
named conditions (`hloc`: `Λ*` circ-free at every world, so the barren
joins suffice; `hsup`: the sole-candidate supply). -/
def visit (K : Kripke) (G : Form)
    (psup : PledgeSupply K G)
    (hsup : CircSupply K G)
    (a : K.W) (t : Nat) (C : Form)
    (hC : C ∈ sfR G) (hnf : ¬ K.force a C) : SatStmt K G a t C := by
  match t, C with
  | 0, .atom p => exact metI_atom hC hnf
  | 0, .bot => exact metI_bot hC hnf
  | 0, .and C₁ C₂ =>
      exact metI_and hC hnf
        (fun h1 => visit K G psup hsup a 0 C₁ (sfR_and hC).1 h1)
        (fun _ h2 => visit K G psup hsup a 0 C₂ (sfR_and hC).2 h2)
  | 0, .or C₁ C₂ =>
      exact metI_or hC hnf
        (fun h1 => visit K G psup hsup a 0 C₁ (sfR_or hC).1 h1)
        (fun h2 => visit K G psup hsup a 0 C₂ (sfR_or hC).2 h2)
  | 0, .imp A B =>
      exact metI_imp hC hnf
        (fun _ hB => visit K G psup hsup a 0 B (sfR_imp hC).2 hB)
        (fun e _ hne _ hB => visit K G psup hsup e 2 B (sfR_imp hC).2 hB)
  | 0, .circ Z =>
      have hnfZ : ¬ K.force a Z := fun hf => hnf (fun b hab =>
        ⟨b, K.rm_refl b, K.force_mono hab hf⟩)
      let mr := minRef hnfZ
      by_cases hea : mr.e = a
      · exact hsup a Z hC hnf (mr.sole hea)
      · exact metI_circ hC
          ((visit K G psup hsup mr.e 1 Z (sfR_circ hC) mr.nfZ).weaken mr.le)
  | 1, .atom p =>
      by_cases hloc : circPart (lamStar K a G) = []
      · exact metR_prime hloc rfl hC hnf
          (fun A hA hnA => visit K G psup hsup a 0 A hA hnA)
      · exact metR_primeP (psup a _ hC hnf hloc) rfl hC hnf
          (fun A hA hnA => visit K G psup hsup a 0 A hA hnA)
  | 1, .bot =>
      by_cases hloc : circPart (lamStar K a G) = []
      · exact metR_prime hloc rfl hC hnf
          (fun A hA hnA => visit K G psup hsup a 0 A hA hnA)
      · exact metR_primeP (psup a _ hC hnf hloc) rfl hC hnf
          (fun A hA hnA => visit K G psup hsup a 0 A hA hnA)
  | 1, .and C₁ C₂ =>
      exact metR_and hC hnf
        (fun h1 => visit K G psup hsup a 1 C₁ (sfR_and hC).1 h1)
        (fun _ h2 => visit K G psup hsup a 1 C₂ (sfR_and hC).2 h2)
  | 1, .or C₁ C₂ =>
      by_cases hloc : circPart (lamStar K a G) = []
      · exact metR_or hloc hC hnf
          (fun A hA hnA => visit K G psup hsup a 0 A hA hnA)
      · exact metR_orP (psup a _ hC hnf hloc) hC hnf
          (fun A hA hnA => visit K G psup hsup a 0 A hA hnA)
  | 1, .imp A B =>
      exact metR_imp hC hnf
        (fun e hle _ hB => visit K G psup hsup e 1 B (sfR_imp hC).2 hB)
  | 1, .circ Z =>
      exact metR_circ hC hnf
        (fun e hle hZ => visit K G psup hsup e 1 Z (sfR_circ hC) hZ)
  | n + 2, .atom p =>
      by_cases hloc : circPart (lamStar K a G) = []
      · exact (metR_prime hloc rfl hC hnf
          (fun A hA hnA => visit K G psup hsup a 0 A hA hnA)).toFree
      · exact metR_primeF rfl hC hnf
          (fun A hA hnA => visit K G psup hsup a 0 A hA hnA)
  | n + 2, .bot =>
      by_cases hloc : circPart (lamStar K a G) = []
      · exact (metR_prime hloc rfl hC hnf
          (fun A hA hnA => visit K G psup hsup a 0 A hA hnA)).toFree
      · exact metR_primeF rfl hC hnf
          (fun A hA hnA => visit K G psup hsup a 0 A hA hnA)
  | n + 2, .and C₁ C₂ =>
      exact metR_andF hC hnf
        (fun h1 => visit K G psup hsup a (n + 2) C₁ (sfR_and hC).1 h1)
        (fun _ h2 => visit K G psup hsup a (n + 2) C₂ (sfR_and hC).2 h2)
  | n + 2, .or C₁ C₂ =>
      by_cases hloc : circPart (lamStar K a G) = []
      · exact (metR_or hloc hC hnf
          (fun A hA hnA => visit K G psup hsup a 0 A hA hnA)).toFree
      · exact metR_orF hC hnf
          (fun A hA hnA => visit K G psup hsup a 0 A hA hnA)
  | n + 2, .imp A B =>
      exact metR_impF hC hnf
        (fun e hle _ hB => visit K G psup hsup e (n + 2) B (sfR_imp hC).2 hB)
  | n + 2, .circ Z =>
      exact (visit K G psup hsup a 1 (.circ Z) hC hnf).toFree
termination_by (ht K a, t, C.size)
decreasing_by
  all_goals
    first
      | (apply Prod.Lex.left
         exact ht_lt (by assumption) (by assumption))
      | (by_cases hne' : e = a
         · subst hne'
           apply Prod.Lex.right
           apply Prod.Lex.right
           simp only [Form.size]; omega
         · apply Prod.Lex.left
           exact ht_lt (by assumption) hne')
      | (apply Prod.Lex.left
         exact ht_lt mr.le hea)
      | (apply Prod.Lex.right
         apply Prod.Lex.left
         omega)
      | (apply Prod.Lex.right
         apply Prod.Lex.right
         first
           | omega
           | (simp only [Form.size]; omega))

/-- **`AllMet` from the two named supplies.** -/
theorem allMet_of_supply {K : Kripke} {G : Form}
    (psup : PledgeSupply K G)
    (hsup : CircSupply K G) : AllMet K G :=
  fun a C hC hnf =>
    ⟨⟨visit K G psup hsup a 0 C hC hnf⟩, ⟨visit K G psup hsup a 1 C hC hnf⟩⟩

/-- **FRJ◯ completeness, modulo the two supplies**: statement (A) for
every model providing pledge families at circ-carrying worlds and the
sole-candidate ◯-supply.  (Docstring corrected 2026-08-17: an earlier
version of this theorem took world-wise circ-freeness in place of
`PledgeSupply`.) -/
theorem completeness_of_supply {K : Kripke} {G : Form}
    (psup : PledgeSupply K G)
    (hsup : CircSupply K G)
    (hK : ¬ K.valid G) : Provable G :=
  completeness_of_allMet (allMet_of_supply psup hsup) hK

/-- World-wise circ-free `Λ*` discharges the pledge supply vacuously. -/
def pledgeSupply_of_locFree {K : Kripke} {G : Form}
    (hloc : ∀ b : K.W, circPart (lamStar K b G) = []) :
    PledgeSupply K G :=
  fun a _ _ _ hne => absurd (hloc a) hne

/-! ### Discharging the kernel at maximal worlds

At a `≤`-maximal infallible world forcing is classical, with the
polarity split doing the bookkeeping between the two subformula sets:
left subformulas carry forcing INTO the classical valuation, right
subformulas carry it back.  The generalised `Ax^I◯` then discharges the
sole-candidate supply outright: the vacuous zone of the world's own
classical theory contains `Λ*_a`, and the side condition
`classForce ats Z = false` is exactly `a ⊮ Z`. -/

/-- The classical valuation of a world: its forced `Ĝ`-atoms. -/
def clAts (K : Kripke) (G : Form) (a : K.W) : List Form :=
  (gAt G).filter (fun q => decide (K.force a q))

theorem clAts_subset {K : Kripke} {G : Form} {a : K.W} :
    clAts K G a ⊆ gAt G := fun _ h => (List.mem_filter.mp h).1

/-- The polarity-split classical correspondence at a maximal infallible
world. -/
theorem force_classForce {K : Kripke} {G : Form} {a : K.W}
    (hmax : ∀ u, K.le a u → u = a) (hinf : ¬ K.Fal a) :
    ∀ X : Form,
      (X ∈ sfL G → K.force a X → classForce (clAts K G a) X = true) ∧
      (X ∈ sfR G → classForce (clAts K G a) X = true → K.force a X) := by
  intro X
  induction X with
  | atom p =>
      constructor
      · intro hL hf
        simp only [classForce, decide_eq_true_eq]
        exact List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨hL, rfl⟩, by
          simpa using hf⟩
      · intro _ hc
        simp only [classForce, decide_eq_true_eq] at hc
        have := (List.mem_filter.mp hc).2
        simpa using this
  | bot =>
      constructor
      · intro _ hf
        exact absurd ((K.force_bot a).mp hf) hinf
      · intro _ hc
        exact Bool.noConfusion hc
  | and A B ihA ihB =>
      constructor
      · intro hL hf
        obtain ⟨h1, h2⟩ := sfL_and hL
        simp only [classForce, Bool.and_eq_true]
        exact ⟨ihA.1 h1 hf.1, ihB.1 h2 hf.2⟩
      · intro hR hc
        obtain ⟨h1, h2⟩ := sfR_and hR
        simp only [classForce, Bool.and_eq_true] at hc
        exact ⟨ihA.2 h1 hc.1, ihB.2 h2 hc.2⟩
  | or A B ihA ihB =>
      constructor
      · intro hL hf
        obtain ⟨h1, h2⟩ := sfL_or hL
        simp only [classForce, Bool.or_eq_true]
        exact hf.elim (fun h => Or.inl (ihA.1 h1 h)) (fun h => Or.inr (ihB.1 h2 h))
      · intro hR hc
        obtain ⟨h1, h2⟩ := sfR_or hR
        simp only [classForce, Bool.or_eq_true] at hc
        exact hc.elim (fun h => Or.inl (ihA.2 h1 h)) (fun h => Or.inr (ihB.2 h2 h))
  | imp A B ihA ihB =>
      constructor
      · intro hL hf
        obtain ⟨h1, h2⟩ := sfL_imp hL
        simp only [classForce, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
        by_cases hcA : classForce (clAts K G a) A = true
        · exact Or.inr (ihB.1 h2 (hf a (K.le_refl a) (ihA.2 h1 hcA)))
        · exact Or.inl (Bool.not_eq_true _ ▸ hcA)
      · intro hR hc
        obtain ⟨h1, h2⟩ := sfR_imp hR
        rw [K.force_imp]
        intro b hab hbA
        rw [hmax b hab] at hbA ⊢
        simp only [classForce, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hc
        rcases hc with hcA | hcB
        · exact absurd (ihA.1 h1 hbA) (by simp [hcA])
        · exact ihB.2 h2 hcB
  | circ A ihA =>
      constructor
      · intro hL hf
        obtain ⟨b, hab, hbA⟩ := hf a (K.le_refl a)
        have hba : b = a := hmax b (K.sub_mi hab)
        exact ihA.1 (sfL_circ hL) (hba ▸ hbA)
      · intro hR hc
        intro b hab
        rw [hmax b hab]
        exact ⟨a, K.rm_refl a, ihA.2 (sfR_circ hR) hc⟩

/-- **The kernel discharged at maximal worlds**, by the generalised
`Ax^I◯` over the world's classical theory. -/
def circWit_of_maximal {K : Kripke} {G : Form} {a : K.W} {Z : Form}
    (hmax : ∀ u, K.le a u → u = a)
    (hZ : Form.circ Z ∈ sfR G) (hnf : ¬ K.force a (.circ Z)) :
    IrrWit K G a (.circ Z) :=
  have hinf : ¬ K.Fal a := fun hf => hnf (K.fal_force _ hf)
  have hnfZ : ¬ K.force a Z := fun hf => hnf (fun b hab =>
    ⟨b, K.rm_refl b, K.force_mono hab hf⟩)
  have hFf : classForce (clAts K G a) Z = false := by
    cases hcZ : classForce (clAts K G a) Z with
    | false => rfl
    | true =>
        exact absurd ((force_classForce hmax hinf Z).2 (sfR_circ hZ) hcZ) hnfZ
  { stab := []
    th := vacZoneA G (clAts K G a)
    der := .axIC Z (clAts K G a) clAts_subset hFf hZ
    sub := List.nil_subset _
    cov := fun X hX => by
      obtain ⟨hsfL, hstar⟩ := mem_lamStar.mp hX
      refine List.mem_append_right _ (mem_nf.mpr ⟨lamStar_subset_gHat hX, ?_⟩)
      exact List.mem_filter.mpr ⟨lamStar_subset_gHat hX,
        (force_classForce hmax hinf X).1 hsfL (K.forceStar_force hstar)⟩
    thNf := nf_idem.symm }

/-- **Unconditional completeness over discrete models.**  When every
world is maximal, `Λ*` is circ-free everywhere and the kernel is
discharged by `circWit_of_maximal`, so statement (A) holds with no
side condition.  (The first completeness instance for the FULL modal
calculus — goals may carry `◯` on both sides.) -/
theorem completeness_of_discrete {K : Kripke} {G : Form}
    (hdisc : ∀ a u : K.W, K.le a u → u = a)
    (hK : ¬ K.valid G) : Provable G :=
  completeness_of_supply
    (pledgeSupply_of_locFree (fun b => circPart_lamStar_nil_of_maximal (hdisc b)))
    (fun a Z hZ hnf _ => circWit_of_maximal (hdisc a) hZ hnf) hK

end FRJ
