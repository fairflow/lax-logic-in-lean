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
HYPOTHESES: the un-orderable recursion of §9/§10 becomes a family of
independently provable lemmas, and the open content of `AllMet`
contracts to the per-instance supply order alone. -/

/-- **The irregular ◯-demand** (`◯∉`), from a regular `Z`-wit anywhere
above `a`.  The §9 bad edge — its supplier is now an input. -/
theorem metI_circ {K : Kripke} {G : Form} {a : K.W} {Z : Form}
    (hgoal : Form.circ Z ∈ sfR G)
    (w : MRWit K G a Z) : Nonempty (IrrWit K G a (.circ Z)) := by
  refine ⟨⟨[], nf G (lamStar K a G),
    FRJi.circNotIn w.der w.tOK (fun X hX => ?_) hgoal,
    List.nil_subset _, fun X hX => ?_, nf_idem.symm⟩⟩
  · obtain ⟨hXG, hXl⟩ := mem_nf.mp hX
    exact ⟨clo_mono w.cov (lamStar_mono w.wfal w.wle X hXl), hXG⟩
  · exact List.mem_append_right _ (mem_nf.mpr ⟨lamStar_subset_gHat hX, hX⟩)

end FRJ
