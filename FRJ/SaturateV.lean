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
import FRJ.Saturate
import FRJ.SoundV
import FRJ.CalculusV
import FRJ.CalculusVLemmas

namespace FRJ.V

/-! ## The four wit records, at the REPAIRED family

Each is the record declared once in `FRJ/Minimal.lean` (`IrrWitOf`) or
`FRJ/Saturate.lean` (`MRWitOf`, `FRWitOf`, `OWitOf`, `PledgeFamOf`),
instantiated here at `FRJVi`/`FRJVr`.  Before 2026-09-18 each was a
second `structure` declaration whose text was byte-identical to the
paper one and whose type was not; the record and everything proved about
it by projection alone (`MRWitOf.toFree`, `.weaken`, `.toOWit`) is now
declared once. -/

/-- The irregular wit over the REPAIRED family. -/
abbrev IrrWit := IrrWitOf FRJVi

/-- The modal regular wit: a tag-carrying derivation anchored at a world
`wld ≥ a` whose `Λ*` the context covers, with the tag consumable by the
modal rules (`circIn`/`circNotIn`/the ⋈^◯ family all gate on exactly
this disjunction). -/
abbrev MRWit := MRWitOf FRJVr

/-- The FREE-grade regular wit: as `MRWit` but with no tag certificate.
Consumed where any tag serves (`impNotIn` premises, the root).  The
fallible joins produce these unconditionally at circ-carrying worlds. -/
abbrev FRWit := FRWitOf FRJVr

/-- The REPAIRED family's rule interface (`FRJ/Saturate.lean`).  The
sixteen constructors the saturation layer applies have, in `FRJVi`/
`FRJVr`, exactly the signatures they have in `FRJi`/`FRJr`, so every
declaration below that only INTRODUCES is the paper one instantiated
here.  `FRJVr.axR`, `.joinAt` and `.joinOr` are deliberately NOT fields:
`FRJVr.joinAt` asks for MORE than `FRJr.joinAt` (the `restrict_keptChain`
premise and `joinCtxAt_eq_base`), so `metR_prime` and `metR_or` are
genuinely two proofs and stay below in full. -/
def satRulesV : SatRules FRJVi FRJVr where
  axI := @FRJVi.axI; axIC := @FRJVi.axIC
  andI1 := @FRJVi.andI1; andI2 := @FRJVi.andI2; orI := @FRJVi.orI
  impInI := @FRJVi.impInI; impNotIn := @FRJVi.impNotIn
  circNotIn := @FRJVi.circNotIn
  andR1 := @FRJVr.andR1; andR2 := @FRJVr.andR2
  circIn := @FRJVr.circIn; impIn := @FRJVr.impIn
  joinAtF := @FRJVr.joinAtF; joinAtP := @FRJVr.joinAtP
  joinOrF := @FRJVr.joinOrF; joinOrP := @FRJVr.joinOrP

/-- **The demand closure.**  Every refuted right-signature formula at
every world of `K` has both an irregular and a (tag-admissible) regular
wit.  `¬ force a C` already yields `¬ Fal a` (a fallible world forces
everything), so no separate infallibility hypothesis is needed. -/
abbrev AllMet := AllMetOf FRJVi FRJVr

/-- **Completeness, given the closure**: statement (A) of the W4 targets
follows from `AllMet` in one step, at the root demand for `G` itself. -/
theorem completeness_of_allMet {K : Kripke} {G : Form}
    (h : AllMet K G) (hK : ¬ K.valid G) : ProvableV G := by
  obtain ⟨w⟩ := (h K.root G (sfR_self G) hK).2
  exact ⟨w.t, w.ctx, ⟨w.der⟩⟩

/-- The soundness half over the repaired family: an
`FRJV(G)`-derivation of `G` yields a countermodel whose root is
infallible (the paper `provable_root_countermodel` over
`V.modR_countermodel`). -/
theorem provableV_root_countermodel {G : Form} (h : ProvableV G) :
    ∃ K : Kripke, ¬ K.Fal K.root ∧ ¬ K.valid G := by
  obtain ⟨t, Γ, ⟨d⟩⟩ := h
  have hc := modR_countermodel d
  exact ⟨modR d, fun hf => hc ((modR d).fal_force G hf), hc⟩

/-- **The full biconditional, given the closure** — W4 statement (B):
`FRJV(G)` proves `G` iff `G` has a root-infallible countermodel.  The
soundness half is unconditional (`provableV_root_countermodel`); the
closure carries the completeness half. -/
theorem frj_iff_root_countermodel_of_allMet {G : Form}
    (hmet : ∀ K : Kripke, AllMet K G) :
    ProvableV G ↔ ∃ K : Kripke, ¬ K.Fal K.root ∧ ¬ K.valid G := by
  constructor
  · exact provableV_root_countermodel
  · rintro ⟨K, -, hv⟩
    exact completeness_of_allMet (hmet K) hv

/- The ◯-free closure slice (`allMet_of_circFree`,
`completeness_via_closure`) is NOT ported: it consumes the paper
`minMod`, and its V-corollary already exists as
`completenessV_via_closure` (`FRJ/CompleteV.lean`) by transfer. -/

/-! ## Case builders (slice 2)

Each of the visit's cases, refactored to take its supplier wits as
INPUTS: the un-orderable recursion of §9/§10 becomes a family of
independently checkable constructions, and the open content of `AllMet`
contracts to the per-instance supply order alone.  Everything is
Type-valued data — `Nonempty` appears only at the `AllMet` interface —
so the layer stays `Classical.choice`-free like the landed `minMod`. -/

/-- **The irregular ◯-demand** (`◯∉`), from a regular `Z`-wit anywhere
above `a`.  The §9 bad edge — its supplier is now an input. -/
abbrev metI_circ := metI_circ_core satRulesV

/-- The irregular atomic demand — supplier-free (`Ax^I` with the full
complement zone), ported from `minMod` unchanged: it never used `hcf`. -/
abbrev metI_atom := metI_atom_core satRulesV

/-- The irregular `⊥`-demand — supplier-free. -/
abbrev metI_bot := metI_bot_core satRulesV

/-- The irregular `∧`-demand, from a wit for whichever conjunct fails. -/
abbrev metI_and := metI_and_core satRulesV

/-- The irregular `∨`-demand, from wits for both disjuncts. -/
abbrev metI_or := metI_or_core satRulesV

/-- The irregular `⊃`-demand.  Two suppliers: the `⊃∈` route (an
irregular `B`-wit at `a` itself, used when `a` forces `A`) and the
`⊃∉` float (a regular `B`-wit at the minEta world, which is then
strictly above `a`). -/
abbrev metI_imp := metI_imp_core satRulesV

/-- Tag admissibility threads through `∧`-introduction via `Covers.andL/R`. -/
abbrev metR_and := metR_and_core satRulesV

/-- Tag admissibility threads through `⊃`-introduction via `Covers.imp`,
whose `Clo` side condition is the same one `impIn` itself consumes.  The
minEta float and the stay-at-`a` case share one body. -/
abbrev metR_imp := metR_imp_core satRulesV

/-- The regular `◯`-demand, by `◯∈` over a `Z`-wit at the minZeta world.
No modal join is needed: `circIn` preserves any admissible tag, and the
measure cycle that forced the ⋈^◯ route in the recursive organisation
does not exist here — the supplier is an input. -/
abbrev metR_circ := metR_circ_core satRulesV

/-! ### The origin-indexed certified interface (build β2, target type)

What `circNotIn`/`circIn` consumers actually need from a certified row
is weaker than `MRWit`: the derivation, the tag certificate, and the
DEMANDING world's `Λ*` grounded through the row's context.  Requiring
the anchor's own full `Λ*`-coverage is over-specification and contains
the one provably-unsatisfiable pledge instance (docs §13). -/

/-- The origin-indexed certified wit: a tagged row grounding the
origin's `Λ*`.  No anchor fields — the anchor is dissolved into
`ground`. -/
abbrev OWit := OWitOf FRJVr

/-- `metI_circ` against the corrected interface: the irregular ◯-demand
from an origin-indexed `Z`-wit.  Subsumes `metI_circ` (via `toOWit`)
and `metI_circ_syn` (an `OWit` with syntactic ground). -/
def metI_circO {K : Kripke} {G : Form} {b : K.W} {Z : Form}
    (hgoal : Form.circ Z ∈ sfR G)
    (w : OWit K G b Z) : IrrWit K G b (.circ Z) where
  stab := []
  th := lamStar K b G
  der := .circNotIn w.der w.tOK
    (fun X hX => ⟨w.ground X hX, lamStar_subset_gHat hX⟩) hgoal
  sub := List.nil_subset _
  cov := fun _ hX => hX

/-! ### The prime and `∨` joins at locally circ-free worlds

`hcf` (the global syntactic circ-freeness) enters the landed helpers in
exactly two roles, both derivable from the runtime per-world condition
`circPart (Λ*_a) = []`: the `hcirc` discharge of the barren joins, and
the `Ĝ_◯`-branch of cov.  The residual — the same demands at worlds
whose `Λ*` carries `◯`-formulas, where the joins must run in promise
mode — is the §8 corner in its final localisation. -/

/-! ### Shared with the paper calculus

21 declarations that stood here were byte-identical to their
`FRJ` originals and mention nothing of `FRJVr`, so they said the same thing
twice.  `FRJ.V` is nested inside `FRJ`, so every use in this file now resolves
to the original (2026-09-16):

`Kripke.ConeGrounded`,
`Kripke.Endpoints`,
`Kripke.coneGrounded_of_discrete`,
`Kripke.coneGrounded_of_rmFull`,
`MaxRef`,
`MaxSeen`,
`MinRef`,
`MinZetaNS`,
`circPart_lamStar_nil_of_corner`,
`circPart_lamStar_nil_of_sfL_circFree`,
`clAts`,
`clAts_subset`,
`coneTrivial_of_corner`,
`endpoints_of_coneGrounded`,
`endpoints_of_rmFull`,
`force_classForce`,
`lamStar_not_circ_loc`,
`maxRef_of_not_circ`,
`minRef`,
`minZetaNS`,
`unionAll_circPart_nil_loc`.
-/


def metR_prime {K : Kripke} {G : Form} {a : K.W} {C : Form}
    (hloc : circPart (lamStar K a G) = [])
    (hCp : C.isPrime) (hC : C ∈ sfR G) (hnf : ¬ K.force a C)
    (ih : ∀ A : Form, A ∈ sfR G → ¬ K.force a A → IrrWit K G a A) :
    MRWit K G a C := by
  by_cases hempty : impPart (lamStar K a G) = []
  · refine ⟨.barren, rm (gAt G) C, .axR C hCp hC (CtxEq.refl _), Or.inl rfl, a, K.le_refl a,
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
    have hfmem : ∀ j, f j ∈ upsPrime K a G := E.f_mem
    let wit : ∀ j, IrrWit K G a (f j) := fun j =>
      ih (f j) (upsPrime_spec (hfmem j)).1 (upsPrime_spec (hfmem j)).2
    let stab := fun j => (wit j).stab
    let th := fun j => (wit j).th
    refine ⟨.barren, joinCtxAt stab th f C, ?_, Or.inl rfl, a, K.le_refl a,
      fun hf => hnf (K.fal_force _ hf), ?_⟩
    · refine .joinAt (fun j => (wit j).der) (fun i j _ X hX => (wit j).cov ((wit i).sub hX))
        (fun A B hmem => ?_) (unionAll_circPart_nil_loc hloc (fun j => (wit j).sub))
        (restrict_keptChain _) hCp (fun hmem => ?_) hC
        ((CtxEq.refl _).trans joinCtxAt_eq_base)
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
    (d : FRJVr G t Γ Z)
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
  have hfmem : ∀ j, f j ∈ U := E.f_mem
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
      (restrict_keptChain _) ⟨.ups ?_, .ups ?_⟩ hC
      ((CtxEq.refl _).trans joinCtxOr_eq_base)
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


/-- `metR_prime` and `metR_or` are the two builders the paper and repaired
families do NOT share, so the visit takes them as parameters.  These two
adapters supply them at the strict-implicit binders `MPrimeOf`/`MOrOf`
use, which exist so that an instantiation is one line rather than a
restated signature; the two builders themselves keep the binders they
have always had. -/
def mPrime : MPrimeOf FRJVi FRJVr :=
  fun _K _G _a _C hloc hCp hC hnf ih => metR_prime hloc hCp hC hnf ih

/-- `metR_or` at the binders `MOrOf` uses.  See `mPrime`. -/
def mOr : MOrOf FRJVi FRJVr :=
  fun _K _G _a _C₁ _C₂ hloc hC hnf ih => metR_or hloc hC hnf ih

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
abbrev PledgeFam := PledgeFamOf FRJVr

/-- **The second named supply**: pledge families at circ-carrying
worlds, for prime and disjunctive demands. -/
abbrev PledgeSupply := PledgeSupplyOf FRJVr

/-- **`PledgeFam` is UNSATISFIABLE at its own defect site** (2026-08-26,
the FRJV completeness campaign's statement screen): whenever
`◯F ∈ Λ*_a`, the family for `F` at `a` cannot exist — `hbody` demands a
row whose context `Clo`-contains `F`, but the row derives `F`, so its
root model forces the context (`lemma39R`) and hence `F` (`clo_forces`),
contradicting the same root's `F`-refutation.  Consequently
`∀ K G, PledgeSupply K G` is FALSE (`wip/frjv_pledge_refute.lean`
realises the configuration on sepM with `F = ⊥`), and
`completeness_of_supply` is VACUOUS on any model realising it — e.g.
the two-world countermodel of `◯p ⊃ p`.  This is the §13
provably-unsatisfiable instance (`docs/frj-w4.md:832-845`); the live
route is the transported-cov refinement designed there
(`docs/frjv-completeness-plan.md`, Lemma A′). -/
theorem not_pledgeFam_of_circ_mem {K : Kripke} {G : Form} {a : K.W}
    {F : Form} (h : Form.circ F ∈ lamStar K a G)
    (pf : PledgeFam K G a F) : False := by
  obtain ⟨i, hclo⟩ := pf.hbody F h
  have hl := lemma39R (pf.dps i)
  have hroot : (modR (pf.dps i)).forces (modR (pf.dps i)).root (pf.Δs i) :=
    fun X hX => hl.1 _ _ ((preR_root_lbl (pf.dps i) X).mpr hX)
  exact hl.2 (clo_forces hroot hclo)

/-- The prime regular demand at a circ-carrying world: the promise
`⋈^At,p`, pledging the goal. -/
abbrev metR_primeP := metR_primeP_core satRulesV

/-- The `∨`-regular demand at a circ-carrying world: the promise
`⋈^∨,p`, pledging the disjunction itself. -/
abbrev metR_orP := metR_orP_core satRulesV


/-- Free-grade `∧`-threading (no tag lift needed). -/
abbrev metR_andF := metR_andF_core satRulesV

/-- Free-grade `⊃`-threading. -/
abbrev metR_impF := metR_impF_core satRulesV

/-- The prime regular demand at a circ-carrying world, FREE grade: the
FALLIBLE `⋈^At,⊥`, whose conclusion keeps the whole modal zone with no
side condition — no pledge needed. -/
abbrev metR_primeF := metR_primeF_core satRulesV

/-- The `∨`-regular demand at a circ-carrying world, FREE grade: the
fallible `⋈^∨,⊥`. -/
abbrev metR_orF := metR_orF_core satRulesV

/-! ## The gluing (slice 3)

The visit that assembles the builders.  Measure `(ht, t, size)` — the
paper's own, irregular-before-regular.  Every builder edge is legal:
the Υ-edges drop phase, the floats drop height (`metI_imp` records
`e ≠ a`; `minZetaNS` prefers a non-self candidate), the in-layer edges
drop size.  The single un-orderable edge — the irregular ◯-demand at a
world that is its own sole minZeta candidate — is discharged by an
explicit supply (`CircSupply`), which is thereby THE open kernel of
FRJ◯ completeness. -/

/-- **The open kernel of FRJV◯ completeness**: supply for the irregular
◯-demand at a world every proper extension of which forces the body.
(Docstring repaired 2026-09-18: the Stage B deletion of 2026-09-16 left
`MinZetaNS`'s docstring stranded here, documenting the wrong
declaration; `MinZetaNS` itself lives in `FRJ/Saturate.lean` and is
inherited.) -/
abbrev CircSupply := CircSupplyOf FRJVi

/-- The statement family: `t = 0` the irregular wit, else the regular. -/
abbrev SatStmt := SatStmtOf FRJVi FRJVr

/-- **The visit.**  Well-founded on `(ht, t, size)`; total given the two
named conditions (`hloc`: `Λ*` circ-free at every world, so the barren
joins suffice; `hsup`: the sole-candidate supply). -/
abbrev visit := visit_core satRulesV mPrime mOr

/-- **`AllMet` from the two named supplies.** -/
abbrev allMet_of_supply :=
  allMet_of_supply_core satRulesV mPrime mOr

/-- **FRJ◯ completeness, modulo the two supplies**: statement (A) for
every model providing pledge families at circ-carrying worlds and the
sole-candidate ◯-supply.  (Docstring corrected 2026-08-17: an earlier
version of this theorem took world-wise circ-freeness in place of
`PledgeSupply`.) -/
theorem completeness_of_supply {K : Kripke} {G : Form}
    (psup : PledgeSupply K G)
    (hsup : CircSupply K G)
    (hK : ¬ K.valid G) : ProvableV G :=
  completeness_of_allMet (allMet_of_supply psup hsup) hK

/-- World-wise circ-free `Λ*` discharges the pledge supply vacuously. -/
abbrev pledgeSupply_of_locFree := @pledgeSupply_of_locFree_core FRJVr

/-! ### Discharging the kernel at maximal worlds

At a `≤`-maximal infallible world forcing is classical, with the
polarity split doing the bookkeeping between the two subformula sets:
left subformulas carry forcing INTO the classical valuation, right
subformulas carry it back.  The generalised `Ax^I◯` then discharges the
sole-candidate supply outright: the vacuous zone of the world's own
classical theory contains `Λ*_a`, and the side condition
`classForce ats Z = false` is exactly `a ⊮ Z`. -/


abbrev circWit_of_maximal := circWit_of_maximal_core satRulesV

/-! ### The kernel's own hypothesis makes the corner cone-trivial

The supply `CircSupply` is asked for at a world `a` every PROPER
`≤`-extension of which forces the body `Z`, and at which `◯Z` is
nevertheless refuted.  That already pins the modal cone of `a` down to
`{a}`:

    a ⊮ ◯Z   and   (∀ u > a, u ⊩ Z)   imply   ∀ c, Rm a c → c = a.

For if `a Rm c` with `c ≠ a` then `c ⊩ Z` (by `sub_mi` and the corner
hypothesis), and every `b ≥ a` then has a `Z`-forcing `Rm`-successor —
`c` when `b = a`, `b` itself otherwise — i.e. `a ⊩ ◯Z`.  This is
`docs/frj-w4.md` §10 fact 3, and it is now a lemma rather than an
observation. -/



abbrev metR_circAt := metR_circAt_core satRulesV

/-- The two-tier statement family at a maximal world: `t = 0` irregular,
otherwise the TAGGED regular wit.  The free grade never arises there —
its only producer, the `⊃∉` float, needs a world strictly above. -/
abbrev MaxStmt := MaxStmtOf FRJVi FRJVr

/-- **The local recursion at a maximal world.**  Measure `(t, |C|)`; no
world ever changes, `hloc` holds throughout, and no supply is consumed. -/
abbrev visitMax := visitMax_core satRulesV mPrime mOr

/-- The global statement family: `t = 0` irregular, otherwise the FREE
regular wit.  The tagged grade is absent — it lives in `visitMax`. -/
abbrev GStmt := GStmtOf FRJVi FRJVr

/-- **The global recursion.**  Measure `(ht a, t, |C|)`.  Both `◯` cases
are LEAVES: they route to `visitMax` at the maximal refuter supplied by
`maxRef_of_not_circ`, so no same-world irregular→regular edge remains. -/
abbrev visitG := visitG_core satRulesV mPrime mOr

/-- The demand closure with the regular half at the FREE grade.  This is
all completeness consumes: the root reads only the derivation, never the
tag. -/
abbrev AllMetF := AllMetFOf FRJVi FRJVr

theorem completeness_of_allMetF {K : Kripke} {G : Form}
    (h : AllMetF K G) (hK : ¬ K.valid G) : ProvableV G := by
  obtain ⟨w⟩ := (h K.root G (sfR_self G) hK).2
  exact ⟨w.t, w.ctx, ⟨w.der⟩⟩

abbrev allMetF_of_endpoints :=
  allMetF_of_endpoints_core satRulesV mPrime mOr

/-- **FRJ◯ COMPLETENESS OVER ENDPOINT-SEEING MODELS, UNCONDITIONAL.**
Statement (A) of the W4 targets for every model whose modal relation is a
reflexive-transitive subrelation of `≤` each of whose cones contains a
`≤`-maximal world.  No hypothesis on the goal, no named supply, and no
condition on the SHAPE of `Rm`: `◯` may occur anywhere, on either side. -/
theorem completeness_of_endpoints {K : Kripke} {G : Form} (hep : K.Endpoints)
    (hK : ¬ K.valid G) : ProvableV G :=
  completeness_of_allMetF (allMetF_of_endpoints hep) hK

/-- **The kernel discharged on cone-grounded frames.**  The corner
forces cone-triviality, the frame condition turns that into maximality,
and the generalised `Ax^I◯` closes it. -/
abbrev circSupply_of_coneGrounded :=
  circSupply_of_coneGrounded_core satRulesV

/-- **Completeness over cone-grounded models.**  An instance of
`completeness_of_endpoints`: no supply of either kind, no condition on
the goal. -/
theorem completeness_of_coneGrounded {K : Kripke} {G : Form}
    (hg : K.ConeGrounded) (hK : ¬ K.valid G) : ProvableV G :=
  completeness_of_endpoints (endpoints_of_coneGrounded hg) hK

/-- **Completeness over `Rm = ≤` models.**  A second instance — the frame
every model extracted from a derivation carries. -/
theorem completeness_of_rmFull {K : Kripke} {G : Form}
    (hfull : ∀ a b : K.W, K.le a b → K.Rm a b) (hK : ¬ K.valid G) :
    ProvableV G :=
  completeness_of_endpoints (endpoints_of_rmFull hfull) hK

/-! ### A supply that is vacuous on the goal

The pledge supply is asked for only at worlds where `Λ*` carries a
`◯`-formula, and `Λ*_b ⊆ Sf^L(G)`.  So a goal whose LEFT subformulas are
`◯`-free discharges it for every model at once.  This is no longer needed
for any completeness statement below, but it is the cheapest discharge of
`PledgeSupply` for the `visit` route and is kept for that. -/

theorem completeness_of_discrete {K : Kripke} {G : Form}
    (hdisc : ∀ a u : K.W, K.le a u → u = a)
    (hK : ¬ K.valid G) : ProvableV G :=
  completeness_of_coneGrounded (Kripke.coneGrounded_of_discrete hdisc) hK

end FRJ.V
