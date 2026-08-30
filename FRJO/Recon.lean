/-
# FRJ◯ W5 — the reconstruction theorem

`Reconstruction` (FRJO/Complete.lean) proved, by structural induction
on `Reject.Built` with an inner induction on the goal formula.

**Constructivity.**  The theorem is stated over EFFECTIVE model data:
`Effective M` packages the three Prop-level facts a reconstruction
actually consumes — forcing is decided at each world, a refuted
implication has a witness world, a refuted `◯` has a witness world
whose modal cone misses the body.  Every model has them classically
(`effective_of_classical`), and they propagate from a join to its
components (`Effective.comp`), which is all the induction needs.  Using
`p ∨ ¬p` rather than `Decidable p` keeps every goal in `Prop`, so the
zone is obtained by `exists_restrict` and premise derivations by
`Nonempty`-elimination: no `Classical.choice`, no
`Classical.propDecidable`, no computed `decide ∘ force`.
-/
import FRJO.Reconstruct

namespace FRJO

open PLLND PLLFormula

/-! ## Effective model data -/

/-- The three Prop-level effectivity facts the reconstruction consumes.
Classically automatic (`effective_of_classical`); carried explicitly so
the reconstruction itself is choice-free. -/
structure Effective (M : ConstraintModel) : Prop where
  /-- forcing is decided (as a `Prop`) at every world -/
  force_dec : ∀ (w : M.W) (φ : PLLFormula), M.force w φ ∨ ¬ M.force w φ
  /-- `⊃∉`: a refuted implication has a witness world -/
  imp_wit : ∀ (w : M.W) (A B : PLLFormula), ¬ M.force w (.ifThen A B) →
      ∃ v, M.Ri w v ∧ M.force v A ∧ ¬ M.force v B
  /-- `◯∉`: a refuted `◯` has a witness world whose cone misses the body -/
  box_wit : ∀ (w : M.W) (A : PLLFormula), ¬ M.force w (.somehow A) →
      ∃ v, M.Ri w v ∧ ∀ u, M.Rm v u → ¬ M.force u A

theorem effective_of_classical (M : ConstraintModel) : Effective M := by
  classical
  refine ⟨fun w φ => em _, ?_, ?_⟩
  · intro w A B h
    by_contra hc
    exact h (by
      intro v hv hA
      by_contra hB
      exact hc ⟨v, hv, hA, hB⟩)
  · intro w A h
    by_contra hc
    exact h (by
      intro v hv
      by_contra hn
      exact hc ⟨v, hv, fun u hu hA => hn ⟨u, hu, hA⟩⟩)

/-! ## The zone, without `decide` -/

/-- Restricting a list by a Prop-decided predicate.  The list is
obtained inside a `Prop` goal, so no `Decidable` instance and no choice
are needed — this is what replaces `List.filter (decide ∘ force)`. -/
theorem exists_restrict {α : Type} (P : α → Prop) (hP : ∀ x, P x ∨ ¬ P x) :
    ∀ l : List α, ∃ S : List α, ∀ x, x ∈ S ↔ (x ∈ l ∧ P x) := by
  intro l
  induction l with
  | nil => exact ⟨[], by simp⟩
  | cons y l ih =>
      obtain ⟨S, hS⟩ := ih
      rcases hP y with hy | hy
      · refine ⟨y :: S, fun x => ?_⟩
        simp only [List.mem_cons, hS]
        constructor
        · rintro (rfl | ⟨h1, h2⟩)
          · exact ⟨Or.inl rfl, hy⟩
          · exact ⟨Or.inr h1, h2⟩
        · rintro ⟨rfl | h1, h2⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨h1, h2⟩
      · refine ⟨S, fun x => ?_⟩
        simp only [List.mem_cons, hS]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨Or.inr h1, h2⟩
        · rintro ⟨rfl | h1, h2⟩
          · exact absurd h2 hy
          · exact ⟨h1, h2⟩

/-! ## Universe bookkeeping -/

theorem sfPlus_and_left {G : Cell} {A B : PLLFormula}
    (h : PLLFormula.and A B ∈ sfPlus G) : A ∈ sfPlus G :=
  sfPlus_closed h (by simp [sf, sf_self])

theorem sfPlus_and_right {G : Cell} {A B : PLLFormula}
    (h : PLLFormula.and A B ∈ sfPlus G) : B ∈ sfPlus G :=
  sfPlus_closed h (by simp [sf, sf_self])

theorem sfPlus_or_left {G : Cell} {A B : PLLFormula}
    (h : PLLFormula.or A B ∈ sfPlus G) : A ∈ sfPlus G :=
  sfPlus_closed h (by simp [sf, sf_self])

theorem sfPlus_or_right {G : Cell} {A B : PLLFormula}
    (h : PLLFormula.or A B ∈ sfPlus G) : B ∈ sfPlus G :=
  sfPlus_closed h (by simp [sf, sf_self])

theorem sfPlus_imp_left {G : Cell} {A B : PLLFormula}
    (h : PLLFormula.ifThen A B ∈ sfPlus G) : A ∈ sfPlus G :=
  sfPlus_closed h (by simp [sf, sf_self])

theorem sfPlus_imp_right {G : Cell} {A B : PLLFormula}
    (h : PLLFormula.ifThen A B ∈ sfPlus G) : B ∈ sfPlus G :=
  sfPlus_closed h (by simp [sf, sf_self])

theorem sfPlus_box {G : Cell} {A : PLLFormula}
    (h : PLLFormula.somehow A ∈ sfPlus G) : A ∈ sfPlus G :=
  sfPlus_closed h (by simp [sf, sf_self])

/-! ## Effectivity passes from a join to its components -/

section Join

variable {ι : Type} {Mods : ι → ConstraintModel}
  {D : Reject.RootData (Reject.union Mods)}

/-- Inside a component, `Rᵢ` is the component's own. -/
theorem join_Ri_some {i : ι} {a : (Mods i).W} {y : (Reject.union Mods).W}
    (h : (Reject.join Mods D).Ri (some ⟨i, a⟩) (some y)) :
    ∃ c : (Mods i).W, y = ⟨i, c⟩ ∧ (Mods i).Ri a c := by
  have h' : Reject.Lift Mods (fun i => (Mods i).Ri) ⟨i, a⟩ y := h
  cases h' with
  | mk hab => exact ⟨_, rfl, hab⟩

theorem Effective.comp (hE : Effective (Reject.join Mods D)) (i : ι) :
    Effective (Mods i) := by
  refine ⟨fun a φ => ?_, fun a A B h => ?_, fun a A h => ?_⟩
  · rcases hE.force_dec (some ⟨i, a⟩) φ with h | h
    · exact Or.inl ((Reject.join_force_comp D φ i a).mp h)
    · exact Or.inr (fun hc => h ((Reject.join_force_comp D φ i a).mpr hc))
  · obtain ⟨v, hv, hA, hB⟩ := hE.imp_wit (some ⟨i, a⟩) A B
      (fun hc => h ((Reject.join_force_comp D _ i a).mp hc))
    cases v with
    | none => exact absurd hv not_false
    | some y =>
        obtain ⟨c, rfl, hac⟩ := join_Ri_some hv
        exact ⟨c, hac, (Reject.join_force_comp D A i c).mp hA,
          fun hc => hB ((Reject.join_force_comp D B i c).mpr hc)⟩
  · obtain ⟨v, hv, hcone⟩ := hE.box_wit (some ⟨i, a⟩) A
      (fun hc => h ((Reject.join_force_comp D _ i a).mp hc))
    cases v with
    | none => exact absurd hv not_false
    | some y =>
        obtain ⟨c, rfl, hac⟩ := join_Ri_some hv
        refine ⟨c, hac, fun u hu hf => hcone (some ⟨i, u⟩) (.mk hu) ?_⟩
        exact (Reject.join_force_comp D A i u).mpr hf

end Join

/-! ## Two list utilities, both constructive -/

/-- Either every member of the list is forced, or one of them is not. -/
theorem all_or_witness {M : ConstraintModel} {w : M.W}
    (hd : ∀ φ, M.force w φ ∨ ¬ M.force w φ) :
    ∀ l : List PLLFormula,
      (∀ φ ∈ l, M.force w φ) ∨ ∃ φ ∈ l, ¬ M.force w φ := by
  intro l
  induction l with
  | nil => exact Or.inl (by simp)
  | cons y l ih =>
      rcases hd y with hy | hy
      · rcases ih with h | ⟨φ, hφ, hnf⟩
        · exact Or.inl (by
            intro φ hmem
            rcases List.mem_cons.mp hmem with rfl | hmem
            · exact hy
            · exact h φ hmem)
        · exact Or.inr ⟨φ, List.mem_cons_of_mem _ hφ, hnf⟩
      · exact Or.inr ⟨y, List.mem_cons_self, hy⟩

/-- Zipping a kid list against an all-`true` cone. -/
theorem zip_all_true {G : Cell} :
    ∀ kids : List (Reg G),
      List.zip kids (List.replicate kids.length true) =
        kids.map (fun k => (k, true)) := by
  intro kids
  induction kids with
  | nil => rfl
  | cons k l ih => rw [List.length_cons, List.replicate_succ, List.zip_cons_cons,
      List.map_cons, ih]

/-- Extending a premise family by one derivation. -/
def consPrems {G : Cell} {b : Nat} {K₀ : Reg G} {kids : List (Reg G)}
    (d : FRJD G b K₀) (prems : ∀ K ∈ kids, FRJD G b K) :
    ∀ K ∈ K₀ :: kids, FRJD G b K :=
  fun K hK =>
    if h : K = K₀ then h ▸ d
    else prems K ((List.mem_cons.mp hK).resolve_left h)

/-! ## A `Prop`-level interface to `worldOK` -/

/-- The goal-shape conjunct of `worldOK` v3, as a `Prop`: an atom fails
by absence from the zone, `⊥` at the (infallible) root, `◯A` when the
root's declared cone misses `A`; a compound goal never discharges at a
`world` node. -/
def GoalOK {G : Cell} (S : List PLLFormula) (C : PLLFormula)
    (kids : List (Reg G)) (leaf : Bool) : Prop :=
  match C with
  | .prop _ => C ∉ S
  | .falsePLL => True
  | .somehow A => leaf = false ∧ A ∉ S ∧ ∀ K ∈ kids, A ∉ K.stable
  | _ => False

/-- `worldOK` with an all-`true` cone, stated in `Prop`.  Every
`world` node below goes through this. -/
theorem worldOK_cone {G : Cell} {b : Nat} {S : List PLLFormula} {C : PLLFormula}
    {kids : List (Reg G)} {leaf : Bool}
    (h1 : ∀ φ ∈ S, φ ∈ sfPlus G) (h2 : C ∈ sfPlus G)
    (h3 : ∀ K ∈ kids, ∀ φ ∈ S, φ ∈ K.stable)
    (h4 : ∀ A, PLLFormula.somehow A ∈ S →
            leaf = true ∨ (∃ K ∈ kids, A ∈ K.stable) ∨ A ∈ S)
    (h5 : GoalOK S C kids leaf) :
    worldOK G b S C kids (List.replicate kids.length true) leaf = true := by
  simp only [worldOK, zip_all_true, Bool.and_eq_true, List.all_eq_true,
    List.any_map, List.all_map]
  refine ⟨⟨⟨⟨fun x hx => List.elem_iff.mpr (h1 x hx), List.elem_iff.mpr h2⟩,
    fun K hK φ hφ => List.elem_iff.mpr (h3 K hK φ hφ)⟩, ?_⟩, ?_⟩
  · intro x hx
    match x, hx with
    | .prop _, _ | .falsePLL, _ | .and _ _, _ | .or _ _, _ | .ifThen _ _, _ => rfl
    | .somehow A, hx =>
        simp only [Function.comp_def, Bool.true_and, Bool.or_eq_true, List.any_eq_true]
        rcases h4 A hx with h | ⟨K, hK, hA⟩ | hA
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr ⟨K, hK, List.elem_iff.mpr hA⟩)
        · exact Or.inr (List.elem_iff.mpr hA)
  · cases C with
    | prop a =>
        simp only [GoalOK] at h5
        exact Bool.not_eq_true' _ ▸ Bool.eq_false_iff.mpr fun hc => h5 (List.elem_iff.mp hc)
    | falsePLL => rfl
    | and A B => exact absurd h5 (by simp [GoalOK])
    | or A B => exact absurd h5 (by simp [GoalOK])
    | ifThen A B => exact absurd h5 (by simp [GoalOK])
    | somehow A =>
        simp only [GoalOK] at h5
        obtain ⟨hl, hA, hK⟩ := h5
        simp only [Function.comp_def, hl, Bool.not_false, Bool.true_and,
          Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, Bool.not_true,
          Bool.false_or]
        exact ⟨Bool.eq_false_iff.mpr fun hc => hA (List.elem_iff.mp hc),
          fun K hKm => Bool.eq_false_iff.mpr fun hc => hK K hKm (List.elem_iff.mp hc)⟩

/-! ## The solo case -/

theorem recon_solo {G : Cell} {b : Nat} {V₀ : String → Prop} {fal : Prop}
    {hfull : fal → ∀ a, V₀ a}
    (hE : Effective (Reject.solo V₀ fal hfull)) :
    ∀ (C : PLLFormula), C ∈ sfPlus G →
      ¬ (Reject.solo V₀ fal hfull).force () C →
      ∃ S : List PLLFormula,
        (∀ φ, φ ∈ S ↔ (φ ∈ sfPlus G ∧ (Reject.solo V₀ fal hfull).force () φ)) ∧
        Nonempty (FRJD G b ⟨S, C⟩) := by
  obtain ⟨S, hS⟩ :=
    exists_restrict (fun φ => (Reject.solo V₀ fal hfull).force () φ)
      (hE.force_dec ()) (sfPlus G)
  -- the universe conjunct, once
  have huniv : S.all (sfPlus G).contains = true := by
    refine List.all_eq_true.mpr (fun φ hφ => ?_)
    exact List.elem_iff.mpr ((hS φ).mp hφ).1
  -- the ◯-positive conjunct, once: at a solo world `◯A` collapses to `A`
  have hbox : ∀ A, PLLFormula.somehow A ∈ S → S.contains A = true := by
    intro A hA
    obtain ⟨hm, hf⟩ := (hS _).mp hA
    exact List.elem_iff.mpr ((hS A).mpr
      ⟨sfPlus_box hm, (Reject.solo_force_somehow V₀ fal hfull A).mp hf⟩)
  suffices h : ∀ C : PLLFormula, C ∈ sfPlus G →
      ¬ (Reject.solo V₀ fal hfull).force () C → Nonempty (FRJD G b ⟨S, C⟩) by
    exact fun C h1 h2 => ⟨S, hS, h C h1 h2⟩
  intro C
  induction C with
  | prop a =>
      intro hmem hnf
      refine ⟨.world [] [] false (fun K hK => absurd hK List.not_mem_nil) ?_⟩
      simp only [worldOK, Bool.and_eq_true, List.all_nil, List.zip_nil_left,
        Bool.false_or, Bool.not_eq_true']
      refine ⟨⟨⟨⟨huniv, List.elem_iff.mpr hmem⟩, trivial⟩, ?_⟩, ?_⟩
      · refine List.all_eq_true.mpr (fun φ hφ => ?_)
        match φ, hφ with
        | .prop _, _ | .falsePLL, _ | .and _ _, _ | .or _ _, _
        | .ifThen _ _, _ => rfl
        | .somehow A, hφ => simpa using hbox A hφ
      · exact Bool.eq_false_iff.mpr (fun hc =>
          hnf ((hS _).mp (List.elem_iff.mp hc)).2)
  | falsePLL =>
      intro hmem _
      refine ⟨.world [] [] false (fun K hK => absurd hK List.not_mem_nil) ?_⟩
      simp only [worldOK, Bool.and_eq_true, List.all_nil, List.zip_nil_left,
        Bool.false_or]
      refine ⟨⟨⟨⟨huniv, List.elem_iff.mpr hmem⟩, trivial⟩, ?_⟩, trivial⟩
      refine List.all_eq_true.mpr (fun φ hφ => ?_)
      match φ, hφ with
      | .prop _, _ | .falsePLL, _ | .and _ _, _ | .or _ _, _
      | .ifThen _ _, _ => rfl
      | .somehow A, hφ => simpa using hbox A hφ
  | and A B ihA ihB =>
      intro hmem hnf
      rcases hE.force_dec () A with hA | hA
      · have hB : ¬ (Reject.solo V₀ fal hfull).force () B := fun hB => hnf ⟨hA, hB⟩
        obtain ⟨d⟩ := ihB (sfPlus_and_right hmem) hB
        exact ⟨.andR2 d⟩
      · obtain ⟨d⟩ := ihA (sfPlus_and_left hmem) hA
        exact ⟨.andR1 d⟩
  | or A B ihA ihB =>
      intro hmem hnf
      obtain ⟨d⟩ := ihA (sfPlus_or_left hmem) (fun h => hnf (Or.inl h))
      obtain ⟨e⟩ := ihB (sfPlus_or_right hmem) (fun h => hnf (Or.inr h))
      exact ⟨.orR d e⟩
  | ifThen A B _ ihB =>
      intro hmem hnf
      obtain ⟨v, -, hA, hB⟩ := hE.imp_wit () A B hnf
      cases v
      obtain ⟨d⟩ := ihB (sfPlus_imp_right hmem) hB
      exact ⟨.impIn d (List.elem_iff.mpr ((hS A).mpr ⟨sfPlus_imp_left hmem, hA⟩))⟩
  | somehow A _ =>
      intro hmem hnf
      have hA : ¬ (Reject.solo V₀ fal hfull).force () A := fun h =>
        hnf ((Reject.solo_force_somehow V₀ fal hfull A).mpr h)
      refine ⟨.world [] [] false (fun K hK => absurd hK List.not_mem_nil) ?_⟩
      simp only [worldOK, Bool.and_eq_true, List.all_nil, List.zip_nil_left,
        Bool.false_or, Bool.not_eq_true']
      refine ⟨⟨⟨⟨huniv, List.elem_iff.mpr hmem⟩, trivial⟩, ?_⟩, ?_⟩
      · refine List.all_eq_true.mpr (fun φ hφ => ?_)
        match φ, hφ with
        | .prop _, _ | .falsePLL, _ | .and _ _, _ | .or _ _, _
        | .ifThen _ _, _ => rfl
        | .somehow A', hφ => simpa using hbox A' hφ
      · exact ⟨⟨trivial, Bool.eq_false_iff.mpr
          (fun hc => hA ((hS _).mp (List.elem_iff.mp hc)).2)⟩, trivial⟩

/-! ## The join case -/

section JoinRoot

variable {G : Cell} {b : Nat} {ι : Type} {Mods : ι → ConstraintModel}
  {D : Reject.RootData (Reject.union Mods)}

/-- A kid of the root's `world` node stands for a world in the root's
DECLARED modal cone, and carries that world's restricted theory. -/
def ConeKid (Mods : ι → ConstraintModel) (D : Reject.RootData (Reject.union Mods))
    (G : Cell) (K : Reg G) : Prop :=
  ∃ (i : ι) (u : (Mods i).W), D.S ⟨i, u⟩ ∧
    ∀ φ, φ ∈ K.stable ↔ (φ ∈ sfPlus G ∧ (Mods i).force u φ)

/-- The component induction hypothesis of the `Built` induction. -/
def CompIH (G : Cell) (b : Nat) (Mods : ι → ConstraintModel) : Prop :=
  ∀ i, Effective (Mods i) → ∀ (r : (Mods i).W) (C : PLLFormula),
    C ∈ sfPlus G → ¬ (Mods i).force r C →
    ∃ S : List PLLFormula,
      (∀ φ, φ ∈ S ↔ (φ ∈ sfPlus G ∧ (Mods i).force r φ)) ∧
      Nonempty (FRJD G b ⟨S, C⟩)

/-- **The realiser/leaf dichotomy.**  Walking the root zone's `◯`
obligations, either every needed realiser refutes something in the
universe — and then it becomes a cone kid, by the component induction
hypothesis — or one of them forces the whole universe, and a single
fallible leaf discharges every obligation at once. -/
theorem exists_cone_kids (ih : CompIH G b Mods) (hE : Effective (Reject.join Mods D))
    (S : List PLLFormula)
    (hS : ∀ φ, φ ∈ S ↔ (φ ∈ sfPlus G ∧ (Reject.join Mods D).force none φ)) :
    ∀ l : List PLLFormula,
      ∃ (kids : List (Reg G)) (leaf : Bool),
        Nonempty (∀ K ∈ kids, FRJD G b K) ∧
        (∀ K ∈ kids, ConeKid Mods D G K) ∧
        (leaf = true → ∃ (i : ι) (u : (Mods i).W), D.S ⟨i, u⟩ ∧
            ∀ φ ∈ sfPlus G, (Mods i).force u φ) ∧
        (∀ A, PLLFormula.somehow A ∈ l → PLLFormula.somehow A ∈ S →
            leaf = true ∨ (∃ K ∈ kids, A ∈ K.stable) ∨ A ∈ S) := by
  intro l
  induction l with
  | nil =>
      exact ⟨[], false, ⟨fun K hK => absurd hK List.not_mem_nil⟩,
        fun K hK => absurd hK List.not_mem_nil, by simp, by simp⟩
  | cons φ l ihl =>
      obtain ⟨kids, leaf, ⟨prems⟩, hcone, hleaf, hcov⟩ := ihl
      cases φ with
      | prop a =>
          exact ⟨kids, leaf, ⟨prems⟩, hcone, hleaf, fun A hA hAS =>
            hcov A ((List.mem_cons.mp hA).resolve_left (by simp)) hAS⟩
      | falsePLL =>
          exact ⟨kids, leaf, ⟨prems⟩, hcone, hleaf, fun A hA hAS =>
            hcov A ((List.mem_cons.mp hA).resolve_left (by simp)) hAS⟩
      | and A' B' =>
          exact ⟨kids, leaf, ⟨prems⟩, hcone, hleaf, fun A hA hAS =>
            hcov A ((List.mem_cons.mp hA).resolve_left (by simp)) hAS⟩
      | or A' B' =>
          exact ⟨kids, leaf, ⟨prems⟩, hcone, hleaf, fun A hA hAS =>
            hcov A ((List.mem_cons.mp hA).resolve_left (by simp)) hAS⟩
      | ifThen A' B' =>
          exact ⟨kids, leaf, ⟨prems⟩, hcone, hleaf, fun A hA hAS =>
            hcov A ((List.mem_cons.mp hA).resolve_left (by simp)) hAS⟩
      | somehow A₀ =>
          cases leaf with
          | true => exact ⟨kids, true, ⟨prems⟩, hcone, hleaf, fun _ _ _ => Or.inl rfl⟩
          | false =>
              rcases Decidable.em (PLLFormula.somehow A₀ ∈ S) with hmem | hmem
              · have hmemU : PLLFormula.somehow A₀ ∈ sfPlus G := ((hS _).mp hmem).1
                have hA₀U : A₀ ∈ sfPlus G := sfPlus_box hmemU
                have hforce : (Reject.join Mods D).force none (.somehow A₀) :=
                  ((hS _).mp hmem).2
                rcases ((Reject.join_force_box_iff D A₀).mp hforce).1 with
                  hroot | ⟨i, u, hSu, hu⟩
                · -- the root realises the obligation itself
                  have hA₀S : A₀ ∈ S := (hS _).mpr ⟨hA₀U, hroot⟩
                  refine ⟨kids, false, ⟨prems⟩, hcone, hleaf, fun A hA hAS => ?_⟩
                  rcases List.mem_cons.mp hA with h | h
                  · have hAA : A = A₀ := by injection h
                    exact Or.inr (Or.inr (hAA ▸ hA₀S))
                  · exact hcov A h hAS
                · rcases all_or_witness ((hE.comp i).force_dec u) (sfPlus G) with
                    hall | ⟨C'', hC''U, hC''⟩
                  · -- the realiser forces the whole universe: one fallible leaf
                    exact ⟨[], true, ⟨fun K hK => absurd hK List.not_mem_nil⟩,
                      fun K hK => absurd hK List.not_mem_nil,
                      fun _ => ⟨i, u, hSu, hall⟩, fun _ _ _ => Or.inl rfl⟩
                  · -- the realiser refutes something: it becomes a cone kid
                    obtain ⟨S', hS', ⟨d⟩⟩ := ih i (hE.comp i) u C'' hC''U hC''
                    refine ⟨⟨S', C''⟩ :: kids, false, ⟨consPrems d prems⟩, ?_, hleaf, ?_⟩
                    · intro K hK
                      rcases List.mem_cons.mp hK with rfl | hK
                      · exact ⟨i, u, hSu, hS'⟩
                      · exact hcone K hK
                    · intro A hA hAS
                      rcases List.mem_cons.mp hA with h | h
                      · have hAA : A = A₀ := by injection h
                        subst hAA
                        exact Or.inr (Or.inl ⟨⟨S', C''⟩, List.mem_cons_self,
                          (hS' A).mpr ⟨hA₀U, hu⟩⟩)
                      · rcases hcov A h hAS with h1 | ⟨K, hK, hAK⟩ | h1
                        · exact Or.inl h1
                        · exact Or.inr (Or.inl ⟨K, List.mem_cons_of_mem _ hK, hAK⟩)
                        · exact Or.inr (Or.inr h1)
              · refine ⟨kids, false, ⟨prems⟩, hcone, hleaf, fun A hA hAS => ?_⟩
                rcases List.mem_cons.mp hA with h | h
                · have hAA : A = A₀ := by injection h
                  exact absurd (hAA ▸ hAS) hmem
                · exact hcov A h hAS

/-- **The join case of the reconstruction.**  A component world is the
component's own induction hypothesis, transported by `join_force_comp`;
the root runs an inner induction on the goal, with the `world` node
assembled by `exists_cone_kids`. -/
theorem recon_join (ih : CompIH G b Mods) (hE : Effective (Reject.join Mods D)) :
    ∀ (r : (Reject.join Mods D).W) (C : PLLFormula), C ∈ sfPlus G →
      ¬ (Reject.join Mods D).force r C →
      ∃ S : List PLLFormula,
        (∀ φ, φ ∈ S ↔ (φ ∈ sfPlus G ∧ (Reject.join Mods D).force r φ)) ∧
        Nonempty (FRJD G b ⟨S, C⟩) := by
  intro r
  cases r with
  | some x =>
      obtain ⟨i, a⟩ := x
      intro C hmem hnf
      obtain ⟨S, hS, hd⟩ := ih i (hE.comp i) a C hmem
        (fun hc => hnf ((Reject.join_force_comp D C i a).mpr hc))
      refine ⟨S, fun φ => ?_, hd⟩
      rw [hS φ]
      exact and_congr_right fun _ => (Reject.join_force_comp D φ i a).symm
  | none =>
      obtain ⟨S, hS⟩ := exists_restrict
        (fun φ => (Reject.join Mods D).force none φ) (hE.force_dec none) (sfPlus G)
      obtain ⟨kids, leaf, ⟨prems⟩, hcone, hleaf, hcov⟩ := exists_cone_kids ih hE S hS S
      have hRi : ∀ v : (Reject.join Mods D).W, (Reject.join Mods D).Ri none v :=
        fun _ => True.intro
      have hSU : ∀ φ ∈ S, φ ∈ sfPlus G := fun φ hφ => ((hS φ).mp hφ).1
      have hpos : ∀ A, PLLFormula.somehow A ∈ S →
          leaf = true ∨ (∃ K ∈ kids, A ∈ K.stable) ∨ A ∈ S := fun A h => hcov A h h
      -- heredity of the root zone into every cone kid
      have hkid : ∀ K ∈ kids, ∀ φ ∈ S, φ ∈ K.stable := by
        intro K hK φ hφ
        obtain ⟨i, u, hSu, hKth⟩ := hcone K hK
        obtain ⟨hm, hf⟩ := (hS φ).mp hφ
        exact (hKth φ).mpr ⟨hm, (Reject.join_force_comp D φ i u).mp
          ((Reject.join Mods D).force_hered (hRi (some ⟨i, u⟩)) hf)⟩
      -- the root zone persists into any world above the root
      have habove : ∀ (i : ι) (y : (Mods i).W) (S' : List PLLFormula),
          (∀ φ, φ ∈ S' ↔ (φ ∈ sfPlus G ∧ (Mods i).force y φ)) →
          S.all (fun φ => S'.contains φ) = true := by
        intro i y S' hS'
        refine List.all_eq_true.mpr (fun φ hφ => ?_)
        obtain ⟨hm, hf⟩ := (hS φ).mp hφ
        exact List.elem_iff.mpr ((hS' φ).mpr ⟨hm,
          (Reject.join_force_comp D φ i y).mp
            ((Reject.join Mods D).force_hered (hRi (some ⟨i, y⟩)) hf)⟩)
      suffices h : ∀ C : PLLFormula, C ∈ sfPlus G →
          ¬ (Reject.join Mods D).force none C → Nonempty (FRJD G b ⟨S, C⟩) by
        exact fun C h1 h2 => ⟨S, hS, h C h1 h2⟩
      intro C
      induction C with
      | prop a =>
          intro hmem hnf
          exact ⟨.world kids (List.replicate kids.length true) leaf prems
            (worldOK_cone hSU hmem hkid hpos (fun hc => hnf ((hS _).mp hc).2))⟩
      | falsePLL =>
          intro hmem _
          exact ⟨.world kids (List.replicate kids.length true) leaf prems
            (worldOK_cone hSU hmem hkid hpos trivial)⟩
      | and A B ihA ihB =>
          intro hmem hnf
          rcases hE.force_dec none A with hA | hA
          · obtain ⟨d⟩ := ihB (sfPlus_and_right hmem) (fun hB => hnf ⟨hA, hB⟩)
            exact ⟨.andR2 d⟩
          · obtain ⟨d⟩ := ihA (sfPlus_and_left hmem) hA
            exact ⟨.andR1 d⟩
      | or A B ihA ihB =>
          intro hmem hnf
          obtain ⟨d⟩ := ihA (sfPlus_or_left hmem) (fun h => hnf (Or.inl h))
          obtain ⟨e⟩ := ihB (sfPlus_or_right hmem) (fun h => hnf (Or.inr h))
          exact ⟨.orR d e⟩
      | ifThen A B _ ihB =>
          intro hmem hnf
          obtain ⟨v, -, hA, hB⟩ := hE.imp_wit none A B hnf
          cases v with
          | none =>
              obtain ⟨d⟩ := ihB (sfPlus_imp_right hmem) hB
              exact ⟨.impIn d (List.elem_iff.mpr ((hS A).mpr ⟨sfPlus_imp_left hmem, hA⟩))⟩
          | some x =>
              obtain ⟨i, y⟩ := x
              obtain ⟨S', hS', ⟨d⟩⟩ := ih i (hE.comp i) y B (sfPlus_imp_right hmem)
                (fun hc => hB ((Reject.join_force_comp D B i y).mpr hc))
              exact ⟨.impOut d (List.elem_iff.mpr ((hS' A).mpr
                ⟨sfPlus_imp_left hmem, (Reject.join_force_comp D A i y).mp hA⟩))
                (habove i y S' hS')⟩
      | somehow A _ =>
          intro hmem hnf
          obtain ⟨v, -, hcone'⟩ := hE.box_wit none A hnf
          cases v with
          | some x =>
              obtain ⟨i, y⟩ := x
              have hnb : ¬ (Mods i).force y (.somehow A) := by
                intro hc
                obtain ⟨z, hz, hfz⟩ := hc y ((Mods i).refl_i y)
                exact hcone' (some ⟨i, z⟩) (.mk hz)
                  ((Reject.join_force_comp D A i z).mpr hfz)
              obtain ⟨S', hS', ⟨d⟩⟩ := ih i (hE.comp i) y (.somehow A) hmem hnb
              exact ⟨.circOut d (habove i y S' hS')⟩
          | none =>
              have hnA : ¬ (Reject.join Mods D).force none A := hcone' none True.intro
              have hleaff : leaf = false := by
                cases hl : leaf with
                | false => rfl
                | true =>
                    obtain ⟨i, u, hSu, hall⟩ := hleaf hl
                    exact absurd ((Reject.join_force_comp D A i u).mpr
                      (hall A (sfPlus_box hmem))) (hcone' (some ⟨i, u⟩) hSu)
              refine ⟨.world kids (List.replicate kids.length true) leaf prems
                (worldOK_cone hSU hmem hkid hpos
                  ⟨hleaff, fun hc => hnA ((hS A).mp hc).2, fun K hK hAK => ?_⟩)⟩
              obtain ⟨i, u, hSu, hKth⟩ := hcone K hK
              exact hcone' (some ⟨i, u⟩) hSu ((Reject.join_force_comp D A i u).mpr
                ((hKth A).mp hAK).2)

end JoinRoot

/-! ## The reconstruction theorem -/

/-- **The reconstruction theorem.**  Every world of a BUILT model, and
every formula of the cell's universe it refutes, carry an FRJ◯
derivation whose stable zone is exactly that world's restricted theory.

Structural induction on `Reject.Built`, with an inner induction on the
goal at each root.  Choice-free: the only non-constructive content is
the `Effective` hypothesis, which is a hypothesis. -/
theorem recon {G : Cell} {b : Nat} :
    ∀ {M : ConstraintModel}, Reject.Built M → Effective M →
      ∀ (r : M.W) (C : PLLFormula), C ∈ sfPlus G → ¬ M.force r C →
        ∃ S : List PLLFormula,
          (∀ φ, φ ∈ S ↔ (φ ∈ sfPlus G ∧ M.force r φ)) ∧
          Nonempty (FRJD G b ⟨S, C⟩) := by
  intro M hB
  induction hB with
  | solo V₀ fal hfull =>
      intro hE r C hmem hnf
      cases r
      exact recon_solo hE C hmem hnf
  | join Mods D _ ihj => intro hE; exact recon_join ihj hE

/-! ## The corollaries -/

/-- **`ReconstructionSolo` (FRJO/Reconstruct.lean), PROVED.** -/
theorem reconstructionSolo (b : Nat) : ReconstructionSolo b := by
  intro Γ C V₀ fal hfull hΓ hC
  obtain ⟨S, hS, hd⟩ := recon_solo (G := ⟨Γ, C⟩) (b := b)
    (effective_of_classical _) C (sfPlus_goal ⟨Γ, C⟩) hC
  exact ⟨⟨S, C⟩, rfl, fun φ hφ => (hS φ).mpr ⟨sfPlus_ctx _ φ hφ, hΓ φ hφ⟩, hd⟩

/-- **`Reconstruction` (FRJO/Complete.lean), PROVED.**  The classical
step is `effective_of_classical` alone; `recon` itself is choice-free. -/
theorem reconstruction (b : Nat) : Reconstruction b := by
  intro Γ C M r hB hΓ hC
  obtain ⟨S, hS, hd⟩ := recon (G := ⟨Γ, C⟩) (b := b) hB
    (effective_of_classical M) r C (sfPlus_goal ⟨Γ, C⟩) hC
  exact ⟨⟨S, C⟩, rfl, fun φ hφ => (hS φ).mpr ⟨sfPlus_ctx _ φ hφ, hΓ φ hφ⟩, hd⟩

/-- **Completeness for FRJ◯, unconditional.**  `completenessFRJO` was
already proved conditional on `Reconstruction`; with `reconstruction`
the hypothesis is discharged. -/
theorem completenessFRJO' {b : Nat} {Γ : List PLLFormula} {C : PLLFormula}
    (h : ¬ Nonempty (PLLND.LaxND Γ C)) :
    ∃ S : Reg ⟨Γ, C⟩, S.goal = C ∧ Γ ⊆ S.stable ∧
      Nonempty (FRJD ⟨Γ, C⟩ b S) :=
  completenessFRJO (reconstruction b) h

/-- **The biconditional, in the shape completeness can actually feed.**

`frjd_iff_not_laxND` (`FRJO/Complete.lean`) asks its derivation for
`S.stable = Γ`, which `completenessFRJO'` does not deliver and cannot:
the zone `recon` builds is the refuting world's THEORY, in general
strictly larger than the context.  The missing glue is `LaxND.rename`
— a proof over `Γ` transports to any superset — and with it the two
sides match exactly.

VACUOUS as it stands: `ExtractForces` is REFUTED for `worldOK` v3
(`FRJO/Screen.lean`).  Stated here so that the shape is on record for
the v4 repair, which is the only thing between this and the
biconditional the campaign is for. -/
theorem frjd_iff' {b : Nat} {Γ : List PLLFormula} {C : PLLFormula}
    (hE : ExtractForces ⟨Γ, C⟩ b) :
    (∃ S : Reg ⟨Γ, C⟩, S.goal = C ∧ Γ ⊆ S.stable ∧
        Nonempty (FRJD ⟨Γ, C⟩ b S)) ↔ ¬ Nonempty (PLLND.LaxND Γ C) := by
  constructor
  · rintro ⟨S, hg, hsub, ⟨d⟩⟩ ⟨p⟩
    refine not_laxND_of_FRJD hE d ⟨?_⟩
    rw [hg]
    exact p.rename fun ψ hψ => hsub hψ
  · exact fun h => completenessFRJO' (b := b) h

/-! ## Pins

Transcribed verbatim from the build output.  The three reconstruction
theorems are CHOICE-FREE; `Classical.choice` enters only at
`effective_of_classical`, i.e. only in the corollaries stated over an
arbitrary (non-effective) model. -/

/-- info: 'FRJO.recon_solo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms recon_solo

/-- info: 'FRJO.exists_cone_kids' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms exists_cone_kids

/-- info: 'FRJO.recon_join' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms recon_join

/-- info: 'FRJO.recon' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms recon

/--
info: 'FRJO.reconstructionSolo' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms reconstructionSolo

/--
info: 'FRJO.reconstruction' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms reconstruction

/--
info: 'FRJO.completenessFRJO'' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms completenessFRJO'

/--
info: 'FRJO.frjd_iff'' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms frjd_iff'

end FRJO
