import wip.esakiaNuclearGen

/-!
# Nuclear Esakia duality: proofs of the bridge statements R1–R4 (Phase A)

R2 is proved choice-free.  R1, R3a, R3b, R3c and R4 are proved with
classical logic, and for R1, R3c and R4 that is NECESSARY: each implies
double-negation elimination for every proposition (`r1_dne`, `r3c_dne`,
`r4_dne`, themselves choice-free).  The reason is the same in each case:
the statements are about the library's models, whose sets (`S`, `V a`,
`Rᵢ`) are arbitrary propositions, and `j_S(U) = X ∖ ↓(S ∖ U)` reads the
`◯`-clause through a double negation.
-/

namespace EsakiaNuclear.Bridge

open Set PLLND PLLFormula

/-! ## R2 (choice-free) -/

theorem r2 : R2 := by
  refine ⟨fun C φ => rfl, fun C U hU => ⟨⟨?_, ?_⟩, ?_⟩, fun C U => ?_, fun C U V hU => ?_⟩
  · intro x y hxy hx v hyv
    exact hx v (C.trans_i hxy hyv)
  · intro f hf v hfv
    exact ⟨v, C.refl_m v, hU.2 (C.hered_F hfv hf)⟩
  · intro w hw v hwv
    exact ⟨v, C.refl_m v, hU.1 hwv hw⟩
  · intro w hw v hwv
    obtain ⟨u, hvu, hu⟩ := hw v hwv
    obtain ⟨u', huu', hu'⟩ := hu u (C.refl_i u)
    exact ⟨u', C.trans_m hvu huu', hu'⟩
  · apply Set.Subset.antisymm
    · intro w hw
      exact ⟨fun v hwv => let ⟨u, h1, h2⟩ := hw v hwv; ⟨u, h1, h2.1⟩,
        fun v hwv => let ⟨u, h1, h2⟩ := hw v hwv; ⟨u, h1, h2.2⟩⟩
    · rintro w ⟨hwU, hwV⟩ v hwv
      obtain ⟨u1, hvu1, hu1⟩ := hwU v hwv
      obtain ⟨u2, hu12, hu2⟩ := hwV u1 (C.trans_i hwv (C.sub_mi hvu1))
      exact ⟨u2, C.trans_m hvu1 hu12, hU (C.sub_mi hu12) hu1, hu2⟩

/-! ## R1 (classical; necessarily so) -/

theorem r1 : R1 := by
  refine ⟨fun M φ => ?_, fun M U hU => ?_, fun M U => ⟨?_, ?_⟩, fun M U V => ?_⟩
  · ext x
    show (∀ v, M.le x v → v ∈ M.S → M.force v φ) ↔ ¬ ∃ y, M.le x y ∧ y ∈ M.S ∧ ¬ M.force y φ
    constructor
    · rintro h ⟨y, hxy, hyS, hn⟩
      exact hn (h y hxy hyS)
    · intro h v hxv hvS
      exact Classical.byContradiction fun hn => h ⟨v, hxv, hvS, hn⟩
  · rintro x hx ⟨y, hxy, hyS, hyU⟩
    exact hyU (hU hxy hx)
  · rintro x y hxy hx ⟨z, hyz, hz⟩
    exact hx ⟨z, M.trans hxy hyz, hz⟩
  · rintro x hx ⟨y, hxy, hyS, hyU⟩
    exact hx ⟨y, hxy, hyS, fun hy => hy ⟨y, M.refl y, hyS, hyU⟩⟩
  · apply Set.Subset.antisymm
    · intro x hx
      exact ⟨fun ⟨y, hxy, hyS, hyU⟩ => hx ⟨y, hxy, hyS, fun h => hyU h.1⟩,
        fun ⟨y, hxy, hyS, hyV⟩ => hx ⟨y, hxy, hyS, fun h => hyV h.2⟩⟩
    · rintro x ⟨hxU, hxV⟩ ⟨y, hxy, hyS, hyUV⟩
      exact hxU ⟨y, hxy, hyS, fun hyU => hxV ⟨y, hxy, hyS, fun hyV => hyUV ⟨hyU, hyV⟩⟩⟩

/-- The one-point subframe model whose `p` is the proposition `P`. -/
def pointModel (P : Prop) : SubframeModel where
  W := Unit
  le := fun _ _ => True
  S := univ
  V := fun _ => setOf fun _ => P
  refl := fun _ => trivial
  trans := fun _ _ => trivial
  hered := fun _ h => h

/-- **R1 needs classical logic**: it implies `¬¬P → P` for every `P`. -/
theorem r1_dne (h : R1) (P : Prop) : ¬¬P → P := by
  intro hnn
  have hf : ∀ y : (pointModel P).W, (pointModel P).force y (.prop "p") ↔ P := fun _ => Iff.rfl
  have e := h.1 (pointModel P) (.prop "p")
  have hj : () ∈ SubframeModel.jS (pointModel P) (SubframeModel.truth (pointModel P) (.prop "p")) :=
    fun ⟨y, _, _, hn⟩ => hnn fun hp => hn ((hf y).mpr hp)
  rw [← e] at hj
  exact (hf ()).mp (hj () trivial (mem_univ _))

/-! ## R3 (classical) -/

theorem r3a : R3a := by
  intro C hanti w
  constructor
  · intro h u hwu
    refine Classical.byContradiction fun hn => ?_
    have hne : u ≠ w := fun e => hn (e ▸ C.refl_m u)
    have hu : ¬ C.Ri u w := fun hr => hne (hanti hr (C.sub_mi hwu))
    have hw : w ∈ ConstraintModel.jC C (ConstraintModel.mPt C w) := by
      intro v hwv
      by_cases hv : v = w
      · subst hv; exact ⟨u, hwu, hu⟩
      · exact ⟨v, C.refl_m v, fun hr => hv (hanti hr hwv)⟩
    rw [h] at hw
    exact hw (C.refl_i w)
  · intro hfin
    ext x
    constructor
    · intro hx hxw
      have hw : w ∈ ConstraintModel.jC C (ConstraintModel.mPt C w) :=
        fun v hwv => hx v (C.trans_i hxw hwv)
      obtain ⟨u, hwu, hu⟩ := hw w (C.refl_i w)
      exact hu (C.sub_mi (hfin u hwu))
    · intro hx v hxv
      exact ⟨v, C.refl_m v, fun hvw => hx (C.trans_i hxv hvw)⟩

theorem mPt_HC (C : ConstraintModel) {w : C.W} (hw : w ∉ C.F) :
    ConstraintModel.HC C (ConstraintModel.mPt C w) :=
  ⟨fun hxy hx hyw => hx (C.trans_i hxy hyw), fun _ hf hfw => hw (C.hered_F hfw hf)⟩

theorem r3c : R3c := by
  intro C
  refine ⟨fun w hw => ⟨mPt_HC C hw, fun e => ?_, fun U V hU hV hUV => ?_⟩, fun v w => ?_⟩
  · have : w ∈ ConstraintModel.mPt C w := e ▸ mem_univ w
    exact this (C.refl_i w)
  · have sub : ∀ {X}, ConstraintModel.HC C X → w ∉ X → X ⊆ ConstraintModel.mPt C w :=
      fun hX hwX _ hx hxw => hwX (hX.1 hxw hx)
    by_cases hwU : w ∈ U
    · by_cases hwV : w ∈ V
      · exact absurd (C.refl_i w) (hUV ⟨hwU, hwV⟩)
      · exact Or.inr (sub hV hwV)
    · exact Or.inl (sub hU hwU)
  · constructor
    · intro h
      exact Classical.byContradiction fun hn => (h hn) (C.refl_i w)
    · intro hwv x hx hxw
      exact hx (C.trans_i hxw hwv)

/-- A two-world constraint model in which `false Rᵢ true` is the proposition
`P`. -/
def dneModel (P : Prop) : ConstraintModel where
  W := Bool
  Ri := fun a b => a = b ∨ (a = false ∧ b = true ∧ P)
  Rm := fun a b => a = b
  F := ∅
  V := fun _ => ∅
  refl_i := fun _ => Or.inl rfl
  trans_i := by
    rintro a b c (rfl | ⟨rfl, rfl, hp⟩) (rfl | ⟨h1, rfl, hp2⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨h1, rfl, hp2⟩
    · exact Or.inr ⟨rfl, rfl, hp⟩
    · exact absurd h1 Bool.noConfusion
  refl_m := fun _ => rfl
  trans_m := fun h1 h2 => h1.trans h2
  sub_mi := fun h => Or.inl h
  hered_F := fun _ h => h.elim
  hered_V := fun _ h => h.elim
  full_F := fun h => h.elim

/-- **R3c needs classical logic**: it implies `¬¬P → P` for every `P`. -/
theorem r3c_dne (h : R3c) (P : Prop) : ¬¬P → P := by
  intro hnn
  have e := ((h (dneModel P)).2 true false).mp
  have hsub : ConstraintModel.mPt (dneModel P) true ⊆ ConstraintModel.mPt (dneModel P) false := by
    intro u hu hu'
    rcases hu' with hu' | ⟨_, h2, _⟩
    · subst hu'
      exact hnn fun hp => hu (Or.inr ⟨rfl, rfl, hp⟩)
    · exact Bool.noConfusion h2
  rcases e hsub with h1 | ⟨_, _, hp⟩
  · exact absurd h1 Bool.noConfusion
  · exact hp

theorem r3b : R3b := by
  classical
  intro C hfin m ⟨hm, hmne, hprime⟩
  obtain ⟨n, ⟨eq⟩⟩ := Finite.exists_equiv_fin C.W
  let D := ((List.finRange n).map eq.symm).filter fun x => decide (x ∉ m)
  have hD : ∀ {x}, x ∈ D ↔ x ∉ m := by
    intro x
    rw [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨List.mem_map.mpr ⟨eq x, List.mem_finRange _, by simp⟩, h⟩⟩
  -- the intersection of the `mPt x`, `x ∈ L`, inside `m` gives one of them
  have key : ∀ L : List C.W, (∀ x ∈ L, x ∉ m) →
      (⋂ x ∈ L, ConstraintModel.mPt C x) ⊆ m → ∃ x ∈ L, ConstraintModel.mPt C x ⊆ m := by
    intro L
    induction L with
    | nil =>
        intro _ h
        exact absurd (Set.eq_univ_of_univ_subset (by simpa using h)) hmne
    | cons a L ih =>
        intro hL h
        have ha : a ∉ m := hL a List.mem_cons_self
        have haF : a ∉ C.F := fun hf => ha (hm.2 hf)
        have hI : ConstraintModel.HC C (⋂ x ∈ L, ConstraintModel.mPt C x) := by
          refine ⟨fun hxy hx => ?_, fun f hf => ?_⟩
          · simp only [mem_iInter] at hx ⊢
            exact fun x hxL hyx => hx x hxL (C.trans_i hxy hyx)
          · simp only [mem_iInter]
            exact fun x hxL hfx => (hL x (List.mem_cons_of_mem a hxL)) (hm.2 (C.hered_F hfx hf))
        have hsplit : ConstraintModel.mPt C a ∩ (⋂ x ∈ L, ConstraintModel.mPt C x) ⊆ m := by
          intro y hy
          apply h
          rw [mem_inter_iff, mem_iInter₂] at hy
          rw [mem_iInter₂]
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hy.1
          · exact hy.2 x hx
        rcases hprime _ _ (mPt_HC C haF) hI hsplit with h1 | h1
        · exact ⟨a, List.mem_cons_self, h1⟩
        · obtain ⟨x, hx, hxm⟩ := ih (fun x hx => hL x (List.mem_cons_of_mem a hx)) h1
          exact ⟨x, List.mem_cons_of_mem a hx, hxm⟩
  have hcover : (⋂ x ∈ D, ConstraintModel.mPt C x) ⊆ m := by
    intro y hy
    simp only [mem_iInter] at hy
    exact Classical.byContradiction fun hn => hy y (hD.mpr hn) (C.refl_i y)
  obtain ⟨x, hx, hxm⟩ := key D (fun x hx => hD.mp hx) hcover
  have hxm' := hD.mp hx
  refine ⟨x, fun hf => hxm' (hm.2 hf), Set.Subset.antisymm (fun y hy hyx => ?_) hxm⟩
  exact hxm' (hm.1 hyx hy)

/-! ## R4 (classical; necessarily so) -/

theorem r4 : R4 := by
  intro M x
  constructor
  · intro h
    exact Classical.byContradiction fun hn => h none hn
  · intro hx u hu
    cases u with
    | none => exact absurd hx hu
    | some y =>
        have hxy : x = y := hu
        show y = x
        exact hxy.symm

/-- The one-point subframe model whose single point is in `S` iff `P`. -/
def sModel (P : Prop) : SubframeModel where
  W := Unit
  le := fun _ _ => True
  S := setOf fun _ => P
  V := fun _ => ∅
  refl := fun _ => trivial
  trans := fun _ _ => trivial
  hered := fun _ h => h

/-- **R4 needs classical logic**: it implies `¬¬P → P` for every `P`. -/
theorem r4_dne (h : R4) (P : Prop) : ¬¬P → P := by
  intro hnn
  refine (h (sModel P) ()).mp fun u hu => ?_
  cases u with
  | none => exact absurd hu hnn
  | some y => exact (show () = y from hu) ▸ rfl

end EsakiaNuclear.Bridge

#axioms_within EsakiaNuclear.Bridge.r2 [propext, Quot.sound]
#axioms_within EsakiaNuclear.Bridge.r1 [propext, Classical.choice, Quot.sound]
#axioms_within EsakiaNuclear.Bridge.r1_dne []
#axioms_within EsakiaNuclear.Bridge.r3a [propext, Classical.choice, Quot.sound]
#axioms_within EsakiaNuclear.Bridge.r3b [propext, Classical.choice, Quot.sound]
#axioms_within EsakiaNuclear.Bridge.r3c [propext, Classical.choice, Quot.sound]
#axioms_within EsakiaNuclear.Bridge.r3c_dne []
#axioms_within EsakiaNuclear.Bridge.r4 [propext, Classical.choice, Quot.sound]
#axioms_within EsakiaNuclear.Bridge.r4_dne []
