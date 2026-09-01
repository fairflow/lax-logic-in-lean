/-
# The W-database lemma layer, `◯` cases — Lemma 9 (11–14) and 13/14

The `◯`-layer of `wip/gbu_circ.lean`'s database lemmas, transcribed to
the W-database.  Genuinely NEW content, beyond renaming:

* `gbuInv12`/`gbuInv13` take the PLEDGED lookup `WEvalRP` where the
  V-versions needed the global `TagClean` supply — the tag-explicit
  database carries the pledge through (DB2), so no supply is needed.
* `gbuInvLift` — the W-family's new general regular→irregular
  transfer, from `Lift`: on a `Ĝ`-context, `WEvalR` gives `WEvalI` at
  ANY goal.  This is what the old `BigAnte` was groping for.
* `gbuInv14` (the irregular-`◯` `Clo`-monotonicity) gains a `lift`
  case: the W-family has a fourth producer of irregular `◯`-rows, and
  re-admission at the enlarged zone goes through `Lift` itself.
-/
import wip.gbu_frjw_db

namespace FRJ.Gbu.W

open FRJ Form FRJ.Gbu FRJ.Search

theorem gbuInv11 {D : WSeq → Prop} {Ψ : List Form} {Z C : Form}
    (h : WEvalR D (Z :: Ψ) C) : WEvalR D (.circ Z :: Ψ) C := by
  obtain ⟨t, Γ, hmem, hcl⟩ := h
  refine ⟨t, Γ, hmem, fun X hX => ?_⟩
  rcases List.mem_cons.mp hX with rfl | hX'
  · exact .circ (hcl Z List.mem_cons_self)
  · exact hcl X (List.mem_cons_of_mem _ hX')


theorem evalI_axI_gHat {G : Form} {D : WSeq → Prop} (hsat : WSaturated G D)
    {Ω : List Form} {F : Form} (hΩ : ∀ X ∈ Ω, X ∈ gHat G)
    (hFp : F.isPrime = true) (hF : F ∈ sfR G) (hFn : F ∉ Ω) : WEvalI D Ω F := by
  obtain ⟨s', hs'mem, hsub⟩ :=
    hsat.2 (.irr [] (rm (gAt G) F ++ gImp G ++ gCirc G) F)
      ⟨.axI F hFp hF (CtxEq.refl _)⟩
  match s', hsub with
  | .irr St' Th' _, ⟨rfl, hSt, hTh⟩ =>
      refine ⟨St', Th', hs'mem,
        fun {x} hx => absurd ((hSt x).mpr hx) List.not_mem_nil, ?_⟩
      intro x hx
      refine List.mem_append_right _ (hTh ?_)
      rcases gHat_cases (hΩ x hx) with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
      · exact List.mem_append_left _ (List.mem_append_left _
          (mem_rm.mpr ⟨fun he => hFn (he ▸ hx), h⟩))
      · exact List.mem_append_left _ (List.mem_append_right _ h)
      · exact List.mem_append_right _ h


/-- **Lemma 11, modal case.** -/
theorem gbuSuccAtF {G : Form} {D : WSeq → Prop} (hsat : WSaturated G D)
    {Ω : List Form} {F : Form}
    (hΩ : ∀ X ∈ Ω, X ∈ gHat G)
    (hFp : F.isPrime = true) (hFgoal : F ∈ sfR G) (hFmem : F ∉ Ω)
    (himp : ∀ A B, Form.imp A B ∈ Ω → WEvalI D Ω A) :
    WEvalR D Ω F := by
  let U := F :: (impPart Ω).map ante
  let E := enumOf U (by simp [U])
  let f := E.f
  have hfmem : ∀ j, f j ∈ U := fun j =>
    (E.spec (f j)).mp (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)
  have hwit : ∀ j, ∃ p : List Form × List Form,
      D (.irr p.1 p.2 (f j)) ∧ p.1 ⊆ Ω ∧ Ω ⊆ p.1 ++ p.2 := by
    intro j
    have hev : WEvalI D Ω (f j) := by
      by_cases e₀ : f j = F
      · exact e₀ ▸ evalI_axI_gHat hsat hΩ hFp hFgoal hFmem
      have hm : f j ∈ (impPart Ω).map ante := by
        rcases List.mem_cons.mp (hfmem j) with h | h
        · exact absurd h e₀
        · exact h
      obtain ⟨X, hXmem, hante⟩ := List.mem_map.mp hm
      obtain ⟨hXΩ, hXi⟩ := List.mem_filter.mp hXmem
      match X, hXi with
      | .imp A B, _ =>
          have hA : A = f j := hante
          exact hA ▸ himp A B hXΩ
    obtain ⟨St, Th, k₁, k₂, k₃⟩ := hev
    exact ⟨(St, Th), k₁, k₂, k₃⟩
  obtain ⟨g, hg⟩ := finEx hwit
  set St : Fin (E.n + 1) → List Form := fun j => (g j).1 with hStdef
  set Th : Fin (E.n + 1) → List Form := fun j => (g j).2 with hThdef
  have hStTh : ∀ j, D (.irr (St j) (Th j) (f j)) := fun j => (hg j).1
  have hStΩ : ∀ j, St j ⊆ Ω := fun j => (hg j).2.1
  have hΩSt : ∀ j, Ω ⊆ St j ++ Th j := fun j => (hg j).2.2
  obtain ⟨d⟩ := finPi (fun j => hsat.1 _ (hStTh j))
  have hJ1 : ∀ i j, i ≠ j → St i ⊆ St j ++ Th j :=
    fun i j _ => fun {_} hX => hΩSt j (hStΩ i hX)
  have hJ2 : ∀ A B : Form,
      Form.imp A B ∈ unionAll (fun j => impPart (St j)) → A ∈ upsilon f := by
    intro A B hmem
    obtain ⟨j, hj⟩ := mem_unionAll.mp hmem
    have hAB : Form.imp A B ∈ Ω := hStΩ j (List.mem_filter.mp hj).1
    exact (E.spec A).mpr (List.mem_cons_of_mem _
      (List.mem_map.mpr ⟨.imp A B, List.mem_filter.mpr ⟨hAB, rfl⟩, rfl⟩))
  have hFn : F ∉ unionAll (fun j => atPart (St j)) := by
    intro hX
    obtain ⟨j, hj⟩ := mem_unionAll.mp hX
    exact hFmem (hStΩ j (List.mem_filter.mp hj).1)
  obtain ⟨s', hs'mem, hsub⟩ :=
    hsat.2 (.reg .blocked (joinCtxAtF St Th f F) F)
      ⟨.joinAtF (fun j => d j) hJ1 hJ2 hFp hFn hFgoal (CtxEq.refl _)⟩
  match s', hsub with
  | .reg t' Γ' _, ⟨rfl, _, hΓ⟩ =>
      refine ⟨t', Γ', hs'mem, fun X hX => .base (hΓ ?_)⟩
      rcases gHat_cases (hΩ X hX) with ⟨_, hpv⟩ | ⟨_, hi⟩ | ⟨_, hc⟩
      · by_cases hin : ∃ j, X ∈ St j
        · obtain ⟨j, hj⟩ := hin
          exact List.mem_append_left _ (List.mem_append_left _
            (List.mem_append_left _ (List.mem_append_left _
              (mem_unionAll.mpr ⟨j, List.mem_filter.mpr ⟨hj, hpv⟩⟩))))
        · have hall : ∀ j, X ∈ Th j := by
            intro j
            rcases List.mem_append.mp (hΩSt j hX) with h' | h'
            · exact absurd ⟨j, h'⟩ hin
            · exact h'
          refine List.mem_append_left _ (List.mem_append_left _
            (List.mem_append_left _ (List.mem_append_right _
              (mem_rm.mpr ⟨fun he => hFmem (he ▸ hX), ?_⟩))))
          exact mem_interAll.mpr (fun j => List.mem_filter.mpr ⟨hall j, hpv⟩)
      · by_cases hin : ∃ j, X ∈ St j
        · obtain ⟨j, hj⟩ := hin
          exact List.mem_append_left _ (List.mem_append_left _
            (List.mem_append_right _
              (mem_unionAll.mpr ⟨j, List.mem_filter.mpr ⟨hj, hi⟩⟩)))
        · have hall : ∀ j, X ∈ Th j := by
            intro j
            rcases List.mem_append.mp (hΩSt j hX) with h' | h'
            · exact absurd ⟨j, h'⟩ hin
            · exact h'
          refine List.mem_append_left _ (List.mem_append_right _ ?_)
          match X, hi with
          | .imp A B, _ =>
              refine mem_restrict.mpr ⟨?_, ?_⟩
              · exact mem_interAll.mpr (fun j => List.mem_filter.mpr ⟨hall j, rfl⟩)
              · exact (E.spec A).mpr (List.mem_cons_of_mem _
                  (List.mem_map.mpr ⟨.imp A B,
                    List.mem_filter.mpr ⟨hX, rfl⟩, rfl⟩))
      · -- the `◯` case: `⋈^At_F` keeps the whole modal zone
        by_cases hin : ∃ j, X ∈ St j
        · obtain ⟨j, hj⟩ := hin
          exact List.mem_append_right _ (List.mem_append_left _
            (mem_unionAll.mpr ⟨j, List.mem_filter.mpr ⟨hj, hc⟩⟩))
        · have hall : ∀ j, X ∈ Th j := by
            intro j
            rcases List.mem_append.mp (hΩSt j hX) with h' | h'
            · exact absurd ⟨j, h'⟩ hin
            · exact h'
          refine List.mem_append_right _ (List.mem_append_right _ ?_)
          exact mem_interAll.mpr (fun j => List.mem_filter.mpr ⟨hall j, hc⟩)

/-- **Lemma 12, modal case.** -/
theorem gbuSuccOrF {G : Form} {D : WSeq → Prop} (hsat : WSaturated G D)
    {Ω : List Form} {C₁ C₂ : Form}
    (hΩ : ∀ X ∈ Ω, X ∈ gHat G)
    (hgoal : Form.or C₁ C₂ ∈ sfR G)
    (himp : ∀ A B, Form.imp A B ∈ Ω → WEvalI D Ω A)
    (h₁ : WEvalI D Ω C₁) (h₂ : WEvalI D Ω C₂) :
    WEvalR D Ω (.or C₁ C₂) := by
  let U := C₁ :: C₂ :: (impPart Ω).map ante
  let E := enumOf U (by simp [U])
  let f := E.f
  have hfmem : ∀ j, f j ∈ U := fun j =>
    (E.spec (f j)).mp (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)
  have hwit : ∀ j, ∃ p : List Form × List Form,
      D (.irr p.1 p.2 (f j)) ∧ p.1 ⊆ Ω ∧ Ω ⊆ p.1 ++ p.2 := by
    intro j
    have hev : WEvalI D Ω (f j) := by
      by_cases e₁ : f j = C₁
      · exact e₁ ▸ h₁
      by_cases e₂ : f j = C₂
      · exact e₂ ▸ h₂
      have hm : f j ∈ (impPart Ω).map ante := by
        rcases List.mem_cons.mp (hfmem j) with h | h
        · exact absurd h e₁
        · rcases List.mem_cons.mp h with h' | h'
          · exact absurd h' e₂
          · exact h'
      obtain ⟨X, hXmem, hante⟩ := List.mem_map.mp hm
      obtain ⟨hXΩ, hXi⟩ := List.mem_filter.mp hXmem
      match X, hXi with
      | .imp A B, _ =>
          have hA : A = f j := hante
          exact hA ▸ himp A B hXΩ
    obtain ⟨St, Th, k₁, k₂, k₃⟩ := hev
    exact ⟨(St, Th), k₁, k₂, k₃⟩
  obtain ⟨g, hg⟩ := finEx hwit
  set St : Fin (E.n + 1) → List Form := fun j => (g j).1 with hStdef
  set Th : Fin (E.n + 1) → List Form := fun j => (g j).2 with hThdef
  have hStTh : ∀ j, D (.irr (St j) (Th j) (f j)) := fun j => (hg j).1
  have hStΩ : ∀ j, St j ⊆ Ω := fun j => (hg j).2.1
  have hΩSt : ∀ j, Ω ⊆ St j ++ Th j := fun j => (hg j).2.2
  obtain ⟨d⟩ := finPi (fun j => hsat.1 _ (hStTh j))
  have hJ1 : ∀ i j, i ≠ j → St i ⊆ St j ++ Th j :=
    fun i j _ => fun {_} hX => hΩSt j (hStΩ i hX)
  have hJ2 : ∀ A B : Form,
      Form.imp A B ∈ unionAll (fun j => impPart (St j)) → A ∈ upsilon f := by
    intro A B hmem
    obtain ⟨j, hj⟩ := mem_unionAll.mp hmem
    have hAB : Form.imp A B ∈ Ω := hStΩ j (List.mem_filter.mp hj).1
    exact (E.spec A).mpr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_map.mpr ⟨.imp A B, List.mem_filter.mpr ⟨hAB, rfl⟩, rfl⟩)))
  obtain ⟨s', hs'mem, hsub⟩ :=
    hsat.2 (.reg .blocked (joinCtxOrF St Th f) (.or C₁ C₂))
      ⟨.joinOrF (fun j => d j) hJ1 hJ2
        ⟨(E.spec C₁).mpr List.mem_cons_self,
         (E.spec C₂).mpr (List.mem_cons_of_mem _ List.mem_cons_self)⟩
        hgoal (CtxEq.refl _)⟩
  match s', hsub with
  | .reg t' Γ' _, ⟨rfl, _, hΓ⟩ =>
      refine ⟨t', Γ', hs'mem, fun X hX => .base (hΓ ?_)⟩
      rcases gHat_cases (hΩ X hX) with ⟨_, hpv⟩ | ⟨_, hi⟩ | ⟨_, hc⟩
      · by_cases hin : ∃ j, X ∈ St j
        · obtain ⟨j, hj⟩ := hin
          exact List.mem_append_left _ (List.mem_append_left _
            (List.mem_append_left _ (List.mem_append_left _
              (mem_unionAll.mpr ⟨j, List.mem_filter.mpr ⟨hj, hpv⟩⟩))))
        · have hall : ∀ j, X ∈ Th j := by
            intro j
            rcases List.mem_append.mp (hΩSt j hX) with h' | h'
            · exact absurd ⟨j, h'⟩ hin
            · exact h'
          refine List.mem_append_left _ (List.mem_append_left _
            (List.mem_append_left _ (List.mem_append_right _ ?_)))
          exact mem_interAll.mpr (fun j => List.mem_filter.mpr ⟨hall j, hpv⟩)
      · by_cases hin : ∃ j, X ∈ St j
        · obtain ⟨j, hj⟩ := hin
          exact List.mem_append_left _ (List.mem_append_left _
            (List.mem_append_right _
              (mem_unionAll.mpr ⟨j, List.mem_filter.mpr ⟨hj, hi⟩⟩)))
        · have hall : ∀ j, X ∈ Th j := by
            intro j
            rcases List.mem_append.mp (hΩSt j hX) with h' | h'
            · exact absurd ⟨j, h'⟩ hin
            · exact h'
          refine List.mem_append_left _ (List.mem_append_right _ ?_)
          match X, hi with
          | .imp A B, _ =>
              refine mem_restrict.mpr ⟨?_, ?_⟩
              · exact mem_interAll.mpr (fun j => List.mem_filter.mpr ⟨hall j, rfl⟩)
              · exact (E.spec A).mpr (List.mem_cons_of_mem _
                  (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨.imp A B,
                    List.mem_filter.mpr ⟨hX, rfl⟩, rfl⟩)))
      · by_cases hin : ∃ j, X ∈ St j
        · obtain ⟨j, hj⟩ := hin
          exact List.mem_append_right _ (List.mem_append_left _
            (mem_unionAll.mpr ⟨j, List.mem_filter.mpr ⟨hj, hc⟩⟩))
        · have hall : ∀ j, X ∈ Th j := by
            intro j
            rcases List.mem_append.mp (hΩSt j hX) with h' | h'
            · exact absurd ⟨j, h'⟩ hin
            · exact h'
          refine List.mem_append_right _ (List.mem_append_right _ ?_)
          exact mem_interAll.mpr (fun j => List.mem_filter.mpr ⟨hall j, hc⟩)


theorem refutedCleanly_and1 {G : Form} {Ω : List Form} {A B : Form}
    (hgoal : Form.and A B ∈ sfR G) (h : WRefutedCleanly G Ω A) :
    WRefutedCleanly G Ω (.and A B) :=
  let ⟨Γ, t, ⟨d⟩, htag, hcov⟩ := h
  ⟨Γ, t, ⟨.andR1 d hgoal⟩,
    htag.elim Or.inl (fun ⟨W, hg, hc⟩ => Or.inr ⟨W, hg, .andL hc⟩), hcov⟩

theorem refutedCleanly_and2 {G : Form} {Ω : List Form} {A B : Form}
    (hgoal : Form.and A B ∈ sfR G) (h : WRefutedCleanly G Ω B) :
    WRefutedCleanly G Ω (.and A B) :=
  let ⟨Γ, t, ⟨d⟩, htag, hcov⟩ := h
  ⟨Γ, t, ⟨.andR2 d hgoal⟩,
    htag.elim Or.inl (fun ⟨W, hg, hc⟩ => Or.inr ⟨W, hg, .andR hc⟩), hcov⟩

/-- `⊃∈`.  The antecedent is asked for in the CONTEXT of the premise, which
is where `impIn`'s own `Clo Γ A` side condition comes from. -/
theorem refutedCleanly_imp {G : Form} {Ω : List Form} {A B : Form}
    (hgoal : Form.imp A B ∈ sfR G) (h : WRefutedCleanly G (A :: Ω) B) :
    WRefutedCleanly G Ω (.imp A B) :=
  let ⟨Γ, t, ⟨d⟩, htag, hcov⟩ := h
  let hA : Clo Γ A := hcov A List.mem_cons_self
  ⟨Γ, t, ⟨.impIn d hA hgoal⟩,
    htag.elim Or.inl (fun ⟨W, hg, hc⟩ => Or.inr ⟨W, hg, .imp hc hA⟩),
    fun X hX => hcov X (List.mem_cons_of_mem _ hX)⟩

/-- `◯∈`, whose side condition is exactly `WRefutedCleanly`'s tag clause. -/
theorem refutedCleanly_circIn {G : Form} {Ω : List Form} {Z : Form}
    (hgoal : Form.circ Z ∈ sfR G) (h : WRefutedCleanly G Ω Z) :
    WRefutedCleanly G Ω (.circ Z) :=
  let ⟨Γ, t, ⟨d⟩, htag, hcov⟩ := h
  ⟨Γ, t, ⟨.circIn d htag hgoal⟩,
    htag.elim Or.inl (fun ⟨W, hg, hc⟩ => Or.inr ⟨W, hg, .circ hc⟩), hcov⟩


theorem refutedCleanly_circ {G : Form} {D : WSeq → Prop} (hsat : WSaturated G D)
    {Ω : List Form} {Z : Form}
    (hΩ : ∀ X ∈ Ω, X ∈ gAt G ++ gImp G)
    (hgoal : Form.circ Z ∈ sfR G)
    (himp : ∀ A B, Form.imp A B ∈ Ω → WEvalI D Ω A)
    (hz : WEvalI D Ω Z) :
    WRefutedCleanly G Ω (.circ Z) := by
  let U := Z :: (impPart Ω).map ante
  let E := enumOf U (by simp [U])
  let f := E.f
  have hfmem : ∀ j, f j ∈ U := fun j =>
    (E.spec (f j)).mp (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)
  have hwit : ∀ j, ∃ p : List Form × List Form,
      D (.irr p.1 p.2 (f j)) ∧ p.1 ⊆ Ω ∧ Ω ⊆ p.1 ++ p.2 := by
    intro j
    have hev : WEvalI D Ω (f j) := by
      by_cases e₀ : f j = Z
      · exact e₀ ▸ hz
      have hm : f j ∈ (impPart Ω).map ante := by
        rcases List.mem_cons.mp (hfmem j) with h | h
        · exact absurd h e₀
        · exact h
      obtain ⟨X, hXmem, hante⟩ := List.mem_map.mp hm
      obtain ⟨hXΩ, hXi⟩ := List.mem_filter.mp hXmem
      match X, hXi with
      | .imp A B, _ =>
          have hA : A = f j := hante
          exact hA ▸ himp A B hXΩ
    obtain ⟨St, Th, k₁, k₂, k₃⟩ := hev
    exact ⟨(St, Th), k₁, k₂, k₃⟩
  obtain ⟨g, hg⟩ := finEx hwit
  set St : Fin (E.n + 1) → List Form := fun j => (g j).1 with hStdef
  set Th : Fin (E.n + 1) → List Form := fun j => (g j).2 with hThdef
  have hStTh : ∀ j, D (.irr (St j) (Th j) (f j)) := fun j => (hg j).1
  have hStΩ : ∀ j, St j ⊆ Ω := fun j => (hg j).2.1
  have hΩSt : ∀ j, Ω ⊆ St j ++ Th j := fun j => (hg j).2.2
  obtain ⟨d⟩ := finPi (fun j => hsat.1 _ (hStTh j))
  have hJ1 : ∀ i j, i ≠ j → St i ⊆ St j ++ Th j :=
    fun i j _ => fun {_} hX => hΩSt j (hStΩ i hX)
  have hJ2 : ∀ A B : Form,
      Form.imp A B ∈ unionAll (fun j => impPart (St j)) → A ∈ upsilon f := by
    intro A B hmem
    obtain ⟨j, hj⟩ := mem_unionAll.mp hmem
    have hAB : Form.imp A B ∈ Ω := hStΩ j (List.mem_filter.mp hj).1
    exact (E.spec A).mpr (List.mem_cons_of_mem _
      (List.mem_map.mpr ⟨.imp A B, List.mem_filter.mpr ⟨hAB, rfl⟩, rfl⟩))
  have hcirc : unionAll (fun j => circPart (St j)) = [] := by
    refine eq_nil_of_forall_not_mem (fun X hX => ?_)
    obtain ⟨j, hj⟩ := mem_unionAll.mp hX
    obtain ⟨hmem, hc⟩ := List.mem_filter.mp hj
    exact absurd hc (by
      rw [not_isCirc_of_gHatAtImp (hΩ X (hStΩ j hmem))]
      exact fun h => Bool.noConfusion h)
  refine ⟨_, .barren,
    ⟨.joinCirc (fun j => d j) hJ1 hJ2 hcirc (keptChainRestrict _ Th)
      (.ups ((E.spec Z).mpr List.mem_cons_self)) hgoal (CtxEq.refl _)⟩,
    Or.inl rfl, fun X hX => .base ?_⟩
  by_cases hin : ∃ j, X ∈ St j
  · obtain ⟨j, hj⟩ := hin
    refine List.mem_append_left _ ?_
    by_cases hi : X.isImp
    · exact List.mem_append_right _
        (mem_unionAll.mpr ⟨j, List.mem_filter.mpr ⟨hj, hi⟩⟩)
    · refine List.mem_append_left _ (List.mem_append_left _
        (mem_unionAll.mpr ⟨j, List.mem_filter.mpr ⟨hj, ?_⟩⟩))
      have := mem_gAt_of_not_imp (hΩ X hX) (by simpa using hi)
      exact (List.mem_filter.mp this).2
  · have hall : ∀ j, X ∈ Th j := by
      intro j
      rcases List.mem_append.mp (hΩSt j hX) with h' | h'
      · exact absurd ⟨j, h'⟩ hin
      · exact h'
    by_cases hi : X.isImp
    · refine List.mem_append_right _ ?_
      match X, hi with
      | .imp A B, _ =>
          refine mem_restrict.mpr ⟨?_, ?_⟩
          · exact List.mem_filter.mpr ⟨mem_interAll.mpr hall, rfl⟩
          · exact (E.spec A).mpr (List.mem_cons_of_mem _
              (List.mem_map.mpr ⟨.imp A B,
                List.mem_filter.mpr ⟨hX, rfl⟩, rfl⟩))
    · refine List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_right _ ?_))
      refine mem_interAll.mpr (fun j => List.mem_filter.mpr ⟨hall j, ?_⟩)
      have := mem_gAt_of_not_imp (hΩ X hX) (by simpa using hi)
      exact (List.mem_filter.mp this).2

/-- Lemma 13, MODAL zone — `gbuSuccCirc` is the clean refutation, forgotten

    into the database. -/
theorem gbuSuccCirc {G : Form} {D : WSeq → Prop} (hsat : WSaturated G D)
    {Ω : List Form} {Z : Form}
    (hΩ : ∀ X ∈ Ω, X ∈ gAt G ++ gImp G)
    (hgoal : Form.circ Z ∈ sfR G)
    (himp : ∀ A B, Form.imp A B ∈ Ω → WEvalI D Ω A)
    (hz : WEvalI D Ω Z) :
    WEvalR D Ω (.circ Z) :=
  wEvalR_of_refutedCleanly hsat (refutedCleanly_circ hsat hΩ hgoal himp hz)


/-- **Lemma 14** — the success lemma for the IRREGULAR `◯` goal, and the
clearing of obstruction 1.  `◯∉` turns a CLEAN refutation of `Ω ⇒ Z`
into an irregular refutation of `Ω →g ◯Z`; (DB2) then puts it in the
database.  No query on `Υ` is needed — the implications are already
carried by `Γ`'s covering of `Ω`. -/
theorem gbuSuccCircI {G : Form} {D : WSeq → Prop} (hsat : WSaturated G D)
    {Ω : List Form} {Z : Form}
    (hΩ : ∀ X ∈ Ω, X ∈ gHat G) (hgoal : Form.circ Z ∈ sfR G)
    (hcl : WRefutedCleanly G Ω Z) : WEvalI D Ω (.circ Z) := by
  obtain ⟨Γ, t, ⟨d⟩, htag, hcov⟩ := hcl
  obtain ⟨s', hs'mem, hsub⟩ :=
    hsat.2 (.irr [] Ω (.circ Z))
      ⟨.circNotIn d htag (fun X hX => ⟨hcov X hX, hΩ X hX⟩) hgoal⟩
  match s', hsub with
  | .irr St' Th' _, ⟨rfl, hSt, hTh⟩ =>
      exact ⟨St', Th', hs'mem,
        fun {x} hx => absurd ((hSt x).mpr hx) List.not_mem_nil,
        fun {x} hx => List.mem_append_right _ (hTh hx)⟩

/-- **Lemma 9, clause 14, W-form** — the irregular `◯` goal is
`Clo`-monotone.  By cases on the row: the W-family adds the `lift`
producer, whose re-admission at the enlarged zone goes through
`Lift` itself. -/
theorem gbuInv14 {G : Form} {D : WSeq → Prop} (hsat : WSaturated G D)
    {Ω Ω' : List Form} {Z : Form}
    (hΩ : ∀ X ∈ Ω, X ∈ gHat G) (hcl : ∀ X ∈ Ω, Clo Ω' X)
    (h : WEvalI D Ω' (.circ Z)) : WEvalI D Ω (.circ Z) := by
  obtain ⟨St, Th, hmem, h1, h2⟩ := h
  obtain ⟨d⟩ := hsat.1 (.irr St Th (.circ Z)) hmem
  cases d with
  | axI F hF hgoal hTh => exact Bool.noConfusion hF
  | circNotIn dr htag hTh hgoal =>
      -- `◯∉`: re-admit the zone, enlarged by `Ω`
      obtain ⟨s', hs'mem, hsub⟩ :=
        hsat.2 (.irr [] (Ω ++ Th) (.circ Z))
          ⟨.circNotIn dr htag (fun X hX => by
              rcases List.mem_append.mp hX with hX' | hX'
              · refine ⟨?_, hΩ X hX'⟩
                refine clo_trans (fun Y hY => ?_) (hcl X hX')
                exact (hTh Y (by
                  have := h2 hY
                  simpa using this)).1
              · exact hTh X hX') hgoal⟩
      match s', hsub with
      | .irr St' Th' _, ⟨rfl, hSt, hTh'⟩ =>
          exact ⟨St', Th', hs'mem,
            fun {x} hx => absurd ((hSt x).mpr hx) List.not_mem_nil,
            fun {x} hx => List.mem_append_right _ (hTh' (List.mem_append_left _ hx))⟩
  | lift dr hTh =>
      -- `Lift`: re-admit at the enlarged zone through `Lift` itself
      obtain ⟨s', hs'mem, hsub⟩ :=
        hsat.2 (.irr [] (Ω ++ Th) (.circ Z))
          ⟨.lift dr (fun X hX => by
              rcases List.mem_append.mp hX with hX' | hX'
              · refine ⟨?_, hΩ X hX'⟩
                refine clo_trans (fun Y hY => ?_) (hcl X hX')
                exact (hTh Y (by
                  have := h2 hY
                  simpa using this)).1
              · exact hTh X hX')⟩
      match s', hsub with
      | .irr St' Th' _, ⟨rfl, hSt, hTh'⟩ =>
          exact ⟨St', Th', hs'mem,
            fun {x} hx => absurd ((hSt x).mpr hx) List.not_mem_nil,
            fun {x} hx =>
              List.mem_append_right _ (hTh' (List.mem_append_left _ hx))⟩
  | axIC F ats hats hFf hgoal hThv =>
      -- `Ax^I◯`: the zone already contains `Ω`, classically
      refine ⟨[], Th, hmem, fun {x} hx => absurd hx List.not_mem_nil, ?_⟩
      intro x hx
      refine List.mem_append_right _ ((hThv x).mpr ?_)
      refine List.mem_filter.mpr ⟨hΩ x hx, ?_⟩
      refine clo_classForce (fun Y hY => ?_) (hcl x hx)
      have hY' : Y ∈ Th := by simpa using h2 hY
      exact (List.mem_filter.mp ((hThv Y).mp hY')).2

/-- On a `Ĝ`-context the invariant IS (BSr1). -/
theorem unrefutedBelow_of_gHat {G : Form} {D : WSeq → Prop} {Ω : List Form}
    {C : Form} (hΩ : ∀ X ∈ Ω, X ∈ gHat G) (h : ¬ WEvalI D Ω C) :
    WUnrefutedBelow G D Ω C :=
  ⟨h, Ω, hΩ, fun X hX => .base hX, h⟩

/-- …and every left rule preserves it, at a `◯` goal. -/
theorem unrefutedBelow_step {G : Form} {D : WSeq → Prop} (hsat : WSaturated G D)
    {Ω Ω' : List Form} {Z : Form} (hcl : ∀ X ∈ Ω, Clo Ω' X)
    (h : WUnrefutedBelow G D Ω (.circ Z)) : WUnrefutedBelow G D Ω' (.circ Z) := by
  obtain ⟨-, Ω₀, hΩ₀, hcl₀, hne₀⟩ := h
  have hcl₀' : ∀ X ∈ Ω₀, Clo Ω' X :=
    fun X hX => clo_trans hcl (hcl₀ X hX)
  exact ⟨fun hev => hne₀ (gbuInv14 hsat hΩ₀ hcl₀' hev), Ω₀, hΩ₀, hcl₀', hne₀⟩

/-- **Lemma 9, clause 12, W-form** — `R◯` from `◯∈` on a PLEDGED row.
The V-version needed `TagClean`; the pledged lookup replaces it. -/
theorem gbuInv12 {D : WSeq → Prop} (hsat : WSaturated G D)
    {Ψ : List Form} {Z : Form}
    (hgoal : Form.circ Z ∈ sfR G) (h : WEvalRP D Ψ Z) :
    WEvalR D Ψ (.circ Z) := by
  obtain ⟨t, Γ, hmem, htag, hcl⟩ := h
  obtain ⟨d⟩ := hsat.1 _ hmem
  obtain ⟨s', hs'mem, hsub⟩ :=
    hsat.2 (.reg t Γ (.circ Z)) ⟨.circIn d htag hgoal⟩
  match s', hsub with
  | .reg t' Γ' _, ⟨rfl, _, hΓ⟩ =>
      exact ⟨t', Γ', hs'mem, fun X hX => clo_mono hΓ (hcl X hX)⟩

/-- **Lemma 9, clause 13, W-form** — `R◯ₙᵢ` from `◯∉` on a pledged
row. -/
theorem gbuInv13 {D : WSeq → Prop} (hsat : WSaturated G D)
    {Ω : List Form} {Z : Form}
    (hgoal : Form.circ Z ∈ sfR G) (hΩ : ∀ X ∈ Ω, X ∈ gHat G)
    (h : WEvalRP D Ω Z) : WEvalI D Ω (.circ Z) := by
  obtain ⟨t, Γ, hmem, htag, hcl⟩ := h
  obtain ⟨d⟩ := hsat.1 _ hmem
  obtain ⟨s', hs'mem, hsub⟩ :=
    hsat.2 (.irr [] Ω (.circ Z))
      ⟨.circNotIn d htag (fun X hX => ⟨hcl X hX, hΩ X hX⟩) hgoal⟩
  match s', hsub with
  | .irr St' Th' _, ⟨rfl, hSt, hTh⟩ =>
      exact ⟨St', Th', hs'mem,
        fun {x} hx => absurd ((hSt x).mpr hx) List.not_mem_nil,
        fun {x} hx => List.mem_append_right _ (hTh hx)⟩

/-- **The `Lift` transfer** — the W-family's general regular→irregular
step: on a `Ĝ`-context, a regular refutation row yields an irregular
one at the SAME goal.  No tag condition, no goal condition; this is
what the retired `BigAnte` supply was groping for. -/
theorem gbuInvLift {D : WSeq → Prop} (hsat : WSaturated G D)
    {Ω : List Form} {C : Form}
    (hΩ : ∀ X ∈ Ω, X ∈ gHat G) (h : WEvalR D Ω C) : WEvalI D Ω C := by
  obtain ⟨t, Γ, hmem, hcl⟩ := h
  obtain ⟨d⟩ := hsat.1 _ hmem
  obtain ⟨s', hs'mem, hsub⟩ :=
    hsat.2 (.irr [] Ω C)
      ⟨.lift d (fun X hX => ⟨hcl X hX, hΩ X hX⟩)⟩
  match s', hsub with
  | .irr St' Th' _, ⟨rfl, hSt, hTh⟩ =>
      exact ⟨St', Th', hs'mem,
        fun {x} hx => absurd ((hSt x).mpr hx) List.not_mem_nil,
        fun {x} hx => List.mem_append_right _ (hTh hx)⟩

/-- The pledged lookup is a clean refutation (via (DB1)); composing
with `gbuSuccCircI` replaces the V-route's `EvalRC` version. -/
theorem wRefutedCleanly_of_wEvalRP {D : WSeq → Prop}
    (hsat : WSaturated G D) {Ω : List Form} {C : Form}
    (h : WEvalRP D Ω C) : WRefutedCleanly G Ω C := by
  obtain ⟨t, Γ, hmem, htag, hcl⟩ := h
  exact ⟨Γ, t, hsat.1 _ hmem, htag, hcl⟩


end FRJ.Gbu.W
