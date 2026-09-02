/-
# B1 and B2′: the join-family arity bounds, as general lemmas

`docs/a2-arity.md` §5; the designed cells are `wip/b1b2_cells.lean`.

    B1.   In a join family, a premise whose goal another premise shares
          is redundant: the sub-family dropping it satisfies the side
          conditions and its conclusion context contains the family's.

    B2′.  A promise family can be cut to any sub-family that still
          witnesses every modal formula the full family witnesses; the
          conclusion context only grows.

Both are statements about the join CONTEXT functions of
`FRJ/Calculus.lean`, `FRJ/CalculusV.lean` and `FRJ/RefAt.lean` under a
reindexing `e : Fin (m+1) → Fin (n+1)` of the family.  The subsumption
form (`WSubsumes`) is packaged at the end.

Method: every aggregate is monotone or antitone in the family (`⋃`
shrinks, `⋂` grows, `Υ` is preserved by a goal-covering reindexing),
and the one non-trivial step is the (J1) cover: a dropped premise's
stable zone lies inside `⋃Ξ ∪ ⋂Θ` of the survivors, since (J1) puts it
inside `Ξⱼ ++ Θⱼ` for every survivor `j`.  Kept implications transfer
through `keptOf_saturated` (the fixpoint property of the kept chain)
and `refAt_mono`.
-/
import FRJ.CalculusV
import FRJ.RefAt
import FRJ.Gbu.W.Dichotomy

open FRJ Form

namespace FRJ.Arity

/-! ## 1. Reindexing the aggregates -/

theorem mem_upsilon' {n : Nat} {rhs : Fin (n + 1) → Form} {x : Form} :
    x ∈ upsilon rhs ↔ ∃ j, rhs j = x := by
  simp [upsilon, List.mem_map, List.mem_finRange]

theorem unionAll_comp_sub {n m : Nat} (e : Fin (m + 1) → Fin (n + 1))
    (f : Fin (n + 1) → List Form) :
    unionAll (fun k => f (e k)) ⊆ unionAll f := by
  intro x hx
  rw [mem_unionAll] at hx ⊢
  obtain ⟨k, hk⟩ := hx
  exact ⟨e k, hk⟩

theorem interAll_sub_comp {n m : Nat} (e : Fin (m + 1) → Fin (n + 1))
    (f : Fin (n + 1) → List Form) :
    interAll f ⊆ interAll (fun k => f (e k)) := by
  intro x hx
  rw [mem_interAll] at hx ⊢
  exact fun k => hx (e k)

theorem upsilon_comp_sub {n m : Nat} (e : Fin (m + 1) → Fin (n + 1))
    (rhs : Fin (n + 1) → Form) :
    upsilon (fun k => rhs (e k)) ⊆ upsilon rhs := by
  intro x hx
  rw [mem_upsilon'] at hx ⊢
  obtain ⟨k, hk⟩ := hx
  exact ⟨e k, hk⟩

/-- A goal-covering reindexing preserves `Υ`. -/
theorem upsilon_sub_comp {n m : Nat} (e : Fin (m + 1) → Fin (n + 1))
    (rhs : Fin (n + 1) → Form) (hcov : ∀ j, ∃ k, rhs (e k) = rhs j) :
    upsilon rhs ⊆ upsilon (fun k => rhs (e k)) := by
  intro x hx
  rw [mem_upsilon'] at hx ⊢
  obtain ⟨j, hj⟩ := hx
  obtain ⟨k, hk⟩ := hcov j
  exact ⟨k, hk.trans hj⟩

theorem thPool_sub_comp {n m : Nat} (e : Fin (m + 1) → Fin (n + 1))
    (Θs : Fin (n + 1) → List Form) :
    thPool Θs ⊆ thPool (fun k => Θs (e k)) := by
  intro x hx
  have h := List.mem_filter.mp hx
  exact List.mem_filter.mpr ⟨interAll_sub_comp e Θs h.1, h.2⟩

/-- Constructive finite case split: if every index satisfies `P` or `Q`,
then some index satisfies `P` or every index satisfies `Q`. -/
theorem exists_or_forall : ∀ {m : Nat} (P Q : Fin (m + 1) → Prop),
    (∀ k, P k ∨ Q k) → (∃ k, P k) ∨ (∀ k, Q k)
  | 0, P, Q, h => by
      rcases h 0 with hp | hq
      · exact Or.inl ⟨0, hp⟩
      · exact Or.inr (fun k => Fin.cases hq (fun k => k.elim0) k)
  | m + 1, P, Q, h => by
      rcases exists_or_forall (fun k : Fin (m + 1) => P k.succ)
          (fun k => Q k.succ) (fun k => h k.succ) with ⟨k, hk⟩ | hall
      · exact Or.inl ⟨k.succ, hk⟩
      · rcases h 0 with hp | hq
        · exact Or.inl ⟨0, hp⟩
        · exact Or.inr (fun k => Fin.cases hq hall k)

/-! ## 2. The (J1) cover

A dropped premise `p` has `Ξs p ⊆ Ξs j ++ Θs j` for every survivor
`j = e k`; so each of its stable formulas is in some survivor's stable
zone or in every survivor's second zone. -/

theorem cover_of_j1 {n m : Nat} {Ξs Θs : Fin (n + 1) → List Form}
    (e : Fin (m + 1) → Fin (n + 1)) (p : Fin (n + 1)) (hne : ∀ k, e k ≠ p)
    (hJ1 : ∀ i j, i ≠ j → Ξs i ⊆ Ξs j ++ Θs j) {x : Form} (hx : x ∈ Ξs p) :
    (∃ k, x ∈ Ξs (e k)) ∨ (∀ k, x ∈ Θs (e k)) :=
  exists_or_forall _ _ (fun k =>
    List.mem_append.mp (hJ1 p (e k) (fun h => hne k h.symm) hx))

/-- Every stable formula of the family is a survivor's stable formula or
lies in every survivor's second zone. -/
theorem stable_cover {n m : Nat} {Ξs Θs : Fin (n + 1) → List Form}
    (e : Fin (m + 1) → Fin (n + 1)) (p : Fin (n + 1)) (hne : ∀ k, e k ≠ p)
    (hsurj : ∀ j, j ≠ p → ∃ k, e k = j)
    (hJ1 : ∀ i j, i ≠ j → Ξs i ⊆ Ξs j ++ Θs j) {x : Form}
    (hx : x ∈ unionAll Ξs) :
    (∃ k, x ∈ Ξs (e k)) ∨ (∀ k, x ∈ Θs (e k)) := by
  rw [mem_unionAll] at hx
  obtain ⟨j, hj⟩ := hx
  by_cases hjp : j = p
  · subst hjp
    exact cover_of_j1 e j hne hJ1 hj
  · obtain ⟨k, hk⟩ := hsurj j hjp
    exact Or.inl ⟨k, hk ▸ hj⟩

/-- A stable formula of the family with property `P` is a survivor's
stable `P`-formula or lies in the survivors' `⋂` of `P`-parts. -/
theorem part_cover {n m : Nat} {Ξs Θs : Fin (n + 1) → List Form}
    (e : Fin (m + 1) → Fin (n + 1)) (p : Fin (n + 1)) (hne : ∀ k, e k ≠ p)
    (hsurj : ∀ j, j ≠ p → ∃ k, e k = j)
    (hJ1 : ∀ i j, i ≠ j → Ξs i ⊆ Ξs j ++ Θs j)
    (P : Form → Bool) {x : Form}
    (hx : x ∈ unionAll (fun j => (Ξs j).filter P)) :
    x ∈ unionAll (fun k => (Ξs (e k)).filter P) ∨
      x ∈ interAll (fun k => (Θs (e k)).filter P) := by
  have hP : P x = true := by
    rw [mem_unionAll] at hx
    obtain ⟨j, hj⟩ := hx
    exact (List.mem_filter.mp hj).2
  have hx' : x ∈ unionAll Ξs := by
    rw [mem_unionAll] at hx ⊢
    obtain ⟨j, hj⟩ := hx
    exact ⟨j, (List.mem_filter.mp hj).1⟩
  rcases stable_cover e p hne hsurj hJ1 hx' with ⟨k, hk⟩ | hall
  · exact Or.inl (mem_unionAll.mpr ⟨k, List.mem_filter.mpr ⟨hk, hP⟩⟩)
  · exact Or.inr (mem_interAll.mpr (fun k => List.mem_filter.mpr ⟨hall k, hP⟩))

theorem isImp_shape {x : Form} (h : x.isImp = true) : ∃ A B, x = Form.imp A B := by
  cases x with
  | imp A B => exact ⟨A, B, rfl⟩
  | atom _ => simp [Form.isImp] at h
  | bot => simp [Form.isImp] at h
  | and _ _ => simp [Form.isImp] at h
  | or _ _ => simp [Form.isImp] at h
  | circ _ => simp [Form.isImp] at h

/-! ## 3. B1 for the barren `⋈^At` context

    ctxAt Ξs Θs rhs F = joinCtxAtVBase Ξs Θs F ++
                        keptOf (upsilon rhs) (joinCtxAtVBase Ξs Θs F) (thPool Θs)

(`FRJWr.joinAt`, and `emitJoinAt` in `FRJ/Gbu/W/Saturate.lean`). -/

def ctxAt {n : Nat} (Ξs Θs : Fin (n + 1) → List Form)
    (rhs : Fin (n + 1) → Form) (F : Form) : List Form :=
  joinCtxAtVBase Ξs Θs F ++
    keptOf (upsilon rhs) (joinCtxAtVBase Ξs Θs F) (thPool Θs)

/-- The base of the family's context is inside the sub-family's full
context: atoms by the cover, stable implications by the cover and the
kept fixpoint. -/
theorem baseAt_sub {n m : Nat} {Ξs Θs : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form} {F : Form}
    (e : Fin (m + 1) → Fin (n + 1)) (p : Fin (n + 1)) (hne : ∀ k, e k ≠ p)
    (hsurj : ∀ j, j ≠ p → ∃ k, e k = j) (hcov : ∀ j, ∃ k, rhs (e k) = rhs j)
    (hJ1 : ∀ i j, i ≠ j → Ξs i ⊆ Ξs j ++ Θs j)
    (hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (Ξs j)) →
      A ∈ upsilon rhs)
    (hF : F ∉ unionAll (fun j => atPart (Ξs j))) :
    joinCtxAtVBase Ξs Θs F ⊆
      ctxAt (fun k => Ξs (e k)) (fun k => Θs (e k)) (fun k => rhs (e k)) F := by
  intro x hx
  simp only [joinCtxAtVBase, List.mem_append] at hx
  simp only [ctxAt, joinCtxAtVBase, List.mem_append]
  rcases hx with (hat | hrm) | himp
  · -- a stable atom of the family
    rcases part_cover e p hne hsurj hJ1 Form.isPV hat with h | h
    · exact Or.inl (Or.inl (Or.inl h))
    · refine Or.inl (Or.inl (Or.inr ?_))
      rw [mem_rm]
      exact ⟨fun hxF => hF (hxF ▸ hat), h⟩
  · -- an atom of the family's ⋂Θ, minus F
    rw [mem_rm] at hrm
    refine Or.inl (Or.inl (Or.inr ?_))
    rw [mem_rm]
    exact ⟨hrm.1, interAll_sub_comp e _ hrm.2⟩
  · -- a stable implication of the family
    rcases part_cover e p hne hsurj hJ1 Form.isImp himp with h | h
    · exact Or.inl (Or.inr h)
    · -- it lies in every survivor's second zone: it is in the sub-pool,
      -- its antecedent is a goal (J2), so the kept fixpoint holds it
      refine Or.inr ?_
      have hpool : x ∈ thPool (fun k => Θs (e k)) := by
        have h' := List.mem_filter.mp (mem_interAll.mp h 0)
        refine List.mem_filter.mpr ⟨mem_interAll.mpr (fun k => ?_), h'.2⟩
        exact (List.mem_filter.mp (mem_interAll.mp h k)).1
      have hisImp : x.isImp = true := by
        rw [mem_unionAll] at himp
        obtain ⟨j, hj⟩ := himp
        exact (List.mem_filter.mp hj).2
      obtain ⟨A, B, rfl⟩ := isImp_shape hisImp
      have hA : A ∈ upsilon rhs := hJ2 A B himp
      have hA' : A ∈ upsilon (fun k => rhs (e k)) := upsilon_sub_comp e rhs hcov hA
      exact keptOf_saturated hpool (.ups hA')

/-- Every link of the family's kept chain is kept by the sub-family. -/
theorem keptAt_sub {n m : Nat} {Ξs Θs : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form} {F : Form}
    (e : Fin (m + 1) → Fin (n + 1)) (p : Fin (n + 1)) (hne : ∀ k, e k ≠ p)
    (hsurj : ∀ j, j ≠ p → ∃ k, e k = j) (hcov : ∀ j, ∃ k, rhs (e k) = rhs j)
    (hJ1 : ∀ i j, i ≠ j → Ξs i ⊆ Ξs j ++ Θs j)
    (hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (Ξs j)) →
      A ∈ upsilon rhs)
    (hF : F ∉ unionAll (fun j => atPart (Ξs j))) :
    keptOf (upsilon rhs) (joinCtxAtVBase Ξs Θs F) (thPool Θs) ⊆
      keptOf (upsilon (fun k => rhs (e k)))
        (joinCtxAtVBase (fun k => Ξs (e k)) (fun k => Θs (e k)) F)
        (thPool (fun k => Θs (e k))) := by
  have hchain := keptOf_ok (upsilon rhs) (joinCtxAtVBase Ξs Θs F) (thPool Θs)
  generalize hk : keptOf (upsilon rhs) (joinCtxAtVBase Ξs Θs F) (thPool Θs) = kept at hchain ⊢
  clear hk
  induction hchain with
  | nil => exact fun _ h => absurd h List.not_mem_nil
  | @cons Y B rest _ hmem href ih =>
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · -- the link: in the sub-pool, antecedent refuted over the sub-context
        have hpool' : Form.imp Y B ∈ thPool (fun k => Θs (e k)) :=
          thPool_sub_comp e Θs hmem
        have hctx : joinCtxAtVBase Ξs Θs F ++ rest ⊆
            joinCtxAtVBase (fun k => Ξs (e k)) (fun k => Θs (e k)) F ++
              keptOf (upsilon (fun k => rhs (e k)))
                (joinCtxAtVBase (fun k => Ξs (e k)) (fun k => Θs (e k)) F)
                (thPool (fun k => Θs (e k))) := by
          intro z hz
          rcases List.mem_append.mp hz with hz | hz
          · exact baseAt_sub e p hne hsurj hcov hJ1 hJ2 hF hz
          · exact List.mem_append_right _ (ih hz)
        have href' := refAt_mono (upsilon_sub_comp e rhs hcov) hctx href
        exact keptOf_saturated hpool' href'
      · exact ih hx'

/-- **B1 for `⋈^At`, the context half**: the family's conclusion context
is inside the sub-family's. -/
theorem ctxAt_sub {n m : Nat} {Ξs Θs : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form} {F : Form}
    (e : Fin (m + 1) → Fin (n + 1)) (p : Fin (n + 1)) (hne : ∀ k, e k ≠ p)
    (hsurj : ∀ j, j ≠ p → ∃ k, e k = j) (hcov : ∀ j, ∃ k, rhs (e k) = rhs j)
    (hJ1 : ∀ i j, i ≠ j → Ξs i ⊆ Ξs j ++ Θs j)
    (hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (Ξs j)) →
      A ∈ upsilon rhs)
    (hF : F ∉ unionAll (fun j => atPart (Ξs j))) :
    ctxAt Ξs Θs rhs F ⊆
      ctxAt (fun k => Ξs (e k)) (fun k => Θs (e k)) (fun k => rhs (e k)) F := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact baseAt_sub e p hne hsurj hcov hJ1 hJ2 hF h
  · exact List.mem_append_right _ (keptAt_sub e p hne hsurj hcov hJ1 hJ2 hF h)

/-! ## 4. The side conditions transfer to the sub-family -/

theorem j1_comp {n m : Nat} {Ξs Θs : Fin (n + 1) → List Form}
    (e : Fin (m + 1) → Fin (n + 1)) (hinj : ∀ k l, e k = e l → k = l)
    (hJ1 : ∀ i j, i ≠ j → Ξs i ⊆ Ξs j ++ Θs j) :
    ∀ k l, k ≠ l → Ξs (e k) ⊆ Ξs (e l) ++ Θs (e l) :=
  fun k l hkl => hJ1 (e k) (e l) (fun h => hkl (hinj k l h))

theorem j2_comp {n m : Nat} {Ξs : Fin (n + 1) → List Form} {rhs : Fin (n + 1) → Form}
    (e : Fin (m + 1) → Fin (n + 1)) (hcov : ∀ j, ∃ k, rhs (e k) = rhs j)
    (hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (Ξs j)) →
      A ∈ upsilon rhs) :
    ∀ A B : Form, Form.imp A B ∈ unionAll (fun k => impPart (Ξs (e k))) →
      A ∈ upsilon (fun k => rhs (e k)) :=
  fun A B h => upsilon_sub_comp e rhs hcov
    (hJ2 A B (unionAll_comp_sub e (fun j => impPart (Ξs j)) h))

theorem j3_comp {n m : Nat} {Ξs : Fin (n + 1) → List Form}
    (e : Fin (m + 1) → Fin (n + 1))
    (hJ3 : unionAll (fun j => circPart (Ξs j)) = []) :
    unionAll (fun k => circPart (Ξs (e k))) = [] :=
  List.eq_nil_of_subset_nil
    (fun x hx => hJ3 ▸ unionAll_comp_sub e (fun j => circPart (Ξs j)) hx)

theorem fNot_comp {n m : Nat} {Ξs : Fin (n + 1) → List Form} {F : Form}
    (e : Fin (m + 1) → Fin (n + 1))
    (hF : F ∉ unionAll (fun j => atPart (Ξs j))) :
    F ∉ unionAll (fun k => atPart (Ξs (e k))) :=
  fun h => hF (unionAll_comp_sub e (fun j => atPart (Ξs j)) h)

/-! ## 5. Dropping one premise whose goal another shares -/

/-- Mathlib's `Fin.succAbove_ne` carries `Classical.choice`; this one does
not. -/
theorem succAbove_ne' {n : Nat} (p : Fin (n + 1)) (k : Fin n) : p.succAbove k ≠ p := by
  intro h
  have hv := congrArg Fin.val h
  unfold Fin.succAbove at hv
  split at hv
  · rename_i hlt
    rw [Fin.lt_def] at hlt
    simp only [Fin.val_castSucc] at hlt hv
    omega
  · rename_i hge
    rw [Fin.lt_def] at hge
    simp only [Fin.val_castSucc, Fin.val_succ] at hge hv
    omega

theorem succAbove_surj {n : Nat} (p : Fin (n + 2)) :
    ∀ j, j ≠ p → ∃ k, p.succAbove k = j :=
  fun _ hj => Fin.exists_succAbove_eq hj

theorem succAbove_inj {n : Nat} (p : Fin (n + 2)) :
    ∀ k l, p.succAbove k = p.succAbove l → k = l :=
  fun _ _ h => Fin.succAbove_right_injective h

/-- A duplicate goal makes the drop goal-covering. -/
theorem cov_of_dup {n : Nat} {rhs : Fin (n + 2) → Form} (p i : Fin (n + 2))
    (hip : i ≠ p) (hgoal : rhs i = rhs p) :
    ∀ j, ∃ k, rhs (p.succAbove k) = rhs j := by
  intro j
  by_cases hjp : j = p
  · obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hip
    exact ⟨k, by rw [hk, hgoal, hjp]⟩
  · obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hjp
    exact ⟨k, by rw [hk]⟩

/-- **B1 for the barren `⋈^At`** (`FRJWr.joinAt`): in a family in which
premise `i` shares the goal of premise `p`, dropping `p` gives a family
that satisfies (J1)–(J3) and the target condition, and whose conclusion
context contains the original one. -/
theorem b1_joinAt {n : Nat} {Ξs Θs : Fin (n + 2) → List Form}
    {rhs : Fin (n + 2) → Form} {F : Form}
    (p i : Fin (n + 2)) (hip : i ≠ p) (hgoal : rhs i = rhs p)
    (hJ1 : ∀ i j, i ≠ j → Ξs i ⊆ Ξs j ++ Θs j)
    (hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (Ξs j)) →
      A ∈ upsilon rhs)
    (hJ3 : unionAll (fun j => circPart (Ξs j)) = [])
    (hF : F ∉ unionAll (fun j => atPart (Ξs j))) :
    (∀ k l, k ≠ l → Ξs (p.succAbove k) ⊆ Ξs (p.succAbove l) ++ Θs (p.succAbove l)) ∧
    (∀ A B : Form,
      Form.imp A B ∈ unionAll (fun k => impPart (Ξs (p.succAbove k))) →
      A ∈ upsilon (fun k => rhs (p.succAbove k))) ∧
    unionAll (fun k => circPart (Ξs (p.succAbove k))) = [] ∧
    F ∉ unionAll (fun k => atPart (Ξs (p.succAbove k))) ∧
    ctxAt Ξs Θs rhs F ⊆
      ctxAt (fun k => Ξs (p.succAbove k)) (fun k => Θs (p.succAbove k))
        (fun k => rhs (p.succAbove k)) F := by
  have hcov := cov_of_dup (rhs := rhs) p i hip hgoal
  exact ⟨j1_comp _ (succAbove_inj p) hJ1, j2_comp _ hcov hJ2, j3_comp _ hJ3,
    fNot_comp _ hF,
    ctxAt_sub (Fin.succAbove p) p (succAbove_ne' p)
      (succAbove_surj p) hcov hJ1 hJ2 hF⟩

/-! ## 6. The generic pieces for the other five contexts -/

theorem filter_mono {X X' : List Form} (f : Form → Bool) (h : X ⊆ X') :
    X.filter f ⊆ X'.filter f := by
  intro x hx
  have h' := List.mem_filter.mp hx
  exact List.mem_filter.mpr ⟨h h'.1, h'.2⟩

theorem inRestrict_mono {Υ Υ' : List Form} (hΥ : Υ ⊆ Υ') {x : Form}
    (h : inRestrict Υ x = true) : inRestrict Υ' x = true := by
  cases x with
  | imp A B =>
      simp only [inRestrict, decide_eq_true_eq] at h ⊢
      exact hΥ h
  | atom _ => simp [inRestrict] at h
  | bot => simp [inRestrict] at h
  | and _ _ => simp [inRestrict] at h
  | or _ _ => simp [inRestrict] at h
  | circ _ => simp [inRestrict] at h

theorem restrict_mono {X X' Υ Υ' : List Form} (hX : X ⊆ X') (hΥ : Υ ⊆ Υ') :
    restrict X Υ ⊆ restrict X' Υ' := by
  intro x hx
  have h := List.mem_filter.mp hx
  exact List.mem_filter.mpr ⟨hX h.1, inRestrict_mono hΥ h.2⟩

theorem isCirc_shape {x : Form} (h : x.isCirc = true) : ∃ Y, x = Form.circ Y := by
  cases x with
  | circ Y => exact ⟨Y, rfl⟩
  | atom _ => simp [Form.isCirc] at h
  | bot => simp [Form.isCirc] at h
  | and _ _ => simp [Form.isCirc] at h
  | or _ _ => simp [Form.isCirc] at h
  | imp _ _ => simp [Form.isCirc] at h

/-- Kept chains are monotone in `Υ`, in the pool, and in the base
(against the target's full kept context). -/
theorem keptOf_mono {Υ Υ' base base' pool pool' : List Form} (hΥ : Υ ⊆ Υ')
    (hpool : pool ⊆ pool') (hbase : base ⊆ base' ++ keptOf Υ' base' pool') :
    keptOf Υ base pool ⊆ keptOf Υ' base' pool' := by
  have hchain := keptOf_ok Υ base pool
  generalize hk : keptOf Υ base pool = kept at hchain ⊢
  clear hk
  induction hchain with
  | nil => exact fun _ h => absurd h List.not_mem_nil
  | @cons Y B rest _ hmem href ih =>
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · have hctx : base ++ rest ⊆ base' ++ keptOf Υ' base' pool' := by
          intro z hz
          rcases List.mem_append.mp hz with hz | hz
          · exact hbase hz
          · exact List.mem_append_right _ (ih hz)
        exact keptOf_saturated (hpool hmem) (refAt_mono hΥ hctx href)
      · exact ih hx'

section Pieces

variable {n m : Nat} {Ξs Θs : Fin (n + 1) → List Form} {rhs : Fin (n + 1) → Form}
  (e : Fin (m + 1) → Fin (n + 1)) (p : Fin (n + 1)) (hne : ∀ k, e k ≠ p)
  (hsurj : ∀ j, j ≠ p → ∃ k, e k = j)
  (hJ1 : ∀ i j, i ≠ j → Ξs i ⊆ Ξs j ++ Θs j)

include p hne hsurj hJ1 in
/-- A stable implication of the family is a survivor's stable implication
or a sub-pool implication whose antecedent is a goal. -/
theorem impU_cover (hcov : ∀ j, ∃ k, rhs (e k) = rhs j)
    (hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (Ξs j)) →
      A ∈ upsilon rhs)
    {x : Form} (hx : x ∈ unionAll (fun j => impPart (Ξs j))) :
    x ∈ unionAll (fun k => impPart (Ξs (e k))) ∨
      (x ∈ interAll (fun k => impPart (Θs (e k))) ∧
        ∃ A B, x = Form.imp A B ∧ A ∈ upsilon (fun k => rhs (e k))) := by
  rcases part_cover e p hne hsurj hJ1 Form.isImp hx with h | h
  · exact Or.inl h
  · refine Or.inr ⟨h, ?_⟩
    have hisImp : x.isImp = true := by
      rw [mem_unionAll] at hx
      obtain ⟨j, hj⟩ := hx
      exact (List.mem_filter.mp hj).2
    obtain ⟨A, B, rfl⟩ := isImp_shape hisImp
    exact ⟨A, B, rfl, upsilon_sub_comp e rhs hcov (hJ2 A B hx)⟩

/-- `⋂` of implication parts is the pool. -/
theorem interImp_eq_pool (Θs : Fin (n + 1) → List Form) :
    interAll (fun j => impPart (Θs j)) ⊆ thPool Θs := by
  intro x hx
  have h0 := List.mem_filter.mp (mem_interAll.mp hx 0)
  exact List.mem_filter.mpr
    ⟨mem_interAll.mpr (fun k => (List.mem_filter.mp (mem_interAll.mp hx k)).1), h0.2⟩

/-- The paper's restriction `Θ^⊃/Υ` (an intersection with goal
antecedents) of the family is inside the sub-family's. -/
theorem restrictInter_sub (hcov : ∀ j, ∃ k, rhs (e k) = rhs j) :
    restrict (interAll (fun j => impPart (Θs j))) (upsilon rhs) ⊆
      restrict (interAll (fun k => impPart (Θs (e k)))) (upsilon (fun k => rhs (e k))) :=
  restrict_mono (interAll_sub_comp e _) (upsilon_sub_comp e rhs hcov)

end Pieces

/-! ## 7. B1 for the remaining five contexts -/

/-- Barren `⋈^∨`, `⋈^◯` (`FRJWr.joinOr`, `FRJWr.joinCirc`). -/
def ctxOr {n : Nat} (Ξs Θs : Fin (n + 1) → List Form)
    (rhs : Fin (n + 1) → Form) : List Form :=
  joinCtxOrVBase Ξs Θs ++
    keptOf (upsilon rhs) (joinCtxOrVBase Ξs Θs) (thPool Θs)

section B1Rest

variable {n m : Nat} {Ξs Θs : Fin (n + 1) → List Form} {rhs : Fin (n + 1) → Form}
  (e : Fin (m + 1) → Fin (n + 1)) (p : Fin (n + 1)) (hne : ∀ k, e k ≠ p)
  (hsurj : ∀ j, j ≠ p → ∃ k, e k = j) (hcov : ∀ j, ∃ k, rhs (e k) = rhs j)
  (hJ1 : ∀ i j, i ≠ j → Ξs i ⊆ Ξs j ++ Θs j)
  (hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (Ξs j)) →
    A ∈ upsilon rhs)

include p hne hsurj hcov hJ1 hJ2

theorem baseOr_sub :
    joinCtxOrVBase Ξs Θs ⊆
      ctxOr (fun k => Ξs (e k)) (fun k => Θs (e k)) (fun k => rhs (e k)) := by
  intro x hx
  simp only [joinCtxOrVBase, List.mem_append] at hx
  simp only [ctxOr, joinCtxOrVBase, List.mem_append]
  rcases hx with (hat | hint) | himp
  · rcases part_cover e p hne hsurj hJ1 Form.isPV hat with h | h
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr h))
  · exact Or.inl (Or.inl (Or.inr (interAll_sub_comp e _ hint)))
  · rcases impU_cover e p hne hsurj hJ1 hcov hJ2 himp with h | ⟨hpool, A, B, rfl, hA⟩
    · exact Or.inl (Or.inr h)
    · exact Or.inr (keptOf_saturated (interImp_eq_pool _ hpool) (.ups hA))

/-- **B1 for `⋈^∨`/`⋈^◯`, the context half.** -/
theorem ctxOr_sub :
    ctxOr Ξs Θs rhs ⊆
      ctxOr (fun k => Ξs (e k)) (fun k => Θs (e k)) (fun k => rhs (e k)) := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact baseOr_sub e p hne hsurj hcov hJ1 hJ2 h
  · exact List.mem_append_right _
      (keptOf_mono (upsilon_sub_comp e rhs hcov) (thPool_sub_comp e Θs)
        (baseOr_sub e p hne hsurj hcov hJ1 hJ2) h)

/-- The paper's `⋈^At` context (used by the fallible and promise joins). -/
theorem joinCtxAt_sub {F : Form} (hF : F ∉ unionAll (fun j => atPart (Ξs j))) :
    joinCtxAt Ξs Θs rhs F ⊆
      joinCtxAt (fun k => Ξs (e k)) (fun k => Θs (e k)) (fun k => rhs (e k)) F := by
  intro x hx
  simp only [joinCtxAt, List.mem_append] at hx
  simp only [joinCtxAt, List.mem_append]
  rcases hx with ((hat | hrm) | himp) | hres
  · rcases part_cover e p hne hsurj hJ1 Form.isPV hat with h | h
    · exact Or.inl (Or.inl (Or.inl h))
    · refine Or.inl (Or.inl (Or.inr ?_))
      rw [mem_rm]
      exact ⟨fun hxF => hF (hxF ▸ hat), h⟩
  · rw [mem_rm] at hrm
    refine Or.inl (Or.inl (Or.inr ?_))
    rw [mem_rm]
    exact ⟨hrm.1, interAll_sub_comp e _ hrm.2⟩
  · rcases impU_cover e p hne hsurj hJ1 hcov hJ2 himp with h | ⟨hpool, A, B, rfl, hA⟩
    · exact Or.inl (Or.inr h)
    · exact Or.inr (List.mem_filter.mpr ⟨hpool, by simpa [inRestrict] using hA⟩)
  · exact Or.inr (restrictInter_sub e hcov hres)

/-- The paper's `⋈^∨` context. -/
theorem joinCtxOr_sub :
    joinCtxOr Ξs Θs rhs ⊆
      joinCtxOr (fun k => Ξs (e k)) (fun k => Θs (e k)) (fun k => rhs (e k)) := by
  intro x hx
  simp only [joinCtxOr, List.mem_append] at hx
  simp only [joinCtxOr, List.mem_append]
  rcases hx with ((hat | hint) | himp) | hres
  · rcases part_cover e p hne hsurj hJ1 Form.isPV hat with h | h
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr h))
  · exact Or.inl (Or.inl (Or.inr (interAll_sub_comp e _ hint)))
  · rcases impU_cover e p hne hsurj hJ1 hcov hJ2 himp with h | ⟨hpool, A, B, rfl, hA⟩
    · exact Or.inl (Or.inr h)
    · exact Or.inr (List.mem_filter.mpr ⟨hpool, by simpa [inRestrict] using hA⟩)
  · exact Or.inr (restrictInter_sub e hcov hres)

/-- The fallible modal part: `⋃Ξ^◯, ⋂Θ^◯`. -/
theorem joinCtxCircF_sub :
    joinCtxCircF Ξs Θs ⊆ joinCtxCircF (fun k => Ξs (e k)) (fun k => Θs (e k)) := by
  intro x hx
  simp only [joinCtxCircF, List.mem_append] at hx
  simp only [joinCtxCircF, List.mem_append]
  rcases hx with hu | hi
  · rcases part_cover e p hne hsurj hJ1 Form.isCirc hu with h | h
    · exact Or.inl h
    · exact Or.inr h
  · exact Or.inr (interAll_sub_comp e _ hi)

/-- The promise modal part under the SAME promise family: `⋃Ξ^◯` transfers
by the cover, with the (J5′) witness of the full family. -/
theorem joinCtxCircP_sub {k : Nat} {Δs : Fin (k + 1) → List Form}
    (hJ5 : ∀ Y, Form.circ Y ∈ unionAll (fun j => circPart (Ξs j)) → ∃ i, Clo (Δs i) Y) :
    joinCtxCircP Ξs Θs Δs ⊆ joinCtxCircP (fun k => Ξs (e k)) (fun k => Θs (e k)) Δs := by
  intro x hx
  simp only [joinCtxCircP, List.mem_append] at hx
  simp only [joinCtxCircP, List.mem_append]
  rcases hx with hu | hr
  · rcases part_cover e p hne hsurj hJ1 Form.isCirc hu with h | h
    · exact Or.inl h
    · have hisCirc : x.isCirc = true := by
        rw [mem_unionAll] at hu
        obtain ⟨j, hj⟩ := hu
        exact (List.mem_filter.mp hj).2
      obtain ⟨Y, rfl⟩ := isCirc_shape hisCirc
      exact Or.inr (mem_restrictC.mpr ⟨h, hJ5 Y hu⟩)
  · exact Or.inr (filter_mono _ (interAll_sub_comp e _) hr)

/-- **B1 for the fallible `⋈^At`** (`FRJWr.joinAtF`), the context half. -/
theorem joinCtxAtF_sub {F : Form} (hF : F ∉ unionAll (fun j => atPart (Ξs j))) :
    joinCtxAtF Ξs Θs rhs F ⊆
      joinCtxAtF (fun k => Ξs (e k)) (fun k => Θs (e k)) (fun k => rhs (e k)) F := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact List.mem_append_left _ (joinCtxAt_sub e p hne hsurj hcov hJ1 hJ2 hF h)
  · exact List.mem_append_right _ (joinCtxCircF_sub e p hne hsurj hcov hJ1 hJ2 h)

/-- **B1 for the fallible `⋈^∨`** (`FRJWr.joinOrF`), the context half. -/
theorem joinCtxOrF_sub :
    joinCtxOrF Ξs Θs rhs ⊆
      joinCtxOrF (fun k => Ξs (e k)) (fun k => Θs (e k)) (fun k => rhs (e k)) := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact List.mem_append_left _ (joinCtxOr_sub e p hne hsurj hcov hJ1 hJ2 h)
  · exact List.mem_append_right _ (joinCtxCircF_sub e p hne hsurj hcov hJ1 hJ2 h)

/-- **B1 for the promise `⋈^At`** (`FRJWr.joinAtP`), the context half. -/
theorem joinCtxAtP_sub {k : Nat} {Δs : Fin (k + 1) → List Form} {F : Form}
    (hF : F ∉ unionAll (fun j => atPart (Ξs j)))
    (hJ5 : ∀ Y, Form.circ Y ∈ unionAll (fun j => circPart (Ξs j)) → ∃ i, Clo (Δs i) Y) :
    joinCtxAtP Ξs Θs rhs F Δs ⊆
      joinCtxAtP (fun k => Ξs (e k)) (fun k => Θs (e k)) (fun k => rhs (e k)) F Δs := by
  refine filter_mono _ (fun x hx => ?_)
  rcases List.mem_append.mp hx with h | h
  · exact List.mem_append_left _ (joinCtxAt_sub e p hne hsurj hcov hJ1 hJ2 hF h)
  · exact List.mem_append_right _ (joinCtxCircP_sub e p hne hsurj hcov hJ1 hJ2 hJ5 h)

/-- **B1 for the promise `⋈^∨`, `⋈^◯`** (`FRJWr.joinOrP`, `FRJWr.joinCircP`),
the context half. -/
theorem joinCtxOrP_sub {k : Nat} {Δs : Fin (k + 1) → List Form}
    (hJ5 : ∀ Y, Form.circ Y ∈ unionAll (fun j => circPart (Ξs j)) → ∃ i, Clo (Δs i) Y) :
    joinCtxOrP Ξs Θs rhs Δs ⊆
      joinCtxOrP (fun k => Ξs (e k)) (fun k => Θs (e k)) (fun k => rhs (e k)) Δs := by
  refine filter_mono _ (fun x hx => ?_)
  rcases List.mem_append.mp hx with h | h
  · exact List.mem_append_left _ (joinCtxOr_sub e p hne hsurj hcov hJ1 hJ2 h)
  · exact List.mem_append_right _ (joinCtxCircP_sub e p hne hsurj hcov hJ1 hJ2 hJ5 h)

end B1Rest

/-- The promise-side conditions on the irregular family transfer. -/
theorem j5_comp {n m k : Nat} {Ξs : Fin (n + 1) → List Form} {Δs : Fin (k + 1) → List Form}
    (e : Fin (m + 1) → Fin (n + 1))
    (hJ5 : ∀ Y, Form.circ Y ∈ unionAll (fun j => circPart (Ξs j)) → ∃ i, Clo (Δs i) Y) :
    ∀ Y, Form.circ Y ∈ unionAll (fun k => circPart (Ξs (e k))) → ∃ i, Clo (Δs i) Y :=
  fun Y h => hJ5 Y (unionAll_comp_sub e _ h)

theorem j6_comp {n m k : Nat} {Ξs : Fin (n + 1) → List Form} {Δs : Fin (k + 1) → List Form}
    (e : Fin (m + 1) → Fin (n + 1))
    (hJ6 : ∀ i j, ∀ X ∈ Ξs j, Clo (Δs i) X) :
    ∀ i j, ∀ X ∈ Ξs (e j), Clo (Δs i) X :=
  fun i j X hX => hJ6 i (e j) X hX

/-! ## 8. B2′: cutting the promise family

`e : Fin (m+1) → Fin (k+1)` selects promise worlds.  It must hit every
modal formula the full family witnesses, among those of `⋃Ξ^◯` and
`⋂Θ^◯`; nothing else is asked of it. -/

section B2

variable {n k m : Nat} {Ξs Θs : Fin (n + 1) → List Form} {rhs : Fin (n + 1) → Form}
  {tps : Fin (k + 1) → Tag} {Δs : Fin (k + 1) → List Form} {Ds : Fin (k + 1) → Form}
  (e : Fin (m + 1) → Fin (k + 1))
  (hhit : ∀ Y, Form.circ Y ∈ unionAll (fun j => circPart (Ξs j)) ++
      interAll (fun j => circPart (Θs j)) →
    (∃ i, Clo (Δs i) Y) → ∃ i', Clo (Δs (e i')) Y)

include hhit

omit hhit in
theorem restrictP_cut {X : List Form} :
    restrictP X Δs ⊆ restrictP X (fun i' => Δs (e i')) := by
  intro x hx
  rw [mem_restrictP] at hx ⊢
  exact ⟨hx.1, fun i' => hx.2 (e i')⟩

theorem joinCtxCircP_cut :
    joinCtxCircP Ξs Θs Δs ⊆ joinCtxCircP Ξs Θs (fun i' => Δs (e i')) := by
  intro x hx
  simp only [joinCtxCircP, List.mem_append] at hx
  simp only [joinCtxCircP, List.mem_append]
  rcases hx with hu | hr
  · exact Or.inl hu
  · have h := List.mem_filter.mp hr
    have hisCirc : x.isCirc = true := (List.mem_filter.mp (mem_interAll.mp h.1 0)).2
    obtain ⟨Y, rfl⟩ := isCirc_shape hisCirc
    have hw := (mem_restrictC.mp hr).2
    exact Or.inr (mem_restrictC.mpr
      ⟨h.1, hhit Y (List.mem_append_right _ h.1) hw⟩)

/-- **B2′ for the promise `⋈^At`, the context half.** -/
theorem joinCtxAtP_cut {F : Form} :
    joinCtxAtP Ξs Θs rhs F Δs ⊆ joinCtxAtP Ξs Θs rhs F (fun i' => Δs (e i')) := by
  intro x hx
  refine restrictP_cut e (X := _) ?_
  have h := List.mem_filter.mp hx
  refine List.mem_filter.mpr ⟨?_, h.2⟩
  rcases List.mem_append.mp h.1 with h1 | h1
  · exact List.mem_append_left _ h1
  · exact List.mem_append_right _ (joinCtxCircP_cut e hhit h1)

/-- **B2′ for the promise `⋈^∨`, `⋈^◯`, the context half.** -/
theorem joinCtxOrP_cut :
    joinCtxOrP Ξs Θs rhs Δs ⊆ joinCtxOrP Ξs Θs rhs (fun i' => Δs (e i')) := by
  intro x hx
  refine restrictP_cut e (X := _) ?_
  have h := List.mem_filter.mp hx
  refine List.mem_filter.mpr ⟨?_, h.2⟩
  rcases List.mem_append.mp h.1 with h1 | h1
  · exact List.mem_append_left _ h1
  · exact List.mem_append_right _ (joinCtxCircP_cut e hhit h1)

/-- The promise-side conditions transfer to the cut family. -/
theorem j5_cut (hJ5 : ∀ Y, Form.circ Y ∈ unionAll (fun j => circPart (Ξs j)) →
      ∃ i, Clo (Δs i) Y) :
    ∀ Y, Form.circ Y ∈ unionAll (fun j => circPart (Ξs j)) → ∃ i', Clo (Δs (e i')) Y :=
  fun Y hY => hhit Y (List.mem_append_left _ hY) (hJ5 Y hY)

omit hhit in
theorem j6_cut (hJ6 : ∀ i j, ∀ X ∈ Ξs j, Clo (Δs i) X) :
    ∀ i' j, ∀ X ∈ Ξs j, Clo (Δs (e i')) X :=
  fun i' j X hX => hJ6 (e i') j X hX

omit hhit in
theorem j7_cut
    (hJ7 : ∀ i, Ds i = Ds 0 ∧
      (tps i = .barren ∨ ∃ W, tps i = .chain W ∧ Covers (Δs i) W (Ds 0))) :
    (∀ i', Ds (e i') = Ds (e 0) ∧
      (tps (e i') = .barren ∨ ∃ W, tps (e i') = .chain W ∧ Covers (Δs (e i')) W (Ds (e 0)))) ∧
    Ds (e 0) = Ds 0 := by
  refine ⟨fun i' => ⟨(hJ7 (e i')).1.trans (hJ7 (e 0)).1.symm, ?_⟩, (hJ7 (e 0)).1⟩
  rw [(hJ7 (e 0)).1]
  exact (hJ7 (e i')).2

end B2

/-! ## 9. The subsumption forms

`WSubsumes` (`FRJ/Gbu/W/Dichotomy.lean`): same goal, `tagLeB`, context
inclusion.  Barren and blocked tags compare to themselves; a chain tag
compares to a chain tag with the same pledge. -/

theorem tagLeB_refl' : ∀ t : Tag, FRJ.Search.tagLeB t t = true
  | .barren => rfl
  | .blocked => rfl
  | .chain D => by simp [FRJ.Search.tagLeB]

/-- **B1, subsumption form, barren `⋈^At`**: the conclusion of a family
with a duplicated goal is subsumed by the conclusion of the family
without the duplicate. -/
theorem b1_joinAt_subsumes {n : Nat} {Ξs Θs : Fin (n + 2) → List Form}
    {rhs : Fin (n + 2) → Form} {F : Form}
    (p i : Fin (n + 2)) (hip : i ≠ p) (hgoal : rhs i = rhs p)
    (hJ1 : ∀ i j, i ≠ j → Ξs i ⊆ Ξs j ++ Θs j)
    (hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (Ξs j)) →
      A ∈ upsilon rhs)
    (hF : F ∉ unionAll (fun j => atPart (Ξs j))) :
    Gbu.W.WSubsumes (.reg .barren (ctxAt Ξs Θs rhs F) F)
      (.reg .barren (ctxAt (fun k => Ξs (p.succAbove k)) (fun k => Θs (p.succAbove k))
        (fun k => rhs (p.succAbove k)) F) F) :=
  ⟨rfl, rfl, ctxAt_sub (Fin.succAbove p) p (succAbove_ne' p) (succAbove_surj p)
    (cov_of_dup (rhs := rhs) p i hip hgoal) hJ1 hJ2 hF⟩

/-- **B1, subsumption form, promise `⋈^At`.** -/
theorem b1_joinAtP_subsumes {n k : Nat} {Ξs Θs : Fin (n + 2) → List Form}
    {rhs : Fin (n + 2) → Form} {F : Form} {Δs : Fin (k + 1) → List Form} {D : Form}
    (p i : Fin (n + 2)) (hip : i ≠ p) (hgoal : rhs i = rhs p)
    (hJ1 : ∀ i j, i ≠ j → Ξs i ⊆ Ξs j ++ Θs j)
    (hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (Ξs j)) →
      A ∈ upsilon rhs)
    (hF : F ∉ unionAll (fun j => atPart (Ξs j)))
    (hJ5 : ∀ Y, Form.circ Y ∈ unionAll (fun j => circPart (Ξs j)) → ∃ i, Clo (Δs i) Y) :
    Gbu.W.WSubsumes (.reg (.chain D) (joinCtxAtP Ξs Θs rhs F Δs) F)
      (.reg (.chain D) (joinCtxAtP (fun k => Ξs (p.succAbove k)) (fun k => Θs (p.succAbove k))
        (fun k => rhs (p.succAbove k)) F Δs) F) :=
  ⟨rfl, tagLeB_refl' _, joinCtxAtP_sub (Fin.succAbove p) p (succAbove_ne' p)
    (succAbove_surj p) (cov_of_dup (rhs := rhs) p i hip hgoal) hJ1 hJ2 hF hJ5⟩

/-- **B2′, subsumption form, promise `⋈^At`**: cutting the promise family
to a witness-hitting sub-family subsumes. -/
theorem b2_joinAtP_subsumes {n k m : Nat} {Ξs Θs : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form} {F : Form} {Δs : Fin (k + 1) → List Form} {D : Form}
    (e : Fin (m + 1) → Fin (k + 1))
    (hhit : ∀ Y, Form.circ Y ∈ unionAll (fun j => circPart (Ξs j)) ++
        interAll (fun j => circPart (Θs j)) →
      (∃ i, Clo (Δs i) Y) → ∃ i', Clo (Δs (e i')) Y) :
    Gbu.W.WSubsumes (.reg (.chain D) (joinCtxAtP Ξs Θs rhs F Δs) F)
      (.reg (.chain D) (joinCtxAtP Ξs Θs rhs F (fun i' => Δs (e i'))) F) :=
  ⟨rfl, tagLeB_refl' _, joinCtxAtP_cut e hhit⟩

/-! ## Pins -/

/-- info: 'FRJ.Arity.b1_joinAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms b1_joinAt

/-- info: 'FRJ.Arity.b1_joinAt_subsumes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms b1_joinAt_subsumes

/-- info: 'FRJ.Arity.ctxOr_sub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ctxOr_sub

/-- info: 'FRJ.Arity.joinCtxAtF_sub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms joinCtxAtF_sub

/-- info: 'FRJ.Arity.joinCtxOrF_sub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms joinCtxOrF_sub

/-- info: 'FRJ.Arity.b1_joinAtP_subsumes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms b1_joinAtP_subsumes

/-- info: 'FRJ.Arity.joinCtxOrP_sub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms joinCtxOrP_sub

/-- info: 'FRJ.Arity.b2_joinAtP_subsumes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms b2_joinAtP_subsumes

/-- info: 'FRJ.Arity.joinCtxOrP_cut' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms joinCtxOrP_cut

/-- info: 'FRJ.Arity.j7_cut' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms j7_cut

end FRJ.Arity
