/-
# The closed database exists — `∀ G, DBClosed G (closureDB G)`

The last object of the `decideGbuW` chain (wip/gbu_frjw_closure.lean):
for every PLL formula `G`, a derivation-carrying row list closed under
the FRJW rules over its own stored sequents.  The construction is a
saturation:

  * rows are stored as produced (former-shaped contexts) but KEYED by
    their canonical sequent (`canonSeq`: zones filtered through the
    deduplicated `Ĝ` pool), so presence-checking is list equality and
    the store's canonical images stay `Nodup`;
  * `stepAll` fires every rule at every stored premise combination —
    families range over sublists of the stored irregular/regular
    triples, parameters over the finite `Sf^R`/`Ĝ`-derived candidate
    lists — guarded by the clauses' own decidable hypotheses, so each
    emitted row carries its derivation by the corresponding
    constructor;
  * termination is a pigeonhole: every genuine insertion adds a fresh
    canonical sequent, all of them wellformed (`wfR`/`wfI`,
    `goalWr`/`goalWi`, `tagWr`), and the wellformed canonical universe
    `univList G` is finite — so `univList.length + 1` rounds reach a
    fixpoint;
  * closedness at the fixpoint: an arbitrary clause instance reindexes
    to the stored-sublist family with the same row set (the aggregates
    `⋃`/`⋂`/`Υ`/`keptOf` are membership-determined), the emitter fires
    on it, and the fixpoint says its canonical sequent is stored.

Everything is choice-free; the target pins are `[propext, Quot.sound]`.
-/
import wip.gbu_frjw_closure
import FRJ.StepW

namespace FRJ.Gbu.W

open FRJ Form FRJ.Search

deriving instance DecidableEq for WSeq

instance decClo (Γ : List Form) (X : Form) : Decidable (Clo Γ X) :=
  decidable_of_iff _ cloB_iff

/-! ## S1: canonicalisation and the finite universe -/

/-- The canonical representative of a context inside a fixed pool: the
pool filtered by membership.  For `Γ ⊆ pool` it is `≐ Γ`, and it is a
sublist of the pool by construction. -/
def canonCtx (pool Γ : List Form) : List Form :=
  pool.filter (fun x => decide (x ∈ Γ))

theorem mem_canonCtx {pool Γ : List Form} {x : Form} :
    x ∈ canonCtx pool Γ ↔ x ∈ pool ∧ x ∈ Γ := by
  simp [canonCtx, List.mem_filter]

theorem canonCtx_ctxEq {pool Γ : List Form} (h : Γ ⊆ pool) :
    canonCtx pool Γ ≐ Γ :=
  fun _ => ⟨fun hx => (mem_canonCtx.mp hx).2,
    fun hx => mem_canonCtx.mpr ⟨h hx, hx⟩⟩

theorem canonCtx_sublist {pool Γ : List Form} :
    List.Sublist (canonCtx pool Γ) pool :=
  List.filter_sublist

/-- Canonical contexts of member-equal contexts are EQUAL lists. -/
theorem canonCtx_congr {pool Γ Γ' : List Form} (h : Γ ≐ Γ') :
    canonCtx pool Γ = canonCtx pool Γ' := by
  simp only [canonCtx]
  exact List.filter_congr (fun x _ => by
    simp only [decide_eq_decide]
    exact h x)

/-- The deduplicated `Ĝ` pool. -/
def gPool (G : Form) : List Form := (gHat G).dedup

theorem mem_gPool {G : Form} {x : Form} : x ∈ gPool G ↔ x ∈ gHat G := by
  simp [gPool, List.mem_dedup]

/-- The deduplicated right-subformula list. -/
def goalPool (G : Form) : List Form := (sfR G).dedup

theorem mem_goalPool {G : Form} {x : Form} : x ∈ goalPool G ↔ x ∈ sfR G := by
  simp [goalPool, List.mem_dedup]

/-- The canonical form of a sequent: zones filtered through the pool;
tag and goal untouched. -/
def canonSeq (G : Form) : WSeq → WSeq
  | .reg t Γ C => .reg t (canonCtx (gPool G) Γ) C
  | .irr St Th C => .irr (canonCtx (gPool G) St) (canonCtx (gPool G) Th) C

/-- The finite wellformed canonical universe. -/
def univList (G : Form) : List WSeq :=
  (Tag.barren :: Tag.blocked :: (goalPool G).map Tag.chain).flatMap
      (fun t => (gPool G).sublists.flatMap
        (fun Γ => (goalPool G).map (fun C => WSeq.reg t Γ C))) ++
    (gPool G).sublists.flatMap
      (fun St => (gPool G).sublists.flatMap
        (fun Th => (goalPool G).map (fun C => WSeq.irr St Th C)))

/-- Wellformedness of a sequent, as the universe needs it. -/
def WfSeq (G : Form) : WSeq → Prop
  | .reg t Γ C => Γ ⊆ gHat G ∧ C ∈ sfR G ∧
      (t = .barren ∨ t = .blocked ∨ ∃ W, t = .chain W ∧ W ∈ sfR G)
  | .irr St Th C => St ⊆ gHat G ∧ Th ⊆ gHat G ∧ C ∈ sfR G

/-- Every stored row is wellformed — from its own derivation. -/
theorem wfSeq_of_wDer {G : Form} : ∀ {s : WSeq}, WDer G s → WfSeq G s
  | .reg _ _ _, d => ⟨_root_.FRJ.W.wfR d, goalWr d, tagWr d⟩
  | .irr _ _ _, d =>
      ⟨fun _ hx => _root_.FRJ.W.wfI d (List.mem_append_left _ hx),
       fun _ hx => _root_.FRJ.W.wfI d (List.mem_append_right _ hx),
       goalWi d⟩

theorem canonSeq_mem_univ {G : Form} {s : WSeq} (h : WfSeq G s) :
    canonSeq G s ∈ univList G := by
  cases s with
  | reg t Γ C =>
      obtain ⟨hΓ, hC, ht⟩ := h
      simp only [univList, canonSeq, List.mem_append, List.mem_flatMap,
        List.mem_map, List.mem_cons, List.mem_sublists]
      refine Or.inl ⟨t, ?_, canonCtx (gPool G) Γ, canonCtx_sublist,
        C, mem_goalPool.mpr hC, rfl⟩
      rcases ht with rfl | rfl | ⟨W, rfl, hW⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr ⟨W, mem_goalPool.mpr hW, rfl⟩)
  | irr St Th C =>
      obtain ⟨hSt, hTh, hC⟩ := h
      simp only [univList, canonSeq, List.mem_append, List.mem_flatMap,
        List.mem_map, List.mem_sublists]
      exact Or.inr ⟨canonCtx (gPool G) St, canonCtx_sublist,
        canonCtx (gPool G) Th, canonCtx_sublist,
        C, mem_goalPool.mpr hC, rfl⟩

/-- Equal canonical sequents of wellformed rows subsume each other; this
is what turns fixpoint presence into the clause's `∃`-subsumer. -/
theorem subsumes_of_canonSeq_eq {G : Form} {s e : WSeq}
    (hs : WfSeq G s) (he : WfSeq G e)
    (h : canonSeq G s = canonSeq G e) : WSubsumes s e := by
  cases s with
  | reg t Γ C =>
      cases e with
      | reg t' Γ' C' =>
          simp only [canonSeq, WSeq.reg.injEq] at h
          obtain ⟨rfl, hctx, rfl⟩ := h
          refine ⟨rfl, tagLeB_refl _, ?_⟩
          intro x hx
          have h1 : x ∈ canonCtx (gPool G) Γ :=
            mem_canonCtx.mpr ⟨mem_gPool.mpr (hs.1 hx), hx⟩
          rw [hctx] at h1
          exact (mem_canonCtx.mp h1).2
      | irr _ _ _ => exact absurd h (by simp [canonSeq])
  | irr St Th C =>
      cases e with
      | reg _ _ _ => exact absurd h (by simp [canonSeq])
      | irr St' Th' C' =>
          simp only [canonSeq, WSeq.irr.injEq] at h
          obtain ⟨hst, hth, rfl⟩ := h
          refine ⟨rfl, ?_, ?_⟩
          · intro x
            constructor
            · intro hx
              have h1 : x ∈ canonCtx (gPool G) St :=
                mem_canonCtx.mpr ⟨mem_gPool.mpr (hs.1 hx), hx⟩
              rw [hst] at h1
              exact (mem_canonCtx.mp h1).2
            · intro hx
              have h1 : x ∈ canonCtx (gPool G) St' :=
                mem_canonCtx.mpr ⟨mem_gPool.mpr (he.1 hx), hx⟩
              rw [← hst] at h1
              exact (mem_canonCtx.mp h1).2
          · intro x hx
            have h1 : x ∈ canonCtx (gPool G) Th :=
              mem_canonCtx.mpr ⟨mem_gPool.mpr (hs.2.1 hx), hx⟩
            rw [hth] at h1
            exact (mem_canonCtx.mp h1).2

/-! ## S2: the reindexing pack

A join clause quantifies over families of arbitrary arity; the emitter
fires only at sublists of the store.  Every aggregate a join consumes
(`⋃`, `⋂`, `Υ`, `thPool`, the formers, `keptOf`) is determined by the
family's row SET, so a two-sided image inclusion transfers everything.
The relation is stated with the g-side components equal to f-side
components, both directions. -/

theorem mem_upsilon {n : Nat} {rhs : Fin (n + 1) → Form} {x : Form} :
    x ∈ upsilon rhs ↔ ∃ j, rhs j = x := by
  simp [upsilon, List.mem_map, List.mem_finRange]

/-- Two irregular families listing the same row set. -/
def SameIrr {n m : Nat} (stab th : Fin (n + 1) → List Form)
    (rhs : Fin (n + 1) → Form) (stab' th' : Fin (m + 1) → List Form)
    (rhs' : Fin (m + 1) → Form) : Prop :=
  (∀ j, ∃ i, stab' i = stab j ∧ th' i = th j ∧ rhs' i = rhs j) ∧
  (∀ i, ∃ j, stab' i = stab j ∧ th' i = th j ∧ rhs' i = rhs j)

/-- Two regular (promise) families listing the same row set. -/
def SameReg {k m : Nat} (tps : Fin (k + 1) → Tag)
    (Δs : Fin (k + 1) → List Form) (Ds : Fin (k + 1) → Form)
    (tps' : Fin (m + 1) → Tag) (Δs' : Fin (m + 1) → List Form)
    (Ds' : Fin (m + 1) → Form) : Prop :=
  (∀ j, ∃ i, tps' i = tps j ∧ Δs' i = Δs j ∧ Ds' i = Ds j) ∧
  (∀ i, ∃ j, tps' i = tps j ∧ Δs' i = Δs j ∧ Ds' i = Ds j)

section Reindex

variable {n m : Nat} {stab th : Fin (n + 1) → List Form}
  {rhs : Fin (n + 1) → Form} {stab' th' : Fin (m + 1) → List Form}
  {rhs' : Fin (m + 1) → Form}

theorem SameIrr.unionAll_filter (h : SameIrr stab th rhs stab' th' rhs')
    (P : Form → Bool) :
    (unionAll fun j => (stab j).filter P) ≐
      (unionAll fun i => (stab' i).filter P) := by
  intro x
  simp only [mem_unionAll]
  constructor
  · rintro ⟨j, hj⟩
    obtain ⟨i, hi, -, -⟩ := h.1 j
    exact ⟨i, hi ▸ hj⟩
  · rintro ⟨i, hi⟩
    obtain ⟨j, hj, -, -⟩ := h.2 i
    exact ⟨j, hj ▸ hi⟩

theorem SameIrr.interAll_filter (h : SameIrr stab th rhs stab' th' rhs')
    (P : Form → Bool) :
    (interAll fun j => (th j).filter P) ≐
      (interAll fun i => (th' i).filter P) := by
  intro x
  simp only [mem_interAll]
  constructor
  · intro hall i
    obtain ⟨j, -, hj, -⟩ := h.2 i
    exact hj ▸ hall j
  · intro hall j
    obtain ⟨i, -, hi, -⟩ := h.1 j
    exact hi ▸ hall i

theorem SameIrr.interAll_th (h : SameIrr stab th rhs stab' th' rhs') :
    interAll th ≐ interAll th' := by
  intro x
  simp only [mem_interAll]
  constructor
  · intro hall i
    obtain ⟨j, -, hj, -⟩ := h.2 i
    exact hj ▸ hall j
  · intro hall j
    obtain ⟨i, -, hi, -⟩ := h.1 j
    exact hi ▸ hall i

theorem SameIrr.upsilon_eq (h : SameIrr stab th rhs stab' th' rhs') :
    upsilon rhs ≐ upsilon rhs' := by
  intro x
  simp only [mem_upsilon]
  constructor
  · rintro ⟨j, hj⟩
    obtain ⟨i, -, -, hi⟩ := h.1 j
    exact ⟨i, hi.trans hj⟩
  · rintro ⟨i, hi⟩
    obtain ⟨j, -, -, hj⟩ := h.2 i
    exact ⟨j, hj.symm.trans hi⟩

theorem SameIrr.thPool_eq (h : SameIrr stab th rhs stab' th' rhs') :
    thPool th ≐ thPool th' := by
  intro x
  simp only [thPool, mem_impPart]
  exact and_congr_left' (h.interAll_th x)

theorem SameIrr.orVBase (h : SameIrr stab th rhs stab' th' rhs') :
    joinCtxOrVBase stab th ≐ joinCtxOrVBase stab' th' := by
  intro x
  simp only [joinCtxOrVBase, List.mem_append]
  exact or_congr (or_congr (h.unionAll_filter _ x) (h.interAll_filter _ x))
    (h.unionAll_filter _ x)

theorem SameIrr.atVBase (h : SameIrr stab th rhs stab' th' rhs')
    {F : Form} :
    joinCtxAtVBase stab th F ≐ joinCtxAtVBase stab' th' F := by
  intro x
  simp only [joinCtxAtVBase, List.mem_append, mem_rm]
  exact or_congr (or_congr (h.unionAll_filter _ x)
    (and_congr_right' (h.interAll_filter _ x))) (h.unionAll_filter _ x)

/-- The kept-chain context transfers: base and pool are `≐`, `Υ` is
`≐`, so every link of the f-side `keptOf` lands in the g-side one. -/
theorem SameIrr.orCtx_sub (h : SameIrr stab th rhs stab' th' rhs') :
    joinCtxOrVBase stab th ++
      keptOf (upsilon rhs) (joinCtxOrVBase stab th) (thPool th) ⊆
    joinCtxOrVBase stab' th' ++
      keptOf (upsilon rhs') (joinCtxOrVBase stab' th') (thPool th') := by
  intro x hx
  rcases List.mem_append.mp hx with h1 | h1
  · exact List.mem_append_left _ ((h.orVBase x).mp h1)
  · exact List.mem_append_right _
      (keptChain_sub_keptOf_of_le h.upsilon_eq.subset h.orVBase.subset
        h.thPool_eq.subset (keptOf_ok _ _ _) x h1)

theorem SameIrr.atCtx_sub (h : SameIrr stab th rhs stab' th' rhs')
    {F : Form} :
    joinCtxAtVBase stab th F ++
      keptOf (upsilon rhs) (joinCtxAtVBase stab th F) (thPool th) ⊆
    joinCtxAtVBase stab' th' F ++
      keptOf (upsilon rhs') (joinCtxAtVBase stab' th' F) (thPool th') := by
  intro x hx
  rcases List.mem_append.mp hx with h1 | h1
  · exact List.mem_append_left _ ((h.atVBase x).mp h1)
  · exact List.mem_append_right _
      (keptChain_sub_keptOf_of_le h.upsilon_eq.subset h.atVBase.subset
        h.thPool_eq.subset (keptOf_ok _ _ _) x h1)

/-! Condition transfers, f-side to g-side.  `hnd` says the g-family has
pairwise-distinct rows (it is enumerated from a `Nodup` sublist). -/

theorem SameIrr.hJ1 (h : SameIrr stab th rhs stab' th' rhs')
    (hnd : ∀ i₁ i₂ : Fin (m + 1), i₁ ≠ i₂ →
      ¬ (stab' i₁ = stab' i₂ ∧ th' i₁ = th' i₂ ∧ rhs' i₁ = rhs' i₂))
    (hJ1 : ∀ i j, i ≠ j → stab i ⊆ stab j ++ th j) :
    ∀ i j, i ≠ j → stab' i ⊆ stab' j ++ th' j := by
  intro i₁ i₂ hne
  obtain ⟨j₁, hs₁, ht₁, hr₁⟩ := h.2 i₁
  obtain ⟨j₂, hs₂, ht₂, hr₂⟩ := h.2 i₂
  have hjne : j₁ ≠ j₂ := by
    rintro rfl
    exact hnd i₁ i₂ hne
      ⟨hs₁.trans hs₂.symm, ht₁.trans ht₂.symm, hr₁.trans hr₂.symm⟩
  rw [hs₁, hs₂, ht₂]
  exact hJ1 j₁ j₂ hjne

theorem SameIrr.hJ2_strict (h : SameIrr stab th rhs stab' th' rhs')
    (hJ2 : ∀ A B : Form,
      Form.imp A B ∈ unionAll (fun j => impPart (stab j)) →
      A ∈ upsilon rhs) :
    ∀ A B : Form, Form.imp A B ∈ unionAll (fun i => impPart (stab' i)) →
      A ∈ upsilon rhs' :=
  fun A B hAB => (h.upsilon_eq _).mp
    (hJ2 A B ((h.unionAll_filter _ _).mpr hAB))

theorem SameIrr.hcirc (h : SameIrr stab th rhs stab' th' rhs')
    (hcirc : unionAll (fun j => circPart (stab j)) = []) :
    unionAll (fun i => circPart (stab' i)) = [] := by
  cases hcase : unionAll (fun i => circPart (stab' i)) with
  | nil => rfl
  | cons y ys =>
      exfalso
      have hy : y ∈ unionAll (fun i => circPart (stab' i)) :=
        hcase ▸ List.mem_cons_self
      have : y ∈ unionAll (fun j => circPart (stab j)) :=
        (h.unionAll_filter _ y).mpr hy
      rw [hcirc] at this
      exact absurd this List.not_mem_nil

theorem SameIrr.hFnot (h : SameIrr stab th rhs stab' th' rhs') {F : Form}
    (hFnot : F ∉ unionAll (fun j => atPart (stab j))) :
    F ∉ unionAll (fun i => atPart (stab' i)) :=
  fun hmem => hFnot ((h.unionAll_filter _ F).mpr hmem)

/-! Full-context congruences (fallible and promise joins). -/

theorem inRestrict_congr {Υ Υ' : List Form} (hu : Υ ≐ Υ') :
    ∀ x, inRestrict Υ x = true ↔ inRestrict Υ' x = true := by
  intro x
  cases x with
  | imp A B => simp only [inRestrict, decide_eq_true_eq]; exact hu A
  | atom p => simp [inRestrict]
  | bot => simp [inRestrict]
  | and _ _ => simp [inRestrict]
  | or _ _ => simp [inRestrict]
  | circ _ => simp [inRestrict]

theorem restrict_ctxEq {X X' Υ Υ' : List Form} (hX : X ≐ X')
    (hu : Υ ≐ Υ') : restrict X Υ ≐ restrict X' Υ' := by
  intro x
  simp only [restrict, List.mem_filter]
  exact and_congr (hX x) (inRestrict_congr hu x)

theorem SameIrr.ctxAt (h : SameIrr stab th rhs stab' th' rhs') {F : Form} :
    joinCtxAt stab th rhs F ≐ joinCtxAt stab' th' rhs' F := by
  intro x
  simp only [joinCtxAt, List.mem_append, mem_rm]
  exact or_congr (or_congr (or_congr (h.unionAll_filter _ x)
      (and_congr_right' (h.interAll_filter _ x)))
    (h.unionAll_filter _ x))
    (restrict_ctxEq (h.interAll_filter _) h.upsilon_eq x)

theorem SameIrr.ctxOr (h : SameIrr stab th rhs stab' th' rhs') :
    joinCtxOr stab th rhs ≐ joinCtxOr stab' th' rhs' := by
  intro x
  simp only [joinCtxOr, List.mem_append]
  exact or_congr (or_congr (or_congr (h.unionAll_filter _ x)
      (h.interAll_filter _ x))
    (h.unionAll_filter _ x))
    (restrict_ctxEq (h.interAll_filter _) h.upsilon_eq x)

theorem SameIrr.ctxCircF (h : SameIrr stab th rhs stab' th' rhs') :
    joinCtxCircF stab th ≐ joinCtxCircF stab' th' := by
  intro x
  simp only [joinCtxCircF, List.mem_append]
  exact or_congr (h.unionAll_filter _ x) (h.interAll_filter _ x)

theorem SameIrr.ctxAtF (h : SameIrr stab th rhs stab' th' rhs') {F : Form} :
    joinCtxAtF stab th rhs F ≐ joinCtxAtF stab' th' rhs' F := by
  intro x
  simp only [joinCtxAtF, List.mem_append]
  exact or_congr (h.ctxAt x) (h.ctxCircF x)

theorem SameIrr.ctxOrF (h : SameIrr stab th rhs stab' th' rhs') :
    joinCtxOrF stab th rhs ≐ joinCtxOrF stab' th' rhs' := by
  intro x
  simp only [joinCtxOrF, List.mem_append]
  exact or_congr (h.ctxOr x) (h.ctxCircF x)

section RegReindex

variable {k m' : Nat} {tps : Fin (k + 1) → Tag}
  {Δs : Fin (k + 1) → List Form} {Ds : Fin (k + 1) → Form}
  {tps' : Fin (m' + 1) → Tag} {Δs' : Fin (m' + 1) → List Form}
  {Ds' : Fin (m' + 1) → Form}

theorem inRestrictC_congr (h' : SameReg tps Δs Ds tps' Δs' Ds') :
    ∀ x, inRestrictC Δs x = true ↔ inRestrictC Δs' x = true := by
  intro x
  cases x with
  | circ Y =>
      simp only [inRestrictC, List.any_eq_true]
      constructor
      · rintro ⟨j, -, hb⟩
        obtain ⟨i, -, hi, -⟩ := h'.1 j
        exact ⟨i, List.mem_finRange i, hi ▸ hb⟩
      · rintro ⟨i, -, hb⟩
        obtain ⟨j, -, hj, -⟩ := h'.2 i
        exact ⟨j, List.mem_finRange j, hj ▸ hb⟩
  | atom p => simp [inRestrictC]
  | bot => simp [inRestrictC]
  | and _ _ => simp [inRestrictC]
  | or _ _ => simp [inRestrictC]
  | imp _ _ => simp [inRestrictC]

theorem cloAllB_congr (h' : SameReg tps Δs Ds tps' Δs' Ds') :
    ∀ x, cloAllB Δs x = true ↔ cloAllB Δs' x = true := by
  intro x
  simp only [cloAllB, List.all_eq_true]
  constructor
  · intro hall i _
    obtain ⟨j, -, hj, -⟩ := h'.2 i
    exact hj ▸ hall j (List.mem_finRange j)
  · intro hall j _
    obtain ⟨i, -, hi, -⟩ := h'.1 j
    exact hi ▸ hall i (List.mem_finRange i)

theorem ctxCircP_eq (h : SameIrr stab th rhs stab' th' rhs')
    (h' : SameReg tps Δs Ds tps' Δs' Ds') :
    joinCtxCircP stab th Δs ≐ joinCtxCircP stab' th' Δs' := by
  intro x
  simp only [joinCtxCircP, restrictC, List.mem_append, List.mem_filter]
  exact or_congr (h.unionAll_filter _ x)
    (and_congr (h.interAll_filter _ x) (inRestrictC_congr h' x))

theorem ctxAtP_eq (h : SameIrr stab th rhs stab' th' rhs')
    (h' : SameReg tps Δs Ds tps' Δs' Ds') {F : Form} :
    joinCtxAtP stab th rhs F Δs ≐ joinCtxAtP stab' th' rhs' F Δs' := by
  intro x
  simp only [joinCtxAtP, restrictP, List.mem_filter, List.mem_append]
  exact and_congr (or_congr (h.ctxAt x) (ctxCircP_eq h h' x))
    (cloAllB_congr h' x)

theorem ctxOrP_eq (h : SameIrr stab th rhs stab' th' rhs')
    (h' : SameReg tps Δs Ds tps' Δs' Ds') :
    joinCtxOrP stab th rhs Δs ≐ joinCtxOrP stab' th' rhs' Δs' := by
  intro x
  simp only [joinCtxOrP, restrictP, List.mem_filter, List.mem_append]
  exact and_congr (or_congr (h.ctxOr x) (ctxCircP_eq h h' x))
    (cloAllB_congr h' x)

theorem hJ5_re (h : SameIrr stab th rhs stab' th' rhs')
    (h' : SameReg tps Δs Ds tps' Δs' Ds')
    (hJ5 : ∀ Y : Form,
      Form.circ Y ∈ unionAll (fun j => circPart (stab j)) →
      ∃ i, Clo (Δs i) Y) :
    ∀ Y : Form, Form.circ Y ∈ unionAll (fun i => circPart (stab' i)) →
      ∃ i, Clo (Δs' i) Y := by
  intro Y hY
  obtain ⟨j, hj⟩ := hJ5 Y ((h.unionAll_filter _ _).mpr hY)
  obtain ⟨i, -, hi, -⟩ := h'.1 j
  exact ⟨i, hi ▸ hj⟩

theorem hJ7s_re (h : SameIrr stab th rhs stab' th' rhs')
    (h' : SameReg tps Δs Ds tps' Δs' Ds')
    (hJ7s : ∀ i j, ∀ X ∈ stab j, Clo (Δs i) X) :
    ∀ i j, ∀ X ∈ stab' j, Clo (Δs' i) X := by
  intro i j X hX
  obtain ⟨jΔ, -, hiΔ, -⟩ := h'.2 i
  obtain ⟨jf, hjf, -, -⟩ := h.2 j
  rw [hiΔ]
  exact hJ7s jΔ jf X (hjf ▸ hX)

theorem htagP_re (h' : SameReg tps Δs Ds tps' Δs' Ds') {t' : Tag}
    (htag : t' = .blocked ∨ (t' = .chain (Ds 0) ∧ ∀ i, Ds i = Ds 0 ∧
      (tps i = .barren ∨ ∃ W, tps i = .chain W ∧ Covers (Δs i) W (Ds 0)))) :
    t' = .blocked ∨ (t' = .chain (Ds' 0) ∧ ∀ i, Ds' i = Ds' 0 ∧
      (tps' i = .barren ∨ ∃ W, tps' i = .chain W ∧
        Covers (Δs' i) W (Ds' 0))) := by
  rcases htag with h0 | ⟨h0, hall⟩
  · exact Or.inl h0
  · obtain ⟨j₀, -, -, hD₀⟩ := h'.2 0
    have hD₀' : Ds' 0 = Ds 0 := hD₀.trans (hall j₀).1
    refine Or.inr ⟨hD₀' ▸ h0, fun i => ?_⟩
    obtain ⟨j, ht, hΔ, hD⟩ := h'.2 i
    refine ⟨(hD.trans (hall j).1).trans hD₀'.symm, ?_⟩
    rcases (hall j).2 with hb | ⟨W, hW, hc⟩
    · exact Or.inl (ht ▸ hb)
    · exact Or.inr ⟨W, ht ▸ hW, hD₀' ▸ hΔ ▸ hc⟩

theorem hDsZ_re (h' : SameReg tps Δs Ds tps' Δs' Ds') {Z : Form}
    (hDs : ∀ i, Ds i = Z ∧
      (tps i = .barren ∨ ∃ W, tps i = .chain W ∧ Covers (Δs i) W Z)) :
    ∀ i, Ds' i = Z ∧
      (tps' i = .barren ∨ ∃ W, tps' i = .chain W ∧ Covers (Δs' i) W Z) := by
  intro i
  obtain ⟨j, ht, hΔ, hD⟩ := h'.2 i
  refine ⟨hD.trans (hDs j).1, ?_⟩
  rcases (hDs j).2 with hb | ⟨W, hW, hc⟩
  · exact Or.inl (ht ▸ hb)
  · exact Or.inr ⟨W, ht ▸ hW, hΔ ▸ hc⟩

end RegReindex

end Reindex

/-! ## S3: stored triples, sublist families, decidability guards -/

/-- A stored irregular row, unpacked with its derivation. -/
structure IrrT (G : Form) where
  St : List Form
  Th : List Form
  C : Form
  d : FRJWi G St Th C

/-- A stored regular row, unpacked with its derivation. -/
structure RegT (G : Form) where
  t : Tag
  Γ : List Form
  C : Form
  d : FRJWr G t Γ C

def rowIrr? {G : Form} : WRow G → Option (IrrT G)
  | ⟨.irr St Th C, d⟩ => some ⟨St, Th, C, d⟩
  | ⟨.reg _ _ _, _⟩ => none

def rowReg? {G : Form} : WRow G → Option (RegT G)
  | ⟨.reg t Γ C, d⟩ => some ⟨t, Γ, C, d⟩
  | ⟨.irr _ _ _, _⟩ => none

def irrTs {G : Form} (db : List (WRow G)) : List (IrrT G) :=
  db.filterMap rowIrr?

def regTs {G : Form} (db : List (WRow G)) : List (RegT G) :=
  db.filterMap rowReg?

def IrrT.seq {G : Form} (tr : IrrT G) : WSeq := .irr tr.St tr.Th tr.C
def RegT.seq {G : Form} (tr : RegT G) : WSeq := .reg tr.t tr.Γ tr.C

/-- Every stored irregular sequent has a triple. -/
theorem irrTs_of_mem {G : Form} {db : List (WRow G)}
    {St Th : List Form} {C : Form}
    (h : (WSeq.irr St Th C) ∈ db.map (·.s)) :
    ∃ tr ∈ irrTs db, tr.St = St ∧ tr.Th = Th ∧ tr.C = C := by
  obtain ⟨r, hr, hrs⟩ := List.mem_map.mp h
  match r, hrs with
  | ⟨.irr St' Th' C', d⟩, hrs =>
      injection hrs with h1 h2 h3
      exact ⟨⟨St', Th', C', d⟩, List.mem_filterMap.mpr ⟨_, hr, rfl⟩,
        h1, h2, h3⟩

theorem regTs_of_mem {G : Form} {db : List (WRow G)}
    {t : Tag} {Γ : List Form} {C : Form}
    (h : (WSeq.reg t Γ C) ∈ db.map (·.s)) :
    ∃ tr ∈ regTs db, tr.t = t ∧ tr.Γ = Γ ∧ tr.C = C := by
  obtain ⟨r, hr, hrs⟩ := List.mem_map.mp h
  match r, hrs with
  | ⟨.reg t' Γ' C', d⟩, hrs =>
      injection hrs with h1 h2 h3
      exact ⟨⟨t', Γ', C', d⟩, List.mem_filterMap.mpr ⟨_, hr, rfl⟩,
        h1, h2, h3⟩

/-- Every triple's sequent is stored. -/
theorem mem_of_irrTs {G : Form} {db : List (WRow G)} {tr : IrrT G}
    (h : tr ∈ irrTs db) : tr.seq ∈ db.map (·.s) := by
  obtain ⟨r, hr, hrt⟩ := List.mem_filterMap.mp h
  match r, hrt with
  | ⟨.irr St' Th' C', d⟩, hrt =>
      refine List.mem_map.mpr ⟨_, hr, ?_⟩
      injection hrt with h1
      subst h1
      rfl

theorem mem_of_regTs {G : Form} {db : List (WRow G)} {tr : RegT G}
    (h : tr ∈ regTs db) : tr.seq ∈ db.map (·.s) := by
  obtain ⟨r, hr, hrt⟩ := List.mem_filterMap.mp h
  match r, hrt with
  | ⟨.reg t' Γ' C', d⟩, hrt =>
      refine List.mem_map.mpr ⟨_, hr, ?_⟩
      injection hrt with h1
      subst h1
      rfl

/-- The triples' sequent image is a sublist of the store's. -/
theorem irrTs_seq_sublist {G : Form} (db : List (WRow G)) :
    List.Sublist ((irrTs db).map IrrT.seq) (db.map (·.s)) := by
  induction db with
  | nil => exact .slnil
  | cons r rest ih =>
      match r with
      | ⟨.irr St Th C, d⟩ =>
          simpa [irrTs, List.filterMap_cons, rowIrr?, IrrT.seq]
            using ih.cons_cons (WSeq.irr St Th C)
      | ⟨.reg t Γ C, d⟩ =>
          simpa [irrTs, List.filterMap_cons, rowIrr?]
            using ih.cons (WSeq.reg t Γ C)

theorem regTs_seq_sublist {G : Form} (db : List (WRow G)) :
    List.Sublist ((regTs db).map RegT.seq) (db.map (·.s)) := by
  induction db with
  | nil => exact .slnil
  | cons r rest ih =>
      match r with
      | ⟨.reg t Γ C, d⟩ =>
          simpa [regTs, List.filterMap_cons, rowReg?, RegT.seq]
            using ih.cons_cons (WSeq.reg t Γ C)
      | ⟨.irr St Th C, d⟩ =>
          simpa [regTs, List.filterMap_cons, rowReg?]
            using ih.cons (WSeq.irr St Th C)

/-! Decidability guards for the shape-bounded join conditions. -/

instance decImpGuard (P : Form → Form → Prop) [∀ A B, Decidable (P A B)]
    (x : Form) : Decidable (∀ A B, x = Form.imp A B → P A B) :=
  match x with
  | .imp A B =>
      if h : P A B then
        isTrue (fun A' B' he => by
          injection he with h1 h2
          exact h1 ▸ h2 ▸ h)
      else isFalse (fun hall => h (hall A B rfl))
  | .atom _ => isTrue (fun _ _ he => Form.noConfusion he)
  | .bot => isTrue (fun _ _ he => Form.noConfusion he)
  | .and _ _ => isTrue (fun _ _ he => Form.noConfusion he)
  | .or _ _ => isTrue (fun _ _ he => Form.noConfusion he)
  | .circ _ => isTrue (fun _ _ he => Form.noConfusion he)

instance decCircGuard (P : Form → Prop) [∀ Y, Decidable (P Y)]
    (x : Form) : Decidable (∀ Y, x = Form.circ Y → P Y) :=
  match x with
  | .circ Y =>
      if h : P Y then
        isTrue (fun Y' he => by injection he with h1; exact h1 ▸ h)
      else isFalse (fun hall => h (hall Y rfl))
  | .atom _ => isTrue (fun _ he => Form.noConfusion he)
  | .bot => isTrue (fun _ he => Form.noConfusion he)
  | .and _ _ => isTrue (fun _ he => Form.noConfusion he)
  | .or _ _ => isTrue (fun _ he => Form.noConfusion he)
  | .imp _ _ => isTrue (fun _ he => Form.noConfusion he)

/-- `∀` over `Fin` decided through `List.finRange` (mathlib's `Fin`
instances are avoided for the choice-free pins). -/
def decForallFin {n : Nat} (p : Fin n → Prop) [DecidablePred p] :
    Decidable (∀ i, p i) :=
  decidable_of_iff (∀ i ∈ List.finRange n, p i)
    ⟨fun h i => h i (List.mem_finRange i), fun h i _ => h i⟩

def decExistsFin {n : Nat} (p : Fin n → Prop) [DecidablePred p] :
    Decidable (∃ i, p i) :=
  decidable_of_iff (∃ i ∈ List.finRange n, p i)
    ⟨fun ⟨i, _, h⟩ => ⟨i, h⟩, fun ⟨i, h⟩ => ⟨i, List.mem_finRange i, h⟩⟩

instance {n : Nat} (p : Fin n → Prop) [DecidablePred p] :
    Decidable (∀ i, p i) := decForallFin p

instance {n : Nat} (p : Fin n → Prop) [DecidablePred p] :
    Decidable (∃ i, p i) := decExistsFin p

/-- Shape-bounded to unbounded: the implication guard. -/
theorem impGuard_elim {pool : List Form} {P : Form → Form → Prop}
    (h : ∀ x ∈ pool, ∀ A B, x = Form.imp A B → P A B) :
    ∀ A B, Form.imp A B ∈ pool → P A B :=
  fun A B hmem => h _ hmem A B rfl

theorem circGuard_elim {pool : List Form} {P : Form → Prop}
    (h : ∀ x ∈ pool, ∀ Y, x = Form.circ Y → P Y) :
    ∀ Y, Form.circ Y ∈ pool → P Y :=
  fun Y hmem => h _ hmem Y rfl

/-- The bounded forms hold whenever the unbounded do (coverage side). -/
theorem impGuard_intro {pool : List Form} {P : Form → Form → Prop}
    (h : ∀ A B, Form.imp A B ∈ pool → P A B) :
    ∀ x ∈ pool, ∀ A B, x = Form.imp A B → P A B :=
  fun _ hx A B he => h A B (he ▸ hx)

theorem circGuard_intro {pool : List Form} {P : Form → Prop}
    (h : ∀ Y, Form.circ Y ∈ pool → P Y) :
    ∀ x ∈ pool, ∀ Y, x = Form.circ Y → P Y :=
  fun _ hx Y he => h Y (he ▸ hx)

/-! ## S4: the emitters

Each emitter fires one rule at every stored premise combination,
guarded by a `dite` on the rule's OWN hypotheses (all decidable), so
the emitted row carries its derivation by the constructor.  Coverage
(S5) will show each `DBClosed` clause instance, reindexed to stored
sublists, is emitted. -/

/-- The two-sided filter split of a zone by a parameter list. -/
theorem filter_split_pre (L Lam : List Form) :
    L ≐ L.filter (fun x => !decide (x ∈ Lam)) ++
      L.filter (fun x => decide (x ∈ Lam)) := by
  intro x
  simp only [List.mem_append, List.mem_filter, Bool.not_eq_eq_eq_not,
    Bool.not_true, decide_eq_true_eq, decide_eq_false_iff_not]
  constructor
  · intro hx
    by_cases hL : x ∈ Lam
    · exact Or.inr ⟨hx, hL⟩
    · exact Or.inl ⟨hx, hL⟩
  · rintro (⟨hx, -⟩ | ⟨hx, -⟩) <;> exact hx

theorem filter_split_disj (L Lam : List Form) :
    cap (L.filter (fun x => !decide (x ∈ Lam)))
      (L.filter (fun x => decide (x ∈ Lam))) = [] := by
  refine List.eq_nil_of_subset_nil (fun x hx => ?_)
  have h := mem_cap.mp hx
  have h₁ := List.mem_filter.mp h.1
  have h₂ := List.mem_filter.mp h.2
  rw [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h₁
  rw [decide_eq_true_eq] at h₂
  exact absurd h₂.2 h₁.2

section Emitters

variable (G : Form)

/-- `Ax^R`. -/
def emitAxR : List (WRow G) :=
  (goalPool G).filterMap (fun F =>
    if h : F.isPrime = true ∧ F ∈ sfR G then
      some ⟨.reg .barren (rm (gAt G) F) F, .axR F h.1 h.2 (CtxEq.refl _)⟩
    else none)

/-- `Ax^I`. -/
def emitAxI : List (WRow G) :=
  (goalPool G).filterMap (fun F =>
    if h : F.isPrime = true ∧ F ∈ sfR G then
      some ⟨.irr [] (rm (gAt G) F ++ gImp G ++ gCirc G) F,
        .axI F h.1 h.2 (CtxEq.refl _)⟩
    else none)

/-- `Ax^I◯`, over the canonical valuations. -/
def emitAxIC : List (WRow G) :=
  (goalPool G).flatMap (fun X =>
    match X with
    | .circ F =>
        (gAt G).sublists.filterMap (fun ats =>
          if h : (∀ x ∈ ats, x ∈ gAt G) ∧ classForce ats F = false ∧
              Form.circ F ∈ sfR G then
            some ⟨.irr [] (vacZoneA G ats) (.circ F),
              .axIC F ats h.1 h.2.1 h.2.2 (CtxEq.refl _)⟩
          else none)
    | _ => [])

variable (db : List (WRow G))

/-- `∧R` (both sides). -/
def emitAndR : List (WRow G) :=
  (regTs db).flatMap (fun tr =>
    (goalPool G).filterMap (fun X =>
      match X with
      | .and A₁ A₂ =>
          if h : A₁ = tr.C ∧ Form.and A₁ A₂ ∈ sfR G then
            some ⟨.reg tr.t tr.Γ (.and A₁ A₂), .andR1 (h.1 ▸ tr.d) h.2⟩
          else if h : A₂ = tr.C ∧ Form.and A₁ A₂ ∈ sfR G then
            some ⟨.reg tr.t tr.Γ (.and A₁ A₂), .andR2 (h.1 ▸ tr.d) h.2⟩
          else none
      | _ => none))

/-- `⊃∈`. -/
def emitImpIn : List (WRow G) :=
  (regTs db).flatMap (fun tr =>
    (goalPool G).filterMap (fun X =>
      match X with
      | .imp A B =>
          if h : B = tr.C ∧ Clo tr.Γ A ∧ Form.imp A B ∈ sfR G then
            some ⟨.reg tr.t tr.Γ (.imp A B),
              .impIn (h.1 ▸ tr.d) h.2.1 h.2.2⟩
          else none
      | _ => none))

/-- `◯∈`. -/
def emitCircIn : List (WRow G) :=
  (regTs db).flatMap (fun tr =>
    (goalPool G).filterMap (fun X =>
      match X with
      | .circ Z =>
          if h : Z = tr.C ∧
              (tr.t = .barren ∨ ∃ W, tr.t = .chain W ∧ Covers tr.Γ W Z) ∧
              Form.circ Z ∈ sfR G then
            some ⟨.reg tr.t tr.Γ (.circ Z),
              .circIn (h.1 ▸ tr.d) h.2.1 h.2.2⟩
          else none
      | _ => none))

/-- `∧I` (both sides). -/
def emitAndI : List (WRow G) :=
  (irrTs db).flatMap (fun tr =>
    (goalPool G).filterMap (fun X =>
      match X with
      | .and A₁ A₂ =>
          if h : A₁ = tr.C ∧ Form.and A₁ A₂ ∈ sfR G then
            some ⟨.irr tr.St tr.Th (.and A₁ A₂), .andI1 (h.1 ▸ tr.d) h.2⟩
          else if h : A₂ = tr.C ∧ Form.and A₁ A₂ ∈ sfR G then
            some ⟨.irr tr.St tr.Th (.and A₁ A₂), .andI2 (h.1 ▸ tr.d) h.2⟩
          else none
      | _ => none))

/-- `∨I`. -/
def emitOrI : List (WRow G) :=
  (irrTs db).flatMap (fun tr₁ =>
    (irrTs db).flatMap (fun tr₂ =>
      (goalPool G).filterMap (fun X =>
        match X with
        | .or C₁ C₂ =>
            if h : C₁ = tr₁.C ∧ C₂ = tr₂.C ∧
                tr₁.St ⊆ tr₂.St ++ tr₂.Th ∧ tr₂.St ⊆ tr₁.St ++ tr₁.Th ∧
                Form.or C₁ C₂ ∈ sfR G then
              some ⟨.irr (tr₁.St ++ tr₂.St) (cap tr₁.Th tr₂.Th)
                  (.or C₁ C₂),
                .orI (h.1 ▸ tr₁.d) (h.2.1 ▸ tr₂.d) h.2.2.1 h.2.2.2.1
                  h.2.2.2.2 (CtxEq.refl _) (CtxEq.refl _)⟩
            else none
        | _ => none)))

/-- `⊃∈ᵢ`, over the canonical second-zone splits. -/
def emitImpInI : List (WRow G) :=
  (irrTs db).flatMap (fun tr =>
    tr.Th.sublists.flatMap (fun Lam =>
      (goalPool G).filterMap (fun X =>
        match X with
        | .imp A B =>
            if h : B = tr.C ∧
                Clo (tr.St ++ tr.Th.filter (fun x => decide (x ∈ Lam))) A ∧
                Form.imp A B ∈ sfR G then
              some ⟨.irr (tr.St ++ tr.Th.filter (fun x => decide (x ∈ Lam)))
                  (tr.Th.filter (fun x => !decide (x ∈ Lam))) (.imp A B),
                .impInI (h.1 ▸ tr.d) (filter_split_pre tr.Th Lam)
                  (filter_split_disj tr.Th Lam) h.2.1 h.2.2
                  (CtxEq.refl _) (CtxEq.refl _)⟩
            else none
        | _ => none)))

/-- `Lift`, at the maximal retained zone. -/
def emitLift : List (WRow G) :=
  (regTs db).map (fun tr => ⟨.irr [] (maxTh G tr.Γ) tr.C, lift_max tr.d⟩)

/-- `◯∉`, at the maximal retained zone. -/
def emitCircNotIn : List (WRow G) :=
  (regTs db).filterMap (fun tr =>
    if h : (tr.t = .barren ∨ ∃ W, tr.t = .chain W ∧ Covers tr.Γ W tr.C) ∧
        Form.circ tr.C ∈ sfR G then
      some ⟨.irr [] (maxTh G tr.Γ) (.circ tr.C),
        circNotIn_max tr.d (fun _ hx => hx) (tagLeB_refl _) h.1 h.2⟩
    else none)

end Emitters

/-- Decidable list inclusion (via `subB`), kept local to avoid instance
surprises. -/
instance decListSubset (l m : List Form) : Decidable (l ⊆ m) :=
  decidable_of_iff (∀ x ∈ l, x ∈ m)
    ⟨fun h _ hx => h _ hx, fun h _ hx => h hx⟩

section JoinEmitters

variable (G : Form) (db : List (WRow G))

/-- Barren `⋈^◯`. -/
def emitJoinCirc : List (WRow G) :=
  (irrTs db).sublists.flatMap (fun l =>
    match l with
    | [] => []
    | a :: t =>
        let stabF : Fin (t.length + 1) → List Form :=
          fun j => ((a :: t).get j).St
        let thF : Fin (t.length + 1) → List Form :=
          fun j => ((a :: t).get j).Th
        let rhsF : Fin (t.length + 1) → Form :=
          fun j => ((a :: t).get j).C
        let base := joinCtxOrVBase stabF thF
        let kept := keptOf (upsilon rhsF) base (thPool thF)
        (goalPool G).filterMap (fun X =>
          match X with
          | .circ Z =>
              if h : (∀ i j, i ≠ j → stabF i ⊆ stabF j ++ thF j) ∧
                  (∀ x ∈ unionAll (fun j => impPart (stabF j)), ∀ A B : Form,
                    x = Form.imp A B →
                    RefAt true (upsilon rhsF) (base ++ kept) A) ∧
                  unionAll (fun j => circPart (stabF j)) = [] ∧
                  RefAt true (upsilon rhsF) (base ++ kept) Z ∧
                  Form.circ Z ∈ sfR G then
                some ⟨.reg .barren (base ++ kept) (.circ Z),
                  .joinCirc (fun j => ((a :: t).get j).d) h.1
                    (impGuard_elim h.2.1) h.2.2.1 (keptOf_ok _ _ _)
                    h.2.2.2.1 h.2.2.2.2 (CtxEq.refl _)⟩
              else none
          | _ => none))

/-- Barren `⋈^∨`. -/
def emitJoinOr : List (WRow G) :=
  (irrTs db).sublists.flatMap (fun l =>
    match l with
    | [] => []
    | a :: t =>
        let stabF : Fin (t.length + 1) → List Form :=
          fun j => ((a :: t).get j).St
        let thF : Fin (t.length + 1) → List Form :=
          fun j => ((a :: t).get j).Th
        let rhsF : Fin (t.length + 1) → Form :=
          fun j => ((a :: t).get j).C
        let base := joinCtxOrVBase stabF thF
        let kept := keptOf (upsilon rhsF) base (thPool thF)
        (goalPool G).filterMap (fun X =>
          match X with
          | .or C₁ C₂ =>
              if h : (∀ i j, i ≠ j → stabF i ⊆ stabF j ++ thF j) ∧
                  (∀ x ∈ unionAll (fun j => impPart (stabF j)), ∀ A B : Form,
                    x = Form.imp A B → A ∈ upsilon rhsF) ∧
                  unionAll (fun j => circPart (stabF j)) = [] ∧
                  (RefAt true (upsilon rhsF) (base ++ kept) C₁ ∧
                    RefAt true (upsilon rhsF) (base ++ kept) C₂) ∧
                  Form.or C₁ C₂ ∈ sfR G then
                some ⟨.reg .barren (base ++ kept) (.or C₁ C₂),
                  .joinOr (fun j => ((a :: t).get j).d) h.1
                    (impGuard_elim h.2.1) h.2.2.1 (keptOf_ok _ _ _)
                    h.2.2.2.1 h.2.2.2.2 (CtxEq.refl _)⟩
              else none
          | _ => none))

/-- Barren `⋈^At`. -/
def emitJoinAt : List (WRow G) :=
  (irrTs db).sublists.flatMap (fun l =>
    match l with
    | [] => []
    | a :: t =>
        let stabF : Fin (t.length + 1) → List Form :=
          fun j => ((a :: t).get j).St
        let thF : Fin (t.length + 1) → List Form :=
          fun j => ((a :: t).get j).Th
        let rhsF : Fin (t.length + 1) → Form :=
          fun j => ((a :: t).get j).C
        (goalPool G).filterMap (fun F =>
          let base := joinCtxAtVBase stabF thF F
          let kept := keptOf (upsilon rhsF) base (thPool thF)
          if h : (∀ i j, i ≠ j → stabF i ⊆ stabF j ++ thF j) ∧
              (∀ x ∈ unionAll (fun j => impPart (stabF j)), ∀ A B : Form,
                x = Form.imp A B → A ∈ upsilon rhsF) ∧
              unionAll (fun j => circPart (stabF j)) = [] ∧
              F.isPrime = true ∧
              F ∉ unionAll (fun j => atPart (stabF j)) ∧
              F ∈ sfR G then
            some ⟨.reg .barren (base ++ kept) F,
              .joinAt (fun j => ((a :: t).get j).d) h.1
                (impGuard_elim h.2.1) h.2.2.1 (keptOf_ok _ _ _)
                h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2 (CtxEq.refl _)⟩
          else none))

/-- Fallible `⋈^At`. -/
def emitJoinAtF : List (WRow G) :=
  (irrTs db).sublists.flatMap (fun l =>
    match l with
    | [] => []
    | a :: t =>
        let stabF : Fin (t.length + 1) → List Form :=
          fun j => ((a :: t).get j).St
        let thF : Fin (t.length + 1) → List Form :=
          fun j => ((a :: t).get j).Th
        let rhsF : Fin (t.length + 1) → Form :=
          fun j => ((a :: t).get j).C
        (goalPool G).filterMap (fun F =>
          if h : (∀ i j, i ≠ j → stabF i ⊆ stabF j ++ thF j) ∧
              (∀ x ∈ unionAll (fun j => impPart (stabF j)), ∀ A B : Form,
                x = Form.imp A B → A ∈ upsilon rhsF) ∧
              F.isPrime = true ∧
              F ∉ unionAll (fun j => atPart (stabF j)) ∧
              F ∈ sfR G then
            some ⟨.reg .blocked (joinCtxAtF stabF thF rhsF F) F,
              .joinAtF (fun j => ((a :: t).get j).d) h.1
                (impGuard_elim h.2.1) h.2.2.1 h.2.2.2.1 h.2.2.2.2
                (CtxEq.refl _)⟩
          else none))

/-- Fallible `⋈^∨`. -/
def emitJoinOrF : List (WRow G) :=
  (irrTs db).sublists.flatMap (fun l =>
    match l with
    | [] => []
    | a :: t =>
        let stabF : Fin (t.length + 1) → List Form :=
          fun j => ((a :: t).get j).St
        let thF : Fin (t.length + 1) → List Form :=
          fun j => ((a :: t).get j).Th
        let rhsF : Fin (t.length + 1) → Form :=
          fun j => ((a :: t).get j).C
        (goalPool G).filterMap (fun X =>
          match X with
          | .or C₁ C₂ =>
              if h : (∀ i j, i ≠ j → stabF i ⊆ stabF j ++ thF j) ∧
                  (∀ x ∈ unionAll (fun j => impPart (stabF j)), ∀ A B : Form,
                    x = Form.imp A B → A ∈ upsilon rhsF) ∧
                  (C₁ ∈ upsilon rhsF ∧ C₂ ∈ upsilon rhsF) ∧
                  Form.or C₁ C₂ ∈ sfR G then
                some ⟨.reg .blocked (joinCtxOrF stabF thF rhsF) (.or C₁ C₂),
                  .joinOrF (fun j => ((a :: t).get j).d) h.1
                    (impGuard_elim h.2.1) h.2.2.1 h.2.2.2 (CtxEq.refl _)⟩
              else none
          | _ => none))

/-- Promise `⋈^At` (chain branch; the blocked branch is subsumed by the
fallible join). -/
def emitJoinAtP : List (WRow G) :=
  (irrTs db).sublists.flatMap (fun l =>
    match l with
    | [] => []
    | a :: t =>
        let stabF : Fin (t.length + 1) → List Form :=
          fun j => ((a :: t).get j).St
        let thF : Fin (t.length + 1) → List Form :=
          fun j => ((a :: t).get j).Th
        let rhsF : Fin (t.length + 1) → Form :=
          fun j => ((a :: t).get j).C
        (regTs db).sublists.flatMap (fun lr =>
          match lr with
          | [] => []
          | b :: u =>
              let tpsF : Fin (u.length + 1) → Tag :=
                fun i => ((b :: u).get i).t
              let ΔsF : Fin (u.length + 1) → List Form :=
                fun i => ((b :: u).get i).Γ
              let DsF : Fin (u.length + 1) → Form :=
                fun i => ((b :: u).get i).C
              (goalPool G).filterMap (fun F =>
                if h : (∀ i j, i ≠ j → stabF i ⊆ stabF j ++ thF j) ∧
                    (∀ x ∈ unionAll (fun j => impPart (stabF j)),
                      ∀ A B : Form, x = Form.imp A B → A ∈ upsilon rhsF) ∧
                    (∀ x ∈ unionAll (fun j => circPart (stabF j)),
                      ∀ Y : Form, x = Form.circ Y → ∃ i, Clo (ΔsF i) Y) ∧
                    (∀ i j, ∀ X ∈ stabF j, Clo (ΔsF i) X) ∧
                    (∀ i, DsF i = DsF 0 ∧
                      (tpsF i = .barren ∨ ∃ W, tpsF i = .chain W ∧
                        Covers (ΔsF i) W (DsF 0))) ∧
                    F.isPrime = true ∧
                    F ∉ unionAll (fun j => atPart (stabF j)) ∧
                    F ∈ sfR G then
                  some ⟨.reg (.chain (DsF 0))
                      (joinCtxAtP stabF thF rhsF F ΔsF) F,
                    .joinAtP (fun j => ((a :: t).get j).d)
                      (fun i => ((b :: u).get i).d) h.1
                      (impGuard_elim h.2.1) (circGuard_elim h.2.2.1)
                      h.2.2.2.1 (Or.inr ⟨rfl, h.2.2.2.2.1⟩)
                      h.2.2.2.2.2.1 h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2
                      (CtxEq.refl _)⟩
                else none)))

/-- Promise `⋈^∨` (chain branch). -/
def emitJoinOrP : List (WRow G) :=
  (irrTs db).sublists.flatMap (fun l =>
    match l with
    | [] => []
    | a :: t =>
        let stabF : Fin (t.length + 1) → List Form :=
          fun j => ((a :: t).get j).St
        let thF : Fin (t.length + 1) → List Form :=
          fun j => ((a :: t).get j).Th
        let rhsF : Fin (t.length + 1) → Form :=
          fun j => ((a :: t).get j).C
        (regTs db).sublists.flatMap (fun lr =>
          match lr with
          | [] => []
          | b :: u =>
              let tpsF : Fin (u.length + 1) → Tag :=
                fun i => ((b :: u).get i).t
              let ΔsF : Fin (u.length + 1) → List Form :=
                fun i => ((b :: u).get i).Γ
              let DsF : Fin (u.length + 1) → Form :=
                fun i => ((b :: u).get i).C
              (goalPool G).filterMap (fun X =>
                match X with
                | .or C₁ C₂ =>
                    if h : (∀ i j, i ≠ j → stabF i ⊆ stabF j ++ thF j) ∧
                        (∀ x ∈ unionAll (fun j => impPart (stabF j)),
                          ∀ A B : Form, x = Form.imp A B →
                            A ∈ upsilon rhsF) ∧
                        (∀ x ∈ unionAll (fun j => circPart (stabF j)),
                          ∀ Y : Form, x = Form.circ Y →
                            ∃ i, Clo (ΔsF i) Y) ∧
                        (∀ i j, ∀ X ∈ stabF j, Clo (ΔsF i) X) ∧
                        (∀ i, DsF i = DsF 0 ∧
                          (tpsF i = .barren ∨ ∃ W, tpsF i = .chain W ∧
                            Covers (ΔsF i) W (DsF 0))) ∧
                        (C₁ ∈ upsilon rhsF ∧ C₂ ∈ upsilon rhsF) ∧
                        Form.or C₁ C₂ ∈ sfR G then
                      some ⟨.reg (.chain (DsF 0))
                          (joinCtxOrP stabF thF rhsF ΔsF) (.or C₁ C₂),
                        .joinOrP (fun j => ((a :: t).get j).d)
                          (fun i => ((b :: u).get i).d) h.1
                          (impGuard_elim h.2.1) (circGuard_elim h.2.2.1)
                          h.2.2.2.1 (Or.inr ⟨rfl, h.2.2.2.2.1⟩)
                          h.2.2.2.2.2.1 h.2.2.2.2.2.2 (CtxEq.refl _)⟩
                    else none
                | _ => none)))

/-- Promise `⋈^◯`. -/
def emitJoinCircP : List (WRow G) :=
  (irrTs db).sublists.flatMap (fun l =>
    match l with
    | [] => []
    | a :: t =>
        let stabF : Fin (t.length + 1) → List Form :=
          fun j => ((a :: t).get j).St
        let thF : Fin (t.length + 1) → List Form :=
          fun j => ((a :: t).get j).Th
        let rhsF : Fin (t.length + 1) → Form :=
          fun j => ((a :: t).get j).C
        (regTs db).sublists.flatMap (fun lr =>
          match lr with
          | [] => []
          | b :: u =>
              let tpsF : Fin (u.length + 1) → Tag :=
                fun i => ((b :: u).get i).t
              let ΔsF : Fin (u.length + 1) → List Form :=
                fun i => ((b :: u).get i).Γ
              let DsF : Fin (u.length + 1) → Form :=
                fun i => ((b :: u).get i).C
              (goalPool G).filterMap (fun X =>
                match X with
                | .circ Z =>
                    if h : (∀ i j, i ≠ j → stabF i ⊆ stabF j ++ thF j) ∧
                        (∀ x ∈ unionAll (fun j => impPart (stabF j)),
                          ∀ A B : Form, x = Form.imp A B →
                            A ∈ upsilon rhsF) ∧
                        (∀ x ∈ unionAll (fun j => circPart (stabF j)),
                          ∀ Y : Form, x = Form.circ Y →
                            ∃ i, Clo (ΔsF i) Y) ∧
                        (∀ i j, ∀ X ∈ stabF j, Clo (ΔsF i) X) ∧
                        (∀ i, DsF i = Z ∧
                          (tpsF i = .barren ∨ ∃ W, tpsF i = .chain W ∧
                            Covers (ΔsF i) W Z)) ∧
                        Z ∈ upsilon rhsF ∧
                        Form.circ Z ∈ sfR G then
                      some ⟨.reg (.chain Z)
                          (joinCtxOrP stabF thF rhsF ΔsF) (.circ Z),
                        .joinCircP (fun j => ((a :: t).get j).d)
                          (fun i => ((b :: u).get i).d) h.1
                          (impGuard_elim h.2.1) (circGuard_elim h.2.2.1)
                          h.2.2.2.1 h.2.2.2.2.1
                          h.2.2.2.2.2.1 h.2.2.2.2.2.2 (CtxEq.refl _)⟩
                    else none
                | _ => none)))

end JoinEmitters

/-- One saturation step: every rule fired at every stored combination. -/
def stepAll (G : Form) (db : List (WRow G)) : List (WRow G) :=
  emitAxR G ++ emitAxI G ++ emitAxIC G ++
    emitAndR G db ++ emitImpIn G db ++ emitCircIn G db ++
    emitAndI G db ++ emitOrI G db ++ emitImpInI G db ++
    emitLift G db ++ emitCircNotIn G db ++
    emitJoinAt G db ++ emitJoinOr G db ++ emitJoinCirc G db ++
    emitJoinAtF G db ++ emitJoinOrF G db ++
    emitJoinAtP G db ++ emitJoinOrP G db ++ emitJoinCircP G db

/-! ## S6: saturation, and the pigeonhole that ends it

Rows are only ever PREPENDED, keyed by canonical sequent; a round that
adds nothing is a fixpoint; a round that adds something grows the
key-nodup store, which lives inside the finite wellformed universe.
So `univList.length + 1` rounds reach the fixpoint from the empty
store. -/

variable {G : Form}

/-- The canonical key of a row. -/
def keyOf (G : Form) (r : WRow G) : WSeq := canonSeq G r.s

def keysOf (G : Form) (db : List (WRow G)) : List WSeq :=
  db.map (keyOf G)

/-- Insert the rows whose canonical key is not yet present. -/
def insertNew (G : Form) (new db : List (WRow G)) : List (WRow G) :=
  new.foldl (fun acc r =>
    if keyOf G r ∈ keysOf G acc then acc else r :: acc) db

/-- The store only grows. -/
theorem insertNew_sup {G : Form} :
    ∀ (new db : List (WRow G)), db ⊆ insertNew G new db := by
  intro new
  induction new with
  | nil => exact fun db _ h => h
  | cons r rest ih =>
      intro db x hx
      simp only [insertNew, List.foldl_cons]
      by_cases hk : keyOf G r ∈ keysOf G db
      · rw [if_pos hk]
        exact ih db hx
      · rw [if_neg hk]
        exact ih (r :: db) (List.mem_cons_of_mem _ hx)

theorem insertNew_length_le {G : Form} :
    ∀ (new db : List (WRow G)),
      db.length ≤ (insertNew G new db).length := by
  intro new
  induction new with
  | nil => exact fun _ => Nat.le_refl _
  | cons r rest ih =>
      intro db
      simp only [insertNew, List.foldl_cons]
      by_cases hk : keyOf G r ∈ keysOf G db
      · rw [if_pos hk]; exact ih db
      · rw [if_neg hk]
        exact Nat.le_trans (Nat.le_succ _) (ih (r :: db))

/-- A round holding a genuinely fresh key strictly grows the store. -/
theorem insertNew_length_lt {G : Form} :
    ∀ (new db : List (WRow G)),
      (∃ r ∈ new, keyOf G r ∉ keysOf G db) →
      db.length < (insertNew G new db).length := by
  intro new
  induction new with
  | nil => rintro db ⟨r, hr, -⟩; exact absurd hr List.not_mem_nil
  | cons r rest ih =>
      rintro db ⟨w, hw, hfresh⟩
      simp only [insertNew, List.foldl_cons]
      by_cases hk : keyOf G r ∈ keysOf G db
      · rw [if_pos hk]
        rcases List.mem_cons.mp hw with rfl | hw'
        · exact absurd hk hfresh
        · exact ih db ⟨w, hw', hfresh⟩
      · rw [if_neg hk]
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
          (insertNew_length_le rest (r :: db))

/-- Key-nodupness survives insertion. -/
theorem insertNew_nodup {G : Form} :
    ∀ (new db : List (WRow G)), (keysOf G db).Nodup →
      (keysOf G (insertNew G new db)).Nodup := by
  intro new
  induction new with
  | nil => exact fun _ h => h
  | cons r rest ih =>
      intro db hnd
      simp only [insertNew, List.foldl_cons]
      by_cases hk : keyOf G r ∈ keysOf G db
      · rw [if_pos hk]; exact ih db hnd
      · rw [if_neg hk]
        exact ih (r :: db) (List.nodup_cons.mpr ⟨hk, hnd⟩)

/-- The new rows of a round. -/
def stepNew (G : Form) (db : List (WRow G)) : List (WRow G) :=
  (stepAll G db).filter (fun r => decide (keyOf G r ∉ keysOf G db))

def sat (G : Form) : Nat → List (WRow G) → List (WRow G)
  | 0, db => db
  | fuel + 1, db =>
      let new := stepNew G db
      if new.isEmpty then db else sat G fuel (insertNew G new db)

theorem sat_sup {G : Form} :
    ∀ (fuel : Nat) (db : List (WRow G)), db ⊆ sat G fuel db := by
  intro fuel
  induction fuel with
  | zero => exact fun _ _ h => h
  | succ fuel ih =>
      intro db
      simp only [sat]
      by_cases he : (stepNew G db).isEmpty
      · rw [if_pos he]; exact fun _ h => h
      · rw [if_neg he]
        exact fun x hx => ih _ (insertNew_sup _ db hx)

/-- Every stored key lies in the wellformed universe. -/
theorem keys_sub_univ {G : Form} (db : List (WRow G)) :
    ∀ k ∈ keysOf G db, k ∈ univList G := by
  intro k hk
  obtain ⟨r, -, rfl⟩ := List.mem_map.mp hk
  exact canonSeq_mem_univ (wfSeq_of_wDer r.d)

/-- The pigeonhole: with enough fuel the round adds nothing. -/
theorem sat_fixed {G : Form} :
    ∀ (fuel : Nat) (db : List (WRow G)), (keysOf G db).Nodup →
      (univList G).length + 1 ≤ db.length + fuel →
      (stepNew G (sat G fuel db)).isEmpty = true := by
  intro fuel
  induction fuel with
  | zero =>
      intro db hnd hlen
      exfalso
      have hbound : db.length ≤ (univList G).length := by
        have := length_le_of_nodup_subset hnd (keys_sub_univ db)
        simpa [keysOf] using this
      omega
  | succ fuel ih =>
      intro db hnd hlen
      simp only [sat]
      by_cases he : (stepNew G db).isEmpty
      · rw [if_pos he]; exact he
      · rw [if_neg he]
        have hne : stepNew G db ≠ [] := by
          intro h
          rw [h] at he
          exact he rfl
        obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil _ hne
        have hfresh : keyOf G w ∉ keysOf G db := by
          have := (List.mem_filter.mp hw).2
          simpa using this
        have hlt := insertNew_length_lt (stepNew G db) db
          ⟨w, hw, hfresh⟩
        exact ih (insertNew G (stepNew G db) db)
          (insertNew_nodup _ db hnd) (by omega)

/-- **The closed database.** -/
def closureDB (G : Form) : List (WRow G) :=
  sat G ((univList G).length + 1) []

/-- At the fixpoint, every emitted row's canonical key is stored. -/
theorem closureDB_fixed (G : Form) :
    ∀ r ∈ stepAll G (closureDB G),
      canonSeq G r.s ∈ keysOf G (closureDB G) := by
  intro r hr
  have hfix : (stepNew G (closureDB G)).isEmpty = true := by
    have := sat_fixed (G := G) ((univList G).length + 1) []
      List.nodup_nil (by simp)
    simpa [closureDB] using this
  by_contra hnot
  have hmem : r ∈ stepNew G (closureDB G) :=
    List.mem_filter.mpr ⟨hr, by simpa [keyOf] using hnot⟩
  rw [List.isEmpty_iff] at hfix
  rw [hfix] at hmem
  exact absurd hmem List.not_mem_nil

/-- Fixpoint presence, packaged for the closedness clauses: an emitted
row is subsumed by a stored one. -/
theorem stored_of_emitted {G : Form} {r : WRow G}
    (h : r ∈ stepAll G (closureDB G)) :
    ∃ e ∈ closureDB G, WSubsumes r.s e.s := by
  obtain ⟨e, he, hkey⟩ := List.mem_map.mp (closureDB_fixed G r h)
  exact ⟨e, he, subsumes_of_canonSeq_eq (wfSeq_of_wDer r.d)
    (wfSeq_of_wDer e.d) hkey.symm⟩

/-! ## S5: coverage — every clause instance is emitted

First the plumbing: sequent-nodupness of the closure store, membership
of each emitter in `stepAll`, and the reindexing extraction (the stored
sublist listing an arbitrary family's row set, with the `SameIrr`/
`SameReg` relations and pairwise distinctness). -/

theorem sat_nodup {G : Form} :
    ∀ (fuel : Nat) (db : List (WRow G)), (keysOf G db).Nodup →
      (keysOf G (sat G fuel db)).Nodup
  | 0, _, h => h
  | fuel + 1, db, h => by
      simp only [sat]
      by_cases he : (stepNew G db).isEmpty
      · rw [if_pos he]; exact h
      · rw [if_neg he]
        exact sat_nodup fuel _ (insertNew_nodup _ db h)

theorem closureDB_keys_nodup (G : Form) :
    (keysOf G (closureDB G)).Nodup :=
  sat_nodup _ _ List.nodup_nil

theorem closureDB_seq_nodup (G : Form) :
    ((closureDB G).map (·.s)).Nodup := by
  have h := closureDB_keys_nodup G
  have heq : keysOf G (closureDB G) =
      ((closureDB G).map (·.s)).map (canonSeq G) := by
    simp [keysOf, keyOf, List.map_map]
  rw [heq] at h
  exact h.of_map

theorem sub_stepAll_AxR {G : Form} {db : List (WRow G)} :
    ∀ x ∈ emitAxR G, x ∈ stepAll G db := by
  intro x hx
  simp only [stepAll, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hx)))))))))))))))))

theorem sub_stepAll_AxI {G : Form} {db : List (WRow G)} :
    ∀ x ∈ emitAxI G, x ∈ stepAll G db := by
  intro x hx
  simp only [stepAll, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hx)))))))))))))))))

theorem sub_stepAll_AxIC {G : Form} {db : List (WRow G)} :
    ∀ x ∈ emitAxIC G, x ∈ stepAll G db := by
  intro x hx
  simp only [stepAll, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hx))))))))))))))))

theorem sub_stepAll_AndR {G : Form} {db : List (WRow G)} :
    ∀ x ∈ emitAndR G db, x ∈ stepAll G db := by
  intro x hx
  simp only [stepAll, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hx)))))))))))))))

theorem sub_stepAll_ImpIn {G : Form} {db : List (WRow G)} :
    ∀ x ∈ emitImpIn G db, x ∈ stepAll G db := by
  intro x hx
  simp only [stepAll, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hx))))))))))))))

theorem sub_stepAll_CircIn {G : Form} {db : List (WRow G)} :
    ∀ x ∈ emitCircIn G db, x ∈ stepAll G db := by
  intro x hx
  simp only [stepAll, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hx)))))))))))))

theorem sub_stepAll_AndI {G : Form} {db : List (WRow G)} :
    ∀ x ∈ emitAndI G db, x ∈ stepAll G db := by
  intro x hx
  simp only [stepAll, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hx))))))))))))

theorem sub_stepAll_OrI {G : Form} {db : List (WRow G)} :
    ∀ x ∈ emitOrI G db, x ∈ stepAll G db := by
  intro x hx
  simp only [stepAll, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hx)))))))))))

theorem sub_stepAll_ImpInI {G : Form} {db : List (WRow G)} :
    ∀ x ∈ emitImpInI G db, x ∈ stepAll G db := by
  intro x hx
  simp only [stepAll, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hx))))))))))

theorem sub_stepAll_Lift {G : Form} {db : List (WRow G)} :
    ∀ x ∈ emitLift G db, x ∈ stepAll G db := by
  intro x hx
  simp only [stepAll, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hx)))))))))

theorem sub_stepAll_CircNotIn {G : Form} {db : List (WRow G)} :
    ∀ x ∈ emitCircNotIn G db, x ∈ stepAll G db := by
  intro x hx
  simp only [stepAll, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hx))))))))

theorem sub_stepAll_JoinAt {G : Form} {db : List (WRow G)} :
    ∀ x ∈ emitJoinAt G db, x ∈ stepAll G db := by
  intro x hx
  simp only [stepAll, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hx)))))))

theorem sub_stepAll_JoinOr {G : Form} {db : List (WRow G)} :
    ∀ x ∈ emitJoinOr G db, x ∈ stepAll G db := by
  intro x hx
  simp only [stepAll, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hx))))))

theorem sub_stepAll_JoinCirc {G : Form} {db : List (WRow G)} :
    ∀ x ∈ emitJoinCirc G db, x ∈ stepAll G db := by
  intro x hx
  simp only [stepAll, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hx)))))

theorem sub_stepAll_JoinAtF {G : Form} {db : List (WRow G)} :
    ∀ x ∈ emitJoinAtF G db, x ∈ stepAll G db := by
  intro x hx
  simp only [stepAll, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hx))))

theorem sub_stepAll_JoinOrF {G : Form} {db : List (WRow G)} :
    ∀ x ∈ emitJoinOrF G db, x ∈ stepAll G db := by
  intro x hx
  simp only [stepAll, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inr hx)))

theorem sub_stepAll_JoinAtP {G : Form} {db : List (WRow G)} :
    ∀ x ∈ emitJoinAtP G db, x ∈ stepAll G db := by
  intro x hx
  simp only [stepAll, List.mem_append]
  exact Or.inl (Or.inl (Or.inr hx))

theorem sub_stepAll_JoinOrP {G : Form} {db : List (WRow G)} :
    ∀ x ∈ emitJoinOrP G db, x ∈ stepAll G db := by
  intro x hx
  simp only [stepAll, List.mem_append]
  exact Or.inl (Or.inr hx)

theorem sub_stepAll_JoinCircP {G : Form} {db : List (WRow G)} :
    ∀ x ∈ emitJoinCircP G db, x ∈ stepAll G db := by
  intro x hx
  simp only [stepAll, List.mem_append]
  exact Or.inr hx

/-- Reindexing extraction, irregular side: the stored sublist listing an
arbitrary family's row set, nonempty, with the transfer relation and
pairwise distinctness. -/
theorem reindex_irr {G : Form} {db : List (WRow G)}
    (hnd : (db.map (·.s)).Nodup)
    {n : Nat} {stab th : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form}
    (hmem : ∀ j, (WSeq.irr (stab j) (th j) (rhs j)) ∈ db.map (·.s)) :
    ∃ (a : IrrT G) (t : List (IrrT G)),
      (a :: t) ∈ (irrTs db).sublists ∧
      SameIrr stab th rhs (fun j => ((a :: t).get j).St)
        (fun j => ((a :: t).get j).Th) (fun j => ((a :: t).get j).C) ∧
      (∀ i₁ i₂ : Fin (t.length + 1), i₁ ≠ i₂ →
        ¬ (((a :: t).get i₁).St = ((a :: t).get i₂).St ∧
           ((a :: t).get i₁).Th = ((a :: t).get i₂).Th ∧
           ((a :: t).get i₁).C = ((a :: t).get i₂).C)) := by
  have hlsub : List.Sublist ((irrTs db).filter (fun tr =>
      decide (∃ j, stab j = tr.St ∧ th j = tr.Th ∧ rhs j = tr.C)))
      (irrTs db) := List.filter_sublist
  have hmem_l : ∀ j, ∃ tr ∈ (irrTs db).filter (fun tr =>
      decide (∃ j, stab j = tr.St ∧ th j = tr.Th ∧ rhs j = tr.C)),
      tr.St = stab j ∧ tr.Th = th j ∧ tr.C = rhs j := by
    intro j
    obtain ⟨tr, htr, h1, h2, h3⟩ := irrTs_of_mem (hmem j)
    refine ⟨tr, List.mem_filter.mpr ⟨htr, ?_⟩, h1, h2, h3⟩
    exact decide_eq_true ⟨j, h1.symm, h2.symm, h3.symm⟩
  obtain ⟨a, t, hlat⟩ : ∃ a t, (irrTs db).filter (fun tr =>
      decide (∃ j, stab j = tr.St ∧ th j = tr.Th ∧ rhs j = tr.C)) =
        a :: t := by
    cases hl : (irrTs db).filter (fun tr =>
        decide (∃ j, stab j = tr.St ∧ th j = tr.Th ∧ rhs j = tr.C)) with
    | nil =>
        obtain ⟨tr, htr, -⟩ := hmem_l 0
        rw [hl] at htr
        exact absurd htr List.not_mem_nil
    | cons a t => exact ⟨a, t, rfl⟩
  rw [hlat] at hlsub hmem_l
  have hseqnd : ((a :: t).map IrrT.seq).Nodup :=
    ((hlsub.map IrrT.seq).trans (irrTs_seq_sublist db)).nodup hnd
  refine ⟨a, t, List.mem_sublists.mpr hlsub, ⟨?_, ?_⟩, ?_⟩
  · intro j
    obtain ⟨tr, htr, h1, h2, h3⟩ := hmem_l j
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp htr
    exact ⟨i, by show ((a :: t).get i).St = stab j; rw [hi]; exact h1,
      by show ((a :: t).get i).Th = th j; rw [hi]; exact h2,
      by show ((a :: t).get i).C = rhs j; rw [hi]; exact h3⟩
  · intro i
    have hi : (a :: t).get i ∈ List.filter (fun tr =>
        decide (∃ j, stab j = tr.St ∧ th j = tr.Th ∧ rhs j = tr.C))
        (irrTs db) := by
      rw [hlat]
      exact List.get_mem (a :: t) i
    have hi' := (List.mem_filter.mp hi).2
    rw [decide_eq_true_eq] at hi'
    obtain ⟨j, h1, h2, h3⟩ := hi'
    exact ⟨j, h1.symm, h2.symm, h3.symm⟩
  · rintro i₁ i₂ hne12 ⟨h1, h2, h3⟩
    have hseq : IrrT.seq ((a :: t).get i₁) = IrrT.seq ((a :: t).get i₂) := by
      simp only [IrrT.seq, h1, h2, h3]
    have hlen : ∀ (i : Fin (t.length + 1)),
        i.val < (List.map IrrT.seq (a :: t)).length := by
      intro i
      simpa using i.isLt
    have hmapeq : (List.map IrrT.seq (a :: t))[i₁.val]'(hlen i₁) =
        (List.map IrrT.seq (a :: t))[i₂.val]'(hlen i₂) := by
      simp only [List.getElem_map]
      simpa [List.get_eq_getElem] using hseq
    have hpw := List.pairwise_iff_getElem.mp hseqnd
    have hvne : i₁.val ≠ i₂.val := fun h => hne12 (Fin.ext h)
    rcases Nat.lt_or_ge i₁.val i₂.val with hlt | hge
    · exact hpw _ _ (hlen i₁) (hlen i₂) hlt hmapeq
    · have hlt2 : i₂.val < i₁.val :=
        Nat.lt_of_le_of_ne hge (Ne.symm hvne)
      exact hpw _ _ (hlen i₂) (hlen i₁) hlt2 hmapeq.symm

/-- Reindexing extraction, regular (promise) side. -/
theorem reindex_reg {G : Form} {db : List (WRow G)}
    {k : Nat} {tps : Fin (k + 1) → Tag} {Δs : Fin (k + 1) → List Form}
    {Ds : Fin (k + 1) → Form}
    (hmem : ∀ i, (WSeq.reg (tps i) (Δs i) (Ds i)) ∈ db.map (·.s)) :
    ∃ (b : RegT G) (u : List (RegT G)),
      (b :: u) ∈ (regTs db).sublists ∧
      SameReg tps Δs Ds (fun i => ((b :: u).get i).t)
        (fun i => ((b :: u).get i).Γ) (fun i => ((b :: u).get i).C) := by
  have hlsub : List.Sublist ((regTs db).filter (fun tr =>
      decide (∃ i, tps i = tr.t ∧ Δs i = tr.Γ ∧ Ds i = tr.C)))
      (regTs db) := List.filter_sublist
  have hmem_l : ∀ i, ∃ tr ∈ (regTs db).filter (fun tr =>
      decide (∃ i, tps i = tr.t ∧ Δs i = tr.Γ ∧ Ds i = tr.C)),
      tr.t = tps i ∧ tr.Γ = Δs i ∧ tr.C = Ds i := by
    intro i
    obtain ⟨tr, htr, h1, h2, h3⟩ := regTs_of_mem (hmem i)
    refine ⟨tr, List.mem_filter.mpr ⟨htr, ?_⟩, h1, h2, h3⟩
    exact decide_eq_true ⟨i, h1.symm, h2.symm, h3.symm⟩
  obtain ⟨b, u, hlat⟩ : ∃ b u, (regTs db).filter (fun tr =>
      decide (∃ i, tps i = tr.t ∧ Δs i = tr.Γ ∧ Ds i = tr.C)) =
        b :: u := by
    cases hl : (regTs db).filter (fun tr =>
        decide (∃ i, tps i = tr.t ∧ Δs i = tr.Γ ∧ Ds i = tr.C)) with
    | nil =>
        obtain ⟨tr, htr, -⟩ := hmem_l 0
        rw [hl] at htr
        exact absurd htr List.not_mem_nil
    | cons b u => exact ⟨b, u, rfl⟩
  rw [hlat] at hlsub hmem_l
  refine ⟨b, u, List.mem_sublists.mpr hlsub, ?_, ?_⟩
  · intro i
    obtain ⟨tr, htr, h1, h2, h3⟩ := hmem_l i
    obtain ⟨i', hi'⟩ := List.mem_iff_get.mp htr
    exact ⟨i', by show ((b :: u).get i').t = tps i; rw [hi']; exact h1,
      by show ((b :: u).get i').Γ = Δs i; rw [hi']; exact h2,
      by show ((b :: u).get i').C = Ds i; rw [hi']; exact h3⟩
  · intro i'
    have hi : (b :: u).get i' ∈ List.filter (fun tr =>
        decide (∃ i, tps i = tr.t ∧ Δs i = tr.Γ ∧ Ds i = tr.C))
        (regTs db) := by
      rw [hlat]
      exact List.get_mem (b :: u) i'
    have hi'' := (List.mem_filter.mp hi).2
    rw [decide_eq_true_eq] at hi''
    obtain ⟨i, h1, h2, h3⟩ := hi''
    exact ⟨i, h1.symm, h2.symm, h3.symm⟩

/-! ### Coverage: the leaf and unary clauses -/

section Coverage

variable (G : Form)

theorem cov_axR : ∀ F : Form, F.isPrime → F ∈ sfR G →
    ∃ r ∈ closureDB G,
      WSubsumes (.reg .barren (rm (gAt G) F) F) r.s := by
  intro F hF hg
  have hemit : (⟨.reg .barren (rm (gAt G) F) F,
      .axR F hF hg (CtxEq.refl _)⟩ : WRow G) ∈ emitAxR G := by
    refine List.mem_filterMap.mpr ⟨F, mem_goalPool.mpr hg, ?_⟩
    exact dif_pos ⟨hF, hg⟩
  exact stored_of_emitted (sub_stepAll_AxR _ hemit)

theorem cov_axI : ∀ F : Form, F.isPrime → F ∈ sfR G →
    ∃ r ∈ closureDB G,
      WSubsumes (.irr [] (rm (gAt G) F ++ gImp G ++ gCirc G) F) r.s := by
  intro F hF hg
  have hemit : (⟨.irr [] (rm (gAt G) F ++ gImp G ++ gCirc G) F,
      .axI F hF hg (CtxEq.refl _)⟩ : WRow G) ∈ emitAxI G := by
    refine List.mem_filterMap.mpr ⟨F, mem_goalPool.mpr hg, ?_⟩
    exact dif_pos ⟨hF, hg⟩
  exact stored_of_emitted (sub_stepAll_AxI _ hemit)

/-- `classForce` sees only atom membership. -/
theorem classForce_congr {ats ats' : List Form}
    (h : ∀ p : String, Form.atom p ∈ ats ↔ Form.atom p ∈ ats') :
    ∀ X : Form, classForce ats X = classForce ats' X := by
  intro X
  induction X with
  | atom p =>
      simp only [classForce]
      exact decide_eq_decide.mpr (h p)
  | bot => rfl
  | and A B ihA ihB => simp [classForce, ihA, ihB]
  | or A B ihA ihB => simp [classForce, ihA, ihB]
  | imp A B ihA ihB => simp [classForce, ihA, ihB]
  | circ A ih => simpa [classForce] using ih

theorem cov_axIC : ∀ (F : Form) (ats : List Form), ats ⊆ gAt G →
    classForce ats F = false → Form.circ F ∈ sfR G →
    ∃ r ∈ closureDB G,
      WSubsumes (.irr [] (vacZoneA G ats) (.circ F)) r.s := by
  intro F ats hats hFf hg
  have hcongr : ∀ X : Form,
      classForce ((gAt G).filter (fun x => decide (x ∈ ats))) X =
        classForce ats X := by
    refine classForce_congr (fun p => ?_)
    simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨hats h, h⟩⟩
  have hzone : vacZoneA G ((gAt G).filter (fun x => decide (x ∈ ats))) =
      vacZoneA G ats := by
    simp only [vacZoneA]
    exact List.filter_congr (fun x _ => hcongr x)
  rw [← hzone]
  have hc1 : ∀ x ∈ (gAt G).filter (fun x => decide (x ∈ ats)),
      x ∈ gAt G := fun x hx => (List.mem_filter.mp hx).1
  have hc2 : classForce ((gAt G).filter (fun x => decide (x ∈ ats)))
      F = false := (hcongr F).trans hFf
  have hemit : (⟨.irr []
      (vacZoneA G ((gAt G).filter (fun x => decide (x ∈ ats)))) (.circ F),
      .axIC F _ hc1 hc2 hg (CtxEq.refl _)⟩ : WRow G) ∈ emitAxIC G := by
    refine List.mem_flatMap.mpr ⟨.circ F, mem_goalPool.mpr hg, ?_⟩
    refine List.mem_filterMap.mpr
      ⟨(gAt G).filter (fun x => decide (x ∈ ats)),
       List.mem_sublists.mpr List.filter_sublist, ?_⟩
    exact dif_pos ⟨hc1, hc2, hg⟩
  exact stored_of_emitted (sub_stepAll_AxIC _ hemit)

theorem cov_andR1 : ∀ (t : Tag) (Γ : List Form) (A₁ A₂ : Form),
    (WSeq.reg t Γ A₁) ∈ (closureDB G).map (·.s) → Form.and A₁ A₂ ∈ sfR G →
    ∃ r ∈ closureDB G, WSubsumes (.reg t Γ (.and A₁ A₂)) r.s := by
  intro t Γ A₁ A₂ hmem hg
  obtain ⟨tr, htr, rfl, rfl, rfl⟩ := regTs_of_mem hmem
  have hemit : (⟨.reg tr.t tr.Γ (.and tr.C A₂),
      .andR1 tr.d hg⟩ : WRow G) ∈ emitAndR G (closureDB G) := by
    refine List.mem_flatMap.mpr ⟨tr, htr, ?_⟩
    refine List.mem_filterMap.mpr
      ⟨.and tr.C A₂, mem_goalPool.mpr hg, ?_⟩
    exact dif_pos ⟨rfl, hg⟩
  exact stored_of_emitted (sub_stepAll_AndR _ hemit)

theorem cov_andR2 : ∀ (t : Tag) (Γ : List Form) (A₁ A₂ : Form),
    (WSeq.reg t Γ A₂) ∈ (closureDB G).map (·.s) → Form.and A₁ A₂ ∈ sfR G →
    ∃ r ∈ closureDB G, WSubsumes (.reg t Γ (.and A₁ A₂)) r.s := by
  intro t Γ A₁ A₂ hmem hg
  obtain ⟨tr, htr, rfl, rfl, rfl⟩ := regTs_of_mem hmem
  by_cases hc : A₁ = tr.C ∧ Form.and A₁ tr.C ∈ sfR G
  · have hemit : (⟨.reg tr.t tr.Γ (.and A₁ tr.C),
        .andR1 (hc.1 ▸ tr.d) hc.2⟩ : WRow G) ∈
          emitAndR G (closureDB G) := by
      refine List.mem_flatMap.mpr ⟨tr, htr, ?_⟩
      refine List.mem_filterMap.mpr
        ⟨.and A₁ tr.C, mem_goalPool.mpr hg, ?_⟩
      exact dif_pos hc
    exact stored_of_emitted (sub_stepAll_AndR _ hemit)
  · have hemit : (⟨.reg tr.t tr.Γ (.and A₁ tr.C),
        .andR2 tr.d hg⟩ : WRow G) ∈ emitAndR G (closureDB G) := by
      refine List.mem_flatMap.mpr ⟨tr, htr, ?_⟩
      refine List.mem_filterMap.mpr
        ⟨.and A₁ tr.C, mem_goalPool.mpr hg, ?_⟩
      exact (dif_neg hc).trans (dif_pos ⟨rfl, hg⟩)
    exact stored_of_emitted (sub_stepAll_AndR _ hemit)

theorem cov_impIn : ∀ (t : Tag) (Γ : List Form) (A B : Form),
    (WSeq.reg t Γ B) ∈ (closureDB G).map (·.s) → Clo Γ A →
    Form.imp A B ∈ sfR G →
    ∃ r ∈ closureDB G, WSubsumes (.reg t Γ (.imp A B)) r.s := by
  intro t Γ A B hmem hA hg
  obtain ⟨tr, htr, rfl, rfl, rfl⟩ := regTs_of_mem hmem
  have hemit : (⟨.reg tr.t tr.Γ (.imp A tr.C),
      .impIn tr.d hA hg⟩ : WRow G) ∈ emitImpIn G (closureDB G) := by
    refine List.mem_flatMap.mpr ⟨tr, htr, ?_⟩
    refine List.mem_filterMap.mpr
      ⟨.imp A tr.C, mem_goalPool.mpr hg, ?_⟩
    exact dif_pos ⟨rfl, hA, hg⟩
  exact stored_of_emitted (sub_stepAll_ImpIn _ hemit)

theorem cov_circIn : ∀ (t : Tag) (Γ : List Form) (Z : Form),
    (WSeq.reg t Γ Z) ∈ (closureDB G).map (·.s) →
    (t = .barren ∨ ∃ W, t = .chain W ∧ Covers Γ W Z) →
    Form.circ Z ∈ sfR G →
    ∃ r ∈ closureDB G, WSubsumes (.reg t Γ (.circ Z)) r.s := by
  intro t Γ Z hmem htag hg
  obtain ⟨tr, htr, rfl, rfl, rfl⟩ := regTs_of_mem hmem
  have hemit : (⟨.reg tr.t tr.Γ (.circ tr.C),
      .circIn tr.d htag hg⟩ : WRow G) ∈ emitCircIn G (closureDB G) := by
    refine List.mem_flatMap.mpr ⟨tr, htr, ?_⟩
    refine List.mem_filterMap.mpr
      ⟨.circ tr.C, mem_goalPool.mpr hg, ?_⟩
    exact dif_pos ⟨rfl, htag, hg⟩
  exact stored_of_emitted (sub_stepAll_CircIn _ hemit)

theorem cov_andI1 : ∀ (St Th : List Form) (A₁ A₂ : Form),
    (WSeq.irr St Th A₁) ∈ (closureDB G).map (·.s) → Form.and A₁ A₂ ∈ sfR G →
    ∃ r ∈ closureDB G, WSubsumes (.irr St Th (.and A₁ A₂)) r.s := by
  intro St Th A₁ A₂ hmem hg
  obtain ⟨tr, htr, rfl, rfl, rfl⟩ := irrTs_of_mem hmem
  have hemit : (⟨.irr tr.St tr.Th (.and tr.C A₂),
      .andI1 tr.d hg⟩ : WRow G) ∈ emitAndI G (closureDB G) := by
    refine List.mem_flatMap.mpr ⟨tr, htr, ?_⟩
    refine List.mem_filterMap.mpr
      ⟨.and tr.C A₂, mem_goalPool.mpr hg, ?_⟩
    exact dif_pos ⟨rfl, hg⟩
  exact stored_of_emitted (sub_stepAll_AndI _ hemit)

theorem cov_andI2 : ∀ (St Th : List Form) (A₁ A₂ : Form),
    (WSeq.irr St Th A₂) ∈ (closureDB G).map (·.s) → Form.and A₁ A₂ ∈ sfR G →
    ∃ r ∈ closureDB G, WSubsumes (.irr St Th (.and A₁ A₂)) r.s := by
  intro St Th A₁ A₂ hmem hg
  obtain ⟨tr, htr, rfl, rfl, rfl⟩ := irrTs_of_mem hmem
  by_cases hc : A₁ = tr.C ∧ Form.and A₁ tr.C ∈ sfR G
  · have hemit : (⟨.irr tr.St tr.Th (.and A₁ tr.C),
        .andI1 (hc.1 ▸ tr.d) hc.2⟩ : WRow G) ∈
          emitAndI G (closureDB G) := by
      refine List.mem_flatMap.mpr ⟨tr, htr, ?_⟩
      refine List.mem_filterMap.mpr
        ⟨.and A₁ tr.C, mem_goalPool.mpr hg, ?_⟩
      exact dif_pos hc
    exact stored_of_emitted (sub_stepAll_AndI _ hemit)
  · have hemit : (⟨.irr tr.St tr.Th (.and A₁ tr.C),
        .andI2 tr.d hg⟩ : WRow G) ∈ emitAndI G (closureDB G) := by
      refine List.mem_flatMap.mpr ⟨tr, htr, ?_⟩
      refine List.mem_filterMap.mpr
        ⟨.and A₁ tr.C, mem_goalPool.mpr hg, ?_⟩
      exact (dif_neg hc).trans (dif_pos ⟨rfl, hg⟩)
    exact stored_of_emitted (sub_stepAll_AndI _ hemit)

theorem cov_orI : ∀ (St₁ Th₁ St₂ Th₂ : List Form) (C₁ C₂ : Form),
    (WSeq.irr St₁ Th₁ C₁) ∈ (closureDB G).map (·.s) →
    (WSeq.irr St₂ Th₂ C₂) ∈ (closureDB G).map (·.s) →
    St₁ ⊆ St₂ ++ Th₂ → St₂ ⊆ St₁ ++ Th₁ →
    Form.or C₁ C₂ ∈ sfR G →
    ∃ r ∈ closureDB G,
      WSubsumes (.irr (St₁ ++ St₂) (cap Th₁ Th₂) (.or C₁ C₂)) r.s := by
  intro St₁ Th₁ St₂ Th₂ C₁ C₂ hmem₁ hmem₂ h₁ h₂ hg
  obtain ⟨tr₁, htr₁, rfl, rfl, rfl⟩ := irrTs_of_mem hmem₁
  obtain ⟨tr₂, htr₂, rfl, rfl, rfl⟩ := irrTs_of_mem hmem₂
  have hemit : (⟨.irr (tr₁.St ++ tr₂.St) (cap tr₁.Th tr₂.Th)
      (.or tr₁.C tr₂.C),
      .orI tr₁.d tr₂.d h₁ h₂ hg (CtxEq.refl _) (CtxEq.refl _)⟩ : WRow G) ∈
        emitOrI G (closureDB G) := by
    refine List.mem_flatMap.mpr ⟨tr₁, htr₁, ?_⟩
    refine List.mem_flatMap.mpr ⟨tr₂, htr₂, ?_⟩
    refine List.mem_filterMap.mpr
      ⟨.or tr₁.C tr₂.C, mem_goalPool.mpr hg, ?_⟩
    exact dif_pos ⟨rfl, rfl, h₁, h₂, hg⟩
  exact stored_of_emitted (sub_stepAll_OrI _ hemit)

theorem cov_lift : ∀ (t₂ : Tag) (Γ₂ : List Form) (C : Form),
    (WSeq.reg t₂ Γ₂ C) ∈ (closureDB G).map (·.s) →
    ∃ r ∈ closureDB G, WSubsumes (.irr [] (maxTh G Γ₂) C) r.s := by
  intro t₂ Γ₂ C hmem
  obtain ⟨tr, htr, rfl, rfl, rfl⟩ := regTs_of_mem hmem
  have hemit : (⟨.irr [] (maxTh G tr.Γ) tr.C,
      lift_max tr.d⟩ : WRow G) ∈ emitLift G (closureDB G) :=
    List.mem_map.mpr ⟨tr, htr, rfl⟩
  exact stored_of_emitted (sub_stepAll_Lift _ hemit)

theorem cov_circNotIn : ∀ (t₂ : Tag) (Γ₂ : List Form) (Z : Form),
    (WSeq.reg t₂ Γ₂ Z) ∈ (closureDB G).map (·.s) →
    (t₂ = .barren ∨ ∃ W, t₂ = .chain W ∧ Covers Γ₂ W Z) →
    Form.circ Z ∈ sfR G →
    ∃ r ∈ closureDB G, WSubsumes (.irr [] (maxTh G Γ₂) (.circ Z)) r.s := by
  intro t₂ Γ₂ Z hmem htag hg
  obtain ⟨tr, htr, rfl, rfl, rfl⟩ := regTs_of_mem hmem
  have hemit : (⟨.irr [] (maxTh G tr.Γ) (.circ tr.C),
      circNotIn_max tr.d (fun _ hx => hx) (tagLeB_refl _) htag hg⟩ :
        WRow G) ∈ emitCircNotIn G (closureDB G) := by
    refine List.mem_filterMap.mpr ⟨tr, htr, ?_⟩
    exact dif_pos ⟨htag, hg⟩
  exact stored_of_emitted (sub_stepAll_CircNotIn _ hemit)

theorem cov_impInI : ∀ (St₂ ThLam₂ Lam : List Form) (A B : Form),
    (WSeq.irr St₂ ThLam₂ B) ∈ (closureDB G).map (·.s) →
    Clo (St₂ ++ ThLam₂.filter (fun x => decide (x ∈ Lam))) A →
    Form.imp A B ∈ sfR G →
    ∃ r ∈ closureDB G,
      WSubsumes (.irr (St₂ ++ ThLam₂.filter (fun x => decide (x ∈ Lam)))
        (ThLam₂.filter (fun x => !decide (x ∈ Lam))) (.imp A B)) r.s := by
  intro St₂ ThLam₂ Lam A B hmem hA hg
  obtain ⟨tr, htr, rfl, rfl, rfl⟩ := irrTs_of_mem hmem
  have hpos : tr.Th.filter (fun x =>
      decide (x ∈ tr.Th.filter (fun y => decide (y ∈ Lam)))) =
      tr.Th.filter (fun x => decide (x ∈ Lam)) := by
    refine List.filter_congr (fun x hx => ?_)
    simp [List.mem_filter, hx]
  have hneg : tr.Th.filter (fun x =>
      !decide (x ∈ tr.Th.filter (fun y => decide (y ∈ Lam)))) =
      tr.Th.filter (fun x => !decide (x ∈ Lam)) := by
    refine List.filter_congr (fun x hx => ?_)
    simp [List.mem_filter, hx]
  rw [← hpos, ← hneg]
  have hA' : Clo (tr.St ++ tr.Th.filter (fun x =>
      decide (x ∈ tr.Th.filter (fun y => decide (y ∈ Lam))))) A := by
    rw [hpos]; exact hA
  have hemit : (⟨.irr (tr.St ++ tr.Th.filter (fun x =>
      decide (x ∈ tr.Th.filter (fun y => decide (y ∈ Lam)))))
      (tr.Th.filter (fun x =>
        !decide (x ∈ tr.Th.filter (fun y => decide (y ∈ Lam)))))
      (.imp A tr.C),
      .impInI tr.d
        (filter_split_pre tr.Th (tr.Th.filter (fun y => decide (y ∈ Lam))))
        (filter_split_disj tr.Th (tr.Th.filter (fun y => decide (y ∈ Lam))))
        hA' hg (CtxEq.refl _) (CtxEq.refl _)⟩ : WRow G) ∈
        emitImpInI G (closureDB G) := by
    refine List.mem_flatMap.mpr ⟨tr, htr, ?_⟩
    refine List.mem_flatMap.mpr
      ⟨tr.Th.filter (fun y => decide (y ∈ Lam)),
       List.mem_sublists.mpr List.filter_sublist, ?_⟩
    refine List.mem_filterMap.mpr
      ⟨.imp A tr.C, mem_goalPool.mpr hg, ?_⟩
    exact dif_pos ⟨rfl, hA', hg⟩
  exact stored_of_emitted (sub_stepAll_ImpInI _ hemit)

end Coverage

end FRJ.Gbu.W
