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

end FRJ.Gbu.W
