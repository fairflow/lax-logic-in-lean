/-
# `LaxLogic.QLL.Complete` — the canonical model

Fairtlough–Mendler's completeness argument (*Propositional Lax Logic* §4),
carried to QLL.  Worlds are theories `(val, fal, mfal)`: validated, falsified,
and — one set per modality — falsified at every reachable state.  A theory is
**consistent** when for all finite `Ds ⊆ fal`, `TA ⊆ mfal ∀`, `TE ⊆ mfal ∃`,
not all empty,

    val ⊬ ⋁Ds ∨ ◯∀(⋁TA) ∨ ◯∃(⋁TE)

with the convention that an *absent* disjunct is dropped rather than read as
`⊥`.  The guard matters twice: without it `(all formulas, ∅, ∅, ∅)` would not
be consistent, and that theory is the single fallible world of the canonical
model; and reading an absent modal disjunct as `◯∀⊥` would make every theory
containing `◯∀⊥` inconsistent, though `◯∀⊥` is satisfiable.

**Two `mfal` sets, because there are two modalities.**  They are independent —
`◯E` never mixes them — so the construction is written once, indexed by `q`.
-/
import LaxLogic.QLL.Prov
import Mathlib.Order.Zorn

namespace LaxLogic.QLL

/-! ## Derivability from a set of hypotheses -/

/-- `Γ ⊩q A`: some finite selection from `Γ` proves `A`. -/
def SetPrv (Γ : Set Form) (A : Form) : Prop :=
  ∃ L : List Form, (∀ B ∈ L, B ∈ Γ) ∧ Prv L A

@[inherit_doc] infix:55 " ⊩q " => SetPrv

namespace SetPrv

theorem of_mem {Γ : Set Form} {A : Form} (h : A ∈ Γ) : Γ ⊩q A :=
  ⟨[A], by simpa using h, .var (List.mem_cons_self ..)⟩

theorem mono {Γ Γ' : Set Form} {A : Form} (hs : Γ ⊆ Γ') (h : Γ ⊩q A) : Γ' ⊩q A := by
  obtain ⟨L, hL, hp⟩ := h; exact ⟨L, fun B hB => hs (hL B hB), hp⟩

theorem map {Γ : Set Form} {A B : Form} (f : ∀ L, Prv L A → Prv L B) (h : Γ ⊩q A) :
    Γ ⊩q B := by
  obtain ⟨L, hL, hp⟩ := h; exact ⟨L, hL, f L hp⟩

theorem map₂ {Γ : Set Form} {A B C : Form}
    (f : ∀ L, Prv L A → Prv L B → Prv L C) (h₁ : Γ ⊩q A) (h₂ : Γ ⊩q B) : Γ ⊩q C := by
  obtain ⟨L₁, hL₁, hp₁⟩ := h₁
  obtain ⟨L₂, hL₂, hp₂⟩ := h₂
  refine ⟨L₁ ++ L₂, fun B hB => ?_, f _ (hp₁.weaken (fun _ h => by simp [h]))
    (hp₂.weaken (fun _ h => by simp [h]))⟩
  rcases List.mem_append.mp hB with h | h
  · exact hL₁ B h
  · exact hL₂ B h

/-- The deduction theorem. -/
theorem deduct {Γ : Set Form} {A B : Form} (h : insert A Γ ⊩q B) : Γ ⊩q .imp A B := by
  obtain ⟨L, hL, hp⟩ := h
  refine ⟨L.filter (fun C => decide (C ≠ A)), ?_, .impI (hp.weaken ?_)⟩
  · intro C hC
    have h1 := (List.mem_filter.mp hC).2
    have h2 := (List.mem_filter.mp hC).1
    rcases hL C h2 with h | h
    · exact absurd h (by simpa using h1)
    · exact h
  · intro C hC
    by_cases hCA : C = A
    · exact hCA ▸ List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hC, by simpa using hCA⟩)

theorem cut {Γ : Set Form} {A B : Form} (h₁ : Γ ⊩q A) (h₂ : insert A Γ ⊩q B) : Γ ⊩q B :=
  map₂ (fun _ p q => .impE q p) h₁ (deduct h₂)

theorem map₃ {Γ : Set Form} {A B C K : Form}
    (f : ∀ L, Prv L A → Prv L B → Prv L C → Prv L K)
    (h₁ : Γ ⊩q A) (h₂ : Γ ⊩q B) (h₃ : Γ ⊩q C) : Γ ⊩q K := by
  obtain ⟨L₁, hL₁, p₁⟩ := h₁
  obtain ⟨L₂, hL₂, p₂⟩ := h₂
  obtain ⟨L₃, hL₃, p₃⟩ := h₃
  refine ⟨L₁ ++ L₂ ++ L₃, ?_, f _ (p₁.weaken ?_) (p₂.weaken ?_) (p₃.weaken ?_)⟩
  · intro X hX
    rcases List.mem_append.mp hX with h | h
    · rcases List.mem_append.mp h with h | h
      · exact hL₁ X h
      · exact hL₂ X h
    · exact hL₃ X h
  · intro X h; simp [h]
  · intro X h; simp [h]
  · intro X h; simp [h]

theorem orE' {Γ : Set Form} {A B K : Form}
    (h : Γ ⊩q .or A B) (h₁ : insert A Γ ⊩q K) (h₂ : insert B Γ ⊩q K) : Γ ⊩q K :=
  map₃ (fun _ p q r => .orE p (.impE (q.weaken (by intro _ h; simp [h]))
      (.var (List.mem_cons_self ..)))
    (.impE (r.weaken (by intro _ h; simp [h])) (.var (List.mem_cons_self ..))))
    h (deduct h₁) (deduct h₂)

end SetPrv

/-! ## Disjunctions -/

/-- `⋁` of a list, with `⊥` for the empty one and no spurious `∨ ⊥`. -/
def bigOr : List Form → Form
  | []      => .bot
  | [A]     => A
  | A :: As => .or A (bigOr As)

theorem bigOr_intro : ∀ (As : List Form) {Γ : List Form} {A : Form},
    A ∈ As → Prv Γ A → Prv Γ (bigOr As)
  | [],           _, _, h, _ => absurd h (by simp)
  | [A'],         _, A, h, hp => by
      rcases List.mem_singleton.mp h with rfl; exact hp
  | A' :: B :: As, _, A, h, hp => by
      rcases List.mem_cons.mp h with rfl | h
      · exact .orI₁ hp
      · exact .orI₂ (bigOr_intro (B :: As) h hp)

theorem bigOr_elim {K : Form} : ∀ (As : List Form) (Γ : List Form),
    Prv Γ (bigOr As) → (∀ A ∈ As, Prv (A :: Γ) K) → Prv Γ K
  | [],            _, hp, _ => .botE hp
  | [A],           _, hp, f => .impE (.impI (f A (List.mem_cons_self ..))) hp
  | A :: B :: As,  Γ, hp, f =>
      .orE hp (f A (List.mem_cons_self ..))
        (bigOr_elim (B :: As) (bigOr (B :: As) :: Γ)
          (.var (List.mem_cons_self ..))
          (fun C hC => (f C (List.mem_cons_of_mem _ hC)).weaken (by
            intro D hD
            rcases List.mem_cons.mp hD with rfl | hD
            · exact List.mem_cons_self ..
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hD))))

/-- The modal disjunct of a consistency formula: absent when the list is. -/
def modalPart (q : Q) : List Form → List Form
  | [] => []
  | Ts => [.circ q (bigOr Ts)]

/-- `⋁Ds ∨ ◯∀(⋁TA) ∨ ◯∃(⋁TE)`, absent disjuncts dropped. -/
def disjOf (Ds TA TE : List Form) : Form :=
  bigOr (Ds ++ modalPart .all TA ++ modalPart .ex TE)

theorem mem_disj_of_mem_fal {Ds TA TE : List Form} {D : Form} (h : D ∈ Ds) :
    D ∈ Ds ++ modalPart .all TA ++ modalPart .ex TE := by
  simp [h]

theorem mem_disj_of_modal {Ds TA TE : List Form} {q : Q} {Ts : List Form}
    (hq : (q = .all ∧ Ts = TA) ∨ (q = .ex ∧ Ts = TE)) (hne : Ts ≠ []) :
    .circ q (bigOr Ts) ∈ Ds ++ modalPart .all TA ++ modalPart .ex TE := by
  rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · cases hTs : Ts with
      | nil => exact absurd hTs hne
      | cons X Xs => subst hTs; simp [modalPart]

/-! ## Reasoning with `disjOf` -/

theorem mem_modalPart {q : Q} {Ts : List Form} {A : Form} :
    A ∈ modalPart q Ts ↔ (Ts ≠ [] ∧ A = .circ q (bigOr Ts)) := by
  cases Ts with
  | nil => simp [modalPart]
  | cons X Xs => simp [modalPart]

theorem mem_disjList {Ds TA TE : List Form} {A : Form}
    (h : A ∈ Ds ++ modalPart .all TA ++ modalPart .ex TE) :
    A ∈ Ds ∨ (TA ≠ [] ∧ A = .circ .all (bigOr TA))
        ∨ (TE ≠ [] ∧ A = .circ .ex (bigOr TE)) := by
  rcases List.mem_append.mp h with h | h
  · rcases List.mem_append.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (mem_modalPart.mp h))
  · exact Or.inr (Or.inr (mem_modalPart.mp h))

/-- Case analysis on a derived consistency formula. -/
theorem disj_elim {Γ : List Form} {K : Form} {Ds TA TE : List Form}
    (h : Prv Γ (disjOf Ds TA TE))
    (hD : ∀ D ∈ Ds, Prv (D :: Γ) K)
    (hA : TA ≠ [] → Prv (.circ .all (bigOr TA) :: Γ) K)
    (hE : TE ≠ [] → Prv (.circ .ex (bigOr TE) :: Γ) K) : Prv Γ K :=
  bigOr_elim _ Γ h (fun X hX => by
    rcases mem_disjList hX with hx | ⟨hne, rfl⟩ | ⟨hne, rfl⟩
    · exact hD X hx
    · exact hA hne
    · exact hE hne)

/-- A disjunct of the falsified part introduces the whole. -/
theorem disj_introD {Γ : List Form} {Ds TA TE : List Form} {D : Form}
    (hD : D ∈ Ds) (h : Prv Γ D) : Prv Γ (disjOf Ds TA TE) :=
  bigOr_intro _ (mem_disj_of_mem_fal hD) h

/-- A modal disjunct introduces the whole. -/
theorem disj_introM {Γ : List Form} {Ds TA TE : List Form} {q : Q} {Ts : List Form}
    (hq : (q = .all ∧ Ts = TA) ∨ (q = .ex ∧ Ts = TE)) (hne : Ts ≠ [])
    (h : Prv Γ (.circ q (bigOr Ts))) : Prv Γ (disjOf Ds TA TE) :=
  bigOr_intro _ (mem_disj_of_modal hq hne) h

/-- `◯q` is monotone in the list under it. -/
theorem lax_mono {Γ : List Form} {q : Q} {Ts Ts' : List Form}
    (hs : ∀ A ∈ Ts, A ∈ Ts') (h : Prv Γ (.circ q (bigOr Ts))) :
    Prv Γ (.circ q (bigOr Ts')) :=
  .circE h (bigOr_elim Ts (bigOr Ts :: Γ) (.var (List.mem_cons_self ..))
    (fun A hA => .circI (bigOr_intro _ (hs A hA) (.var (List.mem_cons_self ..)))))

/-- Enlarging any of the three lists. -/
theorem disj_mono {Γ : List Form} {Ds TA TE Ds' TA' TE' : List Form}
    (hD : ∀ A ∈ Ds, A ∈ Ds') (hA : ∀ A ∈ TA, A ∈ TA') (hE : ∀ A ∈ TE, A ∈ TE')
    (h : Prv Γ (disjOf Ds TA TE)) : Prv Γ (disjOf Ds' TA' TE') := by
  refine disj_elim h (fun D hd => disj_introD (hD D hd) (.var (List.mem_cons_self ..)))
    (fun hne => ?_) (fun hne => ?_)
  · have hne' : TA' ≠ [] := by
      cases hTA : TA with
      | nil => exact absurd hTA hne
      | cons X Xs =>
          intro hnil
          exact absurd (hA X (by simp [hTA])) (by simp [hnil])
    exact disj_introM (Or.inl ⟨rfl, rfl⟩) hne'
      (lax_mono hA (.var (List.mem_cons_self ..)))
  · have hne' : TE' ≠ [] := by
      cases hTE : TE with
      | nil => exact absurd hTE hne
      | cons X Xs =>
          intro hnil
          exact absurd (hE X (by simp [hTE])) (by simp [hnil])
    exact disj_introM (Or.inr ⟨rfl, rfl⟩) hne'
      (lax_mono hE (.var (List.mem_cons_self ..)))

namespace SetPrv

theorem bigOr_elim' {K : Form} : ∀ (As : List Form) (Γ : Set Form),
    Γ ⊩q bigOr As → (∀ A ∈ As, insert A Γ ⊩q K) → Γ ⊩q K
  | [],           _, h, _ => h.map (fun _ p => .botE p)
  | [A],          _, h, f => cut h (f A (by simp))
  | A :: B :: As, Γ, h, f =>
      orE' h (f A (by simp))
        (bigOr_elim' (B :: As) (insert (bigOr (B :: As)) Γ)
          (of_mem (Set.mem_insert ..))
          (fun C hC => (f C (by simp [hC])).mono
            (by intro X hX; rcases hX with rfl | hX
                · exact Set.mem_insert ..
                · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ hX))))

theorem bigOr_collapse {X : Form} : ∀ (Ds : List Form) (Γ : Set Form),
    (∀ A ∈ Ds, A = X) → Γ ⊩q bigOr Ds → Γ ⊩q X := by
  intro Ds Γ f h
  refine bigOr_elim' Ds Γ h (fun A hA => ?_)
  rw [← f A hA]
  exact of_mem (Set.mem_insert ..)

theorem lax_bind {Γ : Set Form} {q : Q} {A B : Form}
    (h₁ : Γ ⊩q .circ q A) (h₂ : Γ ⊩q .imp A (.circ q B)) : Γ ⊩q .circ q B :=
  map₂ (fun _ p₁ p₂ => .circE p₁ (.impE (p₂.weaken (by intro _ h; simp [h]))
    (.var (List.mem_cons_self ..)))) h₁ h₂

theorem lax_collapse {Γ : Set Form} {q : Q} {X : Form} (Ts : List Form)
    (hT : ∀ A ∈ Ts, A = X) (h : Γ ⊩q .circ q (bigOr Ts)) : Γ ⊩q .circ q X :=
  h.map (fun L p => .circE p (bigOr_elim Ts (bigOr Ts :: L)
    (.var (List.mem_cons_self ..))
    (fun A hA => .circI (by rw [← hT A hA]; exact .var (List.mem_cons_self ..)))))

end SetPrv

theorem disjOf_fal (Ds : List Form) : disjOf Ds [] [] = bigOr Ds := by
  simp [disjOf, modalPart]

theorem disjOf_all {Ts : List Form} (h : Ts ≠ []) :
    disjOf [] Ts [] = .circ .all (bigOr Ts) := by
  cases Ts with
  | nil => exact absurd rfl h
  | cons X Xs => simp [disjOf, modalPart, bigOr]

theorem disjOf_ex {Ts : List Form} (h : Ts ≠ []) :
    disjOf [] [] Ts = .circ .ex (bigOr Ts) := by
  cases Ts with
  | nil => exact absurd rfl h
  | cons X Xs => simp [disjOf, modalPart, bigOr]

/-- `disj_elim`, over a set context. -/
theorem SetPrv.disj_elim {Γ : Set Form} {K : Form} {Ds TA TE : List Form}
    (h : Γ ⊩q disjOf Ds TA TE)
    (hD : ∀ D ∈ Ds, insert D Γ ⊩q K)
    (hA : TA ≠ [] → insert (.circ .all (bigOr TA)) Γ ⊩q K)
    (hE : TE ≠ [] → insert (.circ .ex (bigOr TE)) Γ ⊩q K) : Γ ⊩q K :=
  SetPrv.bigOr_elim' _ Γ h (fun X hX => by
    rcases mem_disjList hX with hx | ⟨hne, rfl⟩ | ⟨hne, rfl⟩
    · exact hD X hx
    · exact hA hne
    · exact hE hne)

/-! ## Theories -/

/-- Validated / falsified / falsified at every `q`-reachable state. -/
@[ext]
structure Theory where
  val : Set Form
  fal : Set Form
  mfal : Q → Set Form

instance : Preorder Theory where
  le T T' := T.val ⊆ T'.val ∧ T.fal ⊆ T'.fal ∧ ∀ q, T.mfal q ⊆ T'.mfal q
  le_refl _ := ⟨subset_rfl, subset_rfl, fun _ => subset_rfl⟩
  le_trans _ _ _ h h' := ⟨h.1.trans h'.1, h.2.1.trans h'.2.1,
    fun q => (h.2.2 q).trans (h'.2.2 q)⟩

theorem Theory.le_def {T T' : Theory} :
    T ≤ T' ↔ T.val ⊆ T'.val ∧ T.fal ⊆ T'.fal ∧ ∀ q, T.mfal q ⊆ T'.mfal q := Iff.rfl

/-- No nonempty finite choice from the falsified parts is derivable. -/
def Consistent (T : Theory) : Prop :=
  ∀ Ds TA TE : List Form,
    (∀ A ∈ Ds, A ∈ T.fal) → (∀ A ∈ TA, A ∈ T.mfal .all) → (∀ A ∈ TE, A ∈ T.mfal .ex) →
    Ds ++ TA ++ TE ≠ [] → ¬ (T.val ⊩q disjOf Ds TA TE)

/-- Consistent, and maximal among consistent extensions. -/
def MaxConsistent (T : Theory) : Prop :=
  Consistent T ∧ ∀ T', Consistent T' → T ≤ T' → T' ≤ T

/-- Every formula is decided. -/
def Total (T : Theory) : Prop := ∀ A : Form, A ∈ T.val ∨ A ∈ T.fal

/-- What the canonical model's states need.  *Not* maximality: every property
below follows from consistency and totality alone, and that matters, because
the first-order construction produces a total theory directly and cannot
produce a maximal one — saturation has to interleave with deciding formulas,
and Zorn cannot interleave. -/
structure Good (T : Theory) : Prop where
  /-- No falsified disjunction is derivable. -/
  consistent : Consistent T
  /-- Every formula is decided. -/
  total : Total T

private theorem chain_cover {c : Set Theory} (hc : IsChain (· ≤ ·) c)
    {y : Theory} (hy : y ∈ c) (sel : Theory → Set Form)
    (hsel : ∀ {T T' : Theory}, T ≤ T' → sel T ⊆ sel T')
    (L : List Form) (hL : ∀ A ∈ L, ∃ T ∈ c, A ∈ sel T) :
    ∃ T ∈ c, ∀ A ∈ L, A ∈ sel T := by
  induction L with
  | nil => exact ⟨y, hy, by simp⟩
  | cons B L ih =>
      obtain ⟨T₁, hT₁, hmem⟩ := hL B (List.mem_cons_self ..)
      obtain ⟨T₂, hT₂, hall⟩ := ih (fun A hA => hL A (List.mem_cons_of_mem _ hA))
      rcases eq_or_ne T₁ T₂ with rfl | hne
      · refine ⟨T₁, hT₁, fun A hA => ?_⟩
        rcases List.mem_cons.mp hA with rfl | hA
        exacts [hmem, hall A hA]
      rcases hc hT₁ hT₂ hne with hle | hle
      · refine ⟨T₂, hT₂, fun A hA => ?_⟩
        rcases List.mem_cons.mp hA with rfl | hA
        exacts [hsel hle hmem, hall A hA]
      · refine ⟨T₁, hT₁, fun A hA => ?_⟩
        rcases List.mem_cons.mp hA with rfl | hA
        exacts [hmem, hsel hle (hall A hA)]

private theorem chain_ub₂ {c : Set Theory} (hc : IsChain (· ≤ ·) c)
    {T₁ T₂ : Theory} (h₁ : T₁ ∈ c) (h₂ : T₂ ∈ c) : ∃ T ∈ c, T₁ ≤ T ∧ T₂ ≤ T := by
  rcases eq_or_ne T₁ T₂ with rfl | hne
  · exact ⟨T₁, h₁, le_refl _, le_refl _⟩
  rcases hc h₁ h₂ hne with h | h
  · exact ⟨T₂, h₂, h, le_refl _⟩
  · exact ⟨T₁, h₁, le_refl _, h⟩

/-- **Lindenbaum**: every consistent theory extends to a maximally consistent
one.  Zorn; consistency has finite character. -/
theorem exists_maxConsistent_extension {T₀ : Theory} (h₀ : Consistent T₀) :
    ∃ T, T₀ ≤ T ∧ MaxConsistent T := by
  have hchain : ∀ c ⊆ {T : Theory | Consistent T}, IsChain (· ≤ ·) c →
      ∀ y ∈ c, ∃ ub ∈ {T : Theory | Consistent T}, ∀ z ∈ c, z ≤ ub := by
    intro c hcS hc y hy
    refine ⟨⟨⋃ T ∈ c, T.val, ⋃ T ∈ c, T.fal, fun q => ⋃ T ∈ c, T.mfal q⟩, ?_, ?_⟩
    · intro Ds TA TE hDs hTA hTE hne hder
      obtain ⟨L, hL, hp⟩ := hder
      obtain ⟨Ta, hTa, hLa⟩ := chain_cover hc hy Theory.val (fun h => h.1) L
        (fun A hA => by simpa using hL A hA)
      obtain ⟨Tb, hTb, hLb⟩ := chain_cover hc hy Theory.fal (fun h => h.2.1) Ds
        (fun A hA => by simpa using hDs A hA)
      obtain ⟨Tc, hTc, hLc⟩ := chain_cover hc hy (fun T => T.mfal .all)
        (fun h => h.2.2 .all) TA (fun A hA => by simpa using hTA A hA)
      obtain ⟨Td, hTd, hLd⟩ := chain_cover hc hy (fun T => T.mfal .ex)
        (fun h => h.2.2 .ex) TE (fun A hA => by simpa using hTE A hA)
      obtain ⟨Tab, hTab, hab₁, hab₂⟩ := chain_ub₂ hc hTa hTb
      obtain ⟨Tcd, hTcd, hcd₁, hcd₂⟩ := chain_ub₂ hc hTc hTd
      obtain ⟨T, hT, h₁, h₂⟩ := chain_ub₂ hc hTab hTcd
      exact hcS hT Ds TA TE
        (fun A hA => h₁.2.1 (hab₂.2.1 (hLb A hA)))
        (fun A hA => h₂.2.2 .all (hcd₁.2.2 .all (hLc A hA)))
        (fun A hA => h₂.2.2 .ex (hcd₂.2.2 .ex (hLd A hA)))
        hne
        ⟨L, fun A hA => h₁.1 (hab₁.1 (hLa A hA)), hp⟩
    · intro T hT
      exact ⟨Set.subset_biUnion_of_mem hT, Set.subset_biUnion_of_mem hT,
        fun q => Set.subset_biUnion_of_mem (u := fun T => T.mfal q) hT⟩
  obtain ⟨m, hm₀, hmem, hmax⟩ :=
    zorn_le_nonempty₀ {T : Theory | Consistent T} hchain T₀ h₀
  exact ⟨m, hm₀, hmem, fun T' hT' hle => hmax hT' hle⟩

theorem SetPrv.disj_mono {Γ : Set Form} {Ds TA TE Ds' TA' TE' : List Form}
    (hD : ∀ A ∈ Ds, A ∈ Ds') (hA : ∀ A ∈ TA, A ∈ TA') (hE : ∀ A ∈ TE, A ∈ TE')
    (h : Γ ⊩q disjOf Ds TA TE) : Γ ⊩q disjOf Ds' TA' TE' :=
  h.map (fun _ p => LaxLogic.QLL.disj_mono hD hA hE p)

/-! ## Properties of maximally consistent theories -/

theorem not_consistent_iff {T : Theory} :
    ¬ Consistent T ↔ ∃ Ds TA TE : List Form,
      (∀ A ∈ Ds, A ∈ T.fal) ∧ (∀ A ∈ TA, A ∈ T.mfal .all) ∧
      (∀ A ∈ TE, A ∈ T.mfal .ex) ∧ Ds ++ TA ++ TE ≠ [] ∧ T.val ⊩q disjOf Ds TA TE := by
  unfold Consistent
  push_neg
  rfl

/-! ### Maximality is one way to be total

Zorn settles the propositional case on its own.  The first-order case cannot
use it — see `Good` — so what maximality is really being used for is isolated
here, and everything downstream depends only on the isolated property. -/

theorem MaxConsistent.total {T : Theory} (hM : MaxConsistent T) : Total T := by
  intro A
  by_contra hcon
  push_neg at hcon
  obtain ⟨hv, hf⟩ := hcon
  have h1 : ¬ Consistent ⟨T.val, insert A T.fal, T.mfal⟩ := fun hc =>
    hf ((hM.2 _ hc ⟨subset_rfl, Set.subset_insert _ _, fun _ => subset_rfl⟩).2.1
      (Set.mem_insert ..))
  have h2 : ¬ Consistent ⟨insert A T.val, T.fal, T.mfal⟩ := fun hc =>
    hv ((hM.2 _ hc ⟨Set.subset_insert _ _, subset_rfl, fun _ => subset_rfl⟩).1
      (Set.mem_insert ..))
  obtain ⟨Ds, TA, TE, hD, hA, hE, hne, hder⟩ := not_consistent_iff.mp h1
  obtain ⟨Ds₂, TA₂, TE₂, hD₂, hA₂, hE₂, hne₂, hder₂⟩ := not_consistent_iff.mp h2
  obtain ⟨Ds', hDs'⟩ : ∃ X, X = Ds.filter (fun D => decide ¬(D = A)) := ⟨_, rfl⟩
  have hDs'mem : ∀ D ∈ Ds', D ∈ T.fal := by
    intro D hDmem
    rw [hDs'] at hDmem
    have h := List.mem_filter.mp hDmem
    rcases hD D h.1 with hx | hx
    · exact absurd hx (by simpa using h.2)
    · exact hx
  refine hM.1 (Ds' ++ Ds₂) (TA ++ TA₂) (TE ++ TE₂)
    (fun D h => by rcases List.mem_append.mp h with h | h
                   · exact hDs'mem D h
                   · exact hD₂ D h)
    (fun D h => by rcases List.mem_append.mp h with h | h
                   · exact hA D h
                   · exact hA₂ D h)
    (fun D h => by rcases List.mem_append.mp h with h | h
                   · exact hE D h
                   · exact hE₂ D h)
    (by intro hnil
        simp only [List.append_assoc, List.append_eq_nil_iff] at hnil
        exact hne₂ (by simp [hnil.2.1, hnil.2.2.2]))
    ?_
  refine SetPrv.disj_elim hder ?_ ?_ ?_
  · intro D hDmem
    by_cases hDA : D = A
    · subst hDA
      exact SetPrv.disj_mono (fun X h => List.mem_append.mpr (Or.inr h))
        (fun X h => List.mem_append.mpr (Or.inr h))
        (fun X h => List.mem_append.mpr (Or.inr h)) hder₂
    · refine (SetPrv.of_mem (Set.mem_insert ..)).map (fun _ p => disj_introD ?_ p)
      refine List.mem_append.mpr (Or.inl ?_)
      rw [hDs']
      exact List.mem_filter.mpr ⟨hDmem, by simpa using hDA⟩
  · intro hneA
    exact (SetPrv.of_mem (Set.mem_insert ..)).map (fun _ p =>
      disj_introM (Or.inl ⟨rfl, rfl⟩)
        (by intro hnil; exact hneA (by simpa using (List.append_eq_nil_iff.mp hnil).1))
        (lax_mono (fun X h => List.mem_append.mpr (Or.inl h)) p))
  · intro hneE
    exact (SetPrv.of_mem (Set.mem_insert ..)).map (fun _ p =>
      disj_introM (Or.inr ⟨rfl, rfl⟩)
        (by intro hnil; exact hneE (by simpa using (List.append_eq_nil_iff.mp hnil).1))
        (lax_mono (fun X h => List.mem_append.mpr (Or.inl h)) p))

theorem MaxConsistent.good {T : Theory} (hM : MaxConsistent T) : Good T :=
  ⟨hM.1, hM.total⟩

/-- The interface the canonical model uses.  Zorn is one implementation; the
first-order construction is another, and the truth lemma does not care which. -/
theorem exists_good_extension {T₀ : Theory} (h : Consistent T₀) :
    ∃ T, T₀ ≤ T ∧ Good T := by
  obtain ⟨T, hle, hM⟩ := exists_maxConsistent_extension h
  exact ⟨T, hle, hM.good⟩

namespace Good

variable {T : Theory}

/-- A falsified formula is not derivable. -/
theorem not_fal_deriv (hG : Good T) {A : Form} (hA : A ∈ T.fal)
    (hd : T.val ⊩q A) : False := by
  refine hG.1 [A] [] [] (by simpa using hA) (by simp) (by simp) (by simp) ?_
  rw [disjOf_fal]
  exact hd

/-- `val` is deductively closed — from totality, not from maximality. -/
theorem ded_closed (hG : Good T) {A : Form} (hd : T.val ⊩q A) : A ∈ T.val :=
  (hG.2 A).resolve_right (fun hf => hG.not_fal_deriv hf hd)

theorem mem_val_or_mem_fal (hG : Good T) (A : Form) : A ∈ T.val ∨ A ∈ T.fal := hG.2 A

theorem not_mem_fal_of_mem_val (hG : Good T) {A : Form} (h : A ∈ T.val) :
    A ∉ T.fal := fun hf => hG.not_fal_deriv hf (SetPrv.of_mem h)

/-- Primeness. -/
theorem or_mem (hG : Good T) {A B : Form} (h : Form.or A B ∈ T.val) :
    A ∈ T.val ∨ B ∈ T.val := by
  by_contra hcon
  push_neg at hcon
  have hA : A ∈ T.fal := (hG.2 A).resolve_left hcon.1
  have hB : B ∈ T.fal := (hG.2 B).resolve_left hcon.2
  have hmem : ∀ X ∈ [A, B], X ∈ T.fal := by
    intro X hX
    rcases List.mem_cons.mp hX with rfl | hX
    · exact hA
    · rcases List.mem_singleton.mp hX with rfl
      exact hB
  refine hG.1 [A, B] [] [] hmem (by simp) (by simp) (by simp) ?_
  rw [disjOf_fal]
  exact SetPrv.of_mem h

/-- Implication decomposes. -/
theorem imp_mem (hG : Good T) {A B : Form} (h : Form.imp A B ∈ T.val) :
    A ∈ T.fal ∨ B ∈ T.val := by
  by_contra hcon
  push_neg at hcon
  have hA : A ∈ T.val := (hG.2 A).resolve_right hcon.1
  exact hcon.2 (hG.ded_closed (SetPrv.map₂ (fun _ p q => .impE p q)
    (SetPrv.of_mem h) (SetPrv.of_mem hA)))

/-- A falsified disjunction falsifies both disjuncts. -/
theorem fal_or (hG : Good T) {A B : Form} (h : Form.or A B ∈ T.fal) :
    A ∈ T.fal ∧ B ∈ T.fal := by
  constructor
  · rcases hG.2 A with hA | hA
    · exact absurd (hG.not_fal_deriv h ((SetPrv.of_mem hA).map (fun _ p => .orI₁ p))) (by simp)
    · exact hA
  · rcases hG.2 B with hB | hB
    · exact absurd (hG.not_fal_deriv h ((SetPrv.of_mem hB).map (fun _ p => .orI₂ p))) (by simp)
    · exact hB

/-- A falsified conjunction falsifies one conjunct. -/
theorem fal_and (hG : Good T) {A B : Form} (h : Form.and A B ∈ T.fal) :
    A ∈ T.fal ∨ B ∈ T.fal := by
  by_contra hcon
  push_neg at hcon
  have hA : A ∈ T.val := (hG.2 A).resolve_right hcon.1
  have hB : B ∈ T.val := (hG.2 B).resolve_right hcon.2
  exact hG.not_fal_deriv h
    (SetPrv.map₂ (fun _ p q => .andI p q) (SetPrv.of_mem hA) (SetPrv.of_mem hB))

/-- Modally falsified formulas are falsified. -/
theorem mfal_sub_fal (hG : Good T) {q : Q} {A : Form} (h : A ∈ T.mfal q) :
    A ∈ T.fal := by
  rcases hG.2 A with hv | hf
  · exfalso
    have hlax : T.val ⊩q Form.circ q A := (SetPrv.of_mem hv).map (fun _ p => .circI p)
    cases q
    · refine hG.1 [] [A] [] (by simp) (by simpa using h) (by simp) (by simp) ?_
      rw [disjOf_all (by simp)]
      exact hlax
    · refine hG.1 [] [] [A] (by simp) (by simp) (by simpa using h) (by simp) ?_
      rw [disjOf_ex (by simp)]
      exact hlax
  · exact hf

/-- A falsified existential falsifies every instance. -/
theorem fal_exists (hG : Good T) {A : Form} {t : Tm} (ht : Tm.lcAt 0 t)
    (h : Form.exists_ A ∈ T.fal) : A.openAt 0 t ∈ T.fal := by
  rcases hG.2 (A.openAt 0 t) with hv | hf
  · exact absurd (hG.not_fal_deriv h
      ((SetPrv.of_mem hv).map (fun _ p => .exI t ht p))) (by simp)
  · exact hf

/-- Every instance of a validated universal is validated. -/
theorem all_mem (hG : Good T) {A : Form} {t : Tm} (ht : Tm.lcAt 0 t)
    (h : Form.forall_ A ∈ T.val) : A.openAt 0 t ∈ T.val :=
  hG.ded_closed ((SetPrv.of_mem h).map (fun _ p => .allE t ht p))

end Good

/-! ## The canonical model

States are maximally consistent theories; the domain is the set of terms, and
`ρ` is the identity on names, so a locally closed term denotes itself.  Domains
are constant here because the truth lemma below is proved for the
quantifier-free fragment, where they are never consulted. -/

/-- States of the canonical model. -/
def MaxTheory : Type := {T : Theory // Good T}

/-- The canonical model. -/
def canonical : KModel where
  S := MaxTheory
  D := Tm
  Dom _ _ := True
  Ri T T' := T.1.val ⊆ T'.1.val
  RA T T' := T.1.val ⊆ T'.1.val ∧ T.1.mfal .all ⊆ T'.1.mfal .all
  RE T T' := T.1.val ⊆ T'.1.val ∧ T.1.mfal .ex ⊆ T'.1.mfal .ex
  Fl T := Form.bot ∈ T.1.val
  refl_i _ := subset_rfl
  trans_i h h' := h.trans h'
  refl_A _ := ⟨subset_rfl, subset_rfl⟩
  trans_A h h' := ⟨h.1.trans h'.1, h.2.trans h'.2⟩
  sub_A h := h.1
  refl_E _ := ⟨subset_rfl, subset_rfl⟩
  trans_E h h' := ⟨h.1.trans h'.1, h.2.trans h'.2⟩
  sub_E h := h.1
  dom_mono _ _ := trivial
  d₀ := .fvar "x"
  dom_d₀ _ := trivial
  hered_Fl h hw := h hw
  fn f ds := .fn f ds
  I T P ds := Form.pred P ds ∈ T.1.val
  hered_I h hw := h hw
  fn_dom _ := trivial

/-- The identity valuation. -/
def idρ : String → canonical.D := fun x => .fvar x

mutual
theorem ev_id : ∀ (t : Tm), Tm.lcAt 0 t → canonical.evTm idρ [] t = t
  | .bvar i,  h => absurd h (Nat.not_lt_zero i)
  | .fvar _,  _ => rfl
  | .fn f ts, h => by
      show Tm.fn f (canonical.evTms idρ [] ts) = Tm.fn f ts
      rw [evs_id ts h]
theorem evs_id : ∀ (ts : List Tm), Tm.lcAtList 0 ts → canonical.evTms idρ [] ts = ts
  | [],      _ => rfl
  | t :: ts, h => by
      show canonical.evTm idρ [] t :: canonical.evTms idρ [] ts = _
      rw [ev_id t h.1, evs_id ts h.2]
      rfl
end

/-- The quantifier-free formulas: the fragment the truth lemma covers. -/
def QFree : Form → Prop
  | .top       => True
  | .bot       => True
  | .pred _ _  => True
  | .and A B   => QFree A ∧ QFree B
  | .or A B    => QFree A ∧ QFree B
  | .imp A B   => QFree A ∧ QFree B
  | .circ _ A  => QFree A
  | .forall_ _ => False
  | .exists_ _ => False

/-- **Truth lemma**: on the quantifier-free fragment, membership in `val`
forces and membership in `fal` refutes. -/
theorem truth_lemma : ∀ (A : Form), QFree A → Form.lc A → ∀ T : MaxTheory,
    (A ∈ T.1.val → canonical.force A T idρ []) ∧
    (A ∈ T.1.fal → ¬ canonical.force A T idρ []) := by
  intro A
  induction A with
  | top =>
      intro _ _ T
      exact ⟨fun _ => trivial, fun h _ => T.2.not_fal_deriv h (⟨[], by simp, .topI⟩)⟩
  | bot =>
      intro _ _ T
      exact ⟨fun h => h, fun h hf => T.2.not_fal_deriv h (SetPrv.of_mem hf)⟩
  | pred P ts =>
      intro _ hlc T
      have hev : canonical.evTms idρ [] ts = ts := evs_id ts hlc
      constructor
      · intro h
        show canonical.Fl T ∨ canonical.I T P (canonical.evTms idρ [] ts)
        rw [hev]; exact Or.inr h
      · intro h hf
        rcases (show canonical.Fl T ∨ canonical.I T P (canonical.evTms idρ [] ts) from hf) with
          hb | hp
        · exact T.2.not_fal_deriv h ((SetPrv.of_mem (show Form.bot ∈ T.1.val from hb)).map
            (fun _ p => .botE p))
        · rw [hev] at hp
          exact T.2.not_fal_deriv h (SetPrv.of_mem hp)
  | and A B ihA ihB =>
      intro hq hlc T
      constructor
      · intro h
        exact ⟨(ihA hq.1 hlc.1 T).1 (T.2.ded_closed
                 ((SetPrv.of_mem h).map (fun _ p => .andE₁ p))),
               (ihB hq.2 hlc.2 T).1 (T.2.ded_closed
                 ((SetPrv.of_mem h).map (fun _ p => .andE₂ p)))⟩
      · intro h hf
        rcases T.2.fal_and h with h' | h'
        · exact (ihA hq.1 hlc.1 T).2 h' hf.1
        · exact (ihB hq.2 hlc.2 T).2 h' hf.2
  | or A B ihA ihB =>
      intro hq hlc T
      constructor
      · intro h
        rcases T.2.or_mem h with h' | h'
        · exact Or.inl ((ihA hq.1 hlc.1 T).1 h')
        · exact Or.inr ((ihB hq.2 hlc.2 T).1 h')
      · intro h hf
        obtain ⟨h₁, h₂⟩ := T.2.fal_or h
        rcases hf with hf | hf
        · exact (ihA hq.1 hlc.1 T).2 h₁ hf
        · exact (ihB hq.2 hlc.2 T).2 h₂ hf
  | imp A B ihA ihB =>
      intro hq hlc T
      constructor
      · intro h T' hle hfA
        rcases T'.2.imp_mem (hle h) with h' | h'
        · exact absurd hfA ((ihA hq.1 hlc.1 T').2 h')
        · exact (ihB hq.2 hlc.2 T').1 h'
      · intro h hf
        have hcons : Consistent ⟨insert A T.1.val, {B}, fun _ => ∅⟩ := by
          intro Ds TA TE hD hA' hE hne hder
          have hTA : TA = [] := by
            cases TA with
            | nil => rfl
            | cons X _ => exact absurd (hA' X (by simp)) (by simp)
          have hTE : TE = [] := by
            cases TE with
            | nil => rfl
            | cons X _ => exact absurd (hE X (by simp)) (by simp)
          subst hTA; subst hTE
          rw [disjOf_fal] at hder
          have hB : insert A T.1.val ⊩q B :=
            SetPrv.bigOr_collapse Ds _ (fun X hX => hD X hX) hder
          exact T.2.not_fal_deriv h (SetPrv.deduct hB)
        obtain ⟨T', hle, hM'⟩ := exists_good_extension hcons
        have hRi : T.1.val ⊆ T'.val := (Set.subset_insert ..).trans hle.1
        exact (ihB hq.2 hlc.2 ⟨T', hM'⟩).2 (hle.2.1 rfl)
          (hf ⟨T', hM'⟩ hRi ((ihA hq.1 hlc.1 ⟨T', hM'⟩).1 (hle.1 (Set.mem_insert ..))))
  | circ q A ih =>
      intro hq hlc T
      cases q
      · constructor
        · intro h T₁ hle
          have hcons : Consistent
              ⟨insert A T₁.1.val, ∅, fun r => match r with | .all => T₁.1.mfal .all | .ex => ∅⟩ := by
            intro Ds TA TE hD hA' hE hne hder
            have hDs : Ds = [] := by
              cases Ds with
              | nil => rfl
              | cons X _ => exact absurd (hD X (by simp)) (by simp)
            have hTE : TE = [] := by
              cases TE with
              | nil => rfl
              | cons X _ => exact absurd (hE X (by simp)) (by simp)
            subst hDs; subst hTE
            have hTA : TA ≠ [] := by
              intro hnil; exact hne (by simp [hnil])
            rw [disjOf_all hTA] at hder
            refine T₁.2.1 [] TA [] (by simp) hA' (by simp) (by simp [hTA]) ?_
            rw [disjOf_all hTA]
            exact SetPrv.lax_bind (SetPrv.of_mem (hle h)) (SetPrv.deduct hder)
          obtain ⟨T₂, hle₂, hM₂⟩ := exists_good_extension hcons
          exact ⟨⟨T₂, hM₂⟩, ⟨(Set.subset_insert ..).trans hle₂.1, hle₂.2.2 .all⟩,
            (ih hq hlc ⟨T₂, hM₂⟩).1 (hle₂.1 (Set.mem_insert ..))⟩
        · intro h hf
          have hcons : Consistent
              ⟨T.1.val, ∅, fun r => match r with | .all => {A} | .ex => ∅⟩ := by
            intro Ds TA TE hD hA' hE hne hder
            have hDs : Ds = [] := by
              cases Ds with
              | nil => rfl
              | cons X _ => exact absurd (hD X (by simp)) (by simp)
            have hTE : TE = [] := by
              cases TE with
              | nil => rfl
              | cons X _ => exact absurd (hE X (by simp)) (by simp)
            subst hDs; subst hTE
            have hTA : TA ≠ [] := by
              intro hnil; exact hne (by simp [hnil])
            rw [disjOf_all hTA] at hder
            exact T.2.not_fal_deriv h (SetPrv.lax_collapse TA (fun X hX => hA' X hX) hder)
          obtain ⟨T', hle, hM'⟩ := exists_good_extension hcons
          obtain ⟨T₂, hRm, hfA⟩ := hf ⟨T', hM'⟩ hle.1
          exact (ih hq hlc T₂).2 (T₂.2.mfal_sub_fal (hRm.2 (hle.2.2 .all rfl))) hfA
      · constructor
        · intro h T₁ hle
          have hcons : Consistent
              ⟨insert A T₁.1.val, ∅, fun r => match r with | .all => ∅ | .ex => T₁.1.mfal .ex⟩ := by
            intro Ds TA TE hD hA' hE hne hder
            have hDs : Ds = [] := by
              cases Ds with
              | nil => rfl
              | cons X _ => exact absurd (hD X (by simp)) (by simp)
            have hTA : TA = [] := by
              cases TA with
              | nil => rfl
              | cons X _ => exact absurd (hA' X (by simp)) (by simp)
            subst hDs; subst hTA
            have hTE : TE ≠ [] := by
              intro hnil; exact hne (by simp [hnil])
            rw [disjOf_ex hTE] at hder
            refine T₁.2.1 [] [] TE (by simp) (by simp) hE (by simp [hTE]) ?_
            rw [disjOf_ex hTE]
            exact SetPrv.lax_bind (SetPrv.of_mem (hle h)) (SetPrv.deduct hder)
          obtain ⟨T₂, hle₂, hM₂⟩ := exists_good_extension hcons
          exact ⟨⟨T₂, hM₂⟩, ⟨(Set.subset_insert ..).trans hle₂.1, hle₂.2.2 .ex⟩,
            (ih hq hlc ⟨T₂, hM₂⟩).1 (hle₂.1 (Set.mem_insert ..))⟩
        · intro h hf
          have hcons : Consistent
              ⟨T.1.val, ∅, fun r => match r with | .all => ∅ | .ex => {A}⟩ := by
            intro Ds TA TE hD hA' hE hne hder
            have hDs : Ds = [] := by
              cases Ds with
              | nil => rfl
              | cons X _ => exact absurd (hD X (by simp)) (by simp)
            have hTA : TA = [] := by
              cases TA with
              | nil => rfl
              | cons X _ => exact absurd (hA' X (by simp)) (by simp)
            subst hDs; subst hTA
            have hTE : TE ≠ [] := by
              intro hnil; exact hne (by simp [hnil])
            rw [disjOf_ex hTE] at hder
            exact T.2.not_fal_deriv h (SetPrv.lax_collapse TE (fun X hX => hE X hX) hder)
          obtain ⟨T', hle, hM'⟩ := exists_good_extension hcons
          obtain ⟨T₂, hRm, hfA⟩ := hf ⟨T', hM'⟩ hle.1
          exact (ih hq hlc T₂).2 (T₂.2.mfal_sub_fal (hRm.2 (hle.2.2 .ex rfl))) hfA
  | forall_ _ _ => intro hq _ _; exact absurd hq (by simp [QFree])
  | exists_ _ _ => intro hq _ _; exact absurd hq (by simp [QFree])

/-! ## Completeness -/

/-- **Completeness** on the quantifier-free fragment: a semantic consequence
over a finite context is provable. -/
theorem completeness {Γ : List Form} {A : Form}
    (hΓ : ∀ B ∈ Γ, QFree B ∧ Form.lc B) (hqA : QFree A) (hlcA : Form.lc A)
    (h : Γ ⊫ A) : Γ ⊢q A := by
  by_contra hn
  have hcons : Consistent ⟨{B | B ∈ Γ}, {A}, fun _ => ∅⟩ := by
    intro Ds TA TE hD hA' hE hne hder
    have hTA : TA = [] := by
      cases TA with
      | nil => rfl
      | cons X _ => exact absurd (hA' X (by simp)) (by simp)
    have hTE : TE = [] := by
      cases TE with
      | nil => rfl
      | cons X _ => exact absurd (hE X (by simp)) (by simp)
    subst hTA; subst hTE
    rw [disjOf_fal] at hder
    obtain ⟨L, hL, hp⟩ := SetPrv.bigOr_collapse Ds _ (fun X hX => hD X hX) hder
    exact hn (hp.weaken (fun X hX => hL X hX))
  obtain ⟨T, hle, hM⟩ := exists_good_extension hcons
  refine (truth_lemma A hqA hlcA ⟨T, hM⟩).2 (hle.2.1 rfl) ?_
  exact h canonical ⟨T, hM⟩ idρ (fun _ => trivial) (fun B hB =>
    (truth_lemma B (hΓ B hB).1 (hΓ B hB).2 ⟨T, hM⟩).1 (hle.1 hB))

end LaxLogic.QLL
