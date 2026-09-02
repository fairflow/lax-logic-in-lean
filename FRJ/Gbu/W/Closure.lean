/-
# The `decideGbuW` instantiation — Part I: kept-chain dominance and join monotonicity

`searchW`/`dichotomyW` (FRJ/Gbu/W/Search.lean) are parameterised by a
`WSaturated G D` with decidable row queries.  The instantiation route:

    D := (· ∈ db G)   for a COMPUTED closure `db`,

so the deciders are finite scans and the whole weight concentrates in
`WSaturated.2` — every `WDerivable` row is subsumed by a stored one — by
induction on the derivation.  Each rule case needs its MONOTONICITY
lemma (statement T-B of docs/frjw-fixpoint-attack.md): the rule applied
to stored subsumers of its premises yields a conclusion subsuming the
original's, so the closure need only ever apply rules to stored rows.

This file proves the foundation layer:

  * **T-A, kept-chain dominance** (`keptChain_sub_keptOf`): every link
    of every `KeptChain` lands in the greedy `keptOf` — including the
    parameter-growth form (`keptChain_sub_keptOf_of_le`) that absorbs
    zone growth under premise swap.  The A1 attacker
    (wip/chainprobe.lean) enumerated all chains over five designed
    dependency seeds and found no counterexample before this proof was
    scoped; `keptOf_saturated` (FRJ/RefAt.lean) is the enabling brick.
  * the zone toolkit: part membership under `≐`, `unionAll`/`interAll`
    monotonicity, V-base former monotonicity, `thPool` monotonicity.
  * **T-B for the barren joins** `⋈^◯` (`joinCirc_mono`, the archetype:
    relaxed (J2), canonical kept chain), `⋈^∨` (`joinOr_mono`), `⋈^At`
    (`joinAt_mono`), and for `◯∈` (`circIn_mono`, the first
    tag-interaction case).

Premise swap means: each irregular premise row `(Σⱼ, Θⱼ, Aⱼ)` is
replaced by a stored subsumer `(Σ'ⱼ, Θ'ⱼ, Aⱼ)` with `Σ'ⱼ ≐ Σⱼ` and
`Θⱼ ⊆ Θ'ⱼ` (`WSubsumes` on the irregular stratum, same right formula).
The re-fired join takes the canonical kept chain `keptOf` over the new
base and pool; T-A places the old chain inside it, so the new conclusion
context CONTAINS the old one and the new row subsumes the old row.

All parts have since landed (Parts II-V in this file; the saturation
and assembly in FRJ/Gbu/W/Saturate.lean) and the goal is closed.

ARCHIVE NOTE (2026-09-01 compaction, docs/frjw-compaction.md): the nine
standalone T-B `_mono` defs (`joinCirc_mono`, `joinOr_mono`,
`joinAt_mono`, `joinAtP_mono`, `joinOrP_mono`, `joinCircP_mono`,
`circIn_mono`, `orI_mono`, `impInI_mono`) have NO code consumer — the
saturation emitters fire the constructors directly and the T-C
induction uses the `_of_swap` transfer lemmas.  They are kept compiled
and pinned as the standalone T-B record (archive, not deletion).  The
live pieces are the transfer lemmas, the `ctx_sub` lemmas, `lift_max`,
`circNotIn_max`, `orI_mono_sub`, and `impInI_mono_sub`.
-/
import FRJ.CalculusW
import FRJ.Search.Engine
import FRJ.Gbu.W.Search

namespace FRJ

open Form FRJ.Search

/-! ## T-A: kept-chain dominance -/

/-- T-A with parameter growth: a kept chain over the smaller data lands,
link by link, inside the greedy fixpoint over the larger data.  Each
link's certificate cites the base plus the EARLIER links; by induction
those sit inside `keptOf`, `RefAt`-monotonicity lifts the certificate to
the final kept context, and `keptOf_saturated` absorbs the link. -/
theorem keptChain_sub_keptOf_of_le
    {Υ Υ' base base' pool pool' kept : List Form}
    (hu : Υ ⊆ Υ') (hb : base ⊆ base') (hp : pool ⊆ pool')
    (h : KeptChain Υ base pool kept) :
    ∀ Y ∈ kept, Y ∈ keptOf Υ' base' pool' := by
  induction h with
  | nil => exact fun _ h => absurd h List.not_mem_nil
  | @cons Y B rest hrest hmem hY ih =>
      intro X hX
      rcases List.mem_cons.mp hX with rfl | hX'
      · refine keptOf_saturated (hp hmem) (refAt_mono hu ?_ hY)
        intro x hx
        rcases List.mem_append.mp hx with h₁ | h₂
        · exact List.mem_append_left _ (hb h₁)
        · exact List.mem_append_right _ (ih x h₂)
      · exact ih X hX'

/-- **T-A (kept-chain dominance).**  Every link of every kept chain is
in the greedy `keptOf` over the same data. -/
theorem keptChain_sub_keptOf {Υ base pool kept : List Form}
    (h : KeptChain Υ base pool kept) :
    ∀ Y ∈ kept, Y ∈ keptOf Υ base pool :=
  keptChain_sub_keptOf_of_le (fun _ h => h) (fun _ h => h) (fun _ h => h) h

/-! ## The zone toolkit -/

theorem mem_atPart {Γ : List Form} {x : Form} :
    x ∈ atPart Γ ↔ x ∈ Γ ∧ x.isPV = true := by
  simp [atPart, List.mem_filter]

theorem mem_impPart {Γ : List Form} {x : Form} :
    x ∈ impPart Γ ↔ x ∈ Γ ∧ x.isImp = true := by
  simp [impPart, List.mem_filter]

theorem mem_circPart {Γ : List Form} {x : Form} :
    x ∈ circPart Γ ↔ x ∈ Γ ∧ x.isCirc = true := by
  simp [circPart, List.mem_filter]

/-- A `≐`-swap of every summand preserves union membership of the
filtered parts (used with `atPart`/`impPart`/`circPart`). -/
theorem mem_unionAll_filter_of_ctxEq {n : Nat}
    {f g : Fin (n + 1) → List Form} (P : Form → Bool)
    (h : ∀ j, f j ≐ g j) {x : Form}
    (hx : x ∈ unionAll (fun j => (f j).filter P)) :
    x ∈ unionAll (fun j => (g j).filter P) := by
  obtain ⟨j, hj⟩ := mem_unionAll.mp hx
  have h' := List.mem_filter.mp hj
  exact mem_unionAll.mpr ⟨j, List.mem_filter.mpr ⟨(h j x).mp h'.1, h'.2⟩⟩

/-- Stable-zone `◯`-emptiness transfers across `≐`-swaps of the zones:
an empty filter means no member passes, and membership is all `≐`
preserves or needs. -/
theorem unionAll_circPart_nil_of_ctxEq {n : Nat}
    {stab stab' : Fin (n + 1) → List Form}
    (hst : ∀ j, stab' j ≐ stab j)
    (h : unionAll (fun j => circPart (stab j)) = []) :
    unionAll (fun j => circPart (stab' j)) = [] := by
  cases hcase : unionAll (fun j => circPart (stab' j)) with
  | nil => rfl
  | cons y ys =>
      exfalso
      have hy : y ∈ unionAll (fun j => circPart (stab' j)) :=
        hcase ▸ List.mem_cons_self
      obtain ⟨j, hj⟩ := mem_unionAll.mp hy
      have h' := mem_circPart.mp hj
      have : y ∈ unionAll (fun j => circPart (stab j)) :=
        mem_unionAll.mpr ⟨j, mem_circPart.mpr ⟨(hst j y).mp h'.1, h'.2⟩⟩
      rw [h] at this
      exact absurd this List.not_mem_nil

/-- The retention pool grows with the second zones. -/
theorem thPool_mono {n : Nat} {th th' : Fin (n + 1) → List Form}
    (hth : ∀ j, th j ⊆ th' j) : thPool th ⊆ thPool th' := by
  intro x hx
  have h' := mem_impPart.mp hx
  have hall := mem_interAll.mp h'.1
  exact mem_impPart.mpr ⟨mem_interAll.mpr (fun j => hth j (hall j)), h'.2⟩

/-- The `⋈^∨`/`⋈^◯` base context is monotone under premise swap:
set-equal stable zones, larger second zones. -/
theorem joinCtxOrVBase_mono {n : Nat}
    {stab th stab' th' : Fin (n + 1) → List Form}
    (hst : ∀ j, stab j ≐ stab' j) (hth : ∀ j, th j ⊆ th' j) :
    joinCtxOrVBase stab th ⊆ joinCtxOrVBase stab' th' := by
  intro x hx
  simp only [joinCtxOrVBase, List.mem_append] at hx ⊢
  rcases hx with (h | h) | h
  · exact Or.inl (Or.inl (mem_unionAll_filter_of_ctxEq _ hst h))
  · refine Or.inl (Or.inr ?_)
    have hall := mem_interAll.mp h
    refine mem_interAll.mpr (fun j => ?_)
    have h' := mem_atPart.mp (hall j)
    exact mem_atPart.mpr ⟨hth j h'.1, h'.2⟩
  · exact Or.inr (mem_unionAll_filter_of_ctxEq _ hst h)

/-- The `⋈^At` base context is monotone under premise swap. -/
theorem joinCtxAtVBase_mono {n : Nat}
    {stab th stab' th' : Fin (n + 1) → List Form} {F : Form}
    (hst : ∀ j, stab j ≐ stab' j) (hth : ∀ j, th j ⊆ th' j) :
    joinCtxAtVBase stab th F ⊆ joinCtxAtVBase stab' th' F := by
  intro x hx
  simp only [joinCtxAtVBase, List.mem_append] at hx ⊢
  rcases hx with (h | h) | h
  · exact Or.inl (Or.inl (mem_unionAll_filter_of_ctxEq _ hst h))
  · refine Or.inl (Or.inr ?_)
    have h' := mem_rm.mp h
    have hall := mem_interAll.mp h'.2
    refine mem_rm.mpr ⟨h'.1, ?_⟩
    refine mem_interAll.mpr (fun j => ?_)
    have h'' := mem_atPart.mp (hall j)
    exact mem_atPart.mpr ⟨hth j h''.1, h''.2⟩
  · exact Or.inr (mem_unionAll_filter_of_ctxEq _ hst h)

/-- (J1) transfers to the swapped family. -/
theorem hJ1_of_swap {n : Nat}
    {stab th stab' th' : Fin (n + 1) → List Form}
    (hst : ∀ j, stab' j ≐ stab j) (hth : ∀ j, th j ⊆ th' j)
    (hJ1 : ∀ i j, i ≠ j → stab i ⊆ stab j ++ th j) :
    ∀ i j, i ≠ j → stab' i ⊆ stab' j ++ th' j := by
  intro i j hij x hx
  rcases List.mem_append.mp (hJ1 i j hij ((hst i x).mp hx)) with h | h
  · exact List.mem_append_left _ ((hst j x).mpr h)
  · exact List.mem_append_right _ (hth j h)

/-- The strict (J2) transfers to the swapped family (`Υ` is unchanged —
subsumers keep the right formula). -/
theorem hJ2_strict_of_swap {n : Nat}
    {stab stab' : Fin (n + 1) → List Form} {rhs : Fin (n + 1) → Form}
    (hst : ∀ j, stab' j ≐ stab j)
    (hJ2 : ∀ A B : Form,
      Form.imp A B ∈ unionAll (fun j => impPart (stab j)) →
      A ∈ upsilon rhs) :
    ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (stab' j)) →
      A ∈ upsilon rhs :=
  fun A B hAB => hJ2 A B (mem_unionAll_filter_of_ctxEq _ hst hAB)

/-! ## T-B: the barren joins under premise swap

Shape shared by all three: the old conclusion context (base plus its
kept chain) sits inside the new canonical one (swapped base plus
`keptOf`), by base monotonicity and T-A; every `RefAt` side certificate
lifts by `refAt_mono`; and the join re-fires at the canonical chain
certified by `keptOf_ok`. -/

/-- The old `⋈^∨`/`⋈^◯` conclusion context sits inside the new
canonical one. -/
theorem joinOr_ctx_sub {n : Nat}
    {stab th stab' th' : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form} {kept : List Form}
    (hst : ∀ j, stab' j ≐ stab j) (hth : ∀ j, th j ⊆ th' j)
    (hkc : KeptChain (upsilon rhs) (joinCtxOrVBase stab th)
      (thPool th) kept) :
    joinCtxOrVBase stab th ++ kept ⊆
      joinCtxOrVBase stab' th' ++
        keptOf (upsilon rhs) (joinCtxOrVBase stab' th') (thPool th') := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact List.mem_append_left _
      (joinCtxOrVBase_mono (fun j => (hst j).symm) hth h)
  · exact List.mem_append_right _
      (keptChain_sub_keptOf_of_le (fun _ h => h)
        (joinCtxOrVBase_mono (fun j => (hst j).symm) hth)
        (thPool_mono hth) hkc x h)

/-- **T-B for the relaxed barren `⋈^◯`** (the archetype).  Premise swap
to stored subsumers re-fires the join at the canonical kept chain; the
conclusion context contains the old one (`joinOr_ctx_sub`), so the new
row subsumes the old (`barren` tag and goal unchanged). -/
def joinCirc_mono {G : Form} {n : Nat}
    {stab th stab' th' : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form} {Z : Form} {kept : List Form}
    (prem' : ∀ j, FRJWi G (stab' j) (th' j) (rhs j))
    (hst : ∀ j, stab' j ≐ stab j) (hth : ∀ j, th j ⊆ th' j)
    (hJ1 : ∀ i j, i ≠ j → stab i ⊆ stab j ++ th j)
    (hJ2 : ∀ A B : Form,
      Form.imp A B ∈ unionAll (fun j => impPart (stab j)) →
      RefAt true (upsilon rhs) (joinCtxOrVBase stab th ++ kept) A)
    (hcirc : unionAll (fun j => circPart (stab j)) = [])
    (hkc : KeptChain (upsilon rhs) (joinCtxOrVBase stab th)
      (thPool th) kept)
    (hZ : RefAt true (upsilon rhs) (joinCtxOrVBase stab th ++ kept) Z)
    (hgoal : Form.circ Z ∈ sfR G) :
    FRJWr G .barren
      (joinCtxOrVBase stab' th' ++
        keptOf (upsilon rhs) (joinCtxOrVBase stab' th') (thPool th'))
      (.circ Z) :=
  have hsub := joinOr_ctx_sub hst hth hkc
  .joinCirc prem'
    (hJ1_of_swap hst hth hJ1)
    (fun A B hAB =>
      refAt_mono (fun _ h => h) hsub
        (hJ2 A B (mem_unionAll_filter_of_ctxEq _ hst hAB)))
    (unionAll_circPart_nil_of_ctxEq hst hcirc)
    (keptOf_ok _ _ _)
    (refAt_mono (fun _ h => h) hsub hZ)
    hgoal
    (CtxEq.refl _)

/-- **T-B for the barren `⋈^∨`.**  Same shape; the disjunct certificates
lift by `refAt_mono`, and (J2) stays strict. -/
def joinOr_mono {G : Form} {n : Nat}
    {stab th stab' th' : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form} {C₁ C₂ : Form} {kept : List Form}
    (prem' : ∀ j, FRJWi G (stab' j) (th' j) (rhs j))
    (hst : ∀ j, stab' j ≐ stab j) (hth : ∀ j, th j ⊆ th' j)
    (hJ1 : ∀ i j, i ≠ j → stab i ⊆ stab j ++ th j)
    (hJ2 : ∀ A B : Form,
      Form.imp A B ∈ unionAll (fun j => impPart (stab j)) →
      A ∈ upsilon rhs)
    (hcirc : unionAll (fun j => circPart (stab j)) = [])
    (hkc : KeptChain (upsilon rhs) (joinCtxOrVBase stab th)
      (thPool th) kept)
    (hC : RefAt true (upsilon rhs) (joinCtxOrVBase stab th ++ kept) C₁ ∧
      RefAt true (upsilon rhs) (joinCtxOrVBase stab th ++ kept) C₂)
    (hgoal : Form.or C₁ C₂ ∈ sfR G) :
    FRJWr G .barren
      (joinCtxOrVBase stab' th' ++
        keptOf (upsilon rhs) (joinCtxOrVBase stab' th') (thPool th'))
      (.or C₁ C₂) :=
  have hsub := joinOr_ctx_sub hst hth hkc
  .joinOr prem'
    (hJ1_of_swap hst hth hJ1)
    (hJ2_strict_of_swap hst hJ2)
    (unionAll_circPart_nil_of_ctxEq hst hcirc)
    (keptOf_ok _ _ _)
    ⟨refAt_mono (fun _ h => h) hsub hC.1,
     refAt_mono (fun _ h => h) hsub hC.2⟩
    hgoal
    (CtxEq.refl _)

/-- The old `⋈^At` conclusion context sits inside the new canonical
one. -/
theorem joinAt_ctx_sub {n : Nat}
    {stab th stab' th' : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form} {F : Form} {kept : List Form}
    (hst : ∀ j, stab' j ≐ stab j) (hth : ∀ j, th j ⊆ th' j)
    (hkc : KeptChain (upsilon rhs) (joinCtxAtVBase stab th F)
      (thPool th) kept) :
    joinCtxAtVBase stab th F ++ kept ⊆
      joinCtxAtVBase stab' th' F ++
        keptOf (upsilon rhs) (joinCtxAtVBase stab' th' F) (thPool th') := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact List.mem_append_left _
      (joinCtxAtVBase_mono (fun j => (hst j).symm) hth h)
  · exact List.mem_append_right _
      (keptChain_sub_keptOf_of_le (fun _ h => h)
        (joinCtxAtVBase_mono (fun j => (hst j).symm) hth)
        (thPool_mono hth) hkc x h)

/-- **T-B for the barren `⋈^At`.**  The removed goal atom `F` is fixed,
so `rm`-monotonicity rides along; `F ∉ Σ^at` transfers across the
`≐`-swap by contraposition.  No `RefAt` certificate needs lifting here
(strict (J2), no disjunct/body condition), so the old kept chain enters
only through `joinAt_ctx_sub` on the subsumption side. -/
def joinAt_mono {G : Form} {n : Nat}
    {stab th stab' th' : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form} {F : Form}
    (prem' : ∀ j, FRJWi G (stab' j) (th' j) (rhs j))
    (hst : ∀ j, stab' j ≐ stab j) (hth : ∀ j, th j ⊆ th' j)
    (hJ1 : ∀ i j, i ≠ j → stab i ⊆ stab j ++ th j)
    (hJ2 : ∀ A B : Form,
      Form.imp A B ∈ unionAll (fun j => impPart (stab j)) →
      A ∈ upsilon rhs)
    (hcirc : unionAll (fun j => circPart (stab j)) = [])
    (hF : F.isPrime)
    (hFnot : F ∉ unionAll (fun j => atPart (stab j)))
    (hgoal : F ∈ sfR G) :
    FRJWr G .barren
      (joinCtxAtVBase stab' th' F ++
        keptOf (upsilon rhs) (joinCtxAtVBase stab' th' F) (thPool th'))
      F :=
  .joinAt prem'
    (hJ1_of_swap hst hth hJ1)
    (hJ2_strict_of_swap hst hJ2)
    (unionAll_circPart_nil_of_ctxEq hst hcirc)
    (keptOf_ok _ _ _)
    hF
    (fun hmem => hFnot (mem_unionAll_filter_of_ctxEq _ hst hmem))
    hgoal
    (CtxEq.refl _)

/-- The pledge side condition of `◯∈`/`◯∉` and the promise joins rides
up the retention order: a subsumer's tag can only move from `blocked`
towards `barren` (`chain` only at equal pledge), and each move
preserves the demand. -/
theorem pledge_of_le {t t₂ : Tag} {Γ Γ₂ : List Form} {Z : Form}
    (hle : tagLeB t t₂ = true) (hΓ : Γ ⊆ Γ₂)
    (htag : t = .barren ∨ ∃ W, t = .chain W ∧ Covers Γ W Z) :
    t₂ = .barren ∨ ∃ W, t₂ = .chain W ∧ Covers Γ₂ W Z := by
  rcases htag with rfl | ⟨W, rfl, hcov⟩
  · cases t₂ with
    | barren => exact Or.inl rfl
    | chain D => exact absurd hle (by simp [tagLeB])
    | blocked => exact absurd hle (by simp [tagLeB])
  · cases t₂ with
    | barren => exact Or.inl rfl
    | chain D =>
        have hWD : W = D := by simpa [tagLeB] using hle
        exact Or.inr ⟨D, rfl, hWD ▸ covers_mono hΓ hcov⟩
    | blocked => exact absurd hle (by simp [tagLeB])

/-! ## T-B: `◯∈` under premise swap — the first tag interaction

`tagLeB` (blocked ≤ chain at equal pledge ≤ barren) is the engine's
retention order and `WSubsumes`'s regular tag condition.  `◯∈` demands
`barren` or a covering `chain`; a subsumer's tag can only move UP the
order, and each move preserves the demand. -/

def circIn_mono {G : Form} {t t₂ : Tag} {Γ Γ₂ : List Form} {Z : Form}
    (d₂ : FRJWr G t₂ Γ₂ Z) (hΓ : Γ ⊆ Γ₂)
    (hle : tagLeB t t₂ = true)
    (htag : t = .barren ∨ ∃ W, t = .chain W ∧ Covers Γ W Z)
    (hgoal : Form.circ Z ∈ sfR G) :
    FRJWr G t₂ Γ₂ (.circ Z) :=
  .circIn d₂ (pledge_of_le hle hΓ htag) hgoal

/-! ## Part II helpers -/

/-- `≐` is a congruence for `++`. -/
theorem ctxEq_append {l₁ l₂ m₁ m₂ : List Form} (h₁ : l₁ ≐ l₂)
    (h₂ : m₁ ≐ m₂) : l₁ ++ m₁ ≐ l₂ ++ m₂ := by
  intro x
  simp only [List.mem_append]
  exact ⟨fun h => h.imp (h₁ x).mp (h₂ x).mp,
         fun h => h.imp (h₁ x).mpr (h₂ x).mpr⟩

/-- Filters are monotone in the list AND in a pointwise-implied
predicate (the shape all three `restrict` operators share). -/
theorem mem_filter_mono' {l m : List Form} {p q : Form → Bool}
    (hl : l ⊆ m) (hpq : ∀ x, p x = true → q x = true) :
    l.filter p ⊆ m.filter q := by
  intro x hx
  have h := List.mem_filter.mp hx
  exact List.mem_filter.mpr ⟨hl h.1, hpq x h.2⟩

/-! ## T-B: the structural irregular rules -/

/-- **T-B for `∨ᵢ`.**  The cross conditions and both conclusion zones
are monotone: `Σ`-zones transfer along `≐`, `Θ`-zones along `⊆` and
`cap`-monotonicity. -/
def orI_mono {G : Form} {St₁ Th₁ St₂ Th₂ St₁' Th₁' St₂' Th₂' : List Form}
    {C₁ C₂ : Form}
    (d₁ : FRJWi G St₁' Th₁' C₁) (d₂ : FRJWi G St₂' Th₂' C₂)
    (h₁e : St₁' ≐ St₁) (h₁s : Th₁ ⊆ Th₁')
    (h₂e : St₂' ≐ St₂) (h₂s : Th₂ ⊆ Th₂')
    (h₁ : St₁ ⊆ St₂ ++ Th₂) (h₂ : St₂ ⊆ St₁ ++ Th₁)
    (hgoal : Form.or C₁ C₂ ∈ sfR G) :
    FRJWi G (St₁' ++ St₂') (cap Th₁' Th₂') (.or C₁ C₂) :=
  .orI d₁ d₂
    (fun x hx => by
      rcases List.mem_append.mp (h₁ ((h₁e x).mp hx)) with h | h
      · exact List.mem_append_left _ ((h₂e x).mpr h)
      · exact List.mem_append_right _ (h₂s h))
    (fun x hx => by
      rcases List.mem_append.mp (h₂ ((h₂e x).mp hx)) with h | h
      · exact List.mem_append_left _ ((h₁e x).mpr h)
      · exact List.mem_append_right _ (h₁s h))
    hgoal (CtxEq.refl _) (CtxEq.refl _)

/-- Subsumption side of `orI_mono`: the old conclusion zones sit inside
the new ones (`Σ` by `≐`, `Θ` by `⊆`). -/
theorem orI_mono_sub {St₁ Th₁ St₂ Th₂ St₁' Th₁' St₂' Th₂' St' Th' : List Form}
    (h₁e : St₁' ≐ St₁) (h₁s : Th₁ ⊆ Th₁')
    (h₂e : St₂' ≐ St₂) (h₂s : Th₂ ⊆ Th₂')
    (hSt : St' ≐ St₁ ++ St₂) (hTh : Th' ≐ cap Th₁ Th₂) :
    St' ≐ St₁' ++ St₂' ∧ Th' ⊆ cap Th₁' Th₂' :=
  ⟨hSt.trans (ctxEq_append h₁e.symm h₂e.symm),
   fun x hx => by
    have h := mem_cap.mp ((hTh x).mp hx)
    exact mem_cap.mpr ⟨h₁s h.1, h₂s h.2⟩⟩

/-- **T-B for `⊃∈ᵢ`** — the second-zone split.  The subsumer's larger
combined zone `ΘΛ₂` re-splits by membership in the ORIGINAL `Λ`: the
`Λ`-side filter is set-equal to `Λ` (every `Λ`-member survives into
`ΘΛ₂`), so the new stable zone is `≐` the old, and the new second zone
keeps every old `Θ`-member (disjointness sends them to the right side
of the split). -/
def impInI_mono {G : Form} {St St₂ Th Lam ThLam ThLam₂ : List Form}
    {A B : Form}
    (d₂ : FRJWi G St₂ ThLam₂ B)
    (hSt₂ : St₂ ≐ St) (hTL : ThLam ⊆ ThLam₂)
    (hpre : ThLam ≐ Th ++ Lam)
    (hA : Clo (St ++ Lam) A) (hgoal : Form.imp A B ∈ sfR G) :
    FRJWi G (St₂ ++ ThLam₂.filter (fun x => decide (x ∈ Lam)))
      (ThLam₂.filter (fun x => !decide (x ∈ Lam))) (.imp A B) := by
  have hLamSub : Lam ⊆ ThLam₂ := fun x hx =>
    hTL ((hpre x).mpr (List.mem_append_right _ hx))
  refine .impInI d₂ ?_ ?_ ?_ hgoal (CtxEq.refl _) (CtxEq.refl _)
  · -- the split partitions ΘΛ₂
    intro x
    simp only [List.mem_append, List.mem_filter, Bool.not_eq_eq_eq_not,
      Bool.not_true, decide_eq_true_eq, decide_eq_false_iff_not]
    constructor
    · intro hx
      by_cases hL : x ∈ Lam
      · exact Or.inr ⟨hx, hL⟩
      · exact Or.inl ⟨hx, hL⟩
    · rintro (⟨hx, -⟩ | ⟨hx, -⟩) <;> exact hx
  · -- disjointness of the split
    refine List.eq_nil_of_subset_nil (fun x hx => ?_)
    have h := mem_cap.mp hx
    have h₁ := List.mem_filter.mp h.1
    have h₂ := List.mem_filter.mp h.2
    rw [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h₁
    rw [decide_eq_true_eq] at h₂
    exact absurd h₂.2 h₁.2
  · -- the antecedent stays closure-available
    refine clo_mono (fun x hx => ?_) hA
    rcases List.mem_append.mp hx with h | h
    · exact List.mem_append_left _ ((hSt₂ x).mpr h)
    · exact List.mem_append_right _
        (List.mem_filter.mpr ⟨hLamSub h, by simpa using h⟩)

/-- Subsumption side of `impInI_mono`: the old conclusion zones sit
inside the new split. -/
theorem impInI_mono_sub {St St₂ Th Lam ThLam ThLam₂ St' Th' : List Form}
    (hSt₂ : St₂ ≐ St) (hTL : ThLam ⊆ ThLam₂)
    (hpre : ThLam ≐ Th ++ Lam) (hdisj : cap Th Lam = [])
    (hSt : St' ≐ St ++ Lam) (hTh : Th' ≐ Th) :
    St' ≐ St₂ ++ ThLam₂.filter (fun x => decide (x ∈ Lam)) ∧
      Th' ⊆ ThLam₂.filter (fun x => !decide (x ∈ Lam)) := by
  have hLamSub : Lam ⊆ ThLam₂ := fun x hx =>
    hTL ((hpre x).mpr (List.mem_append_right _ hx))
  constructor
  · refine hSt.trans (ctxEq_append hSt₂.symm (fun x => ?_))
    simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun hx => ⟨hLamSub hx, hx⟩, fun hx => hx.2⟩
  · intro x hx
    have hxTh : x ∈ Th := (hTh x).mp hx
    have hxNotLam : x ∉ Lam := fun hL =>
      absurd (mem_cap.mpr ⟨hxTh, hL⟩) (by simp [hdisj])
    refine List.mem_filter.mpr ⟨hTL ((hpre x).mpr (List.mem_append_left _ hxTh)), ?_⟩
    simpa using hxNotLam

/-! ## T-B: `Lift` and `◯∉` at the maximal second zone

Both rules retain an ARBITRARY `Θ ⊆ Ĝ ∩ Cl(Γ)`.  The closure stores the
MAXIMAL choice over the stored regular row; every other choice over any
subsumed premise is subsumed by it. -/

/-- The maximal retained zone of a `lift`/`◯∉` over context `Γ₂`. -/
def maxTh (G : Form) (Γ₂ : List Form) : List Form :=
  (gHat G).filter (fun X => cloB Γ₂ X)

/-- Any admissible retained zone over a smaller context sits inside the
maximal one over the larger. -/
theorem maxTh_sub {G : Form} {Γ Γ₂ Th : List Form} (hΓ : Γ ⊆ Γ₂)
    (hTh : ∀ X ∈ Th, Clo Γ X ∧ X ∈ gHat G) : Th ⊆ maxTh G Γ₂ :=
  fun X hX => List.mem_filter.mpr
    ⟨(hTh X hX).2, cloB_iff.mpr (clo_mono hΓ (hTh X hX).1)⟩

/-- **T-B for `Lift`**: the maximal lift of a stored regular row. -/
def lift_max {G : Form} {t₂ : Tag} {Γ₂ : List Form} {C : Form}
    (d₂ : FRJWr G t₂ Γ₂ C) : FRJWi G [] (maxTh G Γ₂) C :=
  .lift d₂ (fun X hX => by
    have h := List.mem_filter.mp hX
    exact ⟨cloB_iff.mp h.2, h.1⟩)

/-- **T-B for `◯∉`**: the maximal `circNotIn` of a stored regular row;
the pledge rides up the retention order. -/
def circNotIn_max {G : Form} {t t₂ : Tag} {Γ Γ₂ : List Form} {Z : Form}
    (d₂ : FRJWr G t₂ Γ₂ Z) (hΓ : Γ ⊆ Γ₂) (hle : tagLeB t t₂ = true)
    (htag : t = .barren ∨ ∃ W, t = .chain W ∧ Covers Γ W Z)
    (hgoal : Form.circ Z ∈ sfR G) :
    FRJWi G [] (maxTh G Γ₂) (.circ Z) :=
  .circNotIn d₂ (pledge_of_le hle hΓ htag)
    (fun X hX => by
      have h := List.mem_filter.mp hX
      exact ⟨cloB_iff.mp h.2, h.1⟩)
    hgoal

/-! ## T-B: the fallible joins

No kept zone and no `RefAt` certificate: everything transfers by the
zone toolkit, and the full conclusion contexts (with their restricted
`Θ`-implication and `◯`-components) are monotone by
`mem_filter_mono'`. -/

/-- The full `⋈^At` context is monotone under premise swap. -/
theorem joinCtxAt_mono {n : Nat}
    {stab th stab' th' : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form} {F : Form}
    (hst : ∀ j, stab j ≐ stab' j) (hth : ∀ j, th j ⊆ th' j) :
    joinCtxAt stab th rhs F ⊆ joinCtxAt stab' th' rhs F := by
  intro x hx
  simp only [joinCtxAt, List.mem_append] at hx ⊢
  rcases hx with ((h | h) | h) | h
  · exact Or.inl (Or.inl (Or.inl (mem_unionAll_filter_of_ctxEq _ hst h)))
  · refine Or.inl (Or.inl (Or.inr ?_))
    have h' := mem_rm.mp h
    have hall := mem_interAll.mp h'.2
    refine mem_rm.mpr ⟨h'.1, mem_interAll.mpr (fun j => ?_)⟩
    have h'' := mem_atPart.mp (hall j)
    exact mem_atPart.mpr ⟨hth j h''.1, h''.2⟩
  · exact Or.inl (Or.inr (mem_unionAll_filter_of_ctxEq _ hst h))
  · refine Or.inr (mem_filter_mono' (fun y hy => ?_) (fun _ h => h) h)
    have hall := mem_interAll.mp hy
    refine mem_interAll.mpr (fun j => ?_)
    have h'' := mem_impPart.mp (hall j)
    exact mem_impPart.mpr ⟨hth j h''.1, h''.2⟩

/-- The full `⋈^∨` context is monotone under premise swap. -/
theorem joinCtxOr_mono {n : Nat}
    {stab th stab' th' : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form}
    (hst : ∀ j, stab j ≐ stab' j) (hth : ∀ j, th j ⊆ th' j) :
    joinCtxOr stab th rhs ⊆ joinCtxOr stab' th' rhs := by
  intro x hx
  simp only [joinCtxOr, List.mem_append] at hx ⊢
  rcases hx with ((h | h) | h) | h
  · exact Or.inl (Or.inl (Or.inl (mem_unionAll_filter_of_ctxEq _ hst h)))
  · refine Or.inl (Or.inl (Or.inr ?_))
    have hall := mem_interAll.mp h
    refine mem_interAll.mpr (fun j => ?_)
    have h' := mem_atPart.mp (hall j)
    exact mem_atPart.mpr ⟨hth j h'.1, h'.2⟩
  · exact Or.inl (Or.inr (mem_unionAll_filter_of_ctxEq _ hst h))
  · refine Or.inr (mem_filter_mono' (fun y hy => ?_) (fun _ h => h) h)
    have hall := mem_interAll.mp hy
    refine mem_interAll.mpr (fun j => ?_)
    have h'' := mem_impPart.mp (hall j)
    exact mem_impPart.mpr ⟨hth j h''.1, h''.2⟩

/-- The fallible modal component is monotone under premise swap. -/
theorem joinCtxCircF_mono {n : Nat}
    {stab th stab' th' : Fin (n + 1) → List Form}
    (hst : ∀ j, stab j ≐ stab' j) (hth : ∀ j, th j ⊆ th' j) :
    joinCtxCircF stab th ⊆ joinCtxCircF stab' th' := by
  intro x hx
  simp only [joinCtxCircF, List.mem_append] at hx ⊢
  rcases hx with h | h
  · exact Or.inl (mem_unionAll_filter_of_ctxEq _ hst h)
  · refine Or.inr ?_
    have hall := mem_interAll.mp h
    refine mem_interAll.mpr (fun j => ?_)
    have h' := mem_circPart.mp (hall j)
    exact mem_circPart.mpr ⟨hth j h'.1, h'.2⟩

/-- **T-B for the fallible `⋈^At`.** -/
def joinAtF_mono {G : Form} {n : Nat}
    {stab th stab' th' : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form} {F : Form}
    (prem' : ∀ j, FRJWi G (stab' j) (th' j) (rhs j))
    (hst : ∀ j, stab' j ≐ stab j) (hth : ∀ j, th j ⊆ th' j)
    (hJ1 : ∀ i j, i ≠ j → stab i ⊆ stab j ++ th j)
    (hJ2 : ∀ A B : Form,
      Form.imp A B ∈ unionAll (fun j => impPart (stab j)) →
      A ∈ upsilon rhs)
    (hF : F.isPrime)
    (hFnot : F ∉ unionAll (fun j => atPart (stab j)))
    (hgoal : F ∈ sfR G) :
    FRJWr G .blocked (joinCtxAtF stab' th' rhs F) F :=
  .joinAtF prem' (hJ1_of_swap hst hth hJ1) (hJ2_strict_of_swap hst hJ2)
    hF (fun hmem => hFnot (mem_unionAll_filter_of_ctxEq _ hst hmem))
    hgoal (CtxEq.refl _)

/-- Subsumption side of `joinAtF_mono`. -/
theorem joinCtxAtF_mono {n : Nat}
    {stab th stab' th' : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form} {F : Form}
    (hst : ∀ j, stab j ≐ stab' j) (hth : ∀ j, th j ⊆ th' j) :
    joinCtxAtF stab th rhs F ⊆ joinCtxAtF stab' th' rhs F := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact List.mem_append_left _ (joinCtxAt_mono hst hth h)
  · exact List.mem_append_right _ (joinCtxCircF_mono hst hth h)

/-- **T-B for the fallible `⋈^∨`.** -/
def joinOrF_mono {G : Form} {n : Nat}
    {stab th stab' th' : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form} {C₁ C₂ : Form}
    (prem' : ∀ j, FRJWi G (stab' j) (th' j) (rhs j))
    (hst : ∀ j, stab' j ≐ stab j) (hth : ∀ j, th j ⊆ th' j)
    (hJ1 : ∀ i j, i ≠ j → stab i ⊆ stab j ++ th j)
    (hJ2 : ∀ A B : Form,
      Form.imp A B ∈ unionAll (fun j => impPart (stab j)) →
      A ∈ upsilon rhs)
    (hC : C₁ ∈ upsilon rhs ∧ C₂ ∈ upsilon rhs)
    (hgoal : Form.or C₁ C₂ ∈ sfR G) :
    FRJWr G .blocked (joinCtxOrF stab' th' rhs) (.or C₁ C₂) :=
  .joinOrF prem' (hJ1_of_swap hst hth hJ1) (hJ2_strict_of_swap hst hJ2)
    hC hgoal (CtxEq.refl _)

/-- Subsumption side of `joinOrF_mono`. -/
theorem joinCtxOrF_mono {n : Nat}
    {stab th stab' th' : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form}
    (hst : ∀ j, stab j ≐ stab' j) (hth : ∀ j, th j ⊆ th' j) :
    joinCtxOrF stab th rhs ⊆ joinCtxOrF stab' th' rhs := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact List.mem_append_left _ (joinCtxOr_mono hst hth h)
  · exact List.mem_append_right _ (joinCtxCircF_mono hst hth h)

/-! ## T-B: the promise joins

The double swap: the irregular family moves to subsumers (`≐` stable
zones, larger second zones) AND the promise family moves to subsumers
(larger contexts, tags up the retention order at the same goals `Dᵢ`).
The restriction filters `Θ^◯/Cl(Δ⃗)` and `·/Cl(Δ⃗)` are monotone in the
list and in the predicate (`mem_filter_mono'`), the pledges ride
`pledge_of_le`, and the conclusion keeps its tag, so subsumption closes
by `tagLeB` reflexivity. -/

theorem tagLeB_refl : ∀ t : Tag, tagLeB t t = true
  | .barren => rfl
  | .chain _ => by simp [tagLeB]
  | .blocked => rfl

theorem inRestrictC_mono {k : Nat} {Δs Δs' : Fin (k + 1) → List Form}
    (hΔ : ∀ i, Δs i ⊆ Δs' i) :
    ∀ f, inRestrictC Δs f = true → inRestrictC Δs' f = true := by
  intro f hf
  cases f with
  | circ Y =>
      simp only [inRestrictC, List.any_eq_true] at hf ⊢
      obtain ⟨i, hi, hb⟩ := hf
      exact ⟨i, hi, cloB_iff.mpr (clo_mono (hΔ i) (cloB_iff.mp hb))⟩
  | atom p => simp [inRestrictC] at hf
  | bot => simp [inRestrictC] at hf
  | and Z₁ Z₂ => simp [inRestrictC] at hf
  | or Z₁ Z₂ => simp [inRestrictC] at hf
  | imp A B => simp [inRestrictC] at hf

theorem cloAllB_mono {k : Nat} {Δs Δs' : Fin (k + 1) → List Form}
    (hΔ : ∀ i, Δs i ⊆ Δs' i) :
    ∀ x, cloAllB Δs x = true → cloAllB Δs' x = true := by
  intro x hx
  simp only [cloAllB, List.all_eq_true] at hx ⊢
  exact fun i hi => cloB_iff.mpr (clo_mono (hΔ i) (cloB_iff.mp (hx i hi)))

/-- The promise modal component is monotone under the double swap. -/
theorem joinCtxCircP_mono {n k : Nat}
    {stab th stab' th' : Fin (n + 1) → List Form}
    {Δs Δs' : Fin (k + 1) → List Form}
    (hst : ∀ j, stab j ≐ stab' j) (hth : ∀ j, th j ⊆ th' j)
    (hΔ : ∀ i, Δs i ⊆ Δs' i) :
    joinCtxCircP stab th Δs ⊆ joinCtxCircP stab' th' Δs' := by
  intro x hx
  simp only [joinCtxCircP, restrictC, List.mem_append] at hx ⊢
  rcases hx with h | h
  · exact Or.inl (mem_unionAll_filter_of_ctxEq _ hst h)
  · refine Or.inr (mem_filter_mono' (fun y hy => ?_) (inRestrictC_mono hΔ) h)
    have hall := mem_interAll.mp hy
    refine mem_interAll.mpr (fun j => ?_)
    have h' := mem_circPart.mp (hall j)
    exact mem_circPart.mpr ⟨hth j h'.1, h'.2⟩

/-- The promise `⋈^At` conclusion context is monotone under the double
swap. -/
theorem joinCtxAtP_mono {n k : Nat}
    {stab th stab' th' : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form} {F : Form}
    {Δs Δs' : Fin (k + 1) → List Form}
    (hst : ∀ j, stab j ≐ stab' j) (hth : ∀ j, th j ⊆ th' j)
    (hΔ : ∀ i, Δs i ⊆ Δs' i) :
    joinCtxAtP stab th rhs F Δs ⊆ joinCtxAtP stab' th' rhs F Δs' := by
  simp only [joinCtxAtP, restrictP]
  refine mem_filter_mono' (fun y hy => ?_) (cloAllB_mono hΔ)
  rcases List.mem_append.mp hy with h | h
  · exact List.mem_append_left _ (joinCtxAt_mono hst hth h)
  · exact List.mem_append_right _ (joinCtxCircP_mono hst hth hΔ h)

/-- The promise `⋈^∨` conclusion context is monotone under the double
swap. -/
theorem joinCtxOrP_mono {n k : Nat}
    {stab th stab' th' : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form}
    {Δs Δs' : Fin (k + 1) → List Form}
    (hst : ∀ j, stab j ≐ stab' j) (hth : ∀ j, th j ⊆ th' j)
    (hΔ : ∀ i, Δs i ⊆ Δs' i) :
    joinCtxOrP stab th rhs Δs ⊆ joinCtxOrP stab' th' rhs Δs' := by
  simp only [joinCtxOrP, restrictP]
  refine mem_filter_mono' (fun y hy => ?_) (cloAllB_mono hΔ)
  rcases List.mem_append.mp hy with h | h
  · exact List.mem_append_left _ (joinCtxOr_mono hst hth h)
  · exact List.mem_append_right _ (joinCtxCircP_mono hst hth hΔ h)

/-- (J5) transfers to the double swap. -/
theorem hJ5_of_swap {n k : Nat}
    {stab stab' : Fin (n + 1) → List Form}
    {Δs Δs' : Fin (k + 1) → List Form}
    (hst : ∀ j, stab' j ≐ stab j) (hΔ : ∀ i, Δs i ⊆ Δs' i)
    (hJ5 : ∀ Y : Form,
      Form.circ Y ∈ unionAll (fun j => circPart (stab j)) →
      ∃ i, Clo (Δs i) Y) :
    ∀ Y : Form, Form.circ Y ∈ unionAll (fun j => circPart (stab' j)) →
      ∃ i, Clo (Δs' i) Y := by
  intro Y hY
  obtain ⟨i, hi⟩ := hJ5 Y (mem_unionAll_filter_of_ctxEq _ hst hY)
  exact ⟨i, clo_mono (hΔ i) hi⟩

/-- (J7) transfers to the double swap. -/
theorem hJ7s_of_swap {n k : Nat}
    {stab stab' : Fin (n + 1) → List Form}
    {Δs Δs' : Fin (k + 1) → List Form}
    (hst : ∀ j, stab' j ≐ stab j) (hΔ : ∀ i, Δs i ⊆ Δs' i)
    (hJ7s : ∀ i j, ∀ X ∈ stab j, Clo (Δs i) X) :
    ∀ i j, ∀ X ∈ stab' j, Clo (Δs' i) X :=
  fun i j X hX => clo_mono (hΔ i) (hJ7s i j X ((hst j X).mp hX))

/-- **T-B for the promise `⋈^At`.**  The conclusion keeps its tag `t'`;
the blocked branch needs nothing, the chain branch sends each
component's pledge through `pledge_of_le`. -/
def joinAtP_mono {G : Form} {n k : Nat}
    {stab th stab' th' : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form} {F : Form} {t' : Tag}
    {tps tps' : Fin (k + 1) → Tag} {Δs Δs' : Fin (k + 1) → List Form}
    {Ds : Fin (k + 1) → Form}
    (prem' : ∀ j, FRJWi G (stab' j) (th' j) (rhs j))
    (dps' : ∀ i, FRJWr G (tps' i) (Δs' i) (Ds i))
    (hst : ∀ j, stab' j ≐ stab j) (hth : ∀ j, th j ⊆ th' j)
    (hΔ : ∀ i, Δs i ⊆ Δs' i)
    (hlep : ∀ i, tagLeB (tps i) (tps' i) = true)
    (hJ1 : ∀ i j, i ≠ j → stab i ⊆ stab j ++ th j)
    (hJ2 : ∀ A B : Form,
      Form.imp A B ∈ unionAll (fun j => impPart (stab j)) →
      A ∈ upsilon rhs)
    (hJ5 : ∀ Y : Form,
      Form.circ Y ∈ unionAll (fun j => circPart (stab j)) →
      ∃ i, Clo (Δs i) Y)
    (hJ7s : ∀ i j, ∀ X ∈ stab j, Clo (Δs i) X)
    (htag : t' = .blocked ∨ (t' = .chain (Ds 0) ∧ ∀ i, Ds i = Ds 0 ∧
      (tps i = .barren ∨ ∃ W, tps i = .chain W ∧ Covers (Δs i) W (Ds 0))))
    (hF : F.isPrime)
    (hFnot : F ∉ unionAll (fun j => atPart (stab j)))
    (hgoal : F ∈ sfR G) :
    FRJWr G t' (joinCtxAtP stab' th' rhs F Δs') F :=
  .joinAtP prem' dps' (hJ1_of_swap hst hth hJ1)
    (hJ2_strict_of_swap hst hJ2)
    (hJ5_of_swap hst hΔ hJ5) (hJ7s_of_swap hst hΔ hJ7s)
    (htag.imp id (fun ⟨h0, hall⟩ =>
      ⟨h0, fun i => ⟨(hall i).1,
        pledge_of_le (hlep i) (hΔ i) (hall i).2⟩⟩))
    hF (fun hmem => hFnot (mem_unionAll_filter_of_ctxEq _ hst hmem))
    hgoal (CtxEq.refl _)

/-- **T-B for the promise `⋈^∨`.** -/
def joinOrP_mono {G : Form} {n k : Nat}
    {stab th stab' th' : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form} {C₁ C₂ : Form} {t' : Tag}
    {tps tps' : Fin (k + 1) → Tag} {Δs Δs' : Fin (k + 1) → List Form}
    {Ds : Fin (k + 1) → Form}
    (prem' : ∀ j, FRJWi G (stab' j) (th' j) (rhs j))
    (dps' : ∀ i, FRJWr G (tps' i) (Δs' i) (Ds i))
    (hst : ∀ j, stab' j ≐ stab j) (hth : ∀ j, th j ⊆ th' j)
    (hΔ : ∀ i, Δs i ⊆ Δs' i)
    (hlep : ∀ i, tagLeB (tps i) (tps' i) = true)
    (hJ1 : ∀ i j, i ≠ j → stab i ⊆ stab j ++ th j)
    (hJ2 : ∀ A B : Form,
      Form.imp A B ∈ unionAll (fun j => impPart (stab j)) →
      A ∈ upsilon rhs)
    (hJ5 : ∀ Y : Form,
      Form.circ Y ∈ unionAll (fun j => circPart (stab j)) →
      ∃ i, Clo (Δs i) Y)
    (hJ7s : ∀ i j, ∀ X ∈ stab j, Clo (Δs i) X)
    (htag : t' = .blocked ∨ (t' = .chain (Ds 0) ∧ ∀ i, Ds i = Ds 0 ∧
      (tps i = .barren ∨ ∃ W, tps i = .chain W ∧ Covers (Δs i) W (Ds 0))))
    (hC : C₁ ∈ upsilon rhs ∧ C₂ ∈ upsilon rhs)
    (hgoal : Form.or C₁ C₂ ∈ sfR G) :
    FRJWr G t' (joinCtxOrP stab' th' rhs Δs') (.or C₁ C₂) :=
  .joinOrP prem' dps' (hJ1_of_swap hst hth hJ1)
    (hJ2_strict_of_swap hst hJ2)
    (hJ5_of_swap hst hΔ hJ5) (hJ7s_of_swap hst hΔ hJ7s)
    (htag.imp id (fun ⟨h0, hall⟩ =>
      ⟨h0, fun i => ⟨(hall i).1,
        pledge_of_le (hlep i) (hΔ i) (hall i).2⟩⟩))
    hC hgoal (CtxEq.refl _)

/-- **T-B for the promise `⋈^◯`.**  The conclusion tag `chain Z` is
forced by the rule and shared by old and new, so subsumption closes at
equal pledge. -/
def joinCircP_mono {G : Form} {n k : Nat}
    {stab th stab' th' : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form} {Z : Form}
    {tps tps' : Fin (k + 1) → Tag} {Δs Δs' : Fin (k + 1) → List Form}
    {Ds : Fin (k + 1) → Form}
    (prem' : ∀ j, FRJWi G (stab' j) (th' j) (rhs j))
    (dps' : ∀ i, FRJWr G (tps' i) (Δs' i) (Ds i))
    (hst : ∀ j, stab' j ≐ stab j) (hth : ∀ j, th j ⊆ th' j)
    (hΔ : ∀ i, Δs i ⊆ Δs' i)
    (hlep : ∀ i, tagLeB (tps i) (tps' i) = true)
    (hJ1 : ∀ i j, i ≠ j → stab i ⊆ stab j ++ th j)
    (hJ2 : ∀ A B : Form,
      Form.imp A B ∈ unionAll (fun j => impPart (stab j)) →
      A ∈ upsilon rhs)
    (hJ5 : ∀ Y : Form,
      Form.circ Y ∈ unionAll (fun j => circPart (stab j)) →
      ∃ i, Clo (Δs i) Y)
    (hJ7s : ∀ i j, ∀ X ∈ stab j, Clo (Δs i) X)
    (hDs : ∀ i, Ds i = Z ∧
      (tps i = .barren ∨ ∃ W, tps i = .chain W ∧ Covers (Δs i) W Z))
    (hZ : Z ∈ upsilon rhs)
    (hgoal : Form.circ Z ∈ sfR G) :
    FRJWr G (.chain Z) (joinCtxOrP stab' th' rhs Δs') (.circ Z) :=
  .joinCircP prem' dps' (hJ1_of_swap hst hth hJ1)
    (hJ2_strict_of_swap hst hJ2)
    (hJ5_of_swap hst hΔ hJ5) (hJ7s_of_swap hst hΔ hJ7s)
    (fun i => ⟨(hDs i).1, pledge_of_le (hlep i) (hΔ i) (hDs i).2⟩)
    hZ hgoal (CtxEq.refl _)

/-! ## Wellformedness for the finite universe

`wfR`/`wfI` (FRJ/StepW.lean) bound every derivable context inside `Ĝ`.
The closure computation's termination argument needs two more bounds:
the goal and the pledge live in `Sf^R(G)`.  Together the three confine
every derivable row to a finite canonical universe. -/

mutual

/-- Every derivable regular goal is a right signed subformula. -/
theorem goalWr {G : Form} : ∀ {t : Tag} {Γ : List Form} {C : Form},
    FRJWr G t Γ C → C ∈ sfR G
  | _, _, _, .axR _ _ hg _ => hg
  | _, _, _, .andR1 _ hg => hg
  | _, _, _, .andR2 _ hg => hg
  | _, _, _, .impIn _ _ hg => hg
  | _, _, _, .circIn _ _ hg => hg
  | _, _, _, .joinAt _ _ _ _ _ _ _ hg _ => hg
  | _, _, _, .joinAtP _ _ _ _ _ _ _ _ _ hg _ => hg
  | _, _, _, .joinAtF _ _ _ _ _ hg _ => hg
  | _, _, _, .joinOr _ _ _ _ _ _ hg _ => hg
  | _, _, _, .joinOrP _ _ _ _ _ _ _ _ hg _ => hg
  | _, _, _, .joinOrF _ _ _ _ hg _ => hg
  | _, _, _, .joinCirc _ _ _ _ _ _ hg _ => hg
  | _, _, _, .joinCircP _ _ _ _ _ _ _ _ hg _ => hg

/-- Every derivable irregular goal is a right signed subformula (`lift`
inherits it from its regular premise — the one rule with no `hgoal`). -/
theorem goalWi {G : Form} : ∀ {St Th : List Form} {C : Form},
    FRJWi G St Th C → C ∈ sfR G
  | _, _, _, .axI _ _ hg _ => hg
  | _, _, _, .andI1 _ hg => hg
  | _, _, _, .andI2 _ hg => hg
  | _, _, _, .orI _ _ _ _ hg _ _ => hg
  | _, _, _, .impInI _ _ _ _ hg _ _ => hg
  | _, _, _, .lift d _ => goalWr d
  | _, _, _, .circNotIn _ _ _ hg => hg
  | _, _, _, .axIC _ _ _ _ hg _ => hg

end

/-- Every derivable tag is `barren`, `blocked`, or a chain pledged on a
right signed subformula: the chain producers pledge a promise goal
(`goalWr` of the promise component) or the join goal's body
(`sfR_circ`), and the unary rules preserve the tag. -/
theorem tagWr {G : Form} : ∀ {t : Tag} {Γ : List Form} {C : Form},
    FRJWr G t Γ C →
      t = .barren ∨ t = .blocked ∨ ∃ W, t = .chain W ∧ W ∈ sfR G
  | _, _, _, .axR _ _ _ _ => Or.inl rfl
  | _, _, _, .andR1 d _ => tagWr d
  | _, _, _, .andR2 d _ => tagWr d
  | _, _, _, .impIn d _ _ => tagWr d
  | _, _, _, .circIn d _ _ => tagWr d
  | _, _, _, .joinAt _ _ _ _ _ _ _ _ _ => Or.inl rfl
  | _, _, _, .joinAtP _ dps _ _ _ _ htag _ _ _ _ =>
      htag.elim (fun h => Or.inr (Or.inl h))
        (fun h => Or.inr (Or.inr ⟨_, h.1, goalWr (dps 0)⟩))
  | _, _, _, .joinAtF _ _ _ _ _ _ _ => Or.inr (Or.inl rfl)
  | _, _, _, .joinOr _ _ _ _ _ _ _ _ => Or.inl rfl
  | _, _, _, .joinOrP _ dps _ _ _ _ htag _ _ _ =>
      htag.elim (fun h => Or.inr (Or.inl h))
        (fun h => Or.inr (Or.inr ⟨_, h.1, goalWr (dps 0)⟩))
  | _, _, _, .joinOrF _ _ _ _ _ _ => Or.inr (Or.inl rfl)
  | _, _, _, .joinCirc _ _ _ _ _ _ _ _ => Or.inl rfl
  | _, _, _, .joinCircP _ _ _ _ _ _ _ _ hg _ =>
      Or.inr (Or.inr ⟨_, rfl, sfR_circ hg⟩)

/-! ## The assembly: `decideGbuW` modulo the closed database

Everything below reduces `decideGbuW` to ONE hypothesis: a
derivation-carrying row list subsuming every derivable row
(`WSaturated.2` for its membership predicate).  Rows carry their
derivations as DATA (`WRow`), so `WSaturated.1` needs no choice; the
deciders are finite scans over the list. -/

namespace Gbu.W

/-- The derivation of a database sequent, as data. -/
def WDer (G : Form) : WSeq → Type
  | .reg t Γ C => FRJWr G t Γ C
  | .irr St Th C => FRJWi G St Th C

/-- A stored row: the sequent with its derivation. -/
structure WRow (G : Form) where
  s : WSeq
  d : WDer G s

theorem wDerivable_of_wDer {G : Form} :
    ∀ {s : WSeq}, WDer G s → WDerivable G s
  | .reg _ _ _, d => ⟨d⟩
  | .irr _ _ _, d => ⟨d⟩

/-- Subsumption is reflexive (`tagLeB_refl` at the tag). -/
theorem wSubsumes_refl : ∀ s : WSeq, WSubsumes s s
  | .reg t _ _ => ⟨rfl, tagLeB_refl t, fun _ h => h⟩
  | .irr _ _ _ => ⟨rfl, CtxEq.refl _, fun _ h => h⟩

theorem tagLeB_trans : ∀ {t₁ t₂ t₃ : Tag}, tagLeB t₁ t₂ = true →
    tagLeB t₂ t₃ = true → tagLeB t₁ t₃ = true := by
  intro t₁ t₂ t₃ h₁ h₂
  cases t₁ <;> cases t₂ <;> cases t₃ <;> simp_all [tagLeB]

/-- Subsumption is transitive. -/
theorem wSubsumes_trans {s₁ s₂ s₃ : WSeq} (h₁ : WSubsumes s₁ s₂)
    (h₂ : WSubsumes s₂ s₃) : WSubsumes s₁ s₃ := by
  cases s₁ with
  | reg t₁ Γ₁ C₁ =>
      cases s₂ with
      | reg t₂ Γ₂ C₂ =>
          cases s₃ with
          | reg t₃ Γ₃ C₃ =>
              obtain ⟨e₁, l₁, g₁⟩ := h₁
              obtain ⟨e₂, l₂, g₂⟩ := h₂
              exact ⟨e₁.trans e₂, tagLeB_trans l₁ l₂, fun _ hx => g₂ (g₁ hx)⟩
          | irr _ _ _ => exact h₂.elim
      | irr _ _ _ => exact h₁.elim
  | irr St₁ Th₁ C₁ =>
      cases s₂ with
      | reg _ _ _ => exact h₁.elim
      | irr St₂ Th₂ C₂ =>
          cases s₃ with
          | reg _ _ _ => exact h₂.elim
          | irr St₃ Th₃ C₃ =>
              obtain ⟨e₁, q₁, g₁⟩ := h₁
              obtain ⟨e₂, q₂, g₂⟩ := h₂
              exact ⟨e₁.trans e₂, q₁.trans q₂, fun _ hx => g₂ (g₁ hx)⟩

/-! ### The deciders: finite scans over the stored list -/

/-- The irregular query is decidable over a stored list. -/
def decWEvalI (rows : List WSeq) (Ω : List Form) (C : Form) :
    Decidable (WEvalI (· ∈ rows) Ω C) :=
  decidable_of_iff (rows.any (fun s =>
      match s with
      | .irr St Th C' =>
          decide (C' = C) && subB St Ω && subB Ω (St ++ Th)
      | _ => false) = true) (by
    simp only [List.any_eq_true]
    constructor
    · rintro ⟨s, hs, hp⟩
      match s, hp with
      | .irr St Th C', hp =>
          simp only [Bool.and_eq_true, decide_eq_true_eq, subB,
            List.all_eq_true, decide_eq_true_eq] at hp
          obtain ⟨⟨hC, hSt⟩, hΩ⟩ := hp
          subst hC
          exact ⟨St, Th, hs, fun x hx => hSt x hx, fun x hx => hΩ x hx⟩
    · rintro ⟨St, Th, hmem, hSt, hΩ⟩
      refine ⟨.irr St Th C, hmem, ?_⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq, subB,
        List.all_eq_true, decide_eq_true_eq]
      exact ⟨⟨trivial, fun x hx => hSt hx⟩, fun x hx => hΩ hx⟩)

/-- The plain regular query is decidable over a stored list. -/
def decWEvalR (rows : List WSeq) (Ψ : List Form) (C : Form) :
    Decidable (WEvalR (· ∈ rows) Ψ C) :=
  decidable_of_iff (rows.any (fun s =>
      match s with
      | .reg _ Γ C' => decide (C' = C) && Ψ.all (cloB Γ)
      | _ => false) = true) (by
    simp only [List.any_eq_true]
    constructor
    · rintro ⟨s, hs, hp⟩
      match s, hp with
      | .reg t Γ C', hp =>
          simp only [Bool.and_eq_true, decide_eq_true_eq,
            List.all_eq_true] at hp
          obtain ⟨hC, hclo⟩ := hp
          subst hC
          exact ⟨t, Γ, hs, fun X hX => cloB_iff.mp (hclo X hX)⟩
    · rintro ⟨t, Γ, hmem, hclo⟩
      refine ⟨.reg t Γ C, hmem, ?_⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
      exact ⟨trivial, fun X hX => cloB_iff.mpr (hclo X hX)⟩)

/-- The pledged regular query is decidable over a stored list
(`decPledge` supplies the tag test). -/
def decWEvalRP (rows : List WSeq) (Ψ : List Form) (C : Form) :
    Decidable (WEvalRP (· ∈ rows) Ψ C) :=
  decidable_of_iff (rows.any (fun s =>
      match s with
      | .reg t Γ C' =>
          decide (C' = C) && Ψ.all (cloB Γ) &&
            decide (t = .barren ∨ ∃ W, t = .chain W ∧ Covers Γ W C)
      | _ => false) = true) (by
    simp only [List.any_eq_true]
    constructor
    · rintro ⟨s, hs, hp⟩
      match s, hp with
      | .reg t Γ C', hp =>
          simp only [Bool.and_eq_true, decide_eq_true_eq,
            List.all_eq_true] at hp
          obtain ⟨⟨hC, hclo⟩, htag⟩ := hp
          subst hC
          exact ⟨t, Γ, hs, htag, fun X hX => cloB_iff.mp (hclo X hX)⟩
    · rintro ⟨t, Γ, hmem, htag, hclo⟩
      refine ⟨.reg t Γ C, hmem, ?_⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
      exact ⟨⟨trivial, fun X hX => cloB_iff.mpr (hclo X hX)⟩, htag⟩)

/-! ### The assembly -/

/-- A stored row list whose membership predicate subsumes every
derivable row is a saturated database. -/
theorem wsat_of_closed {G : Form} (db : List (WRow G))
    (h2 : ∀ s, WDerivable G s → ∃ r ∈ db, WSubsumes s r.s) :
    WSaturated G (fun s => s ∈ db.map (·.s)) := by
  constructor
  · intro s hs
    obtain ⟨r, _, hrs⟩ := List.mem_map.mp hs
    exact hrs ▸ wDerivable_of_wDer r.d
  · intro s hs
    obtain ⟨r, hr, hsub⟩ := h2 s hs
    exact ⟨r.s, List.mem_map.mpr ⟨r, hr, rfl⟩, hsub⟩

/-- **`decideGbuW`, modulo the closed database.**  From any
derivation-carrying row list subsuming every derivable row, the
simultaneous decision follows through `dichotomyW`.  The construction
of such a list per `G` (the computed closure, T-C) is the ONLY
remaining obligation. -/
def decideGbuW_of {G : Form} (db : List (WRow G))
    (h2 : ∀ s, WDerivable G s → ∃ r ∈ db, WSubsumes s r.s) :
    ProvableGbuC G ⊕' DisprovableW G :=
  match dichotomyW (wsat_of_closed db h2)
      (fun Ω C => decWEvalI (db.map (·.s)) Ω C)
      (decWEvalR (db.map (·.s)) [] G) with
  | .inl hdis => .inr hdis
  | .inr d => .inl ⟨d⟩

/-! ### Decidable subsumption and choice-free subsumer extraction

The T-C induction turns per-premise existence of stored subsumers into
FAMILIES (functions into zones) without choice: `List.find?` over the
decidable subsumption test skolemises. -/

/-- Decision procedure for `WSubsumes`. -/
def subsumesB : WSeq → WSeq → Bool
  | .reg t₁ Γ₁ C₁, .reg t₂ Γ₂ C₂ =>
      decide (C₁ = C₂) && tagLeB t₁ t₂ && subB Γ₁ Γ₂
  | .irr St₁ Th₁ C₁, .irr St₂ Th₂ C₂ =>
      decide (C₁ = C₂) && subB St₁ St₂ && subB St₂ St₁ && subB Th₁ Th₂
  | _, _ => false

theorem subsumesB_iff : ∀ {s₁ s₂ : WSeq},
    subsumesB s₁ s₂ = true ↔ WSubsumes s₁ s₂ := by
  intro s₁ s₂
  cases s₁ with
  | reg t₁ Γ₁ C₁ =>
      cases s₂ with
      | reg t₂ Γ₂ C₂ =>
          simp only [subsumesB, WSubsumes, Bool.and_eq_true,
            decide_eq_true_eq, subB, List.all_eq_true, decide_eq_true_eq]
          constructor
          · rintro ⟨⟨hC, hle⟩, hsub⟩
            exact ⟨hC, hle, fun x hx => hsub x hx⟩
          · rintro ⟨hC, hle, hsub⟩
            exact ⟨⟨hC, hle⟩, fun x hx => hsub hx⟩
      | irr _ _ _ =>
          simp only [subsumesB, WSubsumes]
          exact ⟨fun h => Bool.noConfusion h, False.elim⟩
  | irr St₁ Th₁ C₁ =>
      cases s₂ with
      | reg _ _ _ =>
          simp only [subsumesB, WSubsumes]
          exact ⟨fun h => Bool.noConfusion h, False.elim⟩
      | irr St₂ Th₂ C₂ =>
          simp only [subsumesB, WSubsumes, Bool.and_eq_true,
            decide_eq_true_eq, subB, List.all_eq_true, decide_eq_true_eq]
          constructor
          · rintro ⟨⟨⟨hC, h₁⟩, h₂⟩, hTh⟩
            exact ⟨hC, fun x => ⟨fun hx => h₁ x hx, fun hx => h₂ x hx⟩,
              fun x hx => hTh x hx⟩
          · rintro ⟨hC, hq, hTh⟩
            exact ⟨⟨⟨hC, fun x hx => (hq x).mp hx⟩,
              fun x hx => (hq x).mpr hx⟩, fun x hx => hTh hx⟩

instance decWSubsumes (s₁ s₂ : WSeq) : Decidable (WSubsumes s₁ s₂) :=
  decidable_of_iff _ subsumesB_iff

/-- The first stored subsumer of `s`, if any. -/
def findSub {G : Form} (db : List (WRow G)) (s : WSeq) : Option (WRow G) :=
  db.find? (fun r => subsumesB s r.s)

theorem findSub_isSome_of_exists {G : Form} {db : List (WRow G)} {s : WSeq}
    (h : ∃ r ∈ db, WSubsumes s r.s) : (findSub db s).isSome := by
  obtain ⟨r, hr, hsub⟩ := h
  simp only [findSub]
  exact List.find?_isSome.mpr ⟨r, hr, subsumesB_iff.mpr hsub⟩

theorem findSub_mem {G : Form} {db : List (WRow G)} {s : WSeq} {r : WRow G}
    (h : findSub db s = some r) : r ∈ db := by
  have h' : db.find? (fun r => subsumesB s r.s) = some r := by
    simpa [findSub] using h
  exact List.mem_of_find?_eq_some h'

theorem findSub_sub {G : Form} {db : List (WRow G)} {s : WSeq} {r : WRow G}
    (h : findSub db s = some r) : WSubsumes s r.s := by
  have h' : db.find? (fun r => subsumesB s r.s) = some r := by
    simpa [findSub] using h
  exact subsumesB_iff.mp (by simpa using List.find?_some h')


/-! ### The closedness interface: one clause per rule

`DBClosed G db` says: every rule fired at STORED premise sequents, with
its canonical kept chain and canonical conclusion context, has a stored
subsumer.  The T-C induction below turns this into `WSaturated.2`; the
closure computation's job (the last open layer) is to construct a `db`
satisfying it, using the T-B `_mono` defs to carry the derivations. -/

structure DBClosed (G : Form) (db : List (WRow G)) : Prop where
  axR : ∀ F : Form, F.isPrime → F ∈ sfR G →
    ∃ r ∈ db, WSubsumes (.reg .barren (rm (gAt G) F) F) r.s
  andR1 : ∀ (t : Tag) (Γ : List Form) (A₁ A₂ : Form),
    (WSeq.reg t Γ A₁) ∈ db.map (·.s) → Form.and A₁ A₂ ∈ sfR G →
    ∃ r ∈ db, WSubsumes (.reg t Γ (.and A₁ A₂)) r.s
  andR2 : ∀ (t : Tag) (Γ : List Form) (A₁ A₂ : Form),
    (WSeq.reg t Γ A₂) ∈ db.map (·.s) → Form.and A₁ A₂ ∈ sfR G →
    ∃ r ∈ db, WSubsumes (.reg t Γ (.and A₁ A₂)) r.s
  impIn : ∀ (t : Tag) (Γ : List Form) (A B : Form),
    (WSeq.reg t Γ B) ∈ db.map (·.s) → Clo Γ A → Form.imp A B ∈ sfR G →
    ∃ r ∈ db, WSubsumes (.reg t Γ (.imp A B)) r.s
  circIn : ∀ (t : Tag) (Γ : List Form) (Z : Form),
    (WSeq.reg t Γ Z) ∈ db.map (·.s) →
    (t = .barren ∨ ∃ W, t = .chain W ∧ Covers Γ W Z) →
    Form.circ Z ∈ sfR G →
    ∃ r ∈ db, WSubsumes (.reg t Γ (.circ Z)) r.s
  joinAt : ∀ {n : Nat} (stab th : Fin (n + 1) → List Form)
    (rhs : Fin (n + 1) → Form) (F : Form),
    (∀ j, (WSeq.irr (stab j) (th j) (rhs j)) ∈ db.map (·.s)) →
    (∀ i j, i ≠ j → stab i ⊆ stab j ++ th j) →
    (∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (stab j)) →
      A ∈ upsilon rhs) →
    unionAll (fun j => circPart (stab j)) = [] →
    F.isPrime → F ∉ unionAll (fun j => atPart (stab j)) → F ∈ sfR G →
    ∃ r ∈ db, WSubsumes
      (.reg .barren (joinCtxAtVBase stab th F ++
        keptOf (upsilon rhs) (joinCtxAtVBase stab th F) (thPool th)) F) r.s
  joinOr : ∀ {n : Nat} (stab th : Fin (n + 1) → List Form)
    (rhs : Fin (n + 1) → Form) (C₁ C₂ : Form),
    (∀ j, (WSeq.irr (stab j) (th j) (rhs j)) ∈ db.map (·.s)) →
    (∀ i j, i ≠ j → stab i ⊆ stab j ++ th j) →
    (∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (stab j)) →
      A ∈ upsilon rhs) →
    unionAll (fun j => circPart (stab j)) = [] →
    (RefAt true (upsilon rhs) (joinCtxOrVBase stab th ++
        keptOf (upsilon rhs) (joinCtxOrVBase stab th) (thPool th)) C₁ ∧
      RefAt true (upsilon rhs) (joinCtxOrVBase stab th ++
        keptOf (upsilon rhs) (joinCtxOrVBase stab th) (thPool th)) C₂) →
    Form.or C₁ C₂ ∈ sfR G →
    ∃ r ∈ db, WSubsumes
      (.reg .barren (joinCtxOrVBase stab th ++
        keptOf (upsilon rhs) (joinCtxOrVBase stab th) (thPool th))
        (.or C₁ C₂)) r.s
  joinCirc : ∀ {n : Nat} (stab th : Fin (n + 1) → List Form)
    (rhs : Fin (n + 1) → Form) (Z : Form),
    (∀ j, (WSeq.irr (stab j) (th j) (rhs j)) ∈ db.map (·.s)) →
    (∀ i j, i ≠ j → stab i ⊆ stab j ++ th j) →
    (∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (stab j)) →
      RefAt true (upsilon rhs) (joinCtxOrVBase stab th ++
        keptOf (upsilon rhs) (joinCtxOrVBase stab th) (thPool th)) A) →
    unionAll (fun j => circPart (stab j)) = [] →
    RefAt true (upsilon rhs) (joinCtxOrVBase stab th ++
      keptOf (upsilon rhs) (joinCtxOrVBase stab th) (thPool th)) Z →
    Form.circ Z ∈ sfR G →
    ∃ r ∈ db, WSubsumes
      (.reg .barren (joinCtxOrVBase stab th ++
        keptOf (upsilon rhs) (joinCtxOrVBase stab th) (thPool th))
        (.circ Z)) r.s
  joinAtP : ∀ {n k : Nat} (stab th : Fin (n + 1) → List Form)
    (rhs : Fin (n + 1) → Form) (F : Form) (t' : Tag)
    (tps : Fin (k + 1) → Tag) (Δs : Fin (k + 1) → List Form)
    (Ds : Fin (k + 1) → Form),
    (∀ j, (WSeq.irr (stab j) (th j) (rhs j)) ∈ db.map (·.s)) →
    (∀ i, (WSeq.reg (tps i) (Δs i) (Ds i)) ∈ db.map (·.s)) →
    (∀ i j, i ≠ j → stab i ⊆ stab j ++ th j) →
    (∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (stab j)) →
      A ∈ upsilon rhs) →
    (∀ Y : Form, Form.circ Y ∈ unionAll (fun j => circPart (stab j)) →
      ∃ i, Clo (Δs i) Y) →
    (∀ i j, ∀ X ∈ stab j, Clo (Δs i) X) →
    (t' = .blocked ∨ (t' = .chain (Ds 0) ∧ ∀ i, Ds i = Ds 0 ∧
      (tps i = .barren ∨ ∃ W, tps i = .chain W ∧ Covers (Δs i) W (Ds 0)))) →
    F.isPrime → F ∉ unionAll (fun j => atPart (stab j)) → F ∈ sfR G →
    ∃ r ∈ db, WSubsumes (.reg t' (joinCtxAtP stab th rhs F Δs) F) r.s
  joinOrP : ∀ {n k : Nat} (stab th : Fin (n + 1) → List Form)
    (rhs : Fin (n + 1) → Form) (C₁ C₂ : Form) (t' : Tag)
    (tps : Fin (k + 1) → Tag) (Δs : Fin (k + 1) → List Form)
    (Ds : Fin (k + 1) → Form),
    (∀ j, (WSeq.irr (stab j) (th j) (rhs j)) ∈ db.map (·.s)) →
    (∀ i, (WSeq.reg (tps i) (Δs i) (Ds i)) ∈ db.map (·.s)) →
    (∀ i j, i ≠ j → stab i ⊆ stab j ++ th j) →
    (∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (stab j)) →
      A ∈ upsilon rhs) →
    (∀ Y : Form, Form.circ Y ∈ unionAll (fun j => circPart (stab j)) →
      ∃ i, Clo (Δs i) Y) →
    (∀ i j, ∀ X ∈ stab j, Clo (Δs i) X) →
    (t' = .blocked ∨ (t' = .chain (Ds 0) ∧ ∀ i, Ds i = Ds 0 ∧
      (tps i = .barren ∨ ∃ W, tps i = .chain W ∧ Covers (Δs i) W (Ds 0)))) →
    (C₁ ∈ upsilon rhs ∧ C₂ ∈ upsilon rhs) →
    Form.or C₁ C₂ ∈ sfR G →
    ∃ r ∈ db, WSubsumes (.reg t' (joinCtxOrP stab th rhs Δs) (.or C₁ C₂)) r.s
  joinCircP : ∀ {n k : Nat} (stab th : Fin (n + 1) → List Form)
    (rhs : Fin (n + 1) → Form) (Z : Form)
    (tps : Fin (k + 1) → Tag) (Δs : Fin (k + 1) → List Form)
    (Ds : Fin (k + 1) → Form),
    (∀ j, (WSeq.irr (stab j) (th j) (rhs j)) ∈ db.map (·.s)) →
    (∀ i, (WSeq.reg (tps i) (Δs i) (Ds i)) ∈ db.map (·.s)) →
    (∀ i j, i ≠ j → stab i ⊆ stab j ++ th j) →
    (∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (stab j)) →
      A ∈ upsilon rhs) →
    (∀ Y : Form, Form.circ Y ∈ unionAll (fun j => circPart (stab j)) →
      ∃ i, Clo (Δs i) Y) →
    (∀ i j, ∀ X ∈ stab j, Clo (Δs i) X) →
    (∀ i, Ds i = Z ∧
      (tps i = .barren ∨ ∃ W, tps i = .chain W ∧ Covers (Δs i) W Z)) →
    Z ∈ upsilon rhs → Form.circ Z ∈ sfR G →
    ∃ r ∈ db, WSubsumes
      (.reg (.chain Z) (joinCtxOrP stab th rhs Δs) (.circ Z)) r.s
  joinAtF : ∀ {n : Nat} (stab th : Fin (n + 1) → List Form)
    (rhs : Fin (n + 1) → Form) (F : Form),
    (∀ j, (WSeq.irr (stab j) (th j) (rhs j)) ∈ db.map (·.s)) →
    (∀ i j, i ≠ j → stab i ⊆ stab j ++ th j) →
    (∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (stab j)) →
      A ∈ upsilon rhs) →
    F.isPrime → F ∉ unionAll (fun j => atPart (stab j)) → F ∈ sfR G →
    ∃ r ∈ db, WSubsumes (.reg .blocked (joinCtxAtF stab th rhs F) F) r.s
  joinOrF : ∀ {n : Nat} (stab th : Fin (n + 1) → List Form)
    (rhs : Fin (n + 1) → Form) (C₁ C₂ : Form),
    (∀ j, (WSeq.irr (stab j) (th j) (rhs j)) ∈ db.map (·.s)) →
    (∀ i j, i ≠ j → stab i ⊆ stab j ++ th j) →
    (∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (stab j)) →
      A ∈ upsilon rhs) →
    (C₁ ∈ upsilon rhs ∧ C₂ ∈ upsilon rhs) →
    Form.or C₁ C₂ ∈ sfR G →
    ∃ r ∈ db, WSubsumes
      (.reg .blocked (joinCtxOrF stab th rhs) (.or C₁ C₂)) r.s
  axI : ∀ F : Form, F.isPrime → F ∈ sfR G →
    ∃ r ∈ db, WSubsumes
      (.irr [] (rm (gAt G) F ++ gImp G ++ gCirc G) F) r.s
  andI1 : ∀ (St Th : List Form) (A₁ A₂ : Form),
    (WSeq.irr St Th A₁) ∈ db.map (·.s) → Form.and A₁ A₂ ∈ sfR G →
    ∃ r ∈ db, WSubsumes (.irr St Th (.and A₁ A₂)) r.s
  andI2 : ∀ (St Th : List Form) (A₁ A₂ : Form),
    (WSeq.irr St Th A₂) ∈ db.map (·.s) → Form.and A₁ A₂ ∈ sfR G →
    ∃ r ∈ db, WSubsumes (.irr St Th (.and A₁ A₂)) r.s
  orI : ∀ (St₁ Th₁ St₂ Th₂ : List Form) (C₁ C₂ : Form),
    (WSeq.irr St₁ Th₁ C₁) ∈ db.map (·.s) →
    (WSeq.irr St₂ Th₂ C₂) ∈ db.map (·.s) →
    St₁ ⊆ St₂ ++ Th₂ → St₂ ⊆ St₁ ++ Th₁ →
    Form.or C₁ C₂ ∈ sfR G →
    ∃ r ∈ db, WSubsumes (.irr (St₁ ++ St₂) (cap Th₁ Th₂) (.or C₁ C₂)) r.s
  impInI : ∀ (St₂ ThLam₂ Lam : List Form) (A B : Form),
    (WSeq.irr St₂ ThLam₂ B) ∈ db.map (·.s) →
    Clo (St₂ ++ ThLam₂.filter (fun x => decide (x ∈ Lam))) A →
    Form.imp A B ∈ sfR G →
    ∃ r ∈ db, WSubsumes
      (.irr (St₂ ++ ThLam₂.filter (fun x => decide (x ∈ Lam)))
        (ThLam₂.filter (fun x => !decide (x ∈ Lam))) (.imp A B)) r.s
  lift : ∀ (t₂ : Tag) (Γ₂ : List Form) (C : Form),
    (WSeq.reg t₂ Γ₂ C) ∈ db.map (·.s) →
    ∃ r ∈ db, WSubsumes (.irr [] (maxTh G Γ₂) C) r.s
  circNotIn : ∀ (t₂ : Tag) (Γ₂ : List Form) (Z : Form),
    (WSeq.reg t₂ Γ₂ Z) ∈ db.map (·.s) →
    (t₂ = .barren ∨ ∃ W, t₂ = .chain W ∧ Covers Γ₂ W Z) →
    Form.circ Z ∈ sfR G →
    ∃ r ∈ db, WSubsumes (.irr [] (maxTh G Γ₂) (.circ Z)) r.s
  axIC : ∀ (F : Form) (ats : List Form), ats ⊆ gAt G →
    classForce ats F = false → Form.circ F ∈ sfR G →
    ∃ r ∈ db, WSubsumes (.irr [] (vacZoneA G ats) (.circ F)) r.s

/-! ### Shape extraction from a subsumption -/

def tagOf : WSeq → Tag
  | .reg t _ _ => t
  | .irr _ _ _ => .blocked

def ctxOf : WSeq → List Form
  | .reg _ Γ _ => Γ
  | .irr St Th _ => St ++ Th

def stabOf : WSeq → List Form
  | .irr St _ _ => St
  | .reg _ Γ _ => Γ

def thOf : WSeq → List Form
  | .irr _ Th _ => Th
  | .reg _ _ _ => []

theorem irr_shape {St Th : List Form} {C : Form} :
    ∀ {s : WSeq}, WSubsumes (.irr St Th C) s →
      s = .irr (stabOf s) (thOf s) C ∧ stabOf s ≐ St ∧ Th ⊆ thOf s
  | .reg _ _ _, h => h.elim
  | .irr St' Th' C', h => by
      obtain ⟨hC, hq, hTh⟩ := h
      subst hC
      exact ⟨rfl, hq.symm, hTh⟩

theorem reg_shape {t : Tag} {Γ : List Form} {C : Form} :
    ∀ {s : WSeq}, WSubsumes (.reg t Γ C) s →
      s = .reg (tagOf s) (ctxOf s) C ∧ tagLeB t (tagOf s) = true ∧
        Γ ⊆ ctxOf s
  | .irr _ _ _, h => h.elim
  | .reg t' Γ' C', h => by
      obtain ⟨hC, hle, hΓ⟩ := h
      subst hC
      exact ⟨rfl, hle, hΓ⟩


/-! ### Family skolemisation

The induction hypothesis delivers, per premise, a Prop-level stored
subsumer; the join clauses need FAMILIES (functions into zones).
`List.find?` over the decidable subsumption test extracts them with no
choice. -/

structure IrrPick (G : Form) (db : List (WRow G)) {n : Nat}
    (stab th : Fin (n + 1) → List Form) (rhs : Fin (n + 1) → Form) where
  stab' : Fin (n + 1) → List Form
  th' : Fin (n + 1) → List Form
  mem : ∀ j, (WSeq.irr (stab' j) (th' j) (rhs j)) ∈ db.map (·.s)
  hst : ∀ j, stab' j ≐ stab j
  hth : ∀ j, th j ⊆ th' j

def irrPick {G : Form} {db : List (WRow G)} {n : Nat}
    {stab th : Fin (n + 1) → List Form} {rhs : Fin (n + 1) → Form}
    (hex : ∀ j, ∃ r ∈ db, WSubsumes (.irr (stab j) (th j) (rhs j)) r.s) :
    IrrPick G db stab th rhs :=
  let pk := fun j => (findSub db (.irr (stab j) (th j) (rhs j))).get
    (findSub_isSome_of_exists (hex j))
  have hfs : ∀ j, findSub db (.irr (stab j) (th j) (rhs j)) = some (pk j) :=
    fun j => (Option.some_get _).symm
  have hshape := fun j => irr_shape (findSub_sub (hfs j))
  { stab' := fun j => stabOf (pk j).s
    th' := fun j => thOf (pk j).s
    mem := fun j => by
      rw [← (hshape j).1]
      exact List.mem_map.mpr ⟨pk j, findSub_mem (hfs j), rfl⟩
    hst := fun j => (hshape j).2.1
    hth := fun j => (hshape j).2.2 }

structure RegPick (G : Form) (db : List (WRow G)) {k : Nat}
    (tps : Fin (k + 1) → Tag) (Δs : Fin (k + 1) → List Form)
    (Ds : Fin (k + 1) → Form) where
  tps' : Fin (k + 1) → Tag
  Δs' : Fin (k + 1) → List Form
  mem : ∀ i, (WSeq.reg (tps' i) (Δs' i) (Ds i)) ∈ db.map (·.s)
  hle : ∀ i, tagLeB (tps i) (tps' i) = true
  hΔ : ∀ i, Δs i ⊆ Δs' i

def regPick {G : Form} {db : List (WRow G)} {k : Nat}
    {tps : Fin (k + 1) → Tag} {Δs : Fin (k + 1) → List Form}
    {Ds : Fin (k + 1) → Form}
    (hex : ∀ i, ∃ r ∈ db, WSubsumes (.reg (tps i) (Δs i) (Ds i)) r.s) :
    RegPick G db tps Δs Ds :=
  let pk := fun i => (findSub db (.reg (tps i) (Δs i) (Ds i))).get
    (findSub_isSome_of_exists (hex i))
  have hfs : ∀ i, findSub db (.reg (tps i) (Δs i) (Ds i)) = some (pk i) :=
    fun i => (Option.some_get _).symm
  have hshape := fun i => reg_shape (findSub_sub (hfs i))
  { tps' := fun i => tagOf (pk i).s
    Δs' := fun i => ctxOf (pk i).s
    mem := fun i => by
      rw [← (hshape i).1]
      exact List.mem_map.mpr ⟨pk i, findSub_mem (hfs i), rfl⟩
    hle := fun i => (hshape i).2.1
    hΔ := fun i => (hshape i).2.2 }

/-- Introduction forms of `WSubsumes` at known shapes (the match-Prop
does not elaborate through `⟨…⟩` while a side is a metavariable). -/
theorem wSubsumes_reg {t₁ t₂ : Tag} {Γ₁ Γ₂ : List Form} {C : Form}
    (hle : tagLeB t₁ t₂ = true) (hΓ : Γ₁ ⊆ Γ₂) :
    WSubsumes (.reg t₁ Γ₁ C) (.reg t₂ Γ₂ C) := ⟨rfl, hle, hΓ⟩

theorem wSubsumes_irr {St₁ St₂ Th₁ Th₂ : List Form} {C : Form}
    (hq : St₁ ≐ St₂) (hTh : Th₁ ⊆ Th₂) :
    WSubsumes (.irr St₁ Th₁ C) (.irr St₂ Th₂ C) := ⟨rfl, hq, hTh⟩

/-! ### The two halves of a T-C case: ascent to the stored premise a
`DBClosed` clause consumes (`regUp`/`irrUp`), descent from that clause's
stored subsumer to the sequent under proof (`downReg`/`downIrr`).  The
join cases reuse the descent half, their ascent being `irrPick`/`regPick`. -/

/-- Ascent, regular stratum: a stored subsumer of `(t, Γ, C)` IS a stored
row `(t', Γ', C)` with `t ≤ t'` and `Γ ⊆ Γ'`. -/
private theorem regUp {G : Form} {db : List (WRow G)} {t : Tag}
    {Γ : List Form} {C : Form} (h : ∃ r ∈ db, WSubsumes (.reg t Γ C) r.s) :
    ∃ t' Γ', (WSeq.reg t' Γ' C) ∈ db.map (·.s) ∧ tagLeB t t' = true ∧
      Γ ⊆ Γ' := by
  obtain ⟨r, hr, hsub⟩ := h
  obtain ⟨hshape, hle, hΓ⟩ := reg_shape hsub
  exact ⟨tagOf r.s, ctxOf r.s,
    by rw [← hshape]; exact List.mem_map.mpr ⟨r, hr, rfl⟩, hle, hΓ⟩

/-- Ascent, irregular stratum: `Σ` moves by `≐`, `Θ` by `⊆`. -/
private theorem irrUp {G : Form} {db : List (WRow G)} {St Th : List Form}
    {C : Form} (h : ∃ r ∈ db, WSubsumes (.irr St Th C) r.s) :
    ∃ St' Th', (WSeq.irr St' Th' C) ∈ db.map (·.s) ∧ St' ≐ St ∧
      Th ⊆ Th' := by
  obtain ⟨r, hr, hsub⟩ := h
  obtain ⟨hshape, hst, hth⟩ := irr_shape hsub
  exact ⟨stabOf r.s, thOf r.s,
    by rw [← hshape]; exact List.mem_map.mpr ⟨r, hr, rfl⟩, hst, hth⟩

/-- Descent, regular stratum (`wSubsumes_trans` at the conclusion). -/
private theorem downReg {G : Form} {db : List (WRow G)} {t₁ t₂ : Tag}
    {Γ₁ Γ₂ : List Form} {C : Form} (hle : tagLeB t₁ t₂ = true)
    (hΓ : Γ₁ ⊆ Γ₂) (h : ∃ r ∈ db, WSubsumes (.reg t₂ Γ₂ C) r.s) :
    ∃ r ∈ db, WSubsumes (.reg t₁ Γ₁ C) r.s := by
  obtain ⟨r, hr, hsub⟩ := h
  exact ⟨r, hr, wSubsumes_trans (wSubsumes_reg hle hΓ) hsub⟩

/-- Descent, irregular stratum. -/
private theorem downIrr {G : Form} {db : List (WRow G)}
    {St₁ St₂ Th₁ Th₂ : List Form} {C : Form} (hq : St₁ ≐ St₂)
    (hTh : Th₁ ⊆ Th₂) (h : ∃ r ∈ db, WSubsumes (.irr St₂ Th₂ C) r.s) :
    ∃ r ∈ db, WSubsumes (.irr St₁ Th₁ C) r.s := by
  obtain ⟨r, hr, hsub⟩ := h
  exact ⟨r, hr, wSubsumes_trans (wSubsumes_irr hq hTh) hsub⟩

/-! ### The T-C induction

`DBClosed` plus the T-B transfer lemmas turn every derivation into a
stored subsumer, by structural induction. -/

mutual

theorem tCr {G : Form} {db : List (WRow G)} (hcl : DBClosed G db) :
    ∀ {t : Tag} {Γ : List Form} {C : Form},
      FRJWr G t Γ C → ∃ r ∈ db, WSubsumes (.reg t Γ C) r.s
  | _, _, _, .axR F hF hg hΓ =>
      downReg (tagLeB_refl _) hΓ.subset (hcl.axR F hF hg)
  | _, _, _, .andR1 (A₁ := A₁) (A₂ := A₂) d hg => by
      obtain ⟨t', Γ', hmem, hle, hΓ⟩ := regUp (tCr hcl d)
      exact downReg hle hΓ (hcl.andR1 t' Γ' A₁ A₂ hmem hg)
  | _, _, _, .andR2 (A₁ := A₁) (A₂ := A₂) d hg => by
      obtain ⟨t', Γ', hmem, hle, hΓ⟩ := regUp (tCr hcl d)
      exact downReg hle hΓ (hcl.andR2 t' Γ' A₁ A₂ hmem hg)
  | _, _, _, .impIn (A := A) (B := B) d hA hg => by
      obtain ⟨t', Γ', hmem, hle, hΓ⟩ := regUp (tCr hcl d)
      exact downReg hle hΓ (hcl.impIn t' Γ' A B hmem (clo_mono hΓ hA) hg)
  | _, _, _, .circIn (Z := Z) d htag hg => by
      obtain ⟨t', Γ', hmem, hle, hΓ⟩ := regUp (tCr hcl d)
      exact downReg hle hΓ
        (hcl.circIn t' Γ' Z hmem (pledge_of_le hle hΓ htag) hg)
  | _, _, _, .joinAt (stab := stab) (th := th) (rhs := rhs) (F := F)
      (kept := kept) prem hJ1 hJ2 hcirc hkc hF hFnot hg hΓ => by
      let pk := irrPick (fun j => tCi hcl (prem j))
      have hsubctx := joinAt_ctx_sub pk.hst pk.hth hkc
      exact downReg (tagLeB_refl _) (subset_of_ctxEq_left hΓ hsubctx)
        (hcl.joinAt pk.stab' pk.th' rhs F pk.mem
          (hJ1_of_swap pk.hst pk.hth hJ1)
          (hJ2_strict_of_swap pk.hst hJ2)
          (unionAll_circPart_nil_of_ctxEq pk.hst hcirc)
          hF (fun hmem => hFnot (mem_unionAll_filter_of_ctxEq _ pk.hst hmem)) hg)
  | _, _, _, .joinAtP (stab := stab) (th := th) (rhs := rhs) (F := F)
      (t' := t') (tps := tps) (Δs := Δs) (Ds := Ds)
      prem dps hJ1 hJ2 hJ5 hJ7s htag hF hFnot hg hΓ => by
      let pk := irrPick (fun j => tCi hcl (prem j))
      let rp := regPick (fun i => tCr hcl (dps i))
      have hsubctx : joinCtxAtP stab th rhs F Δs ⊆
          joinCtxAtP pk.stab' pk.th' rhs F rp.Δs' :=
        joinCtxAtP_mono (fun j => (pk.hst j).symm) pk.hth rp.hΔ
      exact downReg (tagLeB_refl _) (subset_of_ctxEq_left hΓ hsubctx)
        (hcl.joinAtP pk.stab' pk.th' rhs F t'
          rp.tps' rp.Δs' Ds pk.mem rp.mem
          (hJ1_of_swap pk.hst pk.hth hJ1)
          (hJ2_strict_of_swap pk.hst hJ2)
          (hJ5_of_swap pk.hst rp.hΔ hJ5)
          (hJ7s_of_swap pk.hst rp.hΔ hJ7s)
          (htag.imp id (fun h => ⟨h.1, fun i => ⟨(h.2 i).1,
            pledge_of_le (rp.hle i) (rp.hΔ i) (h.2 i).2⟩⟩))
          hF (fun hmem => hFnot (mem_unionAll_filter_of_ctxEq _ pk.hst hmem)) hg)
  | _, _, _, .joinAtF (stab := stab) (th := th) (rhs := rhs) (F := F)
      prem hJ1 hJ2 hF hFnot hg hΓ => by
      let pk := irrPick (fun j => tCi hcl (prem j))
      have hsubctx : joinCtxAtF stab th rhs F ⊆
          joinCtxAtF pk.stab' pk.th' rhs F :=
        joinCtxAtF_mono (fun j => (pk.hst j).symm) pk.hth
      exact downReg (tagLeB_refl _) (subset_of_ctxEq_left hΓ hsubctx)
        (hcl.joinAtF pk.stab' pk.th' rhs F pk.mem
          (hJ1_of_swap pk.hst pk.hth hJ1)
          (hJ2_strict_of_swap pk.hst hJ2)
          hF (fun hmem => hFnot (mem_unionAll_filter_of_ctxEq _ pk.hst hmem)) hg)
  | _, _, _, .joinOr (stab := stab) (th := th) (rhs := rhs)
      (C₁ := C₁) (C₂ := C₂) (kept := kept)
      prem hJ1 hJ2 hcirc hkc hC hg hΓ => by
      let pk := irrPick (fun j => tCi hcl (prem j))
      have hsubctx := joinOr_ctx_sub pk.hst pk.hth hkc
      exact downReg (tagLeB_refl _) (subset_of_ctxEq_left hΓ hsubctx)
        (hcl.joinOr pk.stab' pk.th' rhs C₁ C₂ pk.mem
          (hJ1_of_swap pk.hst pk.hth hJ1)
          (hJ2_strict_of_swap pk.hst hJ2)
          (unionAll_circPart_nil_of_ctxEq pk.hst hcirc)
          ⟨refAt_mono (fun _ h => h) hsubctx hC.1,
           refAt_mono (fun _ h => h) hsubctx hC.2⟩ hg)
  | _, _, _, .joinOrP (stab := stab) (th := th) (rhs := rhs)
      (C₁ := C₁) (C₂ := C₂) (t' := t') (tps := tps) (Δs := Δs) (Ds := Ds)
      prem dps hJ1 hJ2 hJ5 hJ7s htag hC hg hΓ => by
      let pk := irrPick (fun j => tCi hcl (prem j))
      let rp := regPick (fun i => tCr hcl (dps i))
      have hsubctx : joinCtxOrP stab th rhs Δs ⊆
          joinCtxOrP pk.stab' pk.th' rhs rp.Δs' :=
        joinCtxOrP_mono (fun j => (pk.hst j).symm) pk.hth rp.hΔ
      exact downReg (tagLeB_refl _) (subset_of_ctxEq_left hΓ hsubctx)
        (hcl.joinOrP pk.stab' pk.th' rhs C₁ C₂ t'
          rp.tps' rp.Δs' Ds pk.mem rp.mem
          (hJ1_of_swap pk.hst pk.hth hJ1)
          (hJ2_strict_of_swap pk.hst hJ2)
          (hJ5_of_swap pk.hst rp.hΔ hJ5)
          (hJ7s_of_swap pk.hst rp.hΔ hJ7s)
          (htag.imp id (fun h => ⟨h.1, fun i => ⟨(h.2 i).1,
            pledge_of_le (rp.hle i) (rp.hΔ i) (h.2 i).2⟩⟩))
          hC hg)
  | _, _, _, .joinOrF (stab := stab) (th := th) (rhs := rhs)
      (C₁ := C₁) (C₂ := C₂) prem hJ1 hJ2 hC hg hΓ => by
      let pk := irrPick (fun j => tCi hcl (prem j))
      have hsubctx : joinCtxOrF stab th rhs ⊆
          joinCtxOrF pk.stab' pk.th' rhs :=
        joinCtxOrF_mono (fun j => (pk.hst j).symm) pk.hth
      exact downReg (tagLeB_refl _) (subset_of_ctxEq_left hΓ hsubctx)
        (hcl.joinOrF pk.stab' pk.th' rhs C₁ C₂ pk.mem
          (hJ1_of_swap pk.hst pk.hth hJ1)
          (hJ2_strict_of_swap pk.hst hJ2)
          hC hg)
  | _, _, _, .joinCirc (stab := stab) (th := th) (rhs := rhs) (Z := Z)
      (kept := kept) prem hJ1 hJ2 hcirc hkc hZ hg hΓ => by
      let pk := irrPick (fun j => tCi hcl (prem j))
      have hsubctx := joinOr_ctx_sub pk.hst pk.hth hkc
      exact downReg (tagLeB_refl _) (subset_of_ctxEq_left hΓ hsubctx)
        (hcl.joinCirc pk.stab' pk.th' rhs Z pk.mem
          (hJ1_of_swap pk.hst pk.hth hJ1)
          (fun A B hAB => refAt_mono (fun _ h => h) hsubctx
            (hJ2 A B (mem_unionAll_filter_of_ctxEq _ pk.hst hAB)))
          (unionAll_circPart_nil_of_ctxEq pk.hst hcirc)
          (refAt_mono (fun _ h => h) hsubctx hZ)
          hg)
  | _, _, _, .joinCircP (stab := stab) (th := th) (rhs := rhs) (Z := Z)
      (tps := tps) (Δs := Δs) (Ds := Ds)
      prem dps hJ1 hJ2 hJ5 hJ7s hDs hZ hg hΓ => by
      let pk := irrPick (fun j => tCi hcl (prem j))
      let rp := regPick (fun i => tCr hcl (dps i))
      have hsubctx : joinCtxOrP stab th rhs Δs ⊆
          joinCtxOrP pk.stab' pk.th' rhs rp.Δs' :=
        joinCtxOrP_mono (fun j => (pk.hst j).symm) pk.hth rp.hΔ
      exact downReg (tagLeB_refl _) (subset_of_ctxEq_left hΓ hsubctx)
        (hcl.joinCircP pk.stab' pk.th' rhs Z
          rp.tps' rp.Δs' Ds pk.mem rp.mem
          (hJ1_of_swap pk.hst pk.hth hJ1)
          (hJ2_strict_of_swap pk.hst hJ2)
          (hJ5_of_swap pk.hst rp.hΔ hJ5)
          (hJ7s_of_swap pk.hst rp.hΔ hJ7s)
          (fun i => ⟨(hDs i).1,
            pledge_of_le (rp.hle i) (rp.hΔ i) (hDs i).2⟩)
          hZ hg)

theorem tCi {G : Form} {db : List (WRow G)} (hcl : DBClosed G db) :
    ∀ {St Th : List Form} {C : Form},
      FRJWi G St Th C → ∃ r ∈ db, WSubsumes (.irr St Th C) r.s
  | _, _, _, .axI F hF hg hTh =>
      downIrr (CtxEq.refl _) hTh.subset (hcl.axI F hF hg)
  | _, _, _, .andI1 (A₁ := A₁) (A₂ := A₂) d hg => by
      obtain ⟨St', Th', hmem, hst, hth⟩ := irrUp (tCi hcl d)
      exact downIrr hst.symm hth (hcl.andI1 St' Th' A₁ A₂ hmem hg)
  | _, _, _, .andI2 (A₁ := A₁) (A₂ := A₂) d hg => by
      obtain ⟨St', Th', hmem, hst, hth⟩ := irrUp (tCi hcl d)
      exact downIrr hst.symm hth (hcl.andI2 St' Th' A₁ A₂ hmem hg)
  | _, _, _, .orI (C₁ := C₁) (C₂ := C₂) d₁ d₂ h₁ h₂ hg hSt hTh => by
      obtain ⟨St₁', Th₁', hmem₁, hst₁, hth₁⟩ := irrUp (tCi hcl d₁)
      obtain ⟨St₂', Th₂', hmem₂, hst₂, hth₂⟩ := irrUp (tCi hcl d₂)
      have hpair := orI_mono_sub hst₁ hth₁ hst₂ hth₂ hSt hTh
      exact downIrr hpair.1 hpair.2
        (hcl.orI St₁' Th₁' St₂' Th₂' C₁ C₂ hmem₁ hmem₂
          (fun x hx => by
            rcases List.mem_append.mp (h₁ ((hst₁ x).mp hx)) with h | h
            · exact List.mem_append_left _ ((hst₂ x).mpr h)
            · exact List.mem_append_right _ (hth₂ h))
          (fun x hx => by
            rcases List.mem_append.mp (h₂ ((hst₂ x).mp hx)) with h | h
            · exact List.mem_append_left _ ((hst₁ x).mpr h)
            · exact List.mem_append_right _ (hth₁ h))
          hg)
  | _, _, _, .impInI (Lam := Lam) (A := A) (B := B) d hpre hdisj hA hg
      hSt hTh => by
      obtain ⟨St', Th', hmem, hst, hth⟩ := irrUp (tCi hcl d)
      have hpair := impInI_mono_sub hst hth hpre hdisj hSt hTh
      exact downIrr hpair.1 hpair.2
        (hcl.impInI St' Th' Lam A B hmem
          (by
            refine clo_mono (fun x hx => ?_) hA
            rcases List.mem_append.mp hx with h | h
            · exact List.mem_append_left _ ((hst x).mpr h)
            · refine List.mem_append_right _
                (List.mem_filter.mpr ⟨?_, by simpa using h⟩)
              exact hth ((hpre x).mpr (List.mem_append_right _ h)))
          hg)
  | _, _, _, .lift d hTh => by
      obtain ⟨t', Γ', hmem, _, hΓ⟩ := regUp (tCr hcl d)
      exact downIrr (CtxEq.refl _) (maxTh_sub hΓ hTh)
        (hcl.lift t' Γ' _ hmem)
  | _, _, _, .circNotIn (Z := Z) d htag hTh hg => by
      obtain ⟨t', Γ', hmem, hle, hΓ⟩ := regUp (tCr hcl d)
      exact downIrr (CtxEq.refl _) (maxTh_sub hΓ hTh)
        (hcl.circNotIn t' Γ' Z hmem (pledge_of_le hle hΓ htag) hg)
  | _, _, _, .axIC F ats hats hFf hg hTh =>
      downIrr (CtxEq.refl _) hTh.subset (hcl.axIC F ats hats hFf hg)

end

/-- **T-C modulo closedness**: a `DBClosed` database subsumes every
derivable row — `WSaturated.2` for its membership predicate. -/
theorem tC_of_closed {G : Form} {db : List (WRow G)} (hcl : DBClosed G db) :
    ∀ s, WDerivable G s → ∃ r ∈ db, WSubsumes s r.s
  | .reg _ _ _, ⟨d⟩ => tCr hcl d
  | .irr _ _ _, ⟨d⟩ => tCi hcl d

/-- **`decideGbuW` modulo `DBClosed`**: the decision follows from any
derivation-carrying row list closed under the rules. -/
def decideGbuW_of_dbClosed {G : Form} (db : List (WRow G))
    (hcl : DBClosed G db) : ProvableGbuC G ⊕' DisprovableW G :=
  decideGbuW_of db (tC_of_closed hcl)

end Gbu.W

/-! ## Pins -/

/-- info: 'FRJ.keptChain_sub_keptOf_of_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms keptChain_sub_keptOf_of_le

/-- info: 'FRJ.keptChain_sub_keptOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms keptChain_sub_keptOf

/-- info: 'FRJ.joinCirc_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms joinCirc_mono

/-- info: 'FRJ.joinOr_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms joinOr_mono

/-- info: 'FRJ.joinAt_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms joinAt_mono

/-- info: 'FRJ.circIn_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms circIn_mono

/-- info: 'FRJ.pledge_of_le' depends on axioms: [propext] -/
#guard_msgs in
#print axioms pledge_of_le

/-- info: 'FRJ.orI_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms orI_mono

/-- info: 'FRJ.impInI_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms impInI_mono

/-- info: 'FRJ.impInI_mono_sub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms impInI_mono_sub

/-- info: 'FRJ.lift_max' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lift_max

/-- info: 'FRJ.circNotIn_max' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms circNotIn_max

/-- info: 'FRJ.joinAtF_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms joinAtF_mono

/-- info: 'FRJ.joinOrF_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms joinOrF_mono

/-- info: 'FRJ.joinAtP_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms joinAtP_mono

/-- info: 'FRJ.joinOrP_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms joinOrP_mono

/-- info: 'FRJ.joinCircP_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms joinCircP_mono

/-- info: 'FRJ.goalWr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms goalWr

/-- info: 'FRJ.goalWi' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms goalWi

/-- info: 'FRJ.tagWr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms tagWr

/-- info: 'FRJ.Gbu.W.wSubsumes_refl' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Gbu.W.wSubsumes_refl

/-- info: 'FRJ.Gbu.W.wSubsumes_trans' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Gbu.W.wSubsumes_trans

/-- info: 'FRJ.Gbu.W.wsat_of_closed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Gbu.W.wsat_of_closed

/-- info: 'FRJ.Gbu.W.decideGbuW_of' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Gbu.W.decideGbuW_of

/-- info: 'FRJ.Gbu.W.subsumesB_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Gbu.W.subsumesB_iff

/-- info: 'FRJ.Gbu.W.tC_of_closed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Gbu.W.tC_of_closed

/-- info: 'FRJ.Gbu.W.decideGbuW_of_dbClosed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Gbu.W.decideGbuW_of_dbClosed

end FRJ
