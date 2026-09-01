/-
# The `decideGbuW` instantiation — Part I: kept-chain dominance and join monotonicity

`searchW`/`dichotomyW` (wip/gbu_frjw_search.lean) are parameterised by a
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

Still OPEN (later parts): the promise/fallible join cases, `⊃∈ᵢ`
(`impInI`, the second-zone split), the maximal-`Θ` treatment of
`lift`/`circNotIn`, the computed closure itself with its termination
bound, `WSaturated` for it, and the assembly `decideGbuW`.
-/
import FRJ.CalculusW
import FRJ.Search.Engine

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
    FRJWr G t₂ Γ₂ (.circ Z) := by
  refine .circIn d₂ ?_ hgoal
  rcases htag with rfl | ⟨W, rfl, hcov⟩
  · cases t₂ with
    | barren => exact Or.inl rfl
    | chain D => exact absurd hle (by simp [tagLeB])
    | blocked => exact absurd hle (by simp [tagLeB])
  · cases t₂ with
    | barren => exact Or.inl rfl
    | chain D =>
        have hWD : W = D := by
          simpa [tagLeB] using hle
        exact Or.inr ⟨D, rfl, hWD ▸ covers_mono hΓ hcov⟩
    | blocked => exact absurd hle (by simp [tagLeB])

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

end FRJ
