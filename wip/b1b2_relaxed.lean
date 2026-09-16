/-
# B1 for the `RefAt`-relaxed `⋈^∨`/`⋈^◯`

`wip/b1b2_lemmas.lean` proves the context half of B1 for the barren
`⋈^∨`/`⋈^◯` under the STRICT second side condition

    (J2)   ∀ A B.  A ⊃ B ∈ ⋃ⱼ Ξⱼ^⊃  →  A ∈ Υ,

whereas the clause `DBClosed.joinCirc` of `FRJ/Gbu/W/Closure.lean` and
the constructor `FRJWr.joinCirc` of `FRJ/CalculusW.lean` assume only the
RELAXED

    (J2r)  ∀ A B.  A ⊃ B ∈ ⋃ⱼ Ξⱼ^⊃  →  RefAt true Υ (ctxOr Ξs Θs rhs) A,

i.e. the join root refutes the antecedent from its own shape rather than
finding it among the premise right formulas.  This file proves

    ctxOr Ξs Θs rhs ⊆ ctxOr (Ξs ∘ e) (Θs ∘ e) (rhs ∘ e)

for a reindexing `e` that drops one index `p`, under (J1) and (J2r).

Method.  Write `S = ctxOr Ξs Θs rhs = base ++ kept` and `T` for the
sub-family's context `base' ++ kept'`.  A stable implication of the
dropped premise is licensed by a `RefAt` certificate over `S`, whose
`Clo` leaves may be kept links of the FULL family; the sub-family must
re-derive those in its own kept chain first.  The order is well founded
because `Clo Γ X` consults only members of `Γ` of `Form.size` at most
`Form.size X`, and `RefAt cone Υ ctx X` consults `ctx` only through
`Clo` on proper subformulas of `X`.  So the transfer lemmas

    Clo Γ X   → (∀ y ∈ Γ, size y ≤ size X → y ∈ Γ')   → Clo Γ' X
    RefAt c Υ ctx X → Υ ⊆ Υ' → (∀ y ∈ ctx, size y ≤ size X → y ∈ ctx')
                    → RefAt c Υ' ctx' X

turn the inclusion `S ⊆ T` into an induction on `Form.size`, closed at
each implication by the fixpoint property `keptOf_saturated`.
-/
import wip.b1b2_lemmas

open FRJ Form

namespace FRJ.Arity

/-! ## 1. Size-bounded transfer of `Clo` and `RefAt`

Both `Clo` and `RefAt` inspect their context only at formulas no larger
than the target, so a context inclusion that holds BELOW a given size
already transfers derivations at that size. -/

theorem form_size_pos (x : Form) : 0 < Form.size x := by
  cases x <;> simp only [Form.size] <;> omega

/-- Weakening a size-bounded context inclusion to a smaller bound. -/
theorem ctx_shrink {ctx ctx' : List Form} {X Y : Form}
    (hle : Form.size Y ≤ Form.size X)
    (h : ∀ y ∈ ctx, Form.size y ≤ Form.size X → y ∈ ctx') :
    ∀ y ∈ ctx, Form.size y ≤ Form.size Y → y ∈ ctx' :=
  fun y hy hs => h y hy (Nat.le_trans hs hle)

/-- Every `.base` leaf of a `Clo Γ X` derivation is a member of `Γ` of
size at most `Form.size X`; so a context inclusion bounded by that size
suffices to transfer the derivation. -/
theorem clo_transfer {Γ Γ' : List Form} :
    ∀ {X : Form}, Clo Γ X →
      (∀ y ∈ Γ, Form.size y ≤ Form.size X → y ∈ Γ') → Clo Γ' X := by
  intro X hX
  induction hX with
  | @base C hC => exact fun h => .base (h C hC (Nat.le_refl _))
  | @and X Y _ _ ihX ihY =>
      exact fun h =>
        .and (ihX (ctx_shrink (by simp only [Form.size]; omega) h))
          (ihY (ctx_shrink (by simp only [Form.size]; omega) h))
  | @orR A X _ ih =>
      exact fun h => .orR (ih (ctx_shrink (by simp only [Form.size]; omega) h))
  | @orL A X _ ih =>
      exact fun h => .orL (ih (ctx_shrink (by simp only [Form.size]; omega) h))
  | @imp A X _ ih =>
      exact fun h => .imp (ih (ctx_shrink (by simp only [Form.size]; omega) h))
  | @circ X _ ih =>
      exact fun h => .circ (ih (ctx_shrink (by simp only [Form.size]; omega) h))

/-- `RefAt` consults its context only in the `imp` clause, through `Clo`
on the ANTECEDENT — a proper subformula of the target.  So the same
size-bounded inclusion transfers a `RefAt` certificate. -/
theorem refAt_transfer {cone : Bool} {Υ Υ' ctx ctx' : List Form} (hΥ : Υ ⊆ Υ') :
    ∀ {X : Form}, RefAt cone Υ ctx X →
      (∀ y ∈ ctx, Form.size y ≤ Form.size X → y ∈ ctx') →
      RefAt cone Υ' ctx' X := by
  intro X hX
  induction hX with
  | ups hC => exact fun _ => .ups (hΥ hC)
  | bot => exact fun _ => .bot
  | @imp A B hA _ ih =>
      exact fun h =>
        .imp (clo_transfer hA (ctx_shrink (by simp only [Form.size]; omega) h))
          (ih (ctx_shrink (by simp only [Form.size]; omega) h))
  | @circ Z hcone _ ih =>
      exact fun h =>
        .circ hcone (ih (ctx_shrink (by simp only [Form.size]; omega) h))
  | @or Z₁ Z₂ _ _ ih₁ ih₂ =>
      exact fun h =>
        .or (ih₁ (ctx_shrink (by simp only [Form.size]; omega) h))
          (ih₂ (ctx_shrink (by simp only [Form.size]; omega) h))
  | @andL Z₁ Z₂ _ ih =>
      exact fun h => .andL (ih (ctx_shrink (by simp only [Form.size]; omega) h))
  | @andR Z₁ Z₂ _ ih =>
      exact fun h => .andR (ih (ctx_shrink (by simp only [Form.size]; omega) h))

/-! ## 2. The shape of a kept link

Each link of a kept chain is a pool implication whose antecedent is
`RefAt`-refuted over the base plus the EARLIER links; `refAt_mono` lifts
that certificate to the base plus the whole chain. -/

theorem keptChain_shape {Υ base pool : List Form} :
    ∀ {kept : List Form}, KeptChain Υ base pool kept →
      ∀ x ∈ kept, ∃ Y B, x = Form.imp Y B ∧ Form.imp Y B ∈ pool ∧
        RefAt true Υ (base ++ kept) Y := by
  intro kept h
  induction h with
  | nil => exact fun _ hx => absurd hx List.not_mem_nil
  | @cons Y B rest _ hmem href ih =>
      have hsub : base ++ rest ⊆ base ++ (Form.imp Y B :: rest) := by
        intro z hz
        rcases List.mem_append.mp hz with hz | hz
        · exact List.mem_append_left _ hz
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ hz)
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact ⟨Y, B, rfl, hmem, refAt_mono (fun _ hy => hy) hsub href⟩
      · obtain ⟨Y', B', rfl, hp', hr'⟩ := ih x hx'
        exact ⟨Y', B', rfl, hp', refAt_mono (fun _ hy => hy) hsub hr'⟩

theorem keptOf_shape {Υ base pool : List Form} {x : Form}
    (hx : x ∈ keptOf Υ base pool) :
    ∃ Y B, x = Form.imp Y B ∧ Form.imp Y B ∈ pool ∧
      RefAt true Υ (base ++ keptOf Υ base pool) Y :=
  keptChain_shape (keptOf_ok Υ base pool) x hx

/-! ## 3. The membership shape of the family's conclusion context

Under (J1) and (J2r), every member of `ctxOr Ξs Θs rhs` is either a
member of the sub-family's base, or an implication of the sub-family's
retention pool whose antecedent the join root refutes over the family's
own conclusion context. -/

theorem memCtxOr_shape {n m : Nat} {Ξs Θs : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form}
    (e : Fin (m + 1) → Fin (n + 1)) (p : Fin (n + 1)) (hne : ∀ k, e k ≠ p)
    (hsurj : ∀ j, j ≠ p → ∃ k, e k = j)
    (hJ1 : ∀ i j, i ≠ j → Ξs i ⊆ Ξs j ++ Θs j)
    (hJ2r : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (Ξs j)) →
      RefAt true (upsilon rhs) (ctxOr Ξs Θs rhs) A)
    {x : Form} (hx : x ∈ ctxOr Ξs Θs rhs) :
    x ∈ joinCtxOrVBase (fun k => Ξs (e k)) (fun k => Θs (e k)) ∨
      ∃ Y B, x = Form.imp Y B ∧
        Form.imp Y B ∈ thPool (fun k => Θs (e k)) ∧
        RefAt true (upsilon rhs) (ctxOr Ξs Θs rhs) Y := by
  rcases List.mem_append.mp hx with hb | hk
  · -- a member of the family's base
    simp only [joinCtxOrVBase, List.mem_append] at hb
    rcases hb with (hat | hint) | himp
    · rcases part_cover e p hne hsurj hJ1 Form.isPV hat with h | h
      · exact Or.inl (by
          simp only [joinCtxOrVBase, List.mem_append]; exact Or.inl (Or.inl h))
      · exact Or.inl (by
          simp only [joinCtxOrVBase, List.mem_append]; exact Or.inl (Or.inr h))
    · exact Or.inl (by
        simp only [joinCtxOrVBase, List.mem_append]
        exact Or.inl (Or.inr (interAll_sub_comp e _ hint)))
    · rcases part_cover e p hne hsurj hJ1 Form.isImp himp with h | h
      · exact Or.inl (by
          simp only [joinCtxOrVBase, List.mem_append]; exact Or.inr h)
      · -- a stable implication of the dropped premise: it lies in every
        -- survivor's second zone, hence in the sub-pool, and (J2r)
        -- refutes its antecedent over the family's own context
        have hisImp : x.isImp = true := by
          rw [mem_unionAll] at himp
          obtain ⟨j, hj⟩ := himp
          exact (List.mem_filter.mp hj).2
        obtain ⟨A, B, rfl⟩ := isImp_shape hisImp
        exact Or.inr ⟨A, B, rfl, interImp_eq_pool _ h, hJ2r A B himp⟩
  · -- a link of the family's kept chain
    obtain ⟨Y, B, rfl, hpool, href⟩ := keptOf_shape hk
    exact Or.inr ⟨Y, B, rfl, thPool_sub_comp e Θs hpool, href⟩

/-! ## 4. B1 for the relaxed `⋈^∨`/`⋈^◯` -/

/-- The inclusion, stratified by `Form.size`.  In the implication case
`x = Y ⊃ B` the antecedent `Y` is strictly smaller than `x`, so the
induction hypothesis already places every member of the family's context
of size at most `Form.size Y` inside the sub-family's; `refAt_transfer`
then moves the (J2r) certificate across, and `keptOf_saturated` puts `x`
into the sub-family's kept chain. -/
theorem ctxOr_sub_relaxed_upTo {n m : Nat} {Ξs Θs : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form}
    (e : Fin (m + 1) → Fin (n + 1)) (p : Fin (n + 1)) (hne : ∀ k, e k ≠ p)
    (hsurj : ∀ j, j ≠ p → ∃ k, e k = j) (hcov : ∀ j, ∃ k, rhs (e k) = rhs j)
    (hJ1 : ∀ i j, i ≠ j → Ξs i ⊆ Ξs j ++ Θs j)
    (hJ2r : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (Ξs j)) →
      RefAt true (upsilon rhs) (ctxOr Ξs Θs rhs) A) :
    ∀ N : Nat, ∀ x ∈ ctxOr Ξs Θs rhs, Form.size x ≤ N →
      x ∈ ctxOr (fun k => Ξs (e k)) (fun k => Θs (e k)) (fun k => rhs (e k)) := by
  intro N
  induction N with
  | zero =>
      intro x _ hs
      exact absurd hs (by have := form_size_pos x; omega)
  | succ N ih =>
      intro x hx hs
      rcases memCtxOr_shape e p hne hsurj hJ1 hJ2r hx with hb | ⟨Y, B, rfl, hpool, href⟩
      · simp only [ctxOr]
        exact List.mem_append_left _ hb
      · have hY : Form.size Y ≤ N := by
          simp only [Form.size] at hs
          omega
        have hctx : ∀ y ∈ ctxOr Ξs Θs rhs, Form.size y ≤ Form.size Y →
            y ∈ ctxOr (fun k => Ξs (e k)) (fun k => Θs (e k))
              (fun k => rhs (e k)) :=
          fun y hy hsy => ih y hy (Nat.le_trans hsy hY)
        have hkept : Form.imp Y B ∈
            keptOf (upsilon (fun k => rhs (e k)))
              (joinCtxOrVBase (fun k => Ξs (e k)) (fun k => Θs (e k)))
              (thPool (fun k => Θs (e k))) :=
          keptOf_saturated hpool
            (refAt_transfer (upsilon_sub_comp e rhs hcov) href hctx)
        simp only [ctxOr]
        exact List.mem_append_right _ hkept

/-- **B1 for the `RefAt`-relaxed `⋈^∨`/`⋈^◯`, the context half**: with
the relaxed (J2r) in place of (J2), the family's conclusion context is
still inside the sub-family's. -/
theorem ctxOr_sub_relaxed {n m : Nat} {Ξs Θs : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form}
    (e : Fin (m + 1) → Fin (n + 1)) (p : Fin (n + 1)) (hne : ∀ k, e k ≠ p)
    (hsurj : ∀ j, j ≠ p → ∃ k, e k = j) (hcov : ∀ j, ∃ k, rhs (e k) = rhs j)
    (hJ1 : ∀ i j, i ≠ j → Ξs i ⊆ Ξs j ++ Θs j)
    (hJ2r : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (Ξs j)) →
      RefAt true (upsilon rhs) (ctxOr Ξs Θs rhs) A) :
    ctxOr Ξs Θs rhs ⊆
      ctxOr (fun k => Ξs (e k)) (fun k => Θs (e k)) (fun k => rhs (e k)) :=
  fun x hx =>
    ctxOr_sub_relaxed_upTo e p hne hsurj hcov hJ1 hJ2r (Form.size x) x hx
      (Nat.le_refl _)

/-- The relaxed (J2r) transfers to the sub-family: its own conclusion
context contains the family's, so the certificate moves across by
`refAt_mono`. -/
theorem j2r_comp {n m : Nat} {Ξs Θs : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form}
    (e : Fin (m + 1) → Fin (n + 1)) (p : Fin (n + 1)) (hne : ∀ k, e k ≠ p)
    (hsurj : ∀ j, j ≠ p → ∃ k, e k = j) (hcov : ∀ j, ∃ k, rhs (e k) = rhs j)
    (hJ1 : ∀ i j, i ≠ j → Ξs i ⊆ Ξs j ++ Θs j)
    (hJ2r : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (Ξs j)) →
      RefAt true (upsilon rhs) (ctxOr Ξs Θs rhs) A) :
    ∀ A B : Form, Form.imp A B ∈ unionAll (fun k => impPart (Ξs (e k))) →
      RefAt true (upsilon (fun k => rhs (e k)))
        (ctxOr (fun k => Ξs (e k)) (fun k => Θs (e k)) (fun k => rhs (e k))) A :=
  fun A B h =>
    refAt_mono (upsilon_sub_comp e rhs hcov)
      (ctxOr_sub_relaxed e p hne hsurj hcov hJ1 hJ2r)
      (hJ2r A B (unionAll_comp_sub e (fun j => impPart (Ξs j)) h))

/-! ## Pins -/

/-- info: 'FRJ.Arity.ctxOr_sub_relaxed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ctxOr_sub_relaxed

/-- info: 'FRJ.Arity.j2r_comp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms j2r_comp

end FRJ.Arity
