import LaxLogic.PLLG4HComp

/-!
# Termination B: the cumulative set-context calculus `G4s`

`G4iLL″` over `Finset` contexts, **fully cumulative**: every rule
retains its principal and inserts its pieces; nothing is ever erased.
Cumulativity is what the admissibility theorems bought: keeping more
is weakening-sound, and the consuming shapes are recovered on the list
side by inversion + contraction — so `G4s` proves exactly the `G4c`
sequents (`G4c.iff_set`), while on the set side backward search only
ever *grows* contexts inside the finite space of `PLLG4Space.lean`.

The `impLBot` rule is deliberately absent: cumulatively its premise
would equal its conclusion; the list rule's content is absorbed by
`weaken_subset` in the embedding.

The equivalence is engineered for reuse: `G4h.toSet` is a direct
height-preserving induction (all transports are `weaken_subset`), and
`G4sh.toSC` maps the cumulative rules onto `SC`'s keeping rules — the
shapes match almost verbatim, the three Dyckhoff rules going through
the same `SC.cut` constructions as `G4c.toSC` — after which
yesterday's `completeness` closes the loop.
-/

open PLLFormula

namespace PLLND

/-- **G4iLL″ on set contexts, fully cumulative**, height-indexed. -/
inductive G4sh : Nat → Finset PLLFormula → PLLFormula → Prop
  | init {n : Nat} {Γ : Finset PLLFormula} {a : String}
      (h : prop a ∈ Γ) : G4sh n Γ (prop a)
  | botL {n : Nat} {Γ : Finset PLLFormula} {C : PLLFormula}
      (h : falsePLL ∈ Γ) : G4sh n Γ C
  | andR {n : Nat} {Γ : Finset PLLFormula} {A B : PLLFormula} :
      G4sh n Γ A → G4sh n Γ B → G4sh (n + 1) Γ (A.and B)
  | orR1 {n : Nat} {Γ : Finset PLLFormula} {A B : PLLFormula} :
      G4sh n Γ A → G4sh (n + 1) Γ (A.or B)
  | orR2 {n : Nat} {Γ : Finset PLLFormula} {A B : PLLFormula} :
      G4sh n Γ B → G4sh (n + 1) Γ (A.or B)
  | impR {n : Nat} {Γ : Finset PLLFormula} {A B : PLLFormula} :
      G4sh n (insert A Γ) B → G4sh (n + 1) Γ (A.ifThen B)
  | laxR {n : Nat} {Γ : Finset PLLFormula} {A : PLLFormula} :
      G4sh n Γ A → G4sh (n + 1) Γ A.somehow
  | laxL {n : Nat} {Γ : Finset PLLFormula} {A B : PLLFormula}
      (h : A.somehow ∈ Γ) :
      G4sh n (insert A Γ) B.somehow → G4sh (n + 1) Γ B.somehow
  | andL {n : Nat} {Γ : Finset PLLFormula} {A B C : PLLFormula}
      (h : A.and B ∈ Γ) :
      G4sh n (insert A (insert B Γ)) C → G4sh (n + 1) Γ C
  | orL {n : Nat} {Γ : Finset PLLFormula} {A B C : PLLFormula}
      (h : A.or B ∈ Γ) :
      G4sh n (insert A Γ) C → G4sh n (insert B Γ) C → G4sh (n + 1) Γ C
  | impLProp {n : Nat} {Γ : Finset PLLFormula} {a : String} {B C : PLLFormula}
      (h : (prop a).ifThen B ∈ Γ) (ha : prop a ∈ Γ) :
      G4sh n (insert B Γ) C → G4sh (n + 1) Γ C
  | impLAnd {n : Nat} {Γ : Finset PLLFormula} {A B D C : PLLFormula}
      (h : (A.and B).ifThen D ∈ Γ) :
      G4sh n (insert (A.ifThen (B.ifThen D)) Γ) C → G4sh (n + 1) Γ C
  | impLOr {n : Nat} {Γ : Finset PLLFormula} {A B D C : PLLFormula}
      (h : (A.or B).ifThen D ∈ Γ) :
      G4sh n (insert (A.ifThen D) (insert (B.ifThen D) Γ)) C →
      G4sh (n + 1) Γ C
  | impLImp {n : Nat} {Γ : Finset PLLFormula} {A B D C : PLLFormula}
      (h : (A.ifThen B).ifThen D ∈ Γ) :
      G4sh n (insert (B.ifThen D) Γ) (A.ifThen B) →
      G4sh n (insert D Γ) C → G4sh (n + 1) Γ C
  | impLLax {n : Nat} {Γ : Finset PLLFormula} {A B C : PLLFormula}
      (h : A.somehow.ifThen B ∈ Γ) :
      G4sh n Γ A → G4sh n (insert B Γ) C → G4sh (n + 1) Γ C
  | impLLaxLax {n : Nat} {Γ : Finset PLLFormula} {A B X C : PLLFormula}
      (h : A.somehow.ifThen B ∈ Γ) (hX : X.somehow ∈ Γ) :
      G4sh n (insert X Γ) A.somehow → G4sh n (insert B Γ) C →
      G4sh (n + 1) Γ C

/-- Set-context derivability at some height. -/
def G4s (Γ : Finset PLLFormula) (C : PLLFormula) : Prop := ∃ n, G4sh n Γ C

namespace G4sh

theorem succ_mono : ∀ {n : Nat} {Γ : Finset PLLFormula} {C : PLLFormula},
    G4sh n Γ C → G4sh (n + 1) Γ C := by
  intro n Γ C d
  induction d with
  | init h => exact .init h
  | botL h => exact .botL h
  | andR _ _ ih₁ ih₂ => exact .andR ih₁ ih₂
  | orR1 _ ih => exact .orR1 ih
  | orR2 _ ih => exact .orR2 ih
  | impR _ ih => exact .impR ih
  | laxR _ ih => exact .laxR ih
  | laxL h _ ih => exact .laxL h ih
  | andL h _ ih => exact .andL h ih
  | orL h _ _ ih₁ ih₂ => exact .orL h ih₁ ih₂
  | impLProp h ha _ ih => exact .impLProp h ha ih
  | impLAnd h _ ih => exact .impLAnd h ih
  | impLOr h _ ih => exact .impLOr h ih
  | impLImp h _ _ ih₁ ih₂ => exact .impLImp h ih₁ ih₂
  | impLLax h _ _ ih₁ ih₂ => exact .impLLax h ih₁ ih₂
  | impLLaxLax h hX _ _ ih₁ ih₂ => exact .impLLaxLax h hX ih₁ ih₂

theorem mono {n m : Nat} {Γ : Finset PLLFormula} {C : PLLFormula}
    (d : G4sh n Γ C) (hnm : n ≤ m) : G4sh m Γ C := by
  induction hnm with
  | refl => exact d
  | step _ ih => exact ih.succ_mono

/-- **Context monotonicity** — the one structural lemma the set world
needs (exchange is definitional, weakening and contraction are
absorbed by `⊆` and `insert`). Height-preserving. -/
theorem weaken_subset : ∀ {n : Nat} {Γ : Finset PLLFormula} {C : PLLFormula},
    G4sh n Γ C → ∀ {Γ' : Finset PLLFormula}, Γ ⊆ Γ' → G4sh n Γ' C := by
  intro n Γ C d
  induction d with
  | init h => intro Γ' hs; exact .init (hs h)
  | botL h => intro Γ' hs; exact .botL (hs h)
  | andR _ _ ih₁ ih₂ => intro Γ' hs; exact .andR (ih₁ hs) (ih₂ hs)
  | orR1 _ ih => intro Γ' hs; exact .orR1 (ih hs)
  | orR2 _ ih => intro Γ' hs; exact .orR2 (ih hs)
  | impR _ ih =>
      intro Γ' hs
      exact .impR (ih (Finset.insert_subset_insert _ hs))
  | laxR _ ih => intro Γ' hs; exact .laxR (ih hs)
  | laxL h _ ih =>
      intro Γ' hs
      exact .laxL (hs h) (ih (Finset.insert_subset_insert _ hs))
  | andL h _ ih =>
      intro Γ' hs
      exact .andL (hs h)
        (ih (Finset.insert_subset_insert _ (Finset.insert_subset_insert _ hs)))
  | orL h _ _ ih₁ ih₂ =>
      intro Γ' hs
      exact .orL (hs h) (ih₁ (Finset.insert_subset_insert _ hs))
        (ih₂ (Finset.insert_subset_insert _ hs))
  | impLProp h ha _ ih =>
      intro Γ' hs
      exact .impLProp (hs h) (hs ha) (ih (Finset.insert_subset_insert _ hs))
  | impLAnd h _ ih =>
      intro Γ' hs
      exact .impLAnd (hs h) (ih (Finset.insert_subset_insert _ hs))
  | impLOr h _ ih =>
      intro Γ' hs
      exact .impLOr (hs h)
        (ih (Finset.insert_subset_insert _ (Finset.insert_subset_insert _ hs)))
  | impLImp h _ _ ih₁ ih₂ =>
      intro Γ' hs
      exact .impLImp (hs h) (ih₁ (Finset.insert_subset_insert _ hs))
        (ih₂ (Finset.insert_subset_insert _ hs))
  | impLLax h _ _ ih₁ ih₂ =>
      intro Γ' hs
      exact .impLLax (hs h) (ih₁ hs) (ih₂ (Finset.insert_subset_insert _ hs))
  | impLLaxLax h hX _ _ ih₁ ih₂ =>
      intro Γ' hs
      exact .impLLaxLax (hs h) (hs hX)
        (ih₁ (Finset.insert_subset_insert _ hs))
        (ih₂ (Finset.insert_subset_insert _ hs))

end G4sh

private theorem perm_toFinset {Γ Δ : List PLLFormula} (h : Γ.Perm Δ) :
    Γ.toFinset = Δ.toFinset :=
  Finset.ext fun x => by
    rw [List.mem_toFinset, List.mem_toFinset]
    exact h.mem_iff

/-- **The list calculus embeds height-preservingly**: every transport
is `weaken_subset`. -/
theorem G4h.toSet : ∀ {n : Nat} {Γ : List PLLFormula} {E : PLLFormula},
    G4h n Γ E → G4sh n Γ.toFinset E := by
  intro n Γ E d
  induction d with
  | init h => exact .init (List.mem_toFinset.mpr h)
  | botL h => exact .botL (List.mem_toFinset.mpr h)
  | andR _ _ ih₁ ih₂ => exact .andR ih₁ ih₂
  | orR1 _ ih => exact .orR1 ih
  | orR2 _ ih => exact .orR2 ih
  | laxR _ ih => exact .laxR ih
  | impR _ ih =>
      rw [List.toFinset_cons] at ih
      exact .impR ih
  | @laxL _ _ A _ h _ ih =>
      rw [List.toFinset_cons] at ih
      exact .laxL (List.mem_toFinset.mpr h) ih
  | @andL _ Γ₀ Δ A B _ h _ ih =>
      have hΓ : Γ₀.toFinset = insert (A.and B) Δ.toFinset := by
        rw [perm_toFinset h, List.toFinset_cons]
      rw [List.toFinset_cons, List.toFinset_cons] at ih
      refine .andL (by rw [hΓ]; exact Finset.mem_insert_self _ _)
        (ih.weaken_subset ?_)
      exact Finset.insert_subset_insert _ (Finset.insert_subset_insert _
        (by rw [hΓ]; exact Finset.subset_insert _ _))
  | @orL _ Γ₀ Δ A B _ h _ _ ih₁ ih₂ =>
      have hΓ : Γ₀.toFinset = insert (A.or B) Δ.toFinset := by
        rw [perm_toFinset h, List.toFinset_cons]
      rw [List.toFinset_cons] at ih₁ ih₂
      refine .orL (by rw [hΓ]; exact Finset.mem_insert_self _ _)
        (ih₁.weaken_subset ?_) (ih₂.weaken_subset ?_)
      · exact Finset.insert_subset_insert _
          (by rw [hΓ]; exact Finset.subset_insert _ _)
      · exact Finset.insert_subset_insert _
          (by rw [hΓ]; exact Finset.subset_insert _ _)
  | @impLProp _ Γ₀ Δ a B _ h ha _ ih =>
      have hΓ : Γ₀.toFinset = insert ((prop a).ifThen B) Δ.toFinset := by
        rw [perm_toFinset h, List.toFinset_cons]
      rw [List.toFinset_cons] at ih
      refine .impLProp (by rw [hΓ]; exact Finset.mem_insert_self _ _)
        (by rw [hΓ]
            exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr ha))
        (ih.weaken_subset (Finset.insert_subset_insert _
          (by rw [hΓ]; exact Finset.subset_insert _ _)))
  | @impLBot _ Γ₀ Δ B _ h _ ih =>
      have hΓ : Γ₀.toFinset = insert (falsePLL.ifThen B) Δ.toFinset := by
        rw [perm_toFinset h, List.toFinset_cons]
      exact (ih.weaken_subset
        (by rw [hΓ]; exact Finset.subset_insert _ _)).succ_mono
  | @impLAnd _ Γ₀ Δ A B D _ h _ ih =>
      have hΓ : Γ₀.toFinset = insert ((A.and B).ifThen D) Δ.toFinset := by
        rw [perm_toFinset h, List.toFinset_cons]
      rw [List.toFinset_cons] at ih
      refine .impLAnd (by rw [hΓ]; exact Finset.mem_insert_self _ _)
        (ih.weaken_subset (Finset.insert_subset_insert _
          (by rw [hΓ]; exact Finset.subset_insert _ _)))
  | @impLOr _ Γ₀ Δ A B D _ h _ ih =>
      have hΓ : Γ₀.toFinset = insert ((A.or B).ifThen D) Δ.toFinset := by
        rw [perm_toFinset h, List.toFinset_cons]
      rw [List.toFinset_cons, List.toFinset_cons] at ih
      refine .impLOr (by rw [hΓ]; exact Finset.mem_insert_self _ _)
        (ih.weaken_subset (Finset.insert_subset_insert _
          (Finset.insert_subset_insert _
            (by rw [hΓ]; exact Finset.subset_insert _ _))))
  | @impLImp _ Γ₀ Δ A B D _ h _ _ ih₁ ih₂ =>
      have hΓ : Γ₀.toFinset = insert ((A.ifThen B).ifThen D) Δ.toFinset := by
        rw [perm_toFinset h, List.toFinset_cons]
      rw [List.toFinset_cons] at ih₁ ih₂
      refine .impLImp (by rw [hΓ]; exact Finset.mem_insert_self _ _)
        (ih₁.weaken_subset (Finset.insert_subset_insert _
          (by rw [hΓ]; exact Finset.subset_insert _ _)))
        (ih₂.weaken_subset (Finset.insert_subset_insert _
          (by rw [hΓ]; exact Finset.subset_insert _ _)))
  | @impLLax _ Γ₀ Δ A B _ h _ _ ih₁ ih₂ =>
      have hΓ : Γ₀.toFinset = insert (A.somehow.ifThen B) Δ.toFinset := by
        rw [perm_toFinset h, List.toFinset_cons]
      rw [List.toFinset_cons] at ih₂
      refine .impLLax (by rw [hΓ]; exact Finset.mem_insert_self _ _)
        ih₁
        (ih₂.weaken_subset (Finset.insert_subset_insert _
          (by rw [hΓ]; exact Finset.subset_insert _ _)))
  | @impLLaxLax _ Γ₀ Δ A B X _ h hX _ _ ih₁ ih₂ =>
      have hΓ : Γ₀.toFinset = insert (A.somehow.ifThen B) Δ.toFinset := by
        rw [perm_toFinset h, List.toFinset_cons]
      rw [List.toFinset_cons] at ih₁ ih₂
      refine .impLLaxLax (by rw [hΓ]; exact Finset.mem_insert_self _ _)
        (by rw [hΓ]
            exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr hX))
        ih₁
        (ih₂.weaken_subset (Finset.insert_subset_insert _
          (by rw [hΓ]; exact Finset.subset_insert _ _)))

namespace G4sh

private theorem ins_sub {x : PLLFormula} {s : Finset PLLFormula} :
    ∀ ψ ∈ (insert x s).toList, ψ ∈ x :: s.toList := by
  intro ψ hψ
  rw [Finset.mem_toList, Finset.mem_insert] at hψ
  rcases hψ with rfl | h
  · exact .head _
  · exact .tail _ (Finset.mem_toList.mpr h)

private theorem ins2_sub {x y : PLLFormula} {s : Finset PLLFormula} :
    ∀ ψ ∈ (insert x (insert y s)).toList, ψ ∈ x :: y :: s.toList := by
  intro ψ hψ
  rw [Finset.mem_toList, Finset.mem_insert, Finset.mem_insert] at hψ
  rcases hψ with rfl | rfl | h
  · exact .head _
  · exact .tail _ (.head _)
  · exact .tail _ (.tail _ (Finset.mem_toList.mpr h))

/-- **The cumulative calculus maps onto `SC`**, whose keeping rules
match the cumulative shapes; the three Dyckhoff rules go through the
same `SC.cut` constructions as `G4c.toSC`. -/
theorem toSC : ∀ {n : Nat} {Γs : Finset PLLFormula} {E : PLLFormula},
    G4sh n Γs E → SC Γs.toList E := by
  intro n Γs E d
  induction d with
  | init h => exact SC.init (Finset.mem_toList.mpr h)
  | botL h => exact SC.botL (Finset.mem_toList.mpr h)
  | andR _ _ ih₁ ih₂ => exact SC.andR ih₁ ih₂
  | orR1 _ ih => exact SC.orR1 ih
  | orR2 _ ih => exact SC.orR2 ih
  | laxR _ ih => exact SC.laxR ih
  | impR _ ih => exact SC.impR (ih.rename ins_sub)
  | laxL h _ ih =>
      exact SC.laxL (Finset.mem_toList.mpr h) (ih.rename ins_sub)
  | andL h _ ih =>
      exact SC.andL (Finset.mem_toList.mpr h) (ih.rename ins2_sub)
  | orL h _ _ ih₁ ih₂ =>
      exact SC.orL (Finset.mem_toList.mpr h)
        (ih₁.rename ins_sub) (ih₂.rename ins_sub)
  | impLProp h ha _ ih =>
      exact SC.impL (Finset.mem_toList.mpr h)
        (SC.init (Finset.mem_toList.mpr ha)) (ih.rename ins_sub)
  | @impLAnd _ Γ₀ A B D _ h _ ih =>
      have hmem := Finset.mem_toList.mpr h
      have p : SC Γ₀.toList (A.ifThen (B.ifThen D)) := by
        refine SC.impR (SC.impR ?_)
        exact SC.impL (A := A.and B) (.tail _ (.tail _ hmem))
          (SC.andR (SC.iden _ (.tail _ (.head _))) (SC.iden _ (.head _)))
          (SC.iden _ (.head _))
      exact SC.cut p (ih.rename ins_sub)
  | @impLOr _ Γ₀ A B D _ h _ ih =>
      have hmem := Finset.mem_toList.mpr h
      have p₁ : SC Γ₀.toList (A.ifThen D) :=
        SC.impR (SC.impL (A := A.or B) (.tail _ hmem)
          (SC.orR1 (SC.iden _ (.head _))) (SC.iden _ (.head _)))
      have p₂ : SC Γ₀.toList (B.ifThen D) :=
        SC.impR (SC.impL (A := A.or B) (.tail _ hmem)
          (SC.orR2 (SC.iden _ (.head _))) (SC.iden _ (.head _)))
      refine SC.cut p₁ (SC.cut (p₂.rename fun ψ hψ => .tail _ hψ)
        (ih.rename ?_))
      intro ψ hψ
      rcases List.mem_cons.mp (ins2_sub ψ hψ) with rfl | h'
      · exact .tail _ (.head _)
      rcases List.mem_cons.mp h' with rfl | h''
      · exact .head _
      · exact .tail _ (.tail _ h'')
  | @impLImp _ Γ₀ A B D _ h _ _ ih₁ ih₂ =>
      have hmem := Finset.mem_toList.mpr h
      have hBD : SC Γ₀.toList (B.ifThen D) :=
        SC.impR (SC.impL (A := A.ifThen B) (.tail _ hmem)
          (SC.impR (SC.iden _ (.tail _ (.head _)))) (SC.iden _ (.head _)))
      have hAB : SC Γ₀.toList (A.ifThen B) := SC.cut hBD (ih₁.rename ins_sub)
      exact SC.impL hmem hAB (ih₂.rename ins_sub)
  | impLLax h _ _ ih₁ ih₂ =>
      exact SC.impL (Finset.mem_toList.mpr h) (SC.laxR ih₁)
        (ih₂.rename ins_sub)
  | impLLaxLax h hX _ _ ih₁ ih₂ =>
      exact SC.impL (Finset.mem_toList.mpr h)
        (SC.laxL (Finset.mem_toList.mpr hX) (ih₁.rename ins_sub))
        (ih₂.rename ins_sub)

end G4sh

/-- **The set calculus proves exactly the `G4c` sequents.** -/
theorem G4c.iff_set {Γ : List PLLFormula} {E : PLLFormula} :
    G4c Γ E ↔ G4s Γ.toFinset E := by
  constructor
  · rintro ⟨n, d⟩
    exact ⟨n, d.toSet⟩
  · rintro ⟨n, d⟩
    refine G4c.completeness (d.toSC.rename ?_)
    intro ψ hψ
    rw [Finset.mem_toList, List.mem_toFinset] at hψ
    exact hψ
