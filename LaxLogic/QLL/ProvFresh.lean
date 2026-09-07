/-
# `LaxLogic.QLL.ProvFresh` — renaming, and the exists-fresh forms of the binders

`Prv`'s two binding rules are stated cofinitely: `allI` asks for a derivation
at *every* sufficiently fresh name.  The saturation construction has the
opposite shape — it produces a derivation at **one** name and needs the rule.
Bridging the two is exactly the renaming lemma, and that is all this file is.

The two consequences are the ones the canonical model uses:

    Γ ⊢ A⟨c⟩  and c fresh for Γ, A     ⟹  Γ ⊢ ∀x. A
    Γ ⊢ ∃x. A,  A⟨c⟩, Γ ⊢ K, c fresh   ⟹  Γ ⊢ K

The first says a parameter not occurring in the context may be generalised;
the second is the elimination that lets a witness be *added* to a theory
without changing what it proves.  Both are what make the Henkin step
conservative, which is the point on which the naive construction fails: adding
`∃yφ(y) ⊃ φ(c)` as an axiom is not conservative, adding `φ(c)` when `∃yφ(y)` is
already present is.
-/
import LaxLogic.QLL.Prov
import LaxLogic.QLL.Rename

namespace LaxLogic.QLL

/-! ## Local closedness survives renaming

Renaming maps free individuals to free individuals, so no index moves. -/

mutual
theorem Tm.lcAt_renameI (a b : String) (k : Nat) :
    ∀ t : Tm, Tm.lcAt k t → Tm.lcAt k (Tm.renameI a b t)
  | .bvar _,  h => h
  | .fvar y,  _ => by by_cases hy : y = a <;> simp [Tm.renameI, hy, Tm.lcAt]
  | .fn _ ts, h => Tm.lcAtList_renameIList a b k ts h
theorem Tm.lcAtList_renameIList (a b : String) (k : Nat) :
    ∀ ts : List Tm, Tm.lcAtList k ts → Tm.lcAtList k (Tm.renameIList a b ts)
  | [],      h => h
  | t :: ts, h => ⟨Tm.lcAt_renameI a b k t h.1, Tm.lcAtList_renameIList a b k ts h.2⟩
end

/-! ## The renaming lemma

Renaming a derivation renames its context and its conclusion.  The two binder
cases enlarge the excluded set by `a`, so that the name the premise is
instantiated at is one the renaming fixes. -/

theorem Prv.renameI (a b : String) {Γ : List Form} {A : Form} (h : Prv Γ A) :
    Prv (Γ.map (Form.renameI a b)) (Form.renameI a b A) := by
  induction h with
  | var hmem => exact .var (List.mem_map_of_mem hmem)
  | topI => exact .topI
  | botE _ ih => exact .botE ih
  | andI _ _ ih₁ ih₂ => exact .andI ih₁ ih₂
  | andE₁ _ ih => exact .andE₁ ih
  | andE₂ _ ih => exact .andE₂ ih
  | orI₁ _ ih => exact .orI₁ ih
  | orI₂ _ ih => exact .orI₂ ih
  | orE _ _ _ ih ih₁ ih₂ => exact .orE ih ih₁ ih₂
  | impI _ ih => exact .impI ih
  | impE _ _ ih₁ ih₂ => exact .impE ih₁ ih₂
  | circI _ ih => exact .circI ih
  | circE _ _ ih₁ ih₂ => exact .circE ih₁ ih₂
  | allE t ht _ ih =>
      rw [Form.renameI_openAt]
      exact .allE _ (Tm.lcAt_renameI a b 0 t ht) ih
  | exI t ht _ ih =>
      refine .exI (Tm.renameI a b t) (Tm.lcAt_renameI a b 0 t ht) ?_
      rw [← Form.renameI_openAt]
      exact ih
  | @allI Γ' A' L _ ih =>
      refine .allI (a :: L) (fun c hc => ?_)
      have hca : c ≠ a := fun h => hc (by simp [h])
      have hcL : c ∉ L := fun h => hc (by simp [h])
      have := ih c hcL
      rwa [Form.renameI_openWith, if_neg hca] at this
  | @exE Γ' A' K L _ _ ih₁ ih₂ =>
      refine .exE (a :: L) ih₁ (fun c hc => ?_)
      have hca : c ≠ a := fun h => hc (by simp [h])
      have hcL : c ∉ L := fun h => hc (by simp [h])
      have := ih₂ c hcL
      rwa [List.map_cons, Form.renameI_openWith, if_neg hca] at this

/-! ## Renaming away a parameter

If `c` occurs in no formula of `Γ`, renaming it in `Γ` changes nothing. -/

theorem ctxFv_map_renameI_eq {Γ : List Form} {c x : String} (hΓ : c ∉ ctxFv Γ) :
    Γ.map (Form.renameI c x) = Γ := by
  rw [List.map_congr_left (g := id)
    (fun B hB => Form.renameI_eq_of_notMem c x B (fun hc => hΓ (mem_ctxFv hB hc))),
    List.map_id]

/-! ## The exists-fresh binders -/

/-- Generalisation on a parameter fresh for the context. -/
theorem Prv.allI_of_fresh {Γ : List Form} {A : Form} {c : String}
    (hΓ : c ∉ ctxFv Γ) (hA : c ∉ A.fv) (h : Prv Γ (A.openWith c)) :
    Prv Γ (.forall_ A) := by
  refine .allI (c :: (ctxFv Γ ++ A.fv)) (fun x _ => ?_)
  have := h.renameI c x
  rwa [ctxFv_map_renameI_eq hΓ, Form.renameI_openWith, if_pos rfl,
    Form.renameI_eq_of_notMem c x A hA] at this

/-- Elimination at a parameter fresh for the context, the existential and the
conclusion. -/
theorem Prv.exE_of_fresh {Γ : List Form} {A K : Form} {c : String}
    (hΓ : c ∉ ctxFv Γ) (hA : c ∉ A.fv) (hK : c ∉ K.fv)
    (hex : Prv Γ (.exists_ A)) (h : Prv (A.openWith c :: Γ) K) :
    Prv Γ K := by
  refine .exE (c :: (ctxFv Γ ++ A.fv ++ K.fv)) hex (fun x _ => ?_)
  have := h.renameI c x
  rw [List.map_cons, ctxFv_map_renameI_eq hΓ, Form.renameI_openWith, if_pos rfl,
    Form.renameI_eq_of_notMem c x A hA, Form.renameI_eq_of_notMem c x K hK] at this
  exact this

end LaxLogic.QLL
