/-
# `LaxLogic.QLL.Sound` — the checker only accepts derivations

Statement 1 of the four distinguished in discussion with Matthew:

    infer Γ p = .ok M   → Derivable Γ p M
    check Γ p M = .ok () → Derivable Γ p M

Both sides are internal to this development, so this establishes nothing
mathematical about the paper.  What it buys is that `check`'s verdict *means*
something: an accepted term is a derivation in the sense of Fig. 5, and the
obligations `checkTop` returns are the obligations of a real derivation.  It is
a prerequisite for the statements that do carry content — soundness against the
Fig. 4 refinement reading, and sufficiency of the obligations.

The proof follows the checker's own recursion, via the two-motive functional
induction principle Lean generates for the mutual well-founded definition.
-/
import LaxLogic.QLL.Check

namespace LaxLogic.QLL

/-! ## Freshness

`check` picks its binder names with `freshFor`; `Derivable` demands `FreshP` or
`FreshI`.  These say the choice satisfies the demand.  Each `freshFor` argument
in `Check.lean` is the concatenation of exactly the lists the corresponding
side condition mentions, which is why these go through. -/

theorem freshFor_notMem_of_mem_append {A B : List String} {x : String}
    (h : freshFor (A ++ B) = x) : x ∉ A ∧ x ∉ B := by
  subst h
  have h := freshFor_notMem (A ++ B)
  exact ⟨fun hm => h (List.mem_append.mpr (Or.inl hm)),
         fun hm => h (List.mem_append.mpr (Or.inr hm))⟩

theorem freshP_freshFor (Γ : Ctx) (p : Pf) :
    FreshP (freshFor (Ctx.fvP Γ ++ p.fvP)) Γ p :=
  freshFor_notMem_of_mem_append rfl

theorem freshI_freshFor (Γ : Ctx) (p : Pf) (M : Form) :
    FreshI (freshFor (Ctx.fvI Γ ++ p.fvI ++ M.fv)) Γ p M := by
  have h := freshFor_notMem (Ctx.fvI Γ ++ p.fvI ++ M.fv)
  refine ⟨fun hm => h ?_, fun hm => h ?_, fun hm => h ?_⟩
  · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hm)))
  · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hm)))
  · exact List.mem_append.mpr (Or.inr hm)

/-- The `∃E` case chooses away from the goal as well, so the eigenvariable
condition comes for free. -/
theorem freshI_freshFor4 (Γ : Ctx) (p : Pf) (M K : Form) :
    FreshI (freshFor (Ctx.fvI Γ ++ p.fvI ++ M.fv ++ K.fv)) Γ p M ∧
      freshFor (Ctx.fvI Γ ++ p.fvI ++ M.fv ++ K.fv) ∉ K.fv := by
  have h := freshFor_notMem (Ctx.fvI Γ ++ p.fvI ++ M.fv ++ K.fv)
  refine ⟨⟨fun hm => h ?_, fun hm => h ?_, fun hm => h ?_⟩, fun hm => h ?_⟩
  · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl
      (List.mem_append.mpr (Or.inl hm)))))
  · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl
      (List.mem_append.mpr (Or.inr hm)))))
  · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hm)))
  · exact List.mem_append.mpr (Or.inr hm)

/-! ## Context lookup -/

/-- `Ctx.lookup?` only ever finds a *variable* entry, which is what `Derivable.var`
requires. -/
theorem lookup_mem {Γ : Ctx} {x : String} {M : Form} :
    Ctx.lookup? Γ x = some M → (Pf.fvar x, M) ∈ Γ := by
  induction Γ with
  | nil => intro h; simp [Ctx.lookup?] at h
  | cons e Γ' ih =>
    obtain ⟨q, N⟩ := e
    match q with
    | .fvar y =>
        intro h
        simp only [Ctx.lookup?] at h
        by_cases hy : y = x
        · subst hy
          simp at h
          subst h
          exact List.Mem.head _
        · rw [if_neg hy] at h
          exact List.Mem.tail _ (ih h)
    | .bvar _ | .star | .pair _ _ | .fst _ | .snd _ | .inl _ | .inr _
    | .caseOr _ _ _ | .lam _ | .app _ _ | .val _ _ | .letQ _ _ _ | .gen _
    | .inst _ _ | .pack _ _ | .caseEx _ _ | .exf _ _ =>
        intro h
        simp only [Ctx.lookup?] at h
        exact List.Mem.tail _ (ih h)

end LaxLogic.QLL
