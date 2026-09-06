/-
# `LaxLogic.QLL.Kit` — what a checker is built from

Fresh names and the proof that they are fresh; the size lemmas that justify the
recursion; the error type; context lookup.  Split out so that `Certify.lean`
does not depend on a second checker.

Everything here was originally written to *prove* a soundness theorem about a
`Prop`-valued family.  That theorem no longer exists — `Certify.lean` returns
the derivation, so soundness is typed — but the lemmas survived unchanged,
because constructing a derivation needs exactly what proving one needed: that
`freshFor`'s choice satisfies the rule's freshness condition, and that a
successful context lookup lands on a *variable* entry.
-/
import LaxLogic.QLL.Deriv
import LaxLogic.QLL.Lc

namespace LaxLogic.QLL

/-! ## Fresh names -/

/--
A name not occurring in `used`: every name in the list concatenated onto a
`"z"`, so the result is strictly longer than any of them.

Crude on purpose.  A counter would need a search to avoid collisions, and the
freshness property is wanted as a *theorem* for soundness, not as a runtime
check.
-/
def freshFor : List String → String
  | []      => "z"
  | s :: ss => s ++ freshFor ss

theorem freshFor_length : ∀ ss : List String,
    (freshFor ss).length = 1 + (ss.map String.length).sum
  | []      => rfl
  | s :: ss => by
      simp [freshFor, String.length_append, freshFor_length ss]
      omega

theorem length_le_sum : ∀ (ss : List String) (s : String), s ∈ ss →
    s.length ≤ (ss.map String.length).sum
  | [],      _, h => absurd h (by simp)
  | t :: ts, s, h => by
      rcases List.mem_cons.mp h with rfl | h'
      · simp
      · have := length_le_sum ts s h'; simp; omega

/-- `freshFor` does what its name says.  Soundness will need this. -/
theorem freshFor_notMem (ss : List String) : freshFor ss ∉ ss := by
  intro h
  have h1 := length_le_sum ss _ h
  have h2 := freshFor_length ss
  omega

/-! ## Size is preserved by opening

The checker recurses on opened bodies, which are not structural subterms of
the binder, so termination is by `Pf.size`.  Opening with a *variable* leaves
the size alone; opening an individual leaves it alone for any term, since
`openI` touches only the embedded `Tm`s. -/

theorem size_openP (k : Nat) (z : String) (p : Pf) :
    (Pf.openP k (.fvar z) p).size = p.size := by
  induction p generalizing k with
  | bvar i => by_cases h : i = k <;> simp [Pf.openP, Pf.size, h]
  | _ => simp_all [Pf.openP, Pf.size]

theorem size_openI (k : Nat) (u : Tm) (p : Pf) :
    (Pf.openI k u p).size = p.size := by
  induction p generalizing k <;> simp_all [Pf.openI, Pf.size]

/-! ## Errors -/

/-- Why a check failed.  Carries enough to locate the fault. -/
inductive Err where
  /-- A de Bruijn index escaped its binder: the term is not locally closed. -/
  | looseIndex (i : Nat)
  /-- A free proof variable with no variable entry in the context. -/
  | unbound (x : String)
  /-- The inferred formula had the wrong shape for the rule the term names. -/
  | expected (shape : String) (got : Form)
  /-- Inferred and required formulas differ. -/
  | mismatch (required got : Form)
  /-- A term that cannot be inferred appeared where no goal was available. -/
  | notInferable (term : String)
  /-- `∃E`'s eigenvariable escaped into the conclusion. -/
  | escapes (a : String) (K : Form)
  /-- `◯E` mixed the two modalities, which Fig. 5 does not permit. -/
  | modalityClash (found required : Q)
  /-- Inference for `∀` produced a body with a loose de Bruijn index, so the
  open/close roundtrip is unavailable.  Cannot arise for well-formed input;
  refused rather than mis-accepted. -/
  | notLocallyClosed (M : Form)
  deriving Repr, DecidableEq

/-- The formula attached to a *variable* entry of the context. -/
def Ctx.lookup? (Γ : Ctx) (x : String) : Option Form :=
  match Γ with
  | []                 => none
  | (.fvar y, M) :: Γ' => if y = x then some M else Ctx.lookup? Γ' x
  | _ :: Γ'            => Ctx.lookup? Γ' x

/-! ## Freshness, and lookup -/

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
