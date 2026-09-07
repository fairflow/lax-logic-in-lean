/-
# `LaxLogic.QLL.Prov` — the consequence relation, for the model theory

Fig. 5 with the proof terms erased and the binding rules quantified
**cofinitely**: `∀I` asks for a derivation for every eigenvariable outside some
finite set, rather than for one.  Nothing else changes, and the modal rules
still forbid mixing `◯∀` with `◯∃`.

Two reasons for a second presentation rather than reusing `Derives`.

*The model theory does not need proof terms.*  Contexts here are lists of
formulas, so weakening is a one-line induction instead of the eigenvariable
bookkeeping of `Weaken.lean`.

*Cofinite quantification is what makes the canonical model work.*  Building a
derivation at a chosen fresh name is easy; needing one at **every** fresh name
is what the truth lemma has to supply, and an exists-fresh rule cannot be
applied that way without the renaming lemma.  `Derives` keeps exists-fresh
because `Certify.lean` must be able to *apply* its rules; here nothing is
applied by a checker.

## Where this sits

* `Prv Γ A → Γ ⊫ A` — soundness, below.
* `Γ ⊫ A → Prv Γ A` — completeness, in `Complete.lean`.
* `Derives p Γ A → Prv Γ.forms A` — erasure, **OPEN**.  Each exists-fresh
  binder has to be re-based to every fresh name, which `Derives.renameI`
  supplies pointwise but which needs a recursion on the size of a derivation
  rather than on its structure.
* `Prv Γ A → ∃ p, Derives p _ A` — **OPEN**, and the more useful direction:
  it needs closing a proof term over a named variable, which the syntax does
  not yet have.
-/
import LaxLogic.QLL.Kripke
import LaxLogic.QLL.Kit

namespace LaxLogic.QLL

/-- Fig. 5 on formula contexts, with cofinite eigenvariables. -/
inductive Prv : List Form → Form → Prop where
  | var   {Γ A} : A ∈ Γ → Prv Γ A
  | topI  {Γ} : Prv Γ .top
  | botE  {Γ A} : Prv Γ .bot → Prv Γ A
  | andI  {Γ A B} : Prv Γ A → Prv Γ B → Prv Γ (.and A B)
  | andE₁ {Γ A B} : Prv Γ (.and A B) → Prv Γ A
  | andE₂ {Γ A B} : Prv Γ (.and A B) → Prv Γ B
  | orI₁  {Γ A B} : Prv Γ A → Prv Γ (.or A B)
  | orI₂  {Γ A B} : Prv Γ B → Prv Γ (.or A B)
  | orE   {Γ A B K} : Prv Γ (.or A B) → Prv (A :: Γ) K → Prv (B :: Γ) K → Prv Γ K
  | impI  {Γ A B} : Prv (A :: Γ) B → Prv Γ (.imp A B)
  | impE  {Γ A B} : Prv Γ (.imp A B) → Prv Γ A → Prv Γ B
  | circI {Γ q A} : Prv Γ A → Prv Γ (.circ q A)
  | circE {Γ q A B} : Prv Γ (.circ q A) → Prv (A :: Γ) (.circ q B) → Prv Γ (.circ q B)
  | allI  {Γ A} (L : List String) :
      (∀ a, a ∉ L → Prv Γ (A.openWith a)) → Prv Γ (.forall_ A)
  | allE  {Γ A} (t : Tm) : Tm.lcAt 0 t → Prv Γ (.forall_ A) → Prv Γ (A.openAt 0 t)
  | exI   {Γ A} (t : Tm) : Tm.lcAt 0 t → Prv Γ (A.openAt 0 t) → Prv Γ (.exists_ A)
  | exE   {Γ A K} (L : List String) :
      Prv Γ (.exists_ A) → (∀ a, a ∉ L → Prv (A.openWith a :: Γ) K) → Prv Γ K

@[inherit_doc] infix:55 " ⊢q " => Prv

/-- Weakening — free, because the binders are cofinite. -/
theorem Prv.weaken {Γ Δ : List Form} {A : Form} (h : Γ ⊢q A) (hs : ∀ B ∈ Γ, B ∈ Δ) :
    Δ ⊢q A := by
  induction h generalizing Δ with
  | var h => exact .var (hs _ h)
  | topI => exact .topI
  | botE _ ih => exact .botE (ih hs)
  | andI _ _ ih₁ ih₂ => exact .andI (ih₁ hs) (ih₂ hs)
  | andE₁ _ ih => exact .andE₁ (ih hs)
  | andE₂ _ ih => exact .andE₂ (ih hs)
  | orI₁ _ ih => exact .orI₁ (ih hs)
  | orI₂ _ ih => exact .orI₂ (ih hs)
  | orE _ _ _ ih₀ ih₁ ih₂ =>
      exact .orE (ih₀ hs) (ih₁ (List.cons_subset_cons _ hs)) (ih₂ (List.cons_subset_cons _ hs))
  | impI _ ih => exact .impI (ih (List.cons_subset_cons _ hs))
  | impE _ _ ih₁ ih₂ => exact .impE (ih₁ hs) (ih₂ hs)
  | circI _ ih => exact .circI (ih hs)
  | circE _ _ ih₁ ih₂ => exact .circE (ih₁ hs) (ih₂ (List.cons_subset_cons _ hs))
  | allI L _ ih => exact .allI L (fun a ha => ih a ha hs)
  | allE t ht _ ih => exact .allE t ht (ih hs)
  | exI t ht _ ih => exact .exI t ht (ih hs)
  | exE L _ _ ih₀ ih => exact .exE L (ih₀ hs) (fun a ha => ih a ha (List.cons_subset_cons _ hs))

/-! ## Soundness -/

/-- The free individuals of a context. -/
def ctxFv : List Form → List String
  | []     => []
  | A :: Γ => A.fv ++ ctxFv Γ

theorem mem_ctxFv {Γ : List Form} {A : Form} {x : String}
    (hA : A ∈ Γ) (hx : x ∈ A.fv) : x ∈ ctxFv Γ := by
  induction Γ with
  | nil => cases hA
  | cons B Γ ih =>
      rcases List.mem_cons.mp hA with rfl | h
      · exact List.mem_append.mpr (Or.inl hx)
      · exact List.mem_append.mpr (Or.inr (ih h))

theorem assign_mono {M : KModel} {s v : M.S} {ρ : String → M.D}
    (h : M.Ri s v) (hρ : M.Assign s ρ) : M.Assign v ρ :=
  KModel.Assign.mono M h hρ

/-- `ρ` updated at one name. -/
def updρ {M : KModel} (ρ : String → M.D) (a : String) (d : M.D) : String → M.D :=
  fun y => if y = a then d else ρ y

theorem updρ_eq {M : KModel} (ρ : String → M.D) (a : String) (d : M.D) :
    updρ ρ a d a = d := by simp [updρ]

theorem updρ_of_ne {M : KModel} (ρ : String → M.D) {a y : String} (d : M.D) (h : y ≠ a) :
    updρ ρ a d y = ρ y := by simp [updρ, h]

/-- **Soundness**: what is provable holds at every state of every model whose
assignment is at that state and where the context holds. -/
theorem Prv.sound {Γ : List Form} {A : Form} (h : Γ ⊢q A) : Γ ⊫ A := by
  induction h with
  | var h => intro _ _ _ _ hΓ; exact hΓ _ h
  | topI => intro _ _ _ _ _; trivial
  | botE _ ih => intro M s ρ hρ hΓ; exact M.force_of_fallible _ ρ [] (ih M s ρ hρ hΓ)
  | andI _ _ ih₁ ih₂ => intro M s ρ hρ hΓ; exact ⟨ih₁ M s ρ hρ hΓ, ih₂ M s ρ hρ hΓ⟩
  | andE₁ _ ih => intro M s ρ hρ hΓ; exact (ih M s ρ hρ hΓ).1
  | andE₂ _ ih => intro M s ρ hρ hΓ; exact (ih M s ρ hρ hΓ).2
  | orI₁ _ ih => intro M s ρ hρ hΓ; exact Or.inl (ih M s ρ hρ hΓ)
  | orI₂ _ ih => intro M s ρ hρ hΓ; exact Or.inr (ih M s ρ hρ hΓ)
  | orE _ _ _ ih₀ ih₁ ih₂ =>
      intro M s ρ hρ hΓ
      rcases ih₀ M s ρ hρ hΓ with h | h
      · exact ih₁ M s ρ hρ (fun B hB => by
          rcases List.mem_cons.mp hB with rfl | hB
          · exact h
          · exact hΓ B hB)
      · exact ih₂ M s ρ hρ (fun B hB => by
          rcases List.mem_cons.mp hB with rfl | hB
          · exact h
          · exact hΓ B hB)
  | impI _ ih =>
      intro M s ρ hρ hΓ v hv hA
      exact ih M v ρ (assign_mono hv hρ) (fun B hB => by
        rcases List.mem_cons.mp hB with rfl | hB
        · exact hA
        · exact M.hered B ρ [] hv (hΓ B hB))
  | impE _ _ ih₁ ih₂ =>
      intro M s ρ hρ hΓ
      exact ih₁ M s ρ hρ hΓ s (M.refl_i s) (ih₂ M s ρ hρ hΓ)
  | @circI Γ q A _ ih =>
      intro M s ρ hρ hΓ
      cases q
      · intro v hv; exact ⟨v, M.refl_A v, M.hered A ρ [] hv (ih M s ρ hρ hΓ)⟩
      · intro v hv; exact ⟨v, M.refl_E v, M.hered A ρ [] hv (ih M s ρ hρ hΓ)⟩
  | @circE Γ q A B _ _ ih₁ ih₂ =>
      intro M s ρ hρ hΓ
      cases q
      · intro v hv
        obtain ⟨u, hvu, hu⟩ := ih₁ M s ρ hρ hΓ v hv
        have hsu : M.Ri s u := M.trans_i hv (M.sub_A hvu)
        obtain ⟨w, huw, hw⟩ := ih₂ M u ρ (assign_mono hsu hρ) (fun C hC => by
          rcases List.mem_cons.mp hC with rfl | hC
          · exact hu
          · exact M.hered C ρ [] hsu (hΓ C hC)) u (M.refl_i u)
        exact ⟨w, M.trans_A hvu huw, hw⟩
      · intro v hv
        obtain ⟨u, hvu, hu⟩ := ih₁ M s ρ hρ hΓ v hv
        have hsu : M.Ri s u := M.trans_i hv (M.sub_E hvu)
        obtain ⟨w, huw, hw⟩ := ih₂ M u ρ (assign_mono hsu hρ) (fun C hC => by
          rcases List.mem_cons.mp hC with rfl | hC
          · exact hu
          · exact M.hered C ρ [] hsu (hΓ C hC)) u (M.refl_i u)
        exact ⟨w, M.trans_E hvu huw, hw⟩
  | @allI Γ A L _ ih =>
      intro M s ρ hρ hΓ v hv d hd
      obtain ⟨a, hnot⟩ : ∃ a, a ∉ (L ++ A.fv ++ ctxFv Γ) := ⟨_, freshFor_notMem _⟩
      simp only [List.mem_append, not_or] at hnot
      have haL : a ∉ L := hnot.1.1
      have hneA : ∀ x, x ∈ A.fv → x ≠ a := by
        intro x hx hxa; subst hxa; exact hnot.1.2 hx
      have hneΓ : ∀ x, x ∈ ctxFv Γ → x ≠ a := by
        intro x hx hxa; subst hxa; exact hnot.2 hx
      have hρ' : M.Assign v (updρ ρ a d) := fun y => by
        by_cases hy : y = a
        · simpa [updρ, hy] using hd
        · rw [updρ_of_ne ρ d hy]; exact (assign_mono hv hρ) y
      have key := ih a haL M v (updρ ρ a d) hρ' (fun B hB => by
        refine (M.force_congr B v ρ (updρ ρ a d) [] ?_).mp (M.hered B ρ [] hv (hΓ B hB))
        intro x hx
        exact (updρ_of_ne ρ d (hneΓ x (mem_ctxFv hB hx))).symm)
      rw [M.force_openWith (updρ ρ a d) a A v, updρ_eq] at key
      exact (M.force_congr A v (updρ ρ a d) ρ [d]
        (fun x hx => updρ_of_ne ρ d (hneA x hx))).mp key
  | @allE Γ A t ht _ ih =>
      intro M s ρ hρ hΓ
      have key := ih M s ρ hρ hΓ s (M.refl_i s) (M.evTm ρ [] t) (M.evTm_dom hρ (by simp) t)
      exact (M.force_openAt ρ t ht A s []).mpr key
  | @exI Γ A t ht _ ih =>
      intro M s ρ hρ hΓ
      exact ⟨M.evTm ρ [] t, M.evTm_dom hρ (by simp) t,
             (M.force_openAt ρ t ht A s []).mp (ih M s ρ hρ hΓ)⟩
  | @exE Γ A K L _ _ ih₀ ih =>
      intro M s ρ hρ hΓ
      obtain ⟨d, hd, hA⟩ := ih₀ M s ρ hρ hΓ
      obtain ⟨a, hnot⟩ : ∃ a, a ∉ (L ++ A.fv ++ K.fv ++ ctxFv Γ) := ⟨_, freshFor_notMem _⟩
      simp only [List.mem_append, not_or] at hnot
      have haL : a ∉ L := hnot.1.1.1
      have hneA : ∀ x, x ∈ A.fv → x ≠ a := by
        intro x hx hxa; subst hxa; exact hnot.1.1.2 hx
      have hneK : ∀ x, x ∈ K.fv → x ≠ a := by
        intro x hx hxa; subst hxa; exact hnot.1.2 hx
      have hneΓ : ∀ x, x ∈ ctxFv Γ → x ≠ a := by
        intro x hx hxa; subst hxa; exact hnot.2 hx
      have hρ' : M.Assign s (updρ ρ a d) := fun y => by
        by_cases hy : y = a
        · simpa [updρ, hy] using hd
        · rw [updρ_of_ne ρ d hy]; exact hρ y
      have key := ih a haL M s (updρ ρ a d) hρ' (fun B hB => by
        rcases List.mem_cons.mp hB with rfl | hB'
        · rw [M.force_openWith (updρ ρ a d) a A s, updρ_eq]
          exact (M.force_congr A s ρ (updρ ρ a d) [d]
            (fun x hx => (updρ_of_ne ρ d (hneA x hx)).symm)).mp hA
        · exact (M.force_congr B s ρ (updρ ρ a d) []
            (fun x hx => (updρ_of_ne ρ d (hneΓ x (mem_ctxFv hB' hx))).symm)).mp (hΓ B hB'))
      exact (M.force_congr K s (updρ ρ a d) ρ []
        (fun x hx => updρ_of_ne ρ d (hneK x hx))).mp key

end LaxLogic.QLL
