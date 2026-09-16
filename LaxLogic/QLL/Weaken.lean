/-
# `LaxLogic.QLL.Weaken` — weakening, and the eigenvariables a derivation uses

Weakening is not free here, and it is worth saying exactly why.

Fig. 5's binding rules pick a **specific** eigenvariable and require it fresh
for the context: `impI z (hz : FreshP z Γ p) …`.  That is the *exists-fresh*
formulation.  Adding an entry to `Γ` can invalidate such an `hz` — the new
entry may use the very name `z` — so `Derives p Γ A → Derives p (e :: Γ) A` is
**false as stated**, and no induction repairs it: the eigenvariable is fixed
inside the derivation.

The literature's answer is cofinite quantification (Aydemir et al., *Engineering
Formal Metatheory*), where a binding rule quantifies over all names outside a
finite set and weakening becomes routine.  That trade is not free either: a
cofinite rule can no longer be *applied* by exhibiting one fresh name, so
`Certify.lean` could not build a derivation without first proving renaming.

What is proved here instead is weakening under a hypothesis that names the
obstruction: the derivation's eigenvariables must avoid the enlarged context.
`Derives.namesP` and `Derives.namesI` collect them, so the hypothesis is
checkable, and for a derivation the checker built it holds by construction —
`freshFor` can be given the list.

Two facts make the induction go through.  First, `namesP_fresh`: a
derivation's eigenvariables are already fresh for its *own* context.  Second, a
consequence of that — nested eigenvariables are automatically distinct, because
the inner rule's freshness condition sees the outer one in the context.  So the
hypothesis never has to be re-established under a binder.

Weakening is to any **superset**, not to a cons: the target context is
constrained only by membership, which is all `var` ever uses.
-/
import LaxLogic.QLL.Deriv

namespace LaxLogic.QLL

/-! ## The eigenvariables of a derivation -/

/-- Every proof variable chosen by a binding rule inside the derivation. -/
def Derives.namesP : {Γ : Ctx} → {p : Pf} → {A : Form} → Derives p Γ A → List String
  | _, _, _, .var _            => []
  | _, _, _, .topI             => []
  | _, _, _, .botE d           => d.namesP
  | _, _, _, .andI d e         => d.namesP ++ e.namesP
  | _, _, _, .andE₁ d          => d.namesP
  | _, _, _, .andE₂ d          => d.namesP
  | _, _, _, .orI₁ d           => d.namesP
  | _, _, _, .orI₂ d           => d.namesP
  | _, _, _, .orE y z _ _ dr d₁ d₂ => y :: z :: (dr.namesP ++ d₁.namesP ++ d₂.namesP)
  | _, _, _, .impI z _ d       => z :: d.namesP
  | _, _, _, .impE d e         => d.namesP ++ e.namesP
  | _, _, _, .circI d          => d.namesP
  | _, _, _, .circE z _ dp db  => z :: (dp.namesP ++ db.namesP)
  | _, _, _, .allI _ _ d       => d.namesP
  | _, _, _, .allE _ d _       => d.namesP
  | _, _, _, .exI _ d          => d.namesP
  | _, _, _, .exE _ z _ _ _ dr db => z :: (dr.namesP ++ db.namesP)

/-- Every individual chosen by a binding rule inside the derivation. -/
def Derives.namesI : {Γ : Ctx} → {p : Pf} → {A : Form} → Derives p Γ A → List String
  | _, _, _, .var _            => []
  | _, _, _, .topI             => []
  | _, _, _, .botE d           => d.namesI
  | _, _, _, .andI d e         => d.namesI ++ e.namesI
  | _, _, _, .andE₁ d          => d.namesI
  | _, _, _, .andE₂ d          => d.namesI
  | _, _, _, .orI₁ d           => d.namesI
  | _, _, _, .orI₂ d           => d.namesI
  | _, _, _, .orE _ _ _ _ dr d₁ d₂ => dr.namesI ++ d₁.namesI ++ d₂.namesI
  | _, _, _, .impI _ _ d       => d.namesI
  | _, _, _, .impE d e         => d.namesI ++ e.namesI
  | _, _, _, .circI d          => d.namesI
  | _, _, _, .circE _ _ dp db  => dp.namesI ++ db.namesI
  | _, _, _, .allI a _ d       => a :: d.namesI
  | _, _, _, .allE _ d _       => d.namesI
  | _, _, _, .exI _ d          => d.namesI
  | _, _, _, .exE a _ _ _ _ dr db => a :: (dr.namesI ++ db.namesI)

/-! ## An eigenvariable is fresh for its own context

Immediate from the side conditions, and the reason nested eigenvariables are
distinct: the inner rule sees the outer one in `Γ`. -/

theorem namesP_fresh : ∀ {Γ : Ctx} {p : Pf} {A : Form} (d : Derives p Γ A),
    ∀ z ∈ d.namesP, z ∉ Ctx.fvP Γ := by
  intro Γ p A d
  induction d with
  | var _ | topI => intro _ h; cases h
  | botE _ ih | andE₁ _ ih | andE₂ _ ih | orI₁ _ ih | orI₂ _ ih | circI _ ih
  | allE _ _ _ ih | exI _ _ ih => exact ih
  | andI _ _ ih₁ ih₂ | impE _ _ ih₁ ih₂ =>
      intro z hz
      rcases List.mem_append.mp hz with h | h
      · exact ih₁ z h
      · exact ih₂ z h
  | allI _ _ _ ih => exact ih
  | @impI Γ p A B z hz _ ih =>
      intro z' hz'
      rcases List.mem_cons.mp hz' with h | h
      · exact h ▸ hz.1
      · intro hc; exact ih z' h (by simp [Ctx.fvP, Pf.fvP, hc])
  | @circE Γ q p b A B z hz _ _ ihp ihb =>
      intro z' hz'
      rcases List.mem_cons.mp hz' with h | h
      · exact h ▸ hz.1
      · rcases List.mem_append.mp h with h | h
        · exact ihp z' h
        · intro hc; exact ihb z' h (by simp [Ctx.fvP, Pf.fvP, hc])
  | @orE Γ r p q A B K y z hy hz _ _ _ ihr ih₁ ih₂ =>
      intro w hw
      rcases List.mem_cons.mp hw with h | h
      · exact h ▸ hy.1
      rcases List.mem_cons.mp h with h | h
      · exact h ▸ hz.1
      rcases List.mem_append.mp h with h | h
      · rcases List.mem_append.mp h with h | h
        · exact ihr w h
        · intro hc; exact ih₁ w h (by simp [Ctx.fvP, Pf.fvP, hc])
      · intro hc; exact ih₂ w h (by simp [Ctx.fvP, Pf.fvP, hc])
  | @exE Γ r p A K a z ha hK hz _ _ ihr ihb =>
      intro z' hz'
      rcases List.mem_cons.mp hz' with h | h
      · exact h ▸ hz.1
      · rcases List.mem_append.mp h with h | h
        · exact ihr z' h
        · intro hc; exact ihb z' h (by simp [Ctx.fvP, Pf.fvP, hc])

theorem namesI_fresh : ∀ {Γ : Ctx} {p : Pf} {A : Form} (d : Derives p Γ A),
    ∀ a ∈ d.namesI, a ∉ Ctx.fvI Γ := by
  intro Γ p A d
  induction d with
  | var _ | topI => intro _ h; cases h
  | botE _ ih | andE₁ _ ih | andE₂ _ ih | orI₁ _ ih | orI₂ _ ih | circI _ ih
  | allE _ _ _ ih | exI _ _ ih => exact ih
  | andI _ _ ih₁ ih₂ | impE _ _ ih₁ ih₂ =>
      intro a ha
      rcases List.mem_append.mp ha with h | h
      · exact ih₁ a h
      · exact ih₂ a h
  | @impI Γ p A B z _ _ ih =>
      intro a ha hc
      exact ih a ha (by simp [Ctx.fvI, Pf.fvI, hc])
  | @circE Γ q p b A B z _ _ _ ihp ihb =>
      intro a ha
      rcases List.mem_append.mp ha with h | h
      · exact ihp a h
      · intro hc; exact ihb a h (by simp [Ctx.fvI, Pf.fvI, hc])
  | @orE Γ r p q A B K y z _ _ _ _ _ ihr ih₁ ih₂ =>
      intro a ha
      rcases List.mem_append.mp ha with h | h
      · rcases List.mem_append.mp h with h | h
        · exact ihr a h
        · intro hc; exact ih₁ a h (by simp [Ctx.fvI, Pf.fvI, hc])
      · intro hc; exact ih₂ a h (by simp [Ctx.fvI, Pf.fvI, hc])
  | @allI Γ p A a ha _ ih =>
      intro a' ha'
      rcases List.mem_cons.mp ha' with h | h
      · exact h ▸ ha.1
      · exact ih a' h
  | @exE Γ r p A K a z ha hK hz _ _ ihr ihb =>
      intro a' ha'
      rcases List.mem_cons.mp ha' with h | h
      · exact h ▸ ha.1
      · rcases List.mem_append.mp h with h | h
        · exact ihr a' h
        · intro hc; exact ihb a' h (by simp [Ctx.fvI, Pf.fvI, hc])

/-! ## Pushing the hypotheses under a binder

Both of these are the same argument: the sub-derivation's eigenvariables avoid
the new entry because they already avoid the *old* one, which carried the same
formula and the same bound name. -/

theorem weakenP_under {Γ Δ : Ctx} {z : String} {C : Form} {p : Pf} {B : Form}
    (d : Derives p ((Pf.fvar z, C) :: Γ) B)
    (hp : ∀ z' ∈ z :: d.namesP, z' ∉ Ctx.fvP Δ) :
    ∀ z' ∈ d.namesP, z' ∉ Ctx.fvP ((Pf.fvar z, C) :: Δ) := by
  intro z' h hc
  simp only [Ctx.fvP, Pf.fvP, List.singleton_append, List.mem_cons] at hc
  rcases hc with hc | hc
  · exact namesP_fresh d z' h (by simp [Ctx.fvP, Pf.fvP, hc])
  · exact hp z' (List.mem_cons_of_mem _ h) hc

theorem weakenI_under {Γ Δ : Ctx} {z : String} {C : Form} {p : Pf} {B : Form}
    (d : Derives p ((Pf.fvar z, C) :: Γ) B)
    (hi : ∀ a ∈ d.namesI, a ∉ Ctx.fvI Δ) :
    ∀ a ∈ d.namesI, a ∉ Ctx.fvI ((Pf.fvar z, C) :: Δ) := by
  intro a h hc
  simp only [Ctx.fvI, Pf.fvI, List.nil_append, List.mem_append] at hc
  rcases hc with hc | hc
  · exact namesI_fresh d a h (by simp [Ctx.fvI, Pf.fvI, hc])
  · exact hi a h hc

theorem sub_cons {Γ Δ : Ctx} (e : Pf × Form) (hs : ∀ x ∈ Γ, x ∈ Δ) :
    ∀ x ∈ e :: Γ, x ∈ e :: Δ := by
  intro x hx
  rcases List.mem_cons.mp hx with h | h
  · exact h ▸ List.mem_cons_self ..
  · exact List.mem_cons_of_mem _ (hs x h)

/-! ## Weakening

To any superset, provided the derivation's eigenvariables avoid it.  The
hypothesis is not decoration: without it the statement is false. -/

private theorem memL {α : Type} {x : α} {l₁ l₂ : List α} (h : x ∈ l₁) : x ∈ l₁ ++ l₂ :=
  List.mem_append.mpr (Or.inl h)
private theorem memR {α : Type} {x : α} {l₁ l₂ : List α} (h : x ∈ l₂) : x ∈ l₁ ++ l₂ :=
  List.mem_append.mpr (Or.inr h)
private theorem memC {α : Type} {x y : α} {l : List α} (h : x ∈ l) : x ∈ y :: l :=
  List.mem_cons_of_mem _ h

def Derives.weaken : {Γ : Ctx} → {p : Pf} → {A : Form} → (d : Derives p Γ A) →
    (Δ : Ctx) → (∀ e ∈ Γ, e ∈ Δ) →
    (∀ z ∈ d.namesP, z ∉ Ctx.fvP Δ) →
    (∀ a ∈ d.namesI, a ∉ Ctx.fvI Δ) →
    Derives p Δ A
  | _, _, _, .var h,    _, hs, _,  _  => .var (hs _ h)
  | _, _, _, .topI,     _, _,  _,  _  => .topI
  | _, _, _, .botE d,   Δ, hs, hp, hi => .botE (d.weaken Δ hs hp hi)
  | _, _, _, .andE₁ d,  Δ, hs, hp, hi => .andE₁ (d.weaken Δ hs hp hi)
  | _, _, _, .andE₂ d,  Δ, hs, hp, hi => .andE₂ (d.weaken Δ hs hp hi)
  | _, _, _, .orI₁ d,   Δ, hs, hp, hi => .orI₁ (d.weaken Δ hs hp hi)
  | _, _, _, .orI₂ d,   Δ, hs, hp, hi => .orI₂ (d.weaken Δ hs hp hi)
  | _, _, _, .circI d,  Δ, hs, hp, hi => .circI (d.weaken Δ hs hp hi)
  | _, _, _, .exI t d,  Δ, hs, hp, hi => .exI t (d.weaken Δ hs hp hi)
  | _, _, _, .allE t d h, Δ, hs, hp, hi => .allE t (d.weaken Δ hs hp hi) h
  | _, _, _, .andI d e, Δ, hs, hp, hi =>
      .andI (d.weaken Δ hs (fun _ h => hp _ (memL h)) (fun _ h => hi _ (memL h)))
            (e.weaken Δ hs (fun _ h => hp _ (memR h)) (fun _ h => hi _ (memR h)))
  | _, _, _, .impE d e, Δ, hs, hp, hi =>
      .impE (d.weaken Δ hs (fun _ h => hp _ (memL h)) (fun _ h => hi _ (memL h)))
            (e.weaken Δ hs (fun _ h => hp _ (memR h)) (fun _ h => hi _ (memR h)))
  | _, _, _, .impI z hz d, _, hs, hp, hi =>
      .impI z ⟨hp z (List.mem_cons_self ..), hz.2⟩
        (d.weaken _ (sub_cons _ hs) (weakenP_under d hp) (weakenI_under d hi))
  | _, _, _, .allI a ha d, Δ, hs, hp, hi =>
      .allI a ⟨hi a (List.mem_cons_self ..), ha.2⟩
        (d.weaken Δ hs hp (fun _ h => hi _ (memC h)))
  | _, _, _, .circE z hz dp db, Δ, hs, hp, hi =>
      .circE z ⟨hp z (List.mem_cons_self ..), hz.2⟩
        (dp.weaken Δ hs (fun _ h => hp _ (memC (memL h)))
                        (fun _ h => hi _ (memL h)))
        (db.weaken _ (sub_cons _ hs)
          (weakenP_under db (fun w hw =>
            (List.mem_cons.mp hw).elim
              (fun h => h ▸ hp z (List.mem_cons_self ..))
              (fun h => hp w (memC (memR h)))))
          (weakenI_under db (fun _ h => hi _ (memR h))))
  | _, _, _, .orE y z hy hz dr d₁ d₂, Δ, hs, hp, hi =>
      .orE y z ⟨hp y (List.mem_cons_self ..), hy.2⟩
             ⟨hp z (memC (List.mem_cons_self ..)), hz.2⟩
        (dr.weaken Δ hs (fun _ h => hp _ (memC (memC (memL (memL h)))))
                        (fun _ h => hi _ (memL (memL h))))
        (d₁.weaken _ (sub_cons _ hs)
          (weakenP_under d₁ (fun w hw =>
            (List.mem_cons.mp hw).elim
              (fun h => h ▸ hp y (List.mem_cons_self ..))
              (fun h => hp w (memC (memC (memL (memR h)))))))
          (weakenI_under d₁ (fun _ h => hi _ (memL (memR h)))))
        (d₂.weaken _ (sub_cons _ hs)
          (weakenP_under d₂ (fun w hw =>
            (List.mem_cons.mp hw).elim
              (fun h => h ▸ hp z (memC (List.mem_cons_self ..)))
              (fun h => hp w (memC (memC (memR h))))))
          (weakenI_under d₂ (fun _ h => hi _ (memR h))))
  | _, _, _, .exE a z ha hK hz dr db, Δ, hs, hp, hi =>
      .exE a z ⟨hi a (List.mem_cons_self ..), ha.2⟩ hK
             ⟨hp z (List.mem_cons_self ..), hz.2⟩
        (dr.weaken Δ hs (fun _ h => hp _ (memC (memL h)))
                        (fun _ h => hi _ (memC (memL h))))
        (db.weaken _ (sub_cons _ hs)
          (weakenP_under db (fun w hw =>
            (List.mem_cons.mp hw).elim
              (fun h => h ▸ hp z (List.mem_cons_self ..))
              (fun h => hp w (memC (memR h)))))
          (weakenI_under db (fun _ h => hi _ (memC (memR h)))))

/-! ## Weakening is usable, and the hypothesis is checkable

`freshFor` over `d.namesP` supplies a name the derivation cannot be using, so
for a derivation in hand the proof-variable half is discharged by
construction.  The individual half is not: it asks that the derivation's
eigenvariables avoid the *formulas* in the enlarged context, and no choice of
new name can arrange that.  That is precisely the gap a renaming lemma would
close, and it is OPEN. -/

/-- A one-entry weakening, the shape every derived rule needs. -/
def Derives.weakenCons {Γ : Ctx} {p : Pf} {A : Form} (d : Derives p Γ A)
    (e : Pf × Form)
    (hp : ∀ z ∈ d.namesP, z ∉ e.1.fvP)
    (hi : ∀ a ∈ d.namesI, a ∉ e.1.fvI ++ e.2.fv) :
    Derives p (e :: Γ) A :=
  d.weaken (e :: Γ) (fun _ h => List.mem_cons_of_mem _ h)
    (fun z hz hc => by
      rcases List.mem_append.mp hc with h | h
      · exact hp z hz h
      · exact namesP_fresh d z hz h)
    (fun a ha hc => by
      simp only [Ctx.fvI, List.append_assoc, List.mem_append] at hc
      rcases hc with h | h | h
      · exact hi a ha (memL h)
      · exact hi a ha (memR h)
      · exact namesI_fresh d a ha h)

example (A B : Form) (z : String)
    (d : Derives (.fvar "u") [(Pf.fvar "u", A)] A)
    (h : Derives.namesP d = [] ∧ Derives.namesI d = []) :
    Derives (.fvar "u") [(Pf.fvar z, B), (Pf.fvar "u", A)] A :=
  d.weakenCons _ (by simp [h.1]) (by simp [h.2])

end LaxLogic.QLL
