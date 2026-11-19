import CK.Identity

/-!
# `CK.Height` — G4CK with a height bound

`G4CKh n Γ φ`: `Γ ⇒ φ` has a G4CK derivation of height at most `n`.  The
rules are those of `CK.G4CK` (Figure 2 of van der Giessen and Shillito,
arXiv:2602.16880v2), each with its premises at `n` and its conclusion at
`n + 1`.

The paper's contraction and cut proofs (§3; Rocq `contraction`,
`additive_cut`) go by induction on a weight and then on the height of a
derivation (Rocq `height` in `CKSequentProps.v`, commit `cd09fce`).  With
`Prop`-valued provability a derivation has no height to compute, so the bound
is an index, as in `LaxLogic/PLL/G4/G4H.lean`, whose proofs are the templates
for this file and the next ones.  `G4CKh.exists_iff` says the two judgments
agree.
-/

namespace CK

open scoped Form

/-- G4CK with a height bound; constructor for constructor `CK.G4CK`. -/
inductive G4CKh : Nat → List Form → Form → Prop
  | botL {n : Nat} {Γ : List Form} {φ : Form}
      (h : ⊥' ∈ Γ) : G4CKh n Γ φ
  | idP {n : Nat} {Γ : List Form} {p : Nat}
      (h : Form.var p ∈ Γ) : G4CKh n Γ (.var p)
  | andL {n : Nat} {Γ Δ : List Form} {φ ψ χ : Form}
      (h : Γ.Perm ((φ ⋏ ψ) :: Δ)) :
      G4CKh n (φ :: ψ :: Δ) χ → G4CKh (n + 1) Γ χ
  | andR {n : Nat} {Γ : List Form} {φ ψ : Form} :
      G4CKh n Γ φ → G4CKh n Γ ψ → G4CKh (n + 1) Γ (φ ⋏ ψ)
  | orL {n : Nat} {Γ Δ : List Form} {φ ψ χ : Form}
      (h : Γ.Perm ((φ ⋎ ψ) :: Δ)) :
      G4CKh n (φ :: Δ) χ → G4CKh n (ψ :: Δ) χ → G4CKh (n + 1) Γ χ
  | orR1 {n : Nat} {Γ : List Form} {φ ψ : Form} :
      G4CKh n Γ φ → G4CKh (n + 1) Γ (φ ⋎ ψ)
  | orR2 {n : Nat} {Γ : List Form} {φ ψ : Form} :
      G4CKh n Γ ψ → G4CKh (n + 1) Γ (φ ⋎ ψ)
  | impR {n : Nat} {Γ : List Form} {φ ψ : Form} :
      G4CKh n (φ :: Γ) ψ → G4CKh (n + 1) Γ (φ ⟶ ψ)
  | impAndL {n : Nat} {Γ Δ : List Form} {φ ψ χ δ : Form}
      (h : Γ.Perm (((φ ⋏ ψ) ⟶ χ) :: Δ)) :
      G4CKh n ((φ ⟶ (ψ ⟶ χ)) :: Δ) δ → G4CKh (n + 1) Γ δ
  | impOrL {n : Nat} {Γ Δ : List Form} {φ ψ χ δ : Form}
      (h : Γ.Perm (((φ ⋎ ψ) ⟶ χ) :: Δ)) :
      G4CKh n ((φ ⟶ χ) :: (ψ ⟶ χ) :: Δ) δ → G4CKh (n + 1) Γ δ
  | impVarL {n : Nat} {Γ Δ : List Form} {p : Nat} {φ χ : Form}
      (h : Γ.Perm ((Form.var p ⟶ φ) :: Δ)) (hp : Form.var p ∈ Δ) :
      G4CKh n (φ :: Δ) χ → G4CKh (n + 1) Γ χ
  | impImpL {n : Nat} {Γ Δ : List Form} {φ ψ χ δ : Form}
      (h : Γ.Perm (((φ ⟶ ψ) ⟶ χ) :: Δ)) :
      G4CKh n ((ψ ⟶ χ) :: Δ) (φ ⟶ ψ) → G4CKh n (χ :: Δ) δ → G4CKh (n + 1) Γ δ
  | boxR {n : Nat} {Γ : List Form} {φ : Form} :
      G4CKh n (unbox Γ) φ → G4CKh (n + 1) Γ (□φ)
  | impBoxL {n : Nat} {Γ Δ : List Form} {φ ψ δ : Form}
      (h : Γ.Perm (((□φ) ⟶ ψ) :: Δ)) :
      G4CKh n (unbox Δ) φ → G4CKh n (ψ :: Δ) δ → G4CKh (n + 1) Γ δ
  | impDiaL {n : Nat} {Γ Δ : List Form} {γ φ ψ δ : Form}
      (h : Γ.Perm (((◇φ) ⟶ ψ) :: Δ)) (hγ : (◇γ) ∈ Δ) :
      G4CKh n (γ :: unbox Δ) φ → G4CKh n (ψ :: Δ) δ → G4CKh (n + 1) Γ δ
  | diaL {n : Nat} {Γ Δ : List Form} {φ ψ : Form}
      (h : Γ.Perm ((◇φ) :: Δ)) :
      G4CKh n (φ :: unbox Δ) ψ → G4CKh (n + 1) Γ (◇ψ)

namespace G4CKh

/-- Bumping the bound by one. -/
theorem succ_mono {n : Nat} {Γ : List Form} {φ : Form} (d : G4CKh n Γ φ) :
    G4CKh (n + 1) Γ φ := by
  induction d with
  | botL h => exact .botL h
  | idP h => exact .idP h
  | andL h _ ih => exact .andL h ih
  | andR _ _ ih₁ ih₂ => exact .andR ih₁ ih₂
  | orL h _ _ ih₁ ih₂ => exact .orL h ih₁ ih₂
  | orR1 _ ih => exact .orR1 ih
  | orR2 _ ih => exact .orR2 ih
  | impR _ ih => exact .impR ih
  | impAndL h _ ih => exact .impAndL h ih
  | impOrL h _ ih => exact .impOrL h ih
  | impVarL h hp _ ih => exact .impVarL h hp ih
  | impImpL h _ _ ih₁ ih₂ => exact .impImpL h ih₁ ih₂
  | boxR _ ih => exact .boxR ih
  | impBoxL h _ _ ih₁ ih₂ => exact .impBoxL h ih₁ ih₂
  | impDiaL h hγ _ _ ih₁ ih₂ => exact .impDiaL h hγ ih₁ ih₂
  | diaL h _ ih => exact .diaL h ih

/-- The bound may be raised. -/
theorem mono {n m : Nat} {Γ : List Form} {φ : Form} (d : G4CKh n Γ φ) (hnm : n ≤ m) :
    G4CKh m Γ φ := by
  induction hnm with
  | refl => exact d
  | step _ ih => exact ih.succ_mono

/-- Exchange, height-preserving. -/
theorem perm {n : Nat} {Γ : List Form} {φ : Form} (d : G4CKh n Γ φ) :
    ∀ {Γ' : List Form}, Γ.Perm Γ' → G4CKh n Γ' φ := by
  induction d with
  | botL h => intro Γ' hp; exact .botL (hp.mem_iff.1 h)
  | idP h => intro Γ' hp; exact .idP (hp.mem_iff.1 h)
  | andL h d _ => intro Γ' hp; exact .andL (hp.symm.trans h) d
  | andR _ _ ih₁ ih₂ => intro Γ' hp; exact .andR (ih₁ hp) (ih₂ hp)
  | orL h d₁ d₂ _ _ => intro Γ' hp; exact .orL (hp.symm.trans h) d₁ d₂
  | orR1 _ ih => intro Γ' hp; exact .orR1 (ih hp)
  | orR2 _ ih => intro Γ' hp; exact .orR2 (ih hp)
  | impR _ ih => intro Γ' hp; exact .impR (ih (hp.cons _))
  | impAndL h d _ => intro Γ' hp; exact .impAndL (hp.symm.trans h) d
  | impOrL h d _ => intro Γ' hp; exact .impOrL (hp.symm.trans h) d
  | impVarL h hv d _ => intro Γ' hp; exact .impVarL (hp.symm.trans h) hv d
  | impImpL h d₁ d₂ _ _ => intro Γ' hp; exact .impImpL (hp.symm.trans h) d₁ d₂
  | boxR _ ih => intro Γ' hp; exact .boxR (ih (unbox_perm hp))
  | impBoxL h d₁ d₂ _ _ => intro Γ' hp; exact .impBoxL (hp.symm.trans h) d₁ d₂
  | impDiaL h hγ d₁ d₂ _ _ => intro Γ' hp; exact .impDiaL (hp.symm.trans h) hγ d₁ d₂
  | diaL h d _ => intro Γ' hp; exact .diaL (hp.symm.trans h) d

private theorem unbox_weaken {n : Nat} {Δ : List Form} {φ : Form} (ψ : Form)
    (ih : ∀ χ, G4CKh n (χ :: unbox Δ) φ) (d : G4CKh n (unbox Δ) φ) :
    G4CKh n (unbox (ψ :: Δ)) φ := by
  rcases unbox_cons ψ Δ with e | ⟨χ, e⟩
  · rw [e]; exact d
  · rw [e]; exact ih χ

private theorem unbox_weaken_cons {n : Nat} {Δ : List Form} {γ φ : Form} (ψ : Form)
    (ih : ∀ χ, G4CKh n (χ :: γ :: unbox Δ) φ) (d : G4CKh n (γ :: unbox Δ) φ) :
    G4CKh n (γ :: unbox (ψ :: Δ)) φ := by
  rcases unbox_cons ψ Δ with e | ⟨χ, e⟩
  · rw [e]; exact d
  · rw [e]; exact (ih χ).perm (List.Perm.swap _ _ _)

/-- Weakening, height-preserving. -/
theorem weaken {n : Nat} {Γ : List Form} {φ : Form} (d : G4CKh n Γ φ) :
    ∀ ψ : Form, G4CKh n (ψ :: Γ) φ := by
  induction d with
  | botL h => intro ψ; exact .botL (List.mem_cons_of_mem _ h)
  | idP h => intro ψ; exact .idP (List.mem_cons_of_mem _ h)
  | andL h _ ih =>
      intro ψ
      exact .andL ((h.cons ψ).trans (List.Perm.swap _ _ _))
        ((ih ψ).perm (((List.Perm.swap _ _ _).trans
          ((List.Perm.swap _ _ _).cons _))))
  | andR _ _ ih₁ ih₂ => intro ψ; exact .andR (ih₁ ψ) (ih₂ ψ)
  | orL h _ _ ih₁ ih₂ =>
      intro ψ
      exact .orL ((h.cons ψ).trans (List.Perm.swap _ _ _))
        ((ih₁ ψ).perm (List.Perm.swap _ _ _)) ((ih₂ ψ).perm (List.Perm.swap _ _ _))
  | orR1 _ ih => intro ψ; exact .orR1 (ih ψ)
  | orR2 _ ih => intro ψ; exact .orR2 (ih ψ)
  | impR _ ih => intro ψ; exact .impR ((ih ψ).perm (List.Perm.swap _ _ _))
  | impAndL h _ ih =>
      intro ψ
      exact .impAndL ((h.cons ψ).trans (List.Perm.swap _ _ _))
        ((ih ψ).perm (List.Perm.swap _ _ _))
  | impOrL h _ ih =>
      intro ψ
      exact .impOrL ((h.cons ψ).trans (List.Perm.swap _ _ _))
        ((ih ψ).perm (((List.Perm.swap _ _ _).trans
          ((List.Perm.swap _ _ _).cons _))))
  | impVarL h hv _ ih =>
      intro ψ
      exact .impVarL ((h.cons ψ).trans (List.Perm.swap _ _ _)) (List.mem_cons_of_mem _ hv)
        ((ih ψ).perm (List.Perm.swap _ _ _))
  | impImpL h _ _ ih₁ ih₂ =>
      intro ψ
      exact .impImpL ((h.cons ψ).trans (List.Perm.swap _ _ _))
        ((ih₁ ψ).perm (List.Perm.swap _ _ _)) ((ih₂ ψ).perm (List.Perm.swap _ _ _))
  | boxR d ih => intro ψ; exact .boxR (unbox_weaken ψ ih d)
  | impBoxL h d₁ _ ih₁ ih₂ =>
      intro ψ
      exact .impBoxL ((h.cons ψ).trans (List.Perm.swap _ _ _))
        (unbox_weaken ψ ih₁ d₁) ((ih₂ ψ).perm (List.Perm.swap _ _ _))
  | impDiaL h hγ d₁ _ ih₁ ih₂ =>
      intro ψ
      exact .impDiaL ((h.cons ψ).trans (List.Perm.swap _ _ _)) (List.mem_cons_of_mem _ hγ)
        (unbox_weaken_cons ψ ih₁ d₁) ((ih₂ ψ).perm (List.Perm.swap _ _ _))
  | diaL h d ih =>
      intro ψ
      exact .diaL ((h.cons ψ).trans (List.Perm.swap _ _ _)) (unbox_weaken_cons ψ ih d)

/-- Weakening by a list, height-preserving. -/
theorem weakens {n : Nat} {Γ : List Form} {φ : Form} (d : G4CKh n Γ φ) :
    ∀ L : List Form, G4CKh n (L ++ Γ) φ
  | [] => d
  | ψ :: L => (weakens d L).weaken ψ

/-- A bounded derivation is a derivation. -/
theorem toG4CK {n : Nat} {Γ : List Form} {φ : Form} (d : G4CKh n Γ φ) : G4CK Γ φ := by
  induction d with
  | botL h => exact .botL h
  | idP h => exact .idP h
  | andL h _ ih => exact .andL h ih
  | andR _ _ ih₁ ih₂ => exact .andR ih₁ ih₂
  | orL h _ _ ih₁ ih₂ => exact .orL h ih₁ ih₂
  | orR1 _ ih => exact .orR1 ih
  | orR2 _ ih => exact .orR2 ih
  | impR _ ih => exact .impR ih
  | impAndL h _ ih => exact .impAndL h ih
  | impOrL h _ ih => exact .impOrL h ih
  | impVarL h hp _ ih => exact .impVarL h hp ih
  | impImpL h _ _ ih₁ ih₂ => exact .impImpL h ih₁ ih₂
  | boxR _ ih => exact .boxR ih
  | impBoxL h _ _ ih₁ ih₂ => exact .impBoxL h ih₁ ih₂
  | impDiaL h hγ _ _ ih₁ ih₂ => exact .impDiaL h hγ ih₁ ih₂
  | diaL h _ ih => exact .diaL h ih

/-- Two bounded derivations at a common bound. -/
private theorem toSame {Γ₁ Γ₂ : List Form} {φ₁ φ₂ : Form}
    (h₁ : ∃ n, G4CKh n Γ₁ φ₁) (h₂ : ∃ n, G4CKh n Γ₂ φ₂) :
    ∃ n, G4CKh n Γ₁ φ₁ ∧ G4CKh n Γ₂ φ₂ :=
  let ⟨n₁, d₁⟩ := h₁
  let ⟨n₂, d₂⟩ := h₂
  ⟨max n₁ n₂, d₁.mono (Nat.le_max_left _ _), d₂.mono (Nat.le_max_right _ _)⟩

/-- A derivation has a height. -/
theorem ofG4CK {Γ : List Form} {φ : Form} (d : G4CK Γ φ) : ∃ n, G4CKh n Γ φ := by
  induction d with
  | botL h => exact ⟨0, .botL h⟩
  | idP h => exact ⟨0, .idP h⟩
  | andL h _ ih => exact let ⟨n, d⟩ := ih; ⟨n + 1, .andL h d⟩
  | andR _ _ ih₁ ih₂ => exact let ⟨n, d₁, d₂⟩ := toSame ih₁ ih₂; ⟨n + 1, .andR d₁ d₂⟩
  | orL h _ _ ih₁ ih₂ => exact let ⟨n, d₁, d₂⟩ := toSame ih₁ ih₂; ⟨n + 1, .orL h d₁ d₂⟩
  | orR1 _ ih => exact let ⟨n, d⟩ := ih; ⟨n + 1, .orR1 d⟩
  | orR2 _ ih => exact let ⟨n, d⟩ := ih; ⟨n + 1, .orR2 d⟩
  | impR _ ih => exact let ⟨n, d⟩ := ih; ⟨n + 1, .impR d⟩
  | impAndL h _ ih => exact let ⟨n, d⟩ := ih; ⟨n + 1, .impAndL h d⟩
  | impOrL h _ ih => exact let ⟨n, d⟩ := ih; ⟨n + 1, .impOrL h d⟩
  | impVarL h hp _ ih => exact let ⟨n, d⟩ := ih; ⟨n + 1, .impVarL h hp d⟩
  | impImpL h _ _ ih₁ ih₂ =>
      exact let ⟨n, d₁, d₂⟩ := toSame ih₁ ih₂; ⟨n + 1, .impImpL h d₁ d₂⟩
  | boxR _ ih => exact let ⟨n, d⟩ := ih; ⟨n + 1, .boxR d⟩
  | impBoxL h _ _ ih₁ ih₂ =>
      exact let ⟨n, d₁, d₂⟩ := toSame ih₁ ih₂; ⟨n + 1, .impBoxL h d₁ d₂⟩
  | impDiaL h hγ _ _ ih₁ ih₂ =>
      exact let ⟨n, d₁, d₂⟩ := toSame ih₁ ih₂; ⟨n + 1, .impDiaL h hγ d₁ d₂⟩
  | diaL h _ ih => exact let ⟨n, d⟩ := ih; ⟨n + 1, .diaL h d⟩

/-- `G4CK Γ φ` iff `Γ ⇒ φ` is derivable at some height. -/
theorem exists_iff {Γ : List Form} {φ : Form} : (∃ n, G4CKh n Γ φ) ↔ G4CK Γ φ :=
  ⟨fun ⟨_, d⟩ => d.toG4CK, ofG4CK⟩

end G4CKh

end CK

#print axioms CK.G4CKh.weakens
#print axioms CK.G4CKh.exists_iff
