/-
# `LaxLogic.QLL.Rename` — renaming an individual, and re-basing a derivation

The obstruction `Weaken.lean` names is an *individual* one: `weakenCons` asks
that the derivation's individual eigenvariables avoid the formulas in the new
entry, and no choice of new name can arrange that.  Only changing the
derivation can, which means renaming.

Renaming here is name-for-name, not substitution: `renameI a b` replaces the
free individual `a` by `b` throughout.  That is all the eigenvariable case
needs, and it avoids every capture condition a general substitution would
carry — `b` is a name, so it has nothing to capture with.

Proof variables are untouched: `Pf.renameI` passes through `fvar` and rewrites
only the terms and formulas embedded in `inst`, `pack` and `exf`.
-/
import LaxLogic.QLL.Weaken

namespace LaxLogic.QLL

/-! ## The operation -/

mutual
/-- Replace the free individual `a` by `b`. -/
def Tm.renameI (a b : String) : Tm → Tm
  | .bvar i  => .bvar i
  | .fvar x  => .fvar (if x = a then b else x)
  | .fn f ts => .fn f (Tm.renameIList a b ts)
/-- `renameI` on a list of arguments. -/
def Tm.renameIList (a b : String) : List Tm → List Tm
  | []      => []
  | t :: ts => Tm.renameI a b t :: Tm.renameIList a b ts
end

/-- `renameI` on a formula.  Bound individuals are indices, so no binder case
needs to do anything. -/
def Form.renameI (a b : String) : Form → Form
  | .top       => .top
  | .bot       => .bot
  | .pred P ts => .pred P (Tm.renameIList a b ts)
  | .and A B   => .and (Form.renameI a b A) (Form.renameI a b B)
  | .or A B    => .or (Form.renameI a b A) (Form.renameI a b B)
  | .imp A B   => .imp (Form.renameI a b A) (Form.renameI a b B)
  | .circ q A  => .circ q (Form.renameI a b A)
  | .forall_ A => .forall_ (Form.renameI a b A)
  | .exists_ A => .exists_ (Form.renameI a b A)

/-- `renameI` on a proof term.  Proof variables pass through untouched. -/
def Pf.renameI (a b : String) : Pf → Pf
  | .bvar i       => .bvar i
  | .fvar x       => .fvar x
  | .star         => .star
  | .pair p q     => .pair (Pf.renameI a b p) (Pf.renameI a b q)
  | .fst p        => .fst (Pf.renameI a b p)
  | .snd p        => .snd (Pf.renameI a b p)
  | .inl p        => .inl (Pf.renameI a b p)
  | .inr p        => .inr (Pf.renameI a b p)
  | .caseOr r p q => .caseOr (Pf.renameI a b r) (Pf.renameI a b p) (Pf.renameI a b q)
  | .lam p        => .lam (Pf.renameI a b p)
  | .app p q      => .app (Pf.renameI a b p) (Pf.renameI a b q)
  | .val q p      => .val q (Pf.renameI a b p)
  | .letQ q p c   => .letQ q (Pf.renameI a b p) (Pf.renameI a b c)
  | .gen p        => .gen (Pf.renameI a b p)
  | .inst t p     => .inst (Tm.renameI a b t) (Pf.renameI a b p)
  | .pack t p     => .pack (Tm.renameI a b t) (Pf.renameI a b p)
  | .caseEx r p   => .caseEx (Pf.renameI a b r) (Pf.renameI a b p)
  | .exf A p      => .exf (Form.renameI a b A) (Pf.renameI a b p)

/-- `renameI` on a context, in both components of every entry. -/
def Ctx.renameI (a b : String) : Ctx → Ctx
  | []          => []
  | (p, A) :: Γ => (Pf.renameI a b p, Form.renameI a b A) :: Ctx.renameI a b Γ

/-! ## Renaming commutes with opening

`openAt` inserts a term, `openI` an individual, `openP` a proof variable;
renaming an individual passes through all three.  The `if` in the second pair
is the eigenvariable case: opening with `a` becomes opening with `b`. -/

mutual
theorem Tm.renameI_openAt (a b : String) (k : Nat) (u : Tm) :
    ∀ t : Tm, Tm.renameI a b (Tm.openAt k u t)
      = Tm.openAt k (Tm.renameI a b u) (Tm.renameI a b t)
  | .bvar i  => by by_cases h : i = k <;> simp [Tm.openAt, Tm.renameI, h]
  | .fvar _  => rfl
  | .fn _ ts => by simp [Tm.openAt, Tm.renameI, Tm.renameIList_openAtList a b k u ts]
theorem Tm.renameIList_openAtList (a b : String) (k : Nat) (u : Tm) :
    ∀ ts : List Tm, Tm.renameIList a b (Tm.openAtList k u ts)
      = Tm.openAtList k (Tm.renameI a b u) (Tm.renameIList a b ts)
  | []      => rfl
  | t :: ts => by
      simp [Tm.openAtList, Tm.renameIList, Tm.renameI_openAt a b k u t,
            Tm.renameIList_openAtList a b k u ts]
end

theorem Form.renameI_openAt (a b : String) (u : Tm) :
    ∀ (A : Form) (k : Nat), Form.renameI a b (Form.openAt k u A)
      = Form.openAt k (Tm.renameI a b u) (Form.renameI a b A) := by
  intro A
  induction A with
  | top | bot => intro _; rfl
  | pred _ ts => intro k; simp [Form.openAt, Form.renameI, Tm.renameIList_openAtList a b k u ts]
  | and _ _ ih₁ ih₂ | or _ _ ih₁ ih₂ | imp _ _ ih₁ ih₂ =>
      intro k; simp [Form.openAt, Form.renameI, ih₁ k, ih₂ k]
  | circ _ _ ih => intro k; simp [Form.openAt, Form.renameI, ih k]
  | forall_ _ ih | exists_ _ ih =>
      intro k; simp [Form.openAt, Form.renameI, ih (k + 1)]

theorem Form.renameI_openWith (a b c : String) (A : Form) :
    Form.renameI a b (A.openWith c)
      = (Form.renameI a b A).openWith (if c = a then b else c) := by
  simp [Form.openWith, Form.renameI_openAt a b (.fvar c) A 0, Tm.renameI]

theorem Pf.renameI_openI (a b : String) (u : Tm) :
    ∀ (p : Pf) (k : Nat), Pf.renameI a b (Pf.openI k u p)
      = Pf.openI k (Tm.renameI a b u) (Pf.renameI a b p) := by
  intro p
  induction p with
  | bvar _ | fvar _ | star => intro _; rfl
  | pair _ _ ih₁ ih₂ | app _ _ ih₁ ih₂ | letQ _ _ _ ih₁ ih₂ =>
      intro k; simp [Pf.openI, Pf.renameI, ih₁ k, ih₂ k]
  | fst _ ih | snd _ ih | inl _ ih | inr _ ih | lam _ ih | val _ _ ih =>
      intro k; simp [Pf.openI, Pf.renameI, ih k]
  | caseOr _ _ _ ih₁ ih₂ ih₃ => intro k; simp [Pf.openI, Pf.renameI, ih₁ k, ih₂ k, ih₃ k]
  | gen _ ih => intro k; simp [Pf.openI, Pf.renameI, ih (k + 1)]
  | inst t _ ih | pack t _ ih =>
      intro k; simp [Pf.openI, Pf.renameI, ih k, Tm.renameI_openAt a b k u t]
  | caseEx _ _ ih₁ ih₂ => intro k; simp [Pf.openI, Pf.renameI, ih₁ k, ih₂ (k + 1)]
  | exf A _ ih => intro k; simp [Pf.openI, Pf.renameI, ih k, Form.renameI_openAt a b u A k]

theorem Pf.renameI_openIWith (a b c : String) (p : Pf) :
    Pf.renameI a b (p.openIWith c)
      = (Pf.renameI a b p).openIWith (if c = a then b else c) := by
  simp [Pf.openIWith, Pf.renameI_openI a b (.fvar c) p 0, Tm.renameI]

theorem Pf.renameI_openP (a b : String) (z : String) :
    ∀ (p : Pf) (k : Nat), Pf.renameI a b (Pf.openP k (.fvar z) p)
      = Pf.openP k (.fvar z) (Pf.renameI a b p) := by
  intro p
  induction p with
  | bvar i => intro k; by_cases h : i = k <;> simp [Pf.openP, Pf.renameI, h]
  | fvar _ | star => intro _; rfl
  | pair _ _ ih₁ ih₂ | app _ _ ih₁ ih₂ =>
      intro k; simp [Pf.openP, Pf.renameI, ih₁ k, ih₂ k]
  | letQ _ _ _ ih₁ ih₂ => intro k; simp [Pf.openP, Pf.renameI, ih₁ k, ih₂ (k + 1)]
  | fst _ ih | snd _ ih | inl _ ih | inr _ ih | val _ _ ih | gen _ ih
  | inst _ _ ih | pack _ _ ih | exf _ _ ih =>
      intro k; simp [Pf.openP, Pf.renameI, ih k]
  | lam _ ih => intro k; simp [Pf.openP, Pf.renameI, ih (k + 1)]
  | caseOr _ _ _ ih₁ ih₂ ih₃ =>
      intro k; simp [Pf.openP, Pf.renameI, ih₁ k, ih₂ (k + 1), ih₃ (k + 1)]
  | caseEx _ _ ih₁ ih₂ => intro k; simp [Pf.openP, Pf.renameI, ih₁ k, ih₂ (k + 1)]

theorem Pf.renameI_openPWith (a b z : String) (p : Pf) :
    Pf.renameI a b (p.openPWith z) = (Pf.renameI a b p).openPWith z :=
  Pf.renameI_openP a b z p 0

/-! ## Free individuals under renaming

The sharp form.  Reading it: a free individual of the renamed object is either
`b`, and then `a` occurred, or was already there. -/

mutual
theorem Tm.fv_renameI (a b x : String) :
    ∀ t : Tm, x ∈ Tm.fv (Tm.renameI a b t) → (x = b ∧ a ∈ Tm.fv t) ∨ x ∈ Tm.fv t
  | .bvar _  => by simp [Tm.renameI, Tm.fv]
  | .fvar y  => by
      by_cases h : y = a <;> simp [Tm.renameI, Tm.fv, h] <;> intro hx <;> simp [hx]
  | .fn _ ts => by simpa [Tm.renameI, Tm.fv] using Tm.fvList_renameIList a b x ts
theorem Tm.fvList_renameIList (a b x : String) :
    ∀ ts : List Tm, x ∈ Tm.fvList (Tm.renameIList a b ts) →
      (x = b ∧ a ∈ Tm.fvList ts) ∨ x ∈ Tm.fvList ts
  | []      => by simp [Tm.renameIList, Tm.fvList]
  | t :: ts => by
      simp only [Tm.renameIList, Tm.fvList, List.mem_append]
      rintro (h | h)
      · rcases Tm.fv_renameI a b x t h with ⟨h1, h2⟩ | h
        · exact Or.inl ⟨h1, Or.inl h2⟩
        · exact Or.inr (Or.inl h)
      · rcases Tm.fvList_renameIList a b x ts h with ⟨h1, h2⟩ | h
        · exact Or.inl ⟨h1, Or.inr h2⟩
        · exact Or.inr (Or.inr h)
end

theorem Form.fv_renameI (a b x : String) :
    ∀ A : Form, x ∈ Form.fv (Form.renameI a b A) → (x = b ∧ a ∈ Form.fv A) ∨ x ∈ Form.fv A := by
  intro A
  induction A with
  | top | bot => simp [Form.renameI, Form.fv]
  | pred _ ts => simpa [Form.renameI, Form.fv] using Tm.fvList_renameIList a b x ts
  | and _ _ ih₁ ih₂ | or _ _ ih₁ ih₂ | imp _ _ ih₁ ih₂ =>
      simp only [Form.renameI, Form.fv, List.mem_append]
      rintro (h | h)
      · rcases ih₁ h with ⟨h1, h2⟩ | h
        · exact Or.inl ⟨h1, Or.inl h2⟩
        · exact Or.inr (Or.inl h)
      · rcases ih₂ h with ⟨h1, h2⟩ | h
        · exact Or.inl ⟨h1, Or.inr h2⟩
        · exact Or.inr (Or.inr h)
  | circ _ _ ih | forall_ _ ih | exists_ _ ih => exact ih

theorem Pf.fvI_renameI (a b x : String) :
    ∀ p : Pf, x ∈ Pf.fvI (Pf.renameI a b p) → (x = b ∧ a ∈ p.fvI) ∨ x ∈ p.fvI := by
  intro p
  induction p with
  | bvar _ | fvar _ | star => simp [Pf.renameI, Pf.fvI]
  | fst _ ih | snd _ ih | inl _ ih | inr _ ih | lam _ ih | val _ _ ih | gen _ ih => exact ih
  | pair _ _ ih₁ ih₂ | app _ _ ih₁ ih₂ | letQ _ _ _ ih₁ ih₂ | caseEx _ _ ih₁ ih₂ =>
      simp only [Pf.renameI, Pf.fvI, List.mem_append]
      rintro (h | h)
      · rcases ih₁ h with ⟨h1, h2⟩ | h
        · exact Or.inl ⟨h1, Or.inl h2⟩
        · exact Or.inr (Or.inl h)
      · rcases ih₂ h with ⟨h1, h2⟩ | h
        · exact Or.inl ⟨h1, Or.inr h2⟩
        · exact Or.inr (Or.inr h)
  | caseOr _ _ _ ih₁ ih₂ ih₃ =>
      simp only [Pf.renameI, Pf.fvI, List.mem_append]
      rintro ((h | h) | h)
      · rcases ih₁ h with ⟨h1, h2⟩ | h
        · exact Or.inl ⟨h1, Or.inl (Or.inl h2)⟩
        · exact Or.inr (Or.inl (Or.inl h))
      · rcases ih₂ h with ⟨h1, h2⟩ | h
        · exact Or.inl ⟨h1, Or.inl (Or.inr h2)⟩
        · exact Or.inr (Or.inl (Or.inr h))
      · rcases ih₃ h with ⟨h1, h2⟩ | h
        · exact Or.inl ⟨h1, Or.inr h2⟩
        · exact Or.inr (Or.inr h)
  | inst t _ ih | pack t _ ih =>
      simp only [Pf.renameI, Pf.fvI, List.mem_append]
      rintro (h | h)
      · rcases Tm.fv_renameI a b x t h with ⟨h1, h2⟩ | h
        · exact Or.inl ⟨h1, Or.inl h2⟩
        · exact Or.inr (Or.inl h)
      · rcases ih h with ⟨h1, h2⟩ | h
        · exact Or.inl ⟨h1, Or.inr h2⟩
        · exact Or.inr (Or.inr h)
  | exf A _ ih =>
      simp only [Pf.renameI, Pf.fvI, List.mem_append]
      rintro (h | h)
      · rcases Form.fv_renameI a b x A h with ⟨h1, h2⟩ | h
        · exact Or.inl ⟨h1, Or.inl h2⟩
        · exact Or.inr (Or.inl h)
      · rcases ih h with ⟨h1, h2⟩ | h
        · exact Or.inl ⟨h1, Or.inr h2⟩
        · exact Or.inr (Or.inr h)

theorem Ctx.fvI_renameI (a b x : String) :
    ∀ Γ : Ctx, x ∈ Ctx.fvI (Ctx.renameI a b Γ) →
      (x = b ∧ a ∈ Ctx.fvI Γ) ∨ x ∈ Ctx.fvI Γ := by
  intro Γ
  induction Γ with
  | nil => simp [Ctx.renameI, Ctx.fvI]
  | cons e Γ ih =>
      obtain ⟨q, C⟩ := e
      simp only [Ctx.renameI, Ctx.fvI, List.mem_append]
      rintro ((h | h) | h)
      · rcases Pf.fvI_renameI a b x q h with ⟨h1, h2⟩ | h
        · exact Or.inl ⟨h1, Or.inl (Or.inl h2)⟩
        · exact Or.inr (Or.inl (Or.inl h))
      · rcases Form.fv_renameI a b x C h with ⟨h1, h2⟩ | h
        · exact Or.inl ⟨h1, Or.inl (Or.inr h2)⟩
        · exact Or.inr (Or.inl (Or.inr h))
      · rcases ih h with ⟨h1, h2⟩ | h
        · exact Or.inl ⟨h1, Or.inr h2⟩
        · exact Or.inr (Or.inr h)

/-! ## Proof variables are untouched, and opening adds only what it inserts -/

theorem Pf.fvP_renameI (a b : String) : ∀ p : Pf, (Pf.renameI a b p).fvP = p.fvP := by
  intro p; induction p with
  | bvar _ | fvar _ | star => rfl
  | fst _ ih | snd _ ih | inl _ ih | inr _ ih | lam _ ih | val _ _ ih | gen _ ih
  | inst _ _ ih | pack _ _ ih | exf _ _ ih => simp [Pf.renameI, Pf.fvP, ih]
  | pair _ _ ih₁ ih₂ | app _ _ ih₁ ih₂ | letQ _ _ _ ih₁ ih₂ | caseEx _ _ ih₁ ih₂ =>
      simp [Pf.renameI, Pf.fvP, ih₁, ih₂]
  | caseOr _ _ _ ih₁ ih₂ ih₃ => simp [Pf.renameI, Pf.fvP, ih₁, ih₂, ih₃]

theorem Ctx.fvP_renameI (a b : String) : ∀ Γ : Ctx, Ctx.fvP (Ctx.renameI a b Γ) = Ctx.fvP Γ := by
  intro Γ; induction Γ with
  | nil => rfl
  | cons e Γ ih => obtain ⟨q, C⟩ := e; simp [Ctx.renameI, Ctx.fvP, Pf.fvP_renameI, ih]

theorem Pf.fvI_openP (z : String) :
    ∀ (p : Pf) (k : Nat), Pf.fvI (Pf.openP k (.fvar z) p) = p.fvI := by
  intro p; induction p with
  | bvar i => intro k; by_cases h : i = k <;> simp [Pf.openP, Pf.fvI, h]
  | fvar _ | star => intro _; rfl
  | fst _ ih | snd _ ih | inl _ ih | inr _ ih | val _ _ ih | gen _ ih
  | inst _ _ ih | pack _ _ ih | exf _ _ ih => intro k; simp [Pf.openP, Pf.fvI, ih k]
  | lam _ ih => intro k; simp [Pf.openP, Pf.fvI, ih (k + 1)]
  | pair _ _ ih₁ ih₂ | app _ _ ih₁ ih₂ => intro k; simp [Pf.openP, Pf.fvI, ih₁ k, ih₂ k]
  | letQ _ _ _ ih₁ ih₂ | caseEx _ _ ih₁ ih₂ =>
      intro k; simp [Pf.openP, Pf.fvI, ih₁ k, ih₂ (k + 1)]
  | caseOr _ _ _ ih₁ ih₂ ih₃ =>
      intro k; simp [Pf.openP, Pf.fvI, ih₁ k, ih₂ (k + 1), ih₃ (k + 1)]

mutual
theorem Tm.fv_openAt (x : String) (u : Tm) :
    ∀ (t : Tm) (k : Nat), x ∈ Tm.fv (Tm.openAt k u t) → x ∈ Tm.fv u ∨ x ∈ Tm.fv t
  | .bvar i,  k => by by_cases h : i = k <;> simp [Tm.openAt, Tm.fv, h]
  | .fvar _,  _ => by intro h; exact Or.inr h
  | .fn _ ts, k => by simpa [Tm.openAt, Tm.fv] using Tm.fvList_openAtList x u ts k
theorem Tm.fvList_openAtList (x : String) (u : Tm) :
    ∀ (ts : List Tm) (k : Nat),
      x ∈ Tm.fvList (Tm.openAtList k u ts) → x ∈ Tm.fv u ∨ x ∈ Tm.fvList ts
  | [],      _ => by simp [Tm.openAtList, Tm.fvList]
  | t :: ts, k => by
      simp only [Tm.openAtList, Tm.fvList, List.mem_append]
      rintro (h | h)
      · exact (Tm.fv_openAt x u t k h).imp id Or.inl
      · exact (Tm.fvList_openAtList x u ts k h).imp id Or.inr
end

theorem Form.fv_openAt (x : String) (u : Tm) :
    ∀ (A : Form) (k : Nat), x ∈ Form.fv (Form.openAt k u A) → x ∈ Tm.fv u ∨ x ∈ Form.fv A := by
  intro A; induction A with
  | top | bot => intro _; simp [Form.openAt, Form.fv]
  | pred _ ts => intro k; simpa [Form.openAt, Form.fv] using Tm.fvList_openAtList x u ts k
  | and _ _ ih₁ ih₂ | or _ _ ih₁ ih₂ | imp _ _ ih₁ ih₂ =>
      intro k
      simp only [Form.openAt, Form.fv, List.mem_append]
      rintro (h | h)
      · exact (ih₁ k h).imp id Or.inl
      · exact (ih₂ k h).imp id Or.inr
  | circ _ _ ih => intro k; exact ih k
  | forall_ _ ih | exists_ _ ih => intro k; exact ih (k + 1)

theorem Pf.fvI_openI (x : String) (u : Tm) :
    ∀ (p : Pf) (k : Nat), x ∈ Pf.fvI (Pf.openI k u p) → x ∈ Tm.fv u ∨ x ∈ p.fvI := by
  intro p; induction p with
  | bvar _ | fvar _ | star => intro _; simp [Pf.openI, Pf.fvI]
  | fst _ ih | snd _ ih | inl _ ih | inr _ ih | lam _ ih | val _ _ ih => intro k; exact ih k
  | gen _ ih => intro k; exact ih (k + 1)
  | pair _ _ ih₁ ih₂ | app _ _ ih₁ ih₂ | letQ _ _ _ ih₁ ih₂ =>
      intro k
      simp only [Pf.openI, Pf.fvI, List.mem_append]
      rintro (h | h)
      · exact (ih₁ k h).imp id Or.inl
      · exact (ih₂ k h).imp id Or.inr
  | caseEx _ _ ih₁ ih₂ =>
      intro k
      simp only [Pf.openI, Pf.fvI, List.mem_append]
      rintro (h | h)
      · exact (ih₁ k h).imp id Or.inl
      · exact (ih₂ (k + 1) h).imp id Or.inr
  | caseOr _ _ _ ih₁ ih₂ ih₃ =>
      intro k
      simp only [Pf.openI, Pf.fvI, List.mem_append]
      rintro ((h | h) | h)
      · exact (ih₁ k h).imp id (fun h => Or.inl (Or.inl h))
      · exact (ih₂ k h).imp id (fun h => Or.inl (Or.inr h))
      · exact (ih₃ k h).imp id Or.inr
  | inst t _ ih | pack t _ ih =>
      intro k
      simp only [Pf.openI, Pf.fvI, List.mem_append]
      rintro (h | h)
      · exact (Tm.fv_openAt x u t k h).imp id Or.inl
      · exact (ih k h).imp id Or.inr
  | exf A _ ih =>
      intro k
      simp only [Pf.openI, Pf.fvI, List.mem_append]
      rintro (h | h)
      · exact (Form.fv_openAt x u A k h).imp id Or.inl
      · exact (ih k h).imp id Or.inr

theorem Ctx.mem_renameI (a b : String) {q : Pf} {C : Form} :
    ∀ {Γ : Ctx}, (q, C) ∈ Γ →
      (Pf.renameI a b q, Form.renameI a b C) ∈ Ctx.renameI a b Γ := by
  intro Γ h
  induction Γ with
  | nil => cases h
  | cons e Γ ih =>
      obtain ⟨r, D⟩ := e
      rcases List.mem_cons.mp h with h | h
      · rw [Prod.mk.injEq] at h
        rw [h.1, h.2]
        exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih h)

/-! ## The formulas a derivation passes through

`b ∉ A.fv` for the conclusion alone does not survive an elimination — `∧E₁`
forgets the second conjunct, which is then unconstrained.  So the hypothesis is
about every formula the derivation concludes with, at any node. -/

/-- Every formula the derivation concludes with, at any node. -/
def Derives.concls {Γ : Ctx} {p : Pf} {A : Form} (d : Derives p Γ A) : List String :=
  A.fv ++
    match d with
    | .var _            => []
    | .topI             => []
    | .botE d           => d.concls
    | .andI d e         => d.concls ++ e.concls
    | .andE₁ d          => d.concls
    | .andE₂ d          => d.concls
    | .orI₁ d           => d.concls
    | .orI₂ d           => d.concls
    | .orE _ _ _ _ dr d₁ d₂ => dr.concls ++ d₁.concls ++ d₂.concls
    | .impI _ _ d       => d.concls
    | .impE d e         => d.concls ++ e.concls
    | .circI d          => d.concls
    | .circE _ _ dp db  => dp.concls ++ db.concls
    | .allI _ _ d       => d.concls
    | .allE _ d _       => d.concls
    | .exI _ d          => d.concls
    | .exE _ _ _ _ _ dr db => dr.concls ++ db.concls

/-! ## Transferring a non-occurrence across a renaming -/

theorem Ctx.notMem_fvI_renameI {a b x : String} {Γ : Ctx}
    (h : x ∉ Ctx.fvI Γ) (hb : x = b → a ∉ Ctx.fvI Γ) : x ∉ Ctx.fvI (Ctx.renameI a b Γ) := by
  intro hc
  rcases Ctx.fvI_renameI a b x Γ hc with ⟨h1, h2⟩ | h2
  · exact hb h1 h2
  · exact h h2

theorem Pf.notMem_fvI_renameI {a b x : String} {p : Pf}
    (h : x ∉ p.fvI) (hb : x = b → a ∉ p.fvI) : x ∉ (Pf.renameI a b p).fvI := by
  intro hc
  rcases Pf.fvI_renameI a b x p hc with ⟨h1, h2⟩ | h2
  · exact hb h1 h2
  · exact h h2

theorem Form.notMem_fv_renameI {a b x : String} {A : Form}
    (h : x ∉ A.fv) (hb : x = b → a ∉ A.fv) : x ∉ (Form.renameI a b A).fv := by
  intro hc
  rcases Form.fv_renameI a b x A hc with ⟨h1, h2⟩ | h2
  · exact hb h1 h2
  · exact h h2

/-! ## Renaming a derivation

`b` must be new: absent from the context, the proof term, every formula the
derivation concludes with, and every individual eigenvariable it chooses.  The
last is what stops the rename colliding with a binder. -/

/-- The conclusion's free individuals are among the collected ones — by
definition, since `concls` puts them first, outside the match. -/
theorem Derives.mem_concls {Γ : Ctx} {p : Pf} {A : Form} (d : Derives p Γ A) {x : String}
    (h : x ∈ A.fv) : x ∈ d.concls := by
  cases d <;> exact List.mem_append.mpr (Or.inl h)

/-- …so a name missing from `concls` is missing from the conclusion. -/
theorem Derives.notMem_fv {Γ : Ctx} {p : Pf} {A : Form} (d : Derives p Γ A) {x : String}
    (h : x ∉ d.concls) : x ∉ A.fv :=
  fun hx => h (d.mem_concls hx)

private theorem nmL {α : Type} {x : α} {l₁ l₂ : List α} (h : x ∉ l₁ ++ l₂) : x ∉ l₁ :=
  fun hx => h (List.mem_append.mpr (Or.inl hx))
private theorem nmR {α : Type} {x : α} {l₁ l₂ : List α} (h : x ∉ l₁ ++ l₂) : x ∉ l₂ :=
  fun hx => h (List.mem_append.mpr (Or.inr hx))
private theorem nmC {α : Type} {x y : α} {l : List α} (h : x ∉ y :: l) : x ∉ l :=
  fun hx => h (List.mem_cons_of_mem _ hx)
private theorem neC {α : Type} {x y : α} {l : List α} (h : x ∉ y :: l) : x ≠ y :=
  fun hx => h (hx ▸ List.mem_cons_self ..)

noncomputable def Derives.renameI : {Γ : Ctx} → {p : Pf} → {A : Form} → (d : Derives p Γ A) →
    ∀ (a b : String), b ∉ Ctx.fvI Γ → b ∉ p.fvI → b ∉ d.concls → b ∉ d.namesI →
      Derives (Pf.renameI a b p) (Ctx.renameI a b Γ) (Form.renameI a b A) := by
  intro Γ p A d
  induction d with
  | var h => intro a b _ _ _ _; exact .var (Ctx.mem_renameI a b h)
  | topI => intro _ _ _ _ _ _; exact .topI
  | botE _ ih =>
      intro a b hΓ hp hc hn
      try simp only [Derives.namesI, Derives.concls, Pf.fvI] at hn hc hp
      exact .botE (ih a b hΓ (nmR hp) (nmR hc) hn)
  | andI _ _ ih₁ ih₂ =>
      intro a b hΓ hp hc hn
      try simp only [Derives.namesI, Derives.concls, Pf.fvI] at hn hc hp
      exact .andI (ih₁ a b hΓ (nmL hp) (nmL (nmR hc)) (nmL hn))
                  (ih₂ a b hΓ (nmR hp) (nmR (nmR hc)) (nmR hn))
  | andE₁ _ ih =>
      intro a b hΓ hp hc hn
      try simp only [Derives.namesI, Derives.concls, Pf.fvI] at hn hc hp
      exact .andE₁ (ih a b hΓ hp (nmR hc) hn)
  | andE₂ _ ih =>
      intro a b hΓ hp hc hn
      try simp only [Derives.namesI, Derives.concls, Pf.fvI] at hn hc hp
      exact .andE₂ (ih a b hΓ hp (nmR hc) hn)
  | orI₁ _ ih =>
      intro a b hΓ hp hc hn
      try simp only [Derives.namesI, Derives.concls, Pf.fvI] at hn hc hp
      exact .orI₁ (ih a b hΓ hp (nmR hc) hn)
  | orI₂ _ ih =>
      intro a b hΓ hp hc hn
      try simp only [Derives.namesI, Derives.concls, Pf.fvI] at hn hc hp
      exact .orI₂ (ih a b hΓ hp (nmR hc) hn)
  | circI _ ih =>
      intro a b hΓ hp hc hn
      try simp only [Derives.namesI, Derives.concls, Pf.fvI] at hn hc hp
      exact .circI (ih a b hΓ hp (nmR hc) hn)
  | impE _ _ ih₁ ih₂ =>
      intro a b hΓ hp hc hn
      try simp only [Derives.namesI, Derives.concls, Pf.fvI] at hn hc hp
      exact .impE (ih₁ a b hΓ (nmL hp) (nmL (nmR hc)) (nmL hn))
                  (ih₂ a b hΓ (nmR hp) (nmR (nmR hc)) (nmR hn))
  | @impI Γ p₀ C B z hz _ ih =>
      intro a b hΓ hp hc hn
      try simp only [Derives.namesI, Derives.concls, Pf.fvI] at hn hc hp
      refine .impI z ⟨by rw [Ctx.fvP_renameI]; exact hz.1,
                      by rw [Pf.fvP_renameI]; exact hz.2⟩ ?_
      have key := ih a b
        (by intro h
            rcases List.mem_append.mp h with h | h
            · exact (nmL (nmL hc)) h
            · exact hΓ h)
        (by rw [Pf.fvI_openP]; exact hp)
        (nmR hc) hn
      rw [Pf.renameI_openPWith] at key
      exact key
  | @orE Γ r p₁ p₂ A₁ A₂ K y z hy hz dr d₁ d₂ ihr ih₁ ih₂ =>
      intro a b hΓ hp hc hn
      try simp only [Derives.namesI, Derives.concls, Pf.fvI] at hn hc hp
      have hor : b ∉ (Form.or A₁ A₂).fv := dr.notMem_fv (nmL (nmL (nmR hc)))
      have hA₁ : b ∉ A₁.fv := nmL hor
      have hA₂ : b ∉ A₂.fv := nmR hor
      refine .orE y z ⟨by rw [Ctx.fvP_renameI]; exact hy.1, by rw [Pf.fvP_renameI]; exact hy.2⟩
                      ⟨by rw [Ctx.fvP_renameI]; exact hz.1, by rw [Pf.fvP_renameI]; exact hz.2⟩
        (ihr a b hΓ (nmL (nmL hp)) (nmL (nmL (nmR hc))) (nmL (nmL hn))) ?_ ?_
      · have key := ih₁ a b
          (by intro h
              rcases List.mem_append.mp h with h | h
              · exact hA₁ h
              · exact hΓ h)
          (by rw [Pf.fvI_openP]; exact nmR (nmL hp))
          (nmR (nmL (nmR hc))) (nmR (nmL hn))
        rw [Pf.renameI_openPWith] at key
        exact key
      · have key := ih₂ a b
          (by intro h
              rcases List.mem_append.mp h with h | h
              · exact hA₂ h
              · exact hΓ h)
          (by rw [Pf.fvI_openP]; exact nmR hp)
          (nmR (nmR hc)) (nmR hn)
        rw [Pf.renameI_openPWith] at key
        exact key
  | @circE Γ q p₀ c A₁ B z hz dp db ihp ihb =>
      intro a b hΓ hp hc hn
      try simp only [Derives.namesI, Derives.concls, Pf.fvI] at hn hc hp
      have hA₁ : b ∉ A₁.fv := dp.notMem_fv (nmL (nmR hc))
      refine .circE z ⟨by rw [Ctx.fvP_renameI]; exact hz.1, by rw [Pf.fvP_renameI]; exact hz.2⟩
        (ihp a b hΓ (nmL hp) (nmL (nmR hc)) (nmL hn)) ?_
      have key := ihb a b
        (by intro h
            rcases List.mem_append.mp h with h | h
            · exact hA₁ h
            · exact hΓ h)
        (by rw [Pf.fvI_openP]; exact nmR hp)
        (nmR (nmR hc)) (nmR hn)
      rw [Pf.renameI_openPWith] at key
      exact key
  | @allE Γ p₀ A' B t _ h ih =>
      intro a b hΓ hp hc hn
      try simp only [Derives.namesI, Derives.concls, Pf.fvI] at hn hc hp
      refine .allE (Tm.renameI a b t) (ih a b hΓ (nmR hp) (nmR hc) hn) ?_
      rw [h, Form.renameI_openAt]
  | @exI Γ p₀ A' t _ ih =>
      intro a b hΓ hp hc hn
      try simp only [Derives.namesI, Derives.concls, Pf.fvI] at hn hc hp
      have key := ih a b hΓ (nmR hp) (nmR hc) hn
      rw [Form.renameI_openAt] at key
      exact .exI (Tm.renameI a b t) key
  | @allI Γ p₀ A' a' ha d₀ ih =>
      intro a b hΓ hp hc hn
      try simp only [Derives.namesI, Derives.concls, Pf.fvI] at hn hc hp
      have hne : b ≠ a' := neC hn
      have hA' : b ∉ A'.fv := nmL hc
      have key := ih a b hΓ
        (by intro h
            rcases Pf.fvI_openI b (.fvar a') p₀ 0 h with h | h
            · exact hne (by simpa [Tm.fv] using h)
            · exact hp h)
        (nmR hc) (nmC hn)
      rw [Pf.renameI_openIWith, Form.renameI_openWith] at key
      refine .allI (if a' = a then b else a') ?_ key
      by_cases hcase : a' = a
      · subst hcase
        simp only [reduceIte]
        exact ⟨Ctx.notMem_fvI_renameI hΓ (fun _ => ha.1),
               Pf.notMem_fvI_renameI hp (fun _ => ha.2.1),
               Form.notMem_fv_renameI hA' (fun _ => ha.2.2)⟩
      · simp only [if_neg hcase]
        exact ⟨Ctx.notMem_fvI_renameI ha.1 (fun h => absurd h.symm hne),
               Pf.notMem_fvI_renameI ha.2.1 (fun h => absurd h.symm hne),
               Form.notMem_fv_renameI ha.2.2 (fun h => absurd h.symm hne)⟩
  | @exE Γ r p₀ A₁ K a' z ha hK hz dr db ihr ihb =>
      intro a b hΓ hp hc hn
      try simp only [Derives.namesI, Derives.concls, Pf.fvI] at hn hc hp
      have hne : b ≠ a' := neC hn
      have hA₁ : b ∉ A₁.fv := dr.notMem_fv (nmL (nmR hc))
      have hK' : b ∉ K.fv := nmL hc
      refine .exE (if a' = a then b else a') z ?_ ?_
                  ⟨by rw [Ctx.fvP_renameI]; exact hz.1, by rw [Pf.fvP_renameI]; exact hz.2⟩
                  (ihr a b hΓ (nmL hp) (nmL (nmR hc)) (nmL (nmC hn))) ?_
      · by_cases hcase : a' = a
        · subst hcase
          simp only [reduceIte]
          exact ⟨Ctx.notMem_fvI_renameI hΓ (fun _ => ha.1),
                 Pf.notMem_fvI_renameI (nmR hp) (fun _ => ha.2.1),
                 Form.notMem_fv_renameI hA₁ (fun _ => ha.2.2)⟩
        · simp only [if_neg hcase]
          exact ⟨Ctx.notMem_fvI_renameI ha.1 (fun h => absurd h.symm hne),
                 Pf.notMem_fvI_renameI ha.2.1 (fun h => absurd h.symm hne),
                 Form.notMem_fv_renameI ha.2.2 (fun h => absurd h.symm hne)⟩
      · by_cases hcase : a' = a
        · subst hcase
          simp only [reduceIte]
          exact Form.notMem_fv_renameI hK' (fun _ => hK)
        · simp only [if_neg hcase]
          exact Form.notMem_fv_renameI hK (fun h => absurd h.symm hne)
      · have key := ihb a b
          (by intro h
              rcases List.mem_append.mp h with h | h
              · rcases Form.fv_openAt b (.fvar a') A₁ 0 h with h | h
                · exact hne (by simpa [Tm.fv] using h)
                · exact hA₁ h
              · exact hΓ h)
          (by rw [Pf.fvI_openP]
              intro h
              rcases Pf.fvI_openI b (.fvar a') p₀ 0 h with h | h
              · exact hne (by simpa [Tm.fv] using h)
              · exact (nmR hp) h)
          (nmR (nmR hc)) (nmR (nmC hn))
        simp only [Ctx.renameI, Pf.renameI, Pf.renameI_openPWith, Pf.renameI_openIWith,
          Form.renameI_openWith] at key
        exact key

/-! ## Renaming a name that is not there

The form the eigenvariable case wants: if `a` does not occur free in the
judgement then renaming it changes nothing, so the result is a derivation of
the *same* judgement — with `a` replaced by `b` among the eigenvariables. -/

mutual
theorem Tm.renameI_eq_of_notMem (a b : String) :
    ∀ t : Tm, a ∉ Tm.fv t → Tm.renameI a b t = t
  | .bvar _,  _ => rfl
  | .fvar x,  h => by
      have : x ≠ a := fun hx => h (by simp [Tm.fv, hx])
      simp [Tm.renameI, this]
  | .fn _ ts, h => by simp [Tm.renameI, Tm.renameIList_eq_of_notMem a b ts h]
theorem Tm.renameIList_eq_of_notMem (a b : String) :
    ∀ ts : List Tm, a ∉ Tm.fvList ts → Tm.renameIList a b ts = ts
  | [],      _ => rfl
  | t :: ts, h => by
      simp only [Tm.fvList, List.mem_append, not_or] at h
      simp [Tm.renameIList, Tm.renameI_eq_of_notMem a b t h.1,
            Tm.renameIList_eq_of_notMem a b ts h.2]
end

theorem Form.renameI_eq_of_notMem (a b : String) :
    ∀ A : Form, a ∉ Form.fv A → Form.renameI a b A = A := by
  intro A
  induction A with
  | top | bot => intro _; rfl
  | pred _ ts => intro h; simp [Form.renameI, Tm.renameIList_eq_of_notMem a b ts h]
  | and _ _ ih₁ ih₂ | or _ _ ih₁ ih₂ | imp _ _ ih₁ ih₂ =>
      intro h
      simp only [Form.fv, List.mem_append, not_or] at h
      simp [Form.renameI, ih₁ h.1, ih₂ h.2]
  | circ _ _ ih | forall_ _ ih | exists_ _ ih => intro h; simp [Form.renameI, ih h]

theorem Pf.renameI_eq_of_notMem (a b : String) :
    ∀ p : Pf, a ∉ p.fvI → Pf.renameI a b p = p := by
  intro p
  induction p with
  | bvar _ | fvar _ | star => intro _; rfl
  | fst _ ih | snd _ ih | inl _ ih | inr _ ih | lam _ ih | val _ _ ih | gen _ ih =>
      intro h; simp [Pf.renameI, ih h]
  | pair _ _ ih₁ ih₂ | app _ _ ih₁ ih₂ | letQ _ _ _ ih₁ ih₂ | caseEx _ _ ih₁ ih₂ =>
      intro h
      simp only [Pf.fvI, List.mem_append, not_or] at h
      simp [Pf.renameI, ih₁ h.1, ih₂ h.2]
  | caseOr _ _ _ ih₁ ih₂ ih₃ =>
      intro h
      simp only [Pf.fvI, List.mem_append, not_or] at h
      simp [Pf.renameI, ih₁ h.1.1, ih₂ h.1.2, ih₃ h.2]
  | inst t _ ih | pack t _ ih =>
      intro h
      simp only [Pf.fvI, List.mem_append, not_or] at h
      simp [Pf.renameI, Tm.renameI_eq_of_notMem a b t h.1, ih h.2]
  | exf A _ ih =>
      intro h
      simp only [Pf.fvI, List.mem_append, not_or] at h
      simp [Pf.renameI, Form.renameI_eq_of_notMem a b A h.1, ih h.2]

theorem Ctx.renameI_eq_of_notMem (a b : String) :
    ∀ Γ : Ctx, a ∉ Ctx.fvI Γ → Ctx.renameI a b Γ = Γ := by
  intro Γ
  induction Γ with
  | nil => intro _; rfl
  | cons e Γ ih =>
      obtain ⟨q, C⟩ := e
      intro h
      simp only [Ctx.fvI, List.mem_append, not_or] at h
      simp [Ctx.renameI, Pf.renameI_eq_of_notMem a b q h.1.1,
            Form.renameI_eq_of_notMem a b C h.1.2, ih h.2]

/--
Re-basing.  `a` is invisible in the judgement — it can only be an eigenvariable
— so renaming it to a new `b` gives a derivation of *the same thing*.
-/
noncomputable def Derives.rebase {Γ : Ctx} {p : Pf} {A : Form} (d : Derives p Γ A)
    (a b : String)
    (ha : a ∉ Ctx.fvI Γ) (hap : a ∉ p.fvI) (haA : a ∉ A.fv)
    (hΓ : b ∉ Ctx.fvI Γ) (hp : b ∉ p.fvI) (hc : b ∉ d.concls) (hn : b ∉ d.namesI) :
    Derives p Γ A := by
  have key := d.renameI a b hΓ hp hc hn
  rw [Ctx.renameI_eq_of_notMem a b Γ ha, Pf.renameI_eq_of_notMem a b p hap,
      Form.renameI_eq_of_notMem a b A haA] at key
  exact key

end LaxLogic.QLL
