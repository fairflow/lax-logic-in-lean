/-
# `LaxLogic.QLL.Abstract` — abstracting a variable out of a proof term

`Deriv.lean`'s binding rules are stated in the exists-fresh style: `⊃I`
concludes `λp` from a derivation of `p⟨z⟩`, so anyone *building* a derivation
has to produce the body already abstracted.  `Prv` has no proof terms, so its
`impI` gives a derivation in an extended context and nothing else — and turning
that into a `Derives` needs the inverse of opening.

That inverse is `closeP` for proof variables and `closeI` for individuals,
with the two round trips below; they are the proof-term analogues of
`Tm.openAt_closeAt` and `Form.openAt_closeAt` in `Lc.lean`, and each needs the
corresponding local closedness, for the same reason: closing a term with a
loose index and reopening it capture-converts that index into the name.
-/
import LaxLogic.QLL.Lc

namespace LaxLogic.QLL

/-! ## Local closedness in the proof indices -/

/-- No loose *proof* index at or above `k`. -/
def Pf.lcP (k : Nat) : Pf → Prop
  | .bvar i       => i < k
  | .fvar _       => True
  | .star         => True
  | .pair p q     => Pf.lcP k p ∧ Pf.lcP k q
  | .app p q      => Pf.lcP k p ∧ Pf.lcP k q
  | .fst p        => Pf.lcP k p
  | .snd p        => Pf.lcP k p
  | .inl p        => Pf.lcP k p
  | .inr p        => Pf.lcP k p
  | .val _ p      => Pf.lcP k p
  | .gen p        => Pf.lcP k p
  | .inst _ p     => Pf.lcP k p
  | .pack _ p     => Pf.lcP k p
  | .exf _ p      => Pf.lcP k p
  | .caseOr r p q => Pf.lcP k r ∧ Pf.lcP (k + 1) p ∧ Pf.lcP (k + 1) q
  | .lam p        => Pf.lcP (k + 1) p
  | .letQ _ p b   => Pf.lcP k p ∧ Pf.lcP (k + 1) b
  | .caseEx r p   => Pf.lcP k r ∧ Pf.lcP (k + 1) p

/-! ## Abstraction -/

/-- Replace the free proof variable `x` by the bound index `k`. -/
def Pf.closeP (k : Nat) (x : String) : Pf → Pf
  | .bvar i       => .bvar i
  | .fvar y       => if y = x then .bvar k else .fvar y
  | .star         => .star
  | .pair p q     => .pair (closeP k x p) (closeP k x q)
  | .app p q      => .app (closeP k x p) (closeP k x q)
  | .fst p        => .fst (closeP k x p)
  | .snd p        => .snd (closeP k x p)
  | .inl p        => .inl (closeP k x p)
  | .inr p        => .inr (closeP k x p)
  | .val q p      => .val q (closeP k x p)
  | .gen p        => .gen (closeP k x p)
  | .inst t p     => .inst t (closeP k x p)
  | .pack t p     => .pack t (closeP k x p)
  | .exf A p      => .exf A (closeP k x p)
  | .caseOr r p q => .caseOr (closeP k x r) (closeP (k + 1) x p) (closeP (k + 1) x q)
  | .lam p        => .lam (closeP (k + 1) x p)
  | .letQ q p b   => .letQ q (closeP k x p) (closeP (k + 1) x b)
  | .caseEx r p   => .caseEx (closeP k x r) (closeP (k + 1) x p)

/-- Replace the free individual `a` by the bound index `k`, in the proof term
and in the terms and formulas it carries. -/
def Pf.closeI (k : Nat) (a : String) : Pf → Pf
  | .bvar i       => .bvar i
  | .fvar y       => .fvar y
  | .star         => .star
  | .pair p q     => .pair (closeI k a p) (closeI k a q)
  | .app p q      => .app (closeI k a p) (closeI k a q)
  | .fst p        => .fst (closeI k a p)
  | .snd p        => .snd (closeI k a p)
  | .inl p        => .inl (closeI k a p)
  | .inr p        => .inr (closeI k a p)
  | .val q p      => .val q (closeI k a p)
  | .caseOr r p q => .caseOr (closeI k a r) (closeI k a p) (closeI k a q)
  | .lam p        => .lam (closeI k a p)
  | .letQ q p b   => .letQ q (closeI k a p) (closeI k a b)
  | .gen p        => .gen (closeI (k + 1) a p)
  | .inst t p     => .inst (Tm.closeAt k a t) (closeI k a p)
  | .pack t p     => .pack (Tm.closeAt k a t) (closeI k a p)
  | .caseEx r p   => .caseEx (closeI k a r) (closeI (k + 1) a p)
  | .exf A p      => .exf (Form.closeAt k a A) (closeI k a p)

/-! ## The round trips -/

theorem Pf.openP_closeP (x : String) : ∀ (p : Pf) (k : Nat),
    Pf.lcP k p → Pf.openP k (.fvar x) (Pf.closeP k x p) = p := by
  intro p
  induction p with
  | bvar i => intro k h; simp only [Pf.lcP] at h;
              simp only [Pf.closeP, Pf.openP, if_neg (Nat.ne_of_lt h)]
  | fvar y => intro k _; by_cases hy : y = x <;> simp [Pf.closeP, Pf.openP, hy]
  | star => intro _ _; rfl
  | pair _ _ ih₁ ih₂ | app _ _ ih₁ ih₂ =>
      intro k h; simp [Pf.closeP, Pf.openP, ih₁ k h.1, ih₂ k h.2]
  | fst _ ih | snd _ ih | inl _ ih | inr _ ih | val _ _ ih | gen _ ih
  | inst _ _ ih | pack _ _ ih | exf _ _ ih =>
      intro k h; simp [Pf.closeP, Pf.openP, ih k h]
  | lam _ ih => intro k h; simp [Pf.closeP, Pf.openP, ih (k + 1) h]
  | caseOr _ _ _ ih₁ ih₂ ih₃ =>
      intro k h
      simp [Pf.closeP, Pf.openP, ih₁ k h.1, ih₂ (k + 1) h.2.1, ih₃ (k + 1) h.2.2]
  | letQ _ _ _ ih₁ ih₂ =>
      intro k h; simp [Pf.closeP, Pf.openP, ih₁ k h.1, ih₂ (k + 1) h.2]
  | caseEx _ _ ih₁ ih₂ =>
      intro k h; simp [Pf.closeP, Pf.openP, ih₁ k h.1, ih₂ (k + 1) h.2]

theorem Pf.openI_closeI (a : String) : ∀ (p : Pf) (k : Nat),
    Pf.lcI k p → Pf.openI k (.fvar a) (Pf.closeI k a p) = p := by
  intro p
  induction p with
  | bvar _ | fvar _ | star => intro _ _; rfl
  | pair _ _ ih₁ ih₂ | app _ _ ih₁ ih₂ | letQ _ _ _ ih₁ ih₂ =>
      intro k h; simp [Pf.closeI, Pf.openI, ih₁ k h.1, ih₂ k h.2]
  | fst _ ih | snd _ ih | inl _ ih | inr _ ih | val _ _ ih | lam _ ih =>
      intro k h; simp [Pf.closeI, Pf.openI, ih k h]
  | caseOr _ _ _ ih₁ ih₂ ih₃ =>
      intro k h; simp [Pf.closeI, Pf.openI, ih₁ k h.1, ih₂ k h.2.1, ih₃ k h.2.2]
  | gen _ ih => intro k h; simp [Pf.closeI, Pf.openI, ih (k + 1) h]
  | inst t _ ih | pack t _ ih =>
      intro k h
      simp [Pf.closeI, Pf.openI, Tm.openAt_closeAt k a t h.1, ih k h.2]
  | caseEx _ _ ih₁ ih₂ =>
      intro k h; simp [Pf.closeI, Pf.openI, ih₁ k h.1, ih₂ (k + 1) h.2]
  | exf A _ ih =>
      intro k h
      simp [Pf.closeI, Pf.openI, Form.openAt_closeAt a k A h.1, ih k h.2]

/-! ## What abstraction does to the indices and the names -/

theorem Pf.lcP_closeP (x : String) : ∀ (p : Pf) (k : Nat),
    Pf.lcP k p → Pf.lcP (k + 1) (Pf.closeP k x p) := by
  intro p
  induction p with
  | bvar i => intro k h; exact Nat.lt_succ_of_lt h
  | fvar y => intro k _; by_cases hy : y = x <;> simp [Pf.closeP, hy, Pf.lcP]
  | star => intro _ _; trivial
  | pair _ _ ih₁ ih₂ | app _ _ ih₁ ih₂ =>
      intro k h; exact ⟨ih₁ k h.1, ih₂ k h.2⟩
  | fst _ ih | snd _ ih | inl _ ih | inr _ ih | val _ _ ih | gen _ ih
  | inst _ _ ih | pack _ _ ih | exf _ _ ih => intro k h; exact ih k h
  | lam _ ih => intro k h; exact ih (k + 1) h
  | caseOr _ _ _ ih₁ ih₂ ih₃ =>
      intro k h; exact ⟨ih₁ k h.1, ih₂ (k + 1) h.2.1, ih₃ (k + 1) h.2.2⟩
  | letQ _ _ _ ih₁ ih₂ => intro k h; exact ⟨ih₁ k h.1, ih₂ (k + 1) h.2⟩
  | caseEx _ _ ih₁ ih₂ => intro k h; exact ⟨ih₁ k h.1, ih₂ (k + 1) h.2⟩

/-! Closing raises the bound: the abstracted name becomes an index at `k`. -/

mutual
theorem Tm.lcAt_closeAt (k : Nat) (a : String) :
    ∀ t : Tm, Tm.lcAt k t → Tm.lcAt (k + 1) (Tm.closeAt k a t)
  | .bvar i,  h => by
      simp only [Tm.lcAt] at h
      simp only [Tm.closeAt]
      show i < k + 1
      omega
  | .fvar y,  _ => by
      by_cases hy : y = a <;> simp [Tm.closeAt, hy, Tm.lcAt]
  | .fn _ ts, h => Tm.lcAtList_closeAtList k a ts h
theorem Tm.lcAtList_closeAtList (k : Nat) (a : String) :
    ∀ ts : List Tm, Tm.lcAtList k ts → Tm.lcAtList (k + 1) (Tm.closeAtList k a ts)
  | [],      _ => trivial
  | t :: ts, h =>
      ⟨Tm.lcAt_closeAt k a t h.1, Tm.lcAtList_closeAtList k a ts h.2⟩
end

theorem Form.lcAt_closeAt (a : String) : ∀ (k : Nat) (A : Form),
    Form.lcAt k A → Form.lcAt (k + 1) (Form.closeAt k a A) := by
  intro k A
  induction A generalizing k with
  | top | bot => intro _; trivial
  | pred _ ts => intro h; exact Tm.lcAtList_closeAtList k a ts h
  | and _ _ ih₁ ih₂ | or _ _ ih₁ ih₂ | imp _ _ ih₁ ih₂ =>
      intro h; exact ⟨ih₁ k h.1, ih₂ k h.2⟩
  | circ _ _ ih => intro h; exact ih k h
  | forall_ _ ih | exists_ _ ih => intro h; exact ih (k + 1) h

theorem Pf.lcI_closeI (a : String) : ∀ (p : Pf) (k : Nat),
    Pf.lcI k p → Pf.lcI (k + 1) (Pf.closeI k a p) := by
  intro p
  induction p with
  | bvar _ | fvar _ | star => intro _ _; trivial
  | pair _ _ ih₁ ih₂ | app _ _ ih₁ ih₂ | letQ _ _ _ ih₁ ih₂ =>
      intro k h; exact ⟨ih₁ k h.1, ih₂ k h.2⟩
  | fst _ ih | snd _ ih | inl _ ih | inr _ ih | val _ _ ih | lam _ ih =>
      intro k h; exact ih k h
  | caseOr _ _ _ ih₁ ih₂ ih₃ =>
      intro k h; exact ⟨ih₁ k h.1, ih₂ k h.2.1, ih₃ k h.2.2⟩
  | gen _ ih => intro k h; exact ih (k + 1) h
  | inst t _ ih | pack t _ ih =>
      intro k h; exact ⟨Tm.lcAt_closeAt k a t h.1, ih k h.2⟩
  | caseEx _ _ ih₁ ih₂ => intro k h; exact ⟨ih₁ k h.1, ih₂ (k + 1) h.2⟩
  | exf A _ ih => intro k h; exact ⟨Form.lcAt_closeAt a k A h.1, ih k h.2⟩

/-- Closing a proof variable leaves the individual indices alone. -/
theorem Pf.lcI_closeP (x : String) : ∀ (p : Pf) (j k : Nat),
    Pf.lcI k p → Pf.lcI k (Pf.closeP j x p) := by
  intro p
  induction p with
  | bvar _ | star => intro _ _ _; trivial
  | fvar y => intro j _ _; by_cases hy : y = x <;> simp [Pf.closeP, hy, Pf.lcI]
  | pair _ _ ih₁ ih₂ | app _ _ ih₁ ih₂ | letQ _ _ _ ih₁ ih₂ =>
      intro j k h; exact ⟨ih₁ _ k h.1, ih₂ _ k h.2⟩
  | fst _ ih | snd _ ih | inl _ ih | inr _ ih | val _ _ ih | lam _ ih =>
      intro j k h; exact ih _ k h
  | caseOr _ _ _ ih₁ ih₂ ih₃ =>
      intro j k h; exact ⟨ih₁ _ k h.1, ih₂ _ k h.2.1, ih₃ _ k h.2.2⟩
  | gen _ ih => intro j k h; exact ih _ (k + 1) h
  | inst _ _ ih | pack _ _ ih | exf _ _ ih => intro j k h; exact ⟨h.1, ih _ k h.2⟩
  | caseEx _ _ ih₁ ih₂ => intro j k h; exact ⟨ih₁ _ k h.1, ih₂ _ (k + 1) h.2⟩

/-- Closing an individual leaves the proof indices alone. -/
theorem Pf.lcP_closeI (a : String) : ∀ (p : Pf) (j k : Nat),
    Pf.lcP k p → Pf.lcP k (Pf.closeI j a p) := by
  intro p
  induction p with
  | bvar _ | fvar _ | star => intro _ _ h; exact h
  | pair _ _ ih₁ ih₂ | app _ _ ih₁ ih₂ =>
      intro j k h; exact ⟨ih₁ _ k h.1, ih₂ _ k h.2⟩
  | fst _ ih | snd _ ih | inl _ ih | inr _ ih | val _ _ ih
  | inst _ _ ih | pack _ _ ih | exf _ _ ih => intro j k h; exact ih _ k h
  | gen _ ih => intro j k h; exact ih _ k h
  | lam _ ih => intro j k h; exact ih _ (k + 1) h
  | caseOr _ _ _ ih₁ ih₂ ih₃ =>
      intro j k h; exact ⟨ih₁ _ k h.1, ih₂ _ (k + 1) h.2.1, ih₃ _ (k + 1) h.2.2⟩
  | letQ _ _ _ ih₁ ih₂ => intro j k h; exact ⟨ih₁ _ k h.1, ih₂ _ (k + 1) h.2⟩
  | caseEx _ _ ih₁ ih₂ => intro j k h; exact ⟨ih₁ _ k h.1, ih₂ _ (k + 1) h.2⟩

theorem Pf.notMem_fvP_closeP (x : String) : ∀ (p : Pf) (k : Nat),
    x ∉ (Pf.closeP k x p).fvP := by
  intro p
  induction p with
  | bvar _ | star => intro _; simp [Pf.closeP, Pf.fvP]
  | fvar y =>
      intro k
      by_cases hy : y = x <;> simp [Pf.closeP, Pf.fvP, hy]
      exact fun h => hy h.symm
  | pair _ _ ih₁ ih₂ | app _ _ ih₁ ih₂ | letQ _ _ _ ih₁ ih₂ =>
      intro k; simp only [Pf.closeP, Pf.fvP, List.mem_append, not_or]
      exact ⟨ih₁ _, ih₂ _⟩
  | fst _ ih | snd _ ih | inl _ ih | inr _ ih | val _ _ ih | lam _ ih | gen _ ih
  | inst _ _ ih | pack _ _ ih | exf _ _ ih => intro k; exact ih _
  | caseOr _ _ _ ih₁ ih₂ ih₃ =>
      intro k; simp only [Pf.closeP, Pf.fvP, List.mem_append, not_or]
      exact ⟨⟨ih₁ _, ih₂ _⟩, ih₃ _⟩
  | caseEx _ _ ih₁ ih₂ =>
      intro k; simp only [Pf.closeP, Pf.fvP, List.mem_append, not_or]
      exact ⟨ih₁ _, ih₂ _⟩

theorem Pf.notMem_fvI_closeI (a : String) : ∀ (p : Pf) (k : Nat),
    a ∉ (Pf.closeI k a p).fvI := by
  intro p
  induction p with
  | bvar _ | fvar _ | star => intro _; simp [Pf.closeI, Pf.fvI]
  | pair _ _ ih₁ ih₂ | app _ _ ih₁ ih₂ | letQ _ _ _ ih₁ ih₂ =>
      intro k; simp only [Pf.closeI, Pf.fvI, List.mem_append, not_or]
      exact ⟨ih₁ _, ih₂ _⟩
  | fst _ ih | snd _ ih | inl _ ih | inr _ ih | val _ _ ih | lam _ ih | gen _ ih =>
      intro k; exact ih _
  | caseOr _ _ _ ih₁ ih₂ ih₃ =>
      intro k; simp only [Pf.closeI, Pf.fvI, List.mem_append, not_or]
      exact ⟨⟨ih₁ _, ih₂ _⟩, ih₃ _⟩
  | inst t _ ih | pack t _ ih =>
      intro k; simp only [Pf.closeI, Pf.fvI, List.mem_append, not_or]
      exact ⟨Tm.not_mem_fv_closeAt k a t, ih _⟩
  | caseEx _ _ ih₁ ih₂ =>
      intro k; simp only [Pf.closeI, Pf.fvI, List.mem_append, not_or]
      exact ⟨ih₁ _, ih₂ _⟩
  | exf A _ ih =>
      intro k; simp only [Pf.closeI, Pf.fvI, List.mem_append, not_or]
      exact ⟨Form.not_mem_fv_closeAt a k A, ih _⟩

/-- Closing an individual leaves the proof variables where they were. -/
theorem Pf.fvP_closeI (a : String) : ∀ (p : Pf) (k : Nat),
    (Pf.closeI k a p).fvP = p.fvP := by
  intro p
  induction p with
  | bvar _ | fvar _ | star => intro _; rfl
  | pair _ _ ih₁ ih₂ | app _ _ ih₁ ih₂ | letQ _ _ _ ih₁ ih₂ =>
      intro k; simp [Pf.closeI, Pf.fvP, ih₁ _, ih₂ _]
  | fst _ ih | snd _ ih | inl _ ih | inr _ ih | val _ _ ih | lam _ ih | gen _ ih
  | inst _ _ ih | pack _ _ ih | exf _ _ ih => intro k; simp [Pf.closeI, Pf.fvP, ih _]
  | caseOr _ _ _ ih₁ ih₂ ih₃ =>
      intro k; simp [Pf.closeI, Pf.fvP, ih₁ _, ih₂ _, ih₃ _]
  | caseEx _ _ ih₁ ih₂ => intro k; simp [Pf.closeI, Pf.fvP, ih₁ _, ih₂ _]

end LaxLogic.QLL
