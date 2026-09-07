/-
# `LaxLogic.QLL.Lc` — local closedness

C de Bruijn representation admits junk: `pred "P" [Tm.bvar 5]` is a perfectly
good `Form` and is not a formula of the object language.  `lcAt k` carves the
real syntax out of the raw datatype — no index at or above `k` occurs loose.

Only the **individual** index needs tracking.  C formula's well-formedness
cannot depend on proof-variable indices, and opening a proof binder cannot
create a loose individual, so `Pf.lcI` tracks one index and not two.  The
checker already rejects loose *proof* indices at runtime (`Err.looseIndex`);
this layer is about the other sort.

Wanted for three things, only one of which is the soundness proof:

* the open/close roundtrip `openAt k (fvar a) (closeAt k a C) = C`, which
  `infer`'s `∀` case needs and which holds only for locally closed `C`;
* `⊨` and `|A|` (Figs. 3 and 4), defined by recursion on `Form`, which have no
  meaning on a formula with a loose index;
* keeping `Derivable` from making claims about junk.
-/
import LaxLogic.QLL.Syntax

namespace LaxLogic.QLL

/-! ## The predicates -/

mutual
/-- No individual index at or above `k` occurs loose in the term. -/
def Tm.lcAt (k : Nat) : Tm → Prop
  | .bvar i  => i < k
  | .fvar _  => True
  | .fn _ ts => Tm.lcAtList k ts
/-- `lcAt` on a list of arguments. -/
def Tm.lcAtList (k : Nat) : List Tm → Prop
  | []      => True
  | t :: ts => Tm.lcAt k t ∧ Tm.lcAtList k ts
end

/-- No individual index at or above `k` occurs loose in the formula.  The
quantifiers raise `k`, being the only individual binders. -/
def Form.lcAt (k : Nat) : Form → Prop
  | .top       => True
  | .bot       => True
  | .pred _ ts => Tm.lcAtList k ts
  | .and A B   => Form.lcAt k A ∧ Form.lcAt k B
  | .or A B    => Form.lcAt k A ∧ Form.lcAt k B
  | .imp A B   => Form.lcAt k A ∧ Form.lcAt k B
  | .circ _ A  => Form.lcAt k A
  | .forall_ A => Form.lcAt (k + 1) A
  | .exists_ A => Form.lcAt (k + 1) A

/-- C closed formula. -/
abbrev Form.lc (A : Form) : Prop := Form.lcAt 0 A

/-- No individual index at or above `k` occurs loose in the terms and formulas
embedded in the proof term.  `gen` and `caseEx` raise `k`; the proof binders
`lam`, `caseOr` and `letQ` do not, since they bind the other sort. -/
def Pf.lcI (k : Nat) : Pf → Prop
  | .bvar _       => True
  | .fvar _       => True
  | .star         => True
  | .pair p q     => Pf.lcI k p ∧ Pf.lcI k q
  | .fst p        => Pf.lcI k p
  | .snd p        => Pf.lcI k p
  | .inl p        => Pf.lcI k p
  | .inr p        => Pf.lcI k p
  | .caseOr r p q => Pf.lcI k r ∧ Pf.lcI k p ∧ Pf.lcI k q
  | .lam p        => Pf.lcI k p
  | .app p q      => Pf.lcI k p ∧ Pf.lcI k q
  | .val _ p      => Pf.lcI k p
  | .letQ _ p b   => Pf.lcI k p ∧ Pf.lcI k b
  | .gen p        => Pf.lcI (k + 1) p
  | .inst t p     => Tm.lcAt k t ∧ Pf.lcI k p
  | .pack t p     => Tm.lcAt k t ∧ Pf.lcI k p
  | .caseEx r p   => Pf.lcI k r ∧ Pf.lcI (k + 1) p
  | .exf A p      => Form.lcAt k A ∧ Pf.lcI k p

/-- Every formula in the context is closed. -/
def Ctx.lc : Ctx → Prop
  | []          => True
  | (_, A) :: Γ => Form.lc A ∧ Ctx.lc Γ

/-! ## The open/close roundtrip

`closeAt k a` turns free occurrences of `a` into `bvar k`; `openAt k (fvar a)`
turns `bvar k` back into `fvar a`.  The composite is the identity *provided the
formula had no loose `bvar k` to begin with* — otherwise the round trip
capture-converts it into `a`.  This is what `infer`'s `∀` case rests on. -/

mutual
theorem Tm.openAt_closeAt (k : Nat) (a : String) :
    ∀ t : Tm, Tm.lcAt k t → Tm.openAt k (.fvar a) (Tm.closeAt k a t) = t
  | .bvar i, h => by
      simp only [Tm.lcAt] at h
      simp only [Tm.closeAt, Tm.openAt, if_neg (Nat.ne_of_lt h)]
  | .fvar x, _ => by
      by_cases hx : x = a
      · subst hx; simp [Tm.closeAt, Tm.openAt]
      · simp [Tm.closeAt, Tm.openAt, hx]
  | .fn _ ts, h => by
      simp only [Tm.lcAt] at h
      simp only [Tm.closeAt, Tm.openAt, Tm.openAtList_closeAtList k a ts h]
theorem Tm.openAtList_closeAtList (k : Nat) (a : String) :
    ∀ ts : List Tm, Tm.lcAtList k ts →
      Tm.openAtList k (.fvar a) (Tm.closeAtList k a ts) = ts
  | [],      _ => by simp [Tm.closeAtList, Tm.openAtList]
  | t :: ts, h => by
      simp only [Tm.lcAtList] at h
      simp only [Tm.closeAtList, Tm.openAtList,
        Tm.openAt_closeAt k a t h.1, Tm.openAtList_closeAtList k a ts h.2]
end

theorem Form.openAt_closeAt (a : String) :
    ∀ (k : Nat) (A : Form), Form.lcAt k A →
      Form.openAt k (.fvar a) (Form.closeAt k a A) = A
  | _, .top,       _ => rfl
  | _, .bot,       _ => rfl
  | k, .pred _ ts, h => by
      simp only [Form.lcAt] at h
      simp only [Form.closeAt, Form.openAt, Tm.openAtList_closeAtList k a ts h]
  | k, .and A B,   h => by
      simp only [Form.lcAt] at h
      simp only [Form.closeAt, Form.openAt,
        Form.openAt_closeAt a k A h.1, Form.openAt_closeAt a k B h.2]
  | k, .or A B,    h => by
      simp only [Form.lcAt] at h
      simp only [Form.closeAt, Form.openAt,
        Form.openAt_closeAt a k A h.1, Form.openAt_closeAt a k B h.2]
  | k, .imp A B,   h => by
      simp only [Form.lcAt] at h
      simp only [Form.closeAt, Form.openAt,
        Form.openAt_closeAt a k A h.1, Form.openAt_closeAt a k B h.2]
  | k, .circ _ A,  h => by
      simp only [Form.lcAt] at h
      simp only [Form.closeAt, Form.openAt, Form.openAt_closeAt a k A h]
  | k, .forall_ A, h => by
      simp only [Form.lcAt] at h
      simp only [Form.closeAt, Form.openAt, Form.openAt_closeAt a (k + 1) A h]
  | k, .exists_ A, h => by
      simp only [Form.lcAt] at h
      simp only [Form.closeAt, Form.openAt, Form.openAt_closeAt a (k + 1) A h]

/-- The form the `∀` case of `infer` needs. -/
theorem Form.openWith_closeWith {C : Form} (a : String) (h : Form.lc C) :
    Form.openWith a (Form.closeWith a C) = C :=
  Form.openAt_closeAt a 0 C h

/-! ## Deciding local closedness

The checker needs `lcAt` as a *runtime test*, not as a threaded hypothesis: it
is wanted at exactly one place, inference for `∀`.  C boolean twin plus its
characterisation gives the `Decidable` instance. -/

mutual
def Tm.lcAtB (k : Nat) : Tm → Bool
  | .bvar i  => decide (i < k)
  | .fvar _  => true
  | .fn _ ts => Tm.lcAtListB k ts
def Tm.lcAtListB (k : Nat) : List Tm → Bool
  | []      => true
  | t :: ts => Tm.lcAtB k t && Tm.lcAtListB k ts
end

mutual
theorem Tm.lcAtB_iff (k : Nat) : ∀ t : Tm, Tm.lcAtB k t = true ↔ Tm.lcAt k t
  | .bvar _  => by simp [Tm.lcAtB, Tm.lcAt]
  | .fvar _  => by simp [Tm.lcAtB, Tm.lcAt]
  | .fn _ ts => by simp [Tm.lcAtB, Tm.lcAt, Tm.lcAtListB_iff k ts]
theorem Tm.lcAtListB_iff (k : Nat) : ∀ ts : List Tm,
    Tm.lcAtListB k ts = true ↔ Tm.lcAtList k ts
  | []      => by simp [Tm.lcAtListB, Tm.lcAtList]
  | t :: ts => by
      simp [Tm.lcAtListB, Tm.lcAtList, Tm.lcAtB_iff k t, Tm.lcAtListB_iff k ts]
end

def Form.lcAtB (k : Nat) : Form → Bool
  | .top       => true
  | .bot       => true
  | .pred _ ts => Tm.lcAtListB k ts
  | .and A B   => Form.lcAtB k A && Form.lcAtB k B
  | .or A B    => Form.lcAtB k A && Form.lcAtB k B
  | .imp A B   => Form.lcAtB k A && Form.lcAtB k B
  | .circ _ A  => Form.lcAtB k A
  | .forall_ A => Form.lcAtB (k + 1) A
  | .exists_ A => Form.lcAtB (k + 1) A

theorem Form.lcAtB_iff : ∀ (k : Nat) (A : Form), Form.lcAtB k A = true ↔ Form.lcAt k A
  | _, .top       => by simp [Form.lcAtB, Form.lcAt]
  | _, .bot       => by simp [Form.lcAtB, Form.lcAt]
  | k, .pred _ ts => by simp [Form.lcAtB, Form.lcAt, Tm.lcAtListB_iff k ts]
  | k, .and A B   => by simp [Form.lcAtB, Form.lcAt, Form.lcAtB_iff k A, Form.lcAtB_iff k B]
  | k, .or A B    => by simp [Form.lcAtB, Form.lcAt, Form.lcAtB_iff k A, Form.lcAtB_iff k B]
  | k, .imp A B   => by simp [Form.lcAtB, Form.lcAt, Form.lcAtB_iff k A, Form.lcAtB_iff k B]
  | k, .circ _ A  => by simp [Form.lcAtB, Form.lcAt, Form.lcAtB_iff k A]
  | k, .forall_ A => by simp [Form.lcAtB, Form.lcAt, Form.lcAtB_iff (k + 1) A]
  | k, .exists_ A => by simp [Form.lcAtB, Form.lcAt, Form.lcAtB_iff (k + 1) A]

instance Form.decLcAt (k : Nat) (A : Form) : Decidable (Form.lcAt k A) :=
  decidable_of_iff _ (Form.lcAtB_iff k A)

/-! ## Closing removes the name

`allI`'s freshness condition mentions the formula, but inference chooses the
eigenvariable *before* the formula is known.  This is what closes that gap:
whatever `C` was, `a` does not occur free in `closeAt k a C`. -/

mutual
theorem Tm.not_mem_fv_closeAt (k : Nat) (a : String) :
    ∀ t : Tm, a ∉ (Tm.closeAt k a t).fv
  | .bvar _  => by simp [Tm.closeAt, Tm.fv]
  | .fvar x  => by
      by_cases hx : x = a
      · subst hx; simp [Tm.closeAt, Tm.fv]
      · simp [Tm.closeAt, Tm.fv, hx]; exact fun h => hx h.symm
  | .fn _ ts => by
      simpa [Tm.closeAt, Tm.fv] using Tm.not_mem_fvList_closeAtList k a ts
theorem Tm.not_mem_fvList_closeAtList (k : Nat) (a : String) :
    ∀ ts : List Tm, a ∉ Tm.fvList (Tm.closeAtList k a ts)
  | []      => by simp [Tm.closeAtList, Tm.fvList]
  | t :: ts => by
      simp only [Tm.closeAtList, Tm.fvList, List.mem_append, not_or]
      exact ⟨Tm.not_mem_fv_closeAt k a t, Tm.not_mem_fvList_closeAtList k a ts⟩
end

theorem Form.not_mem_fv_closeAt (a : String) :
    ∀ (k : Nat) (A : Form), a ∉ (Form.closeAt k a A).fv
  | _, .top       => by simp [Form.closeAt, Form.fv]
  | _, .bot       => by simp [Form.closeAt, Form.fv]
  | k, .pred _ ts => by
      simpa [Form.closeAt, Form.fv] using Tm.not_mem_fvList_closeAtList k a ts
  | k, .and A B   => by
      simp only [Form.closeAt, Form.fv, List.mem_append, not_or]
      exact ⟨Form.not_mem_fv_closeAt a k A, Form.not_mem_fv_closeAt a k B⟩
  | k, .or A B    => by
      simp only [Form.closeAt, Form.fv, List.mem_append, not_or]
      exact ⟨Form.not_mem_fv_closeAt a k A, Form.not_mem_fv_closeAt a k B⟩
  | k, .imp A B   => by
      simp only [Form.closeAt, Form.fv, List.mem_append, not_or]
      exact ⟨Form.not_mem_fv_closeAt a k A, Form.not_mem_fv_closeAt a k B⟩
  | k, .circ _ A  => Form.not_mem_fv_closeAt a k A
  | k, .forall_ A => Form.not_mem_fv_closeAt a (k + 1) A
  | k, .exists_ A => Form.not_mem_fv_closeAt a (k + 1) A

/-- The form the `∀` case of inference needs. -/
theorem Form.not_mem_fv_closeWith (a : String) (C : Form) :
    a ∉ (Form.closeWith a C).fv :=
  Form.not_mem_fv_closeAt a 0 C

/-! ## Opening lowers the bound

Every rule hands its premises an opened term, so local closedness has to travel
with it.  Opening an individual lowers the bound by one. -/

mutual
theorem Tm.lcAt_mono : ∀ {k k' : Nat}, k ≤ k' → ∀ (t : Tm), Tm.lcAt k t → Tm.lcAt k' t
  | _, _, hk, .bvar i, h => by
      have : i < _ := h
      show i < _
      omega
  | _, _, _,  .fvar _, _ => trivial
  | _, _, hk, .fn _ ts, h => Tm.lcAtList_mono hk ts h
theorem Tm.lcAtList_mono : ∀ {k k' : Nat}, k ≤ k' →
    ∀ (ts : List Tm), Tm.lcAtList k ts → Tm.lcAtList k' ts
  | _, _, _,  [],      _ => trivial
  | _, _, hk, _ :: ts, h => ⟨Tm.lcAt_mono hk _ h.1, Tm.lcAtList_mono hk ts h.2⟩
end

mutual
theorem Tm.lcAt_openAt : ∀ (k : Nat) (u : Tm), Tm.lcAt k u →
    ∀ (t : Tm), Tm.lcAt (k + 1) t → Tm.lcAt k (Tm.openAt k u t)
  | k, u, hu, .bvar i, h => by
      by_cases hi : i = k
      · subst hi; simpa [Tm.openAt] using hu
      · have h' : i < k + 1 := h
        simp only [Tm.openAt, if_neg hi]
        show i < k
        omega
  | _, _, _,  .fvar _, _ => trivial
  | k, u, hu, .fn _ ts, h => Tm.lcAtList_openAtList k u hu ts h
theorem Tm.lcAtList_openAtList : ∀ (k : Nat) (u : Tm), Tm.lcAt k u →
    ∀ (ts : List Tm), Tm.lcAtList (k + 1) ts → Tm.lcAtList k (Tm.openAtList k u ts)
  | _, _, _,  [],      _ => trivial
  | k, u, hu, _ :: ts, h =>
      ⟨Tm.lcAt_openAt k u hu _ h.1, Tm.lcAtList_openAtList k u hu ts h.2⟩
end

theorem Form.lcAt_openAt : ∀ (A : Form) (k : Nat) (u : Tm), Tm.lcAt k u →
    Form.lcAt (k + 1) A → Form.lcAt k (Form.openAt k u A) := by
  intro A
  induction A with
  | top | bot => intro _ _ _ _; trivial
  | pred _ ts => intro k u hu h; exact Tm.lcAtList_openAtList k u hu ts h
  | and A B ihM ihN | or A B ihM ihN | imp A B ihM ihN =>
      intro k u hu h; exact ⟨ihM k u hu h.1, ihN k u hu h.2⟩
  | circ _ A ih => intro k u hu h; exact ih k u hu h
  | forall_ A ih | exists_ A ih =>
      intro k u hu h; exact ih (k + 1) u (Tm.lcAt_mono (Nat.le_succ k) u hu) h

/-! ## Opening a proof term

Opening a proof variable leaves the individual indices alone; opening an
individual lowers their bound by one. -/

theorem Pf.lcI_openP (z : String) : ∀ (p : Pf) (j k : Nat),
    Pf.lcI k p → Pf.lcI k (Pf.openP j (.fvar z) p) := by
  intro p
  induction p with
  | bvar i => intro j _ _; by_cases h : i = j <;> simp [Pf.openP, h, Pf.lcI]
  | fvar _ | star => intro _ _ _; trivial
  | pair _ _ ih₁ ih₂ | app _ _ ih₁ ih₂ | letQ _ _ _ ih₁ ih₂ =>
      intro j k h; exact ⟨ih₁ _ k h.1, ih₂ _ k h.2⟩
  | fst _ ih | snd _ ih | inl _ ih | inr _ ih | lam _ ih | val _ _ ih =>
      intro j k h; exact ih _ k h
  | gen _ ih => intro j k h; exact ih j (k + 1) h
  | caseOr _ _ _ ih₁ ih₂ ih₃ =>
      intro j k h; exact ⟨ih₁ _ k h.1, ih₂ _ k h.2.1, ih₃ _ k h.2.2⟩
  | inst _ _ ih | pack _ _ ih => intro j k h; exact ⟨h.1, ih _ k h.2⟩
  | exf _ _ ih => intro j k h; exact ⟨h.1, ih _ k h.2⟩
  | caseEx _ _ ih₁ ih₂ => intro j k h; exact ⟨ih₁ _ k h.1, ih₂ _ (k + 1) h.2⟩

theorem Pf.lcI_openI : ∀ (p : Pf) (k : Nat) (u : Tm), Tm.lcAt k u →
    Pf.lcI (k + 1) p → Pf.lcI k (Pf.openI k u p) := by
  intro p
  induction p with
  | bvar _ | fvar _ | star => intro _ _ _ _; trivial
  | pair _ _ ih₁ ih₂ | app _ _ ih₁ ih₂ | letQ _ _ _ ih₁ ih₂ =>
      intro k u hu h; exact ⟨ih₁ k u hu h.1, ih₂ k u hu h.2⟩
  | fst _ ih | snd _ ih | inl _ ih | inr _ ih | lam _ ih | val _ _ ih =>
      intro k u hu h; exact ih k u hu h
  | caseOr _ _ _ ih₁ ih₂ ih₃ =>
      intro k u hu h; exact ⟨ih₁ k u hu h.1, ih₂ k u hu h.2.1, ih₃ k u hu h.2.2⟩
  | gen _ ih =>
      intro k u hu h; exact ih (k + 1) u (Tm.lcAt_mono (Nat.le_succ k) u hu) h
  | inst t _ ih | pack t _ ih =>
      intro k u hu h; exact ⟨Tm.lcAt_openAt k u hu t h.1, ih k u hu h.2⟩
  | exf A _ ih =>
      intro k u hu h; exact ⟨Form.lcAt_openAt A k u hu h.1, ih k u hu h.2⟩
  | caseEx _ _ ih₁ ih₂ =>
      intro k u hu h
      exact ⟨ih₁ k u hu h.1, ih₂ (k + 1) u (Tm.lcAt_mono (Nat.le_succ k) u hu) h.2⟩

end LaxLogic.QLL
