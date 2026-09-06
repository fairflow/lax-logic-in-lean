/-
# `LaxLogic.QLL.Lc` — local closedness

A de Bruijn representation admits junk: `pred "P" [Tm.bvar 5]` is a perfectly
good `Form` and is not a formula of the object language.  `lcAt k` carves the
real syntax out of the raw datatype — no index at or above `k` occurs loose.

Only the **individual** index needs tracking.  A formula's well-formedness
cannot depend on proof-variable indices, and opening a proof binder cannot
create a loose individual, so `Pf.lcI` tracks one index and not two.  The
checker already rejects loose *proof* indices at runtime (`Err.looseIndex`);
this layer is about the other sort.

Wanted for three things, only one of which is the soundness proof:

* the open/close roundtrip `openAt k (fvar a) (closeAt k a A) = A`, which
  `infer`'s `∀` case needs and which holds only for locally closed `A`;
* `⊨` and `|M|` (Figs. 3 and 4), defined by recursion on `Form`, which have no
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
  | .and M N   => Form.lcAt k M ∧ Form.lcAt k N
  | .or M N    => Form.lcAt k M ∧ Form.lcAt k N
  | .imp M N   => Form.lcAt k M ∧ Form.lcAt k N
  | .circ _ M  => Form.lcAt k M
  | .forall_ M => Form.lcAt (k + 1) M
  | .exists_ M => Form.lcAt (k + 1) M

/-- A closed formula. -/
abbrev Form.lc (M : Form) : Prop := Form.lcAt 0 M

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
  | .exf M p      => Form.lcAt k M ∧ Pf.lcI k p

/-- Every formula in the context is closed. -/
def Ctx.lc : Ctx → Prop
  | []          => True
  | (_, M) :: Γ => Form.lc M ∧ Ctx.lc Γ

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
    ∀ (k : Nat) (M : Form), Form.lcAt k M →
      Form.openAt k (.fvar a) (Form.closeAt k a M) = M
  | _, .top,       _ => rfl
  | _, .bot,       _ => rfl
  | k, .pred _ ts, h => by
      simp only [Form.lcAt] at h
      simp only [Form.closeAt, Form.openAt, Tm.openAtList_closeAtList k a ts h]
  | k, .and M N,   h => by
      simp only [Form.lcAt] at h
      simp only [Form.closeAt, Form.openAt,
        Form.openAt_closeAt a k M h.1, Form.openAt_closeAt a k N h.2]
  | k, .or M N,    h => by
      simp only [Form.lcAt] at h
      simp only [Form.closeAt, Form.openAt,
        Form.openAt_closeAt a k M h.1, Form.openAt_closeAt a k N h.2]
  | k, .imp M N,   h => by
      simp only [Form.lcAt] at h
      simp only [Form.closeAt, Form.openAt,
        Form.openAt_closeAt a k M h.1, Form.openAt_closeAt a k N h.2]
  | k, .circ _ M,  h => by
      simp only [Form.lcAt] at h
      simp only [Form.closeAt, Form.openAt, Form.openAt_closeAt a k M h]
  | k, .forall_ M, h => by
      simp only [Form.lcAt] at h
      simp only [Form.closeAt, Form.openAt, Form.openAt_closeAt a (k + 1) M h]
  | k, .exists_ M, h => by
      simp only [Form.lcAt] at h
      simp only [Form.closeAt, Form.openAt, Form.openAt_closeAt a (k + 1) M h]

/-- The form the `∀` case of `infer` needs. -/
theorem Form.openWith_closeWith {A : Form} (a : String) (h : Form.lc A) :
    Form.openWith a (Form.closeWith a A) = A :=
  Form.openAt_closeAt a 0 A h

end LaxLogic.QLL
