/-
# `LaxLogic.QLL.Complete1` — first-order completeness

The canonical model, now with the quantifiers.  Three things had to be settled
before it could be built, and each is visible in the definitions below.

**Worlds carry a reserve.**  A state is a saturated theory together with the
infinite set of names it has never mentioned (`LaxLogic.QLL.Saturate`).  The
universal-falsity case needs a genuinely new parameter — ω-completeness fails,
so no term already present will do — and that is what the reserve supplies.
Successors spend one name and inherit the rest, which is why the domains
*increase*: `Dom w` is the terms avoiding `w`'s reserve, and a successor's
reserve is smaller.

**The valuation cannot be the identity.**  `Assign` asks that every name denote
an element of the *initial* world's domain, and reserved names are precisely the
ones excluded from it.  So variables are interpreted by `vnm x = x ++ "z"`,
which is injective and lands outside every reserve — reserved names are runs of
`w`.  Injectivity is what the atomic case needs: two names must not be
identified, or `P(r)` and `P(z)` would have to be validated together.

**The induction is on size, not on structure.**  `A⟨t⟩` is not a subformula of
`∀x. A`, but it has the same size.
-/
import LaxLogic.QLL.Saturate

namespace LaxLogic.QLL

/-! ## Size

Opening does not change it, which is what lets the quantifier cases recurse. -/

/-- The number of connectives and binders. -/
def Form.size : Form → Nat
  | .top | .bot | .pred _ _ => 0
  | .and A B | .or A B | .imp A B => A.size + B.size + 1
  | .circ _ A | .forall_ A | .exists_ A => A.size + 1

theorem Form.size_openAt (t : Tm) : ∀ (A : Form) (k : Nat), (A.openAt k t).size = A.size := by
  intro A
  induction A with
  | top | bot | pred _ _ => intro _; rfl
  | and _ _ ih₁ ih₂ | or _ _ ih₁ ih₂ | imp _ _ ih₁ ih₂ =>
      intro k; simp [Form.openAt, Form.size, ih₁ k, ih₂ k]
  | circ _ _ ih => intro k; simp [Form.openAt, Form.size, ih k]
  | forall_ _ ih | exists_ _ ih => intro k; simp [Form.openAt, Form.size, ih (k + 1)]

theorem Form.size_openWith (a : String) (A : Form) : (A.openWith a).size = A.size :=
  Form.size_openAt (.fvar a) A 0

/-! ## Names for variables

`vnm` sends a variable to a name ending in `z`; reserved names are runs of `w`,
so the two never meet, and `vnm` is injective. -/

/-- The name a variable denotes in the canonical model. -/
def vnm (x : String) : String := x.push 'z'

theorem pnm_toList : ∀ i, (pnm i).toList = List.replicate (i + 1) 'w' := by
  intro i
  induction i with
  | zero => rfl
  | succ n ih => simp [pnm, ih, List.replicate_succ']

theorem vnm_inj : Function.Injective vnm := by
  intro x y h
  have : x.toList ++ ['z'] = y.toList ++ ['z'] := by
    simpa [vnm] using congrArg String.toList h
  exact String.ext (List.append_cancel_right this)

theorem vnm_ne_pnm (x : String) (i : Nat) : vnm x ≠ pnm i := by
  intro h
  have h' : x.toList ++ ['z'] = List.replicate (i + 1) 'w' := by
    rw [← pnm_toList]; simpa [vnm] using congrArg String.toList h
  have : 'z' ∈ List.replicate (i + 1) 'w' := by
    rw [← h']; simp
  exact absurd (List.eq_of_mem_replicate this) (by decide)

/-! ## Terms avoiding a set of names -/

/-- No name of the term is reserved. -/
def TmAvoids (R : Set String) (t : Tm) : Prop := ∀ x ∈ Tm.fv t, x ∉ R

theorem TmAvoids.mono {R R' : Set String} {t : Tm} (h : TmAvoids R t) (hs : R' ⊆ R) :
    TmAvoids R' t := fun x hx hm => h x hx (hs hm)

/-- `vnm` lands outside every reserve. -/
theorem vnm_notMem_allNames {f : Nat → Nat} (x : String) : vnm x ∉ allNames f := by
  rintro ⟨i, hi⟩
  exact vnm_ne_pnm x (f i) hi

theorem vnm_notMem_oddNames {f : Nat → Nat} (x : String) : vnm x ∉ oddNames f :=
  fun h => vnm_notMem_allNames x (unused_sub_allNames (oddNames_sub_unused 0 h))

/-! ## Renaming every name

The interpretation of a term under the canonical valuation. -/

mutual
/-- Apply a renaming to every free name. -/
def Tm.renAll (g : String → String) : Tm → Tm
  | .bvar i  => .bvar i
  | .fvar x  => .fvar (g x)
  | .fn f ts => .fn f (Tm.renAllList g ts)
/-- `renAll` on an argument list. -/
def Tm.renAllList (g : String → String) : List Tm → List Tm
  | []      => []
  | t :: ts => Tm.renAll g t :: Tm.renAllList g ts
end

mutual
theorem Tm.renAll_inj {g : String → String} (hg : Function.Injective g) :
    ∀ (t u : Tm), Tm.renAll g t = Tm.renAll g u → t = u
  | .bvar _,  .bvar _,  h => by simpa [Tm.renAll] using h
  | .bvar _,  .fvar _,  h => by simp [Tm.renAll] at h
  | .bvar _,  .fn _ _,  h => by simp [Tm.renAll] at h
  | .fvar _,  .bvar _,  h => by simp [Tm.renAll] at h
  | .fvar _,  .fn _ _,  h => by simp [Tm.renAll] at h
  | .fn _ _,  .bvar _,  h => by simp [Tm.renAll] at h
  | .fn _ _,  .fvar _,  h => by simp [Tm.renAll] at h
  | .fvar x,  .fvar y,  h => by
      have : g x = g y := by simpa [Tm.renAll] using h
      rw [hg this]
  | .fn f ts, .fn g' us, h => by
      have h' : f = g' ∧ Tm.renAllList g ts = Tm.renAllList g us := by
        simpa [Tm.renAll] using h
      rw [h'.1, Tm.renAllList_inj hg ts us h'.2]
theorem Tm.renAllList_inj {g : String → String} (hg : Function.Injective g) :
    ∀ (ts us : List Tm), Tm.renAllList g ts = Tm.renAllList g us → ts = us
  | [],      [],      _ => rfl
  | [],      _ :: _,  h => by simp [Tm.renAllList] at h
  | _ :: _,  [],      h => by simp [Tm.renAllList] at h
  | t :: ts, u :: us, h => by
      have h' : Tm.renAll g t = Tm.renAll g u ∧
          Tm.renAllList g ts = Tm.renAllList g us := by simpa [Tm.renAllList] using h
      rw [Tm.renAll_inj hg t u h'.1, Tm.renAllList_inj hg ts us h'.2]
end

end LaxLogic.QLL
