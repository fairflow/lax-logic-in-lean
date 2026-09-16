/-
# `LaxLogic.QLL.Countable` — the formulas can be enumerated

The first-order completeness proof needs an ω-schedule: a surjection `ℕ → Form`
along which every existential in the limit theory eventually receives a witness.
That is the *only* thing this file is for, and it is needed because Zorn cannot
supply it — see `LaxLogic.QLL.Saturate`.

Nothing here is available off the shelf.  Mathlib has no `Countable String`
(strings are a core type it never gives a countability instance), so the chain
`Char → ℕ`, `String → List ℕ`, `Form → ℕ` is built by hand.  The numbering is a
plain tagged pairing; injectivity is the content.
-/
import Mathlib.Logic.Equiv.List
import LaxLogic.QLL.Syntax

namespace LaxLogic.QLL

/-! ## Strings

`Char.toNat` is injective because `Char` is a `UInt32` carrying a proof, and
`String` is a `List Char`; the rest is `Encodable (List ℕ)`. -/

/-- A Gödel number for a string. -/
def strCode (s : String) : Nat := Encodable.encode (s.toList.map Char.toNat)

theorem char_toNat_inj : Function.Injective Char.toNat :=
  fun _ _ h => Char.ext (UInt32.toNat_inj.mp h)

theorem strCode_inj : Function.Injective strCode := by
  intro s t h
  have h1 : s.toList.map Char.toNat = t.toList.map Char.toNat :=
    Encodable.encode_injective h
  exact String.ext (List.map_injective_iff.mpr char_toNat_inj h1)

@[simp] theorem strCode_eq_iff {x y : String} : strCode x = strCode y ↔ x = y :=
  strCode_inj.eq_iff

/-! ## Terms -/

/-! A Gödel number for a term.  Tag in the first component, payload in the
second; `Nat.pair` is injective, so distinct tags separate the constructors. -/
mutual
def Tm.code : Tm → Nat
  | .bvar i  => Nat.pair 0 i
  | .fvar x  => Nat.pair 1 (strCode x)
  | .fn f ts => Nat.pair 2 (Nat.pair (strCode f) (Tm.codeList ts))
def Tm.codeList : List Tm → Nat
  | []      => Nat.pair 0 0
  | t :: ts => Nat.pair 1 (Nat.pair (Tm.code t) (Tm.codeList ts))
end

mutual
theorem Tm.code_inj : ∀ (t t' : Tm), Tm.code t = Tm.code t' → t = t'
  | .bvar _,  .bvar _,   h => by simpa [Tm.code] using h
  | .bvar _,  .fvar _,   h => by simp [Tm.code] at h
  | .bvar _,  .fn _ _,   h => by simp [Tm.code] at h
  | .fvar _,  .bvar _,   h => by simp [Tm.code] at h
  | .fvar _,  .fn _ _,   h => by simp [Tm.code] at h
  | .fn _ _,  .bvar _,   h => by simp [Tm.code] at h
  | .fn _ _,  .fvar _,   h => by simp [Tm.code] at h
  | .fvar x,  .fvar y,   h => by
      have : strCode x = strCode y := by simpa [Tm.code] using h
      rw [strCode_inj this]
  | .fn f ts, .fn g us,  h => by
      have h' : strCode f = strCode g ∧ Tm.codeList ts = Tm.codeList us := by
        simpa [Tm.code] using h
      rw [strCode_inj h'.1, Tm.codeList_inj ts us h'.2]
theorem Tm.codeList_inj : ∀ (ts us : List Tm), Tm.codeList ts = Tm.codeList us → ts = us
  | [],      [],      _ => rfl
  | [],      _ :: _,  h => by simp [Tm.codeList] at h
  | _ :: _,  [],      h => by simp [Tm.codeList] at h
  | t :: ts, u :: us, h => by
      have h' : Tm.code t = Tm.code u ∧ Tm.codeList ts = Tm.codeList us := by
        simpa [Tm.codeList] using h
      rw [Tm.code_inj t u h'.1, Tm.codeList_inj ts us h'.2]
end

@[simp] theorem Tm.code_eq_iff {t u : Tm} : Tm.code t = Tm.code u ↔ t = u :=
  ⟨Tm.code_inj t u, fun h => by rw [h]⟩

@[simp] theorem Tm.codeList_eq_iff {ts us : List Tm} :
    Tm.codeList ts = Tm.codeList us ↔ ts = us :=
  ⟨Tm.codeList_inj ts us, fun h => by rw [h]⟩

/-! ## Formulas -/

/-- A Gödel number for a modality. -/
def Q.code : Q → Nat
  | .all => 0
  | .ex  => 1

@[simp] theorem Q.code_eq_iff {q r : Q} : Q.code q = Q.code r ↔ q = r := by
  cases q <;> cases r <;> simp [Q.code]

/-- A Gödel number for a formula. -/
def Form.code : Form → Nat
  | .top       => Nat.pair 0 0
  | .bot       => Nat.pair 1 0
  | .pred P ts => Nat.pair 2 (Nat.pair (strCode P) (Tm.codeList ts))
  | .and A B   => Nat.pair 3 (Nat.pair A.code B.code)
  | .or A B    => Nat.pair 4 (Nat.pair A.code B.code)
  | .imp A B   => Nat.pair 5 (Nat.pair A.code B.code)
  | .circ q A  => Nat.pair 6 (Nat.pair q.code A.code)
  | .forall_ A => Nat.pair 7 A.code
  | .exists_ A => Nat.pair 8 A.code

theorem Form.code_inj' : ∀ (A B : Form), Form.code A = Form.code B → A = B := by
  intro A
  induction A with
  | top | bot | pred _ _ => intro B h; cases B <;> simp_all [Form.code]
  | and A₁ A₂ ih₁ ih₂ | or A₁ A₂ ih₁ ih₂ | imp A₁ A₂ ih₁ ih₂ =>
      intro B h
      cases B <;> simp [Form.code] at h
      rw [ih₁ _ h.1, ih₂ _ h.2]
  | circ q A₁ ih =>
      intro B h
      cases B <;> simp [Form.code] at h
      rw [ih _ h.2, h.1]
  | forall_ A₁ ih | exists_ A₁ ih =>
      intro B h
      cases B <;> simp [Form.code] at h
      rw [ih _ h]

theorem Form.code_inj : Function.Injective Form.code := fun {_ _} h => Form.code_inj' _ _ h

instance : Countable Form := Form.code_inj.countable

/-! ## The schedule

A surjection, obtained from the injection by choice.  `Form.top` is the
value on numbers that are not codes; nothing depends on which value that is. -/

open Classical in
/-- The `n`-th formula.  Every formula appears — `enum_surj`. -/
noncomputable def enum (n : Nat) : Form :=
  if h : ∃ A : Form, Form.code A = n then h.choose else .top

theorem enum_surj (A : Form) : ∃ n, enum n = A := by
  refine ⟨Form.code A, ?_⟩
  have h : ∃ B : Form, Form.code B = Form.code A := ⟨A, rfl⟩
  simp only [enum, dif_pos h]
  exact Form.code_inj h.choose_spec

end LaxLogic.QLL
