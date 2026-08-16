/-
# FRJ(G) — the calculus

Section 3 of Fiorentini–Ferrari (TOCL 21(3), 2020; arXiv:1804.06689),
Figure "The calculus FRJ(G)", transcribed rule by rule.

The judgment is an indexed inductive family with one constructor per
published rule and every side condition present as a field.  Nothing
here is invented: each constructor's docstring quotes the rule it
encodes.
-/
import FRJ.Basic

namespace FRJ

open Form

/-! ## Set operations used by the join rules

The joins take `n ≥ 1` premises, so unions and intersections range over
a nonempty finite index.  We index premises by `Fin (n+1)`.
-/

/-- `⋃_{1≤j≤n} f j`. -/
def unionAll {n : Nat} (f : Fin (n + 1) → List Form) : List Form :=
  (List.finRange (n + 1)).flatMap f

@[simp] theorem mem_unionAll {n : Nat} {f : Fin (n + 1) → List Form} {x : Form} :
    x ∈ unionAll f ↔ ∃ j, x ∈ f j := by
  simp [unionAll, List.mem_flatMap]

/-- `⋂_{1≤j≤n} f j`.  Defined by filtering the first component, which is
legitimate exactly because the index is nonempty. -/
def interAll {n : Nat} (f : Fin (n + 1) → List Form) : List Form :=
  (f 0).filter (fun x => decide (∀ j, x ∈ f j))

@[simp] theorem mem_interAll {n : Nat} {f : Fin (n + 1) → List Form} {x : Form} :
    x ∈ interAll f ↔ ∀ j, x ∈ f j := by
  simp only [interAll, List.mem_filter, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨h 0, h⟩⟩

/-- Membership test for the restriction operator. -/
def inRestrict (Υ : List Form) : Form → Bool
  | .imp A _ => decide (A ∈ Υ)
  | _ => false

/-- "Given a set of ⊃-formulas `Γ⊃` and a set of formulas `Υ`, let
`Γ⊃/Υ = { Y ⊃ Z ∈ Γ⊃ | Y ∈ Υ }`.  We call `Γ⊃/Υ` the *restriction* of
`Γ⊃` to `Υ`." -/
def restrict (X Υ : List Form) : List Form :=
  X.filter (fun f => inRestrict Υ f)

theorem mem_restrict {X Υ : List Form} {A B : Form} :
    Form.imp A B ∈ restrict X Υ ↔ (Form.imp A B ∈ X ∧ A ∈ Υ) := by
  simp [restrict, inRestrict, List.mem_filter]

theorem restrict_subset {X Υ : List Form} : restrict X Υ ⊆ X :=
  fun _ h => (List.mem_filter.mp h).1

/-! ## The conclusion contexts of the join rules

Named so that the `↦` relation of Sec. 3.1 and the calculus cannot drift
apart: both refer to these. -/

/-- `Υ = {A₁, …, Aₙ}`, the right formulas of the join's premises. -/
def upsilon {n : Nat} (rhs : Fin (n + 1) → Form) : List Form :=
  (List.finRange (n + 1)).map rhs

/-- The conclusion context of `⋈^At`:  `Σ^at, Θ^at \ {F}, Σ^imp, Θ^imp`. -/
def joinCtxAt {n : Nat} (stab th : Fin (n + 1) → List Form)
    (rhs : Fin (n + 1) → Form) (F : Form) : List Form :=
  unionAll (fun j => atPart (stab j)) ++
    rm (interAll (fun j => atPart (th j))) F ++
    unionAll (fun j => impPart (stab j)) ++
    restrict (interAll (fun j => impPart (th j))) (upsilon rhs)

/-- The conclusion context of `⋈^∨`:  `Σ^at, Θ^at, Σ^imp, Θ^imp`. -/
def joinCtxOr {n : Nat} (stab th : Fin (n + 1) → List Form)
    (rhs : Fin (n + 1) → Form) : List Form :=
  unionAll (fun j => atPart (stab j)) ++
    interAll (fun j => atPart (th j)) ++
    unionAll (fun j => impPart (stab j)) ++
    restrict (interAll (fun j => impPart (th j))) (upsilon rhs)

/-! ## The calculus

Two mutually inductive families, one per sequent form:

* `FRJr G Γ C` — derivations of the regular sequent `Γ ⇒ C`;
* `FRJi G Σ Θ C` — derivations of the irregular sequent `Σ ; Θ → C`.

The blanket side condition of the figure — "in the conclusion `σ` of each
rule, `Rhs(σ) ∈ Sf^R(G)`" — appears as a field `hgoal` on every
constructor.
-/

mutual

/-- Derivations of regular sequents `Γ ⇒ C`. -/
inductive FRJr (G : Form) : List Form → Form → Type
  /-- `Ax^R`:  `⊢ Ĝ_at \ {F} ⇒ F`,  `F ∈ Prime`. -/
  | axR (F : Form) (hF : F.isPrime) (hgoal : F ∈ sfR G) :
      FRJr G (rm (gAt G) F) F
  /-- `∧` (regular), `k = 1`:  from `Γ ⇒ A₁` infer `Γ ⇒ A₁ ∧ A₂`. -/
  | andR1 {Γ : List Form} {A₁ A₂ : Form}
      (d : FRJr G Γ A₁) (hgoal : Form.and A₁ A₂ ∈ sfR G) :
      FRJr G Γ (.and A₁ A₂)
  /-- `∧` (regular), `k = 2`:  from `Γ ⇒ A₂` infer `Γ ⇒ A₁ ∧ A₂`. -/
  | andR2 {Γ : List Form} {A₁ A₂ : Form}
      (d : FRJr G Γ A₂) (hgoal : Form.and A₁ A₂ ∈ sfR G) :
      FRJr G Γ (.and A₁ A₂)
  /-- `⊃∈` (regular):  from `Γ ⇒ B` infer `Γ ⇒ A ⊃ B`,  side `A ∈ Cl(Γ)`. -/
  | impIn {Γ : List Form} {A B : Form}
      (d : FRJr G Γ B) (hA : Clo Γ A) (hgoal : Form.imp A B ∈ sfR G) :
      FRJr G Γ (.imp A B)
  /-- `⋈^At`: from `n ≥ 1` irregular premises `σⱼ = Σⱼ ; Θⱼ → Aⱼ` infer
      `Σ^at, Θ^at \ {F}, Σ^imp, Θ^imp ⇒ F`, with side conditions
      (J1) `Σᵢ ⊆ Σⱼ ++ Θⱼ` for `i ≠ j`,
      (J2) `Y ⊃ Z ∈ Σ^imp` implies `Y ∈ Υ`, and
      `F ∈ Prime \ Σ^at`. -/
  | joinAt {n : Nat} {stab th : Fin (n + 1) → List Form}
      {rhs : Fin (n + 1) → Form} {F : Form}
      (prem : ∀ j, FRJi G (stab j) (th j) (rhs j))
      (hJ1 : ∀ i j, i ≠ j → stab i ⊆ stab j ++ th j)
      (hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (stab j)) →
        A ∈ upsilon rhs)
      (hF : F.isPrime) (hFnot : F ∉ unionAll (fun j => atPart (stab j)))
      (hgoal : F ∈ sfR G) :
      FRJr G (joinCtxAt stab th rhs F) F
  /-- `⋈^∨`: as `⋈^At`, but the conclusion's right formula is a
      `∨`-formula `C₁ ∨ C₂` with `{C₁,C₂} ⊆ Υ`, and `Θ^at` is kept whole. -/
  | joinOr {n : Nat} {stab th : Fin (n + 1) → List Form}
      {rhs : Fin (n + 1) → Form} {C₁ C₂ : Form}
      (prem : ∀ j, FRJi G (stab j) (th j) (rhs j))
      (hJ1 : ∀ i j, i ≠ j → stab i ⊆ stab j ++ th j)
      (hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (stab j)) →
        A ∈ upsilon rhs)
      (hC : C₁ ∈ upsilon rhs ∧ C₂ ∈ upsilon rhs)
      (hgoal : Form.or C₁ C₂ ∈ sfR G) :
      FRJr G (joinCtxOr stab th rhs) (.or C₁ C₂)

/-- Derivations of irregular sequents `Σ ; Θ → C`. -/
inductive FRJi (G : Form) : List Form → List Form → Form → Type
  /-- `Ax^I`:  `⊢ [] ; Ĝ_at \ {F}, Ĝ_imp → F`,  `F ∈ Prime`. -/
  | axI (F : Form) (hF : F.isPrime) (hgoal : F ∈ sfR G) :
      FRJi G [] (nf G ((rm (gAt G) F) ++ gImp G)) F
  /-- `∧` (irregular), `k = 1`. -/
  | andI1 {St Th : List Form} {A₁ A₂ : Form}
      (d : FRJi G St Th A₁) (hgoal : Form.and A₁ A₂ ∈ sfR G) :
      FRJi G St Th (.and A₁ A₂)
  /-- `∧` (irregular), `k = 2`. -/
  | andI2 {St Th : List Form} {A₁ A₂ : Form}
      (d : FRJi G St Th A₂) (hgoal : Form.and A₁ A₂ ∈ sfR G) :
      FRJi G St Th (.and A₁ A₂)
  /-- `∨`: from `Σ₁ ; Θ₁ → C₁` and `Σ₂ ; Θ₂ → C₂` infer
      `Σ₁, Σ₂ ; Θ₁ ∩ Θ₂ → C₁ ∨ C₂`, side conditions
      `Σ₁ ⊆ Σ₂ ++ Θ₂` and `Σ₂ ⊆ Σ₁ ++ Θ₁`. -/
  | orI {St₁ Th₁ St₂ Th₂ : List Form} {C₁ C₂ : Form}
      (d₁ : FRJi G St₁ Th₁ C₁) (d₂ : FRJi G St₂ Th₂ C₂)
      (h₁ : St₁ ⊆ St₂ ++ Th₂) (h₂ : St₂ ⊆ St₁ ++ Th₁)
      (hgoal : Form.or C₁ C₂ ∈ sfR G) :
      FRJi G (St₁ ++ St₂) (nf G (cap Th₁ Th₂)) (.or C₁ C₂)
  /-- `⊃∈` (irregular): from `Σ ; Θ, Λ → B` infer `Σ, Λ ; Θ → A ⊃ B`,
      side conditions `Θ ∩ Λ = ∅` and `A ∈ Cl(Σ ++ Λ)`. -/
  | impInI {St Th Lam : List Form} {A B : Form}
      (d : FRJi G St (nf G (Th ++ Lam)) B)
      (hdisj : cap Th Lam = []) (hA : Clo (nf G (St ++ Lam)) A)
      (hgoal : Form.imp A B ∈ sfR G) :
      FRJi G (nf G (St ++ Lam)) (nf G Th) (.imp A B)
  /-- `⊃∉`: from the REGULAR premise `Γ ⇒ B` infer `[] ; Θ → A ⊃ B`,
      side conditions `Θ ⊆ Cl(Γ) ∩ Ĝ` and `A ∈ Cl(Γ) \ Cl(Θ)`. -/
  | impNotIn {Γ Th : List Form} {A B : Form}
      (d : FRJr G Γ B)
      (hTh : ∀ X ∈ Th, Clo Γ X ∧ X ∈ gHat G)
      (hA : Clo Γ A) (hAnot : ¬ Clo Th A)
      (hgoal : Form.imp A B ∈ sfR G) :
      FRJi G [] Th (.imp A B)

end

/-! ## Provability

"`Ｄ` is an `FRJ(G)`-derivation of `G` iff there exists a (possibly
empty) set of formulas `Γ` such that `Ｄ` is an `FRJ(G)`-derivation of
`Γ ⇒ G`."
-/

/-- `⊢_{FRJ(G)} G`: the goal formula `G` is provable in `FRJ(G)`. -/
def Provable (G : Form) : Prop := ∃ Γ : List Form, Nonempty (FRJr G Γ G)

end FRJ
