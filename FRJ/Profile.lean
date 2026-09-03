/-
# The Profile Lemma

Every FRJ(◯) join rule takes a premise family

    prem : ∀ j : Fin (n+1), FRJi G (stab j) (th j) (rhs j)

and the search enumerates such families.  Measured 2026-08-21, that
enumeration is where the cost is: on bank cell `cAnd_8_11` the engine
materialises 14748 families in one round out of a 61-row database, with
families capped at arity 3, and the cap bound 119 of 119 negative results.

This file proves that the enumeration is a REPRESENTATION artefact.  Every
join rule's conclusion context, and every side condition, is a function of
four AGGREGATES of the family:

    Σ := ⋃ⱼ stab j     Θ := ⋂ⱼ th j     M := ⋂ⱼ (stab j ++ th j)     Υ := { rhs j }

and — this is the part that makes merging safe — whether a further row may
JOIN the family is also a function of `(Σ, M)` alone.  So two families with
the same profile produce the same conclusion and admit exactly the same
extensions, and a search may keep one witness per profile instead of
enumerating every family.

Design note: `docs/frj-profile-search.md`.

Everything is stated at MEMBERSHIP level (`≐`), which is exactly the
strength the calculus needs: the join rules conclude
`(hΓ : Γ' ≐ joinCtxAt stab th rhs F)`, so the context is only ever
determined up to `CtxEq` in the first place.
-/
import FRJ.Calculus
-- Explicit since 2026-09-03: uses `Fin.cons` and its lemmas; the
-- foundation modules no longer re-export Mathlib.  OUTSIDE the runtime
-- closure of `lake exe pll`, so the decider pays nothing.
import Mathlib

namespace FRJ
namespace Profile

/-! ## 1. Congruence: everything the conclusion contexts are built from
respects `≐`.

`atPart`, `impPart`, `circPart`, `rm`, `restrict`, `restrictC` and
`restrictP` are all `List.filter` by a predicate that inspects the FORMULA
(and fixed parameters), never the list.  One lemma covers them all. -/

theorem filter_ctxEq {X X' : List Form} (h : X ≐ X') (p : Form → Bool) :
    X.filter p ≐ X'.filter p := fun x => by
  simp only [List.mem_filter]
  exact ⟨fun hx => ⟨(h x).mp hx.1, hx.2⟩, fun hx => ⟨(h x).mpr hx.1, hx.2⟩⟩

theorem append_ctxEq {a a' b b' : List Form} (ha : a ≐ a') (hb : b ≐ b') :
    a ++ b ≐ a' ++ b' := fun x => by
  simp only [List.mem_append]
  exact or_congr (ha x) (hb x)

theorem atPart_ctxEq {X X' : List Form} (h : X ≐ X') : atPart X ≐ atPart X' :=
  filter_ctxEq h _
theorem impPart_ctxEq {X X' : List Form} (h : X ≐ X') : impPart X ≐ impPart X' :=
  filter_ctxEq h _
theorem circPart_ctxEq {X X' : List Form} (h : X ≐ X') : circPart X ≐ circPart X' :=
  filter_ctxEq h _
theorem rm_ctxEq {X X' : List Form} (h : X ≐ X') (F : Form) : rm X F ≐ rm X' F :=
  filter_ctxEq h _
theorem restrict_ctxEq {X X' : List Form} (h : X ≐ X') (U : List Form) :
    restrict X U ≐ restrict X' U := filter_ctxEq h _
theorem restrictC_ctxEq {k : Nat} {X X' : List Form} (h : X ≐ X')
    (Δs : Fin (k+1) → List Form) : restrictC X Δs ≐ restrictC X' Δs :=
  filter_ctxEq h _
theorem restrictP_ctxEq {k : Nat} {X X' : List Form} (h : X ≐ X')
    (Δs : Fin (k+1) → List Form) : restrictP X Δs ≐ restrictP X' Δs :=
  filter_ctxEq h _

/-! ## 2. A formula filter commutes with `⋃` and `⋂`

This is why the SIX zone aggregates
`⋃ atPart(stab j)`, `⋂ atPart(th j)`, `⋃ impPart(stab j)`, … collapse to
the two sets `Σ` and `Θ`. -/

theorem filter_unionAll {n : Nat} (p : Form → Bool) (f : Fin (n+1) → List Form) :
    unionAll (fun j => (f j).filter p) ≐ (unionAll f).filter p := fun x => by
  simp only [mem_unionAll, List.mem_filter]
  exact ⟨fun ⟨j, hj, hp⟩ => ⟨⟨j, hj⟩, hp⟩, fun ⟨⟨j, hj⟩, hp⟩ => ⟨j, hj, hp⟩⟩

theorem filter_interAll {n : Nat} (p : Form → Bool) (f : Fin (n+1) → List Form) :
    interAll (fun j => (f j).filter p) ≐ (interAll f).filter p := fun x => by
  simp only [mem_interAll, List.mem_filter]
  exact ⟨fun hall => ⟨fun j => (hall j).1, (hall 0).2⟩, fun h j => ⟨h.1 j, h.2⟩⟩

/-! ### The six zone collapses, named -/

theorem atPart_unionAll {n : Nat} (f : Fin (n+1) → List Form) :
    unionAll (fun j => atPart (f j)) ≐ atPart (unionAll f) := filter_unionAll _ f
theorem impPart_unionAll {n : Nat} (f : Fin (n+1) → List Form) :
    unionAll (fun j => impPart (f j)) ≐ impPart (unionAll f) := filter_unionAll _ f
theorem circPart_unionAll {n : Nat} (f : Fin (n+1) → List Form) :
    unionAll (fun j => circPart (f j)) ≐ circPart (unionAll f) := filter_unionAll _ f
theorem atPart_interAll {n : Nat} (f : Fin (n+1) → List Form) :
    interAll (fun j => atPart (f j)) ≐ atPart (interAll f) := filter_interAll _ f
theorem impPart_interAll {n : Nat} (f : Fin (n+1) → List Form) :
    interAll (fun j => impPart (f j)) ≐ impPart (interAll f) := filter_interAll _ f
theorem circPart_interAll {n : Nat} (f : Fin (n+1) → List Form) :
    interAll (fun j => circPart (f j)) ≐ circPart (interAll f) := filter_interAll _ f

/-! ## 3. The profile

`Σ` and `Θ` are `unionAll stab` and `interAll th`.  `Υ` is `upsilon rhs`.
`M` is the new one: the aggregate that decides who may JOIN. -/

/-- `M := ⋂ⱼ (Σⱼ ++ Θⱼ)`.  A row may extend the family exactly when its
stable zone lands inside this. -/
def mAll {n : Nat} (stab th : Fin (n+1) → List Form) : List Form :=
  interAll (fun j => stab j ++ th j)

@[simp] theorem mem_mAll {n : Nat} {stab th : Fin (n+1) → List Form} {x : Form} :
    x ∈ mAll stab th ↔ ∀ j, x ∈ stab j ++ th j := mem_interAll

/-- The profile of a family: everything any join rule can see. -/
structure Prof where
  sig : List Form   -- Σ
  the : List Form   -- Θ
  mid : List Form   -- M
  ups : List Form   -- Υ

def profOf {n : Nat} (stab th : Fin (n+1) → List Form) (rhs : Fin (n+1) → Form) : Prof :=
  ⟨unionAll stab, interAll th, mAll stab th, upsilon rhs⟩

/-! ## 4. The conclusion contexts factor through the profile -/

/-- `joinCtxAt`, written in terms of `Σ`, `Θ`, `Υ` alone. -/
def ctxAt (S T U : List Form) (F : Form) : List Form :=
  atPart S ++ rm (atPart T) F ++ impPart S ++ restrict (impPart T) U

/-- `joinCtxOr`, likewise. -/
def ctxOr (S T U : List Form) : List Form :=
  atPart S ++ atPart T ++ impPart S ++ restrict (impPart T) U

/-- `joinCtxCircP`, likewise. -/
def ctxCircP {k : Nat} (S T : List Form) (Δs : Fin (k+1) → List Form) : List Form :=
  circPart S ++ restrictC (circPart T) Δs

/-- `joinCtxCircF`, likewise. -/
def ctxCircF (S T : List Form) : List Form :=
  circPart S ++ circPart T

theorem joinCtxAt_prof {n : Nat} (stab th : Fin (n+1) → List Form)
    (rhs : Fin (n+1) → Form) (F : Form) :
    joinCtxAt stab th rhs F
      ≐ ctxAt (unionAll stab) (interAll th) (upsilon rhs) F :=
  append_ctxEq
    (append_ctxEq
      (append_ctxEq (atPart_unionAll stab) (rm_ctxEq (atPart_interAll th) F))
      (impPart_unionAll stab))
    (restrict_ctxEq (impPart_interAll th) (upsilon rhs))

theorem joinCtxOr_prof {n : Nat} (stab th : Fin (n+1) → List Form)
    (rhs : Fin (n+1) → Form) :
    joinCtxOr stab th rhs ≐ ctxOr (unionAll stab) (interAll th) (upsilon rhs) :=
  append_ctxEq
    (append_ctxEq
      (append_ctxEq (atPart_unionAll stab) (atPart_interAll th))
      (impPart_unionAll stab))
    (restrict_ctxEq (impPart_interAll th) (upsilon rhs))

theorem joinCtxCircP_prof {n k : Nat} (stab th : Fin (n+1) → List Form)
    (Δs : Fin (k+1) → List Form) :
    joinCtxCircP stab th Δs ≐ ctxCircP (unionAll stab) (interAll th) Δs :=
  append_ctxEq (circPart_unionAll stab)
    (restrictC_ctxEq (circPart_interAll th) Δs)

theorem joinCtxCircF_prof {n : Nat} (stab th : Fin (n+1) → List Form) :
    joinCtxCircF stab th ≐ ctxCircF (unionAll stab) (interAll th) :=
  append_ctxEq (circPart_unionAll stab) (circPart_interAll th)

/-! ### The composite contexts -/

theorem joinCtxAtF_prof {n : Nat} (stab th : Fin (n+1) → List Form)
    (rhs : Fin (n+1) → Form) (F : Form) :
    joinCtxAtF stab th rhs F
      ≐ ctxAt (unionAll stab) (interAll th) (upsilon rhs) F
        ++ ctxCircF (unionAll stab) (interAll th) :=
  append_ctxEq (joinCtxAt_prof stab th rhs F) (joinCtxCircF_prof stab th)

theorem joinCtxOrF_prof {n : Nat} (stab th : Fin (n+1) → List Form)
    (rhs : Fin (n+1) → Form) :
    joinCtxOrF stab th rhs
      ≐ ctxOr (unionAll stab) (interAll th) (upsilon rhs)
        ++ ctxCircF (unionAll stab) (interAll th) :=
  append_ctxEq (joinCtxOr_prof stab th rhs) (joinCtxCircF_prof stab th)

theorem joinCtxAtP_prof {n k : Nat} (stab th : Fin (n+1) → List Form)
    (rhs : Fin (n+1) → Form) (F : Form) (Δs : Fin (k+1) → List Form) :
    joinCtxAtP stab th rhs F Δs
      ≐ restrictP (ctxAt (unionAll stab) (interAll th) (upsilon rhs) F
                    ++ ctxCircP (unionAll stab) (interAll th) Δs) Δs :=
  restrictP_ctxEq
    (append_ctxEq (joinCtxAt_prof stab th rhs F) (joinCtxCircP_prof stab th Δs)) Δs

theorem joinCtxOrP_prof {n k : Nat} (stab th : Fin (n+1) → List Form)
    (rhs : Fin (n+1) → Form) (Δs : Fin (k+1) → List Form) :
    joinCtxOrP stab th rhs Δs
      ≐ restrictP (ctxOr (unionAll stab) (interAll th) (upsilon rhs)
                    ++ ctxCircP (unionAll stab) (interAll th) Δs) Δs :=
  restrictP_ctxEq
    (append_ctxEq (joinCtxOr_prof stab th rhs) (joinCtxCircP_prof stab th Δs)) Δs

/-! ## 5. The side conditions factor through the profile too

Each join rule's premises constrain the family only through `Σ`, `Υ` and
the promise family `Δ⃗`.  Nothing reads the arity, the ordering, or which
particular rows realise the aggregate. -/

/-- `hcirc` of `⋈^At` / `⋈^∨` / `⋈^◯`. -/
theorem hcirc_prof {n : Nat} (stab : Fin (n+1) → List Form) :
    unionAll (fun j => circPart (stab j)) = [] ↔ circPart (unionAll stab) = [] := by
  simp only [List.eq_nil_iff_forall_not_mem]
  exact forall_congr' (fun x => not_congr (circPart_unionAll stab x))

/-- `hFnot`: the prime formula is not already stable. -/
theorem hFnot_prof {n : Nat} (stab : Fin (n+1) → List Form) (F : Form) :
    F ∉ unionAll (fun j => atPart (stab j)) ↔ F ∉ atPart (unionAll stab) :=
  not_congr (atPart_unionAll stab F)

/-- `hJ2`: every stable implication's antecedent is some premise's rhs. -/
theorem hJ2_prof {n : Nat} (stab : Fin (n+1) → List Form) (rhs : Fin (n+1) → Form) :
    (∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (stab j)) →
        A ∈ upsilon rhs)
      ↔ (∀ A B : Form, Form.imp A B ∈ impPart (unionAll stab) → A ∈ upsilon rhs) :=
  forall_congr' fun A => forall_congr' fun B =>
    imp_congr_left (impPart_unionAll stab (Form.imp A B))

/-- `hJ5`: every stable modal formula's body is absorbed by some promise. -/
theorem hJ5_prof {n k : Nat} (stab : Fin (n+1) → List Form)
    (Δs : Fin (k+1) → List Form) :
    (∀ Y : Form, Form.circ Y ∈ unionAll (fun j => circPart (stab j)) →
        ∃ i, Clo (Δs i) Y)
      ↔ (∀ Y : Form, Form.circ Y ∈ circPart (unionAll stab) → ∃ i, Clo (Δs i) Y) :=
  forall_congr' fun Y => imp_congr_left (circPart_unionAll stab (Form.circ Y))

/-- `hJ7s`: every promise closure absorbs every stable formula.  Stated in
the calculus per-premise; it is a condition on `Σ`. -/
theorem hJ7_prof {n k : Nat} (stab : Fin (n+1) → List Form)
    (Δs : Fin (k+1) → List Form) :
    (∀ (i : Fin (k+1)) (j : Fin (n+1)), ∀ X ∈ stab j, Clo (Δs i) X)
      ↔ (∀ i : Fin (k+1), ∀ X ∈ unionAll stab, Clo (Δs i) X) := by
  constructor
  · intro h i X hX
    obtain ⟨j, hj⟩ := mem_unionAll.mp hX
    exact h i j X hj
  · intro h i j X hX
    exact h i X (mem_unionAll.mpr ⟨j, hX⟩)

/-! ## 6. J1-extendability depends only on `(Σ, M)`

This is the clause that makes MERGING safe.  Without it a search could
discard a family that was the only one some later row could extend. -/

/-- (J1), as the calculus states it. -/
def J1 {n : Nat} (stab th : Fin (n+1) → List Form) : Prop :=
  ∀ i j, i ≠ j → stab i ⊆ stab j ++ th j

/-- **The extendability clause of the Profile Lemma.**

    J1 (b ∷ 𝔉)  ⟺  J1 𝔉  ∧  b.stab ⊆ M(𝔉)  ∧  Σ(𝔉) ⊆ b.stab ++ b.th

So whether a row may join is decided by the two aggregates `Σ` and `M`,
and by nothing else about the family. -/
theorem J1_cons {n : Nat} (bs bt : List Form) (stab th : Fin (n+1) → List Form) :
    J1 (Fin.cons bs stab) (Fin.cons bt th)
      ↔ J1 stab th ∧ bs ⊆ mAll stab th ∧ unionAll stab ⊆ bs ++ bt := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro i j hij
      have := h i.succ j.succ (fun e => hij (Fin.succ_inj.mp e))
      simpa using this
    · intro x hx
      rw [mem_mAll]
      intro j
      have := h 0 j.succ (Ne.symm (Fin.succ_ne_zero j))
      simpa using this hx
    · intro x hx
      obtain ⟨j, hj⟩ := mem_unionAll.mp hx
      have := h j.succ 0 (Fin.succ_ne_zero j)
      simpa using this hj
  · rintro ⟨h1, h2, h3⟩ i j
    induction i using Fin.cases with
    | zero =>
        induction j using Fin.cases with
        | zero => intro hij; exact absurd rfl hij
        | succ j' =>
            intro _ x hx
            simp only [Fin.cons_zero, Fin.cons_succ] at hx ⊢
            exact (mem_mAll.mp (h2 hx)) j'
    | succ i' =>
        induction j using Fin.cases with
        | zero =>
            intro _ x hx
            simp only [Fin.cons_zero, Fin.cons_succ] at hx ⊢
            exact h3 (mem_unionAll.mpr ⟨i', hx⟩)
        | succ j' =>
            intro hij x hx
            simp only [Fin.cons_succ] at hx ⊢
            exact h1 i' j' (fun e => hij (by rw [e])) hx

/-! ## 7. The fixpoint step

Adding one member updates each aggregate MONOTONELY: `Σ` and `Υ` grow,
`Θ` and `M` shrink.  That is what makes the profile space a finite lattice
explored by a worklist, rather than a set of subsets to enumerate. -/

theorem mem_unionAll_cons {n : Nat} (bs : List Form) (stab : Fin (n+1) → List Form)
    (x : Form) : x ∈ unionAll (Fin.cons bs stab) ↔ x ∈ bs ∨ x ∈ unionAll stab := by
  simp only [mem_unionAll, Fin.exists_fin_succ, Fin.cons_zero, Fin.cons_succ]

theorem mem_interAll_cons {n : Nat} (bt : List Form) (th : Fin (n+1) → List Form)
    (x : Form) : x ∈ interAll (Fin.cons bt th) ↔ x ∈ bt ∧ x ∈ interAll th := by
  simp only [mem_interAll, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ]

theorem mem_mAll_cons {n : Nat} (bs bt : List Form) (stab th : Fin (n+1) → List Form)
    (x : Form) : x ∈ mAll (Fin.cons bs stab) (Fin.cons bt th)
      ↔ x ∈ bs ++ bt ∧ x ∈ mAll stab th := by
  simp only [mem_mAll, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ]

theorem mem_upsilon_cons {n : Nat} (br : Form) (rhs : Fin (n+1) → Form) (x : Form) :
    x ∈ upsilon (Fin.cons br rhs) ↔ x = br ∨ x ∈ upsilon rhs := by
  simp only [upsilon, List.mem_map, List.mem_finRange, Fin.exists_fin_succ,
    Fin.cons_zero, Fin.cons_succ, true_and]
  exact ⟨fun h => h.imp Eq.symm id, fun h => h.imp Eq.symm id⟩

/-! ## 8. The SECOND Profile Lemma — the PROMISE family

The first lemma is about the irregular family `(stab, th, rhs)`.  The
promise joins `⋈^At,p`, `⋈^∨,p`, `⋈^◯,p` carry a SECOND family
`Δ⃗ : Fin (k+1) → List Form`, and it enters the calculus through exactly
two Bool-valued predicates on formulas (`FRJ/Calculus.lean:67,98`):

    E(Y) := any i, cloB (Δs i) Y      -- `inRestrictC`, and (J5)
    A(X) := all i, cloB (Δs i) X      -- `cloAllB`, hence `restrictP`, and (J7)

`restrictC`, `restrictP`, (J5) and (J7) are functions of `(E, A)` and of
nothing else about `Δ⃗` — not its arity, not its ordering.  And adding one
promise row updates them MONOTONELY, `E` growing and `A` shrinking, which
is what makes the promise families a second lattice to walk rather than a
second set of subsets to enumerate. -/

/-- `E`: some promise absorbs `Y`. -/
def cupCl {k : Nat} (Δs : Fin (k+1) → List Form) (Y : Form) : Bool :=
  (List.finRange (k+1)).any (fun i => cloB (Δs i) Y)

/-- `A`: every promise absorbs `X`.  This IS `cloAllB`, named for symmetry. -/
def capCl {k : Nat} (Δs : Fin (k+1) → List Form) (X : Form) : Bool :=
  cloAllB Δs X

@[simp] theorem cupCl_iff {k : Nat} {Δs : Fin (k+1) → List Form} {Y : Form} :
    cupCl Δs Y = true ↔ ∃ i, Clo (Δs i) Y := by
  simp [cupCl, List.any_eq_true, List.mem_finRange, cloB_iff]

@[simp] theorem capCl_iff {k : Nat} {Δs : Fin (k+1) → List Form} {X : Form} :
    capCl Δs X = true ↔ ∀ i, Clo (Δs i) X := by
  simp [capCl, cloAllB, List.all_eq_true, List.mem_finRange, cloB_iff]

/-! ### The two rule-level uses factor through `(E, A)` -/

/-- `restrictC` reads `Δ⃗` only through `E`. -/
theorem restrictC_eq_filter {k : Nat} (X : List Form) (Δs : Fin (k+1) → List Form) :
    restrictC X Δs = X.filter (fun f => match f with
      | Form.circ Y => cupCl Δs Y
      | _ => false) := rfl

/-- `restrictP` reads `Δ⃗` only through `A`. -/
theorem restrictP_eq_filter {k : Nat} (X : List Form) (Δs : Fin (k+1) → List Form) :
    restrictP X Δs = X.filter (capCl Δs) := rfl

/-- **Interchangeability.**  Two promise families whose `E` agrees on the
list being filtered give the same `restrictC`.  This is what licenses
keying a promise profile on `E` restricted to a finite universe: `Cl(Δ)`
is a closure over ALL formulas, but only its values on the members of `X`
are ever consulted. -/
theorem restrictC_congr {k k' : Nat} {X : List Form}
    {Δs : Fin (k+1) → List Form} {Δs' : Fin (k'+1) → List Form}
    (h : ∀ Y, Form.circ Y ∈ X → cupCl Δs Y = cupCl Δs' Y) :
    restrictC X Δs = restrictC X Δs' := by
  rw [restrictC_eq_filter, restrictC_eq_filter]
  refine List.filter_congr ?_
  intro f hf
  cases f with
  | atom _ => rfl
  | bot => rfl
  | and _ _ => rfl
  | or _ _ => rfl
  | imp _ _ => rfl
  | circ Y => exact h Y hf

/-- The `restrictP` counterpart, on `A`. -/
theorem restrictP_congr {k k' : Nat} {X : List Form}
    {Δs : Fin (k+1) → List Form} {Δs' : Fin (k'+1) → List Form}
    (h : ∀ Z ∈ X, capCl Δs Z = capCl Δs' Z) :
    restrictP X Δs = restrictP X Δs' := by
  rw [restrictP_eq_filter, restrictP_eq_filter]
  exact List.filter_congr h

/-- (J5) reads `Δ⃗` only through `E` — and, by `hJ5_prof`, the family only
through `Σ`. -/
theorem hJ5_cupCl {n k : Nat} (stab : Fin (n+1) → List Form)
    (Δs : Fin (k+1) → List Form) :
    (∀ Y : Form, Form.circ Y ∈ circPart (unionAll stab) → ∃ i, Clo (Δs i) Y)
      ↔ (∀ Y : Form, Form.circ Y ∈ circPart (unionAll stab) → cupCl Δs Y = true) :=
  forall_congr' fun _ => imp_congr_right fun _ => cupCl_iff.symm

/-- (J7) reads `Δ⃗` only through `A` — and, by `hJ7_prof`, the family only
through `Σ`. -/
theorem hJ7_capCl {n k : Nat} (stab : Fin (n+1) → List Form)
    (Δs : Fin (k+1) → List Form) :
    (∀ i : Fin (k+1), ∀ X ∈ unionAll stab, Clo (Δs i) X)
      ↔ (∀ X ∈ unionAll stab, capCl Δs X = true) := by
  constructor
  · intro h X hX; exact capCl_iff.mpr (fun i => h i X hX)
  · intro h i X hX; exact capCl_iff.mp (h X hX) i

/-! ### The promise fixpoint step: `E` grows, `A` shrinks -/

theorem cupCl_cons {k : Nat} (d : List Form) (Δs : Fin (k+1) → List Form) (Y : Form) :
    cupCl (Fin.cons d Δs) Y = (cloB d Y || cupCl Δs Y) := by
  rw [Bool.eq_iff_iff, Bool.or_eq_true, cupCl_iff, cupCl_iff, cloB_iff,
    Fin.exists_fin_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

theorem capCl_cons {k : Nat} (d : List Form) (Δs : Fin (k+1) → List Form) (X : Form) :
    capCl (Fin.cons d Δs) X = (cloB d X && capCl Δs X) := by
  rw [Bool.eq_iff_iff, Bool.and_eq_true, capCl_iff, capCl_iff, cloB_iff,
    Fin.forall_fin_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

/-! ## 9. Pins

Sorry-free and choice-free.  `J1_cons` is the clause the merging depends
on, so it is the one that must never quietly acquire an axiom. -/

/-- info: 'FRJ.Profile.J1_cons' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms J1_cons

/-- info: 'FRJ.Profile.joinCtxAt_prof' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms joinCtxAt_prof

/-- info: 'FRJ.Profile.joinCtxAtP_prof' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms joinCtxAtP_prof

/-- info: 'FRJ.Profile.hJ7_prof' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms hJ7_prof

/-- info: 'FRJ.Profile.mem_mAll_cons' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms mem_mAll_cons

end Profile
end FRJ
