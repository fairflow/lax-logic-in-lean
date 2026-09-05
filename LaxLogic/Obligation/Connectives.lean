/-
# Fig. 4 in full: every connective, and the rule that constrains it

`Modality.lean` gives the two modal clauses of Fig. 4. This module gives the
rest, and in doing so exposes the structure that makes them cohere.

**Fig. 4 is a family of combinators on `Refined`, one per connective, and Fig. 3
says which index type each lands on.** Writing `⟨M⟩` for the index of `M`:

| connective | Fig. 3 index | combinator |
| --- | --- | --- |
| `true`, `false` | `1` | `Refined.tt`, `Refined.ff` |
| `M ∧ N` | `⟨M⟩ × ⟨N⟩` | `Refined.and` |
| `M ∨ N` | `⟨M⟩ + ⟨N⟩` | `Refined.or` |
| `M ⊃ N` | `⟨M⟩ ⇒ ⟨N⟩` | `Refined.imp` |
| `∀x::α. M` | `α ⇒ ⟨M⟩` | `Refined.all` |
| `∃x::α. M` | `α × ⟨M⟩` | `Refined.ex` |
| `◯∀M`, `◯∃M` | `⟨M⟩ ⇒ 𝔹` | `Refined.boxAll`, `Refined.boxEx` |

The last row is what ties it together: the two modalities are themselves
`Refined` constructors, landing on `Constraint ⟨M⟩ = ⟨M⟩ → Prop`. So `◯` is not
a separate layer bolted onto the connectives — it is one of them, and a formula
like `◯∀(M ⊃ ◯∃N)` is just an iterated application whose index type Lean
computes for us. In the paper that has to be maintained by hand, because `|·|`
is a syntactic recursion over a grammar that HOL does not know about.

Two things fall out and are proved below.

* **The paper's `⊃_◯` rule takes a Fig. 4 implication as its hypothesis.**
  `laxAll_image` was stated with `∀ m, M m → N (r m)`, which is exactly
  `Refined.imp M N r`. `laxAll_imp_image` records the identification, which is
  the coherence check between the two halves of the development.
* **`true` and `false` measure the constraint.** `◯∃[p] true` says `p` is
  satisfiable and `◯∀[p] false` says it is not, so the units are not padding:
  they are where the paper's remark that every refinement type must be
  non-empty becomes visible.
-/

import LaxLogic.Obligation.Modality

universe u v w

namespace LaxLogic.Obligation
namespace Refined

/-! ### The units. Fig. 3: `|true| = |false| = 1`. -/

/-- `true`, at the one-point refinement type. -/
def tt : Refined Unit := fun _ => True

/-- `false`, at the one-point refinement type. The paper notes that the image of
`false` is the same as that of `true`, and that every refinement type must be
non-empty, since an empty type is inconsistent with the base logic. -/
def ff : Refined Unit := fun _ => False

/-! ### Conjunction and disjunction -/

/-- `M ∧ N` at index `⟨M⟩ × ⟨N⟩`. Fig. 4:
`(p : M ∧ N) = (π₁ p : M) ∧ (π₂ p : N)`. -/
def and {γ : Type u} {δ : Type v} (M : Refined γ) (N : Refined δ) :
    Refined (γ × δ) :=
  fun wz => M wz.1 ∧ N wz.2

/-- `M ∨ N` at index `⟨M⟩ + ⟨N⟩`, the `either` of `Modality.lean`. -/
def or {γ : Type u} {δ : Type v} (M : Refined γ) (N : Refined δ) :
    Refined (γ ⊕ δ) :=
  either M N

/-! ### Implication

The clause that most repays writing out. Fig. 4:

    (p : M ⊃ N) = ∀z::|M|. (z : M) ⊃ (p z : N)

so a constraint for an implication is a **function** taking a witness for the
antecedent to one for the consequent, and the clause says it maps witnesses that
satisfy `M` to witnesses that satisfy `N`. -/

/-- `M ⊃ N` at index `⟨M⟩ ⇒ ⟨N⟩`. -/
def imp {γ : Type u} {δ : Type v} (M : Refined γ) (N : Refined δ) :
    Refined (γ → δ) :=
  fun f => ∀ z, M z → N (f z)

/-! ### Quantifiers

Fig. 4's clauses, `(p : ∀x::α.M) = ∀u::α. (p u : M[u/x])` and
`(p : ∃x::α.M) = (π₂ p : M[π₁ p/x])`. An abstract formula with a free object
variable is a *family* of refined formulas, so `M : α → Refined γ`. -/

/-- `∀x::α. M` at index `α ⇒ ⟨M⟩`. -/
def all {α : Type w} {γ : Type u} (M : α → Refined γ) : Refined (α → γ) :=
  fun f => ∀ u, M u (f u)

/-- `∃x::α. M` at index `α × ⟨M⟩`: the witness carries the object-level witness
alongside the refinement witness. -/
def ex {α : Type w} {γ : Type u} (M : α → Refined γ) : Refined (α × γ) :=
  fun uz => M uz.1 uz.2

/-! ### The modalities, as connectives of the same family

Fig. 3: `|◯∀M| = |◯∃M| = |M| ⇒ 𝔹`. So a modal formula is refined by a
*predicate* on the witnesses of its argument, and `◯` takes its place among the
connectives rather than sitting above them. -/

/-- `◯∀M` at index `⟨M⟩ ⇒ 𝔹`. -/
def boxAll {γ : Type u} (M : Refined γ) : Refined (Constraint γ) :=
  fun p => LaxAll p M

/-- `◯∃M` at index `⟨M⟩ ⇒ 𝔹`. -/
def boxEx {γ : Type u} (M : Refined γ) : Refined (Constraint γ) :=
  fun p => LaxEx p M

@[simp] theorem boxAll_apply {γ : Type u} (M : Refined γ) (p : Constraint γ) :
    boxAll M p = LaxAll p M := rfl

@[simp] theorem boxEx_apply {γ : Type u} (M : Refined γ) (p : Constraint γ) :
    boxEx M p = LaxEx p M := rfl

end Refined

/-! ## The rules

One per connective, in both modal readings where both hold. Each says: given
constrained proofs of the parts, here is the constraint for the whole. -/

open Refined

/-! ### Units -/

/-- Anything is true modulo any constraint, at `true`. -/
theorem laxAll_tt {p : Constraint Unit} : ◯∀[p] tt := fun _ _ => trivial

/-- `◯∃[p] true` says exactly that the constraint is **satisfiable**. -/
theorem laxEx_tt {p : Constraint Unit} : ◯∃[p] tt ↔ ∃ z, p z :=
  ⟨fun ⟨z, hz, _⟩ => ⟨z, hz⟩, fun ⟨z, hz⟩ => ⟨z, hz, trivial⟩⟩

/-- `◯∀[p] false` says exactly that the constraint is **unsatisfiable**. Taken
with `laxEx_tt`, the units are the two ways of asking whether a constraint can
be met at all. -/
theorem laxAll_ff {p : Constraint Unit} : ◯∀[p] ff ↔ ∀ z, ¬ p z :=
  ⟨fun h z hz => h z hz, fun h z hz => (h z hz).elim⟩

/-- `◯∃[p] false` is impossible, whatever the constraint. -/
theorem laxEx_ff {p : Constraint Unit} : ◯∃[p] ff ↔ False :=
  ⟨fun ⟨_, _, h⟩ => h, fun h => h.elim⟩

/-! ### Conjunction: the paper's `◯∧`, restated against `Refined.and` -/

theorem laxAll_and' {γ : Type u} {δ : Type v}
    {p : Constraint γ} {q : Constraint δ} {M : Refined γ} {N : Refined δ}
    (hM : ◯∀[p] M) (hN : ◯∀[q] N) : ◯∀[pair p q] (Refined.and M N) :=
  fun _ hz => ⟨hM _ hz.1, hN _ hz.2⟩

theorem laxEx_and' {γ : Type u} {δ : Type v}
    {p : Constraint γ} {q : Constraint δ} {M : Refined γ} {N : Refined δ}
    (hM : ◯∃[p] M) (hN : ◯∃[q] N) : ◯∃[pair p q] (Refined.and M N) := by
  obtain ⟨w, hw, hMw⟩ := hM
  obtain ⟨z, hz, hNz⟩ := hN
  exact ⟨(w, z), ⟨hw, hz⟩, hMw, hNz⟩

/-! ### Implication

The coherence check between the two halves of the development. -/

/-- **The paper's `⊃_◯` rule takes a Fig. 4 implication as its hypothesis.**
`laxAll_image` was stated with the unfolded `∀ m, M m → N (r m)`; that is
literally `Refined.imp M N r`. Nothing changes but the reading, which is the
point: the constraint calculus and the connective family are the same
development seen from two sides. -/
theorem laxAll_imp_image {γ : Type u} {δ : Type v}
    {p : Constraint γ} {M : Refined γ} {N : Refined δ} {r : γ → δ}
    (hM : ◯∀[p] M) (hr : Refined.imp M N r) : ◯∀[image r p] N :=
  laxAll_image hM hr

@[inherit_doc laxAll_imp_image]
theorem laxEx_imp_image {γ : Type u} {δ : Type v}
    {p : Constraint γ} {M : Refined γ} {N : Refined δ} {r : γ → δ}
    (hM : ◯∃[p] M) (hr : Refined.imp M N r) : ◯∃[image r p] N :=
  laxEx_image hM hr

/-- Implication introduction: a constraint for `M ⊃ N` is a function, and it is
constrained pointwise by "sends `p`-witnesses to `q`-witnesses". -/
def toFun {γ : Type u} {δ : Type v} (p : Constraint γ) (q : Constraint δ) :
    Constraint (γ → δ) :=
  fun f => ∀ z, p z → q (f z)

theorem laxAll_imp {γ : Type u} {δ : Type v}
    {p : Constraint γ} {q : Constraint δ} {M : Refined γ} {N : Refined δ}
    (hMp : ∀ z, M z → p z) (hN : ◯∀[q] N) :
    ◯∀[toFun p q] (Refined.imp M N) :=
  fun f hf z hMz => hN (f z) (hf z (hMp z hMz))

/-! ### Quantifiers -/

/-- A constraint for `∀x::α. M` is a choice function, constrained pointwise. -/
def piC {α : Type w} {γ : Type u} (p : α → Constraint γ) : Constraint (α → γ) :=
  fun f => ∀ u, p u (f u)

/-- A constraint for `∃x::α. M` constrains the object witness and the refinement
witness together. -/
def sigC {α : Type w} {γ : Type u} (p : α → Constraint γ) : Constraint (α × γ) :=
  fun uz => p uz.1 uz.2

theorem laxAll_all {α : Type w} {γ : Type u}
    {p : α → Constraint γ} {M : α → Refined γ} (h : ∀ u, ◯∀[p u] (M u)) :
    ◯∀[piC p] (Refined.all M) :=
  fun f hf u => h u (f u) (hf u)

theorem laxEx_ex {α : Type w} {γ : Type u}
    {p : α → Constraint γ} {M : α → Refined γ} {u : α} (h : ◯∃[p u] (M u)) :
    ◯∃[sigC p] (Refined.ex M) := by
  obtain ⟨z, hz, hM⟩ := h
  exact ⟨(u, z), hz, hM⟩

/-- `◯∀` over an existential constraint: the object witness is still universally
quantified, so this is the `∀`-shaped statement, matching `laxAll_sum`'s
behaviour on the other coproduct. -/
theorem laxAll_ex {α : Type w} {γ : Type u}
    {p : α → Constraint γ} {M : α → Refined γ} (h : ∀ u, ◯∀[p u] (M u)) :
    ◯∀[sigC p] (Refined.ex M) :=
  fun uz hz => h uz.1 uz.2 hz

/-! ### Iterating the modality

Because `◯` is a connective of the same family, a doubly-modal formula is an
ordinary application and its index type is computed. These are the two facts one
needs to work with such formulas at all. -/

/-- Unit at the outer modality: a proof of `◯∀[p] M` is a witness of
`Refined.boxAll M` at `p`, so the singleton constraint at `p` gives `◯∀◯∀M`. -/
theorem laxAll_boxAll {γ : Type u} {p : Constraint γ} {M : Refined γ}
    (h : ◯∀[p] M) : ◯∀[val p] (Refined.boxAll M) :=
  laxAll_val h

/-- Collapse: from `◯∀` of `◯∀M` at a constraint that pins the inner constraint
to `p`, recover `◯∀[p] M`. Together with `laxAll_boxAll` this is the round
trip. -/
theorem laxAll_boxAll_elim {γ : Type u} {p : Constraint γ} {M : Refined γ}
    (h : ◯∀[val p] (Refined.boxAll M)) : ◯∀[p] M :=
  h p rfl

end LaxLogic.Obligation
