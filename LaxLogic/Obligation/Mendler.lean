/-
# Mendler's constraint model `(Ω*, [], @)`, and what this library is in his terms

Reading §3.2 of

> M. Mendler, *A Modal Logic for Handling Behavioural Constraints in Formal
> Hardware Verification*, PhD thesis, Edinburgh, ECS-LFCS-93-255, 1993,
> pp. 59–86.

shows the obligation machinery here is not merely *analogous* to constraint
extraction — it is an instance of the model he singles out. He writes (p. 59):

    φ^[γₙ,…,γ₁]  ≝  weak[γₙ,…,γ₁] φ  =  γ₁ ⊃ ⋯ ⊃ γₙ ⊃ φ

so a constraint is a **list of propositions**, the unit is `[]`, composition is
append `@`, and applying a constraint weakens the formula by iterated
implication. That is exactly the shape `postponing theorem` produces:

    theorem foo : obligation₁ → ⋯ → obligationₙ → goal

is `weak [obligationₙ, …, obligation₁] goal`, and the ledger is the list.

His plan (3.2)–(3.5) on the same page lines up term for term with this library:

| Mendler §3.2 | here |
| --- | --- |
| constraint type `\|M\|` | the index type `γ` |
| constraint predicate `M* : \|M\| ⇒ Ω` | `Refined γ = γ → Prop` |
| constraint term `t : \|M\|` extracted from a proof | the recorded obligation |
| proof of `M* t` in the base logic `B` | the theorem `postponing theorem` adds |
| base logic `B`, proof-irrelevant | Lean's `Prop` |

Two remarks from the surrounding pages are worth recording, because they explain
why the Lean rendering is smaller than either the thesis or the TPHOLs paper.

*Dependent types.* On p. 57 he notes that a higher-order `L` would make `|M|`
depend on the formula substituted for a propositional variable, "whence `|M|`
would be a **dependent type**. Adding dependent types to the type system of `L`
and `B` is a major complication that we want to avoid in this thesis." Lean's
base logic is dependently typed, so the complication he had to design around is
simply absent, and `|M|` can be an ordinary index computed by Lean.

*Intuitionism is load-bearing.* Also p. 57: `L` is intuitionistic, and "this
allows us to extract from derivations in `L` constraint information in the form
of ordinary lambda terms." The same point appears here as
`BeliefLink`'s observation that classically `A` modulo `C` collapses to
`A ∨ ¬C` and the debt evaporates.
-/

import LaxLogic.Obligation.Modality

namespace LaxLogic.Obligation

/-- **Mendler's `weak`** (§3.2, p. 59): apply a constraint, given as a list of
propositions, by iterated implication.

His indexing runs `φ^[γₙ,…,γ₁] = γ₁ ⊃ ⋯ ⊃ γₙ ⊃ φ`, i.e. the list is written
outermost-last; here the list is in application order, which is the order
`postponing theorem` puts the obligations in. -/
def weak : List Prop → Prop → Prop
  | [], φ => φ
  | γ :: rest, φ => γ → weak rest φ

/-- The unit of the constraint monoid: the empty constraint changes nothing. -/
@[simp] theorem weak_nil (φ : Prop) : weak [] φ = φ := rfl

/-- A one-element constraint is exactly `Debt`. -/
@[simp] theorem weak_singleton (γ φ : Prop) : weak [γ] φ = Debt γ φ := rfl

/-- **Composition is append.** This is the `@` of Mendler's triple `(Ω*, [], @)`
and the reason obligations from different holes, and from different modules,
combine by concatenating the ledger. -/
@[simp] theorem weak_append (c d : List Prop) (φ : Prop) :
    weak (c ++ d) φ = weak c (weak d φ) := by
  induction c with
  | nil => rfl
  | cons γ rest ih => simp only [List.cons_append, weak, ih]

/-- Applying a constraint is monotone in the formula: the `◯⊃` rule, in list
form. -/
theorem weak_mono {φ ψ : Prop} (c : List Prop) (h : φ → ψ) : weak c φ → weak c ψ := by
  induction c with
  | nil => exact h
  | cons γ rest ih => exact fun f g => ih (f g)

/-- Discharging a whole constraint list recovers the formula. `Debt.discharge`
iterated, and the operation an automated loop is trying to reach. -/
theorem weak_discharge : ∀ (c : List Prop), (∀ γ ∈ c, γ) → ∀ {φ : Prop}, weak c φ → φ
  | [], _, _, h => h
  | γ :: rest, hall, _, h =>
      weak_discharge rest (fun δ hδ => hall δ (List.mem_cons_of_mem _ hδ))
        (h (hall γ (List.mem_cons_self ..)))

/-- A constraint list is vacuous as soon as one of its members is false: nothing
about `φ` can be recovered. The list form of `Debt.vacuous`, and the reason a
recorded obligation is only worth anything when it might hold. -/
theorem weak_vacuous (c d : List Prop) (φ : Prop) : weak (c ++ False :: d) φ := by
  induction c with
  | nil => exact fun h => h.elim
  | cons γ rest ih => exact fun _ => ih

/-! ### The `Refined`/`M*` identification

Mendler's (3.3) asks for a constraint predicate `M* : |M| ⇒ Ω`. That is
`Refined γ` on the nose, and his (3.4)–(3.5) — extract a constraint term `t` and
prove `M* t` — is the pair `postponing theorem` produces. -/

/-- `Refined γ` *is* Mendler's constraint predicate `M* : |M| ⇒ Ω`, with `γ` the
constraint type `|M|` and `Prop` the propositions `Ω`. -/
example (γ : Type) : Refined γ = (γ → Prop) := rfl

/-- And `◯∀` is his `weak` read pointwise: the constraint holds of a witness,
therefore so does the formula. -/
theorem laxAll_as_weak {γ : Type} (p : Constraint γ) (M : Refined γ) :
    ◯∀[p] M ↔ ∀ z, weak [p z] (M z) := Iff.rfl

end LaxLogic.Obligation
