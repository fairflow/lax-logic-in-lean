/-
# `LaxLogic.QLL.Interp` — Figs. 3 and 4: refinement types and the refinement relation

Where `◯∀` and `◯∃` finally stop behaving identically.

Fig. 5 gives them **the same rules** — its modal side condition reads only "if
`Q = ∀` or `Q = ∃`", and Fig. 6 carries the subscript without using it.  All the
content of the distinction is here, in Fig. 4:

    (p : ◯∀A) = ∀z::|A|. p z ⊃ (z : A)
    (p : ◯∃A) = ∃z::|A|. p z ∧ (z : A)

`◯∀` says every witness the constraint admits refines `A`; `◯∃` says some
witness does.  Weakening against strengthening.

## `⊨` is a shallow embedding, not a Kripke semantics

This is the paper's own design, and why its headline result is *conservativity
over HOL* rather than completeness: the zip/unzip equations translate a
refinement pair into an ordinary proposition by recursion on the formula.  No
frames, no worlds, no accessibility.  What is needed instead is an ordinary
first-order structure — a domain, an interpretation of the predicate symbols —
which is what `Model` is.

## Two departures from Fig. 3, both forced by `n`-ary predicates

The report is single-sorted and its atoms are bare predicates `P :: α ⇒ 𝔹`, so
`|P| = α` and `(p : P) = P p`: the constraint witnessing an atom is an
*individual*.  With `n`-ary predicates that has to generalise, and the choice is
recorded rather than silently made:

* a separate witness type `C` for atoms, so `atom : String → List D → C → Prop`
  reads "this constraint witnesses `P(t₁,…,tₙ)`".  Taking `C := D` recovers the
  report exactly.
* the report's `∀x::α.A` carries the sort at the binder; here there is one
  domain `D`, so `|∀x.A| = D ⇒ |A|`.

## Non-empty types, as the report requires

`|false| := 1`, not the empty type, and the report says why: "We must choose a
non-empty type for each formula as empty types are inconsistent with our base
logic."  HOL supplies that for free; Lean does not, so `Model` carries the two
witnesses `d₀` and `c₀` explicitly and `Val.default` propagates them to every
formula.  Nothing is weakened by this — it is the report's own side condition,
made a field instead of a background assumption — and it is what lets ex falso
(our addition, not the figure's) be interpreted at all.

## Bound variables are interpreted, not substituted

`Refines` carries an environment: a list of domain elements for the de Bruijn
indices and a valuation for the named free individuals.  A quantifier extends
the list.  So no opening happens during interpretation, and no freshness
condition is needed — which is a good deal cleaner than substituting terms.
-/
import LaxLogic.QLL.Syntax

namespace LaxLogic.QLL

/--
A first-order structure: a domain of individuals, a witness type for atoms, and
an interpretation of the predicate and function symbols.

Not a Kripke model.  `Refines` below is a translation into Lean's own logic, in the
manner of the paper's translation into HOL.
-/
structure Model where
  /-- The domain of individuals. -/
  D : Type
  /-- Witnesses for atomic formulas.  `C := D` recovers the report's `|P| = α`. -/
  C : Type
  /-- `fn f ⟦t₁⟧ … ⟦tₙ⟧` — the interpretation of a function symbol. -/
  fn : String → List D → D
  /-- `atom P ⟦t₁⟧ … ⟦tₙ⟧ c` — the constraint `c` witnesses `P(t₁,…,tₙ)`. -/
  atom : String → List D → C → Prop
  /-- `D` is non-empty.  Also the value a loose index evaluates to, which
  cannot arise for a locally closed term. -/
  d₀ : D
  /-- `C` is non-empty — the report's requirement on every refinement type. -/
  c₀ : C

variable (𝔐 : Model)

/-! ## Fig. 3 — refinement types

`|A|`, the type of constraints for `A`.  It depends only on the *shape* of the
formula, never on its terms, which is why nothing here needs an environment. -/

/-- The report's `|A|`. -/
def Val : Form → Type
  | .top       => Unit
  | .bot       => Unit
  | .pred _ _  => 𝔐.C
  | .and A B   => Val A × Val B
  | .or A B    => Val A ⊕ Val B
  | .imp A B   => Val A → Val B
  | .circ _ A  => Val A → Prop
  | .forall_ A => 𝔐.D → Val A
  | .exists_ A => 𝔐.D × Val A

/-- Every refinement type is inhabited — the report's side condition on Fig. 3,
here discharged by recursion rather than assumed. -/
def Val.default : (A : Form) → Val 𝔐 A
  | .top       => ()
  | .bot       => ()
  | .pred _ _  => 𝔐.c₀
  | .and A B   => (Val.default A, Val.default B)
  | .or A _    => .inl (Val.default A)
  | .imp _ B   => fun _ => Val.default B
  | .circ _ _  => fun _ => True
  | .forall_ A => fun _ => Val.default A
  | .exists_ A => (𝔐.d₀, Val.default A)

/-!
## `|A| = |A{σ}|`

The report states this in prose — "the mapping removes any dependency of types
on object level terms" — and it is what makes `∀I` and `∃E` interpretable: the
rules open a formula with a fresh individual, and the constraint type must not
notice.  Here it is a theorem. -/

/-- Opening a formula does not change its refinement type. -/
theorem Val_openAt (u : Tm) : ∀ (A : Form) (k : Nat), Val 𝔐 (A.openAt k u) = Val 𝔐 A := by
  intro A
  induction A with
  | top | bot | pred => intro _; rfl
  | and A B ihM ihN => intro k; show (_ × _) = (_ × _); rw [ihM k, ihN k]
  | or A B ihM ihN => intro k; show (_ ⊕ _) = (_ ⊕ _); rw [ihM k, ihN k]
  | imp A B ihM ihN => intro k; show (_ → _) = (_ → _); rw [ihM k, ihN k]
  | circ _ A ih => intro k; show (_ → Prop) = (_ → Prop); rw [ih k]
  | forall_ A ih => intro k; show (_ → _) = (_ → _); rw [ih (k + 1)]
  | exists_ A ih => intro k; show (_ × _) = (_ × _); rw [ih (k + 1)]

/-- The instance the rules actually use. -/
theorem Val_openWith (a : String) (A : Form) : Val 𝔐 (A.openWith a) = Val 𝔐 A :=
  Val_openAt 𝔐 (.fvar a) A 0

/-! ## Interpreting terms

`env` gives the de Bruijn indices their values, innermost first; `ρ` valuates
the named free individuals. -/

mutual
def evalTm (env : List 𝔐.D) (ρ : String → 𝔐.D) : Tm → 𝔐.D
  | .bvar i  => env[i]?.getD 𝔐.d₀
  | .fvar x  => ρ x
  | .fn f ts => 𝔐.fn f (evalTms env ρ ts)
def evalTms (env : List 𝔐.D) (ρ : String → 𝔐.D) : List Tm → List 𝔐.D
  | []      => []
  | t :: ts => evalTm env ρ t :: evalTms env ρ ts
end

/-! ## Fig. 4 — the refinement relation

`Refines 𝔐 env ρ A p` is the report's `p : A`, read as a proposition of the
ambient logic.  Written `p ⊨ A` when the environment is understood. -/

/-- The zip/unzip equations of Fig. 4. -/
def Refines (env : List 𝔐.D) (ρ : String → 𝔐.D) : (A : Form) → Val 𝔐 A → Prop
  | .top,       _ => True
  | .bot,       _ => False
  | .pred P ts, c => 𝔐.atom P (evalTms 𝔐 env ρ ts) c
  | .and A B,   p => Refines env ρ A p.1 ∧ Refines env ρ B p.2
  | .or A B,    p => match p with
                     | .inl a => Refines env ρ A a
                     | .inr b => Refines env ρ B b
  | .imp A B,   f => ∀ z, Refines env ρ A z → Refines env ρ B (f z)
  | .circ .all A, φ => ∀ z, φ z → Refines env ρ A z
  | .circ .ex A,  φ => ∃ z, φ z ∧ Refines env ρ A z
  | .forall_ A, f => ∀ d : 𝔐.D, Refines (d :: env) ρ A (f d)
  | .exists_ A, p => Refines (p.1 :: env) ρ A p.2

/-- A closed formula, in the empty environment. -/
abbrev RefinesC (ρ : String → 𝔐.D) (A : Form) (p : Val 𝔐 A) : Prop := Refines 𝔐 [] ρ A p

end LaxLogic.QLL
