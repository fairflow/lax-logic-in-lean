/-
# `LaxLogic.QLL.Interp` — Figs. 3 and 4: refinement types and the refinement relation

Where `◯∀` and `◯∃` finally stop behaving identically.

Fig. 5 gives them **the same rules** — its modal side condition reads only "if
`Q = ∀` or `Q = ∃`", and Fig. 6 carries the subscript without using it.  All the
content of the distinction is here, in Fig. 4:

    (p : ◯∀M) = ∀z::|M|. p z ⊃ (z : M)
    (p : ◯∃M) = ∃z::|M|. p z ∧ (z : M)

`◯∀` says every witness the constraint admits refines `M`; `◯∃` says some
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
* the report's `∀x::α.M` carries the sort at the binder; here there is one
  domain `D`, so `|∀x.M| = D ⇒ |M|`.

## Bound variables are interpreted, not substituted

`Sat` carries an environment: a list of domain elements for the de Bruijn
indices and a valuation for the named free individuals.  A quantifier extends
the list.  So no opening happens during interpretation, and no freshness
condition is needed — which is a good deal cleaner than substituting terms.
-/
import LaxLogic.QLL.Syntax

namespace LaxLogic.QLL

/--
A first-order structure: a domain of individuals, a witness type for atoms, and
an interpretation of the predicate and function symbols.

Not a Kripke model.  `Sat` below is a translation into Lean's own logic, in the
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

variable (𝔐 : Model)

/-! ## Fig. 3 — refinement types

`|M|`, the type of constraints for `M`.  It depends only on the *shape* of the
formula, never on its terms, which is why nothing here needs an environment. -/

/-- The report's `|M|`. -/
def Val : Form → Type
  | .top       => Unit
  | .bot       => Unit
  | .pred _ _  => 𝔐.C
  | .and M N   => Val M × Val N
  | .or M N    => Val M ⊕ Val N
  | .imp M N   => Val M → Val N
  | .circ _ M  => Val M → Prop
  | .forall_ M => 𝔐.D → Val M
  | .exists_ M => 𝔐.D × Val M

/-! ## Interpreting terms

`env` gives the de Bruijn indices their values, innermost first; `ρ` valuates
the named free individuals. -/

mutual
def evalTm (env : List 𝔐.D) (ρ : String → 𝔐.D) : Tm → 𝔐.D
  | .bvar i  => env[i]?.getD (ρ "")
  | .fvar x  => ρ x
  | .fn f ts => 𝔐.fn f (evalTms env ρ ts)
def evalTms (env : List 𝔐.D) (ρ : String → 𝔐.D) : List Tm → List 𝔐.D
  | []      => []
  | t :: ts => evalTm env ρ t :: evalTms env ρ ts
end

/-! ## Fig. 4 — the refinement relation

`Sat 𝔐 env ρ M p` is the report's `p : M`, read as a proposition of the
ambient logic.  Written `p ⊨ M` when the environment is understood. -/

/-- The zip/unzip equations of Fig. 4. -/
def Sat (env : List 𝔐.D) (ρ : String → 𝔐.D) : (M : Form) → Val 𝔐 M → Prop
  | .top,       _ => True
  | .bot,       _ => False
  | .pred P ts, c => 𝔐.atom P (evalTms 𝔐 env ρ ts) c
  | .and M N,   p => Sat env ρ M p.1 ∧ Sat env ρ N p.2
  | .or M N,    p => match p with
                     | .inl a => Sat env ρ M a
                     | .inr b => Sat env ρ N b
  | .imp M N,   f => ∀ z, Sat env ρ M z → Sat env ρ N (f z)
  | .circ .all M, φ => ∀ z, φ z → Sat env ρ M z
  | .circ .ex M,  φ => ∃ z, φ z ∧ Sat env ρ M z
  | .forall_ M, f => ∀ d : 𝔐.D, Sat (d :: env) ρ M (f d)
  | .exists_ M, p => Sat (p.1 :: env) ρ M p.2

/-- A closed formula, in the empty environment. -/
abbrev SatC (ρ : String → 𝔐.D) (M : Form) (p : Val 𝔐 M) : Prop := Sat 𝔐 [] ρ M p

end LaxLogic.QLL
