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

## Non-empty types, as the report requires

`|false| := 1`, not the empty type, and the report says why: "We must choose a
non-empty type for each formula as empty types are inconsistent with our base
logic."  HOL supplies that for free; Lean does not, so `Model` carries the two
witnesses `d₀` and `c₀` explicitly and `Val.default` propagates them to every
formula.  Nothing is weakened by this — it is the report's own side condition,
made a field instead of a background assumption — and it is what lets ex falso
(our addition, not the figure's) be interpreted at all.

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
  /-- `D` is non-empty.  Also the value a loose index evaluates to, which
  cannot arise for a locally closed term. -/
  d₀ : D
  /-- `C` is non-empty — the report's requirement on every refinement type. -/
  c₀ : C

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

/-- Every refinement type is inhabited — the report's side condition on Fig. 3,
here discharged by recursion rather than assumed. -/
def Val.default : (M : Form) → Val 𝔐 M
  | .top       => ()
  | .bot       => ()
  | .pred _ _  => 𝔐.c₀
  | .and M N   => (Val.default M, Val.default N)
  | .or M _    => .inl (Val.default M)
  | .imp _ N   => fun _ => Val.default N
  | .circ _ _  => fun _ => True
  | .forall_ M => fun _ => Val.default M
  | .exists_ M => (𝔐.d₀, Val.default M)

/-!
## `|M| = |M{σ}|`

The report states this in prose — "the mapping removes any dependency of types
on object level terms" — and it is what makes `∀I` and `∃E` interpretable: the
rules open a formula with a fresh individual, and the constraint type must not
notice.  Here it is a theorem. -/

/-- Opening a formula does not change its refinement type. -/
theorem Val_openAt (u : Tm) : ∀ (M : Form) (k : Nat), Val 𝔐 (M.openAt k u) = Val 𝔐 M := by
  intro M
  induction M with
  | top | bot | pred => intro _; rfl
  | and M N ihM ihN => intro k; show (_ × _) = (_ × _); rw [ihM k, ihN k]
  | or M N ihM ihN => intro k; show (_ ⊕ _) = (_ ⊕ _); rw [ihM k, ihN k]
  | imp M N ihM ihN => intro k; show (_ → _) = (_ → _); rw [ihM k, ihN k]
  | circ _ M ih => intro k; show (_ → Prop) = (_ → Prop); rw [ih k]
  | forall_ M ih => intro k; show (_ → _) = (_ → _); rw [ih (k + 1)]
  | exists_ M ih => intro k; show (_ × _) = (_ × _); rw [ih (k + 1)]

/-- The instance the rules actually use. -/
theorem Val_openWith (a : String) (M : Form) : Val 𝔐 (M.openWith a) = Val 𝔐 M :=
  Val_openAt 𝔐 (.fvar a) M 0

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
