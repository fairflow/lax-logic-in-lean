/-
# `LaxLogic.QLL.LLP` — §5, the Lax Logic Programming fragment

Stage 2 of `docs/qll-clp-implementation-plan.md`.

Definition 5.1 fixes three things: the **Σ-formulas**, which are the queries and
the clause bodies; the **program clauses** `∀x₁…xₘ. S ⊃ H` with `H` a predicate
or a modalised predicate on exactly those bound variables; and the fragment
`Π ⊢LLP S`, `Π ⊢LLP ◯S`.  Figure 3 then gives five derived rules, and the paper
supplies their proof terms:

    ∧◯(p, q)    := let y ⇐ p in let z ⇐ q in val(y, z)
    ∨◯(p, i)    := let z ⇐ p in val(ιᵢ(z))
    ⊃◯(p, w, t̃) := let z ⇐ p in w t̃ z
    N◯(p, w, t̃) := w t̃ p
    ∃◯(p, t)    := let z ⇐ p in val(⟨t⟩(z))

"Derived" is the whole claim: each is built from Fig. 2 alone, which here is
`Derives`.  So this file adds no rule; it discharges five obligations.

## Three design decisions

**The modality stays generic.**  The paper has one `◯`; `Derives` is
`Q`-parametric and `circE` forces the same `Q` throughout, so every rule below
is proved for an arbitrary `q` and the paper's is `q = .ex`.  Nothing is lost
and the `◯∀` reading comes free.

**The rules are stated over assumption contexts**, as in `CLP.lean` and as
resolution does anyway: a program clause *is* an assumption `w : ∀ỹ. M ⊃ ◯N`.
This is not a dodge — it is what `Π ⊢LLP` means, the program sitting in the
context throughout — and it keeps every derivation free of weakening, which
would otherwise be needed in `∧◯` to carry the second premise under the binder
introduced by the first.

**`⊃◯` and `N◯` are stated for an arbitrary head `N`,** not just an atomic one.
Definition 5.1's clauses are the special case where `N` is `P(x₁,…,xₘ)`; the
general form costs nothing and is what the derivation actually establishes.

## What is *not* here

The `?I` rule for the leaves of partial proofs, which the draft records as
disputed between the authors.  It is not needed for any of Figure 3, so it is
left until the abstraction machinery of §6 calls for it, where the choice can be
made against a use.
-/
import LaxLogic.QLL.CLP

namespace LaxLogic.QLL

open LaxLogic.QLL.CLP

/-! ## Iterated universals

`∀x₁…xₘ` and its elimination at `t̃`.  In the locally nameless presentation the
`m` binders nest, so instantiating the outermost first lowers the index each
time, which is what `instAll` records. -/

/-- `∀ⁿ. A`. -/
def Form.foralls : Nat → Form → Form
  | 0,     A => A
  | n + 1, A => .forall_ (Form.foralls n A)

/-- Instantiate the outer universals with `ts`, outermost first. -/
def Form.instAll : List Tm → Form → Form
  | [],      A => A
  | t :: ts, A => Form.instAll ts (A.openAt ts.length t)

/-- The proof term for successive `∀E`s. -/
def Pf.insts : List Tm → Pf → Pf
  | [],      p => p
  | t :: ts, p => Pf.insts ts (.inst t p)

theorem Form.openAt_foralls (t : Tm) : ∀ (n k : Nat) (A : Form),
    (Form.foralls n A).openAt k t = Form.foralls n (A.openAt (k + n) t)
  | 0,     k, A => by simp [Form.foralls]
  | n + 1, k, A => by
      show Form.forall_ ((Form.foralls n A).openAt (k + 1) t) = _
      rw [Form.openAt_foralls t n (k + 1) A]
      show Form.foralls (n + 1) (A.openAt (k + 1 + n) t) = Form.foralls (n + 1) (A.openAt (k + (n + 1)) t)
      rw [show k + 1 + n = k + (n + 1) by omega]

/-! `instAll` is a homomorphism for the connectives that do not bind. -/

theorem Form.instAll_imp : ∀ (ts : List Tm) (A B : Form),
    Form.instAll ts (.imp A B) = .imp (Form.instAll ts A) (Form.instAll ts B)
  | [],      _, _ => rfl
  | t :: ts, A, B => by
      show Form.instAll ts ((Form.imp A B).openAt ts.length t) = _
      show Form.instAll ts (.imp (A.openAt ts.length t) (B.openAt ts.length t)) = _
      rw [Form.instAll_imp ts]
      rfl

theorem Form.instAll_circ : ∀ (ts : List Tm) (q : Q) (A : Form),
    Form.instAll ts (.circ q A) = .circ q (Form.instAll ts A)
  | [],      _, _ => rfl
  | t :: ts, q, A => by
      show Form.instAll ts ((Form.circ q A).openAt ts.length t) = _
      show Form.instAll ts (.circ q (A.openAt ts.length t)) = _
      rw [Form.instAll_circ ts]
      rfl

theorem Pf.openP_insts (k : Nat) (u : Pf) : ∀ (ts : List Tm) (p : Pf),
    Pf.openP k u (Pf.insts ts p) = Pf.insts ts (Pf.openP k u p)
  | [],      _ => rfl
  | t :: ts, p => by
      show Pf.openP k u (Pf.insts ts (.inst t p)) = _
      rw [Pf.openP_insts k u ts]
      rfl

/-- `∀E` introduces no proof variable. -/
theorem Pf.fvP_insts : ∀ (ts : List Tm) (p : Pf), (Pf.insts ts p).fvP = p.fvP
  | [],      _ => rfl
  | t :: ts, p => by
      show (Pf.insts ts (.inst t p)).fvP = p.fvP
      rw [Pf.fvP_insts ts]
      rfl

/-- `∀E`, iterated. -/
def Derives.allEs : ∀ (ts : List Tm) {Γ : Ctx} {p : Pf} {A : Form},
    Derives p Γ (Form.foralls ts.length A) → Derives (Pf.insts ts p) Γ (Form.instAll ts A)
  | [],      _, _, _, d => d
  | t :: ts, _, _, A, d =>
      Derives.allEs ts (A := A.openAt ts.length t)
        (Derives.allE t d (by rw [Form.openAt_foralls, Nat.zero_add]))

/-! ## Definition 5.1 -/

/-- Σ-formulas: the queries, and the bodies of clauses. -/
inductive IsSigma : Form → Prop
  | top : IsSigma .top
  | pred (P : String) (ts : List Tm) : IsSigma (.pred P ts)
  | and {A B} : IsSigma A → IsSigma B → IsSigma (.and A B)
  | or {A B} : IsSigma A → IsSigma B → IsSigma (.or A B)
  | ex {A} : IsSigma A → IsSigma (.exists_ A)

/-- The arguments of a clause head: the bound variables `x₁,…,xₘ` in order. -/
def headVars (m : Nat) : List Tm := ((List.range m).reverse).map Tm.bvar

/-- A program clause `∀x₁…xₘ. S ⊃ H`, with `H` either `P(x̃)` or `◯P(x̃)`. -/
structure Clause where
  /-- `m`, the number of universally quantified variables. -/
  arity : Nat
  /-- `S`, a Σ-formula whose free individuals are among the `xᵢ`. -/
  body : Form
  /-- `S` is a Σ-formula. -/
  body_sigma : IsSigma body
  /-- The head predicate, which must not be a constraint. -/
  head : String
  /-- Whether the head is modalised. -/
  modal : Bool
  /-- The modality, when the head is modalised. -/
  q : Q

/-- The head `H` of a clause. -/
def Clause.headForm (c : Clause) : Form :=
  if c.modal then .circ c.q (.pred c.head (headVars c.arity))
  else .pred c.head (headVars c.arity)

/-- The clause read as a formula of QLL. -/
def Clause.form (c : Clause) : Form :=
  Form.foralls c.arity (.imp c.body c.headForm)

/-- An LLP program: a finite list of clauses. -/
abbrev Program := List Clause

/-- The program as a context, each clause held by a proof variable. -/
def Program.ctx (names : List String) (prog : Program) : Ctx :=
  (names.zip prog).map (fun e => (Pf.fvar e.1, e.2.form))

/-! ## Figure 3

Five rules, five derivations.  Each context holds exactly the premises the rule
names, which is the program-in-the-context reading of `Π ⊢LLP`. -/

variable (q : Q) (A B : Form)

/-! ### `∧◯` -/

/-- Already derived in `CLP.lean`; recorded here under the paper's name. -/
def andCircLLP : Derives (tmAnd q) (ctxAnd q A B) (.circ q (.and A B)) := andCirc q A B

/-! ### `∨◯` -/

/-- `p : ◯_q A`. -/
def ctxOrL : Ctx := [(.fvar "p", .circ q A)]

/-- `∨◯(p, 1) = let_q z ⇐ p in val_q (ι₁ z)`. -/
def tmOrL : Pf := .letQ q (.fvar "p") (.val q (.inl (.bvar 0)))

/-- The rule, derived. -/
def orCircL : Derives (tmOrL q) (ctxOrL q A) (.circ q (.or A B)) :=
  .circE "z" ⟨by simp only [ctxOrL, Ctx.fvP, Pf.fvP] <;> decide,
      by simp only [Pf.fvP] <;> decide⟩
    (.var (.head _))
    (.circI (.orI₁ (.var (.head _))))

/-- `q : ◯_q B`. -/
def ctxOrR : Ctx := [(.fvar "p", .circ q B)]

/-- `∨◯(q, 2) = let_q z ⇐ q in val_q (ι₂ z)`. -/
def tmOrR : Pf := .letQ q (.fvar "p") (.val q (.inr (.bvar 0)))

/-- The rule, derived. -/
def orCircR : Derives (tmOrR q) (ctxOrR q B) (.circ q (.or A B)) :=
  .circE "z" ⟨by simp only [ctxOrR, Ctx.fvP, Pf.fvP] <;> decide,
      by simp only [Pf.fvP] <;> decide⟩
    (.var (.head _))
    (.circI (.orI₂ (.var (.head _))))

/-! ### `∃◯` -/

/-- `p : ◯_q A[t/x]`. -/
def ctxExC (t : Tm) : Ctx := [(.fvar "p", .circ q (A.openAt 0 t))]

/-- `∃◯(p, t) = let_q z ⇐ p in val_q ⟨t⟩(z)`. -/
def tmExC (t : Tm) : Pf := .letQ q (.fvar "p") (.val q (.pack t (.bvar 0)))

/-- The rule, derived. -/
def exCirc (t : Tm) : Derives (tmExC q t) (ctxExC q A t) (.circ q (.exists_ A)) :=
  .circE "z" ⟨by simp only [ctxExC, Ctx.fvP, Pf.fvP] <;> decide,
      by simp only [Pf.fvP] <;> decide⟩
    (.var (.head _))
    (.circI (.exI t (.var (.head _))))

/-! ### `⊃◯` and `N◯`

Both use a clause `w : ∀ỹ. M ⊃ ◯N` and an instantiation `t̃`.  They differ only
in whether the other premise is modalised. -/

/-- `p : ◯_q M[t̃/ỹ]`, `w : ∀ỹ. M ⊃ ◯_q N`. -/
def ctxImpC (M N : Form) (ts : List Tm) : Ctx :=
  [(.fvar "p", .circ q (Form.instAll ts M)),
   (.fvar "w", Form.foralls ts.length (.imp M (.circ q N)))]

/-- `⊃◯(p, w, t̃) = let_q z ⇐ p in w t̃ z`. -/
def tmImpC (ts : List Tm) : Pf :=
  .letQ q (.fvar "p") (.app (Pf.insts ts (.fvar "w")) (.bvar 0))

/-- The rule, derived. -/
def impCircC (M N : Form) (ts : List Tm) :
    Derives (tmImpC q ts) (ctxImpC q M N ts) (.circ q (Form.instAll ts N)) := by
  refine .circE "z" ⟨by simp only [ctxImpC, Ctx.fvP, Pf.fvP] <;> decide, ?_⟩ (.var (.head _)) ?_
  · show "z" ∉ (Pf.insts ts (.fvar "w")).fvP ++ []
    rw [Pf.fvP_insts]; decide
  · show Derives (Pf.openP 0 (.fvar "z") (.app (Pf.insts ts (.fvar "w")) (.bvar 0))) _ _
    show Derives (.app (Pf.openP 0 (.fvar "z") (Pf.insts ts (.fvar "w"))) (.fvar "z")) _ _
    rw [Pf.openP_insts]
    refine .impE ?_ (.var (.head _))
    have h := Derives.allEs (Γ := (Pf.fvar "z", Form.instAll ts M) :: ctxImpC q M N ts)
      (A := Form.imp M (.circ q N)) ts (.var (.tail _ (.tail _ (.head _))))
    rw [Form.instAll_imp, Form.instAll_circ] at h
    exact h

/-- `p : M[t̃/ỹ]`, `w : ∀ỹ. M ⊃ ◯_q N`. -/
def ctxN (M N : Form) (ts : List Tm) : Ctx :=
  [(.fvar "p", Form.instAll ts M),
   (.fvar "w", Form.foralls ts.length (.imp M (.circ q N)))]

/-- `N◯(p, w, t̃) = w t̃ p`. -/
def tmN (ts : List Tm) : Pf := .app (Pf.insts ts (.fvar "w")) (.fvar "p")

/-- The rule, derived.  No `◯E` is needed: this is `∀E` then `⊃E`. -/
def nCirc (M N : Form) (ts : List Tm) :
    Derives (tmN ts) (ctxN q M N ts) (.circ q (Form.instAll ts N)) := by
  refine .impE ?_ (.var (.head _))
  have h := Derives.allEs (Γ := ctxN q M N ts) (A := Form.imp M (.circ q N)) ts
    (.var (.tail _ (.head _)))
  rw [Form.instAll_imp, Form.instAll_circ] at h
  exact h

/-! ## Axioms

None of the five rules uses `Classical.choice`.  The freshness side conditions
of `circE` are discharged by `simp only [defs, Pf.fvP]` and `decide`; plain
`simp` would bring in choice through its default simp set, which is why these
proofs spell out the unfolding. -/

/-- info: 'LaxLogic.QLL.andCircLLP' depends on axioms: [propext] -/
#guard_msgs in #print axioms andCircLLP

/-- info: 'LaxLogic.QLL.orCircL' depends on axioms: [propext] -/
#guard_msgs in #print axioms orCircL

/-- info: 'LaxLogic.QLL.orCircR' depends on axioms: [propext] -/
#guard_msgs in #print axioms orCircR

/-- info: 'LaxLogic.QLL.exCirc' depends on axioms: [propext] -/
#guard_msgs in #print axioms exCirc

/-- info: 'LaxLogic.QLL.impCircC' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms impCircC

/-- info: 'LaxLogic.QLL.nCirc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms nCirc

/-- info: 'LaxLogic.QLL.Derives.allEs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Derives.allEs

end LaxLogic.QLL
