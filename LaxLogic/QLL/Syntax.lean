/-
# `LaxLogic.QLL.Syntax` — a deep embedding of the abstract logic of TPHOLs 2001

The syntax of the abstract language of

> M. Fairtlough, M. Mendler and X. Cheng, *Abstraction and refinement in higher
> order logic*, TPHOLs 2001, LNCS 2152, 201–216,

as a Lean datatype rather than a Lean predicate.  `LaxLogic.Obligation` is the
*shallow* rendering of the same paper: there a refinement pair is a Lean
proposition and its proof is a Lean proof.  Here a formula is a tree, a proof
is a tree, and whether the second proves the first is decided by a program.

Three deliberate departures from the paper, each recorded where it bites.

* **`n`-ary predicates.**  The report has no predicate syntax at all.  CLP and
  Prolog are complete for unary predicates, so nothing is gained in principle,
  but the generality is useful and harmless.  `Form.pred` takes a name and a
  list of terms.

* **Locally nameless binding.**  Free occurrences carry names, bound
  occurrences are de Bruijn indices.  There are *two* binding sorts, because
  Fig. 5 binds two:  `λz.p` and the case branches bind **proof** variables,
  `⟨p | x⟩` binds an **individual**, and `case r of [ιₓ(z) → p]` binds one of
  each.  The two index spaces are independent; `openP`/`openI` open them.

* **`⊤` and `⊥` for the report's `true` and `false`.**  A naming choice only;
  `Form.true` would shadow awkwardly.  `⊥` gains the elimination rule the
  figure omits (see `Deriv.lean`).

The modality subscript `Q` is kept in the syntax even though Fig. 5 gives
`◯∀` and `◯∃` *the same rules* — the side condition there reads only "if
`Q = ∀` or `Q = ∃`", and Fig. 6 carries the subscript without using it.  The
two are told apart by the Fig. 4 refinement clauses

    (p : ◯∀M) = ∀z::|M|. p z ⊃ (z : M)        (p : ◯∃M) = ∃z::|M|. p z ∧ (z : M)

which live in the interpretation, not the deduction system.
-/

namespace LaxLogic.QLL

/-! ## Individual terms -/

/--
First-order individual terms.  `bvar` is a de Bruijn index counting individual
binders outwards; `fvar` is a named free individual; `fn` is an `n`-ary
function symbol, so arity `0` gives constants.
-/
inductive Tm where
  | bvar : Nat → Tm
  | fvar : String → Tm
  | fn   : String → List Tm → Tm
  deriving Repr, Inhabited

namespace Tm

/-! `Tm` nests a `List Tm`, and `deriving DecidableEq` has no handler for that.
Every function below is therefore written as a mutual pair with an explicit
list companion, keeping the recursion structural — no `WellFounded.fix`, whose
cost in this development is on record.  Decidable equality is built by hand
from a boolean equality and its characterisation; once it exists, `Form` and
`Pf` derive theirs in the ordinary way. -/

mutual
/-- Open the bound individual at index `k` with `u`. -/
def openAt (k : Nat) (u : Tm) : Tm → Tm
  | .bvar i  => if i = k then u else .bvar i
  | .fvar x  => .fvar x
  | .fn f ts => .fn f (openAtList k u ts)
/-- `openAt` on a list of arguments. -/
def openAtList (k : Nat) (u : Tm) : List Tm → List Tm
  | []      => []
  | t :: ts => openAt k u t :: openAtList k u ts
end

mutual
/-- The named free individuals of a term. -/
def fv : Tm → List String
  | .bvar _  => []
  | .fvar x  => [x]
  | .fn _ ts => fvList ts
/-- `fv` on a list of arguments. -/
def fvList : List Tm → List String
  | []      => []
  | t :: ts => fv t ++ fvList ts
end

mutual
/-- Close over the named individual `a`, turning its free occurrences into the
bound index `k`.  Inverse to `openAt` on locally closed terms; the checker uses
it to recover `∀x.M` from an inferred body. -/
def closeAt (k : Nat) (a : String) : Tm → Tm
  | .bvar i  => .bvar i
  | .fvar x  => if x = a then .bvar k else .fvar x
  | .fn f ts => .fn f (closeAtList k a ts)
/-- `closeAt` on a list of arguments. -/
def closeAtList (k : Nat) (a : String) : List Tm → List Tm
  | []      => []
  | t :: ts => closeAt k a t :: closeAtList k a ts
end

mutual
/-- Structural equality test. -/
def beq : Tm → Tm → Bool
  | .bvar i,  .bvar j  => i == j
  | .fvar x,  .fvar y  => x == y
  | .fn f ts, .fn g us => f == g && beqList ts us
  | _,        _        => false
/-- `beq` on lists, which also compares lengths. -/
def beqList : List Tm → List Tm → Bool
  | [],      []      => true
  | t :: ts, u :: us => beq t u && beqList ts us
  | _,       _       => false
end

mutual
/-- `beq` decides equality. -/
theorem beq_iff : ∀ a b : Tm, beq a b = true ↔ a = b
  | .bvar _,  .bvar _  => by simp [beq]
  | .fvar _,  .fvar _  => by simp [beq]
  | .fn _ ts, .fn _ us => by simp [beq, beqList_iff ts us]
  | .bvar _,  .fvar _  => by simp [beq]
  | .bvar _,  .fn _ _  => by simp [beq]
  | .fvar _,  .bvar _  => by simp [beq]
  | .fvar _,  .fn _ _  => by simp [beq]
  | .fn _ _,  .bvar _  => by simp [beq]
  | .fn _ _,  .fvar _  => by simp [beq]
/-- `beqList` decides equality of argument lists. -/
theorem beqList_iff : ∀ ts us : List Tm, beqList ts us = true ↔ ts = us
  | [],      []      => by simp [beqList]
  | [],      _ :: _  => by simp [beqList]
  | _ :: _,  []      => by simp [beqList]
  | t :: ts, u :: us => by simp [beqList, beq_iff t u, beqList_iff ts us]
end

instance : DecidableEq Tm := fun a b => decidable_of_iff _ (beq_iff a b)

end Tm

/-! ## Formulas -/

/-- The two lax modalities of QLL, kept distinct in the syntax. -/
inductive Q where
  | all
  | ex
  deriving Repr, DecidableEq, Inhabited

/--
Abstract formulas `M`, `N`.  `forall_` and `exists_` bind one individual: the
body sits under a de Bruijn binder, so `∀x.M` is `forall_ M` with the bound
occurrences of `x` in `M` written `Tm.bvar 0`.
-/
inductive Form where
  | top     : Form
  | bot     : Form
  | pred    : String → List Tm → Form
  | and     : Form → Form → Form
  | or      : Form → Form → Form
  | imp     : Form → Form → Form
  | circ    : Q → Form → Form
  | forall_ : Form → Form
  | exists_ : Form → Form
  deriving Repr, DecidableEq, Inhabited

namespace Form

/-- Open the bound individual at index `k` with the term `u`.  The index is
raised under each individual binder. -/
def openAt (k : Nat) (u : Tm) : Form → Form
  | .top        => .top
  | .bot        => .bot
  | .pred P ts  => .pred P (Tm.openAtList k u ts)
  | .and M N    => .and (openAt k u M) (openAt k u N)
  | .or M N     => .or (openAt k u M) (openAt k u N)
  | .imp M N    => .imp (openAt k u M) (openAt k u N)
  | .circ q M   => .circ q (openAt k u M)
  | .forall_ M  => .forall_ (openAt (k + 1) u M)
  | .exists_ M  => .exists_ (openAt (k + 1) u M)

/-- Close over the named individual `a`, turning its free occurrences into the
bound index `k`. -/
def closeAt (k : Nat) (a : String) : Form → Form
  | .top        => .top
  | .bot        => .bot
  | .pred P ts  => .pred P (Tm.closeAtList k a ts)
  | .and M N    => .and (closeAt k a M) (closeAt k a N)
  | .or M N     => .or (closeAt k a M) (closeAt k a N)
  | .imp M N    => .imp (closeAt k a M) (closeAt k a N)
  | .circ q M   => .circ q (closeAt k a M)
  | .forall_ M  => .forall_ (closeAt (k + 1) a M)
  | .exists_ M  => .exists_ (closeAt (k + 1) a M)

/-- `M` with its outermost individual binder opened by the free individual `a`. -/
abbrev openWith (a : String) (M : Form) : Form := openAt 0 (.fvar a) M

/-- `M` with free occurrences of `a` bound by a fresh outermost binder. -/
abbrev closeWith (a : String) (M : Form) : Form := closeAt 0 a M

/-- The named free individuals of a formula. -/
def fv : Form → List String
  | .top        => []
  | .bot        => []
  | .pred _ ts  => Tm.fvList ts
  | .and M N    => fv M ++ fv N
  | .or M N     => fv M ++ fv N
  | .imp M N    => fv M ++ fv N
  | .circ _ M   => fv M
  | .forall_ M  => fv M
  | .exists_ M  => fv M

end Form

/-! ## Proof terms -/

/--
The proof terms of Fig. 5.

Binding, in the two independent de Bruijn spaces:

| constructor | proof binders | individual binders |
| :-- | :-- | :-- |
| `lam p`            | `z` in `p`            | — |
| `caseOr r p q`     | `y` in `p`, `z` in `q`| — |
| `letQ _ p q`       | `z` in `q`            | — |
| `gen p`            | —                     | `x` in `p` |
| `caseEx r p`       | `z` in `p`            | `x` in `p` |

`inst` and `pack` carry an individual *term*, the `t` of `π_t(p)` and `ι_t(p)`;
they bind nothing.
-/
inductive Pf where
  | bvar   : Nat → Pf
  | fvar   : String → Pf
  | star   : Pf
  | pair   : Pf → Pf → Pf
  | fst    : Pf → Pf
  | snd    : Pf → Pf
  | inl    : Pf → Pf
  | inr    : Pf → Pf
  | caseOr : Pf → Pf → Pf → Pf
  | lam    : Pf → Pf
  | app    : Pf → Pf → Pf
  | val    : Q → Pf → Pf
  | letQ   : Q → Pf → Pf → Pf
  | gen    : Pf → Pf
  | inst   : Tm → Pf → Pf
  | pack   : Tm → Pf → Pf
  | caseEx : Pf → Pf → Pf
  | exf    : Form → Pf → Pf
  deriving Repr, DecidableEq, Inhabited

namespace Pf

/-- Open the bound **proof** variable at index `k` with the proof term `u`.
The index rises under proof binders only. -/
def openP (k : Nat) (u : Pf) : Pf → Pf
  | .bvar i       => if i = k then u else .bvar i
  | .fvar x       => .fvar x
  | .star         => .star
  | .pair p q     => .pair (openP k u p) (openP k u q)
  | .fst p        => .fst (openP k u p)
  | .snd p        => .snd (openP k u p)
  | .inl p        => .inl (openP k u p)
  | .inr p        => .inr (openP k u p)
  | .caseOr r p q => .caseOr (openP k u r) (openP (k + 1) u p) (openP (k + 1) u q)
  | .lam p        => .lam (openP (k + 1) u p)
  | .app p q      => .app (openP k u p) (openP k u q)
  | .val q p      => .val q (openP k u p)
  | .letQ q p b   => .letQ q (openP k u p) (openP (k + 1) u b)
  | .gen p        => .gen (openP k u p)
  | .inst t p     => .inst t (openP k u p)
  | .pack t p     => .pack t (openP k u p)
  | .caseEx r p   => .caseEx (openP k u r) (openP (k + 1) u p)
  | .exf M p      => .exf M (openP k u p)

/-- Open the bound **individual** variable at index `k` with the term `u`.
The index rises under individual binders only, and passes into the embedded
terms and formula. -/
def openI (k : Nat) (u : Tm) : Pf → Pf
  | .bvar i       => .bvar i
  | .fvar x       => .fvar x
  | .star         => .star
  | .pair p q     => .pair (openI k u p) (openI k u q)
  | .fst p        => .fst (openI k u p)
  | .snd p        => .snd (openI k u p)
  | .inl p        => .inl (openI k u p)
  | .inr p        => .inr (openI k u p)
  | .caseOr r p q => .caseOr (openI k u r) (openI k u p) (openI k u q)
  | .lam p        => .lam (openI k u p)
  | .app p q      => .app (openI k u p) (openI k u q)
  | .val q p      => .val q (openI k u p)
  | .letQ q p b   => .letQ q (openI k u p) (openI k u b)
  | .gen p        => .gen (openI (k + 1) u p)
  | .inst t p     => .inst (Tm.openAt k u t) (openI k u p)
  | .pack t p     => .pack (Tm.openAt k u t) (openI k u p)
  | .caseEx r p   => .caseEx (openI k u r) (openI (k + 1) u p)
  | .exf M p      => .exf (Form.openAt k u M) (openI k u p)

/--
Substitute the proof term `u` for the *named* free proof variable `x`.

Distinct from `openP`, which replaces a de Bruijn occurrence.  This is what
`Subst` needs: it rewrites `q` to `q{p/z}` where `z` is a name standing in a
context entry.
-/
def substP (x : String) (u : Pf) : Pf → Pf
  | .bvar i       => .bvar i
  | .fvar y       => if y = x then u else .fvar y
  | .star         => .star
  | .pair p q     => .pair (substP x u p) (substP x u q)
  | .fst p        => .fst (substP x u p)
  | .snd p        => .snd (substP x u p)
  | .inl p        => .inl (substP x u p)
  | .inr p        => .inr (substP x u p)
  | .caseOr r p q => .caseOr (substP x u r) (substP x u p) (substP x u q)
  | .lam p        => .lam (substP x u p)
  | .app p q      => .app (substP x u p) (substP x u q)
  | .val q p      => .val q (substP x u p)
  | .letQ q p b   => .letQ q (substP x u p) (substP x u b)
  | .gen p        => .gen (substP x u p)
  | .inst t p     => .inst t (substP x u p)
  | .pack t p     => .pack t (substP x u p)
  | .caseEx r p   => .caseEx (substP x u r) (substP x u p)
  | .exf M p      => .exf M (substP x u p)

/-- `p` with its outermost bound proof variable opened by the free proof
variable `x`. -/
abbrev openPWith (x : String) (p : Pf) : Pf := openP 0 (.fvar x) p

/-- `p` with its outermost bound individual opened by the free individual `a`. -/
abbrev openIWith (a : String) (p : Pf) : Pf := openI 0 (.fvar a) p

/--
Number of proof-term nodes.  The checker recurses on opened bodies, which are
not structural subterms, so termination is by this measure; opening with a
variable preserves it (`Check.size_openP`, `Check.size_openI`).
-/
def size : Pf → Nat
  | .bvar _       => 1
  | .fvar _       => 1
  | .star         => 1
  | .pair p q     => size p + size q + 1
  | .fst p        => size p + 1
  | .snd p        => size p + 1
  | .inl p        => size p + 1
  | .inr p        => size p + 1
  | .caseOr r p q => size r + size p + size q + 1
  | .lam p        => size p + 1
  | .app p q      => size p + size q + 1
  | .val _ p      => size p + 1
  | .letQ _ p b   => size p + size b + 1
  | .gen p        => size p + 1
  | .inst _ p     => size p + 1
  | .pack _ p     => size p + 1
  | .caseEx r p   => size r + size p + 1
  | .exf _ p      => size p + 1

/-- The named free **proof** variables of a proof term. -/
def fvP : Pf → List String
  | .bvar _       => []
  | .fvar x       => [x]
  | .star         => []
  | .pair p q     => fvP p ++ fvP q
  | .fst p        => fvP p
  | .snd p        => fvP p
  | .inl p        => fvP p
  | .inr p        => fvP p
  | .caseOr r p q => fvP r ++ fvP p ++ fvP q
  | .lam p        => fvP p
  | .app p q      => fvP p ++ fvP q
  | .val _ p      => fvP p
  | .letQ _ p b   => fvP p ++ fvP b
  | .gen p        => fvP p
  | .inst _ p     => fvP p
  | .pack _ p     => fvP p
  | .caseEx r p   => fvP r ++ fvP p
  | .exf _ p      => fvP p

/-- The named free **individuals** of a proof term. -/
def fvI : Pf → List String
  | .bvar _       => []
  | .fvar _       => []
  | .star         => []
  | .pair p q     => fvI p ++ fvI q
  | .fst p        => fvI p
  | .snd p        => fvI p
  | .inl p        => fvI p
  | .inr p        => fvI p
  | .caseOr r p q => fvI r ++ fvI p ++ fvI q
  | .lam p        => fvI p
  | .app p q      => fvI p ++ fvI q
  | .val _ p      => fvI p
  | .letQ _ p b   => fvI p ++ fvI b
  | .gen p        => fvI p
  | .inst t p     => Tm.fv t ++ fvI p
  | .pack t p     => Tm.fv t ++ fvI p
  | .caseEx r p   => fvI r ++ fvI p
  | .exf M p      => Form.fv M ++ fvI p

end Pf

/-! ## Contexts -/

/--
A context is a list of the paper's **refinement pairs** `p : M`, not a list of
formulas.

Fig. 5 forces this.  Rule `I` reads `Γ, z:M, Γ' ⊢ z : M` with `z` a *variable*,
but `Subst` concludes `Γ, p:M, Γ' ⊢ q{p/z} : N` with `p :: |M|` an arbitrary
constraint term.  Both inhabit the same position, so the position holds pairs.

The consequence is worth stating, because it explains a shape that otherwise
looks wrong.  `I` fires only on a variable entry, and `⊃I` can only abstract a
variable entry — `λp.…` is not a term for non-variable `p`.  Every
context-extending rule extends with a *fresh variable*.  So `Subst` is the only
rule that puts a non-variable in a context, and once it has, that slot is
inert: nothing can use it and nothing can discharge it.  `Subst` does not
create a hypothesis for later use; it records that an assumption has been *met*
by a supplied constraint term.
-/
abbrev Ctx := List (Pf × Form)

/-- The names bound by the variable entries of a context. -/
def Ctx.names : Ctx → List String
  | []                    => []
  | (.fvar x, _) :: Γ     => x :: Ctx.names Γ
  | _ :: Γ                => Ctx.names Γ

/--
The context entries that are **not** variables.

By the reading recorded on `Derivable.subst`, these are exactly the residual
refinement obligations a derivation carries: constraint terms supplied by
`Subst` under a typing condition, whose refinement is still outstanding.
-/
def Ctx.obligations : Ctx → List (Pf × Form)
  | []                => []
  | (.fvar _, _) :: Γ => Ctx.obligations Γ
  | e :: Γ            => e :: Ctx.obligations Γ

/-- Every named free individual occurring in a context, in either component. -/
def Ctx.fvI : Ctx → List String
  | []           => []
  | (p, M) :: Γ  => p.fvI ++ M.fv ++ Ctx.fvI Γ

/-- Every named free proof variable occurring in the term components. -/
def Ctx.fvP : Ctx → List String
  | []           => []
  | (p, _) :: Γ  => p.fvP ++ Ctx.fvP Γ

end LaxLogic.QLL
